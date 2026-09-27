package cn.openvape.flowdeobf;

import org.objectweb.asm.ClassReader;
import org.objectweb.asm.ClassWriter;
import org.objectweb.asm.ConstantDynamic;
import org.objectweb.asm.Handle;
import org.objectweb.asm.Opcodes;
import org.objectweb.asm.tree.AbstractInsnNode;
import org.objectweb.asm.tree.ClassNode;
import org.objectweb.asm.tree.FieldInsnNode;
import org.objectweb.asm.tree.InsnNode;
import org.objectweb.asm.tree.IntInsnNode;
import org.objectweb.asm.tree.InvokeDynamicInsnNode;
import org.objectweb.asm.tree.LdcInsnNode;
import org.objectweb.asm.tree.MethodInsnNode;
import org.objectweb.asm.tree.MethodNode;
import org.objectweb.asm.tree.VarInsnNode;
import org.objectweb.asm.tree.analysis.Analyzer;
import org.objectweb.asm.tree.analysis.BasicValue;
import org.objectweb.asm.tree.analysis.BasicVerifier;
import org.objectweb.asm.tree.analysis.Frame;
import org.objectweb.asm.tree.analysis.SourceInterpreter;
import org.objectweb.asm.tree.analysis.SourceValue;
import org.objectweb.asm.util.CheckClassAdapter;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.AtomicMoveNotSupportedException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.StandardCopyOption;
import java.security.MessageDigest;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Set;
import java.util.zip.ZipEntry;
import java.util.zip.ZipInputStream;
import java.util.zip.ZipOutputStream;

/**
 * Audits residual ZKM DES helper methods and directizes the strictly proven
 * {@code (IJ)I} NoPadding family.
 *
 * <p>The integer helper is accepted only when its index prelude is exactly
 * {@code intArg ^ (int) (longArg & 0x7fffL) ^ mask}, its encrypted table is
 * recovered either from an explicit {@code long[]} initializer or from one
 * unique fixed-block NoPadding initializer, and both call arguments have
 * unique constant data-flow producers. Direct calls and matching integer
 * invokedynamic sites are replaced with stack-neutral POP/POP2 plus an integer
 * constant. A helper and its private bootstrap/linker closure are removed only
 * when the rewritten archive contains no reference from outside that closure.</p>
 *
 * <p>This class treats archive classes only as ASM data. It never defines,
 * initializes, reflectively queries, or executes an input class.</p>
 */
public final class ZkmDesHelperDeobfuscator {
    private static final String PKCS5 = "DES/CBC/PKCS5Padding";
    private static final String NO_PADDING = "DES/CBC/NoPadding";
    private static final String INTEGER_DESC = "(IJ)I";
    private static final String STRING_DESC = "(IJ)Ljava/lang/String;";
    private static final String BSM_DESC = "(Ljava/lang/invoke/MethodHandles$Lookup;"
            + "Ljava/lang/String;Ljava/lang/invoke/MethodType;)Ljava/lang/invoke/CallSite;";
    private static final String LINK_DESC = "(Ljava/lang/invoke/MethodHandles$Lookup;"
            + "Ljava/lang/invoke/MutableCallSite;Ljava/lang/String;[Ljava/lang/Object;)"
            + "Ljava/lang/Object;";
    private static final String INTEGER_LINK_DESC = "(Ljava/lang/invoke/MethodHandles$Lookup;"
            + "Ljava/lang/invoke/MutableCallSite;Ljava/lang/String;[Ljava/lang/Object;)I";

    private ZkmDesHelperDeobfuscator() {
    }

    public static void main(String[] args) throws Exception {
        if (args.length < 2 || args.length > 3) {
            System.err.println("usage: ZkmDesHelperDeobfuscator <input.jar> <report-dir> [output.jar]");
            System.exit(2);
        }
        Summary summary = rewrite(Paths.get(args[0]), Paths.get(args[1]),
                args.length == 3 ? Paths.get(args[2]) : null);
        System.out.println("classes=" + summary.parsedClasses
                + " helpers=" + summary.helpers
                + " integer_helpers=" + summary.integerHelpers
                + " proven_integer_helpers=" + summary.provenIntegerHelpers
                + " sites=" + summary.sites
                + " directized=" + summary.directizedSites
                + " helpers_removed=" + summary.helpersRemoved
                + " changed_classes=" + summary.changedClasses
                + " output_committed=" + summary.outputCommitted);
    }

    static Summary rewrite(Path input, Path reportDirectory, Path output) throws Exception {
        if (output != null && input.toAbsolutePath().normalize()
                .equals(output.toAbsolutePath().normalize())) {
            throw new IllegalArgumentException("output must not replace input");
        }
        Files.createDirectories(reportDirectory);
        List<EntryBytes> entries = readEntries(input);
        Map<String, byte[]> originals = classBytes(entries);
        Map<String, ClassNode> classes = classNodes(originals);
        Summary summary = new Summary();
        summary.parsedClasses = classes.size();
        summary.inputSha256 = sha256(input);

        List<Helper> helpers = discoverHelpers(classes);
        summary.helpers = helpers.size();
        for (Helper helper : helpers) {
            if (INTEGER_DESC.equals(helper.ref.desc)) summary.integerHelpers++;
            else if (STRING_DESC.equals(helper.ref.desc)) summary.stringHelpers++;
        }
        Map<MethodRef, Helper> byRef = new LinkedHashMap<>();
        for (Helper helper : helpers) byRef.put(helper.ref, helper);
        indexReferences(classes, helpers, byRef);
        Map<String, Long> classKeys = safeValidatedClassKeys(classes);
        summary.classKeys = classKeys.size();

        List<Site> sites = new ArrayList<>();
        Map<String, List<Site>> sitesByOwner = new LinkedHashMap<>();
        for (Helper helper : helpers) {
            if (!INTEGER_DESC.equals(helper.ref.desc)) continue;
            inspectIntegerHelper(classes.get(helper.ref.owner), helper);
            if (!helper.proven) {
                if (isClosedDeadSupportCandidate(helper)) {
                    sitesByOwner.put(helper.ref.owner, Collections.<Site>emptyList());
                }
                continue;
            }
            summary.provenIntegerHelpers++;
            ClassNode owner = classes.get(helper.ref.owner);
            Map<String, Long> staticLongs = provenLongFields(owner,
                    classKeys.get(helper.ref.owner));
            summary.provenLongFields += staticLongs.size();
            List<Site> ownerSites = inspectIntegerSites(owner, helper, staticLongs);
            sites.addAll(ownerSites);
            sitesByOwner.put(helper.ref.owner, ownerSites);
        }
        summary.sites = sites.size();
        for (Site site : sites) {
            if (site.proven) summary.provenSites++;
            else if (!"support-dynamic-call".equals(site.reason)) summary.runtimeSites++;
        }

        Map<String, byte[]> replacements = new LinkedHashMap<>();
        List<String> verifier = new ArrayList<>();
        verifier.add("scope\tclass\tstatus\tdetail");
        if (output != null) {
            List<String> owners = new ArrayList<>(sitesByOwner.keySet());
            Collections.sort(owners);
            for (String ownerName : owners) {
                Helper helper = byRef.get(integerHelperRef(helpers, ownerName));
                List<Site> ownerSites = sitesByOwner.get(ownerName);
                if (helper == null || ownerSites == null) continue;
                final RewritePlan plan = new RewritePlan(ownerName, helper, ownerSites,
                        externalReferences(classes, ownerName));
                ZkmClassRewriteTransaction.Result result =
                        ZkmClassRewriteTransaction.attempt(originals.get(ownerName),
                                new ZkmClassRewriteTransaction.Mutation() {
                                    @Override
                                    public void apply(ClassNode owner) throws Exception {
                                        applyPlan(owner, plan);
                                    }
                                },
                                new ZkmClassRewriteTransaction.Postcondition() {
                                    @Override
                                    public void verify(ClassNode owner) throws Exception {
                                        verifyPlan(owner, plan);
                                    }
                                }, new ZkmClassRewriteTransaction.Emitter() {
                                    @Override
                                    public byte[] emit(ClassNode owner) {
                                        ClassWriter writer = new ClassWriter(0);
                                        owner.accept(writer);
                                        return writer.toByteArray();
                                    }
                                });
                if (result.isCommitted()) {
                    if (plan.directized == 0 && plan.methodsRemoved == 0) {
                        verifier.add(tsv("class", ownerName, "SKIP", "no-proven-mutation"));
                        continue;
                    }
                    replacements.put(ownerName, result.bytes());
                    summary.changedClasses++;
                    summary.directizedSites += plan.directized;
                    summary.helpersRemoved += plan.helperRemoved ? 1 : 0;
                    summary.supportMethodsRemoved += plan.methodsRemoved;
                    helper.removed = plan.helperRemoved;
                    helper.supportMethodsRemoved = plan.methodsRemoved;
                    verifier.add(tsv("class", ownerName, "PASS",
                            "directized=" + plan.directized + ",removed=" + plan.methodsRemoved));
                    for (Site site : ownerSites) {
                        if (site.proven) site.action = "REWRITE";
                    }
                } else {
                    summary.rollbacks++;
                    helper.rollback = result.stage() + ":" + result.reason();
                    verifier.add(tsv("class", ownerName, "FAIL", helper.rollback));
                    for (Site site : ownerSites) {
                        if (site.proven) {
                            site.action = "ROLLBACK";
                            site.reason = helper.rollback;
                        }
                    }
                }
            }
            writeVerifiedArchive(entries, replacements, output, summary, verifier);
        }

        classifyHelpers(helpers);
        writeReports(input, output, reportDirectory, summary, helpers, sites, verifier);
        return summary;
    }

    private static boolean isClosedDeadSupportCandidate(Helper helper) {
        return (helper.access & (Opcodes.ACC_PRIVATE | Opcodes.ACC_STATIC))
                == (Opcodes.ACC_PRIVATE | Opcodes.ACC_STATIC)
                && helper.businessReferences == 0 && helper.bootstrapSites == 0;
    }

    private static MethodRef integerHelperRef(List<Helper> helpers, String owner) {
        MethodRef result = null;
        for (Helper helper : helpers) {
            if (!owner.equals(helper.ref.owner) || !INTEGER_DESC.equals(helper.ref.desc)) continue;
            if (result != null) return null;
            result = helper.ref;
        }
        return result;
    }

    private static List<Helper> discoverHelpers(Map<String, ClassNode> classes) {
        List<Helper> result = new ArrayList<>();
        List<String> names = new ArrayList<>(classes.keySet());
        Collections.sort(names);
        for (String name : names) {
            ClassNode owner = classes.get(name);
            for (MethodNode method : owner.methods) {
                if (!INTEGER_DESC.equals(method.desc) && !STRING_DESC.equals(method.desc)) continue;
                int pkcs5 = countCipherFactory(method, PKCS5);
                int noPadding = countCipherFactory(method, NO_PADDING);
                if (pkcs5 + noPadding != 1) continue;
                Helper helper = new Helper(new MethodRef(name, method.name, method.desc));
                helper.algorithm = pkcs5 == 1 ? PKCS5 : NO_PADDING;
                helper.access = method.access;
                helper.instructions = method.instructions.size();
                if ((method.access & (Opcodes.ACC_PRIVATE | Opcodes.ACC_STATIC))
                        != (Opcodes.ACC_PRIVATE | Opcodes.ACC_STATIC)) {
                    helper.reason = "not-private-static";
                }
                result.add(helper);
            }
        }
        return result;
    }

    private static void indexReferences(Map<String, ClassNode> classes,
                                        List<Helper> helpers,
                                        Map<MethodRef, Helper> byRef) {
        for (ClassNode owner : classes.values()) {
            for (MethodNode method : owner.methods) {
                for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
                     insn = insn.getNext()) {
                    if (insn instanceof MethodInsnNode) {
                        MethodInsnNode call = (MethodInsnNode) insn;
                        Helper helper = byRef.get(new MethodRef(call.owner, call.name, call.desc));
                        if (helper != null) {
                            helper.directReferences++;
                            if (owner.name.equals(helper.ref.owner) && isSupportMethod(method)) {
                                helper.supportReferences++;
                            } else {
                                helper.businessReferences++;
                            }
                        }
                    } else if (insn instanceof InvokeDynamicInsnNode) {
                        InvokeDynamicInsnNode indy = (InvokeDynamicInsnNode) insn;
                        addHandleReference(indy.bsm, owner, method, helpers, byRef);
                        for (Object argument : indy.bsmArgs) {
                            addConstantReference(argument, owner, method, helpers, byRef);
                        }
                        for (Helper helper : helpers) {
                            if (owner.name.equals(helper.ref.owner)
                                    && helper.ref.desc.equals(indy.desc)
                                    && indy.bsm != null
                                    && owner.name.equals(indy.bsm.getOwner())
                                    && BSM_DESC.equals(indy.bsm.getDesc())) {
                                helper.bootstrapSites++;
                            }
                        }
                    } else if (insn instanceof LdcInsnNode) {
                        addConstantReference(((LdcInsnNode) insn).cst,
                                owner, method, helpers, byRef);
                    }
                }
            }
        }
    }

    private static void addConstantReference(Object value, ClassNode owner,
                                             MethodNode method, List<Helper> helpers,
                                             Map<MethodRef, Helper> byRef) {
        if (value instanceof Handle) {
            addHandleReference((Handle) value, owner, method, helpers, byRef);
        } else if (value instanceof ConstantDynamic) {
            ConstantDynamic dynamic = (ConstantDynamic) value;
            addHandleReference(dynamic.getBootstrapMethod(), owner, method, helpers, byRef);
            for (int index = 0; index < dynamic.getBootstrapMethodArgumentCount(); index++) {
                addConstantReference(dynamic.getBootstrapMethodArgument(index),
                        owner, method, helpers, byRef);
            }
        }
    }

    private static void addHandleReference(Handle handle, ClassNode owner,
                                           MethodNode method, List<Helper> helpers,
                                           Map<MethodRef, Helper> byRef) {
        if (handle == null) return;
        Helper helper = byRef.get(new MethodRef(handle.getOwner(), handle.getName(), handle.getDesc()));
        if (helper == null) return;
        helper.handleReferences++;
        if (owner.name.equals(helper.ref.owner) && isSupportMethod(method)) {
            helper.supportReferences++;
        } else {
            helper.businessReferences++;
        }
    }

    private static void inspectIntegerHelper(ClassNode owner, Helper helper) {
        if (owner == null || !NO_PADDING.equals(helper.algorithm)
                || !helper.reason.isEmpty()) return;
        MethodNode method = method(owner, helper.ref.name, helper.ref.desc);
        if (method == null) {
            helper.reason = "helper-missing";
            return;
        }
        List<AbstractInsnNode> code = code(method);
        if (code.size() < 10
                || code.get(0).getOpcode() != Opcodes.ILOAD
                || ((VarInsnNode) code.get(0)).var != 0
                || code.get(1).getOpcode() != Opcodes.LLOAD
                || ((VarInsnNode) code.get(1)).var != 1
                || !Long.valueOf(0x7fffL).equals(longConstant(code.get(2)))
                || code.get(3).getOpcode() != Opcodes.LAND
                || code.get(4).getOpcode() != Opcodes.L2I
                || code.get(5).getOpcode() != Opcodes.IXOR
                || intConstant(code.get(6)) == null
                || code.get(7).getOpcode() != Opcodes.IXOR
                || code.get(8).getOpcode() != Opcodes.ISTORE) {
            helper.reason = "index-prelude-shape";
            return;
        }
        helper.indexMask = intConstant(code.get(6));
        Set<String> tableFields = new LinkedHashSet<>();
        for (AbstractInsnNode insn : code) {
            if (!(insn instanceof FieldInsnNode)) continue;
            FieldInsnNode field = (FieldInsnNode) insn;
            if (field.getOpcode() == Opcodes.GETSTATIC && owner.name.equals(field.owner)
                    && "[J".equals(field.desc)) tableFields.add(field.name);
        }
        if (tableFields.size() != 1) {
            helper.reason = "table-fields=" + tableFields.size();
            return;
        }
        helper.tableField = tableFields.iterator().next();
        Table table = recoverExplicitTable(owner, helper.tableField);
        if (table == null) table = recoverPackedTable(owner, helper.tableField);
        if (table == null || table.values.isEmpty()) {
            helper.reason = "table-unresolved";
            return;
        }
        helper.tableSource = table.source;
        helper.tableValues.addAll(table.values);
        helper.proven = true;
        helper.reason = "strict-index+" + table.source;
    }

    private static Table recoverExplicitTable(ClassNode owner, String fieldName) {
        MethodNode clinit = method(owner, "<clinit>", "()V");
        if (clinit == null) return null;
        List<AbstractInsnNode> code = code(clinit);
        List<Integer> writes = new ArrayList<>();
        for (int index = 0; index < code.size(); index++) {
            AbstractInsnNode insn = code.get(index);
            if (!(insn instanceof FieldInsnNode)) continue;
            FieldInsnNode field = (FieldInsnNode) insn;
            if (field.getOpcode() == Opcodes.PUTSTATIC && owner.name.equals(field.owner)
                    && fieldName.equals(field.name) && "[J".equals(field.desc)) writes.add(index);
        }
        if (writes.size() != 1) return null;
        int write = writes.get(0);
        if (write == 0 || !(code.get(write - 1) instanceof VarInsnNode)
                || code.get(write - 1).getOpcode() != Opcodes.ALOAD) return null;
        int local = ((VarInsnNode) code.get(write - 1)).var;
        int allocation = -1;
        int capacity = -1;
        for (int index = write - 2; index >= 2; index--) {
            if (!(code.get(index) instanceof VarInsnNode)
                    || code.get(index).getOpcode() != Opcodes.ASTORE
                    || ((VarInsnNode) code.get(index)).var != local) continue;
            if (!(code.get(index - 1) instanceof IntInsnNode)
                    || code.get(index - 1).getOpcode() != Opcodes.NEWARRAY
                    || ((IntInsnNode) code.get(index - 1)).operand != Opcodes.T_LONG) continue;
            Integer size = intConstant(code.get(index - 2));
            if (size != null && size > 0) {
                allocation = index;
                capacity = size;
                break;
            }
        }
        if (allocation < 0) return null;
        Long[] values = new Long[capacity];
        int stores = 0;
        for (int index = allocation + 1; index + 3 < write; index++) {
            if (!(code.get(index) instanceof VarInsnNode)
                    || code.get(index).getOpcode() != Opcodes.ALOAD
                    || ((VarInsnNode) code.get(index)).var != local) continue;
            Integer slot = intConstant(code.get(index + 1));
            Long value = longConstant(code.get(index + 2));
            if (slot == null || slot < 0 || slot >= capacity || value == null
                    || code.get(index + 3).getOpcode() != Opcodes.LASTORE
                    || values[slot] != null) continue;
            values[slot] = value;
            stores++;
        }
        if (stores != capacity) return null;
        return new Table(Arrays.asList(values), "explicit-long-array");
    }

    private static Table recoverPackedTable(ClassNode owner, String fieldName) {
        MethodNode clinit = method(owner, "<clinit>", "()V");
        if (clinit == null) return null;
        List<AbstractInsnNode> code = code(clinit);
        List<Integer> factories = new ArrayList<>();
        for (int index = 0; index < code.size(); index++) {
            if (isCipherFactory(code.get(index), NO_PADDING)) factories.add(index);
        }
        if (factories.size() != 1) return null;
        int factory = factories.get(0);
        int fieldWrite = -1;
        for (int index = factory + 1; index < code.size(); index++) {
            AbstractInsnNode insn = code.get(index);
            if (!(insn instanceof FieldInsnNode)) continue;
            FieldInsnNode field = (FieldInsnNode) insn;
            if (field.getOpcode() == Opcodes.PUTSTATIC && owner.name.equals(field.owner)
                    && fieldName.equals(field.name) && "[J".equals(field.desc)) {
                if (fieldWrite >= 0) return null;
                fieldWrite = index;
            }
        }
        if (fieldWrite < 0) return null;
        int capacity = -1;
        for (int index = factory + 1; index + 1 < fieldWrite; index++) {
            if (!(code.get(index) instanceof IntInsnNode)
                    || code.get(index).getOpcode() != Opcodes.NEWARRAY
                    || ((IntInsnNode) code.get(index)).operand != Opcodes.T_LONG) continue;
            Integer size = intConstant(code.get(index - 1));
            if (size == null || size <= 0) continue;
            if (capacity >= 0) return null;
            capacity = size;
        }
        if (capacity <= 0) return null;

        int keyConstructor = -1;
        for (int index = factory + 1; index < fieldWrite; index++) {
            AbstractInsnNode insn = code.get(index);
            if (!(insn instanceof MethodInsnNode)) continue;
            MethodInsnNode call = (MethodInsnNode) insn;
            if (call.getOpcode() == Opcodes.INVOKESPECIAL
                    && "javax/crypto/spec/DESKeySpec".equals(call.owner)
                    && "<init>".equals(call.name) && "([B)V".equals(call.desc)) {
                if (keyConstructor >= 0) return null;
                keyConstructor = index;
            }
        }
        if (keyConstructor < 0) return null;
        Set<Long> keyConstants = new LinkedHashSet<>();
        for (int index = factory + 1; index < keyConstructor; index++) {
            Long value = longConstant(code.get(index));
            if (value != null) keyConstants.add(value);
        }
        if (keyConstants.size() != 1) return null;
        long key = keyConstants.iterator().next();

        Set<String> packed = new LinkedHashSet<>();
        for (int index = keyConstructor + 1; index < fieldWrite; index++) {
            if (!(code.get(index) instanceof LdcInsnNode)
                    || !(((LdcInsnNode) code.get(index)).cst instanceof String)) continue;
            String value = (String) ((LdcInsnNode) code.get(index)).cst;
            if (value.length() == capacity * 8 && isLatin1(value)) packed.add(value);
        }
        if (packed.size() != 1) return null;
        try {
            List<Long> values = ZkmDesConstantEvaluator.decryptPackedLongs(
                    ZkmDesConstantEvaluator.KeyMaterial.proven(key,
                            "PACKED_HELPER_TABLE_KEY", owner.name + "." + fieldName),
                    packed.iterator().next());
            if (values.size() != capacity) return null;
            return new Table(values, "fixed-block-packed-long-array");
        } catch (Exception failure) {
            return null;
        }
    }

    private static List<Site> inspectIntegerSites(ClassNode owner, Helper helper) {
        return inspectIntegerSites(owner, helper, Collections.<String, Long>emptyMap());
    }

    private static List<Site> inspectIntegerSites(ClassNode owner, Helper helper,
                                                  Map<String, Long> staticLongs) {
        List<Site> result = new ArrayList<>();
        if (owner == null) return result;
        for (MethodNode method : owner.methods) {
            Frame<SourceValue>[] frames;
            try {
                frames = new Analyzer<SourceValue>(new SourceInterpreter()).analyze(owner.name, method);
            } catch (Exception failure) {
                frames = null;
            }
            int instruction = 0;
            for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
                 insn = insn.getNext(), instruction++) {
                boolean direct = insn instanceof MethodInsnNode
                        && helper.ref.equals(new MethodRef(((MethodInsnNode) insn).owner,
                        ((MethodInsnNode) insn).name, ((MethodInsnNode) insn).desc));
                boolean indy = insn instanceof InvokeDynamicInsnNode
                        && INTEGER_DESC.equals(((InvokeDynamicInsnNode) insn).desc)
                        && ((InvokeDynamicInsnNode) insn).bsm != null
                        && owner.name.equals(((InvokeDynamicInsnNode) insn).bsm.getOwner())
                        && BSM_DESC.equals(((InvokeDynamicInsnNode) insn).bsm.getDesc());
                if (!direct && !indy) continue;
                Site site = new Site(owner.name, method.name, method.desc, instruction,
                        direct ? "INVOKESTATIC" : "INVOKEDYNAMIC");
                result.add(site);
                if (direct && isSupportMethod(method)) {
                    site.reason = "support-dynamic-call";
                    continue;
                }
                Expressions expressions = resolveArguments(method, insn, frames,
                        owner.name, staticLongs);
                if (expressions == null) {
                    site.reason = "non-constant-arguments";
                    continue;
                }
                site.intArgument = expressions.intValue;
                site.longArgument = expressions.longValue;
                site.tableIndex = expressions.intValue
                        ^ (int) (expressions.longValue & 0x7fffL) ^ helper.indexMask;
                if (site.tableIndex < 0 || site.tableIndex >= helper.tableValues.size()) {
                    site.reason = "table-index=" + site.tableIndex + "/" + helper.tableValues.size();
                    continue;
                }
                try {
                    site.value = ZkmDesConstantEvaluator.decryptLowInt(
                            ZkmDesConstantEvaluator.KeyMaterial.proven(expressions.longValue,
                                    "HELPER_CALL_KEY", owner.name + "." + method.name
                                            + method.desc + "@" + instruction),
                            helper.tableValues.get(site.tableIndex));
                    site.proven = true;
                    site.reason = "constant-args+strict-helper+proven-table";
                    site.action = "PROVEN_DRY_RUN";
                } catch (Exception failure) {
                    site.reason = "inner-des=" + shortReason(failure);
                }
            }
        }
        return result;
    }

    private static Expressions resolveArguments(MethodNode method, AbstractInsnNode call,
                                                Frame<SourceValue>[] frames,
                                                String owner,
                                                Map<String, Long> staticLongs) {
        int index = method.instructions.indexOf(call);
        if (frames == null || index < 0 || index >= frames.length) return null;
        Frame<SourceValue> frame = frames[index];
        if (frame == null || frame.getStackSize() < 2) return null;
        SourceValue intSource = frame.getStack(frame.getStackSize() - 2);
        SourceValue longSource = frame.getStack(frame.getStackSize() - 1);
        if (intSource == null || longSource == null || intSource.getSize() != 1
                || longSource.getSize() != 2 || intSource.insns.size() != 1
                || longSource.insns.size() != 1) return null;
        IntExpression intValue = evalInt(intSource.insns.iterator().next(), method, 0,
                owner, staticLongs);
        LongExpression longValue = evalLong(longSource.insns.iterator().next(), method, 0,
                owner, staticLongs);
        return intValue == null || longValue == null ? null
                : new Expressions(intValue.value, longValue.value);
    }

    private static IntExpression evalInt(AbstractInsnNode end, MethodNode method, int depth,
                                         String owner, Map<String, Long> staticLongs) {
        if (end == null || depth > 24) return null;
        Integer constant = intConstant(end);
        if (constant != null) return new IntExpression(constant, end);
        if (end instanceof VarInsnNode && end.getOpcode() == Opcodes.ILOAD) {
            AbstractInsnNode store = uniqueStoreBefore(end, ((VarInsnNode) end).var, Opcodes.ISTORE);
            IntExpression stored = store == null ? null
                    : evalInt(previousCode(store), method, depth + 1, owner, staticLongs);
            return stored == null ? null : new IntExpression(stored.value, end);
        }
        int opcode = end.getOpcode();
        if (opcode == Opcodes.IXOR || opcode == Opcodes.IAND || opcode == Opcodes.IOR
                || opcode == Opcodes.IADD || opcode == Opcodes.ISUB) {
            IntExpression right = evalInt(previousCode(end), method, depth + 1,
                    owner, staticLongs);
            IntExpression left = right == null ? null
                    : evalInt(previousCode(right.start), method, depth + 1,
                    owner, staticLongs);
            if (left == null || right == null) return null;
            int value = opcode == Opcodes.IXOR ? left.value ^ right.value
                    : opcode == Opcodes.IAND ? left.value & right.value
                    : opcode == Opcodes.IOR ? left.value | right.value
                    : opcode == Opcodes.IADD ? left.value + right.value
                    : left.value - right.value;
            return new IntExpression(value, left.start);
        }
        if (opcode == Opcodes.INEG) {
            IntExpression value = evalInt(previousCode(end), method, depth + 1,
                    owner, staticLongs);
            return value == null ? null : new IntExpression(-value.value, value.start);
        }
        if (opcode == Opcodes.L2I) {
            LongExpression value = evalLong(previousCode(end), method, depth + 1,
                    owner, staticLongs);
            return value == null ? null : new IntExpression((int) value.value, value.start);
        }
        return null;
    }

    private static LongExpression evalLong(AbstractInsnNode end, MethodNode method, int depth,
                                           String owner, Map<String, Long> staticLongs) {
        if (end == null || depth > 24) return null;
        Long constant = longConstant(end);
        if (constant != null) return new LongExpression(constant, end);
        if (end instanceof FieldInsnNode && end.getOpcode() == Opcodes.GETSTATIC) {
            FieldInsnNode field = (FieldInsnNode) end;
            Long value = owner.equals(field.owner) && "J".equals(field.desc)
                    ? staticLongs.get(field.name) : null;
            if (value != null) return new LongExpression(value, end);
        }
        if (end instanceof VarInsnNode && end.getOpcode() == Opcodes.LLOAD) {
            AbstractInsnNode store = uniqueStoreBefore(end, ((VarInsnNode) end).var, Opcodes.LSTORE);
            LongExpression stored = store == null ? null
                    : evalLong(previousCode(store), method, depth + 1, owner, staticLongs);
            return stored == null ? null : new LongExpression(stored.value, end);
        }
        int opcode = end.getOpcode();
        if (opcode == Opcodes.LXOR || opcode == Opcodes.LAND || opcode == Opcodes.LOR
                || opcode == Opcodes.LADD || opcode == Opcodes.LSUB) {
            LongExpression right = evalLong(previousCode(end), method, depth + 1,
                    owner, staticLongs);
            LongExpression left = right == null ? null
                    : evalLong(previousCode(right.start), method, depth + 1,
                    owner, staticLongs);
            if (left == null || right == null) return null;
            long value = opcode == Opcodes.LXOR ? left.value ^ right.value
                    : opcode == Opcodes.LAND ? left.value & right.value
                    : opcode == Opcodes.LOR ? left.value | right.value
                    : opcode == Opcodes.LADD ? left.value + right.value
                    : left.value - right.value;
            return new LongExpression(value, left.start);
        }
        if (opcode == Opcodes.LNEG) {
            LongExpression value = evalLong(previousCode(end), method, depth + 1,
                    owner, staticLongs);
            return value == null ? null : new LongExpression(-value.value, value.start);
        }
        if (opcode == Opcodes.I2L) {
            IntExpression value = evalInt(previousCode(end), method, depth + 1,
                    owner, staticLongs);
            return value == null ? null : new LongExpression(value.value, value.start);
        }
        return null;
    }

    private static AbstractInsnNode uniqueStoreBefore(AbstractInsnNode load, int local, int opcode) {
        AbstractInsnNode result = null;
        for (AbstractInsnNode cursor = load.getPrevious(); cursor != null;
             cursor = cursor.getPrevious()) {
            if (!(cursor instanceof VarInsnNode) || ((VarInsnNode) cursor).var != local) continue;
            if (cursor.getOpcode() == opcode) {
                if (result != null) return null;
                result = cursor;
            } else if (isStoreOpcode(cursor.getOpcode())) {
                return null;
            }
        }
        return result;
    }

    private static boolean isStoreOpcode(int opcode) {
        return opcode >= Opcodes.ISTORE && opcode <= Opcodes.ASTORE;
    }

    private static void applyPlan(ClassNode owner, RewritePlan plan) throws Exception {
        Map<String, List<Site>> byMethod = new LinkedHashMap<>();
        for (Site site : plan.sites) {
            if (!site.proven) continue;
            String key = site.methodName + site.methodDesc;
            List<Site> list = byMethod.get(key);
            if (list == null) {
                list = new ArrayList<>();
                byMethod.put(key, list);
            }
            list.add(site);
        }
        for (MethodNode method : owner.methods) {
            List<Site> methodSites = byMethod.get(method.name + method.desc);
            if (methodSites == null) continue;
            Collections.sort(methodSites, new Comparator<Site>() {
                @Override
                public int compare(Site left, Site right) {
                    return Integer.compare(right.instruction, left.instruction);
                }
            });
            for (Site site : methodSites) {
                AbstractInsnNode call = method.instructions.get(site.instruction);
                if (call == null || (!(call instanceof MethodInsnNode)
                        && !(call instanceof InvokeDynamicInsnNode))) {
                    throw new IllegalStateException("site-mismatch=" + method.name
                            + method.desc + "@" + site.instruction);
                }
                method.instructions.insertBefore(call, new InsnNode(Opcodes.POP2));
                method.instructions.insertBefore(call, new InsnNode(Opcodes.POP));
                method.instructions.set(call, pushInteger(site.value));
                plan.directized++;
            }
        }

        Set<MethodRef> closure = supportClosure(owner, plan.helper.ref);
        if (closureCanBeRemoved(owner, closure, plan.externalRefs)) {
            int removed = 0;
            boolean helperRemoved = false;
            for (int index = owner.methods.size() - 1; index >= 0; index--) {
                MethodNode method = owner.methods.get(index);
                MethodRef ref = new MethodRef(owner.name, method.name, method.desc);
                if (!closure.contains(ref)) continue;
                owner.methods.remove(index);
                removed++;
                if (ref.equals(plan.helper.ref)) helperRemoved = true;
            }
            plan.methodsRemoved = removed;
            plan.helperRemoved = helperRemoved;
        }
    }

    private static Set<MethodRef> supportClosure(ClassNode owner, MethodRef helper) {
        Set<MethodRef> closure = new LinkedHashSet<>();
        closure.add(helper);
        boolean changed;
        do {
            changed = false;
            for (MethodNode method : owner.methods) {
                MethodRef candidate = new MethodRef(owner.name, method.name, method.desc);
                if (closure.contains(candidate) || !isSupportMethod(method)) continue;
                if (referencesAny(method, closure)) {
                    closure.add(candidate);
                    changed = true;
                }
            }
        } while (changed);
        return closure;
    }

    private static boolean closureCanBeRemoved(ClassNode owner, Set<MethodRef> closure,
                                               Set<MethodRef> externalRefs) {
        for (MethodRef ref : closure) {
            if (externalRefs.contains(ref)) return false;
        }
        for (MethodNode method : owner.methods) {
            MethodRef caller = new MethodRef(owner.name, method.name, method.desc);
            if (closure.contains(caller)) continue;
            if (referencesAny(method, closure)) return false;
        }
        return true;
    }

    private static boolean referencesAny(MethodNode method, Set<MethodRef> targets) {
        for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
             insn = insn.getNext()) {
            if (insn instanceof MethodInsnNode) {
                MethodInsnNode call = (MethodInsnNode) insn;
                if (targets.contains(new MethodRef(call.owner, call.name, call.desc))) return true;
            } else if (insn instanceof InvokeDynamicInsnNode) {
                InvokeDynamicInsnNode indy = (InvokeDynamicInsnNode) insn;
                if (handleTargets(indy.bsm, targets)) return true;
                for (Object argument : indy.bsmArgs) {
                    if (constantTargets(argument, targets)) return true;
                }
            } else if (insn instanceof LdcInsnNode
                    && constantTargets(((LdcInsnNode) insn).cst, targets)) {
                return true;
            }
        }
        return false;
    }

    private static boolean constantTargets(Object value, Set<MethodRef> targets) {
        if (value instanceof Handle) return handleTargets((Handle) value, targets);
        if (!(value instanceof ConstantDynamic)) return false;
        ConstantDynamic dynamic = (ConstantDynamic) value;
        if (handleTargets(dynamic.getBootstrapMethod(), targets)) return true;
        for (int index = 0; index < dynamic.getBootstrapMethodArgumentCount(); index++) {
            if (constantTargets(dynamic.getBootstrapMethodArgument(index), targets)) return true;
        }
        return false;
    }

    private static boolean handleTargets(Handle handle, Set<MethodRef> targets) {
        return handle != null && targets.contains(new MethodRef(
                handle.getOwner(), handle.getName(), handle.getDesc()));
    }

    private static Set<MethodRef> externalReferences(Map<String, ClassNode> classes,
                                                     String targetOwner) {
        Set<MethodRef> result = new LinkedHashSet<>();
        for (ClassNode owner : classes.values()) {
            if (targetOwner.equals(owner.name)) continue;
            for (MethodNode method : owner.methods) {
                collectTargetReferences(method, targetOwner, result);
            }
        }
        return result;
    }

    private static void collectTargetReferences(MethodNode method, String owner,
                                                Set<MethodRef> result) {
        for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
             insn = insn.getNext()) {
            if (insn instanceof MethodInsnNode) {
                MethodInsnNode call = (MethodInsnNode) insn;
                if (owner.equals(call.owner)) result.add(new MethodRef(call.owner, call.name, call.desc));
            } else if (insn instanceof InvokeDynamicInsnNode) {
                InvokeDynamicInsnNode indy = (InvokeDynamicInsnNode) insn;
                collectHandle(indy.bsm, owner, result);
                for (Object argument : indy.bsmArgs) collectConstant(argument, owner, result);
            } else if (insn instanceof LdcInsnNode) {
                collectConstant(((LdcInsnNode) insn).cst, owner, result);
            }
        }
    }

    private static void collectConstant(Object value, String owner, Set<MethodRef> result) {
        if (value instanceof Handle) collectHandle((Handle) value, owner, result);
        else if (value instanceof ConstantDynamic) {
            ConstantDynamic dynamic = (ConstantDynamic) value;
            collectHandle(dynamic.getBootstrapMethod(), owner, result);
            for (int index = 0; index < dynamic.getBootstrapMethodArgumentCount(); index++) {
                collectConstant(dynamic.getBootstrapMethodArgument(index), owner, result);
            }
        }
    }

    private static void collectHandle(Handle handle, String owner, Set<MethodRef> result) {
        if (handle != null && owner.equals(handle.getOwner())) {
            result.add(new MethodRef(handle.getOwner(), handle.getName(), handle.getDesc()));
        }
    }

    private static void verifyPlan(ClassNode owner, RewritePlan plan) throws Exception {
        int remaining = 0;
        for (MethodNode method : owner.methods) {
            for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
                 insn = insn.getNext()) {
                if (insn instanceof MethodInsnNode) {
                    MethodInsnNode call = (MethodInsnNode) insn;
                    if (plan.helper.ref.equals(new MethodRef(call.owner, call.name, call.desc))
                            && !isSupportMethod(method)) remaining++;
                } else if (insn instanceof InvokeDynamicInsnNode) {
                    InvokeDynamicInsnNode indy = (InvokeDynamicInsnNode) insn;
                    if (INTEGER_DESC.equals(indy.desc) && indy.bsm != null
                            && owner.name.equals(indy.bsm.getOwner())
                            && BSM_DESC.equals(indy.bsm.getDesc())) remaining++;
                }
            }
        }
        int expectedUnresolved = 0;
        for (Site site : plan.sites) {
            if (!site.proven && !"support-dynamic-call".equals(site.reason)) expectedUnresolved++;
        }
        if (remaining != expectedUnresolved) {
            throw new IllegalStateException("remaining-sites=" + remaining + "/" + expectedUnresolved);
        }
        if (plan.helperRemoved && method(owner, plan.helper.ref.name, plan.helper.ref.desc) != null) {
            throw new IllegalStateException("helper-still-present");
        }
    }

    private static void classifyHelpers(List<Helper> helpers) {
        for (Helper helper : helpers) {
            if (helper.removed) helper.category = "DIRECTIZED_AND_REMOVED";
            else if (helper.directReferences + helper.handleReferences + helper.bootstrapSites == 0) {
                helper.category = "DEAD_UNREFERENCED";
            } else if (helper.businessReferences == 0 && helper.bootstrapSites == 0) {
                helper.category = "DEAD_SUPPORT_CLOSURE";
            } else if (helper.proven) {
                helper.category = "STATICALLY_EVALUABLE_INTEGER_HELPER";
            } else {
                helper.category = "LIVE_OR_PENDING_STATIC_EVALUATION";
            }
        }
    }

    private static Map<String, Long> safeValidatedClassKeys(Map<String, ClassNode> classes) {
        try {
            return ZkmStringDecryptor.solveValidatedClassKeys(classes);
        } catch (Throwable failure) {
            return Collections.emptyMap();
        }
    }

    private static Map<String, Long> provenLongFields(ClassNode owner, Long classKey) {
        if (owner == null || classKey == null) return Collections.emptyMap();
        MethodNode clinit = method(owner, "<clinit>", "()V");
        if (clinit == null) return Collections.emptyMap();
        Map<String, Long> result = new LinkedHashMap<>();
        for (AbstractInsnNode insn = clinit.instructions.getFirst(); insn != null;
             insn = insn.getNext()) {
            if (!(insn instanceof FieldInsnNode)) continue;
            FieldInsnNode field = (FieldInsnNode) insn;
            if (field.getOpcode() != Opcodes.PUTSTATIC || !owner.name.equals(field.owner)
                    || !"J".equals(field.desc)) continue;
            AbstractInsnNode previous = previousCode(insn);
            if (!(previous instanceof MethodInsnNode)) continue;
            MethodInsnNode call = (MethodInsnNode) previous;
            if (!"(J)J".equals(call.desc)) continue;
            result.put(field.name, classKey);
        }
        return result;
    }

    private static void writeReports(Path input, Path output, Path report,
                                     Summary summary, List<Helper> helpers,
                                     List<Site> sites, List<String> verifier) throws IOException {
        List<String> helperRows = new ArrayList<>();
        helperRows.add("class\tmethod\talgorithm\tinstructions\tdirect_refs\thandle_refs"
                + "\tbusiness_refs\tsupport_refs\tbootstrap_sites\ttable_field\ttable_entries"
                + "\ttable_source\tproven\tcategory\thelper_removed\tsupport_methods_removed"
                + "\treason\trollback");
        for (Helper helper : helpers) helperRows.add(helper.row());
        Files.write(report.resolve("helpers.tsv"), helperRows, StandardCharsets.UTF_8);

        List<String> siteRows = new ArrayList<>();
        siteRows.add("class\tmethod\tinstruction\tkind\tint_argument\tlong_argument_hex"
                + "\ttable_index\tvalue\tproven\taction\treason");
        for (Site site : sites) siteRows.add(site.row());
        Files.write(report.resolve("sites.tsv"), siteRows, StandardCharsets.UTF_8);
        Files.write(report.resolve("verifier.tsv"), verifier, StandardCharsets.UTF_8);

        List<String> removed = new ArrayList<>();
        removed.add("class\tmethod\tsupport_methods_removed");
        for (Helper helper : helpers) {
            if (helper.removed) removed.add(tsv(helper.ref.owner,
                    helper.ref.name + helper.ref.desc, helper.supportMethodsRemoved));
        }
        Files.write(report.resolve("removed-helpers.tsv"), removed, StandardCharsets.UTF_8);

        List<String> audit = new ArrayList<>();
        audit.add("input=" + input.toAbsolutePath().normalize());
        audit.add("input_sha256=" + summary.inputSha256);
        audit.add("output=" + (output == null ? "" : output.toAbsolutePath().normalize()));
        audit.add("parsed_classes=" + summary.parsedClasses);
        audit.add("helpers=" + summary.helpers);
        audit.add("pkcs5_string_helpers=" + summary.stringHelpers);
        audit.add("nopadding_integer_helpers=" + summary.integerHelpers);
        audit.add("proven_integer_helpers=" + summary.provenIntegerHelpers);
        audit.add("validated_class_keys=" + summary.classKeys);
        audit.add("proven_long_key_fields=" + summary.provenLongFields);
        audit.add("sites=" + summary.sites);
        audit.add("proven_sites=" + summary.provenSites);
        audit.add("runtime_or_unresolved_sites=" + summary.runtimeSites);
        audit.add("directized_sites=" + summary.directizedSites);
        audit.add("helpers_removed=" + summary.helpersRemoved);
        audit.add("support_methods_removed=" + summary.supportMethodsRemoved);
        audit.add("changed_classes=" + summary.changedClasses);
        audit.add("rollbacks=" + summary.rollbacks);
        audit.add("output_classes=" + summary.outputClasses);
        audit.add("output_verification_errors=" + summary.outputVerificationErrors);
        audit.add("output_committed=" + summary.outputCommitted);
        audit.add("input_classes_loaded=false");
        audit.add("input_classes_initialized=false");
        audit.add("gate=" + (summary.rollbacks == 0 && summary.outputVerificationErrors == 0
                ? "PASS" : "FAIL"));
        Files.write(report.resolve("audit.txt"), audit, StandardCharsets.UTF_8);
        Files.write(report.resolve("gate.txt"), Collections.singletonList(
                summary.rollbacks == 0 && summary.outputVerificationErrors == 0
                        ? "PASS" : "FAIL"), StandardCharsets.UTF_8);
    }

    private static List<EntryBytes> readEntries(Path input) throws IOException {
        List<EntryBytes> result = new ArrayList<>();
        try (ZipInputStream zip = new ZipInputStream(Files.newInputStream(input))) {
            for (ZipEntry entry; (entry = zip.getNextEntry()) != null; ) {
                ByteArrayOutputStream bytes = new ByteArrayOutputStream();
                byte[] buffer = new byte[8192];
                for (int read; (read = zip.read(buffer)) >= 0; ) {
                    if (read != 0) bytes.write(buffer, 0, read);
                }
                result.add(new EntryBytes(entry.getName(), bytes.toByteArray(), entry.isDirectory()));
            }
        }
        return result;
    }

    private static Map<String, byte[]> classBytes(List<EntryBytes> entries) {
        Map<String, byte[]> result = new LinkedHashMap<>();
        for (EntryBytes entry : entries) {
            if (entry.name.endsWith(".class") && !entry.directory) {
                result.put(entry.name.substring(0, entry.name.length() - 6), entry.bytes);
            }
        }
        return result;
    }

    private static Map<String, ClassNode> classNodes(Map<String, byte[]> bytes) {
        Map<String, ClassNode> result = new LinkedHashMap<>();
        for (Map.Entry<String, byte[]> entry : bytes.entrySet()) {
            ClassNode owner = readClass(entry.getValue());
            result.put(owner.name, owner);
        }
        return result;
    }

    private static ClassNode readClass(byte[] bytes) {
        ClassNode owner = new ClassNode(Opcodes.ASM9);
        new ClassReader(bytes).accept(owner, 0);
        return owner;
    }

    private static void writeVerifiedArchive(List<EntryBytes> entries,
                                             Map<String, byte[]> replacements,
                                             Path output, Summary summary,
                                             List<String> verifier) throws Exception {
        Path absolute = output.toAbsolutePath().normalize();
        Path parent = absolute.getParent();
        if (parent != null) Files.createDirectories(parent);
        Path temporary = Files.createTempFile(parent, absolute.getFileName().toString(), ".tmp");
        try {
            try (ZipOutputStream zip = new ZipOutputStream(Files.newOutputStream(temporary))) {
                for (EntryBytes entry : entries) {
                    ZipEntry target = new ZipEntry(entry.name);
                    zip.putNextEntry(target);
                    if (!entry.directory) {
                        String className = entry.name.endsWith(".class")
                                ? entry.name.substring(0, entry.name.length() - 6) : null;
                        byte[] bytes = className == null ? null : replacements.get(className);
                        zip.write(bytes == null ? entry.bytes : bytes);
                    }
                    zip.closeEntry();
                }
            }
            verifyArchive(temporary, summary, verifier);
            if (summary.outputVerificationErrors != 0) {
                throw new IllegalStateException("archive-verification-errors="
                        + summary.outputVerificationErrors);
            }
            try {
                Files.move(temporary, absolute, StandardCopyOption.ATOMIC_MOVE,
                        StandardCopyOption.REPLACE_EXISTING);
            } catch (AtomicMoveNotSupportedException unsupported) {
                Files.move(temporary, absolute, StandardCopyOption.REPLACE_EXISTING);
            }
            summary.outputCommitted = true;
        } finally {
            Files.deleteIfExists(temporary);
        }
    }

    private static void verifyArchive(Path archive, Summary summary,
                                      List<String> verifier) throws IOException {
        try (ZipInputStream zip = new ZipInputStream(Files.newInputStream(archive))) {
            for (ZipEntry entry; (entry = zip.getNextEntry()) != null; ) {
                if (!entry.getName().endsWith(".class")) continue;
                ByteArrayOutputStream bytes = new ByteArrayOutputStream();
                byte[] buffer = new byte[8192];
                for (int read; (read = zip.read(buffer)) >= 0; ) {
                    if (read != 0) bytes.write(buffer, 0, read);
                }
                summary.outputClasses++;
                try {
                    verifyClass(bytes.toByteArray());
                    verifier.add(tsv("archive", entry.getName(), "PASS", ""));
                } catch (Throwable failure) {
                    summary.outputVerificationErrors++;
                    verifier.add(tsv("archive", entry.getName(), "FAIL", shortReason(failure)));
                }
            }
        }
    }

    private static void verifyClass(byte[] bytes) throws Exception {
        ClassReader reader = new ClassReader(bytes);
        reader.accept(new CheckClassAdapter(new ClassWriter(0), false), 0);
        ClassNode owner = readClass(bytes);
        for (MethodNode method : owner.methods) {
            if (method.instructions != null && method.instructions.size() != 0) {
                new Analyzer<BasicValue>(new BasicVerifier()).analyze(owner.name, method);
            }
        }
    }

    private static int countCipherFactory(MethodNode method, String algorithm) {
        int result = 0;
        for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
             insn = insn.getNext()) {
            if (isCipherFactory(insn, algorithm)) result++;
        }
        return result;
    }

    private static boolean isCipherFactory(AbstractInsnNode insn, String algorithm) {
        if (!(insn instanceof MethodInsnNode)) return false;
        MethodInsnNode call = (MethodInsnNode) insn;
        if (call.getOpcode() != Opcodes.INVOKESTATIC
                || !"javax/crypto/Cipher".equals(call.owner)
                || !"getInstance".equals(call.name)
                || !"(Ljava/lang/String;)Ljavax/crypto/Cipher;".equals(call.desc)) return false;
        AbstractInsnNode previous = previousCode(insn);
        return previous instanceof LdcInsnNode && algorithm.equals(((LdcInsnNode) previous).cst);
    }

    private static boolean isSupportMethod(MethodNode method) {
        return (method.access & (Opcodes.ACC_PRIVATE | Opcodes.ACC_STATIC))
                == (Opcodes.ACC_PRIVATE | Opcodes.ACC_STATIC)
                && (BSM_DESC.equals(method.desc) || LINK_DESC.equals(method.desc)
                || INTEGER_LINK_DESC.equals(method.desc));
    }

    private static MethodNode method(ClassNode owner, String name, String desc) {
        for (MethodNode method : owner.methods) {
            if (name.equals(method.name) && desc.equals(method.desc)) return method;
        }
        return null;
    }

    private static List<AbstractInsnNode> code(MethodNode method) {
        List<AbstractInsnNode> result = new ArrayList<>();
        for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
             insn = insn.getNext()) {
            if (insn.getOpcode() >= 0) result.add(insn);
        }
        return result;
    }

    private static AbstractInsnNode previousCode(AbstractInsnNode insn) {
        for (AbstractInsnNode cursor = insn == null ? null : insn.getPrevious();
             cursor != null; cursor = cursor.getPrevious()) {
            if (cursor.getOpcode() >= 0) return cursor;
        }
        return null;
    }

    private static Integer intConstant(AbstractInsnNode insn) {
        if (insn == null) return null;
        int opcode = insn.getOpcode();
        if (opcode >= Opcodes.ICONST_M1 && opcode <= Opcodes.ICONST_5) {
            return opcode - Opcodes.ICONST_0;
        }
        if (insn instanceof IntInsnNode && (opcode == Opcodes.BIPUSH || opcode == Opcodes.SIPUSH)) {
            return ((IntInsnNode) insn).operand;
        }
        if (insn instanceof LdcInsnNode && ((LdcInsnNode) insn).cst instanceof Integer) {
            return (Integer) ((LdcInsnNode) insn).cst;
        }
        return null;
    }

    private static Long longConstant(AbstractInsnNode insn) {
        if (insn == null) return null;
        if (insn.getOpcode() == Opcodes.LCONST_0) return 0L;
        if (insn.getOpcode() == Opcodes.LCONST_1) return 1L;
        if (insn instanceof LdcInsnNode && ((LdcInsnNode) insn).cst instanceof Long) {
            return (Long) ((LdcInsnNode) insn).cst;
        }
        return null;
    }

    private static AbstractInsnNode pushInteger(int value) {
        if (value >= -1 && value <= 5) return new InsnNode(Opcodes.ICONST_0 + value);
        if (value >= Byte.MIN_VALUE && value <= Byte.MAX_VALUE) {
            return new IntInsnNode(Opcodes.BIPUSH, value);
        }
        if (value >= Short.MIN_VALUE && value <= Short.MAX_VALUE) {
            return new IntInsnNode(Opcodes.SIPUSH, value);
        }
        return new LdcInsnNode(value);
    }

    private static boolean isLatin1(String value) {
        for (int index = 0; index < value.length(); index++) {
            if (value.charAt(index) > 0xff) return false;
        }
        return true;
    }

    private static String sha256(Path path) throws Exception {
        MessageDigest digest = MessageDigest.getInstance("SHA-256");
        byte[] bytes = Files.readAllBytes(path);
        byte[] hash = digest.digest(bytes);
        StringBuilder result = new StringBuilder();
        for (byte value : hash) result.append(String.format(Locale.ROOT, "%02X", value & 0xff));
        return result.toString();
    }

    private static String shortReason(Throwable failure) {
        String message = failure.getMessage();
        return failure.getClass().getSimpleName()
                + (message == null || message.isEmpty() ? "" : ":" + message.replace('\t', ' '));
    }

    private static String tsv(Object... values) {
        StringBuilder result = new StringBuilder();
        for (Object value : values) {
            if (result.length() != 0) result.append('\t');
            String text = value == null ? "" : String.valueOf(value);
            result.append(text.replace('\t', ' ').replace('\r', ' ').replace('\n', ' '));
        }
        return result.toString();
    }

    static final class Summary {
        int parsedClasses;
        int helpers;
        int stringHelpers;
        int integerHelpers;
        int provenIntegerHelpers;
        int classKeys;
        int provenLongFields;
        int sites;
        int provenSites;
        int runtimeSites;
        int directizedSites;
        int helpersRemoved;
        int supportMethodsRemoved;
        int changedClasses;
        int rollbacks;
        int outputClasses;
        int outputVerificationErrors;
        boolean outputCommitted;
        String inputSha256;
    }

    private static final class Helper {
        final MethodRef ref;
        int access;
        int instructions;
        String algorithm = "";
        int directReferences;
        int handleReferences;
        int businessReferences;
        int supportReferences;
        int bootstrapSites;
        int indexMask;
        String tableField = "";
        String tableSource = "";
        final List<Long> tableValues = new ArrayList<>();
        boolean proven;
        boolean removed;
        int supportMethodsRemoved;
        String category = "";
        String reason = "";
        String rollback = "";

        Helper(MethodRef ref) {
            this.ref = ref;
        }

        String row() {
            return tsv(ref.owner, ref.name + ref.desc, algorithm, instructions,
                    directReferences, handleReferences, businessReferences,
                    supportReferences, bootstrapSites, tableField, tableValues.size(),
                    tableSource, proven, category, removed, supportMethodsRemoved,
                    reason, rollback);
        }
    }

    private static final class Site {
        final String owner;
        final String methodName;
        final String methodDesc;
        final int instruction;
        final String kind;
        Integer intArgument;
        Long longArgument;
        Integer tableIndex;
        Integer value;
        boolean proven;
        String action = "SKIP";
        String reason = "";

        Site(String owner, String methodName, String methodDesc, int instruction, String kind) {
            this.owner = owner;
            this.methodName = methodName;
            this.methodDesc = methodDesc;
            this.instruction = instruction;
            this.kind = kind;
        }

        String row() {
            return tsv(owner, methodName + methodDesc, instruction, kind,
                    intArgument, longArgument == null ? "" : String.format(Locale.ROOT,
                            "%016X", longArgument), tableIndex, value, proven, action, reason);
        }
    }

    private static final class Table {
        final List<Long> values;
        final String source;

        Table(List<Long> values, String source) {
            this.values = Collections.unmodifiableList(new ArrayList<Long>(values));
            this.source = source;
        }
    }

    private static final class Expressions {
        final int intValue;
        final long longValue;

        Expressions(int intValue, long longValue) {
            this.intValue = intValue;
            this.longValue = longValue;
        }
    }

    private static final class IntExpression {
        final int value;
        final AbstractInsnNode start;

        IntExpression(int value, AbstractInsnNode start) {
            this.value = value;
            this.start = start;
        }
    }

    private static final class LongExpression {
        final long value;
        final AbstractInsnNode start;

        LongExpression(long value, AbstractInsnNode start) {
            this.value = value;
            this.start = start;
        }
    }

    private static final class RewritePlan {
        final String owner;
        final Helper helper;
        final List<Site> sites;
        final Set<MethodRef> externalRefs;
        int directized;
        int methodsRemoved;
        boolean helperRemoved;

        RewritePlan(String owner, Helper helper, List<Site> sites,
                    Set<MethodRef> externalRefs) {
            this.owner = owner;
            this.helper = helper;
            this.sites = sites;
            this.externalRefs = externalRefs;
        }
    }

    private static final class MethodRef {
        final String owner;
        final String name;
        final String desc;

        MethodRef(String owner, String name, String desc) {
            this.owner = owner;
            this.name = name;
            this.desc = desc;
        }

        @Override
        public boolean equals(Object other) {
            if (!(other instanceof MethodRef)) return false;
            MethodRef ref = (MethodRef) other;
            return owner.equals(ref.owner) && name.equals(ref.name) && desc.equals(ref.desc);
        }

        @Override
        public int hashCode() {
            int result = owner.hashCode();
            result = 31 * result + name.hashCode();
            return 31 * result + desc.hashCode();
        }
    }

    private static final class EntryBytes {
        final String name;
        final byte[] bytes;
        final boolean directory;

        EntryBytes(String name, byte[] bytes, boolean directory) {
            this.name = name;
            this.bytes = bytes;
            this.directory = directory;
        }
    }
}
