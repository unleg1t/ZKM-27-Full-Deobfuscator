package cn.openvape.flowdeobf;

import org.objectweb.asm.ClassReader;
import org.objectweb.asm.ConstantDynamic;
import org.objectweb.asm.Handle;
import org.objectweb.asm.Opcodes;
import org.objectweb.asm.Type;
import org.objectweb.asm.tree.AbstractInsnNode;
import org.objectweb.asm.tree.ClassNode;
import org.objectweb.asm.tree.FieldInsnNode;
import org.objectweb.asm.tree.FieldNode;
import org.objectweb.asm.tree.InvokeDynamicInsnNode;
import org.objectweb.asm.tree.LabelNode;
import org.objectweb.asm.tree.LdcInsnNode;
import org.objectweb.asm.tree.MethodInsnNode;
import org.objectweb.asm.tree.MethodNode;
import org.objectweb.asm.tree.TryCatchBlockNode;
import org.objectweb.asm.tree.VarInsnNode;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.security.MessageDigest;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Set;
import java.util.zip.ZipEntry;
import java.util.zip.ZipInputStream;

/**
 * Read-only, ASM-only inventory of residues left by the deobfuscation passes.
 *
 * <p>This scanner intentionally reports bytecode shapes and evidence rather
 * than claiming semantic recovery.  It never defines, loads, initializes, or
 * reflectively queries a class from the input archive.</p>
 */
public final class DeobfuscationResidueScanner {
    private static final String LONG_KEY_STATE =
            ObfRuntimeNames.STATE;
    private static final String LONG_KEY_STATE_DESC =
            ObfRuntimeNames.BOOTSTRAP_DESC;
    private static final String LONG_KEY_INTERFACE =
            ObfRuntimeNames.STATE_INTERFACE;
    private static final String LONG_KEY_TRANSFORM_DESC = "(J)J";
    private static final String MEMBER_BSM_DESC =
            "(Ljava/lang/invoke/MethodHandles$Lookup;"
                    + "Ljava/lang/invoke/MutableCallSite;Ljava/lang/String;"
                    + "Ljava/lang/invoke/MethodType;JJ)"
                    + "Ljava/lang/invoke/MethodHandle;";
    private static final String STRING_INDY_DESC = "(IJ)Ljava/lang/String;";
    private static final String INTEGER_INDY_DESC = "(IJ)I";
    private static final String CIPHER_FACTORY_DESC =
            "(Ljava/lang/String;)Ljavax/crypto/Cipher;";

    private DeobfuscationResidueScanner() {
    }

    public static void main(String[] args) throws Exception {
        if (args.length != 2) {
            System.err.println("usage: DeobfuscationResidueScanner <input.jar> <output-dir>");
            System.exit(2);
        }
        scan(Paths.get(args[0]), Paths.get(args[1]));
    }

    /** Scan an archive and write classes.tsv, methods.tsv, sites.tsv and audit.txt. */
    static ScanSummary scan(Path input, Path outputDirectory) throws Exception {
        Files.createDirectories(outputDirectory);
        List<ArchiveEntry> entries = readEntries(input);
        List<ClassBytes> classEntries = new ArrayList<>();
        for (ArchiveEntry entry : entries) {
            if (!entry.directory && entry.name.endsWith(".class")) {
                classEntries.add(new ClassBytes(entry.name, entry.bytes));
            }
        }

        List<String> classRows = new ArrayList<>();
        classRows.add("class\tentry\tmethods\tclinit_instructions\t"
                + "zkm_long_key_bootstraps\tzkm_long_key_fields\tzkm_long_key_reads\t"
                + "zkm_long_key_transforms\tstring_indy\tinteger_indy\tmember_indy\t"
                + "des_pkcs5\tdes_nopadding\tmethod_handle_refs\tmutable_call_site_calls\t"
                + "bootstrap_method_refs\tbootstrap_field_refs\tidentity_rethrows\t"
                + "typed_identity_rethrows\tclassification\tparse_status");
        List<String> methodRows = new ArrayList<>();
        methodRows.add("class\tmethod\tinstructions\tclinit\tlong_key_bootstraps\t"
                + "long_key_reads\tstring_indy\tinteger_indy\tmember_indy\tdes_pkcs5\t"
                + "des_nopadding\tmethod_handle_refs\tmutable_call_site_calls\t"
                + "bootstrap_method_refs\tbootstrap_field_refs\tidentity_rethrows\t"
                + "typed_identity_rethrows");
        List<String> siteRows = new ArrayList<>();
        siteRows.add("class\tmethod\tinstruction\ttype\tdetail");

        ScanSummary summary = new ScanSummary();
        summary.archiveEntries = entries.size();
        summary.classEntries = classEntries.size();
        Map<String, ClassNode> classes = new LinkedHashMap<>();
        Map<String, String> classEntryNames = new LinkedHashMap<>();
        List<ParsedClass> parsed = new ArrayList<>();
        for (ClassBytes entry : classEntries) {
            try {
                ClassNode node = new ClassNode(Opcodes.ASM9);
                new ClassReader(entry.bytes).accept(node, ClassReader.SKIP_FRAMES);
                parsed.add(new ParsedClass(entry.entryName, node));
                classes.put(node.name, node);
                classEntryNames.put(node.name, entry.entryName);
                summary.parsedClasses++;
            } catch (Throwable failure) {
                summary.malformedClasses++;
                classRows.add(row("<unknown>", entry.entryName, 0, 0,
                        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                        "unparsed", "ERROR:" + shortReason(failure)));
            }
        }

        Map<MethodRef, String> identityMethods = identityMethods(parsed);
        Map<FieldRef, Boolean> keyFields = new LinkedHashMap<>();
        for (ParsedClass parsedClass : parsed) {
            discoverKeyFields(parsedClass.node, keyFields);
        }
        summary.zkmLongKeyFields = keyFields.size();

        for (ParsedClass parsedClass : parsed) {
            ClassStats stats = inspect(parsedClass.node, keyFields, identityMethods,
                    methodRows, siteRows, summary);
            classRows.add(row(parsedClass.node.name, parsedClass.entryName,
                    parsedClass.node.methods.size(), stats.clinitInstructions,
                    stats.longKeyBootstraps, stats.longKeyFields, stats.longKeyReads,
                    stats.longKeyTransforms, stats.stringIndy, stats.integerIndy,
                    stats.memberIndy, stats.desPkcs5, stats.desNoPadding,
                    stats.methodHandleRefs, stats.mutableCallSiteCalls,
                    stats.bootstrapMethodRefs, stats.bootstrapFieldRefs,
                    stats.identityRethrows, stats.typedIdentityRethrows,
                    stats.classification(), "OK"));
        }
        Comparator<String> natural = Comparator.naturalOrder();
        classRows.subList(1, classRows.size()).sort(natural);
        methodRows.subList(1, methodRows.size()).sort(natural);
        siteRows.subList(1, siteRows.size()).sort(natural);
        Files.write(outputDirectory.resolve("classes.tsv"), classRows, StandardCharsets.UTF_8);
        Files.write(outputDirectory.resolve("methods.tsv"), methodRows, StandardCharsets.UTF_8);
        Files.write(outputDirectory.resolve("sites.tsv"), siteRows, StandardCharsets.UTF_8);
        Files.write(outputDirectory.resolve("audit.txt"), audit(input, summary),
                StandardCharsets.UTF_8);
        Files.write(outputDirectory.resolve("gate.txt"),
                (summary.malformedClasses == 0 ? "PASS\n" : "FAIL\n")
                        .getBytes(StandardCharsets.UTF_8));
        System.out.println("entries=" + summary.archiveEntries + " classes="
                + summary.parsedClasses + "/" + summary.classEntries
                + " parse_errors=" + summary.malformedClasses + " long_key_bootstraps="
                + summary.zkmLongKeyBootstraps + " string_indy=" + summary.stringIndySites
                + " integer_indy=" + summary.integerIndySites + " member_indy="
                + summary.memberIndySites + " report=" + outputDirectory);
        return summary;
    }

    private static ClassStats inspect(ClassNode owner, Map<FieldRef, Boolean> keyFields,
                                      Map<MethodRef, String> identityMethods,
                                      List<String> methodRows, List<String> siteRows,
                                      ScanSummary summary) {
        ClassStats stats = new ClassStats();
        for (MethodNode method : owner.methods) {
            MethodStats methodStats = new MethodStats();
            methodStats.instructions = method.instructions.size();
            methodStats.clinit = "<clinit>".equals(method.name);
            if (methodStats.clinit) stats.clinitInstructions = method.instructions.size();
            int instruction = 0;
            for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
                 insn = insn.getNext(), instruction++) {
                if (insn instanceof MethodInsnNode) {
                    MethodInsnNode call = (MethodInsnNode) insn;
                    if (isLongKeyBootstrap(call)) {
                        methodStats.longKeyBootstraps++;
                        stats.longKeyBootstraps++;
                        summary.zkmLongKeyBootstraps++;
                        addSite(siteRows, owner, method, instruction,
                                "ZKM_LONG_KEY_BOOTSTRAP", call.owner + "." + call.name
                                        + call.desc);
                    }
                    if (isLongKeyTransform(call)) {
                        stats.longKeyTransforms++;
                        summary.zkmLongKeyTransforms++;
                        addSite(siteRows, owner, method, instruction,
                                "ZKM_LONG_KEY_TRANSFORM", call.owner + "." + call.name
                                        + call.desc);
                    }
                    FieldStats cipher = cipherCall(call, insn);
                    if (cipher != null) {
                        if (cipher.pkcs5) {
                            methodStats.desPkcs5++;
                            stats.desPkcs5++;
                            summary.desPkcs5Calls++;
                            addSite(siteRows, owner, method, instruction,
                                    "DES_PKCS5", cipher.algorithm + ",scope="
                                            + scope(method));
                        }
                        if (cipher.noPadding) {
                            methodStats.desNoPadding++;
                            stats.desNoPadding++;
                            summary.desNoPaddingCalls++;
                            addSite(siteRows, owner, method, instruction,
                                    "DES_NOPADDING", cipher.algorithm + ",scope="
                                            + scope(method));
                        }
                        if (methodStats.clinit) summary.desClinitCalls++;
                        else summary.desHelperCalls++;
                    }
                    if (isMethodHandleCall(call)) {
                        methodStats.methodHandleRefs++;
                        stats.methodHandleRefs++;
                        summary.methodHandleReferences++;
                        addSite(siteRows, owner, method, instruction,
                                "METHOD_HANDLE_CALL", call.owner + "." + call.name
                                        + call.desc);
                    }
                    if ("java/lang/invoke/MutableCallSite".equals(call.owner)) {
                        methodStats.mutableCallSiteCalls++;
                        stats.mutableCallSiteCalls++;
                        summary.mutableCallSiteCalls++;
                        addSite(siteRows, owner, method, instruction,
                                "MUTABLE_CALL_SITE", call.name + call.desc);
                    }
                } else if (insn instanceof FieldInsnNode) {
                    FieldInsnNode field = (FieldInsnNode) insn;
                    FieldRef ref = new FieldRef(field.owner, field.name, field.desc);
                    if (insn.getOpcode() == Opcodes.GETSTATIC && keyFields.containsKey(ref)) {
                        methodStats.longKeyReads++;
                        stats.longKeyReads++;
                        summary.zkmLongKeyReads++;
                        addSite(siteRows, owner, method, instruction,
                                "ZKM_LONG_KEY_READ", field.owner + "." + field.name
                                        + field.desc);
                    }
                } else if (insn instanceof InvokeDynamicInsnNode) {
                    InvokeDynamicInsnNode indy = (InvokeDynamicInsnNode) insn;
                    if (STRING_INDY_DESC.equals(indy.desc)) {
                        methodStats.stringIndy++;
                        stats.stringIndy++;
                        summary.stringIndySites++;
                        addSite(siteRows, owner, method, instruction, "STRING_INDY_IJ",
                                indy.name + indy.desc + ",bsm=" + handle(indy.bsm));
                    }
                    if (INTEGER_INDY_DESC.equals(indy.desc)) {
                        methodStats.integerIndy++;
                        stats.integerIndy++;
                        summary.integerIndySites++;
                        addSite(siteRows, owner, method, instruction, "INTEGER_INDY_IJ",
                                indy.name + indy.desc + ",bsm=" + handle(indy.bsm));
                    }
                    if (isMemberIndy(indy, owner.name)) {
                        methodStats.memberIndy++;
                        stats.memberIndy++;
                        summary.memberIndySites++;
                        addSite(siteRows, owner, method, instruction,
                                "MEMBER_INDY_TRAILING_JJ", indy.name + indy.desc
                                        + ",bsm=" + handle(indy.bsm));
                    }
                    int methodRefs = bootstrapMethodReferences(indy, owner, method,
                            instruction, siteRows, summary);
                    int fieldRefs = bootstrapFieldReferences(indy, owner, method,
                            instruction, siteRows, summary);
                    methodStats.bootstrapMethodRefs += methodRefs;
                    methodStats.bootstrapFieldRefs += fieldRefs;
                    stats.bootstrapMethodRefs += methodRefs;
                    stats.bootstrapFieldRefs += fieldRefs;
                } else if (insn instanceof LdcInsnNode) {
                    Object constant = ((LdcInsnNode) insn).cst;
                    if (constant instanceof Handle) {
                        Handle handle = (Handle) constant;
                        if (isMethodHandleTag(handle.getTag())) {
                            methodStats.methodHandleRefs++;
                            stats.methodHandleRefs++;
                            summary.methodHandleReferences++;
                            addSite(siteRows, owner, method, instruction,
                                    "METHOD_HANDLE_REF", handle(handle));
                        } else if (isFieldHandleTag(handle.getTag())) {
                            methodStats.bootstrapFieldRefs++;
                            stats.bootstrapFieldRefs++;
                            summary.bootstrapFieldReferences++;
                            addSite(siteRows, owner, method, instruction,
                                    "FIELD_HANDLE_REF", handle(handle));
                        }
                    } else if (constant instanceof ConstantDynamic) {
                        ConstantDynamic dynamic = (ConstantDynamic) constant;
                        Handle bsm = dynamic.getBootstrapMethod();
                        if (bsm != null) {
                            if (isMethodHandleTag(bsm.getTag())) {
                                methodStats.bootstrapMethodRefs++;
                                stats.bootstrapMethodRefs++;
                                summary.bootstrapMethodReferences++;
                                addSite(siteRows, owner, method, instruction,
                                        "BOOTSTRAP_METHOD_REF", handle(bsm));
                            } else if (isFieldHandleTag(bsm.getTag())) {
                                methodStats.bootstrapFieldRefs++;
                                stats.bootstrapFieldRefs++;
                                summary.bootstrapFieldReferences++;
                                addSite(siteRows, owner, method, instruction,
                                        "BOOTSTRAP_FIELD_REF", handle(bsm));
                            }
                        }
                    }
                }
            }
            IdentityCount identity = identityHandlers(owner, method, identityMethods,
                    siteRows, summary);
            methodStats.identityRethrows = identity.total;
            methodStats.typedIdentityRethrows = identity.typed;
            stats.identityRethrows += identity.total;
            stats.typedIdentityRethrows += identity.typed;
            summary.identityRethrowHandlers += identity.total;
            summary.typedIdentityRethrowHandlers += identity.typed;
            methodRows.add(row(owner.name, method.name + method.desc,
                    methodStats.instructions, methodStats.clinit,
                    methodStats.longKeyBootstraps, methodStats.longKeyReads,
                    methodStats.stringIndy, methodStats.integerIndy, methodStats.memberIndy,
                    methodStats.desPkcs5, methodStats.desNoPadding,
                    methodStats.methodHandleRefs, methodStats.mutableCallSiteCalls,
                    methodStats.bootstrapMethodRefs, methodStats.bootstrapFieldRefs,
                    methodStats.identityRethrows, methodStats.typedIdentityRethrows));
        }
        stats.longKeyFields = countOwnerKeyFields(owner, keyFields);
        summary.zkmLongKeyFields += 0; // fields are counted once during discovery
        return stats;
    }

    private static int bootstrapMethodReferences(InvokeDynamicInsnNode indy,
                                                  ClassNode owner, MethodNode method,
                                                  int instruction, List<String> sites,
                                                  ScanSummary summary) {
        int count = 0;
        if (indy.bsm != null && isMethodHandleTag(indy.bsm.getTag())) {
            count++;
            summary.bootstrapMethodReferences++;
            addSite(sites, owner, method, instruction, "BOOTSTRAP_METHOD_REF",
                    handle(indy.bsm));
        }
        if (indy.bsmArgs != null) {
            for (Object argument : indy.bsmArgs) {
                if (argument instanceof Handle) {
                    Handle value = (Handle) argument;
                    if (isMethodHandleTag(value.getTag())) {
                        count++;
                        summary.bootstrapMethodReferences++;
                        addSite(sites, owner, method, instruction,
                                "BOOTSTRAP_METHOD_REF", handle(value));
                    }
                } else if (argument instanceof ConstantDynamic) {
                    ConstantDynamic value = (ConstantDynamic) argument;
                    Handle bsm = value.getBootstrapMethod();
                    if (bsm != null && isMethodHandleTag(bsm.getTag())) {
                        count++;
                        summary.bootstrapMethodReferences++;
                        addSite(sites, owner, method, instruction,
                                "BOOTSTRAP_METHOD_REF", handle(bsm));
                    }
                }
            }
        }
        return count;
    }

    private static int bootstrapFieldReferences(InvokeDynamicInsnNode indy,
                                                 ClassNode owner, MethodNode method,
                                                 int instruction, List<String> sites,
                                                 ScanSummary summary) {
        int count = 0;
        List<Handle> handles = new ArrayList<>();
        if (indy.bsm != null) handles.add(indy.bsm);
        if (indy.bsmArgs != null) {
            for (Object argument : indy.bsmArgs) if (argument instanceof Handle) {
                handles.add((Handle) argument);
            }
        }
        for (Handle value : handles) {
            if (!isFieldHandleTag(value.getTag())) continue;
            count++;
            summary.bootstrapFieldReferences++;
            addSite(sites, owner, method, instruction, "BOOTSTRAP_FIELD_REF",
                    handle(value));
        }
        return count;
    }

    private static Map<MethodRef, String> identityMethods(List<ParsedClass> parsed) {
        Map<MethodRef, String> result = new LinkedHashMap<>();
        for (ParsedClass parsedClass : parsed) {
            for (MethodNode method : parsedClass.node.methods) {
                Type[] args = Type.getArgumentTypes(method.desc);
                Type returnType = Type.getReturnType(method.desc);
                if ((method.access & Opcodes.ACC_STATIC) == 0 || args.length != 1
                        || args[0].getSort() != Type.OBJECT || !args[0].equals(returnType)) {
                    continue;
                }
                List<AbstractInsnNode> code = code(method);
                if (code.size() == 2 && code.get(0) instanceof VarInsnNode
                        && code.get(0).getOpcode() == Opcodes.ALOAD
                        && ((VarInsnNode) code.get(0)).var == 0
                        && code.get(1).getOpcode() == Opcodes.ARETURN) {
                    result.put(new MethodRef(parsedClass.node.name, method.name, method.desc),
                            args[0].getInternalName());
                }
            }
        }
        return result;
    }

    private static IdentityCount identityHandlers(ClassNode owner, MethodNode method,
                                                    Map<MethodRef, String> identities,
                                                    List<String> sites, ScanSummary summary) {
        IdentityCount result = new IdentityCount();
        for (TryCatchBlockNode block : method.tryCatchBlocks) {
            List<AbstractInsnNode> code = handlerCode(method, block.handler);
            if (code.isEmpty()) continue;
            MethodInsnNode call = null;
            int index = -1;
            if (code.get(0) instanceof MethodInsnNode) {
                call = (MethodInsnNode) code.get(0);
                index = instructionIndex(method, code.get(0));
            } else if (code.size() >= 3 && code.get(0) instanceof VarInsnNode
                    && code.get(0).getOpcode() == Opcodes.ASTORE
                    && code.get(1) instanceof VarInsnNode
                    && code.get(1).getOpcode() == Opcodes.ALOAD
                    && ((VarInsnNode) code.get(0)).var == ((VarInsnNode) code.get(1)).var
                    && code.get(2) instanceof MethodInsnNode) {
                call = (MethodInsnNode) code.get(2);
                index = instructionIndex(method, code.get(2));
            }
            if (call == null || call.getOpcode() != Opcodes.INVOKESTATIC
                    || codeAfterCall(code, call) == null
                    || codeAfterCall(code, call).getOpcode() != Opcodes.ATHROW) continue;
            MethodRef target = new MethodRef(call.owner, call.name, call.desc);
            String identityType = identities.get(target);
            if (identityType == null) continue;
            Type[] args = Type.getArgumentTypes(call.desc);
            if (args.length != 1 || !Type.getReturnType(call.desc).equals(args[0])) continue;
            if (block.type != null && !block.type.equals(identityType)) continue;
            if (block.type == null && !"java/lang/Throwable".equals(identityType)) continue;
            result.total++;
            if (!"java/lang/Throwable".equals(identityType)) result.typed++;
            addSite(sites, owner, method, index < 0 ? 0 : index,
                    "IDENTITY_RETHROW_HANDLER",
                    "catch=" + (block.type == null ? "<any>" : block.type)
                            + ",identity=" + call.owner + "." + call.name + call.desc
                            + ",typed=" + (!"java/lang/Throwable".equals(identityType)));
        }
        return result;
    }

    private static AbstractInsnNode codeAfterCall(List<AbstractInsnNode> code,
                                                   MethodInsnNode call) {
        for (int i = 0; i < code.size(); i++) if (code.get(i) == call) {
            return i + 1 < code.size() ? code.get(i + 1) : null;
        }
        return null;
    }

    private static List<AbstractInsnNode> handlerCode(MethodNode method, LabelNode handler) {
        List<AbstractInsnNode> result = new ArrayList<>();
        boolean started = false;
        for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
             insn = insn.getNext()) {
            if (insn == handler) started = true;
            if (!started) continue;
            if (insn.getOpcode() >= 0) result.add(insn);
            if (result.size() >= 8) break;
        }
        return result;
    }

    private static void discoverKeyFields(ClassNode owner, Map<FieldRef, Boolean> result) {
        MethodNode clinit = method(owner, "<clinit>", "()V");
        if (clinit == null) return;
        for (AbstractInsnNode insn = clinit.instructions.getFirst(); insn != null;
             insn = insn.getNext()) {
            if (!(insn instanceof FieldInsnNode) || insn.getOpcode() != Opcodes.PUTSTATIC) continue;
            FieldInsnNode write = (FieldInsnNode) insn;
            if (!owner.name.equals(write.owner) || !"J".equals(write.desc)) continue;
            AbstractInsnNode transform = previousCode(write);
            AbstractInsnNode transformInput = previousCode(transform);
            AbstractInsnNode bootstrap = previousCode(transformInput);
            if (isLongKeyTransform(transform) && longConstant(transformInput) != null
                    && isLongKeyBootstrap(bootstrap) && keyBootstrapStart(bootstrap) != null) {
                result.put(new FieldRef(write.owner, write.name, write.desc), Boolean.TRUE);
            }
        }
    }

    private static int countOwnerKeyFields(ClassNode owner, Map<FieldRef, Boolean> fields) {
        int count = 0;
        for (FieldNode field : owner.fields) if (fields.containsKey(
                new FieldRef(owner.name, field.name, field.desc))) count++;
        return count;
    }

    private static boolean isLongKeyBootstrap(AbstractInsnNode insn) {
        if (!(insn instanceof MethodInsnNode)) return false;
        MethodInsnNode call = (MethodInsnNode) insn;
        return call.getOpcode() == Opcodes.INVOKESTATIC && LONG_KEY_STATE.equals(call.owner)
                && "a".equals(call.name) && LONG_KEY_STATE_DESC.equals(call.desc);
    }

    private static boolean isLongKeyTransform(AbstractInsnNode insn) {
        if (!(insn instanceof MethodInsnNode)) return false;
        MethodInsnNode call = (MethodInsnNode) insn;
        return call.getOpcode() == Opcodes.INVOKEINTERFACE
                && LONG_KEY_INTERFACE.equals(call.owner) && "a".equals(call.name)
                && LONG_KEY_TRANSFORM_DESC.equals(call.desc);
    }

    private static AbstractInsnNode keyBootstrapStart(AbstractInsnNode bootstrap) {
        AbstractInsnNode ownerArg = previousCode(bootstrap);
        AbstractInsnNode seedB = null;
        if (ownerArg != null && ownerArg.getOpcode() == Opcodes.ACONST_NULL) {
            seedB = previousCode(ownerArg);
        } else if (ownerArg instanceof MethodInsnNode) {
            MethodInsnNode lookupClass = (MethodInsnNode) ownerArg;
            if (lookupClass.getOpcode() == Opcodes.INVOKEVIRTUAL
                    && "java/lang/invoke/MethodHandles$Lookup".equals(lookupClass.owner)
                    && "lookupClass".equals(lookupClass.name)
                    && "()Ljava/lang/Class;".equals(lookupClass.desc)) {
                AbstractInsnNode lookup = previousCode(ownerArg);
                if (lookup instanceof MethodInsnNode) {
                    MethodInsnNode call = (MethodInsnNode) lookup;
                    if (call.getOpcode() == Opcodes.INVOKESTATIC
                            && "java/lang/invoke/MethodHandles".equals(call.owner)
                            && "lookup".equals(call.name)
                            && "()Ljava/lang/invoke/MethodHandles$Lookup;".equals(call.desc)) {
                        seedB = previousCode(lookup);
                    }
                }
            }
        }
        AbstractInsnNode seedA = previousCode(seedB);
        return longConstant(seedA) != null && longConstant(seedB) != null ? seedA : null;
    }

    private static FieldStats cipherCall(MethodInsnNode call, AbstractInsnNode insn) {
        if (call.getOpcode() != Opcodes.INVOKESTATIC
                || !"javax/crypto/Cipher".equals(call.owner)
                || !"getInstance".equals(call.name)
                || !CIPHER_FACTORY_DESC.equals(call.desc)) return null;
        String algorithm = precedingString(insn);
        if (algorithm == null || !algorithm.startsWith("DES/")) return null;
        return new FieldStats(algorithm, algorithm.contains("PKCS5Padding"),
                algorithm.contains("NoPadding"));
    }

    private static boolean isMemberIndy(InvokeDynamicInsnNode indy, String owner) {
        Type[] args = Type.getArgumentTypes(indy.desc);
        if (args.length < 2 || !Type.LONG_TYPE.equals(args[args.length - 1])
                || !Type.LONG_TYPE.equals(args[args.length - 2])) return false;
        return indy.bsm != null && indy.bsm.getTag() == Opcodes.H_INVOKESTATIC
                && owner.equals(indy.bsm.getOwner())
                && MEMBER_BSM_DESC.equals(indy.bsm.getDesc());
    }

    private static boolean isMethodHandleCall(MethodInsnNode call) {
        return call.owner.startsWith("java/lang/invoke/MethodHandle")
                || call.owner.startsWith("java/lang/invoke/MethodHandles$")
                || "java/lang/invoke/MethodHandles".equals(call.owner)
                || "java/lang/invoke/CallSite".equals(call.owner);
    }

    private static boolean isMethodHandleTag(int tag) {
        return tag == Opcodes.H_INVOKEVIRTUAL || tag == Opcodes.H_INVOKESTATIC
                || tag == Opcodes.H_INVOKESPECIAL || tag == Opcodes.H_NEWINVOKESPECIAL
                || tag == Opcodes.H_INVOKEINTERFACE;
    }

    private static boolean isFieldHandleTag(int tag) {
        return tag == Opcodes.H_GETFIELD || tag == Opcodes.H_GETSTATIC
                || tag == Opcodes.H_PUTFIELD || tag == Opcodes.H_PUTSTATIC;
    }

    private static String precedingString(AbstractInsnNode insn) {
        AbstractInsnNode previous = previousCode(insn);
        return previous instanceof LdcInsnNode && ((LdcInsnNode) previous).cst instanceof String
                ? (String) ((LdcInsnNode) previous).cst : null;
    }

    private static AbstractInsnNode previousCode(AbstractInsnNode insn) {
        if (insn == null) return null;
        AbstractInsnNode previous = insn.getPrevious();
        while (previous != null && previous.getOpcode() < 0) previous = previous.getPrevious();
        return previous;
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

    private static List<AbstractInsnNode> code(MethodNode method) {
        List<AbstractInsnNode> result = new ArrayList<>();
        for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
             insn = insn.getNext()) if (insn.getOpcode() >= 0) result.add(insn);
        return result;
    }

    private static int instructionIndex(MethodNode method, AbstractInsnNode target) {
        int index = 0;
        for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
             insn = insn.getNext(), index++) if (insn == target) return index;
        return -1;
    }

    private static MethodNode method(ClassNode owner, String name, String desc) {
        for (MethodNode method : owner.methods) if (name.equals(method.name)
                && desc.equals(method.desc)) return method;
        return null;
    }

    private static String scope(MethodNode method) {
        return "<clinit>".equals(method.name) ? "clinit" : "helper";
    }

    private static void addSite(List<String> sites, ClassNode owner, MethodNode method,
                                int instruction, String type, String detail) {
        sites.add(row(owner.name, method.name + method.desc, instruction, type, detail));
    }

    private static List<String> audit(Path input, ScanSummary summary) throws Exception {
        List<String> rows = new ArrayList<>();
        rows.add("input=" + input.toAbsolutePath());
        rows.add("input_sha256=" + sha256(input));
        rows.add("archive_entries=" + summary.archiveEntries);
        rows.add("class_entries=" + summary.classEntries);
        rows.add("parsed_classes=" + summary.parsedClasses);
        rows.add("malformed_classes=" + summary.malformedClasses);
        rows.add("zkm_long_key_bootstraps=" + summary.zkmLongKeyBootstraps);
        rows.add("zkm_long_key_fields=" + summary.zkmLongKeyFields);
        rows.add("zkm_long_key_reads=" + summary.zkmLongKeyReads);
        rows.add("zkm_long_key_transforms=" + summary.zkmLongKeyTransforms);
        rows.add("string_indy_ij_string=" + summary.stringIndySites);
        rows.add("integer_indy_ij_int=" + summary.integerIndySites);
        rows.add("member_indy_trailing_jj=" + summary.memberIndySites);
        rows.add("des_pkcs5_calls=" + summary.desPkcs5Calls);
        rows.add("des_nopadding_calls=" + summary.desNoPaddingCalls);
        rows.add("des_clinit_calls=" + summary.desClinitCalls);
        rows.add("des_helper_calls=" + summary.desHelperCalls);
        rows.add("method_handle_references=" + summary.methodHandleReferences);
        rows.add("mutable_call_site_calls=" + summary.mutableCallSiteCalls);
        rows.add("bootstrap_method_references=" + summary.bootstrapMethodReferences);
        rows.add("bootstrap_field_references=" + summary.bootstrapFieldReferences);
        rows.add("identity_rethrow_handlers=" + summary.identityRethrowHandlers);
        rows.add("typed_identity_rethrow_handlers=" + summary.typedIdentityRethrowHandlers);
        rows.add("input_classes_loaded=false");
        rows.add("input_classes_initialized=false");
        rows.add("cfr_structuring_claims=false");
        rows.add("gate=" + (summary.malformedClasses == 0 ? "PASS" : "FAIL"));
        return rows;
    }

    private static String row(Object... values) {
        StringBuilder result = new StringBuilder();
        for (Object value : values) {
            if (result.length() > 0) result.append('\t');
            result.append(sanitize(String.valueOf(value)));
        }
        return result.toString();
    }

    private static String sanitize(String value) {
        return value.replace('\t', ' ').replace('\r', ' ').replace('\n', ' ');
    }

    private static String handle(Handle value) {
        return value == null ? "<none>" : value.getOwner() + "." + value.getName()
                + value.getDesc() + "#tag=" + value.getTag();
    }

    private static String shortReason(Throwable failure) {
        String reason = failure.getClass().getSimpleName() + ":" + failure.getMessage();
        reason = sanitize(reason);
        return reason.substring(0, Math.min(reason.length(), 180));
    }

    private static String sha256(Path path) throws Exception {
        MessageDigest digest = MessageDigest.getInstance("SHA-256");
        try (InputStream input = Files.newInputStream(path)) {
            byte[] buffer = new byte[8192];
            int count;
            while ((count = input.read(buffer)) >= 0) digest.update(buffer, 0, count);
        }
        StringBuilder result = new StringBuilder();
        for (byte value : digest.digest()) result.append(String.format(Locale.ROOT, "%02X",
                value & 0xff));
        return result.toString();
    }

    private static List<ArchiveEntry> readEntries(Path input) throws IOException {
        List<ArchiveEntry> result = new ArrayList<>();
        try (ZipInputStream stream = new ZipInputStream(Files.newInputStream(input))) {
            ZipEntry entry;
            while ((entry = stream.getNextEntry()) != null) {
                if (entry.isDirectory()) {
                    result.add(new ArchiveEntry(entry.getName(), true, new byte[0]));
                } else {
                    result.add(new ArchiveEntry(entry.getName(), false, readAll(stream)));
                }
            }
        }
        return result;
    }

    private static byte[] readAll(InputStream input) throws IOException {
        ByteArrayOutputStream output = new ByteArrayOutputStream();
        byte[] buffer = new byte[8192];
        int count;
        while ((count = input.read(buffer)) >= 0) output.write(buffer, 0, count);
        return output.toByteArray();
    }

    static final class ScanSummary {
        int archiveEntries;
        int classEntries;
        int parsedClasses;
        int malformedClasses;
        int zkmLongKeyBootstraps;
        int zkmLongKeyFields;
        int zkmLongKeyReads;
        int zkmLongKeyTransforms;
        int stringIndySites;
        int integerIndySites;
        int memberIndySites;
        int desPkcs5Calls;
        int desNoPaddingCalls;
        int desClinitCalls;
        int desHelperCalls;
        int methodHandleReferences;
        int mutableCallSiteCalls;
        int bootstrapMethodReferences;
        int bootstrapFieldReferences;
        int identityRethrowHandlers;
        int typedIdentityRethrowHandlers;
    }

    private static final class ParsedClass {
        final String entryName;
        final ClassNode node;

        ParsedClass(String entryName, ClassNode node) {
            this.entryName = entryName;
            this.node = node;
        }
    }

    private static final class ClassBytes {
        final String entryName;
        final byte[] bytes;

        ClassBytes(String entryName, byte[] bytes) {
            this.entryName = entryName;
            this.bytes = bytes;
        }
    }

    private static final class ArchiveEntry {
        final String name;
        final boolean directory;
        final byte[] bytes;

        ArchiveEntry(String name, boolean directory, byte[] bytes) {
            this.name = name;
            this.directory = directory;
            this.bytes = bytes;
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

        @Override public boolean equals(Object other) {
            if (!(other instanceof MethodRef)) return false;
            MethodRef value = (MethodRef) other;
            return owner.equals(value.owner) && name.equals(value.name)
                    && desc.equals(value.desc);
        }

        @Override public int hashCode() {
            return (owner.hashCode() * 31 + name.hashCode()) * 31 + desc.hashCode();
        }
    }

    private static final class FieldRef {
        final String owner;
        final String name;
        final String desc;

        FieldRef(String owner, String name, String desc) {
            this.owner = owner;
            this.name = name;
            this.desc = desc;
        }

        @Override public boolean equals(Object other) {
            if (!(other instanceof FieldRef)) return false;
            FieldRef value = (FieldRef) other;
            return owner.equals(value.owner) && name.equals(value.name)
                    && desc.equals(value.desc);
        }

        @Override public int hashCode() {
            return (owner.hashCode() * 31 + name.hashCode()) * 31 + desc.hashCode();
        }
    }

    private static final class ClassStats {
        int clinitInstructions;
        int longKeyBootstraps;
        int longKeyTransforms;
        int longKeyFields;
        int longKeyReads;
        int stringIndy;
        int integerIndy;
        int memberIndy;
        int desPkcs5;
        int desNoPadding;
        int methodHandleRefs;
        int mutableCallSiteCalls;
        int bootstrapMethodRefs;
        int bootstrapFieldRefs;
        int identityRethrows;
        int typedIdentityRethrows;

        String classification() {
            if (longKeyBootstraps > 0 || longKeyFields > 0 || longKeyReads > 0) return "long_key";
            if (stringIndy > 0 || integerIndy > 0 || memberIndy > 0) return "indy";
            if (desPkcs5 > 0 || desNoPadding > 0) return "des";
            if (identityRethrows > 0) return "identity_rethrow";
            if (methodHandleRefs > 0 || mutableCallSiteCalls > 0) return "invoke_support";
            return "none";
        }
    }

    private static final class MethodStats {
        int instructions;
        boolean clinit;
        int longKeyBootstraps;
        int longKeyReads;
        int stringIndy;
        int integerIndy;
        int memberIndy;
        int desPkcs5;
        int desNoPadding;
        int methodHandleRefs;
        int mutableCallSiteCalls;
        int bootstrapMethodRefs;
        int bootstrapFieldRefs;
        int identityRethrows;
        int typedIdentityRethrows;
    }

    private static final class IdentityCount {
        int total;
        int typed;
    }

    private static final class FieldStats {
        final String algorithm;
        final boolean pkcs5;
        final boolean noPadding;

        FieldStats(String algorithm, boolean pkcs5, boolean noPadding) {
            this.algorithm = algorithm;
            this.pkcs5 = pkcs5;
            this.noPadding = noPadding;
        }
    }
}
