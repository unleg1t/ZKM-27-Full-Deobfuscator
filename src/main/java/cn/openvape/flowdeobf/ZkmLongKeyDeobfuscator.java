package cn.openvape.flowdeobf;

import org.objectweb.asm.ClassReader;
import org.objectweb.asm.ClassWriter;
import org.objectweb.asm.Opcodes;
import org.objectweb.asm.commons.JSRInlinerAdapter;
import org.objectweb.asm.tree.AbstractInsnNode;
import org.objectweb.asm.tree.ClassNode;
import org.objectweb.asm.tree.FieldInsnNode;
import org.objectweb.asm.tree.FieldNode;
import org.objectweb.asm.tree.FrameNode;
import org.objectweb.asm.tree.InsnNode;
import org.objectweb.asm.tree.IntInsnNode;
import org.objectweb.asm.tree.InvokeDynamicInsnNode;
import org.objectweb.asm.tree.JumpInsnNode;
import org.objectweb.asm.tree.LabelNode;
import org.objectweb.asm.tree.LdcInsnNode;
import org.objectweb.asm.tree.LookupSwitchInsnNode;
import org.objectweb.asm.tree.MethodInsnNode;
import org.objectweb.asm.tree.MethodNode;
import org.objectweb.asm.tree.TableSwitchInsnNode;
import org.objectweb.asm.tree.TryCatchBlockNode;
import org.objectweb.asm.tree.VarInsnNode;
import org.objectweb.asm.tree.analysis.Analyzer;
import org.objectweb.asm.tree.analysis.BasicVerifier;
import org.objectweb.asm.tree.analysis.Frame;
import org.objectweb.asm.tree.analysis.SourceInterpreter;
import org.objectweb.asm.tree.analysis.SourceValue;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.AtomicMoveNotSupportedException;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.StandardCopyOption;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Set;
import java.util.zip.CRC32;
import java.util.zip.ZipEntry;
import java.util.zip.ZipInputStream;
import java.util.zip.ZipOutputStream;

/**
 * Archive-transactional deobfuscation of ZKM long class keys.
 *
 * <p>A class-key bootstrap must be selected by independent string-table or
 * member-resolution evidence before this pass changes its owner. Static key
 * reads and method-local derived keys are replaced with constants, pure
 * argument-evaluation residues left by the string/integer rewriters are
 * removed, and the now-unnecessary key field/bootstrap is deleted. Owners
 * without evidence remain byte-for-byte unchanged. No sample class is loaded
 * or initialized.</p>
 */
public final class ZkmLongKeyDeobfuscator {
    private static final String STATE = ObfRuntimeNames.STATE;
    private static final String STATE_INTERFACE =
            ObfRuntimeNames.STATE_INTERFACE;
    private static final String KEY_BOOTSTRAP_DESC =
            ObfRuntimeNames.BOOTSTRAP_DESC;

    private ZkmLongKeyDeobfuscator() {
    }

    public static void main(String[] args) throws Exception {
        if (args.length < 2 || args.length > 4) {
            System.err.println("usage: ZkmLongKeyDeobfuscator <input.jar> <report-dir>"
                    + " [rewritten.jar] [--residual-integer-oracle]");
            System.exit(2);
        }
        Path rewrittenOutput = null;
        boolean residualIntegerOracle = false;
        for (int index = 2; index < args.length; index++) {
            if ("--residual-integer-oracle".equals(args[index])) {
                if (residualIntegerOracle) {
                    throw new IllegalArgumentException("duplicate --residual-integer-oracle");
                }
                residualIntegerOracle = true;
            } else if (rewrittenOutput == null) {
                rewrittenOutput = Paths.get(args[index]);
            } else {
                throw new IllegalArgumentException("unknown option: " + args[index]);
            }
        }
        deobfuscate(Paths.get(args[0]), Paths.get(args[1]), rewrittenOutput,
                residualIntegerOracle);
    }

    static Summary deobfuscate(Path input, Path reportDirectory,
                               Path rewrittenOutput) throws Exception {
        return deobfuscate(input, reportDirectory, rewrittenOutput, false);
    }

    static Summary deobfuscate(Path input, Path reportDirectory,
                               Path rewrittenOutput, boolean residualIntegerOracle)
            throws Exception {
        Files.createDirectories(reportDirectory);
        if (rewrittenOutput != null) {
            Path normalizedInput = input.toAbsolutePath().normalize();
            Path normalizedOutput = rewrittenOutput.toAbsolutePath().normalize();
            if (normalizedInput.equals(normalizedOutput)) {
                throw new IllegalArgumentException("rewritten output must not replace input");
            }
            if (normalizedOutput.getParent() != null) {
                Files.createDirectories(normalizedOutput.getParent());
            }
        }

        List<EntryBytes> entries = readEntries(input);
        Map<String, ClassNode> classes = readClasses(entries);
        ZkmClassKeySelector.Selection keySelection = residualIntegerOracle
                ? ZkmClassKeySelector.selectResidual(classes)
                : ZkmClassKeySelector.select(classes);
        Map<String, Long> evaluatedKeys = new LinkedHashMap<>(keySelection.selectedKeys());
        Map<FieldRef, KeyBootstrap> allFieldBootstraps = findKeyBootstraps(classes);
        Map<String, DirectKeyBootstrap> allDirectBootstraps =
                findDirectKeyBootstraps(classes);
        Set<String> classifiedKeyOwners = new LinkedHashSet<>();
        for (FieldRef field : allFieldBootstraps.keySet()) {
            classifiedKeyOwners.add(field.owner);
        }
        classifiedKeyOwners.addAll(allDirectBootstraps.keySet());
        Map<String, StackKeyBootstrap> allStackBootstraps =
                findStackKeyBootstraps(classes, classifiedKeyOwners);
        Set<String> selectedOwners = evaluatedKeys.keySet();
        Map<FieldRef, KeyBootstrap> bootstraps = selectFieldBootstraps(
                allFieldBootstraps, selectedOwners);
        Map<String, DirectKeyBootstrap> directBootstraps = selectOwnerBootstraps(
                allDirectBootstraps, selectedOwners);
        Map<String, StackKeyBootstrap> stackBootstraps = selectOwnerBootstraps(
                allStackBootstraps, selectedOwners);
        Summary summary = new Summary();
        summary.residualIntegerOracle = residualIntegerOracle;
        summary.parsedClasses = classes.size();
        summary.evaluatedKeys = evaluatedKeys.size();
        summary.validatedKeys = keySelection.validatedKeys;
        summary.memberSelectedKeys = keySelection.memberSelected;
        summary.integerSelectedKeys = keySelection.integerSelected;
        summary.detectedKeyBootstraps = allFieldBootstraps.size()
                + allDirectBootstraps.size() + allStackBootstraps.size();
        summary.fieldKeyBootstraps = bootstraps.size();
        summary.directKeyBootstraps = directBootstraps.size();
        summary.stackKeyBootstraps = stackBootstraps.size();
        summary.keyBootstraps = bootstraps.size() + directBootstraps.size()
                + stackBootstraps.size();
        summary.deferredKeyBootstraps = summary.detectedKeyBootstraps
                - summary.keyBootstraps;

        List<String> rows = new ArrayList<>();
        rows.add("class\tmethod\tinstruction\taction\tfield\tvalue\treason");
        if (keySelection.validatedMemberFail != 0
                || keySelection.memberAmbiguous != 0
                || keySelection.memberRejected != 0) {
            summary.coverageErrors++;
            rows.add(tsv("<archive>", "<selector>", -1, "reject", "", "",
                    "member-key-selection-failed"));
            writeReports(input, reportDirectory, rewrittenOutput, summary, rows);
            return summary;
        }
        List<String> failures = validateCoverage(classes, evaluatedKeys, bootstraps,
                directBootstraps, stackBootstraps);
        if (!failures.isEmpty()) {
            summary.coverageErrors = failures.size();
            rows.addAll(failures);
            writeReports(input, reportDirectory, rewrittenOutput, summary, rows);
            return summary;
        }

        for (Map.Entry<FieldRef, KeyBootstrap> entry : bootstraps.entrySet()) {
            FieldRef field = entry.getKey();
            Long key = evaluatedKeys.get(field.owner);
            summary.keyReadsInlined += inlineKeyReads(classes, field, key, rows);
        }
        for (Map.Entry<FieldRef, KeyBootstrap> entry : bootstraps.entrySet()) {
            FieldRef field = entry.getKey();
            KeyBootstrap bootstrap = entry.getValue();
            removeCodeRange(bootstrap.method, bootstrap.start, bootstrap.write);
            ClassNode owner = classes.get(field.owner);
            owner.fields.remove(bootstrap.field);
            if ((bootstrap.field.access & Opcodes.ACC_PUBLIC) != 0) {
                summary.publicKeyFieldsRemoved++;
            }
            summary.keyBootstrapsRemoved++;
            summary.keyFieldsRemoved++;
            rows.add(tsv(field.owner, "<clinit>()V", bootstrap.instruction,
                    "remove-key-bootstrap", field.name, hex(evaluatedKeys.get(field.owner)),
                    "all-archive-keys-evaluated"));
        }
        for (Map.Entry<String, DirectKeyBootstrap> entry : directBootstraps.entrySet()) {
            String owner = entry.getKey();
            DirectKeyBootstrap bootstrap = entry.getValue();
            long value = evaluatedKeys.get(owner) ^ bootstrap.mask;
            summary.directKeyReadsInlined += inlineDirectKeyBootstrap(owner, bootstrap,
                    value, rows);
            summary.keyBootstrapsRemoved++;
            summary.directKeyBootstrapsRemoved++;
        }
        for (Map.Entry<String, StackKeyBootstrap> entry : stackBootstraps.entrySet()) {
            String owner = entry.getKey();
            StackKeyBootstrap bootstrap = entry.getValue();
            long value = evaluatedKeys.get(owner) ^ bootstrap.mask;
            summary.stackKeyReadsInlined += inlineStackKeyBootstrap(owner, bootstrap,
                    value, rows);
            summary.keyBootstrapsRemoved++;
            summary.stackKeyBootstrapsReplaced++;
        }

        for (ClassNode owner : classes.values()) {
            Long classKey = evaluatedKeys.get(owner.name);
            if (classKey == null) continue;
            for (MethodNode method : owner.methods) {
                if (method.instructions == null || method.instructions.size() == 0) continue;
                summary.methodKeysInlined += inlineMethodKeys(owner.name, method,
                        classKey, rows);
                int removed;
                do {
                    removed = removeRestoredArgumentResidues(owner.name, method, rows);
                    if (removed == 0) {
                        removed = removeDataflowRestoredArgumentResidue(owner.name,
                                method, rows);
                        summary.dataflowResiduesRemoved += removed;
                    }
                    summary.argumentResiduesRemoved += removed;
                } while (removed != 0);
            }
        }

        summary.remainingKeyFields = countKeyFields(classes, bootstraps.keySet());
        summary.remainingKeyBootstraps = countKeyBootstrapCalls(classes, selectedOwners);
        summary.remainingKeyReads = countFieldReads(classes, bootstraps.keySet());
        summary.remainingResidues = countRestoredArgumentResidues(classes, selectedOwners);
        if (summary.remainingKeyFields != 0 || summary.remainingKeyBootstraps != 0
                || summary.remainingKeyReads != 0) {
            summary.coverageErrors++;
            rows.add(tsv("<archive>", "<gate>", -1, "reject", "", "",
                    "remaining-key-structure"));
            writeReports(input, reportDirectory, rewrittenOutput, summary, rows);
            return summary;
        }
        if (summary.remainingResidues != 0) {
            rows.add(tsv("<archive>", "<gate>", -1, "incomplete", "", "",
                    "remaining-restored-argument-residues="
                            + summary.remainingResidues));
        }

        Map<String, byte[]> replacements = new LinkedHashMap<>();
        ArchiveHierarchy hierarchy = new ArchiveHierarchy(classes);
        for (ClassNode owner : classes.values()) {
            if (!evaluatedKeys.containsKey(owner.name)) continue;
            summary.jsrMethodsInlined += inlineLegacySubroutines(owner);
            byte[] bytes = writeClass(owner, hierarchy);
            verifyClass(bytes);
            replacements.put(owner.name, bytes);
            summary.changedClasses++;
        }
        if (rewrittenOutput != null) {
            writeVerifiedArchive(entries, replacements, rewrittenOutput, summary);
        }
        writeReports(input, reportDirectory, rewrittenOutput, summary, rows);
        System.out.println("classes=" + summary.parsedClasses
                + " keys=" + summary.evaluatedKeys
                + " key_fields_removed=" + summary.keyFieldsRemoved
                + " method_keys_inlined=" + summary.methodKeysInlined
                + " residues_removed=" + summary.argumentResiduesRemoved
                + " changed=" + summary.changedClasses
                + " report=" + reportDirectory);
        return summary;
    }

    private static Map<FieldRef, KeyBootstrap> selectFieldBootstraps(
            Map<FieldRef, KeyBootstrap> candidates, Set<String> selectedOwners) {
        Map<FieldRef, KeyBootstrap> result = new LinkedHashMap<>();
        for (Map.Entry<FieldRef, KeyBootstrap> entry : candidates.entrySet()) {
            if (selectedOwners.contains(entry.getKey().owner)) {
                result.put(entry.getKey(), entry.getValue());
            }
        }
        return result;
    }

    private static <T> Map<String, T> selectOwnerBootstraps(
            Map<String, T> candidates, Set<String> selectedOwners) {
        Map<String, T> result = new LinkedHashMap<>();
        for (Map.Entry<String, T> entry : candidates.entrySet()) {
            if (selectedOwners.contains(entry.getKey())) {
                result.put(entry.getKey(), entry.getValue());
            }
        }
        return result;
    }

    private static List<String> validateCoverage(Map<String, ClassNode> classes,
                                                 Map<String, Long> keys,
                                                 Map<FieldRef, KeyBootstrap> bootstraps,
                                                 Map<String, DirectKeyBootstrap> directBootstraps,
                                                 Map<String, StackKeyBootstrap> stackBootstraps) {
        List<String> failures = new ArrayList<>();
        Set<String> owners = new LinkedHashSet<>();
        for (FieldRef field : bootstraps.keySet()) owners.add(field.owner);
        for (String owner : directBootstraps.keySet()) {
            if (!owners.add(owner)) {
                failures.add(tsv(owner, "<clinit>()V", -1, "reject", "", "",
                        "multiple-key-bootstrap-kinds"));
            }
        }
        for (String owner : stackBootstraps.keySet()) {
            if (!owners.add(owner)) {
                failures.add(tsv(owner, "<clinit>()V", -1, "reject", "", "",
                        "multiple-key-bootstrap-kinds"));
            }
        }
        for (String owner : keys.keySet()) {
            if (!owners.contains(owner)) {
                failures.add(tsv(owner, "<clinit>()V", -1, "reject", "", hex(keys.get(owner)),
                        "evaluated-key-without-recognized-bootstrap"));
            }
        }
        for (String owner : owners) {
            if (!keys.containsKey(owner)) {
                failures.add(tsv(owner, "<clinit>()V", -1, "reject", "", "",
                        "bootstrap-without-evaluated-key"));
            }
        }
        for (FieldRef field : bootstraps.keySet()) {
            int writes = 0;
            int crossOwnerReads = 0;
            for (ClassNode candidate : classes.values()) {
                for (MethodNode method : candidate.methods) {
                    for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
                         insn = insn.getNext()) {
                        if (!(insn instanceof FieldInsnNode)
                                || !field.matches((FieldInsnNode) insn)) continue;
                        if (insn.getOpcode() == Opcodes.PUTSTATIC) writes++;
                        if (insn.getOpcode() == Opcodes.GETSTATIC
                                && !candidate.name.equals(field.owner)) crossOwnerReads++;
                    }
                }
            }
            if (writes != 1) {
                failures.add(tsv(field.owner, "<clinit>()V", -1, "reject", field.name, "",
                        "key-field-writes=" + writes));
            }
            if (crossOwnerReads != 0) {
                failures.add(tsv(field.owner, "<archive>", -1, "reject", field.name, "",
                        "cross-owner-key-reads=" + crossOwnerReads));
            }
            KeyBootstrap bootstrap = bootstraps.get(field);
            if (hasControlBoundary(bootstrap.method, bootstrap.start, bootstrap.write)) {
                failures.add(tsv(field.owner, bootstrap.method.name
                        + bootstrap.method.desc, bootstrap.instruction, "reject",
                        field.name, "", "field-key-control-boundary"));
            }
        }
        for (Map.Entry<String, DirectKeyBootstrap> entry : directBootstraps.entrySet()) {
            DirectKeyBootstrap bootstrap = entry.getValue();
            int local = bootstrap.store.var;
            if (countStores(bootstrap.method, local, Opcodes.LSTORE) != 1) {
                failures.add(tsv(entry.getKey(), bootstrap.method.name
                        + bootstrap.method.desc, bootstrap.instruction, "reject", "", "",
                        "direct-key-local-has-multiple-stores"));
            } else if (!allLoadsProvenFromStore(entry.getKey(), bootstrap.method, local,
                    bootstrap.store)) {
                failures.add(tsv(entry.getKey(), bootstrap.method.name
                        + bootstrap.method.desc, bootstrap.instruction, "reject", "", "",
                        "direct-key-local-load-provenance"));
            } else if (hasControlBoundary(bootstrap.method, bootstrap.start,
                    bootstrap.store)) {
                failures.add(tsv(entry.getKey(), bootstrap.method.name
                        + bootstrap.method.desc, bootstrap.instruction, "reject", "", "",
                        "direct-key-control-boundary"));
            }
        }
        return failures;
    }

    private static Map<FieldRef, KeyBootstrap> findKeyBootstraps(
            Map<String, ClassNode> classes) {
        Map<FieldRef, KeyBootstrap> result = new LinkedHashMap<>();
        for (ClassNode owner : classes.values()) {
            MethodNode clinit = method(owner, "<clinit>", "()V");
            if (clinit == null) continue;
            Map<String, FieldNode> fields = new LinkedHashMap<>();
            for (FieldNode field : owner.fields) {
                if ("J".equals(field.desc) && (field.access & Opcodes.ACC_STATIC) != 0) {
                    fields.put(field.name, field);
                }
            }
            int instruction = 0;
            for (AbstractInsnNode insn = clinit.instructions.getFirst(); insn != null;
                 insn = insn.getNext(), instruction++) {
                if (!(insn instanceof FieldInsnNode)
                        || insn.getOpcode() != Opcodes.PUTSTATIC) continue;
                FieldInsnNode write = (FieldInsnNode) insn;
                if (!owner.name.equals(write.owner) || !"J".equals(write.desc)) continue;
                AbstractInsnNode transform = previousCode(write);
                AbstractInsnNode transformInput = previousCode(transform);
                AbstractInsnNode bootstrap = previousCode(transformInput);
                AbstractInsnNode seedA = bootstrapStart(bootstrap);
                if (!isTransformCall(transform) || longConstant(transformInput) == null
                        || !isBootstrapCall(bootstrap) || seedA == null) continue;
                FieldNode field = fields.get(write.name);
                if (field == null) continue;
                FieldRef ref = new FieldRef(owner.name, write.name, "J");
                if (result.put(ref, new KeyBootstrap(field, clinit, seedA, write,
                        instruction)) != null) {
                    throw new IllegalStateException("multiple key bootstraps for " + ref);
                }
            }
        }
        return result;
    }

    private static Map<String, DirectKeyBootstrap> findDirectKeyBootstraps(
            Map<String, ClassNode> classes) {
        Map<String, DirectKeyBootstrap> result = new LinkedHashMap<>();
        for (ClassNode owner : classes.values()) {
            for (MethodNode method : owner.methods) {
                int instruction = 0;
                for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
                     insn = insn.getNext(), instruction++) {
                    if (!isBootstrapCall(insn)) continue;
                    AbstractInsnNode start = bootstrapStart(insn);
                    AbstractInsnNode transformInput = nextCode(insn);
                    AbstractInsnNode transform = nextCode(transformInput);
                    if (start == null || longConstant(transformInput) == null
                            || !isTransformCall(transform)) continue;

                    AbstractInsnNode afterTransform = nextCode(transform);
                    long mask = 0L;
                    AbstractInsnNode end = afterTransform;
                    if (longConstant(afterTransform) != null) {
                        AbstractInsnNode xor = nextCode(afterTransform);
                        end = nextCode(xor);
                        if (xor == null || xor.getOpcode() != Opcodes.LXOR) continue;
                        mask = longConstant(afterTransform);
                    }
                    if (!(end instanceof VarInsnNode)
                            || end.getOpcode() != Opcodes.LSTORE) continue;
                    DirectKeyBootstrap bootstrap = new DirectKeyBootstrap(method, start,
                            (VarInsnNode) end, mask, instruction);
                    if (result.put(owner.name, bootstrap) != null) {
                        throw new IllegalStateException("multiple direct key bootstraps in "
                                + owner.name);
                    }
                }
            }
        }
        return result;
    }

    private static Map<String, StackKeyBootstrap> findStackKeyBootstraps(
            Map<String, ClassNode> classes, Set<String> classifiedOwners) {
        Map<String, StackKeyBootstrap> result = new LinkedHashMap<>();
        for (ClassNode owner : classes.values()) {
            if (classifiedOwners.contains(owner.name)) continue;
            for (MethodNode method : owner.methods) {
                int instruction = 0;
                for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
                     insn = insn.getNext(), instruction++) {
                    if (!isBootstrapCall(insn)) continue;
                    AbstractInsnNode start = bootstrapStart(insn);
                    AbstractInsnNode input = nextCode(insn);
                    AbstractInsnNode transform = nextCode(input);
                    if (start == null || longConstant(input) == null
                            || !isTransformCall(transform)) continue;
                    StackKeyBootstrap bootstrap = stackKeyBootstrap(owner.name, method,
                            start, transform, instruction);
                    if (bootstrap == null) continue;
                    if (result.put(owner.name, bootstrap) != null) {
                        throw new IllegalStateException("multiple stack key bootstraps in "
                                + owner.name);
                    }
                }
            }
        }
        return result;
    }

    private static StackKeyBootstrap stackKeyBootstrap(String owner,
                                                        MethodNode method,
                                                        AbstractInsnNode start,
                                                        AbstractInsnNode transform,
                                                        int instruction) {
        try {
            RecordingSourceInterpreter interpreter = new RecordingSourceInterpreter();
            Frame<SourceValue>[] frames = new Analyzer<SourceValue>(interpreter)
                    .analyze(owner, method);
            Map<AbstractInsnNode, Integer> indexes = instructionIndexes(method);
            StackKeyBootstrap match = null;
            for (AbstractInsnNode insn = transform.getNext(); insn != null;
                 insn = insn.getNext()) {
                if (insn.getOpcode() != Opcodes.LXOR) continue;
                Integer index = indexes.get(insn);
                if (index == null || frames[index] == null
                        || frames[index].getStackSize() < 2) continue;
                Frame<SourceValue> frame = frames[index];
                AbstractInsnNode left = soleSource(frame.getStack(
                        frame.getStackSize() - 2));
                AbstractInsnNode right = soleSource(frame.getStack(
                        frame.getStackSize() - 1));
                AbstractInsnNode maskNode;
                if (left == transform && longConstant(right) != null) {
                    maskNode = right;
                } else if (right == transform && longConstant(left) != null) {
                    maskNode = left;
                } else {
                    continue;
                }
                AbstractInsnNode next = nextCode(insn);
                if (!(next instanceof VarInsnNode)
                        || next.getOpcode() != Opcodes.LSTORE) continue;
                VarInsnNode store = (VarInsnNode) next;
                if (countStores(method, store.var, Opcodes.LSTORE) != 1
                        || !allLoadsProvenFromStore(owner, method, store.var, store)
                        || !onlyRecordedUse(interpreter.uses, transform, insn)
                        || !onlyRecordedUse(interpreter.uses, maskNode, insn)) continue;
                if (match != null) return null;
                match = new StackKeyBootstrap(method, start, transform, maskNode,
                        insn, store, longConstant(maskNode), instruction);
            }
            return match;
        } catch (Throwable failure) {
            return null;
        }
    }

    private static AbstractInsnNode bootstrapStart(AbstractInsnNode bootstrap) {
        AbstractInsnNode ownerArgument = previousCode(bootstrap);
        AbstractInsnNode seedB;
        if (ownerArgument != null && ownerArgument.getOpcode() == Opcodes.ACONST_NULL) {
            seedB = previousCode(ownerArgument);
        } else if (isLookupClass(ownerArgument)) {
            AbstractInsnNode lookup = previousCode(ownerArgument);
            if (!isLookup(lookup)) return null;
            seedB = previousCode(lookup);
        } else {
            return null;
        }
        AbstractInsnNode seedA = previousCode(seedB);
        return longConstant(seedA) != null && longConstant(seedB) != null ? seedA : null;
    }

    private static boolean isBootstrapCall(AbstractInsnNode insn) {
        if (!(insn instanceof MethodInsnNode)) return false;
        MethodInsnNode call = (MethodInsnNode) insn;
        return call.getOpcode() == Opcodes.INVOKESTATIC && STATE.equals(call.owner)
                && "a".equals(call.name) && KEY_BOOTSTRAP_DESC.equals(call.desc);
    }

    private static boolean isTransformCall(AbstractInsnNode insn) {
        if (!(insn instanceof MethodInsnNode)) return false;
        MethodInsnNode call = (MethodInsnNode) insn;
        return call.getOpcode() == Opcodes.INVOKEINTERFACE
                && STATE_INTERFACE.equals(call.owner) && "a".equals(call.name)
                && "(J)J".equals(call.desc);
    }

    private static boolean isLookup(AbstractInsnNode insn) {
        if (!(insn instanceof MethodInsnNode)) return false;
        MethodInsnNode call = (MethodInsnNode) insn;
        return call.getOpcode() == Opcodes.INVOKESTATIC
                && "java/lang/invoke/MethodHandles".equals(call.owner)
                && "lookup".equals(call.name)
                && "()Ljava/lang/invoke/MethodHandles$Lookup;".equals(call.desc);
    }

    private static boolean isLookupClass(AbstractInsnNode insn) {
        if (!(insn instanceof MethodInsnNode)) return false;
        MethodInsnNode call = (MethodInsnNode) insn;
        return call.getOpcode() == Opcodes.INVOKEVIRTUAL
                && "java/lang/invoke/MethodHandles$Lookup".equals(call.owner)
                && "lookupClass".equals(call.name) && "()Ljava/lang/Class;".equals(call.desc);
    }

    private static int inlineKeyReads(Map<String, ClassNode> classes, FieldRef field,
                                      long key, List<String> rows) {
        int changed = 0;
        for (ClassNode owner : classes.values()) {
            for (MethodNode method : owner.methods) {
                int instruction = 0;
                for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null; ) {
                    AbstractInsnNode next = insn.getNext();
                    if (insn instanceof FieldInsnNode && insn.getOpcode() == Opcodes.GETSTATIC
                            && field.matches((FieldInsnNode) insn)) {
                        method.instructions.set(insn, new LdcInsnNode(key));
                        rows.add(tsv(owner.name, method.name + method.desc, instruction,
                                "inline-class-key", field.name, hex(key), "evaluated-key"));
                        changed++;
                    }
                    insn = next;
                    instruction++;
                }
            }
        }
        return changed;
    }

    private static int inlineDirectKeyBootstrap(String owner,
                                                DirectKeyBootstrap bootstrap,
                                                long value,
                                                List<String> rows) {
        int changed = 0;
        for (AbstractInsnNode insn = bootstrap.method.instructions.getFirst(); insn != null; ) {
            AbstractInsnNode next = insn.getNext();
            if (insn instanceof VarInsnNode && insn.getOpcode() == Opcodes.LLOAD
                    && ((VarInsnNode) insn).var == bootstrap.store.var) {
                bootstrap.method.instructions.set(insn, new LdcInsnNode(value));
                changed++;
            }
            insn = next;
        }
        removeCodeRange(bootstrap.method, bootstrap.start, bootstrap.store);
        rows.add(tsv(owner, bootstrap.method.name + bootstrap.method.desc,
                bootstrap.instruction, "inline-direct-key", "", hex(value),
                "unique-store-proven-loads=" + changed));
        return changed;
    }

    private static int inlineStackKeyBootstrap(String owner,
                                               StackKeyBootstrap bootstrap,
                                               long value,
                                               List<String> rows) {
        int changed = 0;
        for (AbstractInsnNode insn = bootstrap.method.instructions.getFirst(); insn != null; ) {
            AbstractInsnNode next = insn.getNext();
            if (insn instanceof VarInsnNode && insn.getOpcode() == Opcodes.LLOAD
                    && ((VarInsnNode) insn).var == bootstrap.store.var) {
                bootstrap.method.instructions.set(insn, new LdcInsnNode(value));
                changed++;
            }
            insn = next;
        }
        removeCodeRange(bootstrap.method, bootstrap.start, bootstrap.transform);
        bootstrap.method.instructions.remove(bootstrap.maskNode);
        bootstrap.method.instructions.remove(bootstrap.xor);
        bootstrap.method.instructions.remove(bootstrap.store);
        rows.add(tsv(owner, bootstrap.method.name + bootstrap.method.desc,
                bootstrap.instruction, "inline-stack-key", "", hex(value),
                "exclusive-stack-flow-proven-loads=" + changed));
        return changed;
    }

    private static int inlineMethodKeys(String owner, MethodNode method, long classKey,
                                        List<String> rows) {
        List<MethodKey> definitions = new ArrayList<>();
        int instruction = 0;
        for (AbstractInsnNode first = method.instructions.getFirst(); first != null;
             first = first.getNext(), instruction++) {
            Long firstValue = longConstant(first);
            if (firstValue == null || firstValue.longValue() != classKey) continue;
            AbstractInsnNode mask = nextCode(first);
            AbstractInsnNode xor = nextCode(mask);
            AbstractInsnNode store = nextCode(xor);
            Long maskValue = longConstant(mask);
            if (maskValue == null || xor == null || xor.getOpcode() != Opcodes.LXOR
                    || !(store instanceof VarInsnNode)
                    || store.getOpcode() != Opcodes.LSTORE
                    || hasControlBoundary(method, first, store)) continue;
            int local = ((VarInsnNode) store).var;
            if (countStores(method, local, Opcodes.LSTORE) != 1) continue;
            if (!allLoadsProvenFromStore(owner, method, local, store)) continue;
            definitions.add(new MethodKey(first, mask, xor, (VarInsnNode) store,
                    classKey ^ maskValue.longValue(), instruction));
        }
        int changed = 0;
        for (MethodKey definition : definitions) {
            for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null; ) {
                AbstractInsnNode next = insn.getNext();
                if (insn instanceof VarInsnNode && insn.getOpcode() == Opcodes.LLOAD
                        && ((VarInsnNode) insn).var == definition.store.var) {
                    method.instructions.set(insn, new LdcInsnNode(definition.value));
                }
                insn = next;
            }
            method.instructions.remove(definition.first);
            method.instructions.remove(definition.mask);
            method.instructions.remove(definition.xor);
            method.instructions.remove(definition.store);
            rows.add(tsv(owner, method.name + method.desc, definition.instruction,
                    "inline-method-key", "", hex(definition.value),
                    "unique-store-proven-loads"));
            changed++;
        }
        return changed;
    }

    private static boolean allLoadsProvenFromStore(String owner, MethodNode method,
                                                   int local, AbstractInsnNode store) {
        try {
            Map<AbstractInsnNode, Integer> indexes = instructionIndexes(method);
            Frame<SourceValue>[] frames = new Analyzer<SourceValue>(new SourceInterpreter())
                    .analyze(owner, method);
            for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
                 insn = insn.getNext()) {
                if (!(insn instanceof VarInsnNode) || insn.getOpcode() != Opcodes.LLOAD
                        || ((VarInsnNode) insn).var != local) continue;
                Integer index = indexes.get(insn);
                if (index == null || frames[index] == null
                        || frames[index].getLocals() <= local) return false;
                SourceValue value = frames[index].getLocal(local);
                if (value == null || value.insns.size() != 1
                        || !value.insns.contains(store)) return false;
            }
            return true;
        } catch (Throwable failure) {
            return false;
        }
    }

    private static int removeRestoredArgumentResidues(String owner, MethodNode method,
                                                       List<String> rows) {
        int changed = 0;
        int instruction = 0;
        for (AbstractInsnNode intArg = method.instructions.getFirst(); intArg != null; ) {
            AbstractInsnNode nextIteration = intArg.getNext();
            if (intConstant(intArg) == null) {
                intArg = nextIteration;
                instruction++;
                continue;
            }
            AbstractInsnNode firstLong = nextCode(intArg);
            AbstractInsnNode secondLong = nextCode(firstLong);
            AbstractInsnNode xor = nextCode(secondLong);
            AbstractInsnNode popLong = nextCode(xor);
            AbstractInsnNode popInt = nextCode(popLong);
            AbstractInsnNode restored = nextCode(popInt);
            if (longConstant(firstLong) == null || longConstant(secondLong) == null
                    || xor == null || xor.getOpcode() != Opcodes.LXOR
                    || popLong == null || popLong.getOpcode() != Opcodes.POP2
                    || popInt == null || popInt.getOpcode() != Opcodes.POP
                    || !isRestoredConstant(restored)
                    || hasControlBoundary(method, intArg, popInt)) {
                intArg = nextIteration;
                instruction++;
                continue;
            }
            AbstractInsnNode after = popInt.getNext();
            method.instructions.remove(intArg);
            method.instructions.remove(firstLong);
            method.instructions.remove(secondLong);
            method.instructions.remove(xor);
            method.instructions.remove(popLong);
            method.instructions.remove(popInt);
            rows.add(tsv(owner, method.name + method.desc, instruction,
                    "remove-restored-arguments", "", "", "pure-int-long-arguments"));
            changed++;
            intArg = after;
        }
        return changed;
    }

    private static int removeDataflowRestoredArgumentResidue(String owner,
                                                             MethodNode method,
                                                             List<String> rows) {
        try {
            RecordingSourceInterpreter interpreter = new RecordingSourceInterpreter();
            Frame<SourceValue>[] frames = new Analyzer<SourceValue>(interpreter)
                    .analyze(owner, method);
            Map<AbstractInsnNode, Integer> indexes = instructionIndexes(method);
            for (AbstractInsnNode popLong = method.instructions.getFirst(); popLong != null;
                 popLong = popLong.getNext()) {
                if (popLong.getOpcode() != Opcodes.POP2) continue;
                AbstractInsnNode popInt = nextCode(popLong);
                AbstractInsnNode restored = nextCode(popInt);
                if (popInt == null || popInt.getOpcode() != Opcodes.POP
                        || !isRestoredConstant(restored)) continue;

                SourceValue longValue = stackTop(frames, indexes.get(popLong));
                SourceValue intValue = stackTop(frames, indexes.get(popInt));
                AbstractInsnNode xor = soleSource(longValue);
                AbstractInsnNode intProducer = soleSource(intValue);
                if (longValue == null || longValue.getSize() != 2
                        || intValue == null || intValue.getSize() != 1
                        || xor == null || xor.getOpcode() != Opcodes.LXOR
                        || intConstant(intProducer) == null) continue;

                Integer xorIndex = indexes.get(xor);
                if (xorIndex == null || frames[xorIndex] == null
                        || frames[xorIndex].getStackSize() < 2) continue;
                Frame<SourceValue> xorFrame = frames[xorIndex];
                AbstractInsnNode left = soleSource(xorFrame.getStack(
                        xorFrame.getStackSize() - 2));
                AbstractInsnNode right = soleSource(xorFrame.getStack(
                        xorFrame.getStackSize() - 1));
                if (left == null || right == null || left == right
                        || longConstant(left) == null || longConstant(right) == null
                        || !onlyRecordedUse(interpreter.uses, left, xor)
                        || !onlyRecordedUse(interpreter.uses, right, xor)
                        || !onlyTerminalUse(interpreter.uses, xor, popLong)
                        || !onlyTerminalUse(interpreter.uses, intProducer, popInt)) {
                    continue;
                }

                int instruction = indexes.get(popLong);
                method.instructions.remove(intProducer);
                method.instructions.remove(left);
                method.instructions.remove(right);
                method.instructions.remove(xor);
                method.instructions.remove(popLong);
                method.instructions.remove(popInt);
                rows.add(tsv(owner, method.name + method.desc, instruction,
                        "remove-dataflow-restored-arguments", "", "",
                        "exclusive-pure-producer-chain"));
                return 1;
            }
        } catch (Throwable failure) {
            return 0;
        }
        return 0;
    }

    private static SourceValue stackTop(Frame<SourceValue>[] frames, Integer index) {
        if (frames == null || index == null || frames[index] == null
                || frames[index].getStackSize() == 0) return null;
        return frames[index].getStack(frames[index].getStackSize() - 1);
    }

    private static AbstractInsnNode soleSource(SourceValue value) {
        return value != null && value.insns.size() == 1
                ? value.insns.iterator().next() : null;
    }

    private static boolean onlyRecordedUse(
            Map<AbstractInsnNode, Set<AbstractInsnNode>> uses,
            AbstractInsnNode producer, AbstractInsnNode expected) {
        Set<AbstractInsnNode> consumers = uses.get(producer);
        return consumers != null && consumers.size() == 1
                && consumers.contains(expected);
    }

    private static boolean onlyTerminalUse(
            Map<AbstractInsnNode, Set<AbstractInsnNode>> uses,
            AbstractInsnNode producer, AbstractInsnNode terminal) {
        Set<AbstractInsnNode> consumers = uses.get(producer);
        return consumers == null || consumers.isEmpty()
                || consumers.size() == 1 && consumers.contains(terminal);
    }

    private static boolean isRestoredConstant(AbstractInsnNode insn) {
        return insn instanceof LdcInsnNode
                && (((LdcInsnNode) insn).cst instanceof String
                || ((LdcInsnNode) insn).cst instanceof Integer)
                || intConstant(insn) != null;
    }

    private static boolean hasControlBoundary(MethodNode method, AbstractInsnNode start,
                                              AbstractInsnNode end) {
        Set<LabelNode> targets = new HashSet<>();
        for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
             insn = insn.getNext()) {
            if (insn instanceof JumpInsnNode) targets.add(((JumpInsnNode) insn).label);
            if (insn instanceof TableSwitchInsnNode) {
                TableSwitchInsnNode table = (TableSwitchInsnNode) insn;
                targets.add(table.dflt); targets.addAll(table.labels);
            }
            if (insn instanceof LookupSwitchInsnNode) {
                LookupSwitchInsnNode lookup = (LookupSwitchInsnNode) insn;
                targets.add(lookup.dflt); targets.addAll(lookup.labels);
            }
        }
        for (TryCatchBlockNode block : method.tryCatchBlocks) {
            targets.add(block.start); targets.add(block.end); targets.add(block.handler);
        }
        for (AbstractInsnNode insn = start.getNext(); insn != null && insn != end;
             insn = insn.getNext()) {
            if (insn instanceof LabelNode && targets.contains(insn)) return true;
        }
        return false;
    }

    private static int countStores(MethodNode method, int local, int opcode) {
        int count = 0;
        for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
             insn = insn.getNext()) {
            if (insn instanceof VarInsnNode && insn.getOpcode() == opcode
                    && ((VarInsnNode) insn).var == local) count++;
        }
        return count;
    }

    private static int countKeyFields(Map<String, ClassNode> classes,
                                      Set<FieldRef> targets) {
        int count = 0;
        for (FieldRef target : targets) {
            ClassNode owner = classes.get(target.owner);
            if (owner == null) continue;
            for (FieldNode field : owner.fields) if (target.name.equals(field.name)
                    && target.desc.equals(field.desc)) count++;
        }
        return count;
    }

    private static int countKeyBootstrapCalls(Map<String, ClassNode> classes,
                                              Set<String> selectedOwners) {
        int count = 0;
        for (ClassNode owner : classes.values()) {
            if (!selectedOwners.contains(owner.name)) continue;
            for (MethodNode method : owner.methods) {
            for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
                 insn = insn.getNext()) if (isBootstrapCall(insn)) count++;
            }
        }
        return count;
    }

    private static int countFieldReads(Map<String, ClassNode> classes,
                                       Set<FieldRef> fields) {
        int count = 0;
        for (ClassNode owner : classes.values()) for (MethodNode method : owner.methods) {
            for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
                 insn = insn.getNext()) {
                if (!(insn instanceof FieldInsnNode) || insn.getOpcode() != Opcodes.GETSTATIC) {
                    continue;
                }
                for (FieldRef field : fields) if (field.matches((FieldInsnNode) insn)) count++;
            }
        }
        return count;
    }

    private static int countRestoredArgumentResidues(Map<String, ClassNode> classes,
                                                     Set<String> selectedOwners) {
        int count = 0;
        for (ClassNode owner : classes.values()) {
            if (!selectedOwners.contains(owner.name)) continue;
            for (MethodNode method : owner.methods) {
            for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
                 insn = insn.getNext()) {
                if (insn.getOpcode() == Opcodes.POP2
                        && nextCode(insn) != null && nextCode(insn).getOpcode() == Opcodes.POP
                        && isRestoredConstant(nextCode(nextCode(insn)))) count++;
            }
            }
        }
        return count;
    }

    private static void removeCodeRange(MethodNode method, AbstractInsnNode start,
                                        AbstractInsnNode end) {
        AbstractInsnNode cursor = start;
        while (cursor != null) {
            AbstractInsnNode next = cursor.getNext();
            if (cursor.getOpcode() >= 0 || cursor instanceof FrameNode) {
                method.instructions.remove(cursor);
            }
            if (cursor == end) break;
            cursor = next;
        }
    }

    private static void replaceCodeRangeWithConstant(MethodNode method,
                                                     AbstractInsnNode start,
                                                     AbstractInsnNode end,
                                                     long value) {
        method.instructions.insertBefore(start, new LdcInsnNode(value));
        removeCodeRange(method, start, end);
    }

    private static Map<AbstractInsnNode, Integer> instructionIndexes(MethodNode method) {
        Map<AbstractInsnNode, Integer> result = new IdentityHashMap<>();
        int index = 0;
        for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
             insn = insn.getNext(), index++) result.put(insn, index);
        return result;
    }

    private static Integer intConstant(AbstractInsnNode insn) {
        if (insn == null) return null;
        int opcode = insn.getOpcode();
        if (opcode >= Opcodes.ICONST_M1 && opcode <= Opcodes.ICONST_5) {
            return opcode - Opcodes.ICONST_0;
        }
        if (insn instanceof IntInsnNode
                && (opcode == Opcodes.BIPUSH || opcode == Opcodes.SIPUSH)) {
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
        return insn instanceof LdcInsnNode && ((LdcInsnNode) insn).cst instanceof Long
                ? (Long) ((LdcInsnNode) insn).cst : null;
    }

    private static AbstractInsnNode previousCode(AbstractInsnNode insn) {
        AbstractInsnNode cursor = insn == null ? null : insn.getPrevious();
        while (cursor != null && cursor.getOpcode() < 0) cursor = cursor.getPrevious();
        return cursor;
    }

    private static AbstractInsnNode nextCode(AbstractInsnNode insn) {
        AbstractInsnNode cursor = insn == null ? null : insn.getNext();
        while (cursor != null && cursor.getOpcode() < 0) cursor = cursor.getNext();
        return cursor;
    }

    private static MethodNode method(ClassNode owner, String name, String desc) {
        for (MethodNode method : owner.methods) {
            if (name.equals(method.name) && desc.equals(method.desc)) return method;
        }
        return null;
    }

    private static List<EntryBytes> readEntries(Path input) throws IOException {
        List<EntryBytes> result = new ArrayList<>();
        try (ZipInputStream in = new ZipInputStream(Files.newInputStream(input))) {
            ZipEntry entry;
            while ((entry = in.getNextEntry()) != null) {
                result.add(new EntryBytes(entry, readAll(in)));
            }
        }
        return result;
    }

    private static Map<String, ClassNode> readClasses(List<EntryBytes> entries) {
        Map<String, ClassNode> result = new LinkedHashMap<>();
        for (EntryBytes entry : entries) {
            if (!entry.name.endsWith(".class")) continue;
            ClassNode owner = new ClassNode(Opcodes.ASM9);
            new ClassReader(entry.bytes).accept(owner, 0);
            result.put(owner.name, owner);
        }
        return result;
    }

    private static byte[] writeClass(ClassNode owner, ArchiveHierarchy hierarchy) {
        ClassWriter writer = new ArchiveClassWriter(ClassWriter.COMPUTE_FRAMES, hierarchy);
        owner.accept(writer);
        return writer.toByteArray();
    }

    private static int inlineLegacySubroutines(ClassNode owner) {
        int changed = 0;
        for (int index = 0; index < owner.methods.size(); index++) {
            MethodNode method = owner.methods.get(index);
            if (!containsLegacySubroutine(method)) continue;
            String[] exceptions = method.exceptions == null
                    ? null : method.exceptions.toArray(new String[0]);
            JSRInlinerAdapter inliner = new JSRInlinerAdapter(null, method.access,
                    method.name, method.desc, method.signature, exceptions);
            method.accept(inliner);
            owner.methods.set(index, inliner);
            changed++;
        }
        return changed;
    }

    private static boolean containsLegacySubroutine(MethodNode method) {
        for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
             insn = insn.getNext()) {
            if (insn.getOpcode() == Opcodes.JSR || insn.getOpcode() == Opcodes.RET) {
                return true;
            }
        }
        return false;
    }

    private static void verifyClass(byte[] bytes) throws Exception {
        ClassNode owner = new ClassNode(Opcodes.ASM9);
        new ClassReader(bytes).accept(owner, 0);
        for (MethodNode method : owner.methods) {
            if (method.instructions != null && method.instructions.size() > 0) {
                new Analyzer<>(new BasicVerifier()).analyze(owner.name, method);
            }
        }
    }

    private static void writeArchive(List<EntryBytes> entries,
                                     Map<String, byte[]> replacements,
                                     Path output, Summary summary) throws IOException {
        try (ZipOutputStream out = new ZipOutputStream(Files.newOutputStream(output))) {
            for (EntryBytes entry : entries) {
                if (isSignatureEntry(entry.name) && !replacements.isEmpty()) {
                    summary.signaturesRemoved++;
                    continue;
                }
                byte[] bytes = entry.bytes;
                if (entry.name.endsWith(".class")) {
                    String name = entry.name.substring(0, entry.name.length() - 6);
                    byte[] replacement = replacements.get(name);
                    if (replacement != null) bytes = replacement;
                }
                ZipEntry written = new ZipEntry(entry.name);
                if (entry.time >= 0) written.setTime(entry.time);
                if (entry.method == ZipEntry.STORED) {
                    CRC32 crc = new CRC32(); crc.update(bytes);
                    written.setMethod(ZipEntry.STORED);
                    written.setSize(bytes.length);
                    written.setCompressedSize(bytes.length);
                    written.setCrc(crc.getValue());
                }
                out.putNextEntry(written);
                out.write(bytes);
                out.closeEntry();
                summary.outputEntries++;
            }
        }
    }

    private static void writeVerifiedArchive(List<EntryBytes> entries,
                                             Map<String, byte[]> replacements,
                                             Path output,
                                             Summary summary) throws IOException {
        Path parent = output.toAbsolutePath().getParent();
        if (parent == null) parent = Paths.get(".").toAbsolutePath();
        Files.createDirectories(parent);
        Path temporary = Files.createTempFile(parent,
                output.getFileName().toString() + ".", ".tmp");
        summary.temporaryOutput = temporary.toAbsolutePath().toString();
        try {
            writeArchive(entries, replacements, temporary, summary);
            verifyArchive(temporary, summary);
            if (!transformationGate(summary) || summary.outputVerificationErrors != 0) {
                return;
            }
            try {
                Files.move(temporary, output, StandardCopyOption.ATOMIC_MOVE,
                        StandardCopyOption.REPLACE_EXISTING);
            } catch (AtomicMoveNotSupportedException unsupported) {
                Files.move(temporary, output, StandardCopyOption.REPLACE_EXISTING);
            }
            summary.outputCommitted = true;
        } finally {
            Files.deleteIfExists(temporary);
        }
    }

    private static void verifyArchive(Path archive, Summary summary) throws IOException {
        try (ZipInputStream in = new ZipInputStream(Files.newInputStream(archive))) {
            ZipEntry entry;
            while ((entry = in.getNextEntry()) != null) {
                byte[] bytes = readAll(in);
                if (!entry.getName().endsWith(".class")) continue;
                summary.outputClasses++;
                try {
                    verifyClass(bytes);
                } catch (Throwable failure) {
                    summary.outputVerificationErrors++;
                }
            }
        }
    }

    private static void writeReports(Path input, Path reportDirectory,
                                     Path rewrittenOutput, Summary summary,
                                     List<String> rows) throws IOException {
        Files.write(reportDirectory.resolve("rewrite.tsv"), rows, StandardCharsets.UTF_8);
        List<String> audit = new ArrayList<>();
        audit.add("input=" + input.toAbsolutePath());
        audit.add("input_sha256=" + sha256(input));
        audit.add("residual_integer_oracle=" + summary.residualIntegerOracle);
        audit.add("parsed_classes=" + summary.parsedClasses);
        audit.add("evaluated_keys=" + summary.evaluatedKeys);
        audit.add("validated_keys=" + summary.validatedKeys);
        audit.add("member_selected_keys=" + summary.memberSelectedKeys);
        audit.add("integer_selected_keys=" + summary.integerSelectedKeys);
        audit.add("detected_key_bootstraps=" + summary.detectedKeyBootstraps);
        audit.add("deferred_key_bootstraps=" + summary.deferredKeyBootstraps);
        audit.add("key_bootstraps=" + summary.keyBootstraps);
        audit.add("field_key_bootstraps=" + summary.fieldKeyBootstraps);
        audit.add("direct_key_bootstraps=" + summary.directKeyBootstraps);
        audit.add("stack_key_bootstraps=" + summary.stackKeyBootstraps);
        audit.add("coverage_errors=" + summary.coverageErrors);
        audit.add("key_reads_inlined=" + summary.keyReadsInlined);
        audit.add("direct_key_reads_inlined=" + summary.directKeyReadsInlined);
        audit.add("stack_key_reads_inlined=" + summary.stackKeyReadsInlined);
        audit.add("key_bootstraps_removed=" + summary.keyBootstrapsRemoved);
        audit.add("direct_key_bootstraps_removed="
                + summary.directKeyBootstrapsRemoved);
        audit.add("stack_key_bootstraps_replaced="
                + summary.stackKeyBootstrapsReplaced);
        audit.add("key_fields_removed=" + summary.keyFieldsRemoved);
        audit.add("public_key_fields_removed=" + summary.publicKeyFieldsRemoved);
        audit.add("method_keys_inlined=" + summary.methodKeysInlined);
        audit.add("argument_residues_removed=" + summary.argumentResiduesRemoved);
        audit.add("dataflow_residues_removed=" + summary.dataflowResiduesRemoved);
        audit.add("remaining_key_fields=" + summary.remainingKeyFields);
        audit.add("remaining_key_bootstraps=" + summary.remainingKeyBootstraps);
        audit.add("remaining_key_reads=" + summary.remainingKeyReads);
        audit.add("remaining_residues=" + summary.remainingResidues);
        audit.add("jsr_methods_inlined=" + summary.jsrMethodsInlined);
        audit.add("changed_classes=" + summary.changedClasses);
        audit.add("rewrite_output=" + (rewrittenOutput == null ? "" : rewrittenOutput.toAbsolutePath()));
        audit.add("temporary_output=" + summary.temporaryOutput);
        audit.add("output_committed=" + summary.outputCommitted);
        audit.add("output_classes=" + summary.outputClasses);
        audit.add("output_verification_errors=" + summary.outputVerificationErrors);
        audit.add("input_classes_loaded=false");
        boolean pass = transformationGate(summary)
                && (rewrittenOutput == null || summary.outputCommitted
                && summary.outputVerificationErrors == 0);
        audit.add("gate=" + (pass ? "PASS" : "FAIL"));
        Files.write(reportDirectory.resolve("audit.txt"), audit, StandardCharsets.UTF_8);
        Files.write(reportDirectory.resolve("gate.txt"),
                Collections.singletonList(pass ? "PASS" : "FAIL"), StandardCharsets.UTF_8);
    }

    private static byte[] readAll(InputStream input) throws IOException {
        ByteArrayOutputStream output = new ByteArrayOutputStream();
        byte[] buffer = new byte[8192];
        int read;
        while ((read = input.read(buffer)) >= 0) output.write(buffer, 0, read);
        return output.toByteArray();
    }

    private static String sha256(Path input) throws IOException {
        final MessageDigest digest;
        try {
            digest = MessageDigest.getInstance("SHA-256");
        } catch (NoSuchAlgorithmException failure) {
            throw new IOException("SHA-256 unavailable", failure);
        }
        digest.update(Files.readAllBytes(input));
        StringBuilder result = new StringBuilder(64);
        for (byte value : digest.digest()) {
            result.append(String.format(Locale.ROOT, "%02X", value & 0xff));
        }
        return result.toString();
    }

    private static boolean transformationGate(Summary summary) {
        return summary.coverageErrors == 0
                && summary.keyFieldsRemoved == summary.fieldKeyBootstraps
                && summary.keyBootstrapsRemoved == summary.keyBootstraps
                && summary.remainingKeyFields == 0
                && summary.remainingKeyBootstraps == 0
                && summary.remainingKeyReads == 0
                && summary.remainingResidues == 0;
    }

    private static boolean isSignatureEntry(String name) {
        String upper = name.replace('\\', '/').toUpperCase(Locale.ROOT);
        if (!upper.startsWith("META-INF/")) return false;
        String leaf = upper.substring("META-INF/".length());
        return leaf.startsWith("SIG-") || leaf.endsWith(".SF") || leaf.endsWith(".RSA")
                || leaf.endsWith(".DSA") || leaf.endsWith(".EC");
    }

    private static String hex(long value) {
        return String.format(Locale.ROOT, "%016X", value);
    }

    private static String tsv(Object... values) {
        StringBuilder result = new StringBuilder();
        for (int index = 0; index < values.length; index++) {
            if (index != 0) result.append('\t');
            if (values[index] != null) result.append(values[index]);
        }
        return result.toString();
    }

    static final class Summary {
        boolean residualIntegerOracle;
        int parsedClasses;
        int evaluatedKeys;
        int validatedKeys;
        int memberSelectedKeys;
        int integerSelectedKeys;
        int detectedKeyBootstraps;
        int deferredKeyBootstraps;
        int keyBootstraps;
        int fieldKeyBootstraps;
        int directKeyBootstraps;
        int stackKeyBootstraps;
        int coverageErrors;
        int keyReadsInlined;
        int directKeyReadsInlined;
        int stackKeyReadsInlined;
        int keyBootstrapsRemoved;
        int directKeyBootstrapsRemoved;
        int stackKeyBootstrapsReplaced;
        int keyFieldsRemoved;
        int publicKeyFieldsRemoved;
        int methodKeysInlined;
        int argumentResiduesRemoved;
        int dataflowResiduesRemoved;
        int remainingKeyFields;
        int remainingKeyBootstraps;
        int remainingKeyReads;
        int remainingResidues;
        int jsrMethodsInlined;
        int changedClasses;
        int outputEntries;
        int outputClasses;
        int outputVerificationErrors;
        int signaturesRemoved;
        boolean outputCommitted;
        String temporaryOutput = "";
    }

    private static final class EntryBytes {
        final String name;
        final long time;
        final int method;
        final byte[] bytes;

        EntryBytes(ZipEntry entry, byte[] bytes) {
            this.name = entry.getName();
            this.time = entry.getTime();
            this.method = entry.getMethod();
            this.bytes = bytes;
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

        boolean matches(FieldInsnNode field) {
            return owner.equals(field.owner) && name.equals(field.name) && desc.equals(field.desc);
        }

        @Override public boolean equals(Object other) {
            if (!(other instanceof FieldRef)) return false;
            FieldRef field = (FieldRef) other;
            return owner.equals(field.owner) && name.equals(field.name) && desc.equals(field.desc);
        }

        @Override public int hashCode() {
            int result = owner.hashCode();
            result = 31 * result + name.hashCode();
            return 31 * result + desc.hashCode();
        }

        @Override public String toString() {
            return owner + "." + name + ":" + desc;
        }
    }

    private static final class KeyBootstrap {
        final FieldNode field;
        final MethodNode method;
        final AbstractInsnNode start;
        final FieldInsnNode write;
        final int instruction;

        KeyBootstrap(FieldNode field, MethodNode method, AbstractInsnNode start,
                     FieldInsnNode write, int instruction) {
            this.field = field;
            this.method = method;
            this.start = start;
            this.write = write;
            this.instruction = instruction;
        }
    }

    private static final class DirectKeyBootstrap {
        final MethodNode method;
        final AbstractInsnNode start;
        final VarInsnNode store;
        final long mask;
        final int instruction;

        DirectKeyBootstrap(MethodNode method, AbstractInsnNode start,
                           VarInsnNode store, long mask, int instruction) {
            this.method = method;
            this.start = start;
            this.store = store;
            this.mask = mask;
            this.instruction = instruction;
        }
    }

    private static final class StackKeyBootstrap {
        final MethodNode method;
        final AbstractInsnNode start;
        final AbstractInsnNode transform;
        final AbstractInsnNode maskNode;
        final AbstractInsnNode xor;
        final VarInsnNode store;
        final long mask;
        final int instruction;

        StackKeyBootstrap(MethodNode method, AbstractInsnNode start,
                          AbstractInsnNode transform, AbstractInsnNode maskNode,
                          AbstractInsnNode xor, VarInsnNode store, long mask,
                          int instruction) {
            this.method = method;
            this.start = start;
            this.transform = transform;
            this.maskNode = maskNode;
            this.xor = xor;
            this.store = store;
            this.mask = mask;
            this.instruction = instruction;
        }
    }

    private static final class MethodKey {
        final AbstractInsnNode first;
        final AbstractInsnNode mask;
        final AbstractInsnNode xor;
        final VarInsnNode store;
        final long value;
        final int instruction;

        MethodKey(AbstractInsnNode first, AbstractInsnNode mask, AbstractInsnNode xor,
                  VarInsnNode store, long value, int instruction) {
            this.first = first;
            this.mask = mask;
            this.xor = xor;
            this.store = store;
            this.value = value;
            this.instruction = instruction;
        }
    }

    private static final class RecordingSourceInterpreter extends SourceInterpreter {
        final Map<AbstractInsnNode, Set<AbstractInsnNode>> uses =
                new IdentityHashMap<>();

        RecordingSourceInterpreter() {
            super(Opcodes.ASM9);
        }

        @Override public SourceValue copyOperation(AbstractInsnNode insn,
                                                   SourceValue value) {
            record(insn, value);
            return super.copyOperation(insn, value);
        }

        @Override public SourceValue unaryOperation(AbstractInsnNode insn,
                                                    SourceValue value) {
            record(insn, value);
            return super.unaryOperation(insn, value);
        }

        @Override public SourceValue binaryOperation(AbstractInsnNode insn,
                                                     SourceValue left,
                                                     SourceValue right) {
            record(insn, left);
            record(insn, right);
            return super.binaryOperation(insn, left, right);
        }

        @Override public SourceValue ternaryOperation(AbstractInsnNode insn,
                                                      SourceValue first,
                                                      SourceValue second,
                                                      SourceValue third) {
            record(insn, first);
            record(insn, second);
            record(insn, third);
            return super.ternaryOperation(insn, first, second, third);
        }

        @Override public SourceValue naryOperation(AbstractInsnNode insn,
                                                   List<? extends SourceValue> values) {
            for (SourceValue value : values) record(insn, value);
            return super.naryOperation(insn, values);
        }

        @Override public void returnOperation(AbstractInsnNode insn,
                                              SourceValue value,
                                              SourceValue expected) {
            record(insn, value);
            super.returnOperation(insn, value, expected);
        }

        private void record(AbstractInsnNode consumer, SourceValue value) {
            if (value == null) return;
            for (AbstractInsnNode producer : value.insns) {
                Set<AbstractInsnNode> consumers = uses.get(producer);
                if (consumers == null) {
                    consumers = Collections.newSetFromMap(
                            new IdentityHashMap<AbstractInsnNode, Boolean>());
                    uses.put(producer, consumers);
                }
                consumers.add(consumer);
            }
        }
    }

    private static final class ArchiveHierarchy {
        final Map<String, HierarchyType> types = new HashMap<>();

        ArchiveHierarchy(Map<String, ClassNode> classes) {
            for (ClassNode owner : classes.values()) {
                types.put(owner.name, new HierarchyType(owner.superName,
                        owner.interfaces == null ? Collections.<String>emptyList()
                                : new ArrayList<>(owner.interfaces),
                        (owner.access & Opcodes.ACC_INTERFACE) != 0));
            }
            types.put("java/lang/Object", new HierarchyType(null,
                    Collections.<String>emptyList(), false));
        }

        String commonSuperClass(String left, String right) {
            if (left.equals(right)) return left;
            if (isAssignableFrom(left, right)) return left;
            if (isAssignableFrom(right, left)) return right;
            HierarchyType leftType = types.get(left), rightType = types.get(right);
            if (leftType == null || rightType == null || leftType.isInterface
                    || rightType.isInterface) return "java/lang/Object";
            Set<String> supers = new LinkedHashSet<>();
            for (String current = left; current != null; current = superName(current)) {
                supers.add(current);
            }
            for (String current = right; current != null; current = superName(current)) {
                if (supers.contains(current)) return current;
            }
            return "java/lang/Object";
        }

        private boolean isAssignableFrom(String target, String source) {
            if (target.equals(source) || "java/lang/Object".equals(target)) return true;
            ArrayDeque<String> queue = new ArrayDeque<>();
            Set<String> seen = new HashSet<>();
            queue.add(source);
            while (!queue.isEmpty()) {
                String current = queue.removeFirst();
                if (!seen.add(current)) continue;
                if (target.equals(current)) return true;
                HierarchyType type = types.get(current);
                if (type == null) continue;
                if (type.superName != null) queue.addLast(type.superName);
                queue.addAll(type.interfaces);
            }
            return false;
        }

        private String superName(String name) {
            HierarchyType type = types.get(name);
            return type == null ? null : type.superName;
        }
    }

    private static final class HierarchyType {
        final String superName;
        final List<String> interfaces;
        final boolean isInterface;

        HierarchyType(String superName, List<String> interfaces, boolean isInterface) {
            this.superName = superName;
            this.interfaces = interfaces;
            this.isInterface = isInterface;
        }
    }

    private static final class ArchiveClassWriter extends ClassWriter {
        private final ArchiveHierarchy hierarchy;

        ArchiveClassWriter(int flags, ArchiveHierarchy hierarchy) {
            super(flags);
            this.hierarchy = hierarchy;
        }

        @Override protected String getCommonSuperClass(String left, String right) {
            return hierarchy.commonSuperClass(left, right);
        }
    }
}
