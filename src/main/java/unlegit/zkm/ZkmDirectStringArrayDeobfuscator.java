package unlegit.zkm;

import org.objectweb.asm.ClassReader;
import org.objectweb.asm.ClassWriter;
import org.objectweb.asm.ConstantDynamic;
import org.objectweb.asm.Handle;
import org.objectweb.asm.Opcodes;
import org.objectweb.asm.tree.AbstractInsnNode;
import org.objectweb.asm.tree.ClassNode;
import org.objectweb.asm.tree.FieldInsnNode;
import org.objectweb.asm.tree.FieldNode;
import org.objectweb.asm.tree.FrameNode;
import org.objectweb.asm.tree.IincInsnNode;
import org.objectweb.asm.tree.InsnList;
import org.objectweb.asm.tree.InsnNode;
import org.objectweb.asm.tree.IntInsnNode;
import org.objectweb.asm.tree.InvokeDynamicInsnNode;
import org.objectweb.asm.tree.JumpInsnNode;
import org.objectweb.asm.tree.LabelNode;
import org.objectweb.asm.tree.LdcInsnNode;
import org.objectweb.asm.tree.LookupSwitchInsnNode;
import org.objectweb.asm.tree.MethodInsnNode;
import org.objectweb.asm.tree.MethodNode;
import org.objectweb.asm.tree.MultiANewArrayInsnNode;
import org.objectweb.asm.tree.TableSwitchInsnNode;
import org.objectweb.asm.tree.TryCatchBlockNode;
import org.objectweb.asm.tree.TypeInsnNode;
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
import java.io.InputStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.AtomicMoveNotSupportedException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.StandardCopyOption;
import java.security.MessageDigest;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
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
 * Restores closed ZKM PKCS5 local {@code String[]} initializer tables.
 *
 * <p>This pass is deliberately separate from the single-field string pass.
 * It accepts one statically keyed PKCS5 setup, one local array, one or more
 * packed Latin-1 chunk loops, and constant-index {@code AALOAD} consumers.
 * The crypto region must be a single-entry/single-exit CFG island with an
 * empty stack at both boundaries. A surrounding exception range is retained
 * only when it contains the complete crypto island and has no boundary or
 * handler inside that island. Input classes are parsed but never defined or
 * initialized.</p>
 */
public final class ZkmDirectStringArrayDeobfuscator {
    private static final String ALGORITHM = "DES/CBC/PKCS5Padding";
    private static final String KEY_ALGORITHM = "DES";
    private static final String LATIN1 = "ISO-8859-1";
    private static final String DECODE_DESC = "([B)Ljava/lang/String;";
    private static final String STATE =
            ObfRuntimeNames.STATE;
    private static final String STATE_IFACE =
            ObfRuntimeNames.STATE_INTERFACE;

    private ZkmDirectStringArrayDeobfuscator() {
    }

    public static void main(String[] args) throws Exception {
        if (args.length < 2) {
            usage();
            System.exit(2);
        }
        Path output = null;
        Path authority = null;
        boolean flexibleMaterialization = false;
        for (int index = 2; index < args.length; index++) {
            String argument = args[index];
            if ("--flexible-materialization".equals(argument)) {
                if (flexibleMaterialization) {
                    throw new IllegalArgumentException("duplicate " + argument);
                }
                flexibleMaterialization = true;
            } else if ("--authority".equals(argument)) {
                if (authority != null || ++index >= args.length) {
                    throw new IllegalArgumentException(
                            "missing or duplicate --authority");
                }
                authority = Paths.get(args[index]);
            } else if (!argument.startsWith("--") && output == null) {
                output = Paths.get(argument);
            } else {
                throw new IllegalArgumentException("unknown argument: " + argument);
            }
        }
        if (authority != null && !flexibleMaterialization) {
            throw new IllegalArgumentException(
                    "--authority requires --flexible-materialization");
        }
        if (flexibleMaterialization) {
            deobfuscateFlexibleMaterialization(Paths.get(args[0]),
                    Paths.get(args[1]), output, authority);
        } else {
            deobfuscate(Paths.get(args[0]), Paths.get(args[1]), output);
        }
    }

    private static void usage() {
        System.err.println("usage: ZkmDirectStringArrayDeobfuscator"
                + " <input.jar> <report-dir> [output.jar]"
                + " [--flexible-materialization] [--authority <authority.jar>]");
    }

    static Summary deobfuscate(Path input, Path reportDirectory, Path output)
            throws Exception {
        return deobfuscate(input, reportDirectory, output,
                Collections.<String, StateKeyProof>emptyMap(), false);
    }

    /**
     * Runs the same closed-table proof with independently proven class keys.
     * The class key is bound to the exact state-transform/XOR/local chain in
     * {@code <clinit>} before any ciphertext is evaluated.
     */
    static Summary deobfuscateStateDerived(
            Path input, Path reportDirectory, Path output,
            Map<String, StateKeyProof> keyProofs) throws Exception {
        return deobfuscate(input, reportDirectory, output, keyProofs, true);
    }

    private static Summary deobfuscate(
            Path input, Path reportDirectory, Path output,
            Map<String, StateKeyProof> keyProofs, boolean stateDerived)
            throws Exception {
        return deobfuscate(input, reportDirectory, output, keyProofs,
                stateDerived, false, null);
    }

    static Summary deobfuscateFlexibleMaterialization(
            Path input, Path reportDirectory, Path output, Path authority)
            throws Exception {
        return deobfuscate(input, reportDirectory, output,
                Collections.<String, StateKeyProof>emptyMap(), true, true,
                authority);
    }

    private static Summary deobfuscate(
            Path input, Path reportDirectory, Path output,
            Map<String, StateKeyProof> suppliedKeyProofs, boolean stateDerived,
            boolean flexibleMaterialization, Path authority) throws Exception {
        validatePaths(input, output);
        Files.createDirectories(reportDirectory);
        List<EntryBytes> entries = readEntries(input);
        Map<String, byte[]> originalBytes = classBytes(entries);
        Map<String, ClassNode> classes = readClasses(originalBytes);
        Map<String, StateKeyProof> keyProofs = suppliedKeyProofs;
        Map<String, Set<Long>> classKeyCandidates = new LinkedHashMap<>();
        boolean hasFlexibleCandidates = flexibleMaterialization
                && hasPkcs5Clinit(classes);
        if (hasFlexibleCandidates) {
            keyProofs = ZkmPkcs5StateArrayDeobfuscator
                    .resolveClassKeyProofs(classes);
            mergeKeyCandidates(classKeyCandidates,
                    ZkmClassKeySelector.candidateClassKeys(classes));
            if (authority != null) {
                Map<String, ClassNode> authorityClasses = readClasses(
                        classBytes(readEntries(authority)));
                mergeKeyCandidates(classKeyCandidates,
                        ZkmClassKeySelector.candidateClassKeys(authorityClasses));
            }
        }
        ArchiveHierarchy hierarchy = new ArchiveHierarchy(classes);
        Map<MethodRef, Integer> references = methodReferences(classes);
        Summary summary = new Summary();
        summary.parsedClasses = classes.size();
        summary.outputRequested = output != null;
        summary.flexibleMaterialization = flexibleMaterialization;
        summary.authority = authority == null ? ""
                : authority.toAbsolutePath().normalize().toString();
        summary.authoritySha256 = authority == null ? "" : sha256(authority);
        List<Candidate> candidates = new ArrayList<>();
        List<String> verifierRows = new ArrayList<>();
        verifierRows.add("scope\tclass\tstatus\treason");
        Map<String, byte[]> replacements = new LinkedHashMap<>();

        for (Map.Entry<String, byte[]> original : originalBytes.entrySet()) {
            ClassNode owner = classes.get(original.getKey());
            Candidate candidate = flexibleMaterialization
                    ? inspectFlexibleMaterialization(owner, references, summary,
                    keyProofs.get(owner.name), classKeyCandidates.get(owner.name))
                    : inspect(owner, references, summary, false,
                    keyProofs.get(owner.name), stateDerived);
            if (candidate == null) continue;
            candidates.add(candidate);
            if (!candidate.proven()) continue;
            summary.provenCandidates++;
            summary.provenStrings += candidate.plaintexts.size();
            if (output == null) {
                candidate.action = "PROVEN_DRY_RUN";
                continue;
            }
            try {
                ClassNode rewritten = readClass(original.getValue());
                if (candidate.flexibleMaterialization) {
                    applyFlexibleMaterialization(rewritten, candidate);
                } else {
                    apply(rewritten, candidate);
                }
                byte[] bytes = writeClass(rewritten, hierarchy);
                verifyClass(bytes);
                assertRewritten(bytes, candidate);
                replacements.put(rewritten.name, bytes);
                candidate.action = "REWRITE";
                summary.changedClasses++;
                summary.rewrittenTables++;
                summary.rewrittenStrings += candidate.plaintexts.size();
                if (candidate.removeHelper) summary.helpersRemoved++;
                verifierRows.add(tsv("class-transaction", owner.name,
                        "PASS", ""));
            } catch (Throwable failure) {
                candidate.action = "ROLLBACK";
                candidate.reason = appendReason(candidate.reason,
                        "class-rollback:" + shortReason(failure));
                summary.classRollbacks++;
                verifierRows.add(tsv("class-transaction", owner.name,
                        "ROLLBACK", shortReason(failure)));
            }
        }

        summary.rejectedCandidates = summary.pkcs5ClinitClasses
                - summary.provenCandidates;
        if (output != null) {
            try {
                writeVerifiedArchive(entries, replacements, output, summary,
                        verifierRows);
            } catch (Throwable failure) {
                summary.outputVerificationErrors++;
                verifierRows.add(tsv("archive", "<archive>", "FAIL",
                        "write:" + shortReason(failure)));
            }
        } else {
            summary.outputPkcs5ClinitClasses = summary.pkcs5ClinitClasses;
        }
        writeReports(input, reportDirectory, output, summary, candidates,
                verifierRows, stateDerived);
        System.out.println("pkcs5_clinit_classes=" + summary.pkcs5ClinitClasses
                + " proven=" + summary.provenCandidates
                + " strings=" + summary.provenStrings
                + " rewritten=" + summary.rewrittenTables
                + " rollbacks=" + summary.classRollbacks
                + " output_committed=" + summary.outputCommitted
                + " gate=" + gate(summary));
        return summary;
    }

    private static boolean hasPkcs5Clinit(Map<String, ClassNode> classes) {
        for (ClassNode owner : classes.values()) {
            MethodNode clinit = method(owner, "<clinit>", "()V");
            if (clinit != null && containsCipherFactory(clinit, ALGORITHM)) {
                return true;
            }
        }
        return false;
    }

    /**
     * Package-private proof adapter for a ZKM table deliberately published to
     * one owner-local static {@code String[]} field. The normal array pass
     * continues to reject every escape; this adapter is used only after a
     * caller separately proves the field's delayed string helper semantics.
     */
    static FieldTableProof inspectFieldBackedTable(ClassNode owner) {
        Map<String, ClassNode> singleton = new LinkedHashMap<>();
        singleton.put(owner.name, owner);
        Candidate candidate = inspect(owner, methodReferences(singleton),
                new Summary(), true, null, false);
        return candidate == null ? null : new FieldTableProof(candidate);
    }

    /** Re-runs the complete proof on the mutable class before applying it. */
    static void rewriteFieldBackedTable(ClassNode owner,
                                        String expectedTableField) {
        FieldTableProof proof = inspectFieldBackedTable(owner);
        if (proof == null || !proof.proven) {
            throw new IllegalStateException("field-table-not-proven:"
                    + (proof == null ? "missing" : proof.reason));
        }
        if (!expectedTableField.equals(proof.tableField)) {
            throw new IllegalStateException("field-table-mismatch:"
                    + proof.tableField + "/" + expectedTableField);
        }
        proof.candidate.removeHelper = false;
        apply(owner, proof.candidate);
    }

    static ZkmClassRewriteTransaction.Emitter archiveEmitter(
            Map<String, ClassNode> classes) {
        final ArchiveHierarchy hierarchy = new ArchiveHierarchy(classes);
        return owner -> writeClass(owner, hierarchy);
    }

    static boolean isExactByteDecoder(ClassNode owner, String name) {
        return name != null && isExactZkmByteDecoder(
                method(owner, name, DECODE_DESC));
    }

    private static Candidate inspect(ClassNode owner,
                                     Map<MethodRef, Integer> references,
                                     Summary summary,
                                     boolean allowStaticFieldEscape,
                                     StateKeyProof keyProof,
                                     boolean stateDerived) {
        MethodNode clinit = method(owner, "<clinit>", "()V");
        if (clinit == null) return null;
        List<MethodInsnNode> pkcsCalls = new ArrayList<>();
        for (AbstractInsnNode insn = clinit.instructions.getFirst(); insn != null;
             insn = insn.getNext()) {
            if (isCipherFactory(insn, ALGORITHM)) {
                pkcsCalls.add((MethodInsnNode) insn);
            }
        }
        if (pkcsCalls.isEmpty()) return null;
        summary.pkcs5ClinitClasses++;
        Candidate candidate = new Candidate(owner.name,
                clinit.instructions.size(), pkcsCalls.size());
        if (pkcsCalls.size() != 1) {
            return candidate.reject("pkcs5-call-count=" + pkcsCalls.size());
        }
        Code code = new Code(clinit);
        AbstractInsnNode startNode = previousCode(pkcsCalls.get(0));
        int start = code.index(startNode);
        if (!(startNode instanceof LdcInsnNode) || start < 0
                || !ALGORITHM.equals(((LdcInsnNode) startNode).cst)) {
            return candidate.reject("missing-algorithm-entry");
        }

        List<ArrayAllocation> allocations = new ArrayList<>();
        for (int i = start; i < code.nodes.size(); i++) {
            AbstractInsnNode insn = code.nodes.get(i);
            if (!(insn instanceof TypeInsnNode)
                    || insn.getOpcode() != Opcodes.ANEWARRAY
                    || !"java/lang/String".equals(((TypeInsnNode) insn).desc)) {
                continue;
            }
            Integer capacity = intConstant(i == 0 ? null : code.nodes.get(i - 1));
            AbstractInsnNode next = i + 1 < code.nodes.size()
                    ? code.nodes.get(i + 1) : null;
            if (capacity != null && capacity > 0 && next instanceof VarInsnNode
                    && next.getOpcode() == Opcodes.ASTORE) {
                allocations.add(new ArrayAllocation(i - 1, i, i + 1,
                        capacity, ((VarInsnNode) next).var));
            }
        }
        if (allocations.size() != 1) {
            return candidate.reject("local-string-array-count="
                    + allocations.size());
        }
        ArrayAllocation allocation = allocations.get(0);
        candidate.capacity = allocation.capacity;
        candidate.arrayLocal = allocation.local;

        if (stateDerived) {
            if (keyProof == null) {
                return candidate.reject("state-class-key-unproven");
            }
            String keyFailure = deriveStateKey(owner, clinit, code, start,
                    allocation.storeIndex, keyProof, candidate);
            if (keyFailure != null) return candidate.reject(keyFailure);
        } else {
            Set<Long> keys = new LinkedHashSet<>();
            int keyLoads = 0;
            for (int i = start; i <= allocation.storeIndex; i++) {
                AbstractInsnNode insn = code.nodes.get(i);
                if (insn instanceof LdcInsnNode
                        && ((LdcInsnNode) insn).cst instanceof Long) {
                    keys.add((Long) ((LdcInsnNode) insn).cst);
                    keyLoads++;
                }
            }
            if (keys.size() != 1 || keyLoads != 2) {
                return candidate.reject("constant-key-shape=unique:" + keys.size()
                        + ",loads:" + keyLoads);
            }
            candidate.key = keys.iterator().next();
            candidate.keySource = "literal-key";
        }

        int outputLocal = findOutputLocal(code, allocation.storeIndex);
        if (outputLocal < 0 || outputLocal == allocation.local) {
            return candidate.reject("missing-output-counter");
        }
        candidate.outputLocal = outputLocal;

        List<PackedLoop> loops = new ArrayList<>();
        for (int i = allocation.storeIndex + 1; i < code.nodes.size(); i++) {
            AbstractInsnNode insn = code.nodes.get(i);
            if (!(insn instanceof LdcInsnNode)
                    || !(((LdcInsnNode) insn).cst instanceof String)) continue;
            String value = (String) ((LdcInsnNode) insn).cst;
            if (ALGORITHM.equals(value) || KEY_ALGORITHM.equals(value)
                    || LATIN1.equals(value)) continue;
            PackedLoop loop = parsePackedLoop(owner, code, i, allocation.local,
                    outputLocal);
            if (loop != null) loops.add(loop);
        }
        if (loops.isEmpty()) return candidate.reject("no-packed-array-loops");
        Collections.sort(loops, Comparator.comparingInt(loop -> loop.literalIndex));
        for (int i = 0; i + 1 < loops.size(); i++) {
            if (loops.get(i).endIndex != loops.get(i + 1).literalIndex) {
                return candidate.reject("packed-loop-chain-gap="
                        + loops.get(i).endIndex + "/"
                        + loops.get(i + 1).literalIndex);
            }
        }
        int end = loops.get(loops.size() - 1).endIndex;
        if (end <= allocation.storeIndex || end >= code.nodes.size()) {
            return candidate.reject("invalid-region-end=" + end);
        }
        candidate.startCodeIndex = start;
        candidate.endCodeIndex = end;
        candidate.startNode = code.nodes.get(start);
        candidate.endNode = code.nodes.get(end);
        candidate.helperName = loops.get(0).helperName;
        for (PackedLoop loop : loops) {
            if (!candidate.helperName.equals(loop.helperName)) {
                return candidate.reject("multiple-byte-decoders");
            }
        }
        candidate.packedLiterals = loops.size();

        String shapeFailure = validateRegionShape(owner, code, candidate, loops);
        if (shapeFailure != null) return candidate.reject(shapeFailure);
        String cfgFailure = validateCfgBoundary(code, start, end);
        if (cfgFailure != null) return candidate.reject(cfgFailure);
        String exceptionFailure = validateExceptionRanges(clinit, code,
                start, end);
        if (exceptionFailure != null) return candidate.reject(exceptionFailure);
        String stackFailure = validateBoundaryFrames(owner, clinit, code, start, end);
        if (stackFailure != null) return candidate.reject(stackFailure);
        String useFailure = validateArrayConsumers(code, end, allocation.local,
                allocation.capacity, candidate, allowStaticFieldEscape);
        if (useFailure != null) return candidate.reject(useFailure);

        MethodNode helper = method(owner, candidate.helperName, DECODE_DESC);
        if (!isExactZkmByteDecoder(helper)) {
            return candidate.reject("decoder-not-proven=" + candidate.helperName
                    + DECODE_DESC);
        }

        try {
            for (PackedLoop loop : loops) {
                List<String> values = unpackAndDecrypt(loop.ciphertext,
                        loop.initialChunkLength, candidate.key);
                loop.plaintexts.addAll(values);
                candidate.plaintexts.addAll(values);
            }
        } catch (Throwable failure) {
            return candidate.reject("decrypt:" + shortReason(failure));
        }
        if (candidate.plaintexts.size() != candidate.capacity) {
            return candidate.reject("array-capacity-mismatch="
                    + candidate.plaintexts.size() + "/" + candidate.capacity);
        }
        for (String value : candidate.plaintexts) {
            if (value.indexOf('\u0000') >= 0) {
                return candidate.reject("plaintext-contains-nul");
            }
        }

        MethodRef helperRef = new MethodRef(owner.name, candidate.helperName,
                DECODE_DESC);
        candidate.helperReferences = references.containsKey(helperRef)
                ? references.get(helperRef) : 0;
        candidate.removeHelper = candidate.helperReferences == loops.size();
        candidate.action = "PROVEN";
        return candidate;
    }

    private static Candidate inspectFlexibleMaterialization(
            ClassNode owner, Map<MethodRef, Integer> references,
            Summary summary, StateKeyProof keyProof,
            Set<Long> classKeyCandidates) {
        MethodNode clinit = method(owner, "<clinit>", "()V");
        if (clinit == null) return null;
        List<MethodInsnNode> factories = new ArrayList<>();
        for (AbstractInsnNode insn = clinit.instructions.getFirst(); insn != null;
             insn = insn.getNext()) {
            if (isCipherFactory(insn, ALGORITHM)) {
                factories.add((MethodInsnNode) insn);
            }
        }
        if (factories.isEmpty()) return null;
        summary.pkcs5ClinitClasses++;
        Candidate candidate = new Candidate(owner.name,
                clinit.instructions.size(), factories.size());
        candidate.flexibleMaterialization = true;
        if (factories.size() != 1) {
            return candidate.reject("pkcs5-call-count=" + factories.size());
        }
        Code code = new Code(clinit);
        AbstractInsnNode startNode = previousCode(factories.get(0));
        int start = code.index(startNode);
        if (!(startNode instanceof LdcInsnNode) || start < 0
                || !ALGORITHM.equals(((LdcInsnNode) startNode).cst)) {
            return candidate.reject("missing-algorithm-entry");
        }

        List<ArrayAllocation> allocations = new ArrayList<>();
        for (int index = start; index < code.nodes.size(); index++) {
            AbstractInsnNode insn = code.nodes.get(index);
            if (!(insn instanceof TypeInsnNode)
                    || insn.getOpcode() != Opcodes.ANEWARRAY
                    || !"java/lang/String".equals(
                    ((TypeInsnNode) insn).desc)) continue;
            Integer capacity = intConstant(index == 0
                    ? null : code.nodes.get(index - 1));
            AbstractInsnNode next = index + 1 < code.nodes.size()
                    ? code.nodes.get(index + 1) : null;
            if (capacity != null && capacity > 0
                    && next instanceof VarInsnNode
                    && next.getOpcode() == Opcodes.ASTORE) {
                allocations.add(new ArrayAllocation(index - 1, index,
                        index + 1, capacity, ((VarInsnNode) next).var));
            }
        }
        if (allocations.size() != 1) {
            return candidate.reject("materialization-array-count="
                    + allocations.size());
        }
        ArrayAllocation allocation = allocations.get(0);
        candidate.capacity = allocation.capacity;
        candidate.arrayLocal = allocation.local;

        List<ArrayKeyOption> keyOptions = flexibleKeyOptions(code, start,
                allocation.storeIndex, keyProof, classKeyCandidates);
        if (keyOptions.isEmpty()) {
            return candidate.reject("materialization-key-options=0");
        }
        int outputLocal = findOutputLocal(code, allocation.storeIndex);
        List<PackedLoop> structuralLoops = new ArrayList<>();
        if (outputLocal >= 0 && outputLocal != allocation.local) {
            for (int index = allocation.storeIndex + 1;
                 index < code.nodes.size(); index++) {
                AbstractInsnNode insn = code.nodes.get(index);
                if (!(insn instanceof LdcInsnNode)
                        || !(((LdcInsnNode) insn).cst instanceof String)) continue;
                PackedLoop loop = parsePackedLoop(owner, code, index,
                        allocation.local, outputLocal);
                if (loop != null) structuralLoops.add(loop);
            }
        }
        List<ArrayTableOption> passing = new ArrayList<>();
        int maximumValues = 0;
        int maximumNulValues = 0;
        String structuralFailure = "";
        for (ArrayKeyOption key : keyOptions) {
            List<ZkmStringDecryptor.TableCandidate> fragments =
                    ZkmStringDecryptor.genericOuterCandidates(clinit, key.key);
            List<ZkmStringDecryptor.TableCandidate> afterAllocation =
                    new ArrayList<>();
            for (ZkmStringDecryptor.TableCandidate fragment : fragments) {
                if (fragment.literalInstructions.isEmpty()) continue;
                AbstractInsnNode literal = clinit.instructions.get(
                        fragment.literalInstructions.get(0));
                if (code.index(literal) > allocation.storeIndex) {
                    afterAllocation.add(fragment);
                }
            }
            List<String> values = new ArrayList<>();
            List<Integer> literalInstructions = new ArrayList<>();
            for (ZkmStringDecryptor.TableCandidate fragment : afterAllocation) {
                values.addAll(fragment.entries);
                literalInstructions.addAll(fragment.literalInstructions);
            }
            maximumValues = Math.max(maximumValues, values.size());
            int packedLiterals = afterAllocation.size();
            if (values.size() != allocation.capacity
                    && !structuralLoops.isEmpty()) {
                values.clear();
                literalInstructions.clear();
                try {
                    for (PackedLoop loop : structuralLoops) {
                        values.addAll(unpackAndDecrypt(loop.ciphertext,
                                loop.initialChunkLength, key.key));
                        literalInstructions.add(clinit.instructions.indexOf(
                                code.nodes.get(loop.literalIndex)));
                    }
                    packedLiterals = structuralLoops.size();
                } catch (Throwable ignored) {
                    structuralFailure = shortReason(ignored);
                    values.clear();
                    literalInstructions.clear();
                }
            }
            maximumValues = Math.max(maximumValues, values.size());
            if (values.size() != allocation.capacity
                    || literalInstructions.isEmpty()) continue;
            boolean valid = true;
            int nulValues = 0;
            for (String value : values) {
                if (value.indexOf('\u0000') >= 0) {
                    valid = false;
                    nulValues++;
                }
            }
            if (!key.stateDerived) valid = true;
            maximumNulValues = Math.max(maximumNulValues, nulValues);
            if (valid) passing.add(new ArrayTableOption(key,
                    packedLiterals, literalInstructions, values));
        }
        if (passing.size() != 1) {
            return candidate.reject("materialization-key-oracle="
                    + passing.size() + "/" + keyOptions.size()
                    + ";output-local=" + outputLocal
                    + ";structural-loops=" + structuralLoops.size()
                    + ";max-values=" + maximumValues
                    + ";max-nul-values=" + maximumNulValues
                    + ";structural-failure=" + structuralFailure);
        }
        ArrayTableOption table = passing.get(0);

        Set<String> decoders = new LinkedHashSet<>();
        for (AbstractInsnNode insn = clinit.instructions.getFirst(); insn != null;
             insn = insn.getNext()) {
            if (!(insn instanceof MethodInsnNode)) continue;
            MethodInsnNode call = (MethodInsnNode) insn;
            if (call.getOpcode() == Opcodes.INVOKESTATIC
                    && owner.name.equals(call.owner)
                    && DECODE_DESC.equals(call.desc)
                    && isExactZkmByteDecoder(
                    method(owner, call.name, call.desc))) {
                decoders.add(call.name);
            }
        }
        if (decoders.size() != 1) {
            return candidate.reject("materialization-byte-decoders="
                    + decoders.size());
        }
        candidate.helperName = decoders.iterator().next();

        Set<Integer> literalCodeIndices = new LinkedHashSet<>();
        int lastLiteral = allocation.storeIndex;
        for (int instruction : table.literalInstructions) {
            AbstractInsnNode literal = clinit.instructions.get(instruction);
            int codeIndex = code.index(literal);
            if (codeIndex < 0) {
                return candidate.reject("materialization-literal-metadata");
            }
            literalCodeIndices.add(codeIndex);
            lastLiteral = Math.max(lastLiteral, codeIndex);
        }
        FlexibleBoundary boundary = findFlexibleBoundary(owner, clinit, code,
                start, lastLiteral, allocation, literalCodeIndices,
                candidate.helperName);
        if (boundary == null) {
            return candidate.reject("materialization-closed-boundary");
        }

        candidate.startCodeIndex = start;
        candidate.endCodeIndex = boundary.index;
        candidate.startNode = code.nodes.get(start);
        candidate.endNode = code.nodes.get(boundary.index);
        candidate.packedLiterals = table.packedLiterals;
        candidate.plaintexts.addAll(table.values);
        candidate.key = table.key.key;
        candidate.classKey = table.key.classKey;
        candidate.outerMask = table.key.mask;
        candidate.stateDerived = table.key.stateDerived;
        candidate.keySource = table.key.source;
        candidate.keyChain = keyProof == null ? "" : keyProof.chain;
        MethodRef decoder = new MethodRef(owner.name, candidate.helperName,
                DECODE_DESC);
        candidate.helperReferences = references.containsKey(decoder)
                ? references.get(decoder) : 0;
        candidate.removeHelper = false;
        for (int index = boundary.index; index < code.nodes.size(); index++) {
            AbstractInsnNode insn = code.nodes.get(index);
            if (insn instanceof VarInsnNode
                    && insn.getOpcode() == Opcodes.ALOAD
                    && ((VarInsnNode) insn).var == allocation.local) {
                candidate.consumerLoads++;
            }
        }
        candidate.action = "PROVEN";
        candidate.reason = "closed-array-materialization;unique-capacity-key;"
                + "business-continuation-preserved";
        return candidate;
    }

    private static List<ArrayKeyOption> flexibleKeyOptions(
            Code code, int start, int keyEnd, StateKeyProof keyProof,
            Set<Long> classKeyCandidates) {
        Map<Long, ArrayKeyOption> result = new LinkedHashMap<>();
        Long mask = null;
        for (int index = 1; index < start; index++) {
            if (code.nodes.get(index).getOpcode() != Opcodes.LXOR) continue;
            AbstractInsnNode previous = code.nodes.get(index - 1);
            if (previous instanceof LdcInsnNode
                    && ((LdcInsnNode) previous).cst instanceof Long) {
                if (mask != null && mask.longValue()
                        != ((Long) ((LdcInsnNode) previous).cst).longValue()) {
                    return Collections.emptyList();
                }
                mask = (Long) ((LdcInsnNode) previous).cst;
            }
        }
        if (mask != null && keyProof != null) {
            Set<Long> classKeys = new LinkedHashSet<>();
            classKeys.add(keyProof.classKey);
            if (classKeyCandidates != null) classKeys.addAll(classKeyCandidates);
            for (long classKey : classKeys) {
                long key = classKey ^ mask;
                result.put(key, new ArrayKeyOption(classKey, mask, key, true,
                        "state-model+pkcs5-capacity-oracle"));
            }
        }
        Set<Long> literals = new LinkedHashSet<>();
        for (int index = start; index <= keyEnd; index++) {
            AbstractInsnNode insn = code.nodes.get(index);
            if (insn instanceof LdcInsnNode
                    && ((LdcInsnNode) insn).cst instanceof Long) {
                literals.add((Long) ((LdcInsnNode) insn).cst);
            }
        }
        for (long literal : literals) {
            result.put(literal, new ArrayKeyOption(0L, 0L, literal, false,
                    "literal-key"));
        }
        return new ArrayList<>(result.values());
    }

    private static FlexibleBoundary findFlexibleBoundary(
            ClassNode owner, MethodNode method, Code code, int start,
            int lastLiteral, ArrayAllocation allocation,
            Set<Integer> literalIndices, String decoder) {
        Frame<BasicValue>[] frames;
        try {
            frames = new Analyzer<BasicValue>(new BasicVerifier())
                    .analyze(owner.name, method);
        } catch (Throwable failure) {
            return null;
        }
        int startTree = method.instructions.indexOf(code.nodes.get(start));
        if (startTree < 0 || startTree >= frames.length
                || frames[startTree] == null) {
            return null;
        }
        Frame<BasicValue> entryFrame = frames[startTree];
        List<Set<Integer>> liveInLocals = flexibleLiveInLocals(code);
        FlexibleBoundary best = null;
        for (int boundary = allocation.storeIndex + 1;
             boundary < code.nodes.size(); boundary++) {
            int tree = method.instructions.indexOf(code.nodes.get(boundary));
            Frame<BasicValue> frame = tree < 0 ? null : frames[tree];
            if (frame == null || frame.getStackSize() != 0) continue;
            if (!flexibleBoundaryLocalsAvailable(entryFrame, frame,
                    liveInLocals.get(boundary), allocation.local)) continue;
            Set<Integer> region = closedFlexibleRegion(code, start, boundary);
            if (region == null || !region.contains(allocation.storeIndex)
                    || !region.containsAll(literalIndices)) continue;
            if (flexibleExternalInbound(code, region, start) != null) continue;
            if (validateFlexibleCryptoRegion(owner, code, region,
                    allocation.local, decoder) != null) continue;
            if (best == null || region.size() < best.region.size()) {
                best = new FlexibleBoundary(boundary, region);
            }
        }
        return best;
    }

    private static List<Set<Integer>> flexibleLiveInLocals(Code code) {
        List<List<Integer>> successors = code.successors();
        List<Set<Integer>> liveIn = new ArrayList<>();
        for (int index = 0; index < code.nodes.size(); index++) {
            liveIn.add(new LinkedHashSet<Integer>());
        }
        boolean changed;
        do {
            changed = false;
            for (int index = code.nodes.size() - 1; index >= 0; index--) {
                Set<Integer> next = new LinkedHashSet<>();
                for (int successor : successors.get(index)) {
                    if (successor >= 0 && successor < liveIn.size()) {
                        next.addAll(liveIn.get(successor));
                    }
                }
                AbstractInsnNode insn = code.nodes.get(index);
                if (insn instanceof VarInsnNode) {
                    VarInsnNode variable = (VarInsnNode) insn;
                    int opcode = variable.getOpcode();
                    if (isLocalStore(opcode)) {
                        next.remove(variable.var);
                        if (opcode == Opcodes.LSTORE || opcode == Opcodes.DSTORE) {
                            next.remove(variable.var + 1);
                        }
                    } else if (isLocalLoad(opcode) || opcode == Opcodes.RET) {
                        next.add(variable.var);
                    }
                } else if (insn instanceof IincInsnNode) {
                    next.add(((IincInsnNode) insn).var);
                }
                if (!next.equals(liveIn.get(index))) {
                    liveIn.set(index, next);
                    changed = true;
                }
            }
        } while (changed);
        return liveIn;
    }

    private static boolean flexibleBoundaryLocalsAvailable(
            Frame<BasicValue> entry, Frame<BasicValue> boundary,
            Set<Integer> liveLocals, int materializedArrayLocal) {
        for (int local : liveLocals) {
            if (local == materializedArrayLocal) continue;
            if (local < 0 || local >= boundary.getLocals()) return false;
            BasicValue expected = boundary.getLocal(local);
            if (expected == null || BasicValue.UNINITIALIZED_VALUE.equals(expected)) {
                continue;
            }
            if (local >= entry.getLocals()) return false;
            BasicValue available = entry.getLocal(local);
            if (available == null || !expected.equals(available)) return false;
        }
        return true;
    }

    private static boolean isLocalLoad(int opcode) {
        return opcode >= Opcodes.ILOAD && opcode <= Opcodes.ALOAD;
    }

    private static boolean isLocalStore(int opcode) {
        return opcode >= Opcodes.ISTORE && opcode <= Opcodes.ASTORE;
    }

    private static Set<Integer> closedFlexibleRegion(
            Code code, int start, int boundary) {
        List<List<Integer>> successors = code.successors();
        Set<Integer> region = new LinkedHashSet<>();
        ArrayDeque<Integer> queue = new ArrayDeque<>();
        queue.add(start);
        boolean reachesBoundary = false;
        while (!queue.isEmpty()) {
            int current = queue.removeFirst();
            if (current == boundary) {
                reachesBoundary = true;
                continue;
            }
            if (current < 0 || current >= code.nodes.size()
                    || !region.add(current)) continue;
            List<Integer> next = successors.get(current);
            if (next.isEmpty()) return null;
            for (int target : next) queue.add(target);
        }
        return reachesBoundary ? region : null;
    }

    private static String flexibleExternalInbound(
            Code code, Set<Integer> region, int start) {
        List<List<Integer>> successors = code.successors();
        for (int source = 0; source < successors.size(); source++) {
            for (int target : successors.get(source)) {
                if (region.contains(target) && !region.contains(source)
                        && target != start) {
                    return source + "->" + target;
                }
            }
        }
        return null;
    }

    private static String validateFlexibleCryptoRegion(
            ClassNode owner, Code code, Set<Integer> region,
            int arrayLocal, String decoder) {
        int factories = 0;
        int finals = 0;
        int decodes = 0;
        int interns = 0;
        int stringArrays = 0;
        int arrayStores = 0;
        int arrayLoads = 0;
        for (int index : region) {
            AbstractInsnNode insn = code.nodes.get(index);
            int opcode = insn.getOpcode();
            if (insn instanceof FieldInsnNode
                    || insn instanceof InvokeDynamicInsnNode) {
                return "side-effect=" + index;
            }
            if (opcode == Opcodes.RETURN || opcode == Opcodes.ATHROW
                    || opcode == Opcodes.MONITORENTER
                    || opcode == Opcodes.MONITOREXIT) {
                return "terminal=" + index;
            }
            if (insn instanceof TypeInsnNode) {
                TypeInsnNode type = (TypeInsnNode) insn;
                boolean allowed = opcode == Opcodes.NEW
                        && ("javax/crypto/spec/DESKeySpec".equals(type.desc)
                        || "javax/crypto/spec/IvParameterSpec".equals(type.desc))
                        || opcode == Opcodes.ANEWARRAY
                        && "java/lang/String".equals(type.desc);
                if (!allowed) return "type=" + type.desc;
                if (opcode == Opcodes.ANEWARRAY) stringArrays++;
            }
            if (insn instanceof MethodInsnNode) {
                MethodInsnNode call = (MethodInsnNode) insn;
                boolean allowed = isCipherFactory(call, ALGORITHM)
                        || isCall(call, Opcodes.INVOKESTATIC,
                        "javax/crypto/SecretKeyFactory", "getInstance",
                        "(Ljava/lang/String;)Ljavax/crypto/SecretKeyFactory;")
                        || isCall(call, Opcodes.INVOKESPECIAL,
                        "javax/crypto/spec/DESKeySpec", "<init>", "([B)V")
                        || isCall(call, Opcodes.INVOKEVIRTUAL,
                        "javax/crypto/SecretKeyFactory", "generateSecret",
                        "(Ljava/security/spec/KeySpec;)Ljavax/crypto/SecretKey;")
                        || isCall(call, Opcodes.INVOKESPECIAL,
                        "javax/crypto/spec/IvParameterSpec", "<init>", "([B)V")
                        || isCall(call, Opcodes.INVOKEVIRTUAL,
                        "javax/crypto/Cipher", "init",
                        "(ILjava/security/Key;Ljava/security/spec/AlgorithmParameterSpec;)V")
                        || isCall(call, Opcodes.INVOKEVIRTUAL,
                        "javax/crypto/Cipher", "doFinal", "([B)[B")
                        || isCall(call, Opcodes.INVOKEVIRTUAL,
                        "java/lang/String", "getBytes",
                        "(Ljava/lang/String;)[B")
                        || isCall(call, Opcodes.INVOKEVIRTUAL,
                        "java/lang/String", "substring", "(II)Ljava/lang/String;")
                        || isCall(call, Opcodes.INVOKEVIRTUAL,
                        "java/lang/String", "length", "()I")
                        || isCall(call, Opcodes.INVOKEVIRTUAL,
                        "java/lang/String", "charAt", "(I)C")
                        || isCall(call, Opcodes.INVOKEVIRTUAL,
                        "java/lang/String", "intern", "()Ljava/lang/String;")
                        || isCall(call, Opcodes.INVOKESTATIC, owner.name,
                        decoder, DECODE_DESC);
                if (!allowed) return "call=" + call.owner + "." + call.name;
                if (isCipherFactory(call, ALGORITHM)) factories++;
                if (isCall(call, Opcodes.INVOKEVIRTUAL,
                        "javax/crypto/Cipher", "doFinal", "([B)[B")) finals++;
                if (isCall(call, Opcodes.INVOKESTATIC, owner.name,
                        decoder, DECODE_DESC)) decodes++;
                if (isCall(call, Opcodes.INVOKEVIRTUAL,
                        "java/lang/String", "intern", "()Ljava/lang/String;")) {
                    interns++;
                }
            }
            if (opcode == Opcodes.AASTORE) arrayStores++;
            if (insn instanceof VarInsnNode
                    && opcode == Opcodes.ALOAD
                    && ((VarInsnNode) insn).var == arrayLocal) arrayLoads++;
        }
        if (factories != 1 || finals < 1 || decodes < 1 || interns < 1
                || stringArrays != 1 || arrayStores < 1 || arrayLoads < 1) {
            return "crypto-shape=" + factories + "," + finals + ","
                    + decodes + "," + interns + "," + stringArrays + ","
                    + arrayStores + "," + arrayLoads;
        }
        return null;
    }

    private static String deriveStateKey(
            ClassNode owner, MethodNode clinit, Code code, int start,
            int keyRegionEnd, StateKeyProof proof, Candidate candidate) {
        if (!owner.name.equals(proof.owner)) {
            return "key-proof-owner=" + proof.owner;
        }
        Set<Integer> keyLocals = new LinkedHashSet<>();
        for (int index = start; index <= keyRegionEnd; index++) {
            AbstractInsnNode insn = code.nodes.get(index);
            if (insn instanceof VarInsnNode
                    && insn.getOpcode() == Opcodes.LLOAD) {
                keyLocals.add(((VarInsnNode) insn).var);
            }
        }
        if (keyLocals.size() != 1) {
            return "state-key-long-loads=" + keyLocals;
        }
        int keyLocal = keyLocals.iterator().next();
        int definition = -1;
        int definitions = 0;
        for (int index = 0; index < start; index++) {
            AbstractInsnNode insn = code.nodes.get(index);
            if (insn instanceof VarInsnNode
                    && insn.getOpcode() == Opcodes.LSTORE
                    && ((VarInsnNode) insn).var == keyLocal) {
                definition = index;
                definitions++;
            }
        }
        if (definitions != 1 || definition < 1
                || code.nodes.get(definition - 1).getOpcode() != Opcodes.LXOR) {
            return "state-key-local-definition=" + definitions;
        }

        AbstractInsnNode xor = code.nodes.get(definition - 1);
        AbstractInsnNode maskNode;
        AbstractInsnNode keyNode;
        try {
            Frame<SourceValue>[] frames = new Analyzer<SourceValue>(
                    new SourceInterpreter()).analyze(owner.name, clinit);
            Frame<SourceValue> frame = frames[clinit.instructions.indexOf(xor)];
            if (frame == null || frame.getStackSize() < 2) {
                return "state-key-xor-frame";
            }
            maskNode = uniqueSource(frame.getStack(frame.getStackSize() - 1));
            keyNode = uniqueSource(frame.getStack(frame.getStackSize() - 2));
        } catch (Throwable failure) {
            return "state-key-source-analysis=" + shortReason(failure);
        }
        if (!(maskNode instanceof LdcInsnNode)
                || !(((LdcInsnNode) maskNode).cst instanceof Long)) {
            return "state-key-xor-mask-source";
        }

        MethodInsnNode transform;
        if (keyNode instanceof MethodInsnNode
                && isStateTransform((MethodInsnNode) keyNode)) {
            transform = (MethodInsnNode) keyNode;
        } else if (keyNode instanceof FieldInsnNode
                && keyNode.getOpcode() == Opcodes.GETSTATIC) {
            FieldInsnNode read = (FieldInsnNode) keyNode;
            if (!owner.name.equals(read.owner) || !"J".equals(read.desc)) {
                return "state-key-field=" + read.owner + "." + read.name
                        + read.desc;
            }
            FieldNode keyField = field(owner, read.name, read.desc);
            if (keyField == null
                    || (keyField.access & (Opcodes.ACC_STATIC | Opcodes.ACC_FINAL))
                    != (Opcodes.ACC_STATIC | Opcodes.ACC_FINAL)) {
                return "state-key-field-not-static-final=" + read.name;
            }
            transform = null;
            for (int index = 1; index < definition; index++) {
                AbstractInsnNode insn = code.nodes.get(index);
                if (!(insn instanceof FieldInsnNode)
                        || insn.getOpcode() != Opcodes.PUTSTATIC) continue;
                FieldInsnNode write = (FieldInsnNode) insn;
                if (!read.owner.equals(write.owner)
                        || !read.name.equals(write.name)
                        || !read.desc.equals(write.desc)) continue;
                AbstractInsnNode producer = code.nodes.get(index - 1);
                if (!(producer instanceof MethodInsnNode)
                        || !isStateTransform((MethodInsnNode) producer)
                        || transform != null) {
                    return "state-key-field-transform=" + read.name;
                }
                transform = (MethodInsnNode) producer;
            }
            if (transform == null) return "state-key-field-write=" + read.name;
        } else {
            return "state-key-value-source=" + (keyNode == null ? "null"
                    : keyNode.getClass().getSimpleName() + ":"
                    + keyNode.getOpcode());
        }

        int bootstraps = 0;
        int transforms = 0;
        for (int index = 0; index < start; index++) {
            AbstractInsnNode insn = code.nodes.get(index);
            if (!(insn instanceof MethodInsnNode)) continue;
            MethodInsnNode call = (MethodInsnNode) insn;
            if (call.getOpcode() == Opcodes.INVOKESTATIC
                    && STATE.equals(call.owner) && "a".equals(call.name)
                    && ObfRuntimeNames.BOOTSTRAP_DESC
                    .equals(call.desc)) bootstraps++;
            if (isStateTransform(call)) transforms++;
        }
        if (bootstraps != 1 || transforms != 1) {
            return "state-key-call-count=" + bootstraps + "/" + transforms;
        }
        candidate.classKey = proof.classKey;
        candidate.outerMask = (Long) ((LdcInsnNode) maskNode).cst;
        candidate.key = candidate.classKey ^ candidate.outerMask;
        candidate.keySource = proof.source;
        candidate.keyChain = proof.chain;
        candidate.stateDerived = true;
        return null;
    }

    private static AbstractInsnNode uniqueSource(SourceValue value) {
        if (value == null || value.insns == null || value.insns.size() != 1) {
            return null;
        }
        return value.insns.iterator().next();
    }

    private static boolean isStateTransform(MethodInsnNode call) {
        return call.getOpcode() == Opcodes.INVOKEINTERFACE
                && STATE_IFACE.equals(call.owner) && "a".equals(call.name)
                && "(J)J".equals(call.desc);
    }

    private static int findOutputLocal(Code code, int arrayStore) {
        int limit = Math.min(code.nodes.size(), arrayStore + 8);
        for (int i = arrayStore + 1; i + 1 < limit; i++) {
            Integer value = intConstant(code.nodes.get(i));
            AbstractInsnNode next = code.nodes.get(i + 1);
            if (value != null && value == 0 && next instanceof VarInsnNode
                    && next.getOpcode() == Opcodes.ISTORE) {
                return ((VarInsnNode) next).var;
            }
        }
        return -1;
    }

    private static PackedLoop parsePackedLoop(ClassNode owner, Code code,
                                               int literalIndex, int arrayLocal,
                                               int outputLocal) {
        LdcInsnNode literal = (LdcInsnNode) code.nodes.get(literalIndex);
        String ciphertext = (String) literal.cst;
        if (!latin1(ciphertext) || ciphertext.isEmpty()) return null;
        int cursor = literalIndex + 1;
        if (cursor < code.nodes.size()
                && code.nodes.get(cursor).getOpcode() == Opcodes.DUP) cursor++;
        if (cursor >= code.nodes.size()
                || !(code.nodes.get(cursor) instanceof VarInsnNode)
                || code.nodes.get(cursor).getOpcode() != Opcodes.ASTORE) return null;
        cursor++;
        if (cursor >= code.nodes.size() || !isCall(code.nodes.get(cursor),
                Opcodes.INVOKEVIRTUAL, "java/lang/String", "length", "()I")) {
            return null;
        }
        cursor++;
        if (cursor >= code.nodes.size()
                || !(code.nodes.get(cursor) instanceof VarInsnNode)
                || code.nodes.get(cursor).getOpcode() != Opcodes.ISTORE) return null;
        cursor++;
        if (cursor >= code.nodes.size()) return null;
        Integer initialLength = intConstant(code.nodes.get(cursor));
        if (initialLength == null || initialLength <= 0
                || initialLength % 8 != 0) return null;
        cursor++;
        if (cursor >= code.nodes.size()
                || !(code.nodes.get(cursor) instanceof VarInsnNode)
                || code.nodes.get(cursor).getOpcode() != Opcodes.ISTORE) return null;

        int limit = Math.min(code.nodes.size(), literalIndex + 150);
        int substring = 0, getBytes = 0, doFinal = 0, intern = 0;
        int length = 0, charAt = 0, stores = 0;
        int helperCalls = 0;
        String helperName = null;
        JumpInsnNode exit = null;
        int exitIndex = -1;
        int storeIndex = -1;
        for (int i = literalIndex; i < limit; i++) {
            AbstractInsnNode insn = code.nodes.get(i);
            if (isCall(insn, Opcodes.INVOKEVIRTUAL, "java/lang/String",
                    "length", "()I")) length++;
            else if (isCall(insn, Opcodes.INVOKEVIRTUAL, "java/lang/String",
                    "substring", "(II)Ljava/lang/String;")) substring++;
            else if (isCall(insn, Opcodes.INVOKEVIRTUAL, "java/lang/String",
                    "getBytes", "(Ljava/lang/String;)[B")) getBytes++;
            else if (isCall(insn, Opcodes.INVOKEVIRTUAL, "javax/crypto/Cipher",
                    "doFinal", "([B)[B")) doFinal++;
            else if (isCall(insn, Opcodes.INVOKEVIRTUAL, "java/lang/String",
                    "intern", "()Ljava/lang/String;")) intern++;
            else if (isCall(insn, Opcodes.INVOKEVIRTUAL, "java/lang/String",
                    "charAt", "(I)C")) charAt++;
            if (insn instanceof MethodInsnNode) {
                MethodInsnNode call = (MethodInsnNode) insn;
                if (call.getOpcode() == Opcodes.INVOKESTATIC
                        && owner.name.equals(call.owner)
                        && DECODE_DESC.equals(call.desc)) {
                    helperCalls++;
                    helperName = call.name;
                }
            }
            if (insn.getOpcode() == Opcodes.AASTORE) {
                stores++;
                storeIndex = i;
            }
            if (storeIndex >= 0 && insn instanceof JumpInsnNode
                    && insn.getOpcode() == Opcodes.IF_ICMPGE) {
                exit = (JumpInsnNode) insn;
                exitIndex = i;
                break;
            }
        }
        if (exit == null || substring != 1 || length != 1 || stores != 1) {
            return null;
        }

        int rawEnd = code.target(exit.label);
        int end = followGotoChain(code, rawEnd);
        if (end <= literalIndex || end >= code.nodes.size()) return null;
        // Split-block variants place the decrypt call after the exit test.
        substring = getBytes = doFinal = intern = length = charAt = stores = 0;
        helperCalls = 0;
        helperName = null;
        boolean backwardLoop = false;
        int arrayLoads = 0, outputIncrements = 0;
        for (int i = literalIndex; i < end; i++) {
            AbstractInsnNode insn = code.nodes.get(i);
            if (isCall(insn, Opcodes.INVOKEVIRTUAL, "java/lang/String",
                    "length", "()I")) length++;
            else if (isCall(insn, Opcodes.INVOKEVIRTUAL, "java/lang/String",
                    "substring", "(II)Ljava/lang/String;")) substring++;
            else if (isCall(insn, Opcodes.INVOKEVIRTUAL, "java/lang/String",
                    "getBytes", "(Ljava/lang/String;)[B")) getBytes++;
            else if (isCall(insn, Opcodes.INVOKEVIRTUAL, "javax/crypto/Cipher",
                    "doFinal", "([B)[B")) doFinal++;
            else if (isCall(insn, Opcodes.INVOKEVIRTUAL, "java/lang/String",
                    "intern", "()Ljava/lang/String;")) intern++;
            else if (isCall(insn, Opcodes.INVOKEVIRTUAL, "java/lang/String",
                    "charAt", "(I)C")) charAt++;
            if (insn instanceof MethodInsnNode) {
                MethodInsnNode call = (MethodInsnNode) insn;
                if (call.getOpcode() == Opcodes.INVOKESTATIC
                        && owner.name.equals(call.owner)
                        && DECODE_DESC.equals(call.desc)) {
                    helperCalls++;
                    helperName = call.name;
                }
            }
            if (insn.getOpcode() == Opcodes.AASTORE) stores++;
            if (insn instanceof VarInsnNode && insn.getOpcode() == Opcodes.ALOAD
                    && ((VarInsnNode) insn).var == arrayLocal) arrayLoads++;
            if (insn instanceof IincInsnNode
                    && ((IincInsnNode) insn).var == outputLocal
                    && ((IincInsnNode) insn).incr == 1) outputIncrements++;
            if (insn instanceof JumpInsnNode && insn.getOpcode() == Opcodes.GOTO
                    && code.target(((JumpInsnNode) insn).label) <= exitIndex) {
                backwardLoop = true;
            }
        }
        if (length != 1 || substring != 1 || getBytes != 1 || doFinal != 1
                || helperCalls != 1 || intern != 1 || charAt != 1
                || stores != 1 || arrayLoads != 1 || outputIncrements != 1
                || !backwardLoop) return null;
        return new PackedLoop(literalIndex, end, ciphertext, initialLength,
                helperName);
    }

    private static int followGotoChain(Code code, int index) {
        Set<Integer> seen = new HashSet<>();
        int current = index;
        while (current >= 0 && current < code.nodes.size()
                && seen.add(current)) {
            AbstractInsnNode insn = code.nodes.get(current);
            if (!(insn instanceof JumpInsnNode)
                    || insn.getOpcode() != Opcodes.GOTO) break;
            current = code.target(((JumpInsnNode) insn).label);
        }
        return current;
    }

    private static String validateRegionShape(ClassNode owner, Code code,
                                              Candidate candidate,
                                              List<PackedLoop> loops) {
        Map<String, Integer> expected = new HashMap<>();
        put(expected, call(Opcodes.INVOKESTATIC, "javax/crypto/Cipher",
                "getInstance", "(Ljava/lang/String;)Ljavax/crypto/Cipher;"), 1);
        put(expected, call(Opcodes.INVOKESTATIC,
                "javax/crypto/SecretKeyFactory", "getInstance",
                "(Ljava/lang/String;)Ljavax/crypto/SecretKeyFactory;"), 1);
        put(expected, call(Opcodes.INVOKESPECIAL,
                "javax/crypto/spec/DESKeySpec", "<init>", "([B)V"), 1);
        put(expected, call(Opcodes.INVOKEVIRTUAL,
                "javax/crypto/SecretKeyFactory", "generateSecret",
                "(Ljava/security/spec/KeySpec;)Ljavax/crypto/SecretKey;"), 1);
        put(expected, call(Opcodes.INVOKESPECIAL,
                "javax/crypto/spec/IvParameterSpec", "<init>", "([B)V"), 1);
        put(expected, call(Opcodes.INVOKEVIRTUAL, "javax/crypto/Cipher",
                "init", "(ILjava/security/Key;Ljava/security/spec/AlgorithmParameterSpec;)V"), 1);
        put(expected, call(Opcodes.INVOKEVIRTUAL, "java/lang/String",
                "length", "()I"), loops.size());
        put(expected, call(Opcodes.INVOKEVIRTUAL, "java/lang/String",
                "substring", "(II)Ljava/lang/String;"), loops.size());
        put(expected, call(Opcodes.INVOKEVIRTUAL, "java/lang/String",
                "getBytes", "(Ljava/lang/String;)[B"), loops.size());
        put(expected, call(Opcodes.INVOKEVIRTUAL, "javax/crypto/Cipher",
                "doFinal", "([B)[B"), loops.size());
        put(expected, call(Opcodes.INVOKESTATIC, owner.name,
                candidate.helperName, DECODE_DESC), loops.size());
        put(expected, call(Opcodes.INVOKEVIRTUAL, "java/lang/String",
                "intern", "()Ljava/lang/String;"), loops.size());
        put(expected, call(Opcodes.INVOKEVIRTUAL, "java/lang/String",
                "charAt", "(I)C"), loops.size());

        Map<String, Integer> actual = new HashMap<>();
        Set<String> packed = new HashSet<>();
        for (PackedLoop loop : loops) packed.add(loop.ciphertext);
        int byteArrays = 0, byteStores = 0, lushr = 0, lshl = 0, imul = 0;
        int stringArrays = 0, arrayLoads = 0, arrayStores = 0;
        for (int i = candidate.startCodeIndex; i < candidate.endCodeIndex; i++) {
            AbstractInsnNode insn = code.nodes.get(i);
            if (insn instanceof FieldInsnNode || insn instanceof InvokeDynamicInsnNode
                    || insn instanceof TableSwitchInsnNode
                    || insn instanceof LookupSwitchInsnNode
                    || insn instanceof MultiANewArrayInsnNode) {
                return "unsupported-region-instruction="
                        + insn.getClass().getSimpleName() + ":" + insn.getOpcode();
            }
            if (insn instanceof MethodInsnNode) {
                MethodInsnNode method = (MethodInsnNode) insn;
                increment(actual, call(method.getOpcode(), method.owner,
                        method.name, method.desc));
            } else if (insn instanceof TypeInsnNode) {
                TypeInsnNode type = (TypeInsnNode) insn;
                if (type.getOpcode() == Opcodes.ANEWARRAY
                        && "java/lang/String".equals(type.desc)) stringArrays++;
                else if (type.getOpcode() != Opcodes.NEW
                        || !("javax/crypto/spec/DESKeySpec".equals(type.desc)
                        || "javax/crypto/spec/IvParameterSpec".equals(type.desc))) {
                    return "unsupported-region-type=" + type.getOpcode()
                            + ":" + type.desc;
                }
            } else if (insn instanceof LdcInsnNode) {
                Object value = ((LdcInsnNode) insn).cst;
                if (value instanceof String && !ALGORITHM.equals(value)
                        && !KEY_ALGORITHM.equals(value) && !LATIN1.equals(value)
                        && !packed.contains(value)) {
                    return "unexpected-region-string-literal";
                }
                if (value instanceof Long
                        && ((Long) value).longValue() != candidate.key) {
                    return "unexpected-region-long";
                }
                if (value instanceof Handle || value instanceof ConstantDynamic) {
                    return "dynamic-region-constant";
                }
            }
            if (insn instanceof IntInsnNode
                    && insn.getOpcode() == Opcodes.NEWARRAY) {
                if (((IntInsnNode) insn).operand != Opcodes.T_BYTE) {
                    return "non-byte-primitive-array";
                }
                byteArrays++;
            }
            if (insn.getOpcode() == Opcodes.BASTORE) byteStores++;
            if (insn.getOpcode() == Opcodes.LUSHR) lushr++;
            if (insn.getOpcode() == Opcodes.LSHL) lshl++;
            if (insn.getOpcode() == Opcodes.IMUL) imul++;
            if (insn.getOpcode() == Opcodes.AASTORE) arrayStores++;
            if (insn instanceof VarInsnNode && insn.getOpcode() == Opcodes.ALOAD
                    && ((VarInsnNode) insn).var == candidate.arrayLocal) {
                arrayLoads++;
            }
            int opcode = insn.getOpcode();
            if (opcode == Opcodes.RETURN || opcode == Opcodes.ATHROW
                    || opcode == Opcodes.MONITORENTER || opcode == Opcodes.MONITOREXIT
                    || opcode == Opcodes.JSR || opcode == Opcodes.RET) {
                return "non-neutral-region-opcode=" + opcode;
            }
        }
        if (!actual.equals(expected)) {
            return "region-call-set=" + actual.size() + "/" + expected.size();
        }
        if (byteArrays != 2 || byteStores != 2 || lushr != 2 || lshl != 1
                || imul != 1 || stringArrays != 1) {
            return "key-array-shape=byte-arrays:" + byteArrays + ",byte-stores:"
                    + byteStores + ",lushr:" + lushr + ",lshl:" + lshl
                    + ",imul:" + imul + ",string-arrays:" + stringArrays;
        }
        if (arrayLoads != loops.size() || arrayStores != loops.size()) {
            return "array-fill-shape=loads:" + arrayLoads + ",stores:"
                    + arrayStores + ",loops:" + loops.size();
        }
        return null;
    }

    private static String validateCfgBoundary(Code code, int start, int end) {
        List<List<Integer>> successors = code.successors();
        for (int from = 0; from < successors.size(); from++) {
            for (int target : successors.get(from)) {
                boolean fromInside = from >= start && from < end;
                boolean targetInside = target >= start && target < end;
                if (!fromInside && targetInside && target != start) {
                    return "cfg-external-entry=" + from + "->" + target;
                }
                if (fromInside && !targetInside && target != end) {
                    return "cfg-nonunique-exit=" + from + "->" + target;
                }
            }
        }
        Set<Integer> reached = new HashSet<>();
        ArrayDeque<Integer> queue = new ArrayDeque<>();
        queue.add(start);
        while (!queue.isEmpty()) {
            int current = queue.removeFirst();
            if (!reached.add(current)) continue;
            for (int target : successors.get(current)) {
                if (target >= start && target < end) queue.addLast(target);
            }
        }
        if (reached.size() != end - start) {
            return "cfg-unreachable-region-nodes=" + reached.size() + "/"
                    + (end - start);
        }
        return null;
    }

    private static String validateExceptionRanges(MethodNode method, Code code,
                                                   int start, int end) {
        int coveringRanges = 0;
        for (TryCatchBlockNode block : method.tryCatchBlocks) {
            int tryStart = code.target(block.start);
            int tryEnd = code.target(block.end);
            int handler = code.target(block.handler);
            if (tryStart < 0 || tryEnd < 0 || handler < 0
                    || tryStart >= tryEnd) {
                return "invalid-exception-range";
            }
            boolean overlaps = tryStart < end && tryEnd > start;
            if (!overlaps) continue;
            if (tryStart > start || tryEnd < end) {
                return "exception-boundary-inside-region=" + tryStart + "-"
                        + tryEnd + "/" + start + "-" + end;
            }
            if (handler >= start && handler < end) {
                return "exception-handler-inside-region=" + handler;
            }
            coveringRanges++;
        }
        return coveringRanges > 1
                ? "multiple-covering-exception-ranges=" + coveringRanges : null;
    }

    private static String validateBoundaryFrames(ClassNode owner,
                                                 MethodNode method, Code code,
                                                 int start, int end) {
        try {
            Analyzer<BasicValue> analyzer = new Analyzer<>(new BasicVerifier());
            Frame<BasicValue>[] frames = analyzer.analyze(owner.name, method);
            int startTree = method.instructions.indexOf(code.nodes.get(start));
            int endTree = method.instructions.indexOf(code.nodes.get(end));
            Frame<BasicValue> before = frames[startTree];
            Frame<BasicValue> after = frames[endTree];
            if (before == null || after == null) return "unreachable-boundary";
            if (before.getStackSize() != 0 || after.getStackSize() != 0) {
                return "nonempty-boundary-stack=" + before.getStackSize()
                        + "/" + after.getStackSize();
            }
            return null;
        } catch (Throwable failure) {
            return "boundary-analysis:" + shortReason(failure);
        }
    }

    private static String validateArrayConsumers(Code code, int end,
                                                 int local, int capacity,
                                                 Candidate candidate,
                                                 boolean allowStaticFieldEscape) {
        int consumers = 0;
        int staticEscapes = 0;
        for (int i = end; i < code.nodes.size(); i++) {
            AbstractInsnNode insn = code.nodes.get(i);
            if (insn instanceof VarInsnNode && ((VarInsnNode) insn).var == local) {
                if (insn.getOpcode() == Opcodes.ASTORE) break;
                if (insn.getOpcode() != Opcodes.ALOAD) {
                    return "array-local-unsupported-use=" + i + ":"
                            + insn.getOpcode();
                }
                AbstractInsnNode next = i + 1 < code.nodes.size()
                        ? code.nodes.get(i + 1) : null;
                if (allowStaticFieldEscape && next instanceof FieldInsnNode
                        && next.getOpcode() == Opcodes.PUTSTATIC) {
                    FieldInsnNode field = (FieldInsnNode) next;
                    if (!candidate.owner.equals(field.owner)
                            || !"[Ljava/lang/String;".equals(field.desc)
                            || candidate.tableField != null
                            && !candidate.tableField.equals(field.name)) {
                        return "array-static-field-escape=" + i + ":"
                                + field.owner + "." + field.name + field.desc;
                    }
                    candidate.tableField = field.name;
                    staticEscapes++;
                    consumers++;
                    i++;
                    continue;
                }
                if (i + 2 >= code.nodes.size()) {
                    return "array-local-truncated-use=" + i;
                }
                Integer index = intConstant(code.nodes.get(i + 1));
                if (index == null || index < 0 || index >= capacity
                        || code.nodes.get(i + 2).getOpcode() != Opcodes.AALOAD) {
                    return "array-local-escapes=" + i;
                }
                consumers++;
            } else if (insn instanceof IincInsnNode
                    && ((IincInsnNode) insn).var == local) {
                return "array-local-iinc=" + i;
            }
        }
        if (consumers == 0) return "array-has-no-constant-consumers";
        if (allowStaticFieldEscape && staticEscapes != 1) {
            return "array-static-field-escape-count=" + staticEscapes;
        }
        candidate.consumerLoads = consumers;
        return null;
    }

    private static boolean isExactZkmByteDecoder(MethodNode method) {
        if (method == null || (method.access & (Opcodes.ACC_PRIVATE
                | Opcodes.ACC_STATIC)) != (Opcodes.ACC_PRIVATE
                | Opcodes.ACC_STATIC) || !DECODE_DESC.equals(method.desc)
                || !method.tryCatchBlocks.isEmpty()) return false;
        int charArrays = 0, charStores = 0, byteLoads = 0, returns = 0;
        int constructors = 0;
        Set<Integer> constants = new HashSet<>();
        for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
             insn = insn.getNext()) {
            if (insn.getOpcode() < 0) continue;
            Integer constant = intConstant(insn);
            if (constant != null) constants.add(constant);
            if (insn instanceof FieldInsnNode || insn instanceof InvokeDynamicInsnNode
                    || insn instanceof MultiANewArrayInsnNode
                    || insn instanceof TableSwitchInsnNode
                    || insn instanceof LookupSwitchInsnNode) return false;
            if (insn instanceof IntInsnNode && insn.getOpcode() == Opcodes.NEWARRAY
                    && ((IntInsnNode) insn).operand == Opcodes.T_CHAR) charArrays++;
            if (insn.getOpcode() == Opcodes.CASTORE) charStores++;
            if (insn.getOpcode() == Opcodes.BALOAD) byteLoads++;
            if (insn.getOpcode() == Opcodes.ARETURN) returns++;
            if (insn instanceof MethodInsnNode) {
                MethodInsnNode call = (MethodInsnNode) insn;
                if (call.getOpcode() == Opcodes.INVOKESPECIAL
                        && "java/lang/String".equals(call.owner)
                        && "<init>".equals(call.name)
                        && "([CII)V".equals(call.desc)) constructors++;
                else return false;
            }
            if (insn instanceof TypeInsnNode) {
                TypeInsnNode type = (TypeInsnNode) insn;
                if (type.getOpcode() != Opcodes.NEW
                        || !"java/lang/String".equals(type.desc)) return false;
            }
        }
        return charArrays == 1 && charStores == 3 && byteLoads == 4
                && returns == 1 && constructors == 1
                && constants.contains(255) && constants.contains(192)
                && constants.contains(224) && constants.contains(31)
                && constants.contains(63) && constants.contains(15)
                && constants.contains(6) && constants.contains(12);
    }

    private static List<String> unpackAndDecrypt(String packed,
                                                 int initialLength,
                                                 long key) throws Exception {
        List<String> result = new ArrayList<>();
        int cursor = 0;
        int length = initialLength;
        while (cursor < packed.length()) {
            if (length <= 0 || length % 8 != 0
                    || cursor + length > packed.length()) {
                throw new IllegalArgumentException("invalid-packed-boundary="
                        + cursor + "+" + length + "/" + packed.length());
            }
            result.add(decrypt(packed.substring(cursor, cursor + length), key));
            cursor += length;
            if (cursor == packed.length()) break;
            length = packed.charAt(cursor++);
        }
        if (cursor != packed.length() || result.isEmpty()) {
            throw new IllegalArgumentException("incomplete-packed-table");
        }
        return result;
    }

    private static String decrypt(String ciphertext, long keyValue)
            throws Exception {
        return ZkmDesConstantEvaluator.decryptZkmString(
                ZkmDesConstantEvaluator.KeyMaterial.proven(keyValue,
                        "LDC_LONG", "direct PKCS5 string array"), ciphertext);
    }

    private static void apply(ClassNode owner, Candidate candidate) {
        MethodNode clinit = method(owner, "<clinit>", "()V");
        if (clinit == null) throw new IllegalStateException("missing <clinit>");
        AbstractInsnNode start = nodeAtCodeIndex(clinit, candidate.startCodeIndex);
        AbstractInsnNode end = nodeAtCodeIndex(clinit, candidate.endCodeIndex);
        if (start == null || end == null) throw new IllegalStateException("region moved");

        InsnList replacement = new InsnList();
        pushInt(replacement, candidate.capacity);
        replacement.add(new TypeInsnNode(Opcodes.ANEWARRAY, "java/lang/String"));
        replacement.add(new VarInsnNode(Opcodes.ASTORE, candidate.arrayLocal));
        for (int i = 0; i < candidate.plaintexts.size(); i++) {
            replacement.add(new VarInsnNode(Opcodes.ALOAD, candidate.arrayLocal));
            pushInt(replacement, i);
            replacement.add(new LdcInsnNode(candidate.plaintexts.get(i)));
            replacement.add(new InsnNode(Opcodes.AASTORE));
        }
        clinit.instructions.insertBefore(start, replacement);

        AbstractInsnNode cursor = start;
        while (cursor != null && cursor != end) {
            AbstractInsnNode next = cursor.getNext();
            if (cursor.getOpcode() >= 0 || removableMetadata(cursor, end)) {
                clinit.instructions.remove(cursor);
            }
            cursor = next;
        }
        if (clinit.localVariables != null) clinit.localVariables.clear();
        clinit.visibleLocalVariableAnnotations = null;
        clinit.invisibleLocalVariableAnnotations = null;
        if (candidate.removeHelper) {
            MethodNode helper = method(owner, candidate.helperName, DECODE_DESC);
            if (helper == null || !owner.methods.remove(helper)) {
                throw new IllegalStateException("decoder disappeared");
            }
        }
    }

    private static void applyFlexibleMaterialization(
            ClassNode owner, Candidate candidate) throws Exception {
        MethodNode clinit = method(owner, "<clinit>", "()V");
        if (clinit == null) throw new IllegalStateException("missing <clinit>");
        AbstractInsnNode start = nodeAtCodeIndex(clinit,
                candidate.startCodeIndex);
        AbstractInsnNode boundary = nodeAtCodeIndex(clinit,
                candidate.endCodeIndex);
        if (start == null || boundary == null) {
            throw new IllegalStateException("materialization region moved");
        }
        LabelNode target = new LabelNode();
        clinit.instructions.insertBefore(boundary, target);
        InsnList replacement = new InsnList();
        pushInt(replacement, candidate.capacity);
        replacement.add(new TypeInsnNode(Opcodes.ANEWARRAY,
                "java/lang/String"));
        replacement.add(new VarInsnNode(Opcodes.ASTORE,
                candidate.arrayLocal));
        for (int index = 0; index < candidate.plaintexts.size(); index++) {
            replacement.add(new VarInsnNode(Opcodes.ALOAD,
                    candidate.arrayLocal));
            pushInt(replacement, index);
            replacement.add(new LdcInsnNode(candidate.plaintexts.get(index)));
            replacement.add(new InsnNode(Opcodes.AASTORE));
        }
        replacement.add(new JumpInsnNode(Opcodes.GOTO, target));
        clinit.instructions.insertBefore(start, replacement);

        Frame<BasicValue>[] frames = new Analyzer<BasicValue>(
                new BasicVerifier()).analyze(owner.name, clinit);
        List<AbstractInsnNode> unreachable = new ArrayList<>();
        int raw = 0;
        for (AbstractInsnNode insn = clinit.instructions.getFirst(); insn != null;
             insn = insn.getNext(), raw++) {
            if (insn.getOpcode() >= 0 && frames[raw] == null) {
                unreachable.add(insn);
            }
        }
        clinit.tryCatchBlocks.removeIf(block ->
                !reachableFlexibleExceptionRange(clinit, block, frames));
        for (AbstractInsnNode insn : unreachable) {
            clinit.instructions.remove(insn);
        }
        for (AbstractInsnNode insn = clinit.instructions.getFirst();
             insn != null; ) {
            AbstractInsnNode next = insn.getNext();
            if (insn instanceof FrameNode) clinit.instructions.remove(insn);
            insn = next;
        }
        if (clinit.localVariables != null) clinit.localVariables.clear();
        clinit.visibleLocalVariableAnnotations = null;
        clinit.invisibleLocalVariableAnnotations = null;
        new Analyzer<BasicValue>(new BasicVerifier()).analyze(owner.name,
                clinit);
        if (containsCipherFactory(clinit, ALGORITHM)) {
            throw new IllegalStateException("PKCS5 survived materialization");
        }
    }

    private static boolean reachableFlexibleExceptionRange(
            MethodNode method, TryCatchBlockNode block,
            Frame<BasicValue>[] frames) {
        int handler = method.instructions.indexOf(block.handler);
        int start = method.instructions.indexOf(block.start);
        int end = method.instructions.indexOf(block.end);
        if (handler < 0 || start < 0 || end < 0 || start >= end
                || handler >= frames.length || frames[handler] == null) {
            return false;
        }
        for (int index = start; index < end && index < frames.length; index++) {
            AbstractInsnNode insn = method.instructions.get(index);
            if (insn.getOpcode() >= 0 && frames[index] != null) return true;
        }
        return false;
    }

    private static boolean removableMetadata(AbstractInsnNode node,
                                             AbstractInsnNode end) {
        if (node instanceof FrameNode) return true;
        if (node instanceof LabelNode) {
            AbstractInsnNode next = nextCode(node);
            return next != end;
        }
        return true;
    }

    private static AbstractInsnNode nodeAtCodeIndex(MethodNode method, int index) {
        int current = 0;
        for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
             insn = insn.getNext()) {
            if (insn.getOpcode() < 0) continue;
            if (current++ == index) return insn;
        }
        return null;
    }

    private static void assertRewritten(byte[] bytes, Candidate candidate) {
        ClassNode owner = readClass(bytes);
        MethodNode clinit = method(owner, "<clinit>", "()V");
        if (clinit == null) throw new IllegalStateException("missing rewritten clinit");
        if (containsCipherFactory(clinit, ALGORITHM)) {
            throw new IllegalStateException("PKCS5 setup survived");
        }
        if (candidate.removeHelper
                && method(owner, candidate.helperName, DECODE_DESC) != null) {
            throw new IllegalStateException("dead decoder survived");
        }
        Set<String> constants = new HashSet<>();
        for (AbstractInsnNode insn = clinit.instructions.getFirst(); insn != null;
             insn = insn.getNext()) {
            if (insn instanceof LdcInsnNode
                    && ((LdcInsnNode) insn).cst instanceof String) {
                constants.add((String) ((LdcInsnNode) insn).cst);
            }
        }
        if (!constants.containsAll(candidate.plaintexts)) {
            throw new IllegalStateException("plaintext array incomplete");
        }
    }

    private static void pushInt(InsnList list, int value) {
        if (value >= -1 && value <= 5) {
            list.add(new InsnNode(Opcodes.ICONST_0 + value));
        } else if (value >= Byte.MIN_VALUE && value <= Byte.MAX_VALUE) {
            list.add(new IntInsnNode(Opcodes.BIPUSH, value));
        } else if (value >= Short.MIN_VALUE && value <= Short.MAX_VALUE) {
            list.add(new IntInsnNode(Opcodes.SIPUSH, value));
        } else {
            list.add(new LdcInsnNode(value));
        }
    }

    private static Integer intConstant(AbstractInsnNode insn) {
        if (insn == null) return null;
        int opcode = insn.getOpcode();
        if (opcode >= Opcodes.ICONST_M1 && opcode <= Opcodes.ICONST_5) {
            return opcode - Opcodes.ICONST_0;
        }
        if (insn instanceof IntInsnNode && (opcode == Opcodes.BIPUSH
                || opcode == Opcodes.SIPUSH)) return ((IntInsnNode) insn).operand;
        if (insn instanceof LdcInsnNode
                && ((LdcInsnNode) insn).cst instanceof Integer) {
            return (Integer) ((LdcInsnNode) insn).cst;
        }
        return null;
    }

    private static boolean latin1(String value) {
        for (int i = 0; i < value.length(); i++) {
            if (value.charAt(i) > 0xff) return false;
        }
        return true;
    }

    private static boolean isCall(AbstractInsnNode insn, int opcode,
                                  String owner, String name, String desc) {
        if (!(insn instanceof MethodInsnNode)) return false;
        MethodInsnNode call = (MethodInsnNode) insn;
        return call.getOpcode() == opcode && owner.equals(call.owner)
                && name.equals(call.name) && desc.equals(call.desc);
    }

    private static String call(int opcode, String owner, String name,
                               String desc) {
        return opcode + ":" + owner + "." + name + desc;
    }

    private static void put(Map<String, Integer> map, String key, int value) {
        map.put(key, value);
    }

    private static void increment(Map<String, Integer> map, String key) {
        map.put(key, map.containsKey(key) ? map.get(key) + 1 : 1);
    }

    private static MethodNode method(ClassNode owner, String name, String desc) {
        for (MethodNode method : owner.methods) {
            if (name.equals(method.name) && desc.equals(method.desc)) return method;
        }
        return null;
    }

    private static FieldNode field(ClassNode owner, String name, String desc) {
        for (FieldNode field : owner.fields) {
            if (name.equals(field.name) && desc.equals(field.desc)) return field;
        }
        return null;
    }

    private static boolean isCipherFactory(AbstractInsnNode insn,
                                           String algorithm) {
        if (!isCall(insn, Opcodes.INVOKESTATIC, "javax/crypto/Cipher",
                "getInstance", "(Ljava/lang/String;)Ljavax/crypto/Cipher;")) {
            return false;
        }
        AbstractInsnNode previous = previousCode(insn);
        return previous instanceof LdcInsnNode
                && algorithm.equals(((LdcInsnNode) previous).cst);
    }

    private static boolean containsCipherFactory(MethodNode method,
                                                 String algorithm) {
        for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
             insn = insn.getNext()) {
            if (isCipherFactory(insn, algorithm)) return true;
        }
        return false;
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

    private static Map<MethodRef, Integer> methodReferences(
            Map<String, ClassNode> classes) {
        Map<MethodRef, Integer> result = new HashMap<>();
        for (ClassNode owner : classes.values()) {
            for (MethodNode method : owner.methods) {
                for (AbstractInsnNode insn = method.instructions.getFirst();
                     insn != null; insn = insn.getNext()) {
                    if (insn instanceof MethodInsnNode) {
                        MethodInsnNode call = (MethodInsnNode) insn;
                        increment(result, new MethodRef(call.owner, call.name,
                                call.desc));
                    } else if (insn instanceof InvokeDynamicInsnNode) {
                        InvokeDynamicInsnNode indy = (InvokeDynamicInsnNode) insn;
                        addHandle(result, indy.bsm);
                        for (Object argument : indy.bsmArgs) {
                            addConstant(result, argument);
                        }
                    } else if (insn instanceof LdcInsnNode) {
                        addConstant(result, ((LdcInsnNode) insn).cst);
                    }
                }
            }
        }
        return result;
    }

    private static void addConstant(Map<MethodRef, Integer> references,
                                    Object value) {
        if (value instanceof Handle) addHandle(references, (Handle) value);
        else if (value instanceof ConstantDynamic) {
            ConstantDynamic dynamic = (ConstantDynamic) value;
            addHandle(references, dynamic.getBootstrapMethod());
            for (int i = 0; i < dynamic.getBootstrapMethodArgumentCount(); i++) {
                addConstant(references, dynamic.getBootstrapMethodArgument(i));
            }
        }
    }

    private static void addHandle(Map<MethodRef, Integer> references,
                                  Handle handle) {
        if (handle == null) return;
        int tag = handle.getTag();
        if (tag >= Opcodes.H_INVOKEVIRTUAL && tag <= Opcodes.H_INVOKEINTERFACE) {
            increment(references, new MethodRef(handle.getOwner(),
                    handle.getName(), handle.getDesc()));
        }
    }

    private static <T> void increment(Map<T, Integer> map, T key) {
        map.put(key, map.containsKey(key) ? map.get(key) + 1 : 1);
    }

    private static void validatePaths(Path input, Path output) {
        if (output != null && input.toAbsolutePath().normalize().equals(
                output.toAbsolutePath().normalize())) {
            throw new IllegalArgumentException("output must not replace input");
        }
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

    private static Map<String, byte[]> classBytes(List<EntryBytes> entries) {
        Map<String, byte[]> result = new LinkedHashMap<>();
        for (EntryBytes entry : entries) {
            if (!entry.name.endsWith(".class")) continue;
            ClassReader reader = new ClassReader(entry.bytes);
            result.put(reader.getClassName(), entry.bytes);
        }
        return result;
    }

    private static Map<String, ClassNode> readClasses(Map<String, byte[]> bytes) {
        Map<String, ClassNode> result = new LinkedHashMap<>();
        for (Map.Entry<String, byte[]> entry : bytes.entrySet()) {
            result.put(entry.getKey(), readClass(entry.getValue()));
        }
        return result;
    }

    private static ClassNode readClass(byte[] bytes) {
        ClassNode owner = new ClassNode(Opcodes.ASM9);
        new ClassReader(bytes).accept(owner, 0);
        return owner;
    }

    private static byte[] writeClass(ClassNode owner,
                                     ArchiveHierarchy hierarchy) {
        ClassWriter writer = new ArchiveClassWriter(ClassWriter.COMPUTE_FRAMES
                | ClassWriter.COMPUTE_MAXS, hierarchy);
        owner.accept(writer);
        return writer.toByteArray();
    }

    private static void verifyClass(byte[] bytes) throws Exception {
        ClassReader reader = new ClassReader(bytes);
        reader.accept(new CheckClassAdapter(new ClassWriter(0), false), 0);
        ClassNode owner = new ClassNode(Opcodes.ASM9);
        reader.accept(owner, 0);
        for (MethodNode method : owner.methods) {
            if (method.instructions != null && method.instructions.size() != 0) {
                new Analyzer<>(new BasicVerifier()).analyze(owner.name, method);
            }
        }
    }

    private static void writeVerifiedArchive(List<EntryBytes> entries,
                                             Map<String, byte[]> replacements,
                                             Path output, Summary summary,
                                             List<String> verifierRows)
            throws IOException {
        Path parent = output.toAbsolutePath().getParent();
        if (parent == null) parent = Paths.get(".").toAbsolutePath();
        Files.createDirectories(parent);
        Path temporary = Files.createTempFile(parent,
                output.getFileName().toString() + ".", ".tmp");
        summary.temporaryOutput = temporary.toAbsolutePath().toString();
        try {
            writeArchive(entries, replacements, temporary, summary);
            ArchiveVerification verification = verifyArchive(temporary,
                    verifierRows);
            summary.outputClasses = verification.classes;
            summary.outputVerificationErrors += verification.errors;
            summary.outputPkcs5ClinitClasses = verification.pkcs5ClinitClasses;
            if (verification.classes != summary.parsedClasses) {
                summary.outputVerificationErrors++;
                verifierRows.add(tsv("archive", "<archive>", "FAIL",
                        "class-count=" + verification.classes + "/"
                                + summary.parsedClasses));
            }
            int expectedRemaining = summary.pkcs5ClinitClasses
                    - summary.changedClasses;
            if (verification.pkcs5ClinitClasses != expectedRemaining) {
                summary.outputVerificationErrors++;
                verifierRows.add(tsv("archive", "<archive>", "FAIL",
                        "remaining-pkcs5-clinit="
                                + verification.pkcs5ClinitClasses + "/"
                                + expectedRemaining));
            }
            if (summary.outputVerificationErrors != 0) return;
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

    private static void writeArchive(List<EntryBytes> entries,
                                     Map<String, byte[]> replacements,
                                     Path output, Summary summary)
            throws IOException {
        Set<String> applied = new LinkedHashSet<>();
        try (ZipOutputStream out = new ZipOutputStream(Files.newOutputStream(output))) {
            for (EntryBytes entry : entries) {
                if (isSignatureEntry(entry.name) && !replacements.isEmpty()) {
                    summary.signaturesRemoved++;
                    continue;
                }
                byte[] bytes = entry.bytes;
                if (entry.name.endsWith(".class")) {
                    String name = new ClassReader(bytes).getClassName();
                    byte[] replacement = replacements.get(name);
                    if (replacement != null) {
                        bytes = replacement;
                        applied.add(name);
                    }
                }
                ZipEntry written = new ZipEntry(entry.name);
                if (entry.time >= 0) written.setTime(entry.time);
                if (entry.comment != null) written.setComment(entry.comment);
                if (entry.extra != null) written.setExtra(entry.extra);
                if (entry.method == ZipEntry.STORED) {
                    CRC32 crc = new CRC32();
                    crc.update(bytes);
                    written.setMethod(ZipEntry.STORED);
                    written.setSize(bytes.length);
                    written.setCompressedSize(bytes.length);
                    written.setCrc(crc.getValue());
                } else written.setMethod(ZipEntry.DEFLATED);
                out.putNextEntry(written);
                out.write(bytes);
                out.closeEntry();
                summary.outputEntries++;
            }
        }
        if (applied.size() != replacements.size()) {
            throw new IOException("applied-replacements=" + applied.size() + "/"
                    + replacements.size());
        }
    }

    private static ArchiveVerification verifyArchive(Path archive,
                                                      List<String> verifierRows)
            throws IOException {
        ArchiveVerification result = new ArchiveVerification();
        try (ZipInputStream in = new ZipInputStream(Files.newInputStream(archive))) {
            ZipEntry entry;
            while ((entry = in.getNextEntry()) != null) {
                byte[] bytes = readAll(in);
                if (!entry.getName().endsWith(".class")) continue;
                result.classes++;
                String name = entry.getName().substring(0,
                        entry.getName().length() - 6);
                try {
                    ClassNode owner = readClass(bytes);
                    name = owner.name;
                    verifyClass(bytes);
                    MethodNode clinit = method(owner, "<clinit>", "()V");
                    if (clinit != null && containsCipherFactory(clinit, ALGORITHM)) {
                        result.pkcs5ClinitClasses++;
                    }
                    verifierRows.add(tsv("archive", name, "PASS", ""));
                } catch (Throwable failure) {
                    result.errors++;
                    verifierRows.add(tsv("archive", name, "FAIL",
                            shortReason(failure)));
                }
            }
        }
        return result;
    }

    private static void writeReports(Path input, Path reportDirectory,
                                     Path output, Summary summary,
                                     List<Candidate> candidates,
                                     List<String> verifierRows,
                                     boolean stateDerived) throws Exception {
        List<String> rows = new ArrayList<>();
        rows.add("class\tclinit_nodes\tpkcs5_calls\tcapacity\tpacked_literals"
                + "\tplaintexts\tarray_local\tconsumer_loads\tclass_key_hex"
                + "\touter_mask_hex\tkey_hex\tkey_source\tkey_chain\tdecoder"
                + "\tdecoder_references\tremove_decoder\taction\treason");
        List<String> tableRows = new ArrayList<>();
        tableRows.add("class\tindex\tplaintext");
        List<String> helperRows = new ArrayList<>();
        helperRows.add("class\tmethod\treferences\taction");
        for (Candidate candidate : candidates) {
            rows.add(candidate.row());
            for (int i = 0; i < candidate.plaintexts.size(); i++) {
                tableRows.add(tsv(candidate.owner, i,
                        candidate.plaintexts.get(i)));
            }
            if (candidate.helperName != null) {
                helperRows.add(tsv(candidate.owner,
                        candidate.helperName + DECODE_DESC,
                        candidate.helperReferences,
                        candidate.removeHelper && ("REWRITE".equals(candidate.action)
                                || "PROVEN_DRY_RUN".equals(candidate.action))
                                ? "REMOVE" : "KEEP"));
            }
        }
        Files.write(reportDirectory.resolve("candidates.tsv"), rows,
                StandardCharsets.UTF_8);
        Files.write(reportDirectory.resolve("tables.tsv"), tableRows,
                StandardCharsets.UTF_8);
        Files.write(reportDirectory.resolve("removed-helpers.tsv"), helperRows,
                StandardCharsets.UTF_8);
        Files.write(reportDirectory.resolve("verifier.tsv"), verifierRows,
                StandardCharsets.UTF_8);
        List<String> audit = new ArrayList<>();
        audit.add("input=" + input.toAbsolutePath());
        audit.add("input_sha256=" + sha256(input));
        audit.add("parsed_classes=" + summary.parsedClasses);
        audit.add("pkcs5_clinit_classes=" + summary.pkcs5ClinitClasses);
        audit.add("proven_local_string_array_candidates="
                + summary.provenCandidates);
        audit.add("proven_plaintext_strings=" + summary.provenStrings);
        audit.add("rejected_pkcs5_clinit_classes=" + summary.rejectedCandidates);
        audit.add("changed_classes=" + summary.changedClasses);
        audit.add("rewritten_tables=" + summary.rewrittenTables);
        audit.add("rewritten_strings=" + summary.rewrittenStrings);
        audit.add("helpers_removed=" + summary.helpersRemoved);
        audit.add("class_rollbacks=" + summary.classRollbacks);
        audit.add("output_requested=" + summary.outputRequested);
        audit.add("output=" + (output == null ? "" : output.toAbsolutePath()));
        audit.add("temporary_output=" + value(summary.temporaryOutput));
        audit.add("output_entries=" + summary.outputEntries);
        audit.add("output_classes=" + summary.outputClasses);
        audit.add("output_remaining_pkcs5_clinit_classes="
                + summary.outputPkcs5ClinitClasses);
        audit.add("output_verification_errors=" + summary.outputVerificationErrors);
        audit.add("signatures_removed=" + summary.signaturesRemoved);
        audit.add("output_committed=" + summary.outputCommitted);
        audit.add("materialization_mode="
                + (summary.flexibleMaterialization ? "flexible" : "strict"));
        audit.add("authority=" + value(summary.authority));
        audit.add("authority_sha256=" + value(summary.authoritySha256));
        audit.add("scope=" + (stateDerived
                ? "closed-state-derived-local-String-array-PKCS5-tables"
                : "closed-local-String-array-PKCS5-tables"));
        audit.add("excluded=partial-exception-ranges,dynamic-inputs,array-escape,NoPadding,mixed-CFG");
        audit.add("input_classes_loaded=false");
        audit.add("input_classes_initialized=false");
        audit.add("gate=" + gate(summary));
        Files.write(reportDirectory.resolve("audit.txt"), audit,
                StandardCharsets.UTF_8);
        Files.write(reportDirectory.resolve("gate.txt"),
                Collections.singletonList(gate(summary)), StandardCharsets.UTF_8);
    }

    private static String gate(Summary summary) {
        if (summary.classRollbacks != 0 || summary.outputVerificationErrors != 0
                || summary.outputRequested && !summary.outputCommitted) return "FAIL";
        return summary.provenCandidates == 0 ? "FAIL" : "PASS";
    }

    private static void mergeKeyCandidates(
            Map<String, Set<Long>> target, Map<String, Set<Long>> source) {
        for (Map.Entry<String, Set<Long>> entry : source.entrySet()) {
            target.computeIfAbsent(entry.getKey(), ignored ->
                    new LinkedHashSet<Long>()).addAll(entry.getValue());
        }
    }

    private static String sha256(Path path) throws Exception {
        MessageDigest digest = MessageDigest.getInstance("SHA-256");
        try (InputStream input = Files.newInputStream(path)) {
            byte[] buffer = new byte[8192];
            int read;
            while ((read = input.read(buffer)) != -1) digest.update(buffer, 0, read);
        }
        StringBuilder result = new StringBuilder();
        for (byte value : digest.digest()) {
            result.append(String.format(Locale.ROOT, "%02X", value & 0xff));
        }
        return result.toString();
    }

    private static byte[] readAll(InputStream input) throws IOException {
        ByteArrayOutputStream output = new ByteArrayOutputStream();
        byte[] buffer = new byte[8192];
        int read;
        while ((read = input.read(buffer)) != -1) output.write(buffer, 0, read);
        return output.toByteArray();
    }

    private static boolean isSignatureEntry(String name) {
        String upper = name.replace('\\', '/').toUpperCase(Locale.ROOT);
        if (!upper.startsWith("META-INF/")) return false;
        String leaf = upper.substring("META-INF/".length());
        return leaf.startsWith("SIG-") || leaf.endsWith(".SF")
                || leaf.endsWith(".RSA") || leaf.endsWith(".DSA")
                || leaf.endsWith(".EC");
    }

    private static String appendReason(String current, String added) {
        return current == null || current.isEmpty() ? added : current + ";" + added;
    }

    private static String value(Object value) {
        return value == null ? "" : String.valueOf(value);
    }

    private static String shortReason(Throwable failure) {
        String text = failure.getClass().getSimpleName() + ":"
                + String.valueOf(failure.getMessage());
        text = text.replace('\t', ' ').replace('\r', ' ').replace('\n', ' ');
        return text.substring(0, Math.min(200, text.length()));
    }

    private static String tsv(Object... cells) {
        StringBuilder result = new StringBuilder();
        for (int i = 0; i < cells.length; i++) {
            if (i != 0) result.append('\t');
            if (cells[i] != null) result.append(String.valueOf(cells[i])
                    .replace('\t', ' ').replace('\r', ' ').replace('\n', ' '));
        }
        return result.toString();
    }

    static final class Summary {
        boolean flexibleMaterialization;
        String authority;
        String authoritySha256;
        int parsedClasses;
        int pkcs5ClinitClasses;
        int provenCandidates;
        int provenStrings;
        int rejectedCandidates;
        int changedClasses;
        int rewrittenTables;
        int rewrittenStrings;
        int helpersRemoved;
        int classRollbacks;
        boolean outputRequested;
        String temporaryOutput;
        int outputEntries;
        int outputClasses;
        int outputPkcs5ClinitClasses;
        int outputVerificationErrors;
        int signaturesRemoved;
        boolean outputCommitted;
    }

    static final class FieldTableProof {
        final boolean proven;
        final String owner;
        final String tableField;
        final String byteDecoderName;
        final int capacity;
        final int packedLiterals;
        final long outerKey;
        final List<String> encryptedEntries;
        final String reason;
        private final Candidate candidate;

        FieldTableProof(Candidate candidate) {
            this.candidate = candidate;
            this.proven = candidate.proven();
            this.owner = candidate.owner;
            this.tableField = candidate.tableField;
            this.byteDecoderName = candidate.helperName;
            this.capacity = candidate.capacity;
            this.packedLiterals = candidate.packedLiterals;
            this.outerKey = candidate.key;
            this.encryptedEntries = Collections.unmodifiableList(
                    new ArrayList<>(candidate.plaintexts));
            this.reason = candidate.reason;
        }
    }

    static final class StateKeyProof {
        final String owner;
        final long classKey;
        final String source;
        final String chain;

        StateKeyProof(String owner, long classKey, String source,
                      String chain) {
            this.owner = owner;
            this.classKey = classKey;
            this.source = source;
            this.chain = chain;
        }
    }

    private static final class Candidate {
        final String owner;
        final int clinitNodes;
        final int pkcsCalls;
        int capacity;
        int packedLiterals;
        int arrayLocal;
        int outputLocal;
        int consumerLoads;
        int startCodeIndex;
        int endCodeIndex;
        AbstractInsnNode startNode;
        AbstractInsnNode endNode;
        boolean stateDerived;
        long classKey;
        long outerMask;
        long key;
        String keySource = "";
        String keyChain = "";
        String helperName;
        String tableField;
        int helperReferences;
        boolean removeHelper;
        boolean flexibleMaterialization;
        final List<String> plaintexts = new ArrayList<>();
        String action = "REJECT";
        String reason = "";

        Candidate(String owner, int clinitNodes, int pkcsCalls) {
            this.owner = owner;
            this.clinitNodes = clinitNodes;
            this.pkcsCalls = pkcsCalls;
        }

        Candidate reject(String reason) {
            this.reason = reason;
            this.action = "REJECT";
            return this;
        }

        boolean proven() {
            return "PROVEN".equals(action);
        }

        String row() {
            return tsv(owner, clinitNodes, pkcsCalls, capacity, packedLiterals,
                    plaintexts.size(), arrayLocal, consumerLoads,
                    stateDerived ? String.format(Locale.ROOT, "%016X", classKey) : "",
                    stateDerived ? String.format(Locale.ROOT, "%016X", outerMask) : "",
                    capacity == 0 ? "" : String.format(Locale.ROOT, "%016X", key),
                    value(keySource), value(keyChain),
                    value(helperName), helperReferences, removeHelper,
                    action, reason);
        }
    }

    private static final class ArrayKeyOption {
        final long classKey;
        final long mask;
        final long key;
        final boolean stateDerived;
        final String source;

        ArrayKeyOption(long classKey, long mask, long key,
                       boolean stateDerived, String source) {
            this.classKey = classKey;
            this.mask = mask;
            this.key = key;
            this.stateDerived = stateDerived;
            this.source = source;
        }
    }

    private static final class ArrayTableOption {
        final ArrayKeyOption key;
        final int packedLiterals;
        final List<Integer> literalInstructions;
        final List<String> values;

        ArrayTableOption(ArrayKeyOption key,
                         int packedLiterals,
                         List<Integer> literalInstructions,
                         List<String> values) {
            this.key = key;
            this.packedLiterals = packedLiterals;
            this.literalInstructions = literalInstructions;
            this.values = values;
        }
    }

    private static final class FlexibleBoundary {
        final int index;
        final Set<Integer> region;

        FlexibleBoundary(int index, Set<Integer> region) {
            this.index = index;
            this.region = region;
        }
    }

    private static final class PackedLoop {
        final int literalIndex;
        final int endIndex;
        final String ciphertext;
        final int initialChunkLength;
        final String helperName;
        final List<String> plaintexts = new ArrayList<>();

        PackedLoop(int literalIndex, int endIndex, String ciphertext,
                   int initialChunkLength, String helperName) {
            this.literalIndex = literalIndex;
            this.endIndex = endIndex;
            this.ciphertext = ciphertext;
            this.initialChunkLength = initialChunkLength;
            this.helperName = helperName;
        }
    }

    private static final class ArrayAllocation {
        final int capacityIndex;
        final int arrayIndex;
        final int storeIndex;
        final int capacity;
        final int local;

        ArrayAllocation(int capacityIndex, int arrayIndex, int storeIndex,
                        int capacity, int local) {
            this.capacityIndex = capacityIndex;
            this.arrayIndex = arrayIndex;
            this.storeIndex = storeIndex;
            this.capacity = capacity;
            this.local = local;
        }
    }

    private static final class Code {
        final List<AbstractInsnNode> nodes = new ArrayList<>();
        final IdentityHashMap<AbstractInsnNode, Integer> indices =
                new IdentityHashMap<>();
        final IdentityHashMap<LabelNode, Integer> targets =
                new IdentityHashMap<>();

        Code(MethodNode method) {
            for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
                 insn = insn.getNext()) {
                if (insn.getOpcode() >= 0) {
                    indices.put(insn, nodes.size());
                    nodes.add(insn);
                }
            }
            for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
                 insn = insn.getNext()) {
                if (insn instanceof LabelNode) {
                    AbstractInsnNode target = nextCode(insn);
                    targets.put((LabelNode) insn, target == null ? nodes.size()
                            : index(target));
                }
            }
        }

        int index(AbstractInsnNode node) {
            Integer value = indices.get(node);
            return value == null ? -1 : value;
        }

        int target(LabelNode label) {
            Integer value = targets.get(label);
            return value == null ? -1 : value;
        }

        List<List<Integer>> successors() {
            List<List<Integer>> result = new ArrayList<>();
            for (int i = 0; i < nodes.size(); i++) {
                AbstractInsnNode insn = nodes.get(i);
                List<Integer> next = new ArrayList<>();
                int opcode = insn.getOpcode();
                if (insn instanceof JumpInsnNode) {
                    addTarget(next, target(((JumpInsnNode) insn).label));
                    if (opcode != Opcodes.GOTO && opcode != Opcodes.JSR
                            && i + 1 < nodes.size()) addTarget(next, i + 1);
                } else if (insn instanceof TableSwitchInsnNode) {
                    TableSwitchInsnNode table = (TableSwitchInsnNode) insn;
                    addTarget(next, target(table.dflt));
                    for (LabelNode label : table.labels) addTarget(next, target(label));
                } else if (insn instanceof LookupSwitchInsnNode) {
                    LookupSwitchInsnNode lookup = (LookupSwitchInsnNode) insn;
                    addTarget(next, target(lookup.dflt));
                    for (LabelNode label : lookup.labels) addTarget(next, target(label));
                } else if (opcode != Opcodes.RETURN && opcode != Opcodes.IRETURN
                        && opcode != Opcodes.LRETURN && opcode != Opcodes.FRETURN
                        && opcode != Opcodes.DRETURN && opcode != Opcodes.ARETURN
                        && opcode != Opcodes.ATHROW && opcode != Opcodes.RET
                        && i + 1 < nodes.size()) addTarget(next, i + 1);
                result.add(next);
            }
            return result;
        }

        private static void addTarget(List<Integer> values, int target) {
            if (target >= 0 && !values.contains(target)) values.add(target);
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
            MethodRef ref = (MethodRef) other;
            return owner.equals(ref.owner) && name.equals(ref.name)
                    && desc.equals(ref.desc);
        }

        @Override public int hashCode() {
            int result = owner.hashCode();
            result = 31 * result + name.hashCode();
            return 31 * result + desc.hashCode();
        }
    }

    private static final class ArchiveVerification {
        int classes;
        int errors;
        int pkcs5ClinitClasses;
    }

    private static final class EntryBytes {
        final String name;
        final byte[] bytes;
        final long time;
        final String comment;
        final byte[] extra;
        final int method;

        EntryBytes(ZipEntry entry, byte[] bytes) {
            this.name = entry.getName();
            this.bytes = bytes;
            this.time = entry.getTime();
            this.comment = entry.getComment();
            this.extra = entry.getExtra();
            this.method = entry.getMethod();
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
            for (String current = left; current != null;
                 current = superName(current)) supers.add(current);
            for (String current = right; current != null;
                 current = superName(current)) {
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

        HierarchyType(String superName, List<String> interfaces,
                      boolean isInterface) {
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

        @Override protected String getCommonSuperClass(String left,
                                                       String right) {
            return hierarchy.commonSuperClass(left, right);
        }
    }
}
