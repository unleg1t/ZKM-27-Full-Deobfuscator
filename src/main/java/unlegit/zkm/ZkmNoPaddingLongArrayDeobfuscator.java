package unlegit.zkm;

import org.objectweb.asm.ClassReader;
import org.objectweb.asm.ClassWriter;
import org.objectweb.asm.Opcodes;
import org.objectweb.asm.Type;
import org.objectweb.asm.tree.AbstractInsnNode;
import org.objectweb.asm.tree.ClassNode;
import org.objectweb.asm.tree.FieldInsnNode;
import org.objectweb.asm.tree.FrameNode;
import org.objectweb.asm.tree.IincInsnNode;
import org.objectweb.asm.tree.InsnList;
import org.objectweb.asm.tree.InsnNode;
import org.objectweb.asm.tree.IntInsnNode;
import org.objectweb.asm.tree.JumpInsnNode;
import org.objectweb.asm.tree.LabelNode;
import org.objectweb.asm.tree.LdcInsnNode;
import org.objectweb.asm.tree.LineNumberNode;
import org.objectweb.asm.tree.LookupSwitchInsnNode;
import org.objectweb.asm.tree.MethodInsnNode;
import org.objectweb.asm.tree.MethodNode;
import org.objectweb.asm.tree.TableSwitchInsnNode;
import org.objectweb.asm.tree.VarInsnNode;
import org.objectweb.asm.tree.analysis.Analyzer;
import org.objectweb.asm.tree.analysis.BasicVerifier;
import org.objectweb.asm.tree.analysis.Frame;
import org.objectweb.asm.tree.analysis.BasicValue;
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
 * Replaces the closed ZKM DES/CBC/NoPadding local {@code long[]} table
 * population graph with explicit constants.
 *
 * <p>The original generator has both a linear loop form and a split-tail form
 * whose shared {@code Cipher.doFinal} block is physically after business
 * initialization.  This pass does not assume a contiguous source slice.  It
 * emits the complete table at the proven crypto entry, branches to the loop's
 * normal business continuation, and removes only original instructions that
 * become unreachable because of that branch.  Every pre-existing owner field
 * write and every long-key state call must remain reachable.  The long-key
 * bootstrap and its state mutation therefore stay in their original order.</p>
 *
 * <p>Classes are parsed as byte arrays.  No input class is defined, loaded,
 * initialized, or reflectively queried.</p>
 */
public final class ZkmNoPaddingLongArrayDeobfuscator {
    private static final String ALGORITHM = "DES/CBC/NoPadding";
    private static final String KEY_ALGORITHM = "DES";
    private static final String LATIN1 = "ISO-8859-1";
    private static final String STATE = ObfRuntimeNames.STATE;
    private static final String STATE_IFACE = ObfRuntimeNames.STATE_INTERFACE;

    private ZkmNoPaddingLongArrayDeobfuscator() {
    }

    public static void main(String[] args) throws Exception {
        if (args.length < 2 || args.length > 3) {
            System.err.println("usage: ZkmNoPaddingLongArrayDeobfuscator <input.jar> <report-dir> [output.jar]");
            System.exit(2);
        }
        Summary summary = rewrite(Paths.get(args[0]), Paths.get(args[1]),
                args.length == 3 ? Paths.get(args[2]) : null);
        System.out.println("classes=" + summary.parsedClasses + " candidates="
                + summary.candidates + " proven=" + summary.proven + " rewritten="
                + summary.changedClasses + " entries=" + summary.tableEntries
                + " rollbacks=" + summary.rollbacks + " output_committed="
                + summary.outputCommitted);
    }

    static Summary rewrite(Path input, Path reportDirectory, Path output) throws Exception {
        return rewrite(input, reportDirectory, output, null);
    }

    static Summary rewrite(Path input, Path reportDirectory, Path output,
                           Path authority) throws Exception {
        if (output != null && input.toAbsolutePath().normalize()
                .equals(output.toAbsolutePath().normalize())) {
            throw new IllegalArgumentException("output must not replace input");
        }
        Files.createDirectories(reportDirectory);
        List<EntryBytes> entries = readEntries(input);
        Map<String, byte[]> originals = classBytes(entries);
        Map<String, ClassNode> classes = classNodes(originals);

        Map<String, Long> validated = safeValidatedClassKeys(classes);
        Map<String, Long> isolated = safeClassKeys(classes, false);
        Map<String, Long> sequential = safeClassKeys(classes, true);
        Map<String, Long> hierarchy = safeHierarchyKeys(classes);
        Map<String, Long> authorityKeys = authority == null
                ? Collections.<String, Long>emptyMap()
                : authorityKeys(authority);

        Summary summary = new Summary();
        summary.parsedClasses = classes.size();
        List<Candidate> candidates = new ArrayList<>();
        Map<String, byte[]> replacements = new LinkedHashMap<>();
        List<String> verifier = new ArrayList<>();
        verifier.add("scope\tclass\tstatus\tdetail");

        List<String> names = new ArrayList<>(classes.keySet());
        Collections.sort(names);
        for (String name : names) {
            ClassNode owner = classes.get(name);
            Candidate candidate = inspect(owner, validated, isolated, sequential,
                    hierarchy, authorityKeys);
            if (candidate == null) continue;
            candidates.add(candidate);
            summary.candidates++;
            if (!candidate.proven) {
                summary.rejected++;
                continue;
            }
            summary.proven++;
            summary.tableEntries += candidate.values.size();
            if (output == null) {
                candidate.action = "PROVEN_DRY_RUN";
                continue;
            }
            try {
                ClassNode rewritten = readClass(originals.get(name));
                apply(rewritten, candidate);
                byte[] bytes = writeClass(rewritten, classes);
                verifyClass(bytes);
                assertRewritten(bytes, candidate);
                replacements.put(name, bytes);
                candidate.action = "REWRITE";
                summary.changedClasses++;
                verifier.add(tsv("class", name, "PASS", "entries=" + candidate.values.size()));
            } catch (Throwable failure) {
                candidate.action = "ROLLBACK";
                candidate.reason += ";class-rollback=" + shortReason(failure);
                summary.rollbacks++;
                verifier.add(tsv("class", name, "FAIL", shortReason(failure)));
            }
        }

        if (output != null) {
            writeVerifiedArchive(entries, replacements, output, classes, summary, verifier);
        }
        writeReports(input, output, reportDirectory, summary, candidates, verifier);
        return summary;
    }

    private static Map<String, Long> safeValidatedClassKeys(
            Map<String, ClassNode> classes) {
        try {
            return ZkmStringDecryptor.solveValidatedClassKeys(classes);
        } catch (Throwable ignored) {
            return Collections.emptyMap();
        }
    }

    private static Candidate inspect(ClassNode owner, Map<String, Long> validated,
                                     Map<String, Long> isolated,
                                     Map<String, Long> sequential,
                                     Map<String, Long> hierarchy,
                                     Map<String, Long> authorityKeys) {
        MethodNode clinit = method(owner, "<clinit>", "()V");
        if (clinit == null) return null;
        Code code = new Code(clinit);
        List<Integer> factories = new ArrayList<>();
        for (int index = 0; index < code.nodes.size(); index++) {
            if (isCipherFactory(code.nodes.get(index), ALGORITHM)) factories.add(index);
        }
        if (factories.isEmpty()) return null;

        List<Candidate> tableCandidates = new ArrayList<>();
        List<String> failures = new ArrayList<>();
        for (int factory : factories) {
            try {
                Candidate candidate = locate(owner, clinit, code, factory,
                        validated, isolated, sequential, hierarchy, authorityKeys);
                if (candidate != null) tableCandidates.add(candidate);
            } catch (Throwable failure) {
                failures.add(shortReason(failure));
            }
        }
        if (tableCandidates.isEmpty()) {
            // Other NoPadding forms are intentionally left for their own stage.
            return null;
        }
        if (tableCandidates.size() != 1) {
            Candidate rejected = new Candidate(owner.name);
            rejected.noPaddingFactories = factories.size();
            return rejected.reject("local-long-table-candidates=" + tableCandidates.size());
        }
        Candidate result = tableCandidates.get(0);
        result.noPaddingFactories = factories.size();
        return result;
    }

    private static Candidate locate(ClassNode owner, MethodNode clinit, Code code,
                                    int factoryIndex, Map<String, Long> validated,
                                    Map<String, Long> isolated,
                                    Map<String, Long> sequential,
                                    Map<String, Long> hierarchy,
                                    Map<String, Long> authorityKeys) throws Exception {
        int start = factoryIndex - 1;
        if (start < 0 || !(code.nodes.get(start) instanceof LdcInsnNode)
                || !ALGORITHM.equals(((LdcInsnNode) code.nodes.get(start)).cst)) return null;
        int nextCipher = code.nodes.size();
        for (int index = factoryIndex + 1; index < code.nodes.size(); index++) {
            if (isAnyCipherFactory(code.nodes.get(index))) {
                nextCipher = index - 1;
                break;
            }
        }

        List<Allocation> allocations = new ArrayList<>();
        for (int index = factoryIndex + 1; index + 1 < nextCipher; index++) {
            AbstractInsnNode insn = code.nodes.get(index);
            if (!(insn instanceof IntInsnNode) || insn.getOpcode() != Opcodes.NEWARRAY
                    || ((IntInsnNode) insn).operand != Opcodes.T_LONG) continue;
            Integer size = intConstant(code.nodes.get(index - 1));
            AbstractInsnNode store = code.nodes.get(index + 1);
            if (size != null && size > 0 && store instanceof VarInsnNode
                    && store.getOpcode() == Opcodes.ASTORE) {
                allocations.add(new Allocation(index - 1, index, index + 1,
                        size, ((VarInsnNode) store).var));
            }
        }
        if (allocations.isEmpty()) return null;
        if (allocations.size() != 1) {
            throw new IllegalArgumentException("long-array-allocations=" + allocations.size());
        }
        Allocation allocation = allocations.get(0);
        Candidate candidate = new Candidate(owner.name);
        candidate.startCodeIndex = start;
        candidate.capacity = allocation.capacity;
        candidate.arrayLocal = allocation.local;
        candidate.originalNoPaddingCount = countCipherFactories(clinit, ALGORITHM);

        List<PackedLoop> loops = new ArrayList<>();
        int search = allocation.storeIndex + 1;
        while (true) {
            PackedLoop loop = null;
            int limit = Math.min(code.nodes.size(), search + 10);
            for (int index = search; index < limit; index++) {
                loop = parsePackedLoop(code, index);
                if (loop != null) break;
            }
            if (loop == null) break;
            loops.add(loop);
            search = loop.exitIndex + 1;
            PackedLoop next = null;
            int nextLimit = Math.min(code.nodes.size(), search + 4);
            for (int index = search; index < nextLimit; index++) {
                next = parsePackedLoop(code, index);
                if (next != null) break;
                if (code.nodes.get(index) instanceof JumpInsnNode) break;
            }
            if (next == null) break;
        }
        if (loops.isEmpty()) throw new IllegalArgumentException("packed-loops=0");
        int entries = 0;
        for (PackedLoop loop : loops) entries += loop.packed.length() / 8;
        if (entries != allocation.capacity) {
            throw new IllegalArgumentException("packed-capacity=" + entries + "/"
                    + allocation.capacity);
        }

        PackedLoop last = loops.get(loops.size() - 1);
        int continuationIndex = followGotoChain(code, last.exitIndex + 1);
        if (continuationIndex <= last.exitIndex || continuationIndex >= code.nodes.size()) {
            throw new IllegalArgumentException("business-continuation=" + continuationIndex);
        }
        if (parsePackedLoop(code, continuationIndex) != null) {
            throw new IllegalArgumentException("packed-loop-chain-incomplete");
        }
        candidate.continuationCodeIndex = continuationIndex;
        candidate.packedLiterals = loops.size();

        validateSetupShape(code, start, allocation.storeIndex, loops.size());
        validateBoundary(owner, clinit, code, start, continuationIndex);
        KeySelection keys = selectKey(owner, code, start, allocation.allocationIndex,
                validated, isolated, sequential, hierarchy, authorityKeys);
        candidate.key = keys.outerKey;
        candidate.classKey = keys.classKey;
        candidate.outerMask = keys.outerMask;
        candidate.keySource = keys.source;
        candidate.stateDerived = keys.stateDerived;
        candidate.isolatedClassKey = keys.isolated;
        candidate.sequentialClassKey = keys.sequential;
        candidate.hierarchyClassKey = keys.hierarchy;
        if (!keys.trusted) {
            candidate.action = "REJECT";
            candidate.reason = "unproven-class-key-authority;candidate="
                    + candidate.keySource;
            return candidate;
        }

        for (PackedLoop loop : loops) {
            for (int offset = 0; offset < loop.packed.length(); offset += 8) {
                candidate.values.add(decryptBlock(loop.packed, offset, candidate.key));
            }
        }
        if (candidate.values.size() != candidate.capacity) {
            throw new IllegalArgumentException("plaintext-capacity="
                    + candidate.values.size() + "/" + candidate.capacity);
        }
        candidate.proven = true;
        candidate.action = "PROVEN";
        candidate.reason = "closed-local-long-table;cfg-bypass;business-writes-preserved;key="
                + candidate.keySource;
        return candidate;
    }

    private static PackedLoop parsePackedLoop(Code code, int literalIndex) {
        if (literalIndex < 0 || literalIndex >= code.nodes.size()) return null;
        AbstractInsnNode insn = code.nodes.get(literalIndex);
        if (!(insn instanceof LdcInsnNode)
                || !(((LdcInsnNode) insn).cst instanceof String)) return null;
        String packed = (String) ((LdcInsnNode) insn).cst;
        if (packed.isEmpty() || (packed.length() & 7) != 0 || !latin1(packed)
                || ALGORITHM.equals(packed) || KEY_ALGORITHM.equals(packed)
                || LATIN1.equals(packed)) return null;
        int cursor = literalIndex + 1;
        if (cursor < code.nodes.size() && code.nodes.get(cursor).getOpcode() == Opcodes.DUP) cursor++;
        if (cursor >= code.nodes.size() || !(code.nodes.get(cursor) instanceof VarInsnNode)
                || code.nodes.get(cursor).getOpcode() != Opcodes.ASTORE) return null;
        cursor++;
        if (cursor >= code.nodes.size() || !isCall(code.nodes.get(cursor),
                Opcodes.INVOKEVIRTUAL, "java/lang/String", "length", "()I")) return null;
        cursor++;
        if (cursor >= code.nodes.size() || !(code.nodes.get(cursor) instanceof VarInsnNode)
                || code.nodes.get(cursor).getOpcode() != Opcodes.ISTORE) return null;
        cursor++;
        if (cursor + 1 >= code.nodes.size() || intConstant(code.nodes.get(cursor)) == null
                || intConstant(code.nodes.get(cursor)) != 0
                || !(code.nodes.get(cursor + 1) instanceof VarInsnNode)
                || code.nodes.get(cursor + 1).getOpcode() != Opcodes.ISTORE) return null;

        int substring = 0;
        int getBytes = 0;
        int stores = 0;
        int limit = Math.min(code.nodes.size(), literalIndex + 520);
        for (int index = cursor + 2; index < limit; index++) {
            AbstractInsnNode current = code.nodes.get(index);
            if (isCall(current, Opcodes.INVOKEVIRTUAL, "java/lang/String",
                    "substring", "(II)Ljava/lang/String;")) substring++;
            if (isCall(current, Opcodes.INVOKEVIRTUAL, "java/lang/String",
                    "getBytes", "(Ljava/lang/String;)[B")) getBytes++;
            if (current.getOpcode() == Opcodes.LASTORE) stores++;
            if (!(current instanceof JumpInsnNode)) continue;
            int opcode = current.getOpcode();
            if (opcode != Opcodes.IF_ICMPLT && opcode != Opcodes.IF_ICMPGE
                    && opcode != Opcodes.IFLT && opcode != Opcodes.IFGE) continue;
            int target = code.target(((JumpInsnNode) current).label);
            if (target < literalIndex || target >= index) continue;
            if (substring == 1 && getBytes == 1 && stores == 1) {
                return new PackedLoop(literalIndex, index, packed);
            }
        }
        return null;
    }

    private static void validateSetupShape(Code code, int start, int allocationStore,
                                           int loops) {
        Map<String, Integer> expected = new LinkedHashMap<>();
        expected.put(call(Opcodes.INVOKESTATIC, "javax/crypto/Cipher", "getInstance",
                "(Ljava/lang/String;)Ljavax/crypto/Cipher;"), 1);
        expected.put(call(Opcodes.INVOKESTATIC, "javax/crypto/SecretKeyFactory", "getInstance",
                "(Ljava/lang/String;)Ljavax/crypto/SecretKeyFactory;"), 1);
        expected.put(call(Opcodes.INVOKESPECIAL, "javax/crypto/spec/DESKeySpec", "<init>",
                "([B)V"), 1);
        expected.put(call(Opcodes.INVOKEVIRTUAL, "javax/crypto/SecretKeyFactory",
                "generateSecret", "(Ljava/security/spec/KeySpec;)Ljavax/crypto/SecretKey;"), 1);
        expected.put(call(Opcodes.INVOKESPECIAL, "javax/crypto/spec/IvParameterSpec", "<init>",
                "([B)V"), 1);
        expected.put(call(Opcodes.INVOKEVIRTUAL, "javax/crypto/Cipher", "init",
                "(ILjava/security/Key;Ljava/security/spec/AlgorithmParameterSpec;)V"), 1);
        Map<String, Integer> actual = new LinkedHashMap<>();
        int longArrays = 0;
        int byteArrays = 0;
        for (int index = start; index <= allocationStore; index++) {
            AbstractInsnNode insn = code.nodes.get(index);
            if (insn instanceof MethodInsnNode) {
                MethodInsnNode method = (MethodInsnNode) insn;
                String id = call(method.getOpcode(), method.owner, method.name, method.desc);
                actual.put(id, actual.getOrDefault(id, 0) + 1);
            }
            if (insn instanceof IntInsnNode && insn.getOpcode() == Opcodes.NEWARRAY) {
                int type = ((IntInsnNode) insn).operand;
                if (type == Opcodes.T_LONG) longArrays++;
                else if (type == Opcodes.T_BYTE) byteArrays++;
                else throw new IllegalArgumentException("setup-primitive-array=" + type);
            }
        }
        if (!actual.equals(expected)) {
            throw new IllegalArgumentException("setup-call-set=" + actual.size()
                    + "/" + expected.size());
        }
        if (longArrays != 1 || byteArrays != 2) {
            throw new IllegalArgumentException("setup-arrays=long:" + longArrays
                    + ",byte:" + byteArrays + ",loops:" + loops);
        }
    }

    private static void validateBoundary(ClassNode owner, MethodNode method, Code code,
                                         int start, int continuation) throws Exception {
        if (method.tryCatchBlocks != null) {
            for (org.objectweb.asm.tree.TryCatchBlockNode block : method.tryCatchBlocks) {
                int protectedStart = code.target(block.start);
                int protectedEnd = code.target(block.end);
                int handler = code.target(block.handler);
                boolean protectedOverlap = protectedStart < continuation
                        && protectedEnd > start;
                boolean handlerInside = handler >= start && handler < continuation;
                if (protectedStart < 0 || protectedEnd < 0 || handler < 0
                        || protectedOverlap || handlerInside) {
                    throw new IllegalArgumentException("clinit-exception-overlap="
                            + protectedStart + ".." + protectedEnd + "->" + handler);
                }
            }
        }
        Analyzer<BasicValue> analyzer = new Analyzer<>(new BasicVerifier());
        Frame<BasicValue>[] frames = analyzer.analyze(owner.name, method);
        Frame<BasicValue> entry = frames[method.instructions.indexOf(code.nodes.get(start))];
        Frame<BasicValue> exit = frames[method.instructions.indexOf(code.nodes.get(continuation))];
        if (entry == null || exit == null || entry.getStackSize() != 0
                || exit.getStackSize() != 0) {
            throw new IllegalArgumentException("boundary-stack="
                    + (entry == null ? "unreachable" : entry.getStackSize()) + "/"
                    + (exit == null ? "unreachable" : exit.getStackSize()));
        }
    }

    private static KeySelection selectKey(ClassNode owner, Code code, int start,
                                          int allocation, Map<String, Long> validated,
                                          Map<String, Long> isolated,
                                          Map<String, Long> sequential,
                                          Map<String, Long> hierarchy,
                                          Map<String, Long> authorityKeys) {
        Set<Long> literals = new LinkedHashSet<>();
        Set<Integer> longLoads = new LinkedHashSet<>();
        for (int index = start; index <= allocation; index++) {
            AbstractInsnNode insn = code.nodes.get(index);
            if (insn instanceof LdcInsnNode && ((LdcInsnNode) insn).cst instanceof Long) {
                long value = (Long) ((LdcInsnNode) insn).cst;
                if (value != 255L) literals.add(value);
            }
            if (insn instanceof VarInsnNode && insn.getOpcode() == Opcodes.LLOAD) {
                longLoads.add(((VarInsnNode) insn).var);
            }
        }
        KeySelection result = new KeySelection();
        result.isolated = isolated.get(owner.name);
        result.sequential = sequential.get(owner.name);
        result.hierarchy = hierarchy.get(owner.name);
        if (longLoads.isEmpty()) {
            if (literals.size() != 1) {
                throw new IllegalArgumentException("literal-key-count=" + literals.size());
            }
            result.outerKey = literals.iterator().next();
            result.source = "literal-key";
            result.trusted = true;
            return result;
        }
        if (longLoads.size() != 1 || !literals.isEmpty()) {
            throw new IllegalArgumentException("key-loads=" + longLoads.size()
                    + ",literals=" + literals.size());
        }
        int local = longLoads.iterator().next();
        int definition = -1;
        int definitions = 0;
        for (int index = 0; index < start; index++) {
            AbstractInsnNode insn = code.nodes.get(index);
            if (insn instanceof VarInsnNode && insn.getOpcode() == Opcodes.LSTORE
                    && ((VarInsnNode) insn).var == local) {
                definition = index;
                definitions++;
            }
        }
        if (definitions != 1 || definition < 1) {
            throw new IllegalArgumentException("key-local-definitions=" + definitions);
        }
        AbstractInsnNode producer = code.nodes.get(definition - 1);
        if (producer instanceof LdcInsnNode && ((LdcInsnNode) producer).cst instanceof Long) {
            result.outerKey = (Long) ((LdcInsnNode) producer).cst;
            result.source = "literal-key-local";
            result.trusted = true;
            return result;
        }
        if (producer.getOpcode() != Opcodes.LXOR || definition < 2
                || !(code.nodes.get(definition - 2) instanceof LdcInsnNode)
                || !(((LdcInsnNode) code.nodes.get(definition - 2)).cst instanceof Long)) {
            throw new IllegalArgumentException("key-local-producer=" + producer.getOpcode());
        }
        long mask = (Long) ((LdcInsnNode) code.nodes.get(definition - 2)).cst;
        boolean bootstrap = false;
        boolean transform = false;
        for (int index = 0; index < definition; index++) {
            AbstractInsnNode insn = code.nodes.get(index);
            if (!(insn instanceof MethodInsnNode)) continue;
            MethodInsnNode call = (MethodInsnNode) insn;
            if (STATE.equals(call.owner) && "a".equals(call.name)
                    && ObfRuntimeNames.BOOTSTRAP_DESC
                    .equals(call.desc)) bootstrap = true;
            if (STATE_IFACE.equals(call.owner) && "a".equals(call.name)
                    && "(J)J".equals(call.desc)) transform = true;
        }
        if (!bootstrap || !transform) {
            throw new IllegalArgumentException("state-key-chain=" + bootstrap + "/" + transform);
        }
        Long classKey = authorityKeys.get(owner.name);
        String source = "pre-removal-authority-jvm-chain";
        boolean trusted = classKey != null;
        if (classKey == null) {
            classKey = validated.get(owner.name);
            source = "validated-string-key";
            trusted = isTrustedStateKey(classKey, isolated.get(owner.name));
        }
        if (classKey == null) {
            // Isolated execution is useful as a diagnostic candidate, but the
            // state graph is order-sensitive.  It is not rewrite authority.
            classKey = isolated.get(owner.name);
            source = "isolated-static-long-key-model-candidate";
        }
        if (classKey == null) throw new IllegalArgumentException("class-key-unresolved");
        result.classKey = classKey;
        result.outerMask = mask;
        result.outerKey = classKey ^ mask;
        result.source = source;
        result.trusted = trusted;
        result.stateDerived = true;
        return result;
    }

    private static Map<String, Long> authorityKeys(Path authority) throws Exception {
        Map<String, ZkmNoPaddingLiteralFragmentDeobfuscator.KeyProof> proofs =
                ZkmNoPaddingStateFragmentDeobfuscator.keyProofs(authority);
        Map<String, Long> result = new LinkedHashMap<>();
        for (Map.Entry<String, ZkmNoPaddingLiteralFragmentDeobfuscator.KeyProof> entry
                : proofs.entrySet()) {
            result.put(entry.getKey(), entry.getValue().classKey);
        }
        return result;
    }

    static boolean isTrustedStateKey(Long validatedClassKey,
                                     Long isolatedCandidate) {
        return validatedClassKey != null;
    }

    private static long decryptBlock(String packed, int offset, long keyValue) throws Exception {
        byte[] encrypted = new byte[8];
        for (int index = 0; index < 8; index++) {
            char value = packed.charAt(offset + index);
            if (value > 0xff) throw new IllegalArgumentException("non-Latin1-ciphertext");
            encrypted[index] = (byte) value;
        }
        ZkmDesConstantEvaluator.KeyMaterial key =
                ZkmDesConstantEvaluator.KeyMaterial.proven(keyValue,
                        "LONG_TABLE_KEY", "NoPadding local long[] table");
        return ZkmDesConstantEvaluator.decryptLong(key,
                ZkmDesConstantEvaluator.bytesToLong(encrypted));
    }

    private static void apply(ClassNode owner, Candidate expected) throws Exception {
        MethodNode method = method(owner, "<clinit>", "()V");
        if (method == null) throw new IllegalStateException("missing <clinit>");
        Code code = new Code(method);
        AbstractInsnNode start = code.nodes.get(expected.startCodeIndex);
        AbstractInsnNode continuation = code.nodes.get(expected.continuationCodeIndex);
        Analyzer<BasicValue> analyzer = new Analyzer<>(new BasicVerifier());
        Frame<BasicValue>[] before = analyzer.analyze(owner.name, method);
        Set<AbstractInsnNode> baselineReachable = Collections.newSetFromMap(
                new IdentityHashMap<AbstractInsnNode, Boolean>());
        List<FieldInsnNode> fieldWrites = new ArrayList<>();
        List<MethodInsnNode> stateCalls = new ArrayList<>();
        for (int index = 0; index < method.instructions.size(); index++) {
            AbstractInsnNode insn = method.instructions.get(index);
            if (index < before.length && before[index] != null) baselineReachable.add(insn);
            if (insn instanceof FieldInsnNode && insn.getOpcode() == Opcodes.PUTSTATIC
                    && owner.name.equals(((FieldInsnNode) insn).owner)) {
                fieldWrites.add((FieldInsnNode) insn);
            }
            if (insn instanceof MethodInsnNode) {
                MethodInsnNode call = (MethodInsnNode) insn;
                if (STATE.equals(call.owner) || STATE_IFACE.equals(call.owner)) stateCalls.add(call);
            }
        }

        LabelNode continuationLabel = labelBefore(method, continuation);
        InsnList replacement = new InsnList();
        pushInt(replacement, expected.capacity);
        replacement.add(new IntInsnNode(Opcodes.NEWARRAY, Opcodes.T_LONG));
        replacement.add(new VarInsnNode(Opcodes.ASTORE, expected.arrayLocal));
        for (int index = 0; index < expected.values.size(); index++) {
            replacement.add(new VarInsnNode(Opcodes.ALOAD, expected.arrayLocal));
            pushInt(replacement, index);
            replacement.add(new LdcInsnNode(expected.values.get(index)));
            replacement.add(new InsnNode(Opcodes.LASTORE));
        }
        replacement.add(new JumpInsnNode(Opcodes.GOTO, continuationLabel));
        method.instructions.insertBefore(start, replacement);

        Frame<BasicValue>[] after = analyzer.analyze(owner.name, method);
        Map<AbstractInsnNode, Frame<BasicValue>> reachability = new IdentityHashMap<>();
        for (int index = 0; index < method.instructions.size() && index < after.length; index++) {
            reachability.put(method.instructions.get(index), after[index]);
        }
        if (reachability.get(continuation) == null) {
            throw new IllegalStateException("business-continuation-unreachable");
        }
        for (FieldInsnNode write : fieldWrites) {
            if (baselineReachable.contains(write) && reachability.get(write) == null) {
                throw new IllegalStateException("business-field-write-lost=" + write.name + write.desc);
            }
        }
        for (MethodInsnNode call : stateCalls) {
            if (baselineReachable.contains(call) && reachability.get(call) == null) {
                throw new IllegalStateException("long-key-state-call-lost=" + call.owner + "." + call.name);
            }
        }
        MethodInsnNode originalFactory = (MethodInsnNode) code.nodes.get(expected.startCodeIndex + 1);
        if (reachability.get(originalFactory) != null) {
            throw new IllegalStateException("crypto-entry-still-reachable");
        }

        Set<AbstractInsnNode> dead = Collections.newSetFromMap(
                new IdentityHashMap<AbstractInsnNode, Boolean>());
        for (AbstractInsnNode insn : baselineReachable) {
            if (insn.getOpcode() >= 0 && reachability.get(insn) == null) dead.add(insn);
        }
        if (!dead.contains(start) || dead.size() < 20) {
            throw new IllegalStateException("newly-unreachable-crypto=" + dead.size());
        }
        Set<AbstractInsnNode> metadata = Collections.newSetFromMap(
                new IdentityHashMap<AbstractInsnNode, Boolean>());
        for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
             insn = insn.getNext()) {
            if (!(insn instanceof FrameNode) && !(insn instanceof LineNumberNode)) continue;
            AbstractInsnNode next = nextCode(insn);
            if (next != null && dead.contains(next)) metadata.add(insn);
        }
        for (AbstractInsnNode insn : dead) method.instructions.remove(insn);
        for (AbstractInsnNode insn : metadata) method.instructions.remove(insn);
        pruneUntargetedDeadLabels(method, dead, continuationLabel);
        if (method.localVariables != null) method.localVariables.clear();
        method.visibleLocalVariableAnnotations = null;
        method.invisibleLocalVariableAnnotations = null;

        Frame<BasicValue>[] finalFrames = analyzer.analyze(owner.name, method);
        if (finalFrames.length == 0 || countReachableReturns(method, finalFrames) == 0) {
            throw new IllegalStateException("rewritten-clinit-has-no-return");
        }
    }

    private static LabelNode labelBefore(MethodNode method, AbstractInsnNode target) {
        AbstractInsnNode cursor = target.getPrevious();
        while (cursor != null && cursor.getOpcode() < 0) {
            if (cursor instanceof LabelNode) return (LabelNode) cursor;
            cursor = cursor.getPrevious();
        }
        LabelNode label = new LabelNode();
        method.instructions.insertBefore(target, label);
        return label;
    }

    private static void pruneUntargetedDeadLabels(MethodNode method,
                                                   Set<AbstractInsnNode> dead,
                                                   LabelNode continuation) {
        Set<LabelNode> targets = Collections.newSetFromMap(new IdentityHashMap<LabelNode, Boolean>());
        targets.add(continuation);
        for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
             insn = insn.getNext()) {
            if (insn instanceof JumpInsnNode) targets.add(((JumpInsnNode) insn).label);
            else if (insn instanceof TableSwitchInsnNode) {
                TableSwitchInsnNode table = (TableSwitchInsnNode) insn;
                targets.add(table.dflt);
                targets.addAll(table.labels);
            } else if (insn instanceof LookupSwitchInsnNode) {
                LookupSwitchInsnNode lookup = (LookupSwitchInsnNode) insn;
                targets.add(lookup.dflt);
                targets.addAll(lookup.labels);
            }
        }
        List<LabelNode> remove = new ArrayList<>();
        for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
             insn = insn.getNext()) {
            if (!(insn instanceof LabelNode) || targets.contains(insn)) continue;
            AbstractInsnNode next = nextCode(insn);
            if (next == null || dead.contains(next)) remove.add((LabelNode) insn);
        }
        for (LabelNode label : remove) method.instructions.remove(label);
    }

    private static int countReachableReturns(MethodNode method, Frame<BasicValue>[] frames) {
        int result = 0;
        for (int index = 0; index < method.instructions.size() && index < frames.length; index++) {
            if (frames[index] != null && method.instructions.get(index).getOpcode() == Opcodes.RETURN) result++;
        }
        return result;
    }

    private static void assertRewritten(byte[] bytes, Candidate candidate) {
        ClassNode owner = readClass(bytes);
        MethodNode clinit = method(owner, "<clinit>", "()V");
        if (clinit == null) throw new IllegalStateException("rewritten <clinit> missing");
        int after = countCipherFactories(clinit, ALGORITHM);
        if (after != candidate.originalNoPaddingCount - 1) {
            throw new IllegalStateException("NoPadding-count=" + after + "/"
                    + (candidate.originalNoPaddingCount - 1));
        }
        int constants = 0;
        int stores = 0;
        for (AbstractInsnNode insn = clinit.instructions.getFirst(); insn != null;
             insn = insn.getNext()) {
            if (insn instanceof LdcInsnNode && ((LdcInsnNode) insn).cst instanceof Long
                    && candidate.values.contains((Long) ((LdcInsnNode) insn).cst)) constants++;
            if (insn.getOpcode() == Opcodes.LASTORE) stores++;
        }
        if (constants < candidate.values.size() || stores < candidate.values.size()) {
            throw new IllegalStateException("explicit-table=" + constants + "/" + stores
                    + "/" + candidate.values.size());
        }
    }

    private static Map<String, Long> evaluateHierarchyKeys(Map<String, ClassNode> classes) {
        ZkmLongKeyEvaluator.StatefulKeySequence sequence =
                ZkmLongKeyEvaluator.newStatefulKeySequence(classes);
        Set<String> keyOwners = new LinkedHashSet<>(sequence.owners());
        List<String> order = new ArrayList<>();
        Set<String> visited = new HashSet<>();
        Set<String> active = new HashSet<>();
        for (String owner : sequence.owners()) {
            visitHierarchy(owner, classes, keyOwners, visited, active, order);
        }
        Map<String, Long> result = new LinkedHashMap<>();
        for (String owner : order) result.put(owner, sequence.commit(owner));
        return result;
    }

    private static Map<String, Long> safeClassKeys(Map<String, ClassNode> classes,
                                                   boolean sequential) {
        if (!classes.containsKey(STATE)
                || !classes.containsKey(ObfRuntimeNames.GRAPH_BOOTSTRAP)) {
            return Collections.emptyMap();
        }
        return sequential ? ZkmLongKeyEvaluator.evaluateClassKeysSequential(classes)
                : ZkmLongKeyEvaluator.evaluateClassKeys(classes);
    }

    private static Map<String, Long> safeHierarchyKeys(Map<String, ClassNode> classes) {
        if (!classes.containsKey(STATE)
                || !classes.containsKey(ObfRuntimeNames.GRAPH_BOOTSTRAP)) {
            return Collections.emptyMap();
        }
        return evaluateHierarchyKeys(classes);
    }

    private static void visitHierarchy(String owner, Map<String, ClassNode> classes,
                                       Set<String> keyOwners, Set<String> visited,
                                       Set<String> active, List<String> order) {
        if (visited.contains(owner)) return;
        if (!active.add(owner)) throw new IllegalStateException("hierarchy-cycle=" + owner);
        ClassNode node = classes.get(owner);
        if (node != null && (node.access & Opcodes.ACC_INTERFACE) == 0
                && node.superName != null && classes.containsKey(node.superName)) {
            visitHierarchy(node.superName, classes, keyOwners, visited, active, order);
        }
        active.remove(owner);
        visited.add(owner);
        if (keyOwners.contains(owner)) order.add(owner);
    }

    private static int followGotoChain(Code code, int index) {
        Set<Integer> seen = new HashSet<>();
        int current = index;
        while (current >= 0 && current < code.nodes.size() && seen.add(current)) {
            AbstractInsnNode insn = code.nodes.get(current);
            if (!(insn instanceof JumpInsnNode) || insn.getOpcode() != Opcodes.GOTO) break;
            current = code.target(((JumpInsnNode) insn).label);
        }
        return current;
    }

    private static boolean isCipherFactory(AbstractInsnNode insn, String algorithm) {
        if (!(insn instanceof MethodInsnNode)) return false;
        MethodInsnNode call = (MethodInsnNode) insn;
        AbstractInsnNode previous = previousCode(insn);
        return call.getOpcode() == Opcodes.INVOKESTATIC
                && "javax/crypto/Cipher".equals(call.owner)
                && "getInstance".equals(call.name)
                && "(Ljava/lang/String;)Ljavax/crypto/Cipher;".equals(call.desc)
                && previous instanceof LdcInsnNode
                && algorithm.equals(((LdcInsnNode) previous).cst);
    }

    private static boolean isAnyCipherFactory(AbstractInsnNode insn) {
        if (!(insn instanceof MethodInsnNode)) return false;
        MethodInsnNode call = (MethodInsnNode) insn;
        return call.getOpcode() == Opcodes.INVOKESTATIC
                && "javax/crypto/Cipher".equals(call.owner)
                && "getInstance".equals(call.name)
                && "(Ljava/lang/String;)Ljavax/crypto/Cipher;".equals(call.desc);
    }

    private static int countCipherFactories(MethodNode method, String algorithm) {
        int result = 0;
        for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
             insn = insn.getNext()) if (isCipherFactory(insn, algorithm)) result++;
        return result;
    }

    private static boolean isCall(AbstractInsnNode insn, int opcode,
                                  String owner, String name, String desc) {
        if (!(insn instanceof MethodInsnNode)) return false;
        MethodInsnNode call = (MethodInsnNode) insn;
        return call.getOpcode() == opcode && owner.equals(call.owner)
                && name.equals(call.name) && desc.equals(call.desc);
    }

    private static String call(int opcode, String owner, String name, String desc) {
        return opcode + ":" + owner + "." + name + desc;
    }

    private static boolean latin1(String value) {
        for (int index = 0; index < value.length(); index++) {
            if (value.charAt(index) > 0xff) return false;
        }
        return true;
    }

    private static Integer intConstant(AbstractInsnNode insn) {
        if (insn == null) return null;
        int opcode = insn.getOpcode();
        if (opcode >= Opcodes.ICONST_M1 && opcode <= Opcodes.ICONST_5) {
            return opcode - Opcodes.ICONST_0;
        }
        if (insn instanceof IntInsnNode && (opcode == Opcodes.BIPUSH
                || opcode == Opcodes.SIPUSH)) return ((IntInsnNode) insn).operand;
        if (insn instanceof LdcInsnNode && ((LdcInsnNode) insn).cst instanceof Integer) {
            return (Integer) ((LdcInsnNode) insn).cst;
        }
        return null;
    }

    private static void pushInt(InsnList list, int value) {
        if (value >= -1 && value <= 5) list.add(new InsnNode(Opcodes.ICONST_0 + value));
        else if (value >= Byte.MIN_VALUE && value <= Byte.MAX_VALUE)
            list.add(new IntInsnNode(Opcodes.BIPUSH, value));
        else if (value >= Short.MIN_VALUE && value <= Short.MAX_VALUE)
            list.add(new IntInsnNode(Opcodes.SIPUSH, value));
        else list.add(new LdcInsnNode(value));
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

    private static ClassNode readClass(byte[] bytes) {
        ClassNode owner = new ClassNode(Opcodes.ASM9);
        new ClassReader(bytes).accept(owner, 0);
        return owner;
    }

    private static Map<String, ClassNode> classNodes(Map<String, byte[]> bytes) {
        Map<String, ClassNode> result = new LinkedHashMap<>();
        for (Map.Entry<String, byte[]> entry : bytes.entrySet()) {
            result.put(entry.getKey(), readClass(entry.getValue()));
        }
        return result;
    }

    private static byte[] writeClass(ClassNode owner, Map<String, ClassNode> hierarchy) {
        int flags = containsLegacySubroutine(owner)
                ? ClassWriter.COMPUTE_MAXS
                : ClassWriter.COMPUTE_FRAMES | ClassWriter.COMPUTE_MAXS;
        ClassWriter writer = flags == ClassWriter.COMPUTE_MAXS
                ? new ClassWriter(flags)
                : new HierarchyClassWriter(flags, hierarchy);
        owner.accept(writer);
        return writer.toByteArray();
    }

    private static boolean containsLegacySubroutine(ClassNode owner) {
        for (MethodNode method : owner.methods) {
            for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
                 insn = insn.getNext()) {
                if (insn.getOpcode() == Opcodes.JSR || insn.getOpcode() == Opcodes.RET) {
                    return true;
                }
            }
        }
        return false;
    }

    private static void verifyClass(byte[] bytes) throws Exception {
        ClassReader reader = new ClassReader(bytes);
        reader.accept(new CheckClassAdapter(new ClassWriter(0), false), 0);
        ClassNode owner = readClass(bytes);
        for (MethodNode method : owner.methods) {
            if (method.instructions != null && method.instructions.size() != 0) {
                new Analyzer<>(new BasicVerifier()).analyze(owner.name, method);
            }
        }
    }

    private static List<EntryBytes> readEntries(Path input) throws IOException {
        List<EntryBytes> result = new ArrayList<>();
        try (ZipInputStream zip = new ZipInputStream(Files.newInputStream(input))) {
            ZipEntry entry;
            while ((entry = zip.getNextEntry()) != null) {
                result.add(new EntryBytes(entry, readAll(zip)));
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

    private static byte[] readAll(java.io.InputStream input) throws IOException {
        ByteArrayOutputStream output = new ByteArrayOutputStream();
        byte[] buffer = new byte[8192];
        int count;
        while ((count = input.read(buffer)) >= 0) if (count != 0) output.write(buffer, 0, count);
        return output.toByteArray();
    }

    private static void writeVerifiedArchive(List<EntryBytes> entries,
                                             Map<String, byte[]> replacements,
                                             Path output,
                                             Map<String, ClassNode> hierarchy,
                                             Summary summary,
                                             List<String> verifier) throws IOException {
        Path parent = output.toAbsolutePath().getParent();
        if (parent == null) parent = Paths.get(".").toAbsolutePath();
        Files.createDirectories(parent);
        Path temporary = Files.createTempFile(parent, output.getFileName().toString() + ".", ".tmp");
        try {
            Set<String> applied = new LinkedHashSet<>();
            try (ZipOutputStream zip = new ZipOutputStream(Files.newOutputStream(temporary))) {
                for (EntryBytes entry : entries) {
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
                    zip.putNextEntry(written);
                    zip.write(bytes);
                    zip.closeEntry();
                }
            }
            if (!applied.equals(replacements.keySet())) {
                throw new IOException("replacement-coverage=" + applied.size() + "/"
                        + replacements.size());
            }
            verifyArchive(temporary, summary, verifier);
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

    private static void verifyArchive(Path archive, Summary summary,
                                      List<String> verifier) throws IOException {
        try (ZipInputStream zip = new ZipInputStream(Files.newInputStream(archive))) {
            ZipEntry entry;
            while ((entry = zip.getNextEntry()) != null) {
                byte[] bytes = readAll(zip);
                if (!entry.getName().endsWith(".class")) continue;
                summary.outputClasses++;
                try {
                    verifyClass(bytes);
                    ClassNode owner = readClass(bytes);
                    for (MethodNode method : owner.methods) {
                        summary.outputResidualNoPadding += countCipherFactories(method, ALGORITHM);
                    }
                    verifier.add(tsv("archive", owner.name, "PASS", ""));
                } catch (Throwable failure) {
                    summary.outputVerificationErrors++;
                    verifier.add(tsv("archive", entry.getName(), "FAIL", shortReason(failure)));
                }
            }
        }
    }

    private static void writeReports(Path input, Path output, Path report,
                                     Summary summary, List<Candidate> candidates,
                                     List<String> verifier) throws Exception {
        List<String> rows = new ArrayList<>();
        rows.add("class\tcapacity\tentries\tpacked_literals\tarray_local\tstate_derived"
                + "\tclass_key_hex\touter_mask_hex\touter_key_hex\tkey_source"
                + "\tisolated_key_hex\tsequential_key_hex\thierarchy_key_hex"
                + "\tno_padding_factories\taction\tproven\treason");
        for (Candidate candidate : candidates) rows.add(candidate.row());
        Files.write(report.resolve("candidates.tsv"), rows, StandardCharsets.UTF_8);
        List<String> tables = new ArrayList<>();
        tables.add("class\tindex\tvalue\tvalue_hex");
        for (Candidate candidate : candidates) {
            for (int index = 0; index < candidate.values.size(); index++) {
                long value = candidate.values.get(index);
                tables.add(tsv(candidate.owner, index, value, hex(value)));
            }
        }
        Files.write(report.resolve("tables.tsv"), tables, StandardCharsets.UTF_8);
        Files.write(report.resolve("verifier.tsv"), verifier, StandardCharsets.UTF_8);
        List<String> audit = new ArrayList<>();
        audit.add("input=" + input.toAbsolutePath().normalize());
        audit.add("input_sha256=" + sha256(Files.readAllBytes(input)));
        audit.add("output=" + (output == null ? "" : output.toAbsolutePath().normalize()));
        audit.add("parsed_classes=" + summary.parsedClasses);
        audit.add("candidates=" + summary.candidates);
        audit.add("proven=" + summary.proven);
        audit.add("rejected=" + summary.rejected);
        audit.add("table_entries=" + summary.tableEntries);
        audit.add("changed_classes=" + summary.changedClasses);
        audit.add("rollbacks=" + summary.rollbacks);
        audit.add("output_classes=" + summary.outputClasses);
        audit.add("output_residual_nopadding=" + summary.outputResidualNoPadding);
        audit.add("output_verification_errors=" + summary.outputVerificationErrors);
        audit.add("output_committed=" + summary.outputCommitted);
        audit.add("key_policy=literal or validated string key only; isolated/static/sequential/hierarchy models are audit candidates");
        audit.add("rewrite_policy=explicit local long array; preserve key-state prefix and all reachable owner field writes");
        audit.add("input_classes_loaded=false");
        String gate = summary.rollbacks == 0 && summary.outputVerificationErrors == 0
                && (output == null || summary.outputCommitted) ? "PASS" : "FAIL";
        audit.add("integrity_gate=" + gate);
        Files.write(report.resolve("audit.txt"), audit, StandardCharsets.UTF_8);
        Files.write(report.resolve("gate.txt"), Collections.singletonList(gate),
                StandardCharsets.UTF_8);
    }

    private static String sha256(byte[] bytes) throws Exception {
        MessageDigest digest = MessageDigest.getInstance("SHA-256");
        StringBuilder result = new StringBuilder();
        for (byte value : digest.digest(bytes)) result.append(String.format("%02X", value));
        return result.toString();
    }

    private static String shortReason(Throwable failure) {
        String message = failure.getMessage();
        String result = failure.getClass().getSimpleName()
                + (message == null ? "" : ":" + message);
        return result.replace('\t', ' ').replace('\r', ' ').replace('\n', ' ');
    }

    private static String tsv(Object... values) {
        StringBuilder result = new StringBuilder();
        for (Object value : values) {
            if (result.length() != 0) result.append('\t');
            result.append(value == null ? "" : value.toString().replace('\t', ' ')
                    .replace('\r', ' ').replace('\n', ' '));
        }
        return result.toString();
    }

    private static String hex(long value) {
        return String.format(Locale.ROOT, "%016X", value);
    }

    private static String hex(Long value) {
        return value == null ? "" : hex(value.longValue());
    }

    static final class Summary {
        int parsedClasses;
        int candidates;
        int proven;
        int rejected;
        int tableEntries;
        int changedClasses;
        int rollbacks;
        int outputClasses;
        int outputResidualNoPadding;
        int outputVerificationErrors;
        boolean outputCommitted;
    }

    private static final class Candidate {
        final String owner;
        int capacity;
        int arrayLocal;
        int packedLiterals;
        int startCodeIndex;
        int continuationCodeIndex;
        int noPaddingFactories;
        int originalNoPaddingCount;
        long key;
        Long classKey;
        long outerMask;
        String keySource = "";
        Long isolatedClassKey;
        Long sequentialClassKey;
        Long hierarchyClassKey;
        boolean stateDerived;
        boolean proven;
        String action = "REJECT";
        String reason = "";
        final List<Long> values = new ArrayList<>();

        Candidate(String owner) {
            this.owner = owner;
        }

        Candidate reject(String reason) {
            this.reason = reason;
            return this;
        }

        String row() {
            return tsv(owner, capacity, values.size(), packedLiterals, arrayLocal,
                    stateDerived, hex(classKey), stateDerived ? hex(outerMask) : "",
                    hex(key), keySource, hex(isolatedClassKey), hex(sequentialClassKey),
                    hex(hierarchyClassKey), noPaddingFactories, action, proven, reason);
        }
    }

    private static final class Allocation {
        final int sizeIndex;
        final int allocationIndex;
        final int storeIndex;
        final int capacity;
        final int local;

        Allocation(int sizeIndex, int allocationIndex, int storeIndex,
                   int capacity, int local) {
            this.sizeIndex = sizeIndex;
            this.allocationIndex = allocationIndex;
            this.storeIndex = storeIndex;
            this.capacity = capacity;
            this.local = local;
        }
    }

    private static final class PackedLoop {
        final int literalIndex;
        final int exitIndex;
        final String packed;

        PackedLoop(int literalIndex, int exitIndex, String packed) {
            this.literalIndex = literalIndex;
            this.exitIndex = exitIndex;
            this.packed = packed;
        }
    }

    private static final class KeySelection {
        long outerKey;
        Long classKey;
        long outerMask;
        String source;
        boolean stateDerived;
        boolean trusted;
        Long isolated;
        Long sequential;
        Long hierarchy;
    }

    private static final class Code {
        final MethodNode method;
        final List<AbstractInsnNode> nodes = new ArrayList<>();
        final Map<AbstractInsnNode, Integer> indexes = new IdentityHashMap<>();

        Code(MethodNode method) {
            this.method = method;
            for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
                 insn = insn.getNext()) {
                if (insn.getOpcode() < 0) continue;
                indexes.put(insn, nodes.size());
                nodes.add(insn);
            }
        }

        int target(LabelNode label) {
            AbstractInsnNode target = nextCode(label);
            Integer index = indexes.get(target);
            return index == null ? -1 : index;
        }
    }

    private static final class EntryBytes {
        final String name;
        final byte[] bytes;
        final int method;
        final long time;
        final String comment;
        final byte[] extra;

        EntryBytes(ZipEntry entry, byte[] bytes) {
            this.name = entry.getName();
            this.bytes = bytes;
            this.method = entry.getMethod();
            this.time = entry.getTime();
            this.comment = entry.getComment();
            this.extra = entry.getExtra();
        }
    }

    private static final class HierarchyClassWriter extends ClassWriter {
        private final Map<String, ClassNode> classes;

        HierarchyClassWriter(int flags, Map<String, ClassNode> classes) {
            super(flags);
            this.classes = classes;
        }

        @Override
        protected String getCommonSuperClass(String left, String right) {
            if (left.equals(right)) return left;
            if (left.startsWith("[") || right.startsWith("[")) {
                return commonArray(left, right);
            }
            if (isAssignable(left, right)) return left;
            if (isAssignable(right, left)) return right;
            Set<String> rightTypes = supertypes(right);
            for (String type : orderedSupertypes(left)) {
                if (rightTypes.contains(type)) return type;
            }
            return "java/lang/Object";
        }

        private String commonArray(String left, String right) {
            if (!left.startsWith("[") || !right.startsWith("[")) return "java/lang/Object";
            Type a = Type.getType(left);
            Type b = Type.getType(right);
            if (a.getDimensions() != b.getDimensions()) return "java/lang/Object";
            Type ea = a.getElementType();
            Type eb = b.getElementType();
            if (ea.getSort() != Type.OBJECT || eb.getSort() != Type.OBJECT) {
                return left.equals(right) ? left : "java/lang/Object";
            }
            String common = getCommonSuperClass(ea.getInternalName(), eb.getInternalName());
            StringBuilder descriptor = new StringBuilder();
            for (int index = 0; index < a.getDimensions(); index++) descriptor.append('[');
            return descriptor.append('L').append(common).append(';').toString();
        }

        private boolean isAssignable(String target, String source) {
            return "java/lang/Object".equals(target) || supertypes(source).contains(target);
        }

        private Set<String> supertypes(String type) {
            return new LinkedHashSet<>(orderedSupertypes(type));
        }

        private List<String> orderedSupertypes(String type) {
            List<String> result = new ArrayList<>();
            Set<String> seen = new HashSet<>();
            ArrayDeque<String> queue = new ArrayDeque<>();
            queue.add(type);
            while (!queue.isEmpty()) {
                String current = queue.removeFirst();
                if (!seen.add(current)) continue;
                result.add(current);
                ClassNode node = classes.get(current);
                if (node != null) {
                    if (node.superName != null) queue.addLast(node.superName);
                    if (node.interfaces != null) queue.addAll(node.interfaces);
                } else if (!"java/lang/Object".equals(current)) {
                    queue.addLast("java/lang/Object");
                }
            }
            if (!seen.contains("java/lang/Object")) result.add("java/lang/Object");
            return result;
        }
    }
}
