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
import org.objectweb.asm.tree.InsnList;
import org.objectweb.asm.tree.InsnNode;
import org.objectweb.asm.tree.IntInsnNode;
import org.objectweb.asm.tree.JumpInsnNode;
import org.objectweb.asm.tree.LabelNode;
import org.objectweb.asm.tree.LdcInsnNode;
import org.objectweb.asm.tree.MethodInsnNode;
import org.objectweb.asm.tree.MethodNode;
import org.objectweb.asm.tree.TableSwitchInsnNode;
import org.objectweb.asm.tree.LookupSwitchInsnNode;
import org.objectweb.asm.tree.TypeInsnNode;
import org.objectweb.asm.tree.VarInsnNode;
import org.objectweb.asm.tree.InvokeDynamicInsnNode;
import org.objectweb.asm.tree.MultiANewArrayInsnNode;
import org.objectweb.asm.tree.analysis.Analyzer;
import org.objectweb.asm.tree.analysis.BasicValue;
import org.objectweb.asm.tree.analysis.BasicVerifier;
import org.objectweb.asm.tree.analysis.Frame;
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
import java.util.HashMap;
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
 * Replaces only the closed DES string slice in a mixed static initializer.
 *
 * <p>This pass is intentionally narrower than
 * {@link ZkmDirectStringConstantDeobfuscator}: instructions before the
 * algorithm literal and after the unique crypto exit are retained bytecode
 * operations.  This is needed for classes such as Wrapper, whose initializer
 * performs real state setup around the obfuscated string. A surrounding
 * exception range is retained only when it completely contains the slice and
 * its handler is outside the removed instructions. No class is defined,
 * loaded, initialized, or reflectively queried.</p>
 */
public final class ZkmDirectStringFragmentDeobfuscator {
    private static final String ALGORITHM = "DES/CBC/PKCS5Padding";
    private static final String KEY_ALGORITHM = "DES";
    private static final String LATIN1 = "ISO-8859-1";
    private static final String STRING_DESC = "Ljava/lang/String;";
    private static final String DECODE_DESC = "([B)Ljava/lang/String;";

    private ZkmDirectStringFragmentDeobfuscator() {
    }

    public static void main(String[] args) throws Exception {
        if (args.length != 2 && args.length != 3) {
            System.err.println("usage: ZkmDirectStringFragmentDeobfuscator"
                    + " <input.jar> <report-dir> [output.jar]");
            System.exit(2);
        }
        deobfuscate(Paths.get(args[0]), Paths.get(args[1]),
                args.length == 3 ? Paths.get(args[2]) : null);
    }

    static Summary deobfuscate(Path input, Path reportDirectory, Path output)
            throws Exception {
        validatePaths(input, output);
        Files.createDirectories(reportDirectory);
        List<EntryBytes> entries = readEntries(input);
        Map<String, byte[]> original = classBytes(entries);
        Map<String, ClassNode> classes = readClasses(original);
        Map<MethodRef, Integer> references = methodReferences(classes);
        Summary summary = new Summary();
        summary.parsedClasses = classes.size();
        summary.outputRequested = output != null;
        List<Candidate> candidates = new ArrayList<>();
        List<String> verifier = new ArrayList<>();
        verifier.add("scope\tclass\tstatus\treason");
        Map<String, byte[]> replacements = new LinkedHashMap<>();

        for (Map.Entry<String, byte[]> entry : original.entrySet()) {
            ClassNode owner = classes.get(entry.getKey());
            Candidate candidate = inspect(owner, references, summary);
            if (candidate == null) continue;
            candidates.add(candidate);
            if (!candidate.proven()) continue;
            summary.provenCandidates++;
            summary.provenStrings++;
            if (output == null) {
                candidate.action = "PROVEN_DRY_RUN";
                continue;
            }
            try {
                ClassNode rewritten = readClass(entry.getValue());
                apply(rewritten, candidate);
                byte[] bytes = writeClass(rewritten);
                verifyClass(bytes);
                assertRewritten(bytes, candidate);
                replacements.put(rewritten.name, bytes);
                candidate.action = "REWRITE";
                summary.changedClasses++;
                summary.rewrittenFields++;
                if (candidate.removeHelper) summary.helpersRemoved++;
                verifier.add(tsv("class-transaction", owner.name, "PASS", ""));
            } catch (Throwable failure) {
                candidate.action = "ROLLBACK";
                candidate.reason = appendReason(candidate.reason,
                        "class-rollback:" + shortReason(failure));
                summary.classRollbacks++;
                verifier.add(tsv("class-transaction", owner.name, "ROLLBACK",
                        shortReason(failure)));
            }
        }

        summary.rejectedCandidates = summary.pkcs5ClinitClasses
                - summary.provenCandidates;
        if (output != null) {
            try {
                writeVerifiedArchive(entries, replacements, output, summary,
                        verifier);
            } catch (Throwable failure) {
                summary.outputVerificationErrors++;
                verifier.add(tsv("archive", "<archive>", "FAIL",
                        "write:" + shortReason(failure)));
            }
        }
        writeReports(input, reportDirectory, output, summary, candidates,
                verifier);
        System.out.println("pkcs5_clinit_classes=" + summary.pkcs5ClinitClasses
                + " proven=" + summary.provenCandidates
                + " rewritten=" + summary.rewrittenFields
                + " rollbacks=" + summary.classRollbacks
                + " output_committed=" + summary.outputCommitted
                + " gate=" + gate(summary));
        return summary;
    }

    private static Candidate inspect(ClassNode owner,
                                     Map<MethodRef, Integer> references,
                                     Summary summary) {
        if (owner == null) return null;
        MethodNode clinit = method(owner, "<clinit>", "()V");
        if (clinit == null) return null;
        int pkcs5 = 0;
        for (AbstractInsnNode insn = clinit.instructions.getFirst(); insn != null;
             insn = insn.getNext()) {
            if (isCipherFactory(insn, ALGORITHM)) pkcs5++;
        }
        if (pkcs5 == 0) return null;
        summary.pkcs5ClinitClasses++;
        Candidate candidate = new Candidate(owner.name, clinit.instructions.size());
        candidate.pkcs5Calls = pkcs5;
        if (pkcs5 != 1) return candidate.reject("pkcs5-call-count=" + pkcs5);
        Slice slice;
        try {
            slice = locateSlice(owner, clinit);
        } catch (Throwable failure) {
            return candidate.reject("slice:" + shortReason(failure));
        }
        candidate.slice = slice;
        candidate.fieldName = slice.field.name;
        candidate.key = slice.key;
        candidate.ciphertext = slice.ciphertext;
        candidate.plaintext = slice.plaintext;
        candidate.helperName = slice.helper.name;
        candidate.helperReferences = references.getOrDefault(
                new MethodRef(owner.name, slice.helper.name, DECODE_DESC), 0);
        candidate.removeHelper = candidate.helperReferences == 1;
        candidate.action = "PROVEN";
        return candidate;
    }

    /** Locates and proves the only closed DES island in a mixed initializer. */
    private static Slice locateSlice(ClassNode owner, MethodNode clinit)
            throws Exception {
        Code code = new Code(clinit);
        MethodInsnNode factory = null;
        int factoryIndex = -1;
        for (int i = 0; i < code.nodes.size(); i++) {
            AbstractInsnNode insn = code.nodes.get(i);
            if (isCipherFactory(insn, ALGORITHM)) {
                factory = (MethodInsnNode) insn;
                factoryIndex = i;
            }
        }
        if (factory == null) throw new IllegalArgumentException("missing-cipher");
        AbstractInsnNode start = previousCode(code.nodes.get(factoryIndex));
        if (!(start instanceof LdcInsnNode)
                || !ALGORITHM.equals(((LdcInsnNode) start).cst)) {
            throw new IllegalArgumentException("algorithm-entry-not-ldc");
        }
        int startIndex = code.index(start);

        List<MethodInsnNode> helperCalls = new ArrayList<>();
        List<FieldInsnNode> writes = new ArrayList<>();
        List<MethodInsnNode> calls = new ArrayList<>();
        List<String> strings = new ArrayList<>();
        Set<Long> keys = new LinkedHashSet<>();
        int keyLoads = 0;
        int endCandidate = -1;
        FieldInsnNode target = null;
        for (int i = startIndex; i < code.nodes.size(); i++) {
            AbstractInsnNode insn = code.nodes.get(i);
            if (insn instanceof MethodInsnNode) {
                MethodInsnNode call = (MethodInsnNode) insn;
                calls.add(call);
                if (owner.name.equals(call.owner) && DECODE_DESC.equals(call.desc)
                        && call.getOpcode() == Opcodes.INVOKESTATIC) {
                    helperCalls.add(call);
                }
            }
            if (insn instanceof LdcInsnNode) {
                Object value = ((LdcInsnNode) insn).cst;
                if (value instanceof String) strings.add((String) value);
                if (value instanceof Long) {
                    keys.add((Long) value);
                    keyLoads++;
                }
            }
            if (insn instanceof FieldInsnNode
                    && insn.getOpcode() == Opcodes.PUTSTATIC
                    && owner.name.equals(((FieldInsnNode) insn).owner)
                    && STRING_DESC.equals(((FieldInsnNode) insn).desc)) {
                writes.add((FieldInsnNode) insn);
                AbstractInsnNode next = nextCode(insn);
                if (target == null && next instanceof JumpInsnNode
                        && next.getOpcode() == Opcodes.GOTO) {
                    target = (FieldInsnNode) insn;
                    JumpInsnNode exit = (JumpInsnNode) next;
                    int exitTarget = code.index(exit.label);
                    int protectedEnd = coveringExceptionEnd(clinit, code,
                            startIndex, i, exitTarget);
                    if (protectedEnd > i) {
                        // Some ZKM loops place their loop body after the field
                        // write in bytecode order. The try-end label is the
                        // first boundary that includes the complete loop while
                        // still excluding the javac catch handler.
                        endCandidate = protectedEnd;
                    } else if (exitTarget > i) {
                        endCandidate = exitTarget;
                    }
                }
            }
            if (endCandidate >= 0 && i >= endCandidate) break;
        }
        if (target == null || endCandidate <= startIndex) {
            throw new IllegalArgumentException("missing-closed-exit");
        }
        if (writes.size() != 1) {
            throw new IllegalArgumentException("string-putstatic-count="
                    + writes.size());
        }
        if (helperCalls.size() != 1) {
            throw new IllegalArgumentException("decoder-call-count="
                    + helperCalls.size());
        }
        MethodNode helper = method(owner, helperCalls.get(0).name, DECODE_DESC);
        if (helper == null || (helper.access & (Opcodes.ACC_PRIVATE | Opcodes.ACC_STATIC))
                != (Opcodes.ACC_PRIVATE | Opcodes.ACC_STATIC)) {
            throw new IllegalArgumentException("decoder-not-private-static="
                    + helperCalls.get(0).name);
        }
        FieldNode field = field(owner, target.name, STRING_DESC);
        if (field == null || (field.access & (Opcodes.ACC_STATIC | Opcodes.ACC_FINAL))
                != (Opcodes.ACC_STATIC | Opcodes.ACC_FINAL)) {
            throw new IllegalArgumentException("target-not-static-final-string="
                    + target.name);
        }
        if (keys.size() != 1 || keyLoads != 2) {
            throw new IllegalArgumentException("constant-key-shape=unique:"
                    + keys.size() + ",loads:" + keyLoads);
        }
        int algorithm = 0;
        int keyAlgorithm = 0;
        int charset = 0;
        List<String> ciphertext = new ArrayList<>();
        for (String value : strings) {
            if (ALGORITHM.equals(value)) algorithm++;
            else if (KEY_ALGORITHM.equals(value)) keyAlgorithm++;
            else if (LATIN1.equals(value)) charset++;
            else ciphertext.add(value);
        }
        if (algorithm != 1 || keyAlgorithm != 1 || charset != 1
                || ciphertext.size() != 1) {
            throw new IllegalArgumentException("string-constant-shape=algorithm:"
                    + algorithm + ",key-algorithm:" + keyAlgorithm
                    + ",charset:" + charset + ",ciphertext:" + ciphertext.size());
        }
        String encrypted = ciphertext.get(0);
        if (!latin1Ciphertext(encrypted) || encrypted.length() % 8 != 0) {
            throw new IllegalArgumentException("ciphertext-not-latin1-des-blocks:length="
                    + encrypted.length());
        }
        long key = keys.iterator().next();
        String plaintext = decrypt(encrypted, key);
        if (plaintext.indexOf('\u0000') >= 0) {
            throw new IllegalArgumentException("plaintext-contains-nul");
        }
        int endExclusive = endCandidate;
        validateBoundary(owner, clinit, code, startIndex, endExclusive);
        validateCallSet(owner, calls, helperCalls.get(0));
        validateStackBoundary(owner, clinit, code, startIndex, endExclusive);
        return new Slice(start, code.nodes.get(endExclusive), target, helper,
                key, encrypted, plaintext);
    }

    private static void validateCallSet(ClassNode owner, List<MethodInsnNode> calls,
                                        MethodInsnNode helper) {
        Map<String, Integer> expected = new LinkedHashMap<>();
        expected.put(call(Opcodes.INVOKESTATIC, "javax/crypto/Cipher", "getInstance",
                "(Ljava/lang/String;)Ljavax/crypto/Cipher;"), 1);
        expected.put(call(Opcodes.INVOKESTATIC, "javax/crypto/SecretKeyFactory",
                "getInstance", "(Ljava/lang/String;)Ljavax/crypto/SecretKeyFactory;"), 1);
        expected.put(call(Opcodes.INVOKESPECIAL, "javax/crypto/spec/DESKeySpec",
                "<init>", "([B)V"), 1);
        expected.put(call(Opcodes.INVOKEVIRTUAL, "javax/crypto/SecretKeyFactory",
                "generateSecret", "(Ljava/security/spec/KeySpec;)Ljavax/crypto/SecretKey;"), 1);
        expected.put(call(Opcodes.INVOKESPECIAL, "javax/crypto/spec/IvParameterSpec",
                "<init>", "([B)V"), 1);
        expected.put(call(Opcodes.INVOKEVIRTUAL, "javax/crypto/Cipher", "init",
                "(ILjava/security/Key;Ljava/security/spec/AlgorithmParameterSpec;)V"), 1);
        expected.put(call(Opcodes.INVOKEVIRTUAL, "java/lang/String", "getBytes",
                "(Ljava/lang/String;)[B"), 1);
        expected.put(call(Opcodes.INVOKEVIRTUAL, "javax/crypto/Cipher", "doFinal",
                "([B)[B"), 1);
        expected.put(call(Opcodes.INVOKEVIRTUAL, "java/lang/String", "intern",
                "()Ljava/lang/String;"), 1);
        Map<String, Integer> actual = new LinkedHashMap<>();
        for (MethodInsnNode method : calls) {
            if (method == helper) continue;
            String id = call(method.getOpcode(), method.owner, method.name, method.desc);
            actual.put(id, actual.getOrDefault(id, 0) + 1);
        }
        if (!actual.equals(expected)) {
            throw new IllegalArgumentException("jce-call-set=" + actual.size()
                    + "/" + expected.size());
        }
    }

    /** Rejects incoming edges and handler/frame boundaries that would be cut. */
    private static void validateBoundary(ClassNode owner, MethodNode method,
                                         Code code, int start, int end) {
        Set<LabelNode> insideLabels = new java.util.HashSet<>();
        for (int i = start; i < end; i++) {
            AbstractInsnNode insn = code.nodes.get(i);
            if (insn instanceof LabelNode) insideLabels.add((LabelNode) insn);
            if (insn instanceof FrameNode) {
                // A frame inside the removed island is harmless; it is removed
                // transactionally with the island.  Frames at boundaries are
                // checked by the stack proof below.
            }
        }
        for (int i = 0; i < code.nodes.size(); i++) {
            AbstractInsnNode insn = code.nodes.get(i);
            if (insn instanceof JumpInsnNode) {
                JumpInsnNode jump = (JumpInsnNode) insn;
                int target = code.index(jump.label);
                if (target >= start && target < end && (i < start || i >= end)) {
                    throw new IllegalArgumentException("incoming-edge=" + i
                            + "->" + target);
                }
                if (i >= start && i < end && target >= end && target != end) {
                    throw new IllegalArgumentException("extra-exit-edge=" + i
                            + "->" + target);
                }
            } else if (insn instanceof TableSwitchInsnNode) {
                TableSwitchInsnNode sw = (TableSwitchInsnNode) insn;
                if (incomingSwitch(sw, code, start, end, i)
                        || outgoingSwitch(sw, code, start, end, i)) {
                    throw new IllegalArgumentException("switch-edge-crosses-slice=" + i);
                }
            } else if (insn instanceof LookupSwitchInsnNode) {
                LookupSwitchInsnNode sw = (LookupSwitchInsnNode) insn;
                if (incomingSwitch(sw, code, start, end, i)
                        || outgoingSwitch(sw, code, start, end, i)) {
                    throw new IllegalArgumentException("switch-edge-crosses-slice=" + i);
                }
            }
        }
        int coveringRanges = 0;
        for (org.objectweb.asm.tree.TryCatchBlockNode block : method.tryCatchBlocks) {
            int from = code.index(block.start);
            int to = code.index(block.end);
            int handler = code.index(block.handler);
            if (handler >= start && handler < end) {
                throw new IllegalArgumentException("exception-handler-inside-slice");
            }
            if (rangesOverlap(start, end, from, to)) {
                if (from > start || to < end) {
                    throw new IllegalArgumentException(
                            "exception-boundary-inside-slice=" + from + "-"
                                    + to + "/" + start + "-" + end);
                }
                coveringRanges++;
            }
        }
        if (coveringRanges > 1) {
            throw new IllegalArgumentException(
                    "multiple-covering-exception-ranges=" + coveringRanges);
        }
    }

    private static int coveringExceptionEnd(MethodNode method, Code code,
                                            int start, int fieldWrite,
                                            int normalExit) {
        int result = -1;
        for (org.objectweb.asm.tree.TryCatchBlockNode block
                : method.tryCatchBlocks) {
            int from = code.index(block.start);
            int to = code.index(block.end);
            int handler = code.index(block.handler);
            if (from <= start && to > fieldWrite && to <= normalExit
                    && (handler < start || handler >= to)) {
                if (result >= 0 && result != to) return -1;
                result = to;
            }
        }
        return result;
    }

    private static boolean incomingSwitch(TableSwitchInsnNode sw, Code code,
                                           int start, int end, int source) {
        if (incomingLabel(sw.dflt, code, start, end)) return source < start || source >= end;
        for (LabelNode label : sw.labels) {
            if (incomingLabel(label, code, start, end)) return source < start || source >= end;
        }
        return false;
    }

    private static boolean incomingSwitch(LookupSwitchInsnNode sw, Code code,
                                           int start, int end, int source) {
        if (incomingLabel(sw.dflt, code, start, end)) return source < start || source >= end;
        for (LabelNode label : sw.labels) {
            if (incomingLabel(label, code, start, end)) return source < start || source >= end;
        }
        return false;
    }

    private static boolean incomingLabel(LabelNode label, Code code,
                                         int start, int end) {
        int index = code.index(label);
        return index >= start && index < end;
    }

    private static boolean outgoingSwitch(TableSwitchInsnNode sw, Code code,
                                          int start, int end, int source) {
        if (source < start || source >= end) return false;
        if (outgoingLabel(sw.dflt, code, end)) return true;
        for (LabelNode label : sw.labels) if (outgoingLabel(label, code, end)) return true;
        return false;
    }

    private static boolean outgoingSwitch(LookupSwitchInsnNode sw, Code code,
                                          int start, int end, int source) {
        if (source < start || source >= end) return false;
        if (outgoingLabel(sw.dflt, code, end)) return true;
        for (LabelNode label : sw.labels) if (outgoingLabel(label, code, end)) return true;
        return false;
    }

    private static boolean outgoingLabel(LabelNode label, Code code, int end) {
        return code.index(label) > end;
    }

    private static boolean rangesOverlap(int a, int b, int c, int d) {
        return a < d && c < b;
    }

    private static void validateStackBoundary(ClassNode owner, MethodNode method,
                                              Code code, int start, int end)
            throws Exception {
        Analyzer<BasicValue> analyzer = new Analyzer<>(new BasicVerifier());
        Frame<BasicValue>[] frames;
        try {
            frames = analyzer.analyze(owner.name, method);
        } catch (Throwable failure) {
            throw new IllegalArgumentException("stack-analysis="
                    + shortReason(failure));
        }
        Frame<BasicValue> entry = frames[start];
        Frame<BasicValue> exit = end < frames.length ? frames[end] : null;
        if (entry == null || entry.getStackSize() != 0) {
            throw new IllegalArgumentException("nonempty-entry-stack");
        }
        if (exit != null && exit.getStackSize() != 0) {
            throw new IllegalArgumentException("nonempty-exit-stack="
                    + exit.getStackSize());
        }
    }

    private static void apply(ClassNode owner, Candidate candidate) {
        MethodNode clinit = method(owner, "<clinit>", "()V");
        if (clinit == null) throw new IllegalStateException("missing <clinit>");
        Slice slice;
        try {
            slice = locateSlice(owner, clinit);
        } catch (Exception failure) {
            throw new IllegalStateException("slice-disappeared:" + shortReason(failure));
        }
        if (!candidate.fieldName.equals(slice.field.name)
                || candidate.key != slice.key
                || !candidate.ciphertext.equals(slice.ciphertext)) {
            throw new IllegalStateException("slice-identity-changed");
        }
        AbstractInsnNode cursor = slice.start;
        while (cursor != slice.endExclusive) {
            AbstractInsnNode next = cursor.getNext();
            clinit.instructions.remove(cursor);
            cursor = next;
        }
        InsnList replacement = new InsnList();
        replacement.add(new LdcInsnNode(candidate.plaintext));
        replacement.add(new FieldInsnNode(Opcodes.PUTSTATIC, owner.name,
                candidate.fieldName, STRING_DESC));
        clinit.instructions.insertBefore(slice.endExclusive, replacement);
        if (candidate.removeHelper) {
            MethodNode helper = method(owner, candidate.helperName, DECODE_DESC);
            if (helper == null || !owner.methods.remove(helper)) {
                throw new IllegalStateException("decoder-disappeared-before-removal");
            }
        }
    }

    private static void assertRewritten(byte[] bytes, Candidate candidate) {
        ClassNode owner = readClass(bytes);
        MethodNode clinit = method(owner, "<clinit>", "()V");
        boolean plaintext = false;
        boolean target = false;
        boolean cipher = false;
        if (clinit != null) {
            for (AbstractInsnNode insn = clinit.instructions.getFirst(); insn != null;
                 insn = insn.getNext()) {
                if (insn instanceof LdcInsnNode
                        && candidate.plaintext.equals(((LdcInsnNode) insn).cst)) plaintext = true;
                if (insn instanceof FieldInsnNode && insn.getOpcode() == Opcodes.PUTSTATIC
                        && candidate.fieldName.equals(((FieldInsnNode) insn).name)) target = true;
                if (isCipherFactory(insn, ALGORITHM)) cipher = true;
            }
        }
        if (!plaintext || !target || cipher) {
            throw new IllegalStateException("rewrite-assertion-failed");
        }
        if (candidate.removeHelper && method(owner, candidate.helperName, DECODE_DESC) != null) {
            throw new IllegalStateException("decoder-retained");
        }
    }

    private static String decrypt(String ciphertext, long keyValue) throws Exception {
        return ZkmDesConstantEvaluator.decryptZkmString(
                ZkmDesConstantEvaluator.KeyMaterial.proven(keyValue,
                        "LDC_LONG", "mixed PKCS5 string fragment"), ciphertext);
    }

    private static boolean latin1Ciphertext(String value) {
        if (value == null || value.isEmpty()) return false;
        for (int i = 0; i < value.length(); i++) if (value.charAt(i) > 0xff) return false;
        return true;
    }

    private static boolean isCipherFactory(AbstractInsnNode insn, String algorithm) {
        if (!(insn instanceof MethodInsnNode)) return false;
        MethodInsnNode call = (MethodInsnNode) insn;
        return call.getOpcode() == Opcodes.INVOKESTATIC
                && "javax/crypto/Cipher".equals(call.owner)
                && "getInstance".equals(call.name)
                && "(Ljava/lang/String;)Ljavax/crypto/Cipher;".equals(call.desc)
                && previousCode(insn) instanceof LdcInsnNode
                && algorithm.equals(((LdcInsnNode) previousCode(insn)).cst);
    }

    private static AbstractInsnNode previousCode(AbstractInsnNode node) {
        AbstractInsnNode cursor = node == null ? null : node.getPrevious();
        while (cursor != null && cursor.getOpcode() < 0) cursor = cursor.getPrevious();
        return cursor;
    }

    private static AbstractInsnNode nextCode(AbstractInsnNode node) {
        AbstractInsnNode cursor = node == null ? null : node.getNext();
        while (cursor != null && cursor.getOpcode() < 0) cursor = cursor.getNext();
        return cursor;
    }

    private static Map<MethodRef, Integer> methodReferences(Map<String, ClassNode> classes) {
        Map<MethodRef, Integer> result = new HashMap<>();
        for (ClassNode owner : classes.values()) {
            for (MethodNode method : owner.methods) {
                for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
                     insn = insn.getNext()) {
                    if (insn instanceof MethodInsnNode) {
                        MethodInsnNode call = (MethodInsnNode) insn;
                        increment(result, new MethodRef(call.owner, call.name, call.desc));
                    } else if (insn instanceof InvokeDynamicInsnNode) {
                        InvokeDynamicInsnNode indy = (InvokeDynamicInsnNode) insn;
                        addHandle(result, indy.bsm);
                        for (Object arg : indy.bsmArgs) addConstant(result, arg);
                    } else if (insn instanceof LdcInsnNode) addConstant(result, ((LdcInsnNode) insn).cst);
                }
            }
        }
        return result;
    }

    private static void addConstant(Map<MethodRef, Integer> refs, Object value) {
        if (value instanceof Handle) addHandle(refs, (Handle) value);
        else if (value instanceof ConstantDynamic) {
            ConstantDynamic dynamic = (ConstantDynamic) value;
            addHandle(refs, dynamic.getBootstrapMethod());
            for (int i = 0; i < dynamic.getBootstrapMethodArgumentCount(); i++)
                addConstant(refs, dynamic.getBootstrapMethodArgument(i));
        }
    }

    private static void addHandle(Map<MethodRef, Integer> refs, Handle handle) {
        if (handle == null) return;
        int tag = handle.getTag();
        if (tag >= Opcodes.H_INVOKEVIRTUAL && tag <= Opcodes.H_INVOKEINTERFACE)
            increment(refs, new MethodRef(handle.getOwner(), handle.getName(), handle.getDesc()));
    }

    private static void increment(Map<MethodRef, Integer> refs, MethodRef ref) {
        refs.put(ref, refs.getOrDefault(ref, 0) + 1);
    }

    private static String call(int opcode, String owner, String name, String desc) {
        return opcode + ":" + owner + "." + name + desc;
    }

    private static MethodNode method(ClassNode owner, String name, String desc) {
        for (MethodNode method : owner.methods)
            if (name.equals(method.name) && desc.equals(method.desc)) return method;
        return null;
    }

    private static FieldNode field(ClassNode owner, String name, String desc) {
        for (FieldNode field : owner.fields)
            if (name.equals(field.name) && desc.equals(field.desc)) return field;
        return null;
    }

    private static byte[] writeClass(ClassNode owner) {
        ClassWriter writer = new ClassWriter(ClassWriter.COMPUTE_MAXS);
        owner.accept(writer);
        return writer.toByteArray();
    }

    private static void verifyClass(byte[] bytes) throws Exception {
        ClassReader reader = new ClassReader(bytes);
        reader.accept(new CheckClassAdapter(new ClassWriter(0), false), 0);
        ClassNode owner = readClass(bytes);
        for (MethodNode method : owner.methods)
            if (method.instructions != null && method.instructions.size() != 0)
                new Analyzer<>(new BasicVerifier()).analyze(owner.name, method);
    }

    private static void writeVerifiedArchive(List<EntryBytes> entries,
                                             Map<String, byte[]> replacements,
                                             Path output, Summary summary,
                                             List<String> verifier) throws IOException {
        Path parent = output.toAbsolutePath().getParent();
        if (parent == null) parent = Paths.get(".").toAbsolutePath();
        Files.createDirectories(parent);
        Path temporary = Files.createTempFile(parent, output.getFileName().toString() + ".", ".tmp");
        summary.temporaryOutput = temporary.toAbsolutePath().toString();
        try {
            writeArchive(entries, replacements, temporary);
            ArchiveVerification check = verifyArchive(temporary, verifier);
            summary.outputEntries = check.entries;
            summary.outputClasses = check.classes;
            summary.outputPkcs5ClinitClasses = check.pkcs5;
            summary.outputVerificationErrors += check.errors;
            if (check.errors != 0) throw new IOException("archive-verification-errors=" + check.errors);
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

    private static void writeArchive(List<EntryBytes> entries, Map<String, byte[]> replacements,
                                     Path output) throws IOException {
        try (ZipOutputStream out = new ZipOutputStream(Files.newOutputStream(output))) {
            for (EntryBytes entry : entries) {
                ZipEntry zip = new ZipEntry(entry.name);
                if (entry.time >= 0) zip.setTime(entry.time);
                if (entry.comment != null) zip.setComment(entry.comment);
                if (entry.extra != null) zip.setExtra(entry.extra);
                out.putNextEntry(zip);
                byte[] value = entry.name.endsWith(".class")
                        ? replacements.getOrDefault(new ClassReader(entry.bytes).getClassName(), entry.bytes)
                        : entry.bytes;
                out.write(value);
                out.closeEntry();
            }
        }
    }

    private static ArchiveVerification verifyArchive(Path archive, List<String> verifier)
            throws IOException {
        ArchiveVerification result = new ArchiveVerification();
        try (ZipInputStream in = new ZipInputStream(Files.newInputStream(archive))) {
            ZipEntry entry;
            while ((entry = in.getNextEntry()) != null) {
                result.entries++;
                byte[] bytes = readAll(in);
                if (!entry.getName().endsWith(".class")) continue;
                result.classes++;
                try {
                    ClassNode owner = readClass(bytes);
                    MethodNode clinit = method(owner, "<clinit>", "()V");
                    if (clinit != null)
                        for (AbstractInsnNode insn = clinit.instructions.getFirst(); insn != null;
                             insn = insn.getNext())
                            if (isCipherFactory(insn, ALGORITHM)) { result.pkcs5++; break; }
                    verifyClass(bytes);
                    verifier.add(tsv("archive-class", owner.name, "PASS", ""));
                } catch (Throwable failure) {
                    result.errors++;
                    verifier.add(tsv("archive-class", entry.getName(), "FAIL", shortReason(failure)));
                }
            }
        }
        return result;
    }

    private static List<EntryBytes> readEntries(Path input) throws IOException {
        List<EntryBytes> result = new ArrayList<>();
        try (ZipInputStream in = new ZipInputStream(Files.newInputStream(input))) {
            ZipEntry entry;
            while ((entry = in.getNextEntry()) != null)
                result.add(new EntryBytes(entry, readAll(in)));
        }
        return result;
    }

    private static byte[] readAll(java.io.InputStream in) throws IOException {
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        byte[] buffer = new byte[8192];
        int count;
        while ((count = in.read(buffer)) >= 0) if (count != 0) out.write(buffer, 0, count);
        return out.toByteArray();
    }

    private static Map<String, byte[]> classBytes(List<EntryBytes> entries) {
        Map<String, byte[]> result = new LinkedHashMap<>();
        for (EntryBytes entry : entries) if (entry.name.endsWith(".class")) {
            ClassReader reader = new ClassReader(entry.bytes);
            result.put(reader.getClassName(), entry.bytes);
        }
        return result;
    }

    private static Map<String, ClassNode> readClasses(Map<String, byte[]> bytes) {
        Map<String, ClassNode> result = new LinkedHashMap<>();
        for (Map.Entry<String, byte[]> entry : bytes.entrySet()) result.put(entry.getKey(), readClass(entry.getValue()));
        return result;
    }

    private static ClassNode readClass(byte[] bytes) {
        ClassNode owner = new ClassNode(Opcodes.ASM9);
        new ClassReader(bytes).accept(owner, 0);
        return owner;
    }

    private static String appendReason(String old, String next) {
        return old == null || old.isEmpty() ? next : old + ";" + next;
    }

    private static String shortReason(Throwable failure) {
        String message = failure.getMessage();
        if (message == null || message.isEmpty()) return failure.getClass().getSimpleName();
        return failure.getClass().getSimpleName() + ":" + message.replace('\n', ' ');
    }

    private static String tsv(Object... values) {
        StringBuilder result = new StringBuilder();
        for (int i = 0; i < values.length; i++) {
            if (i != 0) result.append('\t');
            result.append(values[i] == null ? "" : String.valueOf(values[i]).replace('\t', ' '));
        }
        return result.toString();
    }

    private static String value(Object value) {
        return value == null ? "" : String.valueOf(value).replace('\t', ' ').replace('\n', ' ');
    }

    private static String gate(Summary summary) {
        return summary.outputRequested
                ? (summary.outputCommitted && summary.outputVerificationErrors == 0 ? "PASS" : "FAIL")
                : (summary.classRollbacks == 0 ? "PASS" : "FAIL");
    }

    private static void writeReports(Path input, Path report, Path output,
                                     Summary summary, List<Candidate> candidates,
                                     List<String> verifier) throws IOException {
        List<String> rows = new ArrayList<>();
        rows.add("class\tclinit_nodes\tpkcs5_calls\tfield\tkey_hex\tciphertext_length"
                + "\tplaintext\thelper\thelper_references\tremove_helper\taction\treason");
        for (Candidate candidate : candidates) rows.add(candidate.row());
        Files.write(report.resolve("candidates.tsv"), rows, StandardCharsets.UTF_8);
        Files.write(report.resolve("verifier.tsv"), verifier, StandardCharsets.UTF_8);
        List<String> helpers = new ArrayList<>();
        helpers.add("class\thelper\treferences\taction");
        for (Candidate candidate : candidates)
            if (candidate.removeHelper)
                helpers.add(tsv(candidate.owner, candidate.helperName,
                        candidate.helperReferences, candidate.action));
        Files.write(report.resolve("removed-helpers.tsv"), helpers, StandardCharsets.UTF_8);
        List<String> audit = new ArrayList<>();
        audit.add("input=" + input.toAbsolutePath());
        audit.add("input_sha256=" + sha256(input));
        audit.add("parsed_classes=" + summary.parsedClasses);
        audit.add("pkcs5_clinit_classes=" + summary.pkcs5ClinitClasses);
        audit.add("proven_fragment_candidates=" + summary.provenCandidates);
        audit.add("rejected_pkcs5_clinit_classes=" + summary.rejectedCandidates);
        audit.add("changed_classes=" + summary.changedClasses);
        audit.add("rewritten_fields=" + summary.rewrittenFields);
        audit.add("helpers_removed=" + summary.helpersRemoved);
        audit.add("class_rollbacks=" + summary.classRollbacks);
        audit.add("output_requested=" + summary.outputRequested);
        if (output != null) audit.add("output=" + output.toAbsolutePath());
        audit.add("output_entries=" + summary.outputEntries);
        audit.add("output_classes=" + summary.outputClasses);
        audit.add("output_remaining_pkcs5_clinit_classes=" + summary.outputPkcs5ClinitClasses);
        audit.add("output_verification_errors=" + summary.outputVerificationErrors);
        audit.add("input_classes_loaded=false");
        audit.add("input_classes_initialized=false");
        audit.add("slice_policy=unique closed DES/CBC/PKCS5Padding island; preserve mixed initializer order and complete enclosing exception range");
        audit.add("gate=" + gate(summary));
        Files.write(report.resolve("audit.txt"), audit, StandardCharsets.UTF_8);
        Files.write(report.resolve("gate.txt"), java.util.Collections.singletonList(gate(summary)), StandardCharsets.UTF_8);
    }

    private static String sha256(Path path) throws IOException {
        try {
            MessageDigest digest = MessageDigest.getInstance("SHA-256");
            try (java.io.InputStream input = Files.newInputStream(path)) {
                byte[] buffer = new byte[8192];
                int count;
                while ((count = input.read(buffer)) >= 0) if (count != 0) digest.update(buffer, 0, count);
            }
            StringBuilder result = new StringBuilder();
            for (byte value : digest.digest()) result.append(String.format(Locale.ROOT, "%02X", value));
            return result.toString();
        } catch (java.security.NoSuchAlgorithmException impossible) {
            throw new IOException(impossible);
        }
    }

    private static void validatePaths(Path input, Path output) {
        if (output != null && input.toAbsolutePath().normalize().equals(output.toAbsolutePath().normalize()))
            throw new IllegalArgumentException("output must not replace input");
    }

    public static final class Summary {
        int parsedClasses;
        int pkcs5ClinitClasses;
        int provenCandidates;
        int rejectedCandidates;
        int provenStrings;
        int changedClasses;
        int rewrittenFields;
        int helpersRemoved;
        int classRollbacks;
        boolean outputRequested;
        String temporaryOutput;
        int outputEntries;
        int outputClasses;
        int outputPkcs5ClinitClasses;
        int outputVerificationErrors;
        boolean outputCommitted;

        public int getParsedClasses() { return parsedClasses; }
        public int getPkcs5ClinitClasses() { return pkcs5ClinitClasses; }
        public int getProvenCandidates() { return provenCandidates; }
        public int getChangedClasses() { return changedClasses; }
        public int getHelpersRemoved() { return helpersRemoved; }
        public int getClassRollbacks() { return classRollbacks; }
        public int getOutputVerificationErrors() { return outputVerificationErrors; }
        public boolean isOutputCommitted() { return outputCommitted; }
    }

    private static final class Candidate {
        final String owner;
        final int clinitNodes;
        int pkcs5Calls;
        String fieldName;
        long key;
        String ciphertext;
        String plaintext;
        String helperName;
        int helperReferences;
        boolean removeHelper;
        Slice slice;
        String action = "REJECT";
        String reason = "";

        Candidate(String owner, int clinitNodes) {
            this.owner = owner;
            this.clinitNodes = clinitNodes;
        }

        Candidate reject(String reason) {
            this.reason = reason;
            this.action = "REJECT";
            return this;
        }

        boolean proven() { return "PROVEN".equals(action); }

        String row() {
            return tsv(owner, clinitNodes, pkcs5Calls, value(fieldName),
                    fieldName == null ? "" : String.format(Locale.ROOT, "%016X", key),
                    ciphertext == null ? "" : ciphertext.length(), value(plaintext),
                    value(helperName), helperReferences, removeHelper, action, reason);
        }
    }

    private static final class Slice {
        final AbstractInsnNode start;
        final AbstractInsnNode endExclusive;
        final FieldInsnNode field;
        final MethodNode helper;
        final long key;
        final String ciphertext;
        final String plaintext;

        Slice(AbstractInsnNode start, AbstractInsnNode endExclusive,
              FieldInsnNode field, MethodNode helper, long key,
              String ciphertext, String plaintext) {
            this.start = start;
            this.endExclusive = endExclusive;
            this.field = field;
            this.helper = helper;
            this.key = key;
            this.ciphertext = ciphertext;
            this.plaintext = plaintext;
        }
    }

    private static final class Code {
        final List<AbstractInsnNode> nodes = new ArrayList<>();
        final Map<AbstractInsnNode, Integer> indices = new HashMap<>();

        Code(MethodNode method) {
            int index = 0;
            for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
                 insn = insn.getNext()) {
                nodes.add(insn);
                indices.put(insn, index++);
            }
        }

        int index(AbstractInsnNode insn) {
            Integer index = indices.get(insn);
            if (index == null) throw new IllegalArgumentException("foreign-instruction");
            return index;
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

        @Override public boolean equals(Object value) {
            if (!(value instanceof MethodRef)) return false;
            MethodRef other = (MethodRef) value;
            return owner.equals(other.owner) && name.equals(other.name) && desc.equals(other.desc);
        }

        @Override public int hashCode() {
            int result = owner.hashCode();
            result = 31 * result + name.hashCode();
            return 31 * result + desc.hashCode();
        }
    }

    private static final class ArchiveVerification {
        int entries;
        int classes;
        int pkcs5;
        int errors;
    }

    private static final class EntryBytes {
        final String name;
        final byte[] bytes;
        final long time;
        final String comment;
        final byte[] extra;

        EntryBytes(ZipEntry entry, byte[] bytes) {
            this.name = entry.getName();
            this.bytes = bytes;
            this.time = entry.getTime();
            this.comment = entry.getComment();
            this.extra = entry.getExtra();
        }
    }
}
