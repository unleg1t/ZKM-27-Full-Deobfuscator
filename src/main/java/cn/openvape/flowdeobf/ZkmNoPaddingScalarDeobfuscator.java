package cn.openvape.flowdeobf;

import org.objectweb.asm.ClassReader;
import org.objectweb.asm.ClassWriter;
import org.objectweb.asm.Opcodes;
import org.objectweb.asm.tree.AbstractInsnNode;
import org.objectweb.asm.tree.ClassNode;
import org.objectweb.asm.tree.FieldInsnNode;
import org.objectweb.asm.tree.FieldNode;
import org.objectweb.asm.tree.InsnList;
import org.objectweb.asm.tree.InsnNode;
import org.objectweb.asm.tree.LdcInsnNode;
import org.objectweb.asm.tree.LabelNode;
import org.objectweb.asm.tree.MethodInsnNode;
import org.objectweb.asm.tree.MethodNode;
import org.objectweb.asm.tree.TypeInsnNode;
import org.objectweb.asm.tree.JumpInsnNode;
import org.objectweb.asm.tree.IntInsnNode;
import org.objectweb.asm.util.CheckClassAdapter;
import org.objectweb.asm.tree.analysis.Analyzer;
import org.objectweb.asm.tree.analysis.BasicVerifier;

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
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.zip.CRC32;
import java.util.zip.ZipEntry;
import java.util.zip.ZipInputStream;
import java.util.zip.ZipOutputStream;

/**
 * Folds the strict scalar ZKM DES/CBC/NoPadding initializer.
 *
 * <p>The accepted template has one DES call, one byte key assembled from a
 * literal long, one eight-byte ciphertext assembled from a second literal
 * long, and one owner-local static-final long write.  Any
 * {@code ZkmLongKeyState} call, array table, exception range, second crypto
 * call, or unknown method in the crypto region rejects the class.  Prefix
 * instructions before the first Cipher factory are retained verbatim, so a
 * proven non-crypto static side effect is not silently dropped.  The sample
 * class is never loaded or initialized.</p>
 */
public final class ZkmNoPaddingScalarDeobfuscator {
    private static final String ALGORITHM = "DES/CBC/NoPadding";
    private static final String STATE = ObfRuntimeNames.STATE;
    private static final String STATE_IFACE = ObfRuntimeNames.STATE_INTERFACE;

    private ZkmNoPaddingScalarDeobfuscator() {
    }

    public static void main(String[] args) throws Exception {
        if (args.length < 2 || args.length > 3) {
            System.err.println("usage: ZkmNoPaddingScalarDeobfuscator <input.jar> <report-dir> [output.jar]");
            System.exit(2);
        }
        rewrite(Paths.get(args[0]), Paths.get(args[1]),
                args.length == 3 ? Paths.get(args[2]) : null);
    }

    static Summary rewrite(Path input, Path reportDirectory, Path output) throws Exception {
        if (output != null && input.toAbsolutePath().normalize().equals(output.toAbsolutePath().normalize())) {
            throw new IllegalArgumentException("output must not replace input");
        }
        Files.createDirectories(reportDirectory);
        List<Entry> entries = readEntries(input);
        Map<String, byte[]> classBytes = classBytes(entries);
        List<Candidate> candidates = new ArrayList<>();
        Map<String, byte[]> replacements = new LinkedHashMap<>();
        Summary summary = new Summary();
        summary.parsedClasses = classBytes.size();
        for (Map.Entry<String, byte[]> item : classBytes.entrySet()) {
            ClassNode owner = readClass(item.getValue());
            Candidate candidate = inspect(owner);
            if (candidate == null) continue;
            candidates.add(candidate);
            summary.candidates++;
            if (!candidate.proven) {
                summary.rejected++;
                continue;
            }
            summary.proven++;
            if (output == null) {
                candidate.action = "PROVEN_DRY_RUN";
                continue;
            }
            try {
                ClassNode rewritten = readClass(item.getValue());
                apply(rewritten, candidate);
                byte[] bytes = writeClass(rewritten);
                verifyClass(bytes);
                replacements.put(rewritten.name, bytes);
                candidate.action = "REWRITE";
                summary.changedClasses++;
            } catch (Throwable failure) {
                candidate.action = "ROLLBACK";
                candidate.reason = candidate.reason + ";class-rollback=" + shortReason(failure);
                summary.rollbacks++;
            }
        }
        if (output != null) {
            writeVerifiedArchive(entries, replacements, output, summary);
        }
        writeReports(input, output, reportDirectory, summary, candidates);
        System.out.println("classes=" + summary.parsedClasses + " candidates=" + summary.candidates
                + " proven=" + summary.proven + " rewritten=" + summary.changedClasses
                + " rejected=" + summary.rejected + " rollbacks=" + summary.rollbacks
                + " output_committed=" + summary.outputCommitted);
        return summary;
    }

    private static Candidate inspect(ClassNode owner) {
        MethodNode clinit = method(owner, "<clinit>", "()V");
        if (clinit == null) return null;
        boolean hasNoPadding = false;
        for (AbstractInsnNode insn = clinit.instructions.getFirst(); insn != null; insn = insn.getNext()) {
            if (isCipherFactory(insn)) {
                hasNoPadding = true;
                break;
            }
        }
        if (!hasNoPadding) return null;
        Candidate candidate = new Candidate(owner.name);
        candidate.instructions = clinit.instructions.size();
        if (clinit.tryCatchBlocks != null && !clinit.tryCatchBlocks.isEmpty()) {
            return candidate.reject("exception-ranges");
        }
        AbstractInsnNode firstCipher = null;
        int cipherCalls = 0;
        int doFinalCalls = 0;
        int factoryCalls = 0;
        int keySpecCalls = 0;
        int ivCalls = 0;
        int initCalls = 0;
        int stateCalls = 0;
        int stateResolveCalls = 0;
        int ownerWrites = 0;
        FieldInsnNode write = null;
        Set<Long> nonMaskConstants = new LinkedHashSet<>();
        Map<String, Integer> allowedCallCounts = new LinkedHashMap<>();
        int firstCipherIndex = -1;
        int index = 0;
        for (AbstractInsnNode insn = clinit.instructions.getFirst(); insn != null; insn = insn.getNext(), index++) {
            if (isCipherFactory(insn)) {
                if (firstCipher == null) {
                    firstCipher = insn;
                    firstCipherIndex = index;
                }
                cipherCalls++;
            }
            if (insn instanceof LdcInsnNode && ((LdcInsnNode) insn).cst instanceof Long) {
                long value = (Long) ((LdcInsnNode) insn).cst;
                if (value != 255L) nonMaskConstants.add(value);
            }
            if (insn instanceof FieldInsnNode && insn.getOpcode() == Opcodes.PUTSTATIC) {
                FieldInsnNode field = (FieldInsnNode) insn;
                if (owner.name.equals(field.owner)) {
                    ownerWrites++;
                    write = field;
                }
            }
            if (!(insn instanceof MethodInsnNode)) continue;
            MethodInsnNode call = (MethodInsnNode) insn;
            if (STATE.equals(call.owner)) stateCalls++;
            if (STATE_IFACE.equals(call.owner) && "a".equals(call.name)
                    && "(J)J".equals(call.desc)) stateResolveCalls++;
            if ("javax/crypto/Cipher".equals(call.owner) && "doFinal".equals(call.name)) doFinalCalls++;
            if ("javax/crypto/SecretKeyFactory".equals(call.owner)
                    && "getInstance".equals(call.name)) factoryCalls++;
            if ("javax/crypto/spec/DESKeySpec".equals(call.owner)
                    && "<init>".equals(call.name)) keySpecCalls++;
            if ("javax/crypto/spec/IvParameterSpec".equals(call.owner)
                    && "<init>".equals(call.name)) ivCalls++;
            if ("javax/crypto/Cipher".equals(call.owner) && "init".equals(call.name)) initCalls++;
            String callKey = call.getOpcode() + ":" + call.owner + "." + call.name + call.desc;
            allowedCallCounts.merge(callKey, 1, Integer::sum);
        }
        candidate.noPaddingCalls = cipherCalls;
        candidate.stateCalls = stateCalls;
        candidate.prefixInstructions = firstCipherIndex;
        if (cipherCalls != 1) return candidate.reject("cipher-calls=" + cipherCalls);
        if (doFinalCalls != 1 || factoryCalls != 1 || keySpecCalls != 1
                || ivCalls != 1 || initCalls != 1) {
            return candidate.reject("crypto-call-shape=doFinal:" + doFinalCalls
                    + ",factory:" + factoryCalls + ",keySpec:" + keySpecCalls
                    + ",iv:" + ivCalls + ",init:" + initCalls);
        }
        if (stateCalls != 0 || stateResolveCalls != 0) {
            return candidate.reject("state-bootstrap-present");
        }
        if (ownerWrites != 1 || write == null || !"J".equals(write.desc)) {
            return candidate.reject("owner-long-write=" + ownerWrites + "/"
                    + (write == null ? "" : write.desc));
        }
        FieldNode field = field(owner, write.name, write.desc);
        if (field == null || (field.access & (Opcodes.ACC_STATIC | Opcodes.ACC_FINAL))
                != (Opcodes.ACC_STATIC | Opcodes.ACC_FINAL)) {
            return candidate.reject("target-not-static-final-long=" + write.name);
        }
        candidate.fieldName = write.name;
        if (nonMaskConstants.size() != 2) {
            return candidate.reject("non-mask-long-constants=" + nonMaskConstants.size());
        }
        if (firstCipher == null || !prefixHasNoJumps(clinit, firstCipher)) {
            return candidate.reject("prefix-control-flow");
        }
        String unsupported = unsupportedCryptoRegion(clinit, firstCipher);
        if (unsupported != null) return candidate.reject(unsupported);
        LongPair pair = extractKeyAndCiphertext(clinit, firstCipher);
        if (pair == null) return candidate.reject("key-ciphertext-constants");
        try {
            candidate.key = pair.key;
            candidate.ciphertext = pair.ciphertext;
            candidate.plaintext = decrypt(pair.key, pair.ciphertext);
        } catch (Throwable failure) {
            return candidate.reject("decrypt=" + shortReason(failure));
        }
        candidate.proven = true;
        candidate.reason = "strict-single-scalar-template;prefix-preserved";
        return candidate;
    }

    private static String unsupportedCryptoRegion(MethodNode clinit, AbstractInsnNode firstCipher) {
        boolean inRegion = false;
        for (AbstractInsnNode insn = clinit.instructions.getFirst(); insn != null; insn = insn.getNext()) {
            if (insn == firstCipher) inRegion = true;
            if (!inRegion || insn.getOpcode() < 0) continue;
            if (insn instanceof JumpInsnNode || insn instanceof LabelNode) {
                // The generated crypto block has its own fake loop. It is removed as
                // a whole, so only reject jumps before the factory (handled separately).
                continue;
            }
            if (!(insn instanceof MethodInsnNode)) continue;
            MethodInsnNode call = (MethodInsnNode) insn;
            if (isCipherFactory(insn)
                    || ("javax/crypto/Cipher".equals(call.owner)
                    && ("init".equals(call.name) || "doFinal".equals(call.name)))
                    || ("javax/crypto/SecretKeyFactory".equals(call.owner)
                    && ("getInstance".equals(call.name) || "generateSecret".equals(call.name)))
                    || ("javax/crypto/spec/DESKeySpec".equals(call.owner)
                    && "<init>".equals(call.name))
                    || ("javax/crypto/spec/IvParameterSpec".equals(call.owner)
                    && "<init>".equals(call.name))) {
                continue;
            }
            return "unknown-crypto-call=" + call.owner + "." + call.name + call.desc;
        }
        return null;
    }

    private static boolean prefixHasNoJumps(MethodNode method, AbstractInsnNode firstCipher) {
        for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null && insn != firstCipher;
             insn = insn.getNext()) {
            if (insn instanceof JumpInsnNode || insn instanceof LabelNode) return false;
        }
        return true;
    }

    private static LongPair extractKeyAndCiphertext(MethodNode clinit, AbstractInsnNode firstCipher) {
        List<LongAt> values = new ArrayList<>();
        int index = 0;
        int initIndex = -1;
        for (AbstractInsnNode insn = clinit.instructions.getFirst(); insn != null; insn = insn.getNext(), index++) {
            if (insn instanceof LdcInsnNode && ((LdcInsnNode) insn).cst instanceof Long) {
                long value = (Long) ((LdcInsnNode) insn).cst;
                if (value != 255L) values.add(new LongAt(index, value));
            }
            if (insn instanceof MethodInsnNode) {
                MethodInsnNode call = (MethodInsnNode) insn;
                if ("javax/crypto/Cipher".equals(call.owner) && "init".equals(call.name)) {
                    initIndex = index;
                }
            }
        }
        if (initIndex < 0 || values.isEmpty()) return null;
        LinkedHashSet<Long> before = new LinkedHashSet<>();
        LinkedHashSet<Long> after = new LinkedHashSet<>();
        for (LongAt value : values) {
            if (value.index < initIndex) before.add(value.value);
            if (value.index > initIndex) after.add(value.value);
        }
        if (before.size() != 1 || after.size() != 1 || before.equals(after)) return null;
        return new LongPair(before.iterator().next(), after.iterator().next());
    }

    private static long decrypt(long key, long ciphertext) throws Exception {
        ZkmDesConstantEvaluator.KeyMaterial material =
                ZkmDesConstantEvaluator.KeyMaterial.proven(key,
                        "LDC_LONG", "strict NoPadding scalar template");
        return ZkmDesConstantEvaluator.decryptLong(material, ciphertext);
    }

    private static void apply(ClassNode owner, Candidate candidate) {
        MethodNode clinit = method(owner, "<clinit>", "()V");
        AbstractInsnNode firstCipher = null;
        FieldInsnNode write = null;
        for (AbstractInsnNode insn = clinit.instructions.getFirst(); insn != null; insn = insn.getNext()) {
            if (firstCipher == null && isCipherFactory(insn)) firstCipher = insn;
            if (insn instanceof FieldInsnNode && insn.getOpcode() == Opcodes.PUTSTATIC) {
                FieldInsnNode field = (FieldInsnNode) insn;
                if (owner.name.equals(field.owner) && candidate.fieldName.equals(field.name)
                        && "J".equals(field.desc)) write = field;
            }
        }
        if (firstCipher == null || write == null) throw new IllegalStateException("apply-shape-lost");
        InsnList replacement = new InsnList();
        replacement.add(new LdcInsnNode(candidate.plaintext));
        replacement.add(new FieldInsnNode(Opcodes.PUTSTATIC, owner.name, candidate.fieldName, "J"));
        replacement.add(new InsnNode(Opcodes.RETURN));
        // The algorithm literal is part of the crypto template too.  Removing
        // only the factory call would leave a misleading DES residue in CFR.
        AbstractInsnNode cursor = previousCode(firstCipher);
        if (!(cursor instanceof LdcInsnNode) || !ALGORITHM.equals(((LdcInsnNode) cursor).cst)) {
            throw new IllegalStateException("apply-algorithm-literal-lost");
        }
        while (cursor != null) {
            AbstractInsnNode next = cursor.getNext();
            clinit.instructions.remove(cursor);
            cursor = next;
        }
        clinit.instructions.add(replacement);
        clinit.tryCatchBlocks.clear();
        candidate.applied = true;
    }

    private static boolean isCipherFactory(AbstractInsnNode insn) {
        if (!(insn instanceof MethodInsnNode)) return false;
        MethodInsnNode call = (MethodInsnNode) insn;
        if (call.getOpcode() != Opcodes.INVOKESTATIC
                || !"javax/crypto/Cipher".equals(call.owner)
                || !"getInstance".equals(call.name)
                || !"(Ljava/lang/String;)Ljavax/crypto/Cipher;".equals(call.desc)) return false;
        AbstractInsnNode previous = previousCode(insn);
        return previous instanceof LdcInsnNode && ALGORITHM.equals(((LdcInsnNode) previous).cst);
    }

    private static ClassNode readClass(byte[] bytes) {
        ClassNode owner = new ClassNode(Opcodes.ASM9);
        new ClassReader(bytes).accept(owner, 0);
        return owner;
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
        for (MethodNode method : owner.methods) {
            if (method.instructions != null && method.instructions.size() != 0) {
                new Analyzer<>(new BasicVerifier()).analyze(owner.name, method);
            }
        }
    }

    private static List<Entry> readEntries(Path input) throws IOException {
        List<Entry> result = new ArrayList<>();
        try (ZipInputStream zip = new ZipInputStream(Files.newInputStream(input))) {
            ZipEntry entry;
            while ((entry = zip.getNextEntry()) != null) {
                result.add(new Entry(entry, readAll(zip)));
            }
        }
        return result;
    }

    private static Map<String, byte[]> classBytes(List<Entry> entries) {
        Map<String, byte[]> result = new LinkedHashMap<>();
        for (Entry entry : entries) {
            if (!entry.name.endsWith(".class")) continue;
            ClassReader reader = new ClassReader(entry.bytes);
            result.put(reader.getClassName(), entry.bytes);
        }
        return result;
    }

    private static void writeVerifiedArchive(List<Entry> entries, Map<String, byte[]> replacements,
                                             Path output, Summary summary) throws IOException {
        Path parent = output.toAbsolutePath().getParent();
        if (parent == null) parent = Paths.get(".").toAbsolutePath();
        Files.createDirectories(parent);
        Path temporary = Files.createTempFile(parent, output.getFileName().toString() + ".", ".tmp");
        try {
            Set<String> applied = new LinkedHashSet<>();
            try (ZipOutputStream zip = new ZipOutputStream(Files.newOutputStream(temporary))) {
                for (Entry entry : entries) {
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
                    } else {
                        written.setMethod(ZipEntry.DEFLATED);
                    }
                    zip.putNextEntry(written);
                    zip.write(bytes);
                    zip.closeEntry();
                }
            }
            if (!applied.equals(replacements.keySet())) {
                throw new IOException("replacement-coverage=" + applied.size() + "/" + replacements.size());
            }
            verifyArchive(temporary, summary);
            if (summary.outputVerificationErrors != 0) return;
            try {
                Files.move(temporary, output, StandardCopyOption.ATOMIC_MOVE, StandardCopyOption.REPLACE_EXISTING);
            } catch (AtomicMoveNotSupportedException unsupported) {
                Files.move(temporary, output, StandardCopyOption.REPLACE_EXISTING);
            }
            summary.outputCommitted = true;
        } finally {
            Files.deleteIfExists(temporary);
        }
    }

    private static void verifyArchive(Path archive, Summary summary) throws IOException {
        try (ZipInputStream zip = new ZipInputStream(Files.newInputStream(archive))) {
            ZipEntry entry;
            while ((entry = zip.getNextEntry()) != null) {
                byte[] bytes = readAll(zip);
                if (!entry.getName().endsWith(".class")) continue;
                summary.outputClasses++;
                try {
                    verifyClass(bytes);
                    ClassNode owner = readClass(bytes);
                    MethodNode clinit = method(owner, "<clinit>", "()V");
                    if (clinit != null) {
                        for (AbstractInsnNode insn = clinit.instructions.getFirst(); insn != null; insn = insn.getNext()) {
                            if (isCipherFactory(insn)) {
                                summary.outputResidualNoPadding++;
                                break;
                            }
                        }
                    }
                } catch (Throwable failure) {
                    summary.outputVerificationErrors++;
                }
            }
        }
    }

    private static void writeReports(Path input, Path output, Path reportDirectory,
                                     Summary summary, List<Candidate> candidates) throws IOException {
        List<String> lines = new ArrayList<>();
        lines.add("class\tinstructions\tprefix\tfield\tkey_hex\tciphertext_hex\tplaintext_hex\tstate_calls\tno_padding_calls\taction\tproven\treason");
        for (Candidate candidate : candidates) lines.add(candidate.row());
        Files.write(reportDirectory.resolve("candidates.tsv"), lines, StandardCharsets.UTF_8);
        List<String> audit = new ArrayList<>();
        audit.add("input=" + input.toAbsolutePath().normalize());
        audit.add("input_sha256=" + sha256(Files.readAllBytes(input)));
        audit.add("output=" + (output == null ? "" : output.toAbsolutePath().normalize()));
        audit.add("parsed_classes=" + summary.parsedClasses);
        audit.add("candidates=" + summary.candidates);
        audit.add("proven=" + summary.proven);
        audit.add("rejected=" + summary.rejected);
        audit.add("changed_classes=" + summary.changedClasses);
        audit.add("rollbacks=" + summary.rollbacks);
        audit.add("output_classes=" + summary.outputClasses);
        audit.add("output_residual_nopadding=" + summary.outputResidualNoPadding);
        audit.add("output_verification_errors=" + summary.outputVerificationErrors);
        audit.add("output_committed=" + summary.outputCommitted);
        audit.add("policy=only strict no-state scalar template; prefix instructions retained; arrays/state/mixed blocks rejected");
        Files.write(reportDirectory.resolve("audit.txt"), audit, StandardCharsets.UTF_8);
    }

    private static String sha256(byte[] bytes) throws IOException {
        try {
            MessageDigest digest = MessageDigest.getInstance("SHA-256");
            StringBuilder result = new StringBuilder();
            for (byte value : digest.digest(bytes)) result.append(String.format("%02X", value));
            return result.toString();
        } catch (Exception failure) {
            throw new IOException(failure);
        }
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

    private static AbstractInsnNode previousCode(AbstractInsnNode insn) {
        AbstractInsnNode cursor = insn == null ? null : insn.getPrevious();
        while (cursor != null && cursor.getOpcode() < 0) cursor = cursor.getPrevious();
        return cursor;
    }

    private static byte[] readAll(ZipInputStream zip) throws IOException {
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        byte[] buffer = new byte[8192];
        int read;
        while ((read = zip.read(buffer)) >= 0) if (read != 0) out.write(buffer, 0, read);
        return out.toByteArray();
    }

    private static String shortReason(Throwable failure) {
        String message = failure.getMessage();
        return failure.getClass().getSimpleName() + (message == null ? "" : ":" + message);
    }

    static final class Summary {
        int parsedClasses;
        int candidates;
        int proven;
        int rejected;
        int changedClasses;
        int rollbacks;
        int outputClasses;
        int outputResidualNoPadding;
        int outputVerificationErrors;
        boolean outputCommitted;
    }

    private static final class Candidate {
        final String owner;
        int instructions;
        int prefixInstructions;
        int noPaddingCalls;
        int stateCalls;
        String fieldName;
        long key;
        long ciphertext;
        long plaintext;
        boolean proven;
        boolean applied;
        String action = "REJECT";
        String reason = "";

        Candidate(String owner) {
            this.owner = owner;
        }

        Candidate reject(String reason) {
            this.reason = reason;
            return this;
        }

        String row() {
            return String.join("\t", owner, Integer.toString(instructions), Integer.toString(prefixInstructions),
                    fieldName == null ? "" : fieldName, hex(key), hex(ciphertext), hex(plaintext),
                    Integer.toString(stateCalls), Integer.toString(noPaddingCalls), action,
                    Boolean.toString(proven), reason);
        }
    }

    private static final class LongAt {
        final int index;
        final long value;

        LongAt(int index, long value) {
            this.index = index;
            this.value = value;
        }
    }

    private static final class LongPair {
        final long key;
        final long ciphertext;

        LongPair(long key, long ciphertext) {
            this.key = key;
            this.ciphertext = ciphertext;
        }
    }

    private static final class Entry {
        final String name;
        final byte[] bytes;
        final int method;
        final long time;
        final String comment;
        final byte[] extra;

        Entry(ZipEntry entry, byte[] bytes) {
            this.name = entry.getName();
            this.bytes = bytes;
            this.method = entry.getMethod();
            this.time = entry.getTime();
            this.comment = entry.getComment();
            this.extra = entry.getExtra();
        }
    }

    private static String hex(long value) {
        return String.format("%016X", value);
    }
}
