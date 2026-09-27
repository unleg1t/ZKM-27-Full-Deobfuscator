package cn.openvape.flowdeobf;

import org.objectweb.asm.ClassReader;
import org.objectweb.asm.ClassWriter;
import org.objectweb.asm.ConstantDynamic;
import org.objectweb.asm.Handle;
import org.objectweb.asm.Opcodes;
import org.objectweb.asm.Type;
import org.objectweb.asm.tree.AbstractInsnNode;
import org.objectweb.asm.tree.ClassNode;
import org.objectweb.asm.tree.FieldInsnNode;
import org.objectweb.asm.tree.FieldNode;
import org.objectweb.asm.tree.InsnNode;
import org.objectweb.asm.tree.IntInsnNode;
import org.objectweb.asm.tree.InvokeDynamicInsnNode;
import org.objectweb.asm.tree.LdcInsnNode;
import org.objectweb.asm.tree.MethodInsnNode;
import org.objectweb.asm.tree.MethodNode;
import org.objectweb.asm.tree.MultiANewArrayInsnNode;
import org.objectweb.asm.tree.TypeInsnNode;
import org.objectweb.asm.util.CheckClassAdapter;
import org.objectweb.asm.tree.analysis.Analyzer;
import org.objectweb.asm.tree.analysis.BasicVerifier;

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
import java.util.ArrayList;
import java.util.Collections;
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
 * Folds the closed, single-field ZKM DES static-string initializer template.
 *
 * <p>The input archive is parsed with ASM and is never defined or initialized.
 * This first-stage pass intentionally excludes local String-array/enum tables,
 * NoPadding integer tables, mixed business initializers, and any initializer
 * with a dynamic input. A candidate class is committed only after structural
 * and bytecode verification; the optional output archive is verified again
 * before it is atomically published.</p>
 */
public final class ZkmDirectStringConstantDeobfuscator {
    private static final String ALGORITHM = "DES/CBC/PKCS5Padding";
    private static final String KEY_ALGORITHM = "DES";
    private static final String LATIN1 = "ISO-8859-1";
    private static final String STRING_DESC = "Ljava/lang/String;";
    private static final String DECODE_DESC = "([B)Ljava/lang/String;";

    private ZkmDirectStringConstantDeobfuscator() {
    }

    public static void main(String[] args) throws Exception {
        if (args.length != 2 && args.length != 3) {
            System.err.println("usage: ZkmDirectStringConstantDeobfuscator"
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
        Map<String, byte[]> originalBytes = classBytes(entries);
        Map<String, ClassNode> classes = readClasses(originalBytes);
        Map<MethodRef, Integer> references = methodReferences(classes);
        Summary summary = new Summary();
        summary.parsedClasses = classes.size();
        summary.outputRequested = output != null;
        List<Candidate> candidates = new ArrayList<>();
        List<String> verifierRows = new ArrayList<>();
        verifierRows.add("scope\tclass\tstatus\treason");
        Map<String, byte[]> replacements = new LinkedHashMap<>();

        for (Map.Entry<String, byte[]> original : originalBytes.entrySet()) {
            ClassNode owner = classes.get(original.getKey());
            Candidate candidate = inspect(owner, references, summary);
            if (candidate == null) continue;
            candidates.add(candidate);
            if (!candidate.proven()) continue;
            summary.provenCandidates++;
            if (output == null) {
                candidate.action = "PROVEN_DRY_RUN";
                continue;
            }
            try {
                ClassNode rewritten = readClass(original.getValue());
                apply(rewritten, candidate);
                byte[] bytes = writeClass(rewritten);
                verifyClass(bytes);
                replacements.put(rewritten.name, bytes);
                candidate.action = "REWRITE";
                summary.changedClasses++;
                summary.rewrittenFields++;
                if (candidate.removeHelper) summary.helpersRemoved++;
                verifierRows.add(tsv("class-transaction", owner.name, "PASS", ""));
            } catch (Throwable failure) {
                candidate.action = "ROLLBACK";
                candidate.reason = appendReason(candidate.reason,
                        "class-rollback:" + shortReason(failure));
                summary.classRollbacks++;
                verifierRows.add(tsv("class-transaction", owner.name, "ROLLBACK",
                        shortReason(failure)));
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
        }
        writeReports(input, reportDirectory, output, summary, candidates,
                verifierRows);
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
        MethodNode clinit = method(owner, "<clinit>", "()V");
        if (clinit == null) return null;
        int pkcsCalls = 0;
        for (AbstractInsnNode insn = clinit.instructions.getFirst(); insn != null;
             insn = insn.getNext()) {
            if (isCipherFactory(insn, ALGORITHM)) pkcsCalls++;
        }
        if (pkcsCalls == 0) return null;
        summary.pkcs5ClinitClasses++;
        Candidate candidate = new Candidate(owner.name, clinit.instructions.size());
        candidate.pkcs5Calls = pkcsCalls;
        if (pkcsCalls != 1) return candidate.reject("pkcs5-call-count=" + pkcsCalls);
        if (!clinit.tryCatchBlocks.isEmpty()) {
            return candidate.reject("initializer-has-exception-ranges");
        }

        List<MethodInsnNode> calls = new ArrayList<>();
        List<FieldInsnNode> fields = new ArrayList<>();
        List<LdcInsnNode> strings = new ArrayList<>();
        Set<Long> longValues = new LinkedHashSet<>();
        int longLoads = 0;
        int returns = 0;
        int byteArrays = 0;
        int byteStores = 0;
        int longUnsignedShifts = 0;
        int longLeftShifts = 0;
        int integerMultiplies = 0;
        int integerIncrements = 0;
        String unsupported = null;
        for (AbstractInsnNode insn = clinit.instructions.getFirst(); insn != null;
             insn = insn.getNext()) {
            int opcode = insn.getOpcode();
            if (opcode < 0) continue;
            if (!allowedTemplateInstruction(insn)) {
                unsupported = instructionName(insn);
                break;
            }
            if (insn instanceof MethodInsnNode) calls.add((MethodInsnNode) insn);
            if (insn instanceof FieldInsnNode) fields.add((FieldInsnNode) insn);
            if (insn instanceof LdcInsnNode) {
                Object value = ((LdcInsnNode) insn).cst;
                if (value instanceof String) strings.add((LdcInsnNode) insn);
                if (value instanceof Long) {
                    longValues.add((Long) value);
                    longLoads++;
                }
            }
            if (opcode == Opcodes.RETURN) returns++;
            if (insn instanceof IntInsnNode && opcode == Opcodes.NEWARRAY
                    && ((IntInsnNode) insn).operand == Opcodes.T_BYTE) byteArrays++;
            if (opcode == Opcodes.BASTORE) byteStores++;
            if (opcode == Opcodes.LUSHR) longUnsignedShifts++;
            if (opcode == Opcodes.LSHL) longLeftShifts++;
            if (opcode == Opcodes.IMUL) integerMultiplies++;
            if (opcode == Opcodes.IINC) integerIncrements++;
        }
        if (unsupported != null) {
            return candidate.reject("unsupported-instruction=" + unsupported);
        }
        if (returns != 1 || lastCode(clinit) == null
                || lastCode(clinit).getOpcode() != Opcodes.RETURN) {
            return candidate.reject("initializer-return-shape=" + returns);
        }
        if (byteArrays != 2 || byteStores != 2 || longUnsignedShifts != 2
                || longLeftShifts != 1 || integerMultiplies != 1
                || integerIncrements != 1) {
            return candidate.reject("key-loop-shape=arrays:" + byteArrays
                    + ",stores:" + byteStores + ",lushr:" + longUnsignedShifts
                    + ",lshl:" + longLeftShifts + ",imul:" + integerMultiplies
                    + ",iinc:" + integerIncrements);
        }
        if (longValues.size() != 1 || longLoads != 2) {
            return candidate.reject("constant-key-shape=unique:" + longValues.size()
                    + ",loads:" + longLoads);
        }
        candidate.key = longValues.iterator().next();

        String callReason = exactCallSet(owner, calls, candidate);
        if (callReason != null) return candidate.reject(callReason);
        if (fields.size() != 1) {
            return candidate.reject("field-instruction-count=" + fields.size());
        }
        FieldInsnNode write = fields.get(0);
        if (write.getOpcode() != Opcodes.PUTSTATIC || !owner.name.equals(write.owner)
                || !STRING_DESC.equals(write.desc)) {
            return candidate.reject("field-write=" + write.owner + "."
                    + write.name + write.desc + "/" + write.getOpcode());
        }
        FieldNode field = field(owner, write.name, write.desc);
        if (field == null || (field.access & (Opcodes.ACC_STATIC | Opcodes.ACC_FINAL))
                != (Opcodes.ACC_STATIC | Opcodes.ACC_FINAL)) {
            return candidate.reject("target-not-static-final-string=" + write.name);
        }
        candidate.fieldName = write.name;

        List<String> ciphertexts = new ArrayList<>();
        int algorithmConstants = 0;
        int keyAlgorithmConstants = 0;
        int charsetConstants = 0;
        for (LdcInsnNode stringNode : strings) {
            String value = (String) stringNode.cst;
            if (ALGORITHM.equals(value)) algorithmConstants++;
            else if (KEY_ALGORITHM.equals(value)) keyAlgorithmConstants++;
            else if (LATIN1.equals(value)) charsetConstants++;
            else ciphertexts.add(value);
        }
        if (algorithmConstants != 1 || keyAlgorithmConstants != 1
                || charsetConstants != 1 || ciphertexts.size() != 1) {
            return candidate.reject("string-constant-shape=algorithm:"
                    + algorithmConstants + ",key-algorithm:" + keyAlgorithmConstants
                    + ",charset:" + charsetConstants + ",ciphertext:"
                    + ciphertexts.size());
        }
        candidate.ciphertext = ciphertexts.get(0);
        if (!latin1Ciphertext(candidate.ciphertext)
                || candidate.ciphertext.length() % 8 != 0) {
            return candidate.reject("ciphertext-not-latin1-des-blocks:length="
                    + candidate.ciphertext.length());
        }
        try {
            candidate.plaintext = decrypt(candidate.ciphertext, candidate.key);
        } catch (Throwable failure) {
            return candidate.reject("decrypt:" + shortReason(failure));
        }
        if (candidate.plaintext.indexOf('\u0000') >= 0) {
            return candidate.reject("plaintext-contains-nul");
        }

        MethodNode helper = method(owner, candidate.helperName, DECODE_DESC);
        if (helper == null || (helper.access & (Opcodes.ACC_PRIVATE | Opcodes.ACC_STATIC))
                != (Opcodes.ACC_PRIVATE | Opcodes.ACC_STATIC)) {
            return candidate.reject("decoder-not-private-static="
                    + candidate.helperName + DECODE_DESC);
        }
        MethodRef helperRef = new MethodRef(owner.name, helper.name, helper.desc);
        int helperReferences = references.containsKey(helperRef)
                ? references.get(helperRef) : 0;
        candidate.helperReferences = helperReferences;
        candidate.removeHelper = helperReferences == 1;
        candidate.action = "PROVEN";
        return candidate;
    }

    private static String exactCallSet(ClassNode owner, List<MethodInsnNode> calls,
                                       Candidate candidate) {
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
        expected.put(call(Opcodes.INVOKEVIRTUAL, "java/lang/String", "getBytes",
                "(Ljava/lang/String;)[B"), 1);
        expected.put(call(Opcodes.INVOKEVIRTUAL, "javax/crypto/Cipher", "doFinal",
                "([B)[B"), 1);
        expected.put(call(Opcodes.INVOKEVIRTUAL, "java/lang/String", "intern",
                "()Ljava/lang/String;"), 1);
        Map<String, Integer> actual = new HashMap<>();
        int helperCalls = 0;
        for (MethodInsnNode method : calls) {
            if (method.getOpcode() == Opcodes.INVOKESTATIC
                    && owner.name.equals(method.owner)
                    && DECODE_DESC.equals(method.desc)) {
                helperCalls++;
                candidate.helperName = method.name;
                continue;
            }
            String key = call(method.getOpcode(), method.owner, method.name, method.desc);
            actual.put(key, actual.containsKey(key) ? actual.get(key) + 1 : 1);
        }
        if (helperCalls != 1) return "decoder-call-count=" + helperCalls;
        if (!actual.equals(expected)) {
            return "jce-call-set=" + actual.size() + "/" + expected.size();
        }
        return null;
    }

    private static boolean allowedTemplateInstruction(AbstractInsnNode insn) {
        int opcode = insn.getOpcode();
        if (insn instanceof InvokeDynamicInsnNode
                || insn instanceof MultiANewArrayInsnNode) return false;
        if (insn instanceof FieldInsnNode) return opcode == Opcodes.PUTSTATIC;
        if (insn instanceof TypeInsnNode) {
            if (opcode != Opcodes.NEW) return false;
            String type = ((TypeInsnNode) insn).desc;
            return "javax/crypto/spec/DESKeySpec".equals(type)
                    || "javax/crypto/spec/IvParameterSpec".equals(type);
        }
        if (insn instanceof MethodInsnNode || insn instanceof LdcInsnNode) return true;
        switch (opcode) {
            case Opcodes.NOP:
            case Opcodes.ICONST_M1:
            case Opcodes.ICONST_0:
            case Opcodes.ICONST_1:
            case Opcodes.ICONST_2:
            case Opcodes.ICONST_3:
            case Opcodes.ICONST_4:
            case Opcodes.ICONST_5:
            case Opcodes.BIPUSH:
            case Opcodes.SIPUSH:
            case Opcodes.ILOAD:
            case Opcodes.ALOAD:
            case Opcodes.ISTORE:
            case Opcodes.ASTORE:
            case Opcodes.POP:
            case Opcodes.DUP:
            case Opcodes.DUP_X1:
            case Opcodes.SWAP:
            case Opcodes.IMUL:
            case Opcodes.LSHL:
            case Opcodes.LUSHR:
            case Opcodes.I2B:
            case Opcodes.L2I:
            case Opcodes.IINC:
            case Opcodes.NEWARRAY:
            case Opcodes.BASTORE:
            case Opcodes.IF_ICMPGE:
            case Opcodes.GOTO:
            case Opcodes.RETURN:
                return true;
            default:
                return false;
        }
    }

    private static void apply(ClassNode owner, Candidate candidate) {
        MethodNode clinit = method(owner, "<clinit>", "()V");
        if (clinit == null) throw new IllegalStateException("missing <clinit>");
        clinit.instructions.clear();
        clinit.instructions.add(new LdcInsnNode(candidate.plaintext));
        clinit.instructions.add(new FieldInsnNode(Opcodes.PUTSTATIC, owner.name,
                candidate.fieldName, STRING_DESC));
        clinit.instructions.add(new InsnNode(Opcodes.RETURN));
        clinit.tryCatchBlocks.clear();
        if (clinit.localVariables != null) clinit.localVariables.clear();
        clinit.visibleLocalVariableAnnotations = null;
        clinit.invisibleLocalVariableAnnotations = null;
        clinit.maxLocals = 0;
        clinit.maxStack = 1;
        if (candidate.removeHelper) {
            MethodNode helper = method(owner, candidate.helperName, DECODE_DESC);
            if (helper == null || !owner.methods.remove(helper)) {
                throw new IllegalStateException("decoder disappeared before removal");
            }
        }
    }

    private static String decrypt(String ciphertext, long keyValue) throws Exception {
        return ZkmDesConstantEvaluator.decryptZkmString(
                ZkmDesConstantEvaluator.KeyMaterial.proven(keyValue,
                        "LDC_LONG", "direct PKCS5 string constant"), ciphertext);
    }

    private static boolean latin1Ciphertext(String value) {
        if (value.isEmpty()) return false;
        for (int i = 0; i < value.length(); i++) {
            if (value.charAt(i) > 0xff) return false;
        }
        return true;
    }

    private static Map<MethodRef, Integer> methodReferences(
            Map<String, ClassNode> classes) {
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
                        for (Object argument : indy.bsmArgs) addConstant(result, argument);
                    } else if (insn instanceof LdcInsnNode) {
                        addConstant(result, ((LdcInsnNode) insn).cst);
                    }
                }
            }
        }
        return result;
    }

    private static void addConstant(Map<MethodRef, Integer> references, Object value) {
        if (value instanceof Handle) {
            addHandle(references, (Handle) value);
        } else if (value instanceof ConstantDynamic) {
            ConstantDynamic dynamic = (ConstantDynamic) value;
            addHandle(references, dynamic.getBootstrapMethod());
            for (int i = 0; i < dynamic.getBootstrapMethodArgumentCount(); i++) {
                addConstant(references, dynamic.getBootstrapMethodArgument(i));
            }
        }
    }

    private static void addHandle(Map<MethodRef, Integer> references, Handle handle) {
        if (handle == null) return;
        int tag = handle.getTag();
        if (tag >= Opcodes.H_INVOKEVIRTUAL && tag <= Opcodes.H_INVOKEINTERFACE) {
            increment(references, new MethodRef(handle.getOwner(), handle.getName(),
                    handle.getDesc()));
        }
    }

    private static void increment(Map<MethodRef, Integer> references, MethodRef ref) {
        references.put(ref, references.containsKey(ref) ? references.get(ref) + 1 : 1);
    }

    private static String call(int opcode, String owner, String name, String desc) {
        return opcode + ":" + owner + "." + name + desc;
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

    private static AbstractInsnNode lastCode(MethodNode method) {
        AbstractInsnNode cursor = method.instructions.getLast();
        while (cursor != null && cursor.getOpcode() < 0) cursor = cursor.getPrevious();
        return cursor;
    }

    private static String instructionName(AbstractInsnNode insn) {
        return insn.getClass().getSimpleName() + ":" + insn.getOpcode();
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

    private static byte[] writeClass(ClassNode owner) {
        ClassWriter writer = new ClassWriter(ClassWriter.COMPUTE_MAXS);
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

    private static void writeVerifiedArchive(
            List<EntryBytes> entries, Map<String, byte[]> replacements, Path output,
            Summary summary, List<String> verifierRows) throws IOException {
        Path parent = output.toAbsolutePath().getParent();
        if (parent == null) parent = Paths.get(".").toAbsolutePath();
        Files.createDirectories(parent);
        Path temporary = Files.createTempFile(parent,
                output.getFileName().toString() + ".", ".tmp");
        summary.temporaryOutput = temporary.toAbsolutePath().toString();
        try {
            writeArchive(entries, replacements, temporary, summary);
            ArchiveVerification verification = verifyArchive(temporary, verifierRows);
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
                    - summary.rewrittenFields;
            if (verification.pkcs5ClinitClasses != expectedRemaining) {
                summary.outputVerificationErrors++;
                verifierRows.add(tsv("archive", "<archive>", "FAIL",
                        "remaining-pkcs5-clinit=" + verification.pkcs5ClinitClasses
                                + "/" + expectedRemaining));
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
                                     Map<String, byte[]> replacements, Path output,
                                     Summary summary) throws IOException {
        Set<String> applied = new LinkedHashSet<>();
        try (ZipOutputStream out = new ZipOutputStream(Files.newOutputStream(output))) {
            for (EntryBytes entry : entries) {
                if (isSignatureEntry(entry.name) && !replacements.isEmpty()) {
                    summary.signaturesRemoved++;
                    continue;
                }
                byte[] bytes = entry.bytes;
                if (entry.name.endsWith(".class")) {
                    String className = new ClassReader(bytes).getClassName();
                    byte[] replacement = replacements.get(className);
                    if (replacement != null) {
                        bytes = replacement;
                        applied.add(className);
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

    private static ArchiveVerification verifyArchive(
            Path archive, List<String> verifierRows) throws IOException {
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
                    if (clinit != null) {
                        for (AbstractInsnNode insn = clinit.instructions.getFirst();
                             insn != null; insn = insn.getNext()) {
                            if (isCipherFactory(insn, ALGORITHM)) {
                                result.pkcs5ClinitClasses++;
                                break;
                            }
                        }
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

    private static boolean isCipherFactory(AbstractInsnNode insn, String algorithm) {
        if (!(insn instanceof MethodInsnNode)) return false;
        MethodInsnNode call = (MethodInsnNode) insn;
        if (call.getOpcode() != Opcodes.INVOKESTATIC
                || !"javax/crypto/Cipher".equals(call.owner)
                || !"getInstance".equals(call.name)
                || !"(Ljava/lang/String;)Ljavax/crypto/Cipher;".equals(call.desc)) {
            return false;
        }
        AbstractInsnNode previous = previousCode(call);
        return previous instanceof LdcInsnNode
                && algorithm.equals(((LdcInsnNode) previous).cst);
    }

    private static AbstractInsnNode previousCode(AbstractInsnNode insn) {
        AbstractInsnNode cursor = insn == null ? null : insn.getPrevious();
        while (cursor != null && cursor.getOpcode() < 0) cursor = cursor.getPrevious();
        return cursor;
    }

    private static void writeReports(Path input, Path reportDirectory, Path output,
                                     Summary summary, List<Candidate> candidates,
                                     List<String> verifierRows) throws Exception {
        List<String> rows = new ArrayList<>();
        rows.add("class\tclinit_nodes\tpkcs5_calls\tfield\tkey_hex"
                + "\tciphertext_length\tplaintext\tdecoder\tdecoder_references"
                + "\tremove_decoder\taction\treason");
        List<String> helperRows = new ArrayList<>();
        helperRows.add("class\tmethod\treferences\taction");
        for (Candidate candidate : candidates) {
            rows.add(candidate.row());
            if (candidate.helperName != null) {
                helperRows.add(tsv(candidate.owner, candidate.helperName + DECODE_DESC,
                        candidate.helperReferences,
                        candidate.removeHelper && ("REWRITE".equals(candidate.action)
                                || "PROVEN_DRY_RUN".equals(candidate.action))
                                ? "REMOVE" : "KEEP"));
            }
        }
        Files.write(reportDirectory.resolve("candidates.tsv"), rows,
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
        audit.add("proven_single_field_candidates=" + summary.provenCandidates);
        audit.add("rejected_pkcs5_clinit_classes=" + summary.rejectedCandidates);
        audit.add("changed_classes=" + summary.changedClasses);
        audit.add("rewritten_fields=" + summary.rewrittenFields);
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
        audit.add("scope=closed-single-static-final-string-template");
        audit.add("excluded=NoPadding,local-string-arrays,enums,mixed-business-initializers,dynamic-inputs");
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
        int parsedClasses;
        int pkcs5ClinitClasses;
        int provenCandidates;
        int rejectedCandidates;
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
        int signaturesRemoved;
        boolean outputCommitted;
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

        boolean proven() {
            return "PROVEN".equals(action);
        }

        String row() {
            return tsv(owner, clinitNodes, pkcs5Calls, value(fieldName),
                    fieldName == null ? "" : String.format(Locale.ROOT, "%016X", key),
                    ciphertext == null ? "" : ciphertext.length(),
                    value(plaintext), value(helperName), helperReferences,
                    removeHelper, action, reason);
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
            return owner.equals(ref.owner) && name.equals(ref.name)
                    && desc.equals(ref.desc);
        }

        @Override
        public int hashCode() {
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
        final int method;
        final String comment;
        final byte[] extra;

        EntryBytes(ZipEntry entry, byte[] bytes) {
            this.name = entry.getName();
            this.bytes = bytes;
            this.time = entry.getTime();
            this.method = entry.getMethod();
            this.comment = entry.getComment();
            this.extra = entry.getExtra();
        }
    }
}
