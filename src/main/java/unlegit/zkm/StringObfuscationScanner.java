package unlegit.zkm;

import org.objectweb.asm.ClassReader;
import org.objectweb.asm.Handle;
import org.objectweb.asm.Opcodes;
import org.objectweb.asm.Type;
import org.objectweb.asm.tree.AbstractInsnNode;
import org.objectweb.asm.tree.ClassNode;
import org.objectweb.asm.tree.FieldNode;
import org.objectweb.asm.tree.InvokeDynamicInsnNode;
import org.objectweb.asm.tree.LdcInsnNode;
import org.objectweb.asm.tree.MethodInsnNode;
import org.objectweb.asm.tree.MethodNode;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.security.MessageDigest;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.List;
import java.util.Locale;
import java.util.zip.ZipEntry;
import java.util.zip.ZipInputStream;

/** Read-only inventory of ZKM-style string protection in a JVM archive. */
public final class StringObfuscationScanner {
    private static final String LONG_KEY_OWNER = ObfRuntimeNames.STATE;
    private static final String LONG_KEY_DESC =
            ObfRuntimeNames.BOOTSTRAP_DESC;
    private static final String LONG_STATE_OWNER = ObfRuntimeNames.STATE_INTERFACE;

    private StringObfuscationScanner() {
    }

    public static void main(String[] args) throws Exception {
        if (args.length != 2) {
            System.err.println("usage: StringObfuscationScanner <input.jar> <output-dir>");
            System.exit(2);
        }
        scan(Paths.get(args[0]), Paths.get(args[1]));
    }

    static ScanSummary scan(Path input, Path outputDir) throws Exception {
        Files.createDirectories(outputDir);
        List<ClassBytes> classes = readClasses(input);
        List<String> classRows = new ArrayList<>();
        List<String> siteRows = new ArrayList<>();
        classRows.add("class\tentry\tmethods\tstring_array_fields\tldc_strings\tlatin1_cipher_literals"
                + "\tdes_cipher_calls\tlong_key_bootstraps\tlong_key_transforms\tstring_indy_sites"
                + "\tclinit_instructions\tclassification\tparse_status");
        siteRows.add("class\tmethod\tinstruction\ttype\tdetail");

        ScanSummary summary = new ScanSummary();
        summary.classEntries = classes.size();
        for (ClassBytes entry : classes) {
            ClassNode node = new ClassNode(Opcodes.ASM9);
            try {
                new ClassReader(entry.bytes).accept(node, ClassReader.SKIP_FRAMES);
                summary.parsedClasses++;
                ClassStats stats = inspect(node, siteRows);
                summary.methods += node.methods.size();
                summary.ldcStrings += stats.ldcStrings;
                summary.latin1CipherLiterals += stats.latin1CipherLiterals;
                summary.desCipherCalls += stats.desCipherCalls;
                summary.longKeyBootstraps += stats.longKeyBootstraps;
                summary.longKeyTransforms += stats.longKeyTransforms;
                summary.stringIndySites += stats.stringIndySites;
                if (stats.isProtected()) summary.protectedClasses++;
                classRows.add(row(node.name, entry.name, node.methods.size(), stats.stringArrayFields,
                        stats.ldcStrings, stats.latin1CipherLiterals, stats.desCipherCalls,
                        stats.longKeyBootstraps, stats.longKeyTransforms, stats.stringIndySites,
                        stats.clinitInstructions, stats.classification(), "OK"));
            } catch (Throwable failure) {
                summary.malformedClasses++;
                classRows.add(row("<unknown>", entry.name, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                        "unparsed", "ERROR:" + shortReason(failure)));
            }
        }

        classRows.subList(1, classRows.size()).sort(Comparator.naturalOrder());
        siteRows.subList(1, siteRows.size()).sort(Comparator.naturalOrder());
        Files.write(outputDir.resolve("classes.tsv"), classRows, StandardCharsets.UTF_8);
        Files.write(outputDir.resolve("sites.tsv"), siteRows, StandardCharsets.UTF_8);
        Files.write(outputDir.resolve("audit.txt"), audit(input, summary), StandardCharsets.UTF_8);
        Files.write(outputDir.resolve("gate.txt"),
                (summary.malformedClasses == 0 ? "PASS\n" : "FAIL\n").getBytes(StandardCharsets.UTF_8));
        System.out.println("classes=" + summary.parsedClasses + "/" + summary.classEntries
                + " protected=" + summary.protectedClasses
                + " des=" + summary.desCipherCalls
                + " indy=" + summary.stringIndySites
                + " report=" + outputDir);
        return summary;
    }

    private static ClassStats inspect(ClassNode node, List<String> siteRows) {
        ClassStats stats = new ClassStats();
        for (FieldNode field : node.fields) {
            if ("[Ljava/lang/String;".equals(field.desc)) stats.stringArrayFields++;
        }
        for (MethodNode method : node.methods) {
            if ("<clinit>".equals(method.name)) stats.clinitInstructions = method.instructions.size();
            int index = 0;
            for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
                 insn = insn.getNext(), index++) {
                if (insn instanceof LdcInsnNode && ((LdcInsnNode) insn).cst instanceof String) {
                    String value = (String) ((LdcInsnNode) insn).cst;
                    stats.ldcStrings++;
                    if (looksLikeLatin1Ciphertext(value)) {
                        stats.latin1CipherLiterals++;
                        siteRows.add(site(node, method, index, "LATIN1_CIPHERTEXT",
                                "length=" + value.length() + ",hex_prefix=" + hexPrefix(value)));
                    }
                } else if (insn instanceof MethodInsnNode) {
                    MethodInsnNode call = (MethodInsnNode) insn;
                    if (isDesCipherFactory(call)) {
                        stats.desCipherCalls++;
                        siteRows.add(site(node, method, index, "DES_CIPHER", call.owner + "."
                                + call.name + call.desc + ",algorithm=" + precedingString(call)));
                    } else if (isLongKeyBootstrap(call)) {
                        stats.longKeyBootstraps++;
                        siteRows.add(site(node, method, index, "LONG_KEY_BOOTSTRAP",
                                call.owner + "." + call.name + call.desc + ","
                                        + longKeyBootstrapArguments(call)));
                    } else if (isLongKeyTransform(call)) {
                        stats.longKeyTransforms++;
                        siteRows.add(site(node, method, index, "LONG_KEY_TRANSFORM",
                                call.owner + "." + call.name + call.desc
                                        + ",input=" + value(longConstant(previousCode(call)))));
                    }
                } else if (insn instanceof InvokeDynamicInsnNode) {
                    InvokeDynamicInsnNode indy = (InvokeDynamicInsnNode) insn;
                    if (Type.getReturnType(indy.desc).getSort() == Type.OBJECT
                            && "java/lang/String".equals(Type.getReturnType(indy.desc).getInternalName())) {
                        stats.stringIndySites++;
                        siteRows.add(site(node, method, index, "STRING_INDY",
                                indy.name + indy.desc + ",bootstrap=" + handle(indy.bsm)
                                        + ",bootstrap_args=" + bootstrapArguments(indy.bsmArgs)));
                    }
                }
            }
        }
        return stats;
    }

    private static boolean isDesCipherFactory(MethodInsnNode call) {
        if (call.getOpcode() != Opcodes.INVOKESTATIC
                || !"javax/crypto/Cipher".equals(call.owner)
                || !"getInstance".equals(call.name)
                || !"(Ljava/lang/String;)Ljavax/crypto/Cipher;".equals(call.desc)) return false;
        String algorithm = precedingString(call);
        return algorithm != null && algorithm.startsWith("DES/");
    }

    private static boolean isLongKeyBootstrap(MethodInsnNode call) {
        return call.getOpcode() == Opcodes.INVOKESTATIC
                && LONG_KEY_OWNER.equals(call.owner)
                && "a".equals(call.name)
                && LONG_KEY_DESC.equals(call.desc);
    }

    private static boolean isLongKeyTransform(MethodInsnNode call) {
        return call.getOpcode() == Opcodes.INVOKEINTERFACE
                && LONG_STATE_OWNER.equals(call.owner)
                && "a".equals(call.name)
                && "(J)J".equals(call.desc);
    }

    private static String longKeyBootstrapArguments(MethodInsnNode call) {
        AbstractInsnNode owner = previousCode(call);
        String ownerKind = "unknown";
        AbstractInsnNode seedBNode = null;
        if (owner != null && owner.getOpcode() == Opcodes.ACONST_NULL) {
            ownerKind = "null";
            seedBNode = previousCode(owner);
        } else if (owner instanceof MethodInsnNode) {
            MethodInsnNode lookupClass = (MethodInsnNode) owner;
            if ("java/lang/invoke/MethodHandles$Lookup".equals(lookupClass.owner)
                    && "lookupClass".equals(lookupClass.name)) {
                ownerKind = "lookupClass";
                AbstractInsnNode lookup = previousCode(owner);
                seedBNode = previousCode(lookup);
            }
        }
        AbstractInsnNode seedA = seedBNode == null ? null : previousCode(seedBNode);
        return "seed_a=" + value(longConstant(seedA))
                + ",seed_b=" + value(longConstant(seedBNode))
                + ",owner_arg=" + ownerKind;
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

    private static String value(Object value) {
        return value == null ? "unknown" : String.valueOf(value);
    }

    private static String bootstrapArguments(Object[] arguments) {
        if (arguments == null || arguments.length == 0) return "[]";
        StringBuilder result = new StringBuilder("[");
        for (int i = 0; i < arguments.length; i++) {
            if (i > 0) result.append('|');
            Object argument = arguments[i];
            if (argument instanceof Handle) result.append(handle((Handle) argument));
            else if (argument instanceof Type) result.append(((Type) argument).getDescriptor());
            else result.append(String.valueOf(argument));
        }
        return result.append(']').toString();
    }

    private static String precedingString(AbstractInsnNode insn) {
        AbstractInsnNode previous = previousCode(insn);
        return previous instanceof LdcInsnNode && ((LdcInsnNode) previous).cst instanceof String
                ? (String) ((LdcInsnNode) previous).cst : null;
    }

    static boolean looksLikeLatin1Ciphertext(String value) {
        if (value.length() < 8) return false;
        int suspicious = 0;
        int highLatin1 = 0;
        for (int i = 0; i < value.length(); i++) {
            char c = value.charAt(i);
            if (c > 0xff) return false;
            if (c >= 0x80) {
                highLatin1++;
                suspicious++;
            } else if (c < 0x20 && c != '\t' && c != '\n' && c != '\r') {
                suspicious++;
            }
        }
        return highLatin1 > 0 && suspicious * 4 >= value.length();
    }

    private static String hexPrefix(String value) {
        StringBuilder result = new StringBuilder();
        int limit = Math.min(value.length(), 12);
        for (int i = 0; i < limit; i++) {
            if (i > 0) result.append('-');
            result.append(String.format(Locale.ROOT, "%02X", (int) value.charAt(i)));
        }
        return result.toString();
    }

    private static String handle(Handle handle) {
        return handle.getOwner() + "." + handle.getName() + handle.getDesc();
    }

    private static String site(ClassNode owner, MethodNode method, int instruction,
                               String type, String detail) {
        return owner.name + "\t" + method.name + method.desc + "\t" + instruction + "\t"
                + type + "\t" + sanitize(detail);
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

    private static AbstractInsnNode previousCode(AbstractInsnNode insn) {
        AbstractInsnNode previous = insn.getPrevious();
        while (previous != null && previous.getOpcode() < 0) previous = previous.getPrevious();
        return previous;
    }

    private static List<ClassBytes> readClasses(Path input) throws IOException {
        List<ClassBytes> result = new ArrayList<>();
        try (ZipInputStream in = new ZipInputStream(Files.newInputStream(input))) {
            ZipEntry entry;
            while ((entry = in.getNextEntry()) != null) {
                if (!entry.isDirectory() && entry.getName().endsWith(".class")) {
                    result.add(new ClassBytes(entry.getName(), readAll(in)));
                }
            }
        }
        return result;
    }

    private static byte[] readAll(InputStream in) throws IOException {
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        byte[] buffer = new byte[8192];
        int count;
        while ((count = in.read(buffer)) >= 0) out.write(buffer, 0, count);
        return out.toByteArray();
    }

    private static List<String> audit(Path input, ScanSummary summary) throws Exception {
        List<String> rows = new ArrayList<>();
        rows.add("input=" + input.toAbsolutePath());
        rows.add("input_sha256=" + sha256(input));
        rows.add("class_entries=" + summary.classEntries);
        rows.add("parsed_classes=" + summary.parsedClasses);
        rows.add("malformed_classes=" + summary.malformedClasses);
        rows.add("methods=" + summary.methods);
        rows.add("protected_classes=" + summary.protectedClasses);
        rows.add("ldc_strings=" + summary.ldcStrings);
        rows.add("latin1_cipher_literals=" + summary.latin1CipherLiterals);
        rows.add("des_cipher_calls=" + summary.desCipherCalls);
        rows.add("long_key_bootstraps=" + summary.longKeyBootstraps);
        rows.add("long_key_transforms=" + summary.longKeyTransforms);
        rows.add("string_indy_sites=" + summary.stringIndySites);
        rows.add("read_only=true");
        return rows;
    }

    private static String sha256(Path path) throws Exception {
        MessageDigest digest = MessageDigest.getInstance("SHA-256");
        try (InputStream in = Files.newInputStream(path)) {
            byte[] buffer = new byte[8192];
            int count;
            while ((count = in.read(buffer)) >= 0) digest.update(buffer, 0, count);
        }
        StringBuilder result = new StringBuilder();
        for (byte value : digest.digest()) result.append(String.format(Locale.ROOT, "%02X", value & 0xff));
        return result.toString();
    }

    private static String shortReason(Throwable failure) {
        String reason = failure.getClass().getSimpleName() + ":" + String.valueOf(failure.getMessage());
        return sanitize(reason).substring(0, Math.min(180, reason.length()));
    }

    static final class ScanSummary {
        int classEntries;
        int parsedClasses;
        int malformedClasses;
        int methods;
        int protectedClasses;
        int ldcStrings;
        int latin1CipherLiterals;
        int desCipherCalls;
        int longKeyBootstraps;
        int longKeyTransforms;
        int stringIndySites;
    }

    private static final class ClassStats {
        int stringArrayFields;
        int ldcStrings;
        int latin1CipherLiterals;
        int desCipherCalls;
        int longKeyBootstraps;
        int longKeyTransforms;
        int stringIndySites;
        int clinitInstructions;

        boolean isProtected() {
            return desCipherCalls > 0 || longKeyBootstraps > 0 || stringIndySites > 0;
        }

        String classification() {
            if (desCipherCalls > 0 && stringIndySites > 0) return "zkm_des_indy";
            if (desCipherCalls > 0 && longKeyBootstraps > 0) return "zkm_des_static";
            if (stringIndySites > 0 && longKeyBootstraps > 0) return "zkm_indy";
            if (desCipherCalls > 0) return "des_only";
            if (stringIndySites > 0) return "string_indy_only";
            if (longKeyBootstraps > 0) return "long_key_only";
            return "none";
        }
    }

    private static final class ClassBytes {
        final String name;
        final byte[] bytes;

        ClassBytes(String name, byte[] bytes) {
            this.name = name;
            this.bytes = bytes;
        }
    }
}
