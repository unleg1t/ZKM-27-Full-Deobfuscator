package cn.openvape.flowdeobf;

import org.objectweb.asm.ClassReader;
import org.objectweb.asm.ClassWriter;
import org.objectweb.asm.Opcodes;
import org.objectweb.asm.tree.AbstractInsnNode;
import org.objectweb.asm.tree.ClassNode;
import org.objectweb.asm.tree.IntInsnNode;
import org.objectweb.asm.tree.LdcInsnNode;
import org.objectweb.asm.tree.MethodNode;
import org.objectweb.asm.tree.analysis.Analyzer;
import org.objectweb.asm.tree.analysis.BasicVerifier;
import org.objectweb.asm.util.CheckClassAdapter;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.AtomicMoveNotSupportedException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.StandardCopyOption;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.zip.CRC32;
import java.util.zip.ZipEntry;
import java.util.zip.ZipInputStream;
import java.util.zip.ZipOutputStream;

/** Shared ASM-only archive IO used by the full-pipeline stages. */
public final class ZkmArchiveIo {
    private ZkmArchiveIo() {
    }

    public static final class EntryBytes {
        public final String name;
        public final byte[] bytes;
        public final long time;
        public final String comment;
        public final byte[] extra;
        public final int method;

        public EntryBytes(String name, byte[] bytes, long time, String comment,
                          byte[] extra, int method) {
            this.name = name;
            this.bytes = bytes;
            this.time = time;
            this.comment = comment;
            this.extra = extra;
            this.method = method;
        }
    }

    public static List<EntryBytes> readEntries(Path input) throws IOException {
        List<EntryBytes> entries = new ArrayList<EntryBytes>();
        try (ZipInputStream in = new ZipInputStream(Files.newInputStream(input))) {
            ZipEntry entry;
            while ((entry = in.getNextEntry()) != null) {
                if (entry.isDirectory()) continue;
                entries.add(new EntryBytes(entry.getName(), readAll(in), entry.getTime(),
                        entry.getComment(), entry.getExtra(), entry.getMethod()));
            }
        }
        return entries;
    }

    public static Map<String, byte[]> classBytes(List<EntryBytes> entries) {
        Map<String, byte[]> result = new LinkedHashMap<String, byte[]>();
        for (EntryBytes entry : entries) {
            if (!entry.name.endsWith(".class")) continue;
            result.put(new ClassReader(entry.bytes).getClassName(), entry.bytes);
        }
        return result;
    }

    public static Map<String, ClassNode> readClasses(Map<String, byte[]> bytes) {
        Map<String, ClassNode> result = new LinkedHashMap<String, ClassNode>();
        for (Map.Entry<String, byte[]> entry : bytes.entrySet()) {
            result.put(entry.getKey(), readClass(entry.getValue()));
        }
        return result;
    }

    public static ClassNode readClass(byte[] bytes) {
        ClassNode owner = new ClassNode(Opcodes.ASM9);
        new ClassReader(bytes).accept(owner, 0);
        return owner;
    }

    public static byte[] writeClass(ClassNode owner) {
        ClassWriter writer = new ClassWriter(ClassWriter.COMPUTE_MAXS);
        owner.accept(writer);
        return writer.toByteArray();
    }

    public static void verifyClass(byte[] bytes) throws Exception {
        ClassReader reader = new ClassReader(bytes);
        reader.accept(new CheckClassAdapter(new ClassWriter(0), false), 0);
        ClassNode owner = readClass(bytes);
        for (MethodNode method : owner.methods) {
            if (method.instructions != null && method.instructions.size() != 0) {
                new Analyzer<org.objectweb.asm.tree.analysis.BasicValue>(
                        new BasicVerifier()).analyze(owner.name, method);
            }
        }
    }

    public static void writeArchive(List<EntryBytes> entries,
                                    Map<String, byte[]> replacements, Path output)
            throws IOException {
        Set<String> applied = new LinkedHashSet<String>();
        Path parent = output.toAbsolutePath().getParent();
        if (parent != null) Files.createDirectories(parent);
        Path temporary = Files.createTempFile(parent == null
                        ? output.toAbsolutePath().getParent() : parent,
                output.getFileName().toString() + ".", ".tmp");
        try {
            try (ZipOutputStream out = new ZipOutputStream(Files.newOutputStream(temporary))) {
                for (EntryBytes entry : entries) {
                    if (isSignatureEntry(entry.name) && !replacements.isEmpty()) continue;
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
                }
            }
            if (applied.size() != replacements.size()) {
                throw new IOException("applied-replacements=" + applied.size() + "/"
                        + replacements.size());
            }
            try {
                Files.move(temporary, output, StandardCopyOption.ATOMIC_MOVE,
                        StandardCopyOption.REPLACE_EXISTING);
            } catch (AtomicMoveNotSupportedException unsupported) {
                Files.move(temporary, output, StandardCopyOption.REPLACE_EXISTING);
            }
        } finally {
            Files.deleteIfExists(temporary);
        }
    }

    public static void validatePaths(Path input, Path output) throws IOException {
        if (output == null) return;
        Path source = input.toAbsolutePath().normalize();
        Path target = output.toAbsolutePath().normalize();
        if (source.equals(target)
                || Files.exists(target) && Files.isSameFile(source, target)) {
            throw new IllegalArgumentException("output must not replace input");
        }
    }

    public static boolean isSignatureEntry(String name) {
        String lower = name.toLowerCase();
        return lower.startsWith("meta-inf/")
                && (lower.endsWith(".sf") || lower.endsWith(".rsa")
                || lower.endsWith(".dsa") || lower.endsWith(".ec"));
    }

    public static Integer intConstant(AbstractInsnNode insn) {
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

    public static Long longConstant(AbstractInsnNode insn) {
        if (insn == null) return null;
        if (insn.getOpcode() == Opcodes.LCONST_0) return 0L;
        if (insn.getOpcode() == Opcodes.LCONST_1) return 1L;
        if (insn instanceof LdcInsnNode && ((LdcInsnNode) insn).cst instanceof Long) {
            return (Long) ((LdcInsnNode) insn).cst;
        }
        return null;
    }

    public static AbstractInsnNode previousCode(AbstractInsnNode insn) {
        AbstractInsnNode cursor = insn;
        while (cursor != null) {
            cursor = cursor.getPrevious();
            if (cursor != null && cursor.getOpcode() >= 0) return cursor;
        }
        return null;
    }

    public static AbstractInsnNode nextCode(AbstractInsnNode insn) {
        AbstractInsnNode cursor = insn;
        while (cursor != null) {
            cursor = cursor.getNext();
            if (cursor != null && cursor.getOpcode() >= 0) return cursor;
        }
        return null;
    }

    public static AbstractInsnNode pushInt(int value) {
        if (value >= -1 && value <= 5) {
            return new org.objectweb.asm.tree.InsnNode(Opcodes.ICONST_0 + value);
        }
        if (value >= Byte.MIN_VALUE && value <= Byte.MAX_VALUE) {
            return new IntInsnNode(Opcodes.BIPUSH, value);
        }
        if (value >= Short.MIN_VALUE && value <= Short.MAX_VALUE) {
            return new IntInsnNode(Opcodes.SIPUSH, value);
        }
        return new LdcInsnNode(value);
    }

    public static AbstractInsnNode pushLong(long value) {
        if (value == 0L) return new org.objectweb.asm.tree.InsnNode(Opcodes.LCONST_0);
        if (value == 1L) return new org.objectweb.asm.tree.InsnNode(Opcodes.LCONST_1);
        return new LdcInsnNode(value);
    }

    public static MethodNode method(ClassNode owner, String name, String desc) {
        for (MethodNode method : owner.methods) {
            if (name.equals(method.name) && desc.equals(method.desc)) return method;
        }
        return null;
    }

    public static String tsv(String... columns) {
        return String.join("\t", columns);
    }

    public static void writeText(Path path, List<String> lines) throws IOException {
        Path parent = path.toAbsolutePath().getParent();
        if (parent != null) Files.createDirectories(parent);
        Files.write(path, lines, StandardCharsets.UTF_8);
    }

    public static byte[] readAll(InputStream in) throws IOException {
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        byte[] buffer = new byte[8192];
        int count;
        while ((count = in.read(buffer)) >= 0) out.write(buffer, 0, count);
        return out.toByteArray();
    }
}
