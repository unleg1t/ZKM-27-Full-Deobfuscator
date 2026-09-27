package unlegit.zkm;

import org.objectweb.asm.ClassReader;
import org.objectweb.asm.Opcodes;
import org.objectweb.asm.tree.AbstractInsnNode;
import org.objectweb.asm.tree.ClassNode;
import org.objectweb.asm.tree.FieldInsnNode;
import org.objectweb.asm.tree.FieldNode;
import org.objectweb.asm.tree.IntInsnNode;
import org.objectweb.asm.tree.InvokeDynamicInsnNode;
import org.objectweb.asm.tree.JumpInsnNode;
import org.objectweb.asm.tree.LdcInsnNode;
import org.objectweb.asm.tree.MethodInsnNode;
import org.objectweb.asm.tree.MethodNode;
import org.objectweb.asm.tree.TypeInsnNode;
import org.objectweb.asm.tree.VarInsnNode;

import java.io.IOException;
import java.io.InputStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.zip.ZipEntry;
import java.util.zip.ZipInputStream;

/**
 * Read-only inventory of DES/CBC/NoPadding static initializers.
 *
 * <p>This audit deliberately does not evaluate or rewrite any class.  It
 * records the state-bootstrap boundary, array/table writes, static writes,
 * and control-flow shape so a later transformer can require a strict proof
 * instead of treating all NoPadding blocks as interchangeable.</p>
 */
public final class ZkmNoPaddingShapeAudit {
    private static final String NO_PADDING = "DES/CBC/NoPadding";
    private static final String STATE = ObfRuntimeNames.STATE;
    private static final String STATE_IFACE = ObfRuntimeNames.STATE_INTERFACE;

    private ZkmNoPaddingShapeAudit() {
    }

    public static void main(String[] args) throws Exception {
        if (args.length != 2) {
            System.err.println("usage: ZkmNoPaddingShapeAudit <input.jar> <report-dir>");
            System.exit(2);
        }
        audit(Paths.get(args[0]), Paths.get(args[1]));
    }

    static Summary audit(Path input, Path reportDirectory) throws Exception {
        Files.createDirectories(reportDirectory);
        List<Row> rows = new ArrayList<>();
        try (ZipInputStream zip = new ZipInputStream(Files.newInputStream(input))) {
            ZipEntry entry;
            while ((entry = zip.getNextEntry()) != null) {
                if (entry.isDirectory() || !entry.getName().endsWith(".class")) continue;
                byte[] bytes = readCurrent(zip);
                ClassNode owner = new ClassNode(Opcodes.ASM9);
                new ClassReader(bytes).accept(owner, ClassReader.SKIP_FRAMES);
                MethodNode clinit = null;
                for (MethodNode method : owner.methods) {
                    if ("<clinit>".equals(method.name) && "()V".equals(method.desc)) {
                        clinit = method;
                        break;
                    }
                }
                if (clinit == null) continue;
                Row row = inspect(owner, clinit);
                if (row.noPaddingCalls != 0) rows.add(row);
            }
        }
        rows.sort(Comparator.comparing(row -> row.owner));
        writeTsv(reportDirectory.resolve("nopadding-shapes.tsv"), rows);
        Summary summary = summarize(rows);
        List<String> lines = new ArrayList<>();
        lines.add("input=" + input.toAbsolutePath().normalize());
        lines.add("classes=" + summary.classes);
        lines.add("no_padding_calls=" + summary.noPaddingCalls);
        lines.add("state_bootstrap_classes=" + summary.stateBootstrapClasses);
        lines.add("state_bootstrap_calls=" + summary.stateBootstrapCalls);
        lines.add("state_resolve_calls=" + summary.stateResolveCalls);
        lines.add("long_array_classes=" + summary.longArrayClasses);
        lines.add("long_array_creates=" + summary.longArrayCreates);
        lines.add("long_array_stores=" + summary.longArrayStores);
        lines.add("scalar_long_putstatic_classes=" + summary.scalarLongPutstaticClasses);
        lines.add("scalar_integer_putstatic_classes=" + summary.scalarIntegerPutstaticClasses);
        lines.add("mixed_putstatic_classes=" + summary.mixedPutstaticClasses);
        lines.add("try_catch_classes=" + summary.tryCatchClasses);
        lines.add("invokedynamic_classes=" + summary.invokedynamicClasses);
        lines.add("shape_counts=" + summary.shapeCounts);
        lines.add("policy=read-only; no class was evaluated, loaded, initialized, or rewritten");
        Files.write(reportDirectory.resolve("nopadding-shapes-summary.txt"), lines,
                StandardCharsets.UTF_8);
        System.out.println(String.join(" ", lines));
        return summary;
    }

    private static Row inspect(ClassNode owner, MethodNode clinit) {
        Row row = new Row();
        row.owner = owner.name;
        row.instructions = clinit.instructions.size();
        row.tryCatchBlocks = clinit.tryCatchBlocks == null ? 0 : clinit.tryCatchBlocks.size();
        for (AbstractInsnNode insn = clinit.instructions.getFirst(); insn != null;
             insn = insn.getNext()) {
            int opcode = insn.getOpcode();
            if (opcode < 0) continue;
            if (insn instanceof LdcInsnNode) {
                Object constant = ((LdcInsnNode) insn).cst;
                if (constant instanceof Long) row.longConstants++;
                if (constant instanceof String && NO_PADDING.equals(constant)) {
                    row.noPaddingLiterals++;
                }
            }
            if (insn instanceof MethodInsnNode) {
                MethodInsnNode call = (MethodInsnNode) insn;
                if (isCipherFactory(call)) row.noPaddingCalls++;
                if (STATE.equals(call.owner) && "a".equals(call.name)) {
                    row.stateBootstrapCalls++;
                }
                if (STATE_IFACE.equals(call.owner) && "a".equals(call.name)
                        && "(J)J".equals(call.desc)) row.stateResolveCalls++;
                if ("javax/crypto/Cipher".equals(call.owner)
                        && "doFinal".equals(call.name)) row.doFinalCalls++;
                if ("javax/crypto/SecretKeyFactory".equals(call.owner)
                        && "generateSecret".equals(call.name)) row.generateSecretCalls++;
                if ("javax/crypto/spec/DESKeySpec".equals(call.owner)
                        && "<init>".equals(call.name)) row.desKeySpecCreates++;
                if ("javax/crypto/spec/IvParameterSpec".equals(call.owner)
                        && "<init>".equals(call.name)) row.ivCreates++;
                if ("javax/crypto/Cipher".equals(call.owner) && "init".equals(call.name)) {
                    row.cipherInitCalls++;
                }
                if ("javax/crypto/SecretKeyFactory".equals(call.owner)
                        && "getInstance".equals(call.name)) row.keyFactoryCalls++;
                if (call.getOpcode() == Opcodes.INVOKEDYNAMIC) row.invokedynamicCalls++;
            }
            if (insn instanceof InvokeDynamicInsnNode) row.invokedynamicCalls++;
            if (insn instanceof FieldInsnNode) {
                FieldInsnNode field = (FieldInsnNode) insn;
                if (opcode == Opcodes.PUTSTATIC && owner.name.equals(field.owner)) {
                    row.putstaticCount++;
                    row.putstaticDescs.merge(field.desc, 1, Integer::sum);
                }
            }
            if (insn instanceof IntInsnNode && opcode == Opcodes.NEWARRAY) {
                int operand = ((IntInsnNode) insn).operand;
                if (operand == Opcodes.T_LONG) row.longArrayCreates++;
                if (operand == Opcodes.T_BYTE) row.byteArrayCreates++;
            }
            if (insn instanceof TypeInsnNode && opcode == Opcodes.ANEWARRAY) {
                row.objectArrayCreates++;
            }
            if (opcode == Opcodes.LASTORE) row.longArrayStores++;
            if (opcode == Opcodes.IASTORE) row.intArrayStores++;
            if (opcode == Opcodes.AASTORE) row.objectArrayStores++;
            if (opcode == Opcodes.BASTORE) row.byteArrayStores++;
            if (opcode == Opcodes.GOTO || insn instanceof JumpInsnNode) row.jumps++;
            if (opcode == Opcodes.IINC) row.iincs++;
        }
        row.shape = classify(row);
        return row;
    }

    private static String classify(Row row) {
        if (row.tryCatchBlocks != 0) return "EXCEPTION_MIXED";
        if (row.invokedynamicCalls != 0) return "INDY_MIXED";
        if (row.longArrayCreates != 0 && row.longArrayStores != 0) {
            return row.stateBootstrapCalls != 0 ? "STATE_LONG_ARRAY_TABLE" : "LONG_ARRAY_TABLE";
        }
        if (row.stateBootstrapCalls != 0) {
            return row.putstaticCount == 1 ? "STATE_SCALAR_OR_MIXED" : "STATE_MIXED";
        }
        if (row.putstaticCount == 1 && row.putstaticDescs.containsKey("J")) {
            return "SCALAR_LONG";
        }
        if (row.putstaticCount != 0 && row.longArrayCreates == 0) {
            return "SCALAR_OR_OBJECT_MIXED";
        }
        return "OTHER";
    }

    private static boolean isCipherFactory(MethodInsnNode call) {
        AbstractInsnNode previous = previousCode(call);
        return call.getOpcode() == Opcodes.INVOKESTATIC
                && "javax/crypto/Cipher".equals(call.owner)
                && "getInstance".equals(call.name)
                && "(Ljava/lang/String;)Ljavax/crypto/Cipher;".equals(call.desc)
                && previous instanceof LdcInsnNode
                && NO_PADDING.equals(((LdcInsnNode) previous).cst);
    }

    private static AbstractInsnNode previousCode(AbstractInsnNode node) {
        AbstractInsnNode previous = node.getPrevious();
        while (previous != null && previous.getOpcode() < 0) {
            previous = previous.getPrevious();
        }
        return previous;
    }

    private static Summary summarize(List<Row> rows) {
        Summary summary = new Summary();
        summary.classes = rows.size();
        for (Row row : rows) {
            summary.noPaddingCalls += row.noPaddingCalls;
            summary.stateBootstrapCalls += row.stateBootstrapCalls;
            summary.stateResolveCalls += row.stateResolveCalls;
            summary.longArrayCreates += row.longArrayCreates;
            summary.longArrayStores += row.longArrayStores;
            summary.shapeCounts.merge(row.shape, 1, Integer::sum);
            if (row.stateBootstrapCalls != 0) summary.stateBootstrapClasses++;
            if (row.longArrayCreates != 0) summary.longArrayClasses++;
            if (row.putstaticDescs.containsKey("J")) summary.scalarLongPutstaticClasses++;
            if (row.putstaticDescs.containsKey("I")) summary.scalarIntegerPutstaticClasses++;
            if (row.putstaticCount > 1 || row.putstaticDescs.size() > 1) summary.mixedPutstaticClasses++;
            if (row.tryCatchBlocks != 0) summary.tryCatchClasses++;
            if (row.invokedynamicCalls != 0) summary.invokedynamicClasses++;
        }
        return summary;
    }

    private static void writeTsv(Path path, List<Row> rows) throws IOException {
        List<String> lines = new ArrayList<>();
        lines.add("class\tshape\tinsns\ttry_catch\tno_padding_calls\tstate_bootstrap_calls\tstate_resolve_calls\tdo_final\tlong_consts\tbyte_arrays\tlong_arrays\tlong_array_stores\tint_array_stores\tobject_arrays\tobject_array_stores\tputstatic\tputstatic_descs\tjumps\tiincs\tkey_factory\tdes_key_spec\tiv\tcipher_init\tgeneric_generate_secret");
        for (Row row : rows) {
            lines.add(String.join("\t", row.owner, row.shape, Integer.toString(row.instructions),
                    Integer.toString(row.tryCatchBlocks), Integer.toString(row.noPaddingCalls),
                    Integer.toString(row.stateBootstrapCalls), Integer.toString(row.stateResolveCalls),
                    Integer.toString(row.doFinalCalls), Integer.toString(row.longConstants),
                    Integer.toString(row.byteArrayCreates), Integer.toString(row.longArrayCreates),
                    Integer.toString(row.longArrayStores), Integer.toString(row.intArrayStores),
                    Integer.toString(row.objectArrayCreates), Integer.toString(row.objectArrayStores),
                    Integer.toString(row.putstaticCount), row.putstaticDescs.toString(),
                    Integer.toString(row.jumps), Integer.toString(row.iincs),
                    Integer.toString(row.keyFactoryCalls), Integer.toString(row.desKeySpecCreates),
                    Integer.toString(row.ivCreates), Integer.toString(row.cipherInitCalls),
                    Integer.toString(row.generateSecretCalls)));
        }
        Files.write(path, lines, StandardCharsets.UTF_8);
    }

    private static byte[] readCurrent(ZipInputStream zip) throws IOException {
        byte[] buffer = new byte[8192];
        java.io.ByteArrayOutputStream out = new java.io.ByteArrayOutputStream();
        int read;
        while ((read = zip.read(buffer)) >= 0) {
            if (read != 0) out.write(buffer, 0, read);
        }
        return out.toByteArray();
    }

    static final class Summary {
        int classes;
        int noPaddingCalls;
        int stateBootstrapClasses;
        int stateBootstrapCalls;
        int stateResolveCalls;
        int longArrayClasses;
        int longArrayCreates;
        int longArrayStores;
        int scalarLongPutstaticClasses;
        int scalarIntegerPutstaticClasses;
        int mixedPutstaticClasses;
        int tryCatchClasses;
        int invokedynamicClasses;
        final Map<String, Integer> shapeCounts = new LinkedHashMap<>();
    }

    private static final class Row {
        String owner;
        String shape;
        int instructions;
        int tryCatchBlocks;
        int noPaddingCalls;
        int noPaddingLiterals;
        int stateBootstrapCalls;
        int stateResolveCalls;
        int doFinalCalls;
        int longConstants;
        int byteArrayCreates;
        int longArrayCreates;
        int longArrayStores;
        int intArrayStores;
        int byteArrayStores;
        int objectArrayCreates;
        int objectArrayStores;
        int putstaticCount;
        int jumps;
        int iincs;
        int keyFactoryCalls;
        int desKeySpecCreates;
        int ivCreates;
        int cipherInitCalls;
        int generateSecretCalls;
        int invokedynamicCalls;
        final Map<String, Integer> putstaticDescs = new LinkedHashMap<>();
    }
}
