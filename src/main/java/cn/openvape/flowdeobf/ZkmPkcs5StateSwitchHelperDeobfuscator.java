package cn.openvape.flowdeobf;

import org.objectweb.asm.Opcodes;
import org.objectweb.asm.tree.AbstractInsnNode;
import org.objectweb.asm.tree.ClassNode;
import org.objectweb.asm.tree.FieldInsnNode;
import org.objectweb.asm.tree.FieldNode;
import org.objectweb.asm.tree.LdcInsnNode;
import org.objectweb.asm.tree.MethodInsnNode;
import org.objectweb.asm.tree.MethodNode;
import org.objectweb.asm.tree.TypeInsnNode;
import org.objectweb.asm.tree.VarInsnNode;
import org.objectweb.asm.tree.analysis.Analyzer;
import org.objectweb.asm.tree.analysis.Frame;
import org.objectweb.asm.tree.analysis.SourceInterpreter;
import org.objectweb.asm.tree.analysis.SourceValue;

import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.StandardOpenOption;
import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Directizes the state-keyed PKCS5 delayed-string helper family whose outer
 * table uses a switch-shaped initializer.
 *
 * <p>This pass supplies only two facts to the existing strict helper proof:
 * an outer DES key bound to the exact state-field/XOR/local chain, and the
 * value of a static-final long written by that same proven state transform.
 * The shared helper proof still requires a unique outer table, exact helper
 * shape, constant call arguments, in-range table indices, successful inner
 * PKCS5 evaluation, closed support references, and verified class mutation.
 * Input classes are parsed only and are never loaded or initialized.</p>
 */
public final class ZkmPkcs5StateSwitchHelperDeobfuscator {
    private static final String PKCS5 = "DES/CBC/PKCS5Padding";
    private static final String HELPER_DESC = "(IJ)Ljava/lang/String;";
    private static final String STATE =
            ObfRuntimeNames.STATE;
    private static final String STATE_IFACE =
            ObfRuntimeNames.STATE_INTERFACE;

    private ZkmPkcs5StateSwitchHelperDeobfuscator() {
    }

    public static void main(String[] args) throws Exception {
        if (args.length < 2 || args.length > 3) {
            System.err.println("usage: ZkmPkcs5StateSwitchHelperDeobfuscator "
                    + "<input.jar> <report-dir> [output.jar]");
            System.exit(2);
        }
        ZkmDirectStringHelperDeobfuscator.Summary summary = rewrite(
                Paths.get(args[0]), Paths.get(args[1]),
                args.length == 3 ? Paths.get(args[2]) : null);
        System.out.println("candidates=" + summary.fieldTableCandidates
                + " proven=" + summary.provenClasses
                + " sites=" + summary.provenSites
                + " changed=" + summary.changedClasses
                + " pkcs5_removed=" + summary.pkcs5CallsRemoved
                + " rollbacks=" + summary.classRollbacks
                + " output_committed=" + summary.outputCommitted);
    }

    static ZkmDirectStringHelperDeobfuscator.Summary rewrite(
            Path input, Path reportDirectory, Path output) throws Exception {
        Map<String, ClassNode> classes = ZkmLongKeyEvaluator.readClasses(input);
        Map<String, ZkmDirectStringArrayDeobfuscator.StateKeyProof> classKeys =
                ZkmPkcs5StateArrayDeobfuscator.resolveClassKeyProofs(classes);
        Map<String, ZkmDirectStringHelperDeobfuscator.StateHelperProof> proofs =
                new LinkedHashMap<>();
        List<Row> rows = new ArrayList<>();
        for (ClassNode owner : classes.values()) {
            if (!hasPkcs5Helper(owner)) continue;
            Row row = inspect(owner, classKeys.get(owner.name));
            rows.add(row);
            if (row.proven) proofs.put(owner.name, row.proof);
        }

        ZkmDirectStringHelperDeobfuscator.Summary summary =
                ZkmDirectStringHelperDeobfuscator.rewriteWithStateProofs(
                        input, reportDirectory, output, proofs);
        writeProofs(reportDirectory, rows, classKeys.size());
        return summary;
    }

    static ZkmDirectStringHelperDeobfuscator.Summary rewriteWithProofs(
            Path input, Path reportDirectory, Path output,
            Map<String, ZkmDirectStringHelperDeobfuscator.StateHelperProof>
                    proofs) throws Exception {
        return ZkmDirectStringHelperDeobfuscator.rewriteWithStateProofs(
                input, reportDirectory, output, proofs);
    }

    private static Row inspect(
            ClassNode owner,
            ZkmDirectStringArrayDeobfuscator.StateKeyProof classProof) {
        Row row = new Row(owner.name);
        if (classProof == null) return row.reject("class-key-unproven");
        MethodNode clinit = method(owner, "<clinit>", "()V");
        if (clinit == null) return row.reject("missing-clinit");
        List<AbstractInsnNode> code = code(clinit);
        int factory = -1;
        int bootstraps = 0;
        int transforms = 0;
        MethodInsnNode transform = null;
        for (int index = 0; index < code.size(); index++) {
            AbstractInsnNode insn = code.get(index);
            if (isPkcs5Factory(insn)) {
                if (factory >= 0) return row.reject("pkcs5-factories-multiple");
                factory = index;
            }
            if (!(insn instanceof MethodInsnNode)) continue;
            MethodInsnNode call = (MethodInsnNode) insn;
            if (isStateBootstrap(call)) bootstraps++;
            if (isStateTransform(call)) {
                transforms++;
                transform = call;
            }
        }
        if (factory < 1) return row.reject("pkcs5-factory-missing");
        if (bootstraps != 1 || transforms != 1 || transform == null) {
            return row.reject("state-call-count=" + bootstraps + "/"
                    + transforms);
        }

        FieldInsnNode stateWrite = null;
        for (int index = 1; index < factory; index++) {
            AbstractInsnNode insn = code.get(index);
            if (!(insn instanceof FieldInsnNode)
                    || insn.getOpcode() != Opcodes.PUTSTATIC) continue;
            FieldInsnNode field = (FieldInsnNode) insn;
            if (!owner.name.equals(field.owner) || !"J".equals(field.desc)
                    || code.get(index - 1) != transform) continue;
            if (stateWrite != null) return row.reject("state-field-writes-multiple");
            FieldNode declaration = field(owner, field.name, field.desc);
            if (declaration == null
                    || (declaration.access
                    & (Opcodes.ACC_STATIC | Opcodes.ACC_FINAL))
                    != (Opcodes.ACC_STATIC | Opcodes.ACC_FINAL)) {
                return row.reject("state-field-not-static-final=" + field.name);
            }
            stateWrite = field;
        }
        if (stateWrite == null) return row.reject("state-field-write-missing");

        int keyStore = -1;
        for (int index = 1; index < factory; index++) {
            AbstractInsnNode insn = code.get(index);
            if (insn instanceof VarInsnNode
                    && insn.getOpcode() == Opcodes.LSTORE
                    && code.get(index - 1).getOpcode() == Opcodes.LXOR) {
                if (keyStore >= 0) return row.reject("outer-key-stores-multiple");
                keyStore = index;
            }
        }
        if (keyStore < 0) return row.reject("outer-key-store-missing");
        AbstractInsnNode xor = code.get(keyStore - 1);
        AbstractInsnNode left;
        AbstractInsnNode right;
        try {
            Frame<SourceValue>[] frames = new Analyzer<SourceValue>(
                    new SourceInterpreter()).analyze(owner.name, clinit);
            Frame<SourceValue> frame = frames[clinit.instructions.indexOf(xor)];
            if (frame == null || frame.getStackSize() < 2) {
                return row.reject("outer-key-xor-frame");
            }
            left = unique(frame.getStack(frame.getStackSize() - 2));
            right = unique(frame.getStack(frame.getStackSize() - 1));
        } catch (Throwable failure) {
            return row.reject("source-analysis=" + shortReason(failure));
        }
        LdcInsnNode maskNode = left instanceof LdcInsnNode
                && ((LdcInsnNode) left).cst instanceof Long
                ? (LdcInsnNode) left
                : right instanceof LdcInsnNode
                && ((LdcInsnNode) right).cst instanceof Long
                ? (LdcInsnNode) right : null;
        FieldInsnNode read = left instanceof FieldInsnNode
                && left.getOpcode() == Opcodes.GETSTATIC
                ? (FieldInsnNode) left
                : right instanceof FieldInsnNode
                && right.getOpcode() == Opcodes.GETSTATIC
                ? (FieldInsnNode) right : null;
        if (maskNode == null || read == null
                || !owner.name.equals(read.owner)
                || !stateWrite.name.equals(read.name)
                || !"J".equals(read.desc)) {
            return row.reject("outer-key-xor-sources");
        }
        int keyLocal = ((VarInsnNode) code.get(keyStore)).var;
        int keyLoads = 0;
        for (int index = factory + 1; index < code.size(); index++) {
            AbstractInsnNode insn = code.get(index);
            if (insn instanceof VarInsnNode
                    && insn.getOpcode() == Opcodes.LLOAD
                    && ((VarInsnNode) insn).var == keyLocal) keyLoads++;
            if (insn instanceof MethodInsnNode) {
                MethodInsnNode call = (MethodInsnNode) insn;
                if ("javax/crypto/spec/DESKeySpec".equals(call.owner)
                        && "<init>".equals(call.name)) break;
            }
        }
        if (keyLoads < 2) return row.reject("outer-key-loads=" + keyLoads);

        long mask = (Long) maskNode.cst;
        long outerKey = classProof.classKey ^ mask;
        OuterTable table;
        try {
            table = recoverOuterTable(owner, clinit, factory, outerKey);
        } catch (Throwable failure) {
            return row.reject("outer-table=" + shortReason(failure));
        }
        Map<String, Long> staticLongs = new LinkedHashMap<>();
        staticLongs.put(stateWrite.name, classProof.classKey);
        row.classKey = classProof.classKey;
        row.stateField = stateWrite.name;
        row.mask = mask;
        row.outerKey = outerKey;
        row.tableField = table.field;
        row.outerEntries = table.entries.size();
        row.source = classProof.source;
        row.proof = new ZkmDirectStringHelperDeobfuscator.StateHelperProof(
                owner.name, outerKey, staticLongs, table.field, table.entries,
                classProof.source + ";state-field/XOR/local-bound");
        row.proven = true;
        row.reason = "state-field/XOR/local-bound";
        return row;
    }

    private static OuterTable recoverOuterTable(
            ClassNode owner, MethodNode clinit, int factory, long outerKey)
            throws Exception {
        String tableField = helperTableField(owner);
        if (tableField == null) {
            throw new IllegalArgumentException("helper-table-field");
        }
        FieldNode declaration = field(owner, tableField,
                "[Ljava/lang/String;");
        if (declaration == null
                || (declaration.access & (Opcodes.ACC_STATIC | Opcodes.ACC_FINAL))
                != (Opcodes.ACC_STATIC | Opcodes.ACC_FINAL)) {
            throw new IllegalArgumentException("table-not-static-final="
                    + tableField);
        }
        List<AbstractInsnNode> code = code(clinit);
        int tableStore = -1;
        for (int index = factory + 1; index < code.size(); index++) {
            AbstractInsnNode insn = code.get(index);
            if (!(insn instanceof FieldInsnNode)
                    || insn.getOpcode() != Opcodes.PUTSTATIC) continue;
            FieldInsnNode field = (FieldInsnNode) insn;
            if (!owner.name.equals(field.owner)
                    || !tableField.equals(field.name)
                    || !"[Ljava/lang/String;".equals(field.desc)) continue;
            if (tableStore >= 0) {
                throw new IllegalArgumentException("table-stores-multiple");
            }
            tableStore = index;
        }
        if (tableStore < 0) throw new IllegalArgumentException("table-store");

        int capacity = -1;
        int allocationStore = -1;
        for (int index = factory + 1; index + 1 < tableStore; index++) {
            AbstractInsnNode insn = code.get(index);
            if (!(insn instanceof TypeInsnNode)
                    || insn.getOpcode() != Opcodes.ANEWARRAY
                    || !"java/lang/String".equals(
                    ((TypeInsnNode) insn).desc)) continue;
            Integer size = intConstant(code.get(index - 1));
            AbstractInsnNode store = code.get(index + 1);
            if (size == null || size <= 0
                    || !(store instanceof VarInsnNode)
                    || store.getOpcode() != Opcodes.ASTORE) continue;
            if (capacity >= 0) {
                throw new IllegalArgumentException("table-allocations-multiple");
            }
            capacity = size;
            allocationStore = index + 1;
        }
        if (capacity <= 0) throw new IllegalArgumentException("table-allocation");

        Map<String, Integer> calls = new LinkedHashMap<>();
        for (int index = factory; index < tableStore; index++) {
            AbstractInsnNode insn = code.get(index);
            if (insn instanceof MethodInsnNode) {
                MethodInsnNode call = (MethodInsnNode) insn;
                String id = call.owner + "." + call.name + call.desc;
                calls.put(id, calls.containsKey(id) ? calls.get(id) + 1 : 1);
            }
        }
        requireCall(calls, "javax/crypto/Cipher.getInstance"
                + "(Ljava/lang/String;)Ljavax/crypto/Cipher;");
        requireCall(calls, "javax/crypto/SecretKeyFactory.getInstance"
                + "(Ljava/lang/String;)Ljavax/crypto/SecretKeyFactory;");
        requireCall(calls, "javax/crypto/spec/DESKeySpec.<init>([B)V");
        requireCall(calls, "javax/crypto/SecretKeyFactory.generateSecret"
                + "(Ljava/security/spec/KeySpec;)Ljavax/crypto/SecretKey;");
        requireCall(calls, "javax/crypto/spec/IvParameterSpec.<init>([B)V");
        requireCall(calls, "javax/crypto/Cipher.init"
                + "(ILjava/security/Key;Ljava/security/spec/AlgorithmParameterSpec;)V");
        requireCall(calls, "javax/crypto/Cipher.doFinal([B)[B");

        List<PackedLiteral> packed = new ArrayList<>();
        // Switch-flattened variants can place a later packed literal after the
        // table PUTSTATIC in bytecode order and jump back into the shared
        // decrypt body. The literal header itself remains exact, so scan the
        // complete initializer rather than assuming source-order loops.
        for (int index = allocationStore + 1; index + 6 < code.size(); index++) {
            if (!(code.get(index) instanceof LdcInsnNode)
                    || !(((LdcInsnNode) code.get(index)).cst
                    instanceof String)) continue;
            String value = (String) ((LdcInsnNode) code.get(index)).cst;
            if (!(code.get(index + 1) instanceof VarInsnNode)
                    || code.get(index + 1).getOpcode() != Opcodes.ASTORE
                    || !(code.get(index + 2) instanceof LdcInsnNode)
                    || !value.equals(((LdcInsnNode) code.get(index + 2)).cst)
                    || !isCall(code.get(index + 3), "java/lang/String",
                    "length", "()I")
                    || !(code.get(index + 4) instanceof VarInsnNode)
                    || code.get(index + 4).getOpcode() != Opcodes.ISTORE
                    || !(code.get(index + 6) instanceof VarInsnNode)
                    || code.get(index + 6).getOpcode() != Opcodes.ISTORE) {
                continue;
            }
            Integer initial = intConstant(code.get(index + 5));
            if (initial == null || initial <= 0 || (initial & 7) != 0) {
                continue;
            }
            ZkmDesConstantEvaluator.latin1Bytes(value);
            packed.add(new PackedLiteral(value, initial));
        }
        if (packed.isEmpty()) {
            throw new IllegalArgumentException("packed-literals=0");
        }
        List<String> entries = new ArrayList<>();
        List<String> packedShape = new ArrayList<>();
        ZkmDesConstantEvaluator.KeyMaterial key =
                ZkmDesConstantEvaluator.KeyMaterial.proven(outerKey,
                        "STATE_FIELD_XOR", owner.name + "." + tableField);
        for (PackedLiteral literal : packed) {
            List<String> decoded = ZkmDesConstantEvaluator.decryptPackedStrings(
                    key, literal.value, literal.initialLength);
            entries.addAll(decoded);
            packedShape.add(literal.value.length() + ":"
                    + literal.initialLength + ":" + decoded.size());
        }
        if (entries.size() != capacity) {
            throw new IllegalArgumentException("table-capacity="
                    + entries.size() + "/" + capacity + ",packed="
                    + packedShape);
        }
        for (String entry : entries) {
            ZkmDesConstantEvaluator.latin1Bytes(entry);
            if (entry.isEmpty() || (entry.length() & 7) != 0) {
                throw new IllegalArgumentException("inner-ciphertext-length="
                        + entry.length());
            }
        }
        return new OuterTable(tableField, entries);
    }

    private static String helperTableField(ClassNode owner) {
        Set<String> fields = new LinkedHashSet<>();
        for (MethodNode method : owner.methods) {
            if (!HELPER_DESC.equals(method.desc)) continue;
            List<AbstractInsnNode> code = code(method);
            for (int index = 0; index < code.size(); index++) {
                AbstractInsnNode insn = code.get(index);
                if (!(insn instanceof FieldInsnNode)
                        || insn.getOpcode() != Opcodes.GETSTATIC) continue;
                FieldInsnNode field = (FieldInsnNode) insn;
                if (!owner.name.equals(field.owner)
                        || !"[Ljava/lang/String;".equals(field.desc)) continue;
                for (int next = index + 1;
                     next < code.size() && next <= index + 10; next++) {
                    if (isCall(code.get(next), "java/lang/String", "getBytes",
                            "(Ljava/lang/String;)[B")) {
                        fields.add(field.name);
                        break;
                    }
                    if (code.get(next) instanceof FieldInsnNode) break;
                }
            }
        }
        return fields.size() == 1 ? fields.iterator().next() : null;
    }

    private static void requireCall(Map<String, Integer> calls, String id) {
        if (!Integer.valueOf(1).equals(calls.get(id))) {
            throw new IllegalArgumentException("outer-call=" + id + ":"
                    + calls.get(id));
        }
    }

    private static boolean isCall(AbstractInsnNode insn, String owner,
                                  String name, String desc) {
        if (!(insn instanceof MethodInsnNode)) return false;
        MethodInsnNode call = (MethodInsnNode) insn;
        return owner.equals(call.owner) && name.equals(call.name)
                && desc.equals(call.desc);
    }

    private static Integer intConstant(AbstractInsnNode insn) {
        if (insn == null) return null;
        int opcode = insn.getOpcode();
        if (opcode >= Opcodes.ICONST_M1 && opcode <= Opcodes.ICONST_5) {
            return opcode - Opcodes.ICONST_0;
        }
        if (insn instanceof org.objectweb.asm.tree.IntInsnNode
                && (opcode == Opcodes.BIPUSH || opcode == Opcodes.SIPUSH)) {
            return ((org.objectweb.asm.tree.IntInsnNode) insn).operand;
        }
        if (insn instanceof LdcInsnNode
                && ((LdcInsnNode) insn).cst instanceof Integer) {
            return (Integer) ((LdcInsnNode) insn).cst;
        }
        return null;
    }

    private static boolean hasPkcs5Helper(ClassNode owner) {
        for (MethodNode method : owner.methods) {
            if (!HELPER_DESC.equals(method.desc)) continue;
            for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
                 insn = insn.getNext()) {
                if (isPkcs5Factory(insn)) return true;
            }
        }
        return false;
    }

    private static boolean isPkcs5Factory(AbstractInsnNode insn) {
        if (!(insn instanceof MethodInsnNode)) return false;
        MethodInsnNode call = (MethodInsnNode) insn;
        AbstractInsnNode previous = previousCode(insn);
        return call.getOpcode() == Opcodes.INVOKESTATIC
                && "javax/crypto/Cipher".equals(call.owner)
                && "getInstance".equals(call.name)
                && "(Ljava/lang/String;)Ljavax/crypto/Cipher;".equals(call.desc)
                && previous instanceof LdcInsnNode
                && PKCS5.equals(((LdcInsnNode) previous).cst);
    }

    private static boolean isStateBootstrap(MethodInsnNode call) {
        return call.getOpcode() == Opcodes.INVOKESTATIC
                && STATE.equals(call.owner) && "a".equals(call.name)
                && ObfRuntimeNames.BOOTSTRAP_DESC
                .equals(call.desc);
    }

    private static boolean isStateTransform(MethodInsnNode call) {
        return call.getOpcode() == Opcodes.INVOKEINTERFACE
                && STATE_IFACE.equals(call.owner) && "a".equals(call.name)
                && "(J)J".equals(call.desc);
    }

    private static AbstractInsnNode unique(SourceValue value) {
        if (value == null || value.insns == null || value.insns.size() != 1) {
            return null;
        }
        return value.insns.iterator().next();
    }

    private static List<AbstractInsnNode> code(MethodNode method) {
        List<AbstractInsnNode> result = new ArrayList<>();
        for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
             insn = insn.getNext()) {
            if (insn.getOpcode() >= 0) result.add(insn);
        }
        return result;
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

    private static AbstractInsnNode previousCode(AbstractInsnNode node) {
        AbstractInsnNode cursor = node == null ? null : node.getPrevious();
        while (cursor != null && cursor.getOpcode() < 0) cursor = cursor.getPrevious();
        return cursor;
    }

    private static void writeProofs(Path reportDirectory, List<Row> rows,
                                    int classKeys) throws Exception {
        List<String> proofRows = new ArrayList<>();
        proofRows.add("class\tclass_key_hex\tstate_field\touter_mask_hex"
                + "\touter_key_hex\ttable_field\touter_entries\tsource"
                + "\tproven\treason");
        int proven = 0;
        for (Row row : rows) {
            proofRows.add(row.tsv());
            if (row.proven) proven++;
        }
        Files.write(reportDirectory.resolve("state-helper-proofs.tsv"),
                proofRows, StandardCharsets.UTF_8);
        List<String> audit = new ArrayList<>();
        audit.add("state_class_key_proofs=" + classKeys);
        audit.add("state_helper_candidates=" + rows.size());
        audit.add("state_helper_proofs=" + proven);
        audit.add("key_binding=state-field/XOR/local-chain");
        audit.add("input_classes_loaded=false");
        audit.add("input_classes_initialized=false");
        Files.write(reportDirectory.resolve("audit.txt"), audit,
                StandardCharsets.UTF_8, StandardOpenOption.APPEND);
    }

    private static String shortReason(Throwable failure) {
        String value = failure.getClass().getSimpleName() + ":"
                + String.valueOf(failure.getMessage());
        return value.replace('\t', ' ').replace('\r', ' ')
                .replace('\n', ' ');
    }

    private static String hex(long value) {
        return String.format("%016X", value);
    }

    private static final class Row {
        final String owner;
        long classKey;
        String stateField = "";
        long mask;
        long outerKey;
        String tableField = "";
        int outerEntries;
        String source = "";
        boolean proven;
        String reason = "";
        ZkmDirectStringHelperDeobfuscator.StateHelperProof proof;

        Row(String owner) {
            this.owner = owner;
        }

        Row reject(String reason) {
            this.reason = reason;
            return this;
        }

        String tsv() {
            return String.join("\t", owner,
                    proven ? hex(classKey) : "", stateField,
                    proven ? hex(mask) : "",
                    proven ? hex(outerKey) : "", tableField,
                    Integer.toString(outerEntries), source,
                    Boolean.toString(proven), reason);
        }
    }

    private static final class PackedLiteral {
        final String value;
        final int initialLength;

        PackedLiteral(String value, int initialLength) {
            this.value = value;
            this.initialLength = initialLength;
        }
    }

    private static final class OuterTable {
        final String field;
        final List<String> entries;

        OuterTable(String field, List<String> entries) {
            this.field = field;
            this.entries = Collections.unmodifiableList(
                    new ArrayList<>(entries));
        }
    }
}
