package cn.openvape.flowdeobf;

import org.objectweb.asm.Opcodes;
import org.objectweb.asm.tree.AbstractInsnNode;
import org.objectweb.asm.tree.FieldInsnNode;
import org.objectweb.asm.tree.FieldNode;
import org.objectweb.asm.tree.JumpInsnNode;
import org.objectweb.asm.tree.LdcInsnNode;
import org.objectweb.asm.tree.MethodNode;

import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * Folds ZKM opaque-predicate fields that are written once in {@code <clinit>}
 * (or never written and therefore default) and then used as {@code IFEQ}/
 * {@code IFNE}/{@code IFNULL}/{@code IFNONNULL} guards.
 */
public final class ZkmOpaquePredicateDeobfuscator {
    private ZkmOpaquePredicateDeobfuscator() {
    }

    public static void main(String[] args) throws Exception {
        if (args.length != 2 && args.length != 3) {
            System.err.println("usage: ZkmOpaquePredicateDeobfuscator <input.jar> <report-dir> [output.jar]");
            System.exit(2);
        }
        rewrite(Paths.get(args[0]), Paths.get(args[1]),
                args.length == 3 ? Paths.get(args[2]) : null);
    }

    static Summary rewrite(Path input, Path reportDirectory, Path output)
            throws Exception {
        Files.createDirectories(reportDirectory);
        ZkmArchiveIo.validatePaths(input, output);
        List<ZkmArchiveIo.EntryBytes> entries = ZkmArchiveIo.readEntries(input);
        Map<String, byte[]> original = ZkmArchiveIo.classBytes(entries);
        Map<String, org.objectweb.asm.tree.ClassNode> classes =
                ZkmArchiveIo.readClasses(original);
        Map<String, Predicate> predicates = collectPredicates(classes);
        Summary summary = new Summary();
        summary.parsedClasses = original.size();
        summary.predicates = predicates.size();
        List<String> rows = new ArrayList<String>();
        rows.add("class\tmethod\toffset\taction\treason");
        Map<String, byte[]> replacements = new LinkedHashMap<String, byte[]>();

        for (Map.Entry<String, byte[]> entry : original.entrySet()) {
            final int[] rewritten = {0};
            ZkmClassRewriteTransaction.Result result = ZkmClassRewriteTransaction.attempt(
                    entry.getValue(),
                    new ZkmClassRewriteTransaction.Mutation() {
                        @Override
                        public void apply(org.objectweb.asm.tree.ClassNode owner) {
                            rewritten[0] = fold(owner, predicates, rows);
                        }
                    },
                    new ZkmClassRewriteTransaction.Postcondition() {
                        @Override
                        public void verify(org.objectweb.asm.tree.ClassNode owner) {
                        }
                    });
            if (!result.isCommitted()) {
                summary.rollbacks++;
                rows.add(ZkmArchiveIo.tsv(entry.getKey(), "<class>", "-1", "rollback",
                        result.reason()));
                continue;
            }
            if (rewritten[0] == 0) continue;
            replacements.put(entry.getKey(), result.bytes());
            summary.changedClasses++;
            summary.sitesRewritten += rewritten[0];
        }

        ZkmArchiveIo.writeText(reportDirectory.resolve("rewrite.tsv"), rows);
        if (output != null) {
            ZkmArchiveIo.writeArchive(entries, replacements, output);
            summary.outputCommitted = true;
        }
        ZkmArchiveIo.writeText(reportDirectory.resolve("audit.txt"), Arrays.asList(
                "parsed_classes=" + summary.parsedClasses,
                "predicates=" + summary.predicates,
                "changed_classes=" + summary.changedClasses,
                "sites_rewritten=" + summary.sitesRewritten,
                "rollbacks=" + summary.rollbacks,
                "output_committed=" + summary.outputCommitted,
                "input_classes_loaded=false",
                "input_classes_initialized=false"));
        return summary;
    }

    private static Map<String, Predicate> collectPredicates(
            Map<String, org.objectweb.asm.tree.ClassNode> classes) {
        Map<String, Integer> writes = new HashMap<String, Integer>();
        Map<String, Boolean> nonzero = new HashMap<String, Boolean>();
        Map<String, String> types = new HashMap<String, String>();
        for (org.objectweb.asm.tree.ClassNode owner : classes.values()) {
            for (FieldNode field : owner.fields) {
                if ((field.access & Opcodes.ACC_STATIC) == 0) continue;
                if (!isPredicateType(field.desc)) continue;
                String key = owner.name + "." + field.name;
                types.put(key, field.desc);
                writes.put(key, 0);
                nonzero.put(key, Boolean.FALSE);
            }
            for (MethodNode method : owner.methods) {
                if (method.instructions == null) continue;
                for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
                     insn = insn.getNext()) {
                    if (!(insn instanceof FieldInsnNode)
                            || insn.getOpcode() != Opcodes.PUTSTATIC) {
                        continue;
                    }
                    FieldInsnNode field = (FieldInsnNode) insn;
                    String key = field.owner + "." + field.name;
                    if (!types.containsKey(key)) continue;
                    writes.put(key, writes.get(key) + 1);
                    nonzero.put(key, isNonZeroStore(field));
                }
            }
        }
        Map<String, Predicate> result = new LinkedHashMap<String, Predicate>();
        for (Map.Entry<String, String> type : types.entrySet()) {
            Integer count = writes.get(type.getKey());
            if (count != null && count > 1) continue;
            Predicate predicate = new Predicate();
            predicate.key = type.getKey();
            predicate.desc = type.getValue();
            predicate.nonzero = Boolean.TRUE.equals(nonzero.get(type.getKey()));
            result.put(type.getKey(), predicate);
        }
        return result;
    }

    private static boolean isPredicateType(String desc) {
        return "I".equals(desc) || "Z".equals(desc)
                || "Ljava/lang/String;".equals(desc)
                || desc.startsWith("[");
    }

    private static boolean isNonZeroStore(FieldInsnNode field) {
        AbstractInsnNode prev = ZkmArchiveIo.previousCode(field);
        if (prev == null) return false;
        Integer value = ZkmArchiveIo.intConstant(prev);
        if (value != null) return value.intValue() != 0;
        if (prev.getOpcode() == Opcodes.ACONST_NULL) return false;
        if (prev instanceof LdcInsnNode) return ((LdcInsnNode) prev).cst != null;
        if (prev.getOpcode() == Opcodes.NEW
                || prev.getOpcode() == Opcodes.ANEWARRAY
                || prev.getOpcode() == Opcodes.NEWARRAY
                || prev.getOpcode() == Opcodes.MULTIANEWARRAY) {
            return true;
        }
        return false;
    }

    private static int fold(org.objectweb.asm.tree.ClassNode owner,
                            Map<String, Predicate> predicates, List<String> rows) {
        int count = 0;
        for (MethodNode method : owner.methods) {
            if (method.instructions == null) continue;
            AbstractInsnNode insn = method.instructions.getFirst();
            int offset = 0;
            while (insn != null) {
                AbstractInsnNode next = insn.getNext();
                if (insn instanceof FieldInsnNode
                        && insn.getOpcode() == Opcodes.GETSTATIC) {
                    FieldInsnNode field = (FieldInsnNode) insn;
                    Predicate predicate = predicates.get(field.owner + "." + field.name);
                    if (predicate != null) {
                        AbstractInsnNode consumer = findUnaryConsumer(field);
                        if (consumer instanceof JumpInsnNode) {
                            Boolean taken = taken(predicate, consumer.getOpcode());
                            if (taken != null) {
                                if (taken.booleanValue()) {
                                    method.instructions.insert(consumer,
                                            new JumpInsnNode(Opcodes.GOTO,
                                                    ((JumpInsnNode) consumer).label));
                                }
                                method.instructions.remove(field);
                                method.instructions.remove(consumer);
                                rows.add(ZkmArchiveIo.tsv(owner.name,
                                        method.name + method.desc,
                                        Integer.toString(offset),
                                        taken.booleanValue() ? "zkm-fold-opaque-goto"
                                                : "zkm-fold-opaque-fallthrough",
                                        predicate.key + "=" + (predicate.nonzero ? "set" : "unset")));
                                count++;
                            }
                        } else if (consumer != null && isStore(consumer)) {
                            method.instructions.insert(field,
                                    ZkmArchiveIo.pushInt(predicate.nonzero ? 1 : 0));
                            method.instructions.remove(field);
                            rows.add(ZkmArchiveIo.tsv(owner.name,
                                    method.name + method.desc,
                                    Integer.toString(offset),
                                    "zkm-materialize-opaque",
                                    predicate.key + "=" + (predicate.nonzero ? "1" : "0")));
                            count++;
                        }
                    }
                }
                insn = next;
                offset++;
            }
        }
        return count;
    }

    private static AbstractInsnNode findUnaryConsumer(AbstractInsnNode start) {
        AbstractInsnNode cursor = ZkmArchiveIo.nextCode(start);
        int depth = 1;
        int steps = 0;
        while (cursor != null && steps < 16 && depth > 0) {
            int change = stackChange(cursor);
            if (depth + Math.min(change, 0) == 0 && isUnaryConsumer(cursor)) {
                return cursor;
            }
            depth += change;
            if (depth <= 0) break;
            cursor = ZkmArchiveIo.nextCode(cursor);
            steps++;
        }
        return null;
    }

    private static boolean isUnaryConsumer(AbstractInsnNode insn) {
        int opcode = insn.getOpcode();
        return insn instanceof JumpInsnNode
                && (opcode == Opcodes.IFEQ || opcode == Opcodes.IFNE
                || opcode == Opcodes.IFNULL || opcode == Opcodes.IFNONNULL)
                || isStore(insn);
    }

    private static boolean isStore(AbstractInsnNode insn) {
        int opcode = insn.getOpcode();
        return opcode == Opcodes.ISTORE || opcode == Opcodes.ASTORE;
    }

    private static int stackChange(AbstractInsnNode insn) {
        int opcode = insn.getOpcode();
        if (opcode == Opcodes.DUP) return 1;
        if (opcode == Opcodes.POP) return -1;
        if (opcode == Opcodes.SWAP) return 0;
        if (ZkmArchiveIo.intConstant(insn) != null) return 1;
        if (insn instanceof org.objectweb.asm.tree.TypeInsnNode
                && opcode == Opcodes.NEW) return 1;
        if (insn instanceof org.objectweb.asm.tree.MethodInsnNode) {
            org.objectweb.asm.tree.MethodInsnNode call =
                    (org.objectweb.asm.tree.MethodInsnNode) insn;
            int args = org.objectweb.asm.Type.getArgumentCount(call.desc);
            if (opcode != Opcodes.INVOKESTATIC) args++;
            int ret = org.objectweb.asm.Type.getReturnType(call.desc).getSize();
            if (org.objectweb.asm.Type.getReturnType(call.desc)
                    == org.objectweb.asm.Type.VOID_TYPE) ret = 0;
            return ret - args;
        }
        if (opcode == Opcodes.ISTORE || opcode == Opcodes.ASTORE) return -1;
        if (insn instanceof JumpInsnNode) return -1;
        return 0;
    }

    private static Boolean taken(Predicate predicate, int opcode) {
        boolean set = predicate.nonzero;
        switch (opcode) {
            case Opcodes.IFNE:
            case Opcodes.IFNONNULL:
                return set;
            case Opcodes.IFEQ:
            case Opcodes.IFNULL:
                return !set;
            default:
                return null;
        }
    }

    private static final class Predicate {
        String key;
        String desc;
        boolean nonzero;
    }

    static final class Summary {
        int parsedClasses;
        int predicates;
        int changedClasses;
        int sitesRewritten;
        int rollbacks;
        boolean outputCommitted;
    }
}
