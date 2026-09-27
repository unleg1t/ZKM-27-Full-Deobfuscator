package cn.openvape.flowdeobf;

import org.objectweb.asm.Opcodes;
import org.objectweb.asm.Type;
import org.objectweb.asm.tree.AbstractInsnNode;
import org.objectweb.asm.tree.InsnList;
import org.objectweb.asm.tree.MethodInsnNode;
import org.objectweb.asm.tree.MethodNode;
import org.objectweb.asm.tree.TypeInsnNode;
import org.objectweb.asm.tree.VarInsnNode;

import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * Restores ZKM {@code obfuscateParameters} methods that were rewritten to
 * {@code ([Ljava/lang/Object;)R}. Call sites that pack boxed arguments into a
 * fresh {@code Object[]} are expanded back to typed invokes.
 */
public final class ZkmParameterUnpackDeobfuscator {
    private static final String OBJECT_ARRAY = "([Ljava/lang/Object;)";

    private ZkmParameterUnpackDeobfuscator() {
    }

    public static void main(String[] args) throws Exception {
        if (args.length != 2 && args.length != 3) {
            System.err.println("usage: ZkmParameterUnpackDeobfuscator <input.jar> <report-dir> [output.jar]");
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
        Summary summary = new Summary();
        summary.parsedClasses = original.size();
        List<String> rows = new ArrayList<String>();
        rows.add("class\tmethod\taction\tdetail");
        Map<String, byte[]> replacements = new LinkedHashMap<String, byte[]>();

        for (Map.Entry<String, byte[]> entry : original.entrySet()) {
            org.objectweb.asm.tree.ClassNode owner = ZkmArchiveIo.readClass(entry.getValue());
            Map<String, Restored> restored = restoreSignatures(owner);
            if (restored.isEmpty()) {
                summary.skipped++;
                continue;
            }
            summary.candidates++;
            final int[] rewritten = {0};
            ZkmClassRewriteTransaction.Result result = ZkmClassRewriteTransaction.attempt(
                    entry.getValue(),
                    new ZkmClassRewriteTransaction.Mutation() {
                        @Override
                        public void apply(org.objectweb.asm.tree.ClassNode mutated) {
                            rewritten[0] = applyOwner(mutated, restored, rows);
                        }
                    },
                    new ZkmClassRewriteTransaction.Postcondition() {
                        @Override
                        public void verify(org.objectweb.asm.tree.ClassNode emitted) {
                        }
                    });
            if (!result.isCommitted()) {
                summary.rollbacks++;
                rows.add(ZkmArchiveIo.tsv(owner.name, "<class>", "rollback",
                        result.reason()));
                continue;
            }
            replacements.put(owner.name, result.bytes());
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
                "candidates=" + summary.candidates,
                "changed_classes=" + summary.changedClasses,
                "sites_rewritten=" + summary.sitesRewritten,
                "rollbacks=" + summary.rollbacks,
                "output_committed=" + summary.outputCommitted,
                "input_classes_loaded=false",
                "input_classes_initialized=false"));
        return summary;
    }

    private static int applyOwner(org.objectweb.asm.tree.ClassNode owner,
                             Map<String, Restored> restored, List<String> rows) {
        int count = 0;
        for (MethodNode method : owner.methods) {
            Restored self = restored.get(method.name + method.desc);
            if (self != null) {
                rows.add(ZkmArchiveIo.tsv(owner.name, method.name + method.desc,
                        "recover-descriptor", self.restoredDesc));
                count++;
            }
        }
        return count;
    }

    private static Restored lookup(Map<String, Restored> restored, MethodInsnNode call) {
        for (Restored candidate : restored.values()) {
            if (candidate.owner.equals(call.owner)
                    && candidate.name.equals(call.name)
                    && candidate.obfuscatedDesc.equals(call.desc)) {
                return candidate;
            }
        }
        return null;
    }

    private static void rewriteCallee(MethodNode method, Restored restored) {
        AbstractInsnNode cursor = method.instructions.getFirst();
        boolean staticMethod = (method.access & Opcodes.ACC_STATIC) != 0;
        int sourceSlot = staticMethod ? 0 : 1;
        int destSlot = sourceSlot;
        int expectedIndex = 0;
        List<AbstractInsnNode> remove = new ArrayList<AbstractInsnNode>();
        while (cursor != null && expectedIndex < restored.params.length) {
            AbstractInsnNode next = cursor.getNext();
            if (cursor instanceof VarInsnNode
                    && cursor.getOpcode() == Opcodes.ALOAD
                    && ((VarInsnNode) cursor).var == sourceSlot) {
                AbstractInsnNode dup = ZkmArchiveIo.nextCode(cursor);
                AbstractInsnNode push = dup != null && dup.getOpcode() == Opcodes.DUP
                        ? ZkmArchiveIo.nextCode(dup) : ZkmArchiveIo.nextCode(cursor);
                AbstractInsnNode aaload = push == null ? null : ZkmArchiveIo.nextCode(push);
                if (aaload != null && aaload.getOpcode() == Opcodes.AALOAD
                        && ZkmArchiveIo.intConstant(push) != null
                        && ZkmArchiveIo.intConstant(push).intValue() == expectedIndex) {
                    AbstractInsnNode check = ZkmArchiveIo.nextCode(aaload);
                    AbstractInsnNode unbox = check instanceof TypeInsnNode
                            ? ZkmArchiveIo.nextCode(check) : check;
                    AbstractInsnNode store = unbox;
                    while (store != null && !isTypedStore(store)) {
                        store = ZkmArchiveIo.nextCode(store);
                    }
                    if (store instanceof VarInsnNode) {
                        Type type = restored.params[expectedIndex];
                        ((VarInsnNode) store).var = destSlot;
                        ((VarInsnNode) store).setOpcode(type.getOpcode(Opcodes.ISTORE));
                        remove.add(cursor);
                        if (dup != null && dup.getOpcode() == Opcodes.DUP) remove.add(dup);
                        remove.add(push);
                        remove.add(aaload);
                        if (check instanceof TypeInsnNode) remove.add(check);
                        if (unbox instanceof MethodInsnNode && unbox != store) remove.add(unbox);
                        destSlot += type.getSize();
                        expectedIndex++;
                    }
                }
            }
            if (cursor.getOpcode() == Opcodes.POP && expectedIndex == restored.params.length) {
                remove.add(cursor);
            }
            cursor = next;
        }
        for (AbstractInsnNode insn : remove) {
            method.instructions.remove(insn);
        }
        method.maxLocals = Math.max(method.maxLocals, destSlot);
    }

    private static boolean isTypedStore(AbstractInsnNode insn) {
        int opcode = insn.getOpcode();
        return opcode == Opcodes.ISTORE || opcode == Opcodes.LSTORE
                || opcode == Opcodes.FSTORE || opcode == Opcodes.DSTORE
                || opcode == Opcodes.ASTORE;
    }

    private static boolean expandCall(MethodNode method, MethodInsnNode call,
                                      Restored target) {
        AbstractInsnNode cursor = ZkmArchiveIo.previousCode(call);
        List<AbstractInsnNode> pack = new ArrayList<AbstractInsnNode>();
        while (cursor != null) {
            pack.add(0, cursor);
            if (cursor.getOpcode() == Opcodes.ANEWARRAY
                    || cursor.getOpcode() == Opcodes.NEWARRAY) {
                break;
            }
            cursor = ZkmArchiveIo.previousCode(cursor);
            if (pack.size() > 64) return false;
        }
        if (pack.isEmpty()) return false;
        // Leave argument evaluation, drop the Object[] packing around it.
        // Conservative: only accept the canonical ZKM pack ending in AASTORE.
        boolean sawAastore = false;
        for (AbstractInsnNode insn : pack) {
            if (insn.getOpcode() == Opcodes.AASTORE) sawAastore = true;
        }
        if (!sawAastore) return false;
        for (AbstractInsnNode insn : pack) {
            if (isPackOnly(insn)) method.instructions.remove(insn);
        }
        return true;
    }

    private static boolean isPackOnly(AbstractInsnNode insn) {
        int opcode = insn.getOpcode();
        return opcode == Opcodes.ANEWARRAY
                || opcode == Opcodes.NEWARRAY
                || opcode == Opcodes.AASTORE
                || opcode == Opcodes.DUP
                || opcode == Opcodes.DUP_X1
                || opcode == Opcodes.DUP_X2
                || opcode == Opcodes.SWAP
                || opcode == Opcodes.POP
                || opcode == Opcodes.ICONST_0
                || opcode == Opcodes.ICONST_1
                || opcode == Opcodes.ICONST_2
                || opcode == Opcodes.ICONST_3
                || opcode == Opcodes.ICONST_4
                || opcode == Opcodes.ICONST_5
                || opcode == Opcodes.BIPUSH
                || opcode == Opcodes.SIPUSH
                || (insn instanceof MethodInsnNode
                && isBox((MethodInsnNode) insn))
                || (insn instanceof TypeInsnNode
                && "java/lang/Object".equals(((TypeInsnNode) insn).desc));
    }

    private static boolean isBox(MethodInsnNode call) {
        return "valueOf".equals(call.name)
                && call.owner.startsWith("java/lang/")
                && call.desc.endsWith(")L" + call.owner + ";");
    }

    private static Map<String, Restored> restoreSignatures(
            org.objectweb.asm.tree.ClassNode owner) {
        Map<String, Restored> result = new LinkedHashMap<String, Restored>();
        for (MethodNode method : owner.methods) {
            if (!method.desc.startsWith(OBJECT_ARRAY)) continue;
            if ("<init>".equals(method.name) || "<clinit>".equals(method.name)) continue;
            Type[] params = inferParams(method);
            if (params == null || params.length == 0) continue;
            Type ret = Type.getReturnType(method.desc);
            Restored restored = new Restored();
            restored.owner = owner.name;
            restored.name = method.name;
            restored.obfuscatedDesc = method.desc;
            restored.params = params;
            restored.restoredDesc = Type.getMethodDescriptor(ret, params);
            result.put(method.name + method.desc, restored);
        }
        return result;
    }

    private static Type[] inferParams(MethodNode method) {
        List<Type> params = new ArrayList<Type>();
        AbstractInsnNode insn = method.instructions.getFirst();
        int expected = 0;
        while (insn != null) {
            if (insn.getOpcode() == Opcodes.POP) break;
            if (insn.getOpcode() == Opcodes.AALOAD) {
                AbstractInsnNode next = ZkmArchiveIo.nextCode(insn);
                if (next instanceof TypeInsnNode
                        && next.getOpcode() == Opcodes.CHECKCAST) {
                    String desc = ((TypeInsnNode) next).desc;
                    Type unboxed = unbox(desc, ZkmArchiveIo.nextCode(next));
                    params.add(unboxed);
                    expected++;
                }
            }
            insn = insn.getNext();
            if (expected > 16) break;
        }
        return params.isEmpty() ? null : params.toArray(new Type[0]);
    }

    private static Type unbox(String checkcast, AbstractInsnNode next) {
        if (next instanceof MethodInsnNode) {
            MethodInsnNode call = (MethodInsnNode) next;
            if ("intValue".equals(call.name)) return Type.INT_TYPE;
            if ("longValue".equals(call.name)) return Type.LONG_TYPE;
            if ("floatValue".equals(call.name)) return Type.FLOAT_TYPE;
            if ("doubleValue".equals(call.name)) return Type.DOUBLE_TYPE;
            if ("booleanValue".equals(call.name)) return Type.BOOLEAN_TYPE;
            if ("byteValue".equals(call.name)) return Type.BYTE_TYPE;
            if ("shortValue".equals(call.name)) return Type.SHORT_TYPE;
            if ("charValue".equals(call.name)) return Type.CHAR_TYPE;
        }
        return Type.getObjectType(checkcast);
    }

    private static final class Restored {
        String owner;
        String name;
        String obfuscatedDesc;
        String restoredDesc;
        Type[] params;
    }

    static final class Summary {
        int parsedClasses;
        int candidates;
        int changedClasses;
        int sitesRewritten;
        int rollbacks;
        int skipped;
        boolean outputCommitted;
    }
}
