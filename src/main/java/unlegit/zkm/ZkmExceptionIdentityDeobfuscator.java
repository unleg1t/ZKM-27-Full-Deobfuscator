package unlegit.zkm;

import org.objectweb.asm.Opcodes;
import org.objectweb.asm.Type;
import org.objectweb.asm.tree.AbstractInsnNode;
import org.objectweb.asm.tree.MethodInsnNode;
import org.objectweb.asm.tree.MethodNode;
import org.objectweb.asm.tree.TryCatchBlockNode;
import org.objectweb.asm.tree.VarInsnNode;

import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Inlines ZKM exception-identity helpers {@code (LType;)LType;} whose body is
 * {@code ALOAD_0; ARETURN}, then drops empty {@code ATHROW} dummy handlers.
 */
public final class ZkmExceptionIdentityDeobfuscator {
    private ZkmExceptionIdentityDeobfuscator() {
    }

    public static void main(String[] args) throws Exception {
        if (args.length != 2 && args.length != 3) {
            System.err.println("usage: ZkmExceptionIdentityDeobfuscator <input.jar> <report-dir> [output.jar]");
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
        rows.add("class\tmethod\taction\treason");
        Map<String, byte[]> replacements = new LinkedHashMap<String, byte[]>();

        for (Map.Entry<String, byte[]> entry : original.entrySet()) {
            org.objectweb.asm.tree.ClassNode owner = ZkmArchiveIo.readClass(entry.getValue());
            Set<String> identities = findIdentities(owner);
            if (identities.isEmpty() && !hasDummyHandlers(owner)) {
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
                            rewritten[0] = applyOwner(mutated, identities, rows);
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
            if (rewritten[0] == 0) continue;
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
                             Set<String> identities, List<String> rows) {
        int count = 0;
        Set<String> stillUsed = new HashSet<String>();
        for (MethodNode method : owner.methods) {
            if (method.instructions == null) continue;
            AbstractInsnNode insn = method.instructions.getFirst();
            while (insn != null) {
                AbstractInsnNode next = insn.getNext();
                if (insn instanceof MethodInsnNode) {
                    MethodInsnNode call = (MethodInsnNode) insn;
                    if (owner.name.equals(call.owner)
                            && identities.contains(call.name + call.desc)) {
                        method.instructions.remove(call);
                        rows.add(ZkmArchiveIo.tsv(owner.name,
                                method.name + method.desc,
                                "inline-identity", call.name + call.desc));
                        count++;
                    } else if (owner.name.equals(call.owner)) {
                        stillUsed.add(call.name + call.desc);
                    }
                }
                insn = next;
            }
            count += dropDummyHandlers(owner, method, rows);
        }
        if (!identities.isEmpty()) {
            List<MethodNode> keep = new ArrayList<MethodNode>();
            for (MethodNode method : owner.methods) {
                String key = method.name + method.desc;
                if (identities.contains(key) && !stillUsed.contains(key)) {
                    rows.add(ZkmArchiveIo.tsv(owner.name, key, "remove-identity",
                            "unused"));
                    count++;
                    continue;
                }
                keep.add(method);
            }
            owner.methods = keep;
        }
        return count;
    }

    private static int dropDummyHandlers(org.objectweb.asm.tree.ClassNode owner,
                                         MethodNode method, List<String> rows) {
        if (method.tryCatchBlocks == null || method.tryCatchBlocks.isEmpty()) return 0;
        List<TryCatchBlockNode> keep = new ArrayList<TryCatchBlockNode>();
        int removed = 0;
        for (TryCatchBlockNode block : method.tryCatchBlocks) {
            if (isDummyAthrow(block)) {
                rows.add(ZkmArchiveIo.tsv(owner.name, method.name + method.desc,
                        "drop-dummy-handler",
                        block.type == null ? "java/lang/Throwable" : block.type));
                removed++;
            } else {
                keep.add(block);
            }
        }
        method.tryCatchBlocks = keep;
        return removed;
    }

    private static boolean isDummyAthrow(TryCatchBlockNode block) {
        AbstractInsnNode cursor = block.handler;
        while (cursor != null && cursor.getOpcode() < 0) cursor = cursor.getNext();
        return cursor != null && cursor.getOpcode() == Opcodes.ATHROW;
    }

    private static boolean hasDummyHandlers(org.objectweb.asm.tree.ClassNode owner) {
        for (MethodNode method : owner.methods) {
            if (method.tryCatchBlocks == null) continue;
            for (TryCatchBlockNode block : method.tryCatchBlocks) {
                if (isDummyAthrow(block)) return true;
            }
        }
        return false;
    }

    private static Set<String> findIdentities(org.objectweb.asm.tree.ClassNode owner) {
        Set<String> result = new HashSet<String>();
        for (MethodNode method : owner.methods) {
            if ((method.access & Opcodes.ACC_STATIC) == 0) continue;
            Type type = Type.getMethodType(method.desc);
            if (type.getArgumentTypes().length != 1) continue;
            if (!type.getReturnType().equals(type.getArgumentTypes()[0])) continue;
            if (!isIdentityBody(method)) continue;
            result.add(method.name + method.desc);
        }
        return result;
    }

    private static boolean isIdentityBody(MethodNode method) {
        AbstractInsnNode first = firstCode(method);
        if (first == null || first.getOpcode() != Opcodes.ALOAD) return false;
        if (!(first instanceof VarInsnNode) || ((VarInsnNode) first).var != 0) return false;
        AbstractInsnNode second = ZkmArchiveIo.nextCode(first);
        return second != null && second.getOpcode() == Opcodes.ARETURN;
    }

    private static AbstractInsnNode firstCode(MethodNode method) {
        if (method.instructions == null) return null;
        AbstractInsnNode insn = method.instructions.getFirst();
        while (insn != null && insn.getOpcode() < 0) insn = insn.getNext();
        return insn;
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
