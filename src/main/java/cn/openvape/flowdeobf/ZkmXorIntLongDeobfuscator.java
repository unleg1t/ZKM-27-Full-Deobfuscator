package cn.openvape.flowdeobf;

import org.objectweb.asm.Opcodes;
import org.objectweb.asm.tree.AbstractInsnNode;
import org.objectweb.asm.tree.FieldInsnNode;
import org.objectweb.asm.tree.LdcInsnNode;
import org.objectweb.asm.tree.MethodInsnNode;
import org.objectweb.asm.tree.MethodNode;

import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * Recovers ZKM XOR integer {@code (IJ)I} and long {@code (IJ)J} lookup
 * helpers. The packed ISO-8859-1 table is XOR'd with the class key from
 * {@code <clinit>}; each call site supplies the per-value key.
 */
public final class ZkmXorIntLongDeobfuscator {
    private ZkmXorIntLongDeobfuscator() {
    }

    public static void main(String[] args) throws Exception {
        if (args.length != 2 && args.length != 3) {
            System.err.println("usage: ZkmXorIntLongDeobfuscator <input.jar> <report-dir> [output.jar]");
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
        rows.add("class\tmethod\tkind\tvalue\treason");
        Map<String, byte[]> replacements = new LinkedHashMap<String, byte[]>();

        for (Map.Entry<String, byte[]> entry : original.entrySet()) {
            org.objectweb.asm.tree.ClassNode owner = ZkmArchiveIo.readClass(entry.getValue());
            List<Helper> helpers = findHelpers(owner);
            if (helpers.isEmpty()) {
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
                            rewritten[0] = rewriteOwner(mutated, helpers, rows);
                        }
                    },
                    new ZkmClassRewriteTransaction.Postcondition() {
                        @Override
                        public void verify(org.objectweb.asm.tree.ClassNode emitted) {
                            if (rewritten[0] == 0) {
                                throw new IllegalStateException("no-int-long-sites");
                            }
                        }
                    });
            if (!result.isCommitted()) {
                summary.rollbacks++;
                rows.add(ZkmArchiveIo.tsv(owner.name, "<class>", "rollback", "",
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

    private static int rewriteOwner(org.objectweb.asm.tree.ClassNode owner,
                                    List<Helper> helpers, List<String> rows) {
        int count = 0;
        for (Helper helper : helpers) {
            for (MethodNode method : owner.methods) {
                if (helper.name.equals(method.name) && helper.desc.equals(method.desc)) {
                    continue;
                }
                AbstractInsnNode insn = method.instructions.getFirst();
                while (insn != null) {
                    AbstractInsnNode next = insn.getNext();
                    if (insn instanceof MethodInsnNode) {
                        MethodInsnNode call = (MethodInsnNode) insn;
                        if (owner.name.equals(call.owner)
                                && helper.name.equals(call.name)
                                && helper.desc.equals(call.desc)) {
                            AbstractInsnNode longNode = ZkmArchiveIo.previousCode(call);
                            AbstractInsnNode intNode = longNode == null
                                    ? null : ZkmArchiveIo.previousCode(longNode);
                            Integer encoded = ZkmArchiveIo.intConstant(intNode);
                            Long key = ZkmArchiveIo.longConstant(longNode);
                            if (encoded != null && key != null) {
                                int index = helper.index(encoded, key);
                                if (index >= 0 && index < helper.table.length) {
                                    long decoded = helper.table[index] ^ key;
                                    method.instructions.insertBefore(intNode,
                                            helper.wide
                                                    ? ZkmArchiveIo.pushLong(decoded)
                                                    : ZkmArchiveIo.pushInt((int) decoded));
                                    method.instructions.remove(intNode);
                                    method.instructions.remove(longNode);
                                    method.instructions.remove(call);
                                    rows.add(ZkmArchiveIo.tsv(owner.name,
                                            method.name + method.desc,
                                            helper.wide ? "long" : "int",
                                            helper.wide ? Long.toString(decoded)
                                                    : Integer.toString((int) decoded),
                                            "index=" + index));
                                    count++;
                                }
                            }
                        }
                    }
                    insn = next;
                }
            }
        }
        return count;
    }

    private static List<Helper> findHelpers(org.objectweb.asm.tree.ClassNode owner) {
        List<Helper> helpers = new ArrayList<Helper>();
        MethodNode clinit = ZkmArchiveIo.method(owner, "<clinit>", "()V");
        if (clinit == null) return helpers;
        for (MethodNode method : owner.methods) {
            boolean wide = "(IJ)J".equals(method.desc);
            boolean narrow = "(IJ)I".equals(method.desc);
            if (!wide && !narrow) continue;
            Helper helper = parseHelper(method, clinit, wide);
            if (helper != null) helpers.add(helper);
        }
        return helpers;
    }

    private static Helper parseHelper(MethodNode method, MethodNode clinit, boolean wide) {
        Integer indexXor = null;
        String tableField = null;
        boolean and32767 = false;
        boolean useLongLow = false;
        int xorCount = 0;
        for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
             insn = insn.getNext()) {
            if (insn.getOpcode() == Opcodes.LAND) {
                Long mask = ZkmArchiveIo.longConstant(ZkmArchiveIo.previousCode(insn));
                if (mask != null && mask.longValue() == 32767L) and32767 = true;
            }
            if (insn.getOpcode() == Opcodes.IAND) {
                Integer mask = ZkmArchiveIo.intConstant(ZkmArchiveIo.previousCode(insn));
                if (mask != null && mask.intValue() == 32767) and32767 = true;
            }
            if (insn.getOpcode() == Opcodes.L2I) useLongLow = true;
            if (insn.getOpcode() == Opcodes.IXOR) {
                xorCount++;
                Integer mask = ZkmArchiveIo.intConstant(ZkmArchiveIo.previousCode(insn));
                if (mask != null) indexXor = mask;
            }
            if (insn instanceof FieldInsnNode
                    && insn.getOpcode() == Opcodes.GETSTATIC
                    && "[J".equals(((FieldInsnNode) insn).desc)
                    && tableField == null) {
                tableField = ((FieldInsnNode) insn).name;
            }
        }
        if (indexXor == null || tableField == null) return null;
        long[] table = extractLongTable(clinit, tableField);
        if (table == null || table.length == 0) return null;
        Helper helper = new Helper();
        helper.name = method.name;
        helper.desc = method.desc;
        helper.wide = wide;
        helper.indexXor = indexXor;
        helper.and32767 = and32767;
        helper.useLongLow = useLongLow;
        helper.table = table;
        return helper;
    }

    private static long[] extractLongTable(MethodNode clinit, String fieldName) {
        Long classKey = null;
        String packed = null;
        for (AbstractInsnNode insn = clinit.instructions.getFirst(); insn != null;
             insn = insn.getNext()) {
            Long value = ZkmArchiveIo.longConstant(insn);
            if (value != null && insn.getNext() != null
                    && insn.getNext().getOpcode() == Opcodes.LSTORE) {
                classKey = value;
                packed = null;
            }
            if (insn instanceof LdcInsnNode && ((LdcInsnNode) insn).cst instanceof String) {
                String literal = (String) ((LdcInsnNode) insn).cst;
                if (literal.length() >= 8 && literal.length() % 8 == 0) {
                    packed = packed == null ? literal : packed + literal;
                }
            }
            if (insn instanceof FieldInsnNode
                    && insn.getOpcode() == Opcodes.PUTSTATIC
                    && fieldName.equals(((FieldInsnNode) insn).name)) {
                break;
            }
        }
        if (classKey == null || packed == null) return null;
        byte[] raw;
        try {
            raw = packed.getBytes("ISO-8859-1");
        } catch (Exception failure) {
            raw = packed.getBytes(StandardCharsets.ISO_8859_1);
        }
        if (raw.length % 8 != 0) return null;
        long[] table = new long[raw.length / 8];
        for (int i = 0; i < table.length; i++) {
            long word = 0L;
            for (int b = 0; b < 8; b++) {
                word = (word << 8) | (raw[i * 8 + b] & 255L);
            }
            table[i] = word ^ classKey;
        }
        return table;
    }

    private static final class Helper {
        String name;
        String desc;
        boolean wide;
        int indexXor;
        boolean and32767;
        boolean useLongLow;
        long[] table;

        int index(int encoded, long key) {
            int mixed = encoded;
            if (useLongLow && and32767) {
                mixed ^= (int) (key & 32767L);
            } else if (useLongLow) {
                mixed ^= (int) key;
            }
            mixed ^= indexXor;
            if (and32767 && !(useLongLow && and32767 && tableWideMask())) {
                mixed &= 32767;
            }
            if (!useLongLow && and32767) mixed &= 32767;
            return mixed & 0x7FFF;
        }

        private boolean tableWideMask() {
            return wide;
        }
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
