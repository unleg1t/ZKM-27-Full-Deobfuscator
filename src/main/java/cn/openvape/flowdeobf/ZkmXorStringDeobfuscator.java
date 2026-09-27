package cn.openvape.flowdeobf;

import org.objectweb.asm.Opcodes;
import org.objectweb.asm.tree.AbstractInsnNode;
import org.objectweb.asm.tree.FieldInsnNode;
import org.objectweb.asm.tree.FieldNode;
import org.objectweb.asm.tree.InsnNode;
import org.objectweb.asm.tree.LdcInsnNode;
import org.objectweb.asm.tree.MethodInsnNode;
import org.objectweb.asm.tree.MethodNode;
import org.objectweb.asm.tree.TableSwitchInsnNode;
import org.objectweb.asm.tree.LabelNode;

import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * Recovers ZKM 7-key XOR string tables and (II) rolling-XOR lookup helpers.
 * Input classes are never defined or executed.
 */
public final class ZkmXorStringDeobfuscator {
    private ZkmXorStringDeobfuscator() {
    }

    public static void main(String[] args) throws Exception {
        if (args.length != 2 && args.length != 3) {
            System.err.println("usage: ZkmXorStringDeobfuscator <input.jar> <report-dir> [output.jar]");
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
        rows.add("class\tmethod\taction\tplaintext\treason");
        Map<String, byte[]> replacements = new LinkedHashMap<String, byte[]>();

        for (Map.Entry<String, byte[]> entry : original.entrySet()) {
            org.objectweb.asm.tree.ClassNode owner = ZkmArchiveIo.readClass(entry.getValue());
            Model model = Model.build(owner);
            if (model == null) {
                summary.skipped++;
                continue;
            }
            summary.candidates++;
            ZkmClassRewriteTransaction.Result result = ZkmClassRewriteTransaction.attempt(
                    entry.getValue(),
                    new Apply(model),
                    new Post(model));
            if (!result.isCommitted()) {
                summary.rollbacks++;
                rows.add(ZkmArchiveIo.tsv(owner.name, "<class>", "rollback", "",
                        result.reason()));
                continue;
            }
            replacements.put(owner.name, result.bytes());
            summary.changedClasses++;
            summary.stringsRecovered += model.plainByIndex.size();
            summary.sitesRewritten += model.rewrittenSites;
            for (Map.Entry<Integer, String> plaintext : model.plainByIndex.entrySet()) {
                rows.add(ZkmArchiveIo.tsv(owner.name, "<table>", "recover",
                        printable(plaintext.getValue()),
                        "index=" + plaintext.getKey()));
            }
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
                "strings_recovered=" + summary.stringsRecovered,
                "sites_rewritten=" + summary.sitesRewritten,
                "rollbacks=" + summary.rollbacks,
                "output_committed=" + summary.outputCommitted,
                "input_classes_loaded=false",
                "input_classes_initialized=false"));
        return summary;
    }

    private static final class Apply implements ZkmClassRewriteTransaction.Mutation {
        private final Model model;

        private Apply(Model model) {
            this.model = model;
        }

        @Override
        public void apply(org.objectweb.asm.tree.ClassNode owner) {
            model.rewrittenSites = 0;
            if (!model.plainByIndex.isEmpty() && model.tableField != null) {
                rewriteArrayLoads(owner, model);
            }
            if (model.lookup != null) {
                rewriteLookupCalls(owner, model);
            }
        }
    }

    private static final class Post implements ZkmClassRewriteTransaction.Postcondition {
        private final Model model;

        private Post(Model model) {
            this.model = model;
        }

        @Override
        public void verify(org.objectweb.asm.tree.ClassNode owner) {
            if (model.rewrittenSites == 0) {
                throw new IllegalStateException("no-sites-rewritten");
            }
        }
    }

    private static void rewriteArrayLoads(org.objectweb.asm.tree.ClassNode owner,
                                          Model model) {
        for (MethodNode method : owner.methods) {
            AbstractInsnNode insn = method.instructions.getFirst();
            while (insn != null) {
                AbstractInsnNode next = insn.getNext();
                if (insn instanceof FieldInsnNode
                        && insn.getOpcode() == Opcodes.GETSTATIC) {
                    FieldInsnNode field = (FieldInsnNode) insn;
                    if (owner.name.equals(field.owner)
                            && model.tableField.equals(field.name)
                            && "[Ljava/lang/String;".equals(field.desc)) {
                        AbstractInsnNode afterGet = ZkmArchiveIo.nextCode(field);
                        AbstractInsnNode push = afterGet;
                        AbstractInsnNode load;
                        List<AbstractInsnNode> extra = new ArrayList<AbstractInsnNode>();
                        if (afterGet != null && afterGet.getOpcode() == Opcodes.ASTORE) {
                            extra.add(afterGet);
                            AbstractInsnNode reload = ZkmArchiveIo.nextCode(afterGet);
                            if (reload != null && reload.getOpcode() == Opcodes.ALOAD) {
                                extra.add(reload);
                                push = ZkmArchiveIo.nextCode(reload);
                            }
                        }
                        load = push == null ? null : ZkmArchiveIo.nextCode(push);
                        Integer slot = ZkmArchiveIo.intConstant(push);
                        if (slot != null && load != null
                                && load.getOpcode() == Opcodes.AALOAD
                                && model.plainByIndex.containsKey(slot)) {
                            AbstractInsnNode after = load.getNext();
                            method.instructions.insertBefore(field,
                                    new LdcInsnNode(model.plainByIndex.get(slot)));
                            method.instructions.remove(field);
                            for (AbstractInsnNode node : extra) {
                                method.instructions.remove(node);
                            }
                            method.instructions.remove(push);
                            method.instructions.remove(load);
                            model.rewrittenSites++;
                            insn = after;
                            continue;
                        }
                    }
                }
                insn = next;
            }
        }
    }

    private static void rewriteLookupCalls(org.objectweb.asm.tree.ClassNode owner,
                                           Model model) {
        LookupModel lookup = model.lookup;
        for (MethodNode method : owner.methods) {
            if (lookup.name.equals(method.name) && lookup.desc.equals(method.desc)) {
                continue;
            }
            AbstractInsnNode insn = method.instructions.getFirst();
            while (insn != null) {
                AbstractInsnNode next = insn.getNext();
                if (insn instanceof MethodInsnNode) {
                    MethodInsnNode call = (MethodInsnNode) insn;
                    if (owner.name.equals(call.owner)
                            && lookup.name.equals(call.name)
                            && lookup.desc.equals(call.desc)) {
                        AbstractInsnNode second = ZkmArchiveIo.previousCode(call);
                        AbstractInsnNode first = second == null
                                ? null : ZkmArchiveIo.previousCode(second);
                        Integer encoded = ZkmArchiveIo.intConstant(first);
                        Integer packedKey = ZkmArchiveIo.intConstant(second);
                        if (encoded != null && packedKey != null) {
                            int slot = (encoded ^ lookup.indexXorKey) & 0xFFFF;
                            String ciphertext = model.cipherByIndex.get(slot);
                            if (ciphertext != null) {
                            String plain = decryptLookup(ciphertext, packedKey, lookup);
                            if (isPrintableRecovered(plain)) {
                            AbstractInsnNode after = call.getNext();
                            method.instructions.insertBefore(first, new LdcInsnNode(plain));
                            method.instructions.remove(first);
                            method.instructions.remove(second);
                            method.instructions.remove(call);
                            model.plainByIndex.put(slot, plain);
                            model.rewrittenSites++;
                            insn = after;
                            continue;
                            }
                            }
                        }
                    }
                }
                insn = next;
            }
        }
    }

    private static String decryptLookup(String ciphertext, int packedKey,
                                        LookupModel lookup) {
        int first = ciphertext.isEmpty() ? 0 : ciphertext.charAt(0) & 255;
        int offset = lookup.shuffle[first];
        int key0 = (packedKey & 255) - offset;
        int key1 = ((packedKey >>> 8) & 255) - offset;
        if (key0 < 0) key0 += 256;
        if (key1 < 0) key1 += 256;
        return rollingXorDecrypt(ciphertext, new int[] {key0, key1});
    }

    private static String rollingXorDecrypt(String value, int[] keys) {
        int[] state = Arrays.copyOf(keys, keys.length);
        char[] chars = value.toCharArray();
        for (int i = 0; i < chars.length; i++) {
            int slot = i % state.length;
            chars[i] = (char) (chars[i] ^ state[slot]);
            int mixed = state[slot] >>> 3 | state[slot] << 5;
            mixed ^= chars[i];
            state[slot] = mixed & 255;
        }
        return new String(chars);
    }

    private static final class Model {
        String tableField;
        Map<Integer, String> plainByIndex = new LinkedHashMap<Integer, String>();
        Map<Integer, String> cipherByIndex = new LinkedHashMap<Integer, String>();
        LookupModel lookup;
        int rewrittenSites;

        static Model build(org.objectweb.asm.tree.ClassNode owner) {
            Model model = new Model();
            int[] seven = findSevenKeys(owner);
            MethodNode clinit = ZkmArchiveIo.method(owner, "<clinit>", "()V");
            if (seven != null && clinit != null) {
                List<String> recovered = unpackPacked(clinit, seven);
                if (!recovered.isEmpty()) {
                    model.tableField = findStringArrayField(owner, clinit);
                    for (int i = 0; i < recovered.size(); i++) {
                        model.cipherByIndex.put(i, recovered.get(i));
                    }
                }
            }
            model.lookup = LookupModel.parse(owner);
            if (model.lookup == null && !hasLookupHelper(owner)) {
                for (Map.Entry<Integer, String> item : model.cipherByIndex.entrySet()) {
                    if (isPrintableRecovered(item.getValue())) {
                        model.plainByIndex.put(item.getKey(), item.getValue());
                    }
                }
            }
            if (model.plainByIndex.isEmpty() && model.lookup == null) return null;
            return model;
        }
    }

    private static int[] findSevenKeys(org.objectweb.asm.tree.ClassNode owner) {
        for (MethodNode method : owner.methods) {
            int[] keys = extractSevenKeys(method);
            if (keys != null) return keys;
        }
        return null;
    }

    private static int[] extractSevenKeys(MethodNode method) {
        if (method.instructions == null) return null;
        for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
             insn = insn.getNext()) {
            if (!(insn instanceof TableSwitchInsnNode)) continue;
            TableSwitchInsnNode table = (TableSwitchInsnNode) insn;
            if (table.min != 0 || table.labels.size() != 6) continue;
            int[] keys = new int[7];
            boolean ok = true;
            for (int i = 0; i < 6; i++) {
                Integer value = firstInt(table.labels.get(i));
                if (value == null) {
                    ok = false;
                    break;
                }
                keys[i] = value;
            }
            Integer last = firstInt(table.dflt);
            if (!ok || last == null) continue;
            keys[6] = last;
            return keys;
        }
        return null;
    }

    private static Integer firstInt(LabelNode label) {
        AbstractInsnNode cursor = label;
        while (cursor != null) {
            Integer value = ZkmArchiveIo.intConstant(cursor);
            if (value != null) return value;
            if (cursor.getOpcode() >= 0 && cursor.getOpcode() != Opcodes.GOTO) break;
            cursor = cursor.getNext();
        }
        return null;
    }

    private static List<String> unpackPacked(MethodNode clinit, int[] keys) {
        List<String> packed = new ArrayList<String>();
        for (AbstractInsnNode insn = clinit.instructions.getFirst(); insn != null;
             insn = insn.getNext()) {
            if (insn instanceof LdcInsnNode && ((LdcInsnNode) insn).cst instanceof String) {
                String value = (String) ((LdcInsnNode) insn).cst;
                if (value.length() >= 4) packed.add(value);
            }
        }
        List<String> recovered = new ArrayList<String>();
        for (String chunk : packed) recovered.addAll(unpackXorChunk(chunk, keys));
        return recovered;
    }

    private static List<String> unpackXorChunk(String packed, int[] keys) {
        List<String> result = new ArrayList<String>();
        int firstLen = inferFirstLength(packed, keys);
        if (firstLen <= 0 || firstLen > packed.length()) return result;
        result.add(xorWithKeys(packed.substring(0, firstLen), keys));
        int cursor = firstLen;
        while (cursor < packed.length()) {
            int length = packed.charAt(cursor);
            cursor++;
            if (length <= 0 || cursor + length > packed.length()) break;
            result.add(xorWithKeys(packed.substring(cursor, cursor + length), keys));
            cursor += length;
        }
        return result;
    }

    private static int inferFirstLength(String packed, int[] keys) {
        int printableMatch = -1;
        int structuralMatch = -1;
        for (int length = 1; length <= packed.length(); length++) {
            int cursor = length;
            boolean ok = true;
            boolean printable = isPrintableRecovered(
                    xorWithKeys(packed.substring(0, length), keys));
            while (cursor < packed.length()) {
                int next = packed.charAt(cursor);
                cursor++;
                if (next <= 0 || cursor + next > packed.length()) {
                    ok = false;
                    break;
                }
                if (!isPrintableRecovered(
                        xorWithKeys(packed.substring(cursor, cursor + next), keys))) {
                    printable = false;
                }
                cursor += next;
            }
            if (ok && cursor == packed.length()) {
                if (structuralMatch < 0) structuralMatch = length;
                if (printable) {
                    printableMatch = length;
                    break;
                }
            }
        }
        return printableMatch > 0 ? printableMatch : structuralMatch;
    }

    private static boolean isPrintableRecovered(String value) {
        if (value == null || value.isEmpty() || value.length() > 512) return false;
        int printable = 0;
        for (int i = 0; i < value.length(); i++) {
            char ch = value.charAt(i);
            if (ch == 9 || ch == 10 || ch == 13 || (ch >= 32 && ch < 127)) printable++;
        }
        return printable * 4 >= value.length() * 3;
    }

    private static String xorWithKeys(String value, int[] keys) {
        char[] chars = value.toCharArray();
        for (int i = 0; i < chars.length; i++) {
            chars[i] = (char) (chars[i] ^ keys[i % keys.length]);
        }
        return new String(chars);
    }

    private static boolean hasLookupHelper(org.objectweb.asm.tree.ClassNode owner) {
        for (MethodNode method : owner.methods) {
            if ("(II)Ljava/lang/String;".equals(method.desc)
                    || "(III)Ljava/lang/String;".equals(method.desc)) {
                return true;
            }
        }
        return false;
    }

    private static String findStringArrayField(org.objectweb.asm.tree.ClassNode owner,
                                               MethodNode clinit) {
        for (AbstractInsnNode insn = clinit.instructions.getFirst(); insn != null;
             insn = insn.getNext()) {
            if (insn instanceof FieldInsnNode && insn.getOpcode() == Opcodes.PUTSTATIC) {
                FieldInsnNode field = (FieldInsnNode) insn;
                if (owner.name.equals(field.owner)
                        && "[Ljava/lang/String;".equals(field.desc)) {
                    return field.name;
                }
            }
        }
        for (FieldNode field : owner.fields) {
            if ("[Ljava/lang/String;".equals(field.desc)
                    && (field.access & Opcodes.ACC_STATIC) != 0) {
                return field.name;
            }
        }
        return null;
    }

    private static final class LookupModel {
        String name;
        String desc;
        int indexXorKey;
        int[] shuffle = new int[256];

        static LookupModel parse(org.objectweb.asm.tree.ClassNode owner) {
            for (MethodNode method : owner.methods) {
                if (!"(II)Ljava/lang/String;".equals(method.desc)
                        && !"(III)Ljava/lang/String;".equals(method.desc)) {
                    continue;
                }
                LookupModel model = new LookupModel();
                model.name = method.name;
                model.desc = method.desc;
                boolean sawXor = false;
                boolean sawShuffle = false;
                for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
                     insn = insn.getNext()) {
                    if (insn.getOpcode() == Opcodes.IXOR && !sawXor) {
                        Integer mask = ZkmArchiveIo.intConstant(ZkmArchiveIo.previousCode(insn));
                        if (mask != null) {
                            model.indexXorKey = mask;
                            sawXor = true;
                        }
                    }
                    if (insn instanceof TableSwitchInsnNode) {
                        TableSwitchInsnNode table = (TableSwitchInsnNode) insn;
                        if (table.min == 0 && table.labels.size() >= 254) {
                            int count = table.labels.size();
                            boolean ok = true;
                            for (int i = 0; i < count; i++) {
                                Integer value = firstInt(table.labels.get(i));
                                if (value == null) {
                                    ok = false;
                                    break;
                                }
                                if (i < 256) model.shuffle[i] = value;
                            }
                            Integer last = firstInt(table.dflt);
                            if (ok && last != null) {
                                if (count < 256) model.shuffle[count] = last;
                                else model.shuffle[255] = last;
                                sawShuffle = true;
                            }
                        }
                    }
                }
                if (sawXor && sawShuffle) return model;
            }
            return null;
        }
    }

    private static String printable(String value) {
        return value.replace('\t', ' ').replace('\n', ' ').replace('\r', ' ');
    }

    static final class Summary {
        int parsedClasses;
        int candidates;
        int changedClasses;
        int stringsRecovered;
        int sitesRewritten;
        int rollbacks;
        int skipped;
        boolean outputCommitted;
    }
}
