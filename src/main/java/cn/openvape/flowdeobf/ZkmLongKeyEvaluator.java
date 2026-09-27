package cn.openvape.flowdeobf;

import org.objectweb.asm.ClassReader;
import org.objectweb.asm.Opcodes;
import org.objectweb.asm.tree.AbstractInsnNode;
import org.objectweb.asm.tree.ClassNode;
import org.objectweb.asm.tree.FieldInsnNode;
import org.objectweb.asm.tree.IntInsnNode;
import org.objectweb.asm.tree.LdcInsnNode;
import org.objectweb.asm.tree.MethodInsnNode;
import org.objectweb.asm.tree.MethodNode;
import org.objectweb.asm.tree.TypeInsnNode;
import org.objectweb.asm.tree.VarInsnNode;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.zip.ZipEntry;
import java.util.zip.ZipInputStream;

/**
 * Static evaluator for the long-key state graph used by this ZKM-protected archive.
 * Input classes are parsed as data and are never defined or initialized.
 */
public final class ZkmLongKeyEvaluator {
    private static final String STATE = ObfRuntimeNames.STATE;
    private static final String GRAPH = ObfRuntimeNames.GRAPH_BOOTSTRAP;
    private static final String STATE_INTERFACE = ObfRuntimeNames.STATE_INTERFACE;
    private static final String BOOTSTRAP_DESC =
            ObfRuntimeNames.BOOTSTRAP_DESC;
    private static final boolean DIAGNOSTIC_IGNORE_MAP_HASH =
            Boolean.getBoolean("zkm.model.ignoreMapHash");
    private static final boolean DIAGNOSTIC_REVERSE_INITIAL_MAP =
            Boolean.getBoolean("zkm.model.reverseInitialMap");
    private static final boolean DIAGNOSTIC_DESCENDING_SORT =
            Boolean.getBoolean("zkm.model.descendingSort");

    private ZkmLongKeyEvaluator() {
    }

    public static void main(String[] args) throws Exception {
        if (args.length != 2) {
            System.err.println("usage: ZkmLongKeyEvaluator <input.jar> <output-dir>");
            System.exit(2);
        }
        evaluate(Paths.get(args[0]), Paths.get(args[1]));
    }

    static EvaluationSummary evaluate(Path input, Path outputDirectory) throws Exception {
        Files.createDirectories(outputDirectory);
        Map<String, ClassNode> classes = readClasses(input);
        ClassNode stateClass = requireClass(classes, STATE);
        ClassNode graphClass = requireClass(classes, GRAPH);
        BuildStats buildStats = new BuildStats();
        Model base = buildModel(stateClass, graphClass, buildStats);

        List<KeySite> sites = findKeySites(classes);
        List<String> rows = new ArrayList<>();
        rows.add("class\tmethod\tinstruction\tseed_a\tseed_b\ttransform_input\tkey\tkey_hex\tstatus");
        EvaluationSummary summary = new EvaluationSummary();
        summary.parsedClasses = classes.size();
        summary.keySites = sites.size();
        for (KeySite site : sites) {
            try {
                Model work = base.copy();
                long key = work.evaluate(site.seedA, site.seedB, site.transformInput);
                rows.add(site.owner + "\t" + site.method + "\t" + site.instruction + "\t"
                        + site.seedA + "\t" + site.seedB + "\t" + site.transformInput + "\t"
                        + key + "\t" + String.format(Locale.ROOT, "%016X", key) + "\tOK");
                summary.evaluatedKeys++;
            } catch (Throwable failure) {
                rows.add(site.owner + "\t" + site.method + "\t" + site.instruction + "\t"
                        + site.seedA + "\t" + site.seedB + "\t" + site.transformInput
                        + "\t\t\tERROR:" + sanitize(shortReason(failure)));
                summary.failedKeys++;
            }
        }
        rows.subList(1, rows.size()).sort(Comparator.naturalOrder());
        Files.write(outputDirectory.resolve("keys.tsv"), rows, StandardCharsets.UTF_8);

        List<String> audit = new ArrayList<>();
        audit.add("input=" + input.toAbsolutePath());
        audit.add("parsed_classes=" + summary.parsedClasses);
        audit.add("population_states=" + buildStats.populationStates);
        audit.add("population_permutations=" + buildStats.populationPermutations);
        audit.add("population_clones=" + buildStats.populationClones);
        audit.add("map_puts=" + buildStats.mapPuts);
        audit.add("auxiliary_map_puts=" + buildStats.auxiliaryMapPuts);
        audit.add("map_entries=" + base.mapEntries.size());
        audit.add("permutation_targets=" + buildStats.permutationTargets);
        audit.add("permutation_writes=" + buildStats.permutationWrites);
        audit.add("chain_links=" + buildStats.chainLinks);
        audit.add("delta_sets=" + buildStats.deltaSets);
        audit.add("model_states=" + base.states.size());
        audit.add("model_limit=" + base.limit);
        audit.add("key_sites=" + summary.keySites);
        audit.add("evaluated_keys=" + summary.evaluatedKeys);
        audit.add("failed_keys=" + summary.failedKeys);
        audit.add("input_classes_loaded=false");
        Files.write(outputDirectory.resolve("audit.txt"), audit, StandardCharsets.UTF_8);
        Files.write(outputDirectory.resolve("gate.txt"),
                (summary.failedKeys == 0 && summary.evaluatedKeys == summary.keySites ? "PASS\n" : "FAIL\n")
                        .getBytes(StandardCharsets.UTF_8));
        System.out.println("key_sites=" + summary.keySites + " evaluated=" + summary.evaluatedKeys
                + " failed=" + summary.failedKeys + " states=" + base.states.size()
                + " report=" + outputDirectory);
        return summary;
    }

    static Map<String, Long> evaluateClassKeys(Map<String, ClassNode> classes) {
        ClassNode stateClass = requireClass(classes, STATE);
        ClassNode graphClass = requireClass(classes, GRAPH);
        Model base = buildModel(stateClass, graphClass, new BuildStats());
        Map<String, Long> result = new LinkedHashMap<>();
        for (KeySite site : findKeySites(classes)) {
            Long previous = result.put(site.owner,
                    base.copy().evaluate(site.seedA, site.seedB, site.transformInput));
            if (previous != null) {
                throw new IllegalStateException("multiple class-key bootstraps in " + site.owner);
            }
        }
        return result;
    }

    static Map<String, Long> evaluateClassKeysSequential(Map<String, ClassNode> classes) {
        ClassNode stateClass = requireClass(classes, STATE);
        ClassNode graphClass = requireClass(classes, GRAPH);
        Model work = buildModel(stateClass, graphClass, new BuildStats());
        Map<String, Long> result = new LinkedHashMap<>();
        for (KeySite site : findKeySites(classes)) {
            Long previous = result.put(site.owner,
                    work.evaluate(site.seedA, site.seedB, site.transformInput));
            if (previous != null) {
                throw new IllegalStateException("multiple class-key bootstraps in " + site.owner);
            }
        }
        return result;
    }

    static StatefulKeySequence newStatefulKeySequence(Map<String, ClassNode> classes) {
        Model model = buildModel(requireClass(classes, STATE), requireClass(classes, GRAPH),
                new BuildStats());
        Map<String, KeySite> sites = new LinkedHashMap<>();
        for (KeySite site : findKeySites(classes)) {
            if (sites.put(site.owner, site) != null) {
                throw new IllegalStateException("multiple class-key bootstraps in " + site.owner);
            }
        }
        return new StatefulKeySequence(model, sites);
    }

    private static Model buildModel(ClassNode stateClass, ClassNode graphClass, BuildStats stats) {
        Model model = new Model();
        populateStates(model, requireMethod(stateClass, "a0", "()V"), stats);
        populateStates(model, requireMethod(stateClass, "a1", "()V"), stats);
        if (model.currentPermutation == null || model.states.isEmpty()) {
            throw new IllegalStateException("state population was not recovered");
        }

        model.limit = model.states.size();
        model.sortStates();
        populateGraphMap(model, requireMethod(graphClass, "b0", "()V"), stats);
        model.graphPermutation = readMethodIntArray(requireMethod(graphClass, "<init>", "()V"));
        requirePermutation(model.graphPermutation, "graph permutation");

        // ZkmLongKeyState.a(graph): freeze the post-map limit, sort, then graph.d().
        model.limit = model.states.size();
        model.sortStates();
        modifyStatePermutations(model, requireMethod(graphClass, "c0", "()V"), stats);

        // ZkmLongKeyState.b(graph): sort again, replace the global permutation, then graph.c().
        model.sortStates();
        model.currentPermutation = readMethodIntArray(
                requireMethod(stateClass, "b", "(L" + GRAPH + ";)V"));
        requirePermutation(model.currentPermutation, "post-graph global permutation");
        processGraphActions(model, requireMethod(graphClass, "d0", "()V"), stats);
        processGraphActions(model, requireMethod(graphClass, "d1", "()V"), stats);
        processGraphActions(model, requireMethod(graphClass, "d2", "()V"), stats);
        return model;
    }

    private static void populateStates(Model model, MethodNode method, BuildStats stats) {
        for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null; insn = insn.getNext()) {
            if (insn instanceof FieldInsnNode) {
                FieldInsnNode field = (FieldInsnNode) insn;
                if (field.getOpcode() == Opcodes.PUTSTATIC && STATE.equals(field.owner)
                        && "e".equals(field.name) && "[I".equals(field.desc)) {
                    if (isArrayClone(field)) {
                        if (model.currentPermutation == null) {
                            throw new IllegalStateException("permutation clone before initialization");
                        }
                        model.currentPermutation = model.currentPermutation.clone();
                        stats.populationClones++;
                    } else {
                        model.currentPermutation = readIntArrayBefore(field);
                        requirePermutation(model.currentPermutation, method.name + " population permutation");
                        stats.populationPermutations++;
                    }
                }
            }
            if (insn instanceof MethodInsnNode) {
                MethodInsnNode call = (MethodInsnNode) insn;
                if (call.getOpcode() == Opcodes.INVOKESPECIAL && STATE.equals(call.owner)
                        && "<init>".equals(call.name) && "(J)V".equals(call.desc)) {
                    Long seed = longConstant(previousCode(call));
                    if (seed == null || model.currentPermutation == null) {
                        throw new IllegalStateException("non-constant state population in " + method.name);
                    }
                    model.states.add(new StateValue(model.nextId++, seed, model.currentPermutation));
                    stats.populationStates++;
                }
            }
        }
    }

    private static void populateGraphMap(Model model, MethodNode method, BuildStats stats) {
        List<StateValue> resolved = new ArrayList<>();
        for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null; insn = insn.getNext()) {
            if (!(insn instanceof MethodInsnNode)) continue;
            MethodInsnNode call = (MethodInsnNode) insn;
            if (isStateResolve(call)) {
                Long seed = longConstant(previousCode(call));
                if (seed == null) throw new IllegalStateException("non-constant graph map state");
                resolved.add(model.resolve(seed));
            } else if ("java/util/concurrent/ConcurrentHashMap".equals(call.owner)
                    && "put".equals(call.name)
                    && "(Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object;".equals(call.desc)) {
                if (resolved.size() == 1 && isAuxiliaryGraphPut(call)) {
                    resolved.clear();
                    stats.auxiliaryMapPuts++;
                    continue;
                }
                if (resolved.size() != 2) {
                    throw new IllegalStateException("graph map put without exactly two states");
                }
                StateValue key = resolved.get(resolved.size() - 2);
                StateValue value = resolved.get(resolved.size() - 1);
                model.mapPut(DIAGNOSTIC_REVERSE_INITIAL_MAP ? value : key,
                        DIAGNOSTIC_REVERSE_INITIAL_MAP ? key : value);
                stats.mapPuts++;
                resolved.clear();
            }
        }
        if (stats.mapPuts == 0) throw new IllegalStateException("graph map is empty");
    }

    private static boolean isAuxiliaryGraphPut(MethodInsnNode put) {
        AbstractInsnNode value = previousCode(put);
        AbstractInsnNode resolve = previousCode(value);
        AbstractInsnNode seed = previousCode(resolve);
        AbstractInsnNode duplicateMap = previousCode(seed);
        return value instanceof VarInsnNode
                && value.getOpcode() == Opcodes.ALOAD
                && resolve instanceof MethodInsnNode
                && isStateResolve((MethodInsnNode) resolve)
                && longConstant(seed) != null
                && duplicateMap != null
                && duplicateMap.getOpcode() == Opcodes.DUP;
    }

    private static void modifyStatePermutations(Model model, MethodNode method, BuildStats stats) {
        StateValue selected = null;
        int writesForSelected = 0;
        for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null; insn = insn.getNext()) {
            if (insn instanceof MethodInsnNode) {
                MethodInsnNode call = (MethodInsnNode) insn;
                if (isStateResolve(call)) {
                    if (selected != null) {
                        requirePermutation(selected.permutation, "state permutation target");
                        stats.permutationTargets++;
                        if (writesForSelected != 64) {
                            throw new IllegalStateException("state permutation writes=" + writesForSelected);
                        }
                    }
                    Long seed = longConstant(previousCode(call));
                    if (seed == null) throw new IllegalStateException("non-constant permutation target");
                    selected = model.resolve(seed);
                    writesForSelected = 0;
                }
            } else if (insn.getOpcode() == Opcodes.IASTORE && selected != null) {
                Integer value = intConstant(previousCode(insn));
                Integer index = intConstant(previousCode(previousCode(insn)));
                if (index == null || value == null || index < 0 || index >= 64) {
                    throw new IllegalStateException("non-constant state permutation write");
                }
                selected.permutation[index] = value;
                writesForSelected++;
                stats.permutationWrites++;
            }
        }
        if (selected != null) {
            requirePermutation(selected.permutation, "state permutation target");
            stats.permutationTargets++;
            if (writesForSelected != 64) {
                throw new IllegalStateException("state permutation writes=" + writesForSelected);
            }
        }
    }

    private static void processGraphActions(Model model, MethodNode method, BuildStats stats) {
        List<StateValue> resolved = new ArrayList<>();
        for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null; insn = insn.getNext()) {
            if (!(insn instanceof MethodInsnNode)) continue;
            MethodInsnNode call = (MethodInsnNode) insn;
            if (isStateResolve(call)) {
                Long seed = longConstant(previousCode(call));
                if (seed == null) throw new IllegalStateException("non-constant graph action state");
                resolved.add(model.resolve(seed));
            } else if (STATE_INTERFACE.equals(call.owner) && "a".equals(call.name)
                    && ("(L" + STATE_INTERFACE + ";)V").equals(call.desc)) {
                if (resolved.size() < 2) throw new IllegalStateException("chain action without two states");
                StateValue receiver = resolved.get(resolved.size() - 2);
                StateValue argument = resolved.get(resolved.size() - 1);
                appendChain(receiver, argument);
                stats.chainLinks++;
                resolved.clear();
            } else if (STATE_INTERFACE.equals(call.owner) && "b".equals(call.name)
                    && "(J)V".equals(call.desc)) {
                if (resolved.isEmpty()) throw new IllegalStateException("delta action without state");
                Long delta = longConstant(previousCode(call));
                if (delta == null) throw new IllegalStateException("non-constant state delta");
                resolved.get(resolved.size() - 1).delta = delta;
                stats.deltaSets++;
                resolved.clear();
            }
        }
    }

    private static void appendChain(StateValue receiver, StateValue argument) {
        if (receiver == argument) return;
        IdentityHashMap<StateValue, Boolean> seen = new IdentityHashMap<>();
        StateValue cursor = receiver;
        while (cursor.next != null) {
            if (seen.put(cursor, Boolean.TRUE) != null) {
                throw new IllegalStateException("cycle while appending state chain");
            }
            cursor = cursor.next;
        }
        cursor.next = argument;
    }

    private static List<KeySite> findKeySites(Map<String, ClassNode> classes) {
        List<KeySite> result = new ArrayList<>();
        for (ClassNode owner : classes.values()) {
            for (MethodNode method : owner.methods) {
                int index = 0;
                for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
                     insn = insn.getNext(), index++) {
                    if (!(insn instanceof MethodInsnNode)) continue;
                    MethodInsnNode call = (MethodInsnNode) insn;
                    if (call.getOpcode() != Opcodes.INVOKESTATIC || !STATE.equals(call.owner)
                            || !"a".equals(call.name) || !BOOTSTRAP_DESC.equals(call.desc)) continue;
                    SeedPair seeds = seedPair(call);
                    AbstractInsnNode inputNode = nextCode(call);
                    AbstractInsnNode transformNode = inputNode == null ? null : nextCode(inputNode);
                    Long input = longConstant(inputNode);
                    if (!(transformNode instanceof MethodInsnNode)
                            || !isLongTransform((MethodInsnNode) transformNode) || input == null) {
                        throw new IllegalStateException("unrecognized class key transform in "
                                + owner.name + "." + method.name + method.desc);
                    }
                    result.add(new KeySite(owner.name, method.name + method.desc, index,
                            seeds.seedA, seeds.seedB, input));
                }
            }
        }
        return result;
    }

    private static SeedPair seedPair(MethodInsnNode bootstrap) {
        AbstractInsnNode owner = previousCode(bootstrap);
        AbstractInsnNode seedB;
        if (owner != null && owner.getOpcode() == Opcodes.ACONST_NULL) {
            seedB = previousCode(owner);
        } else if (owner instanceof MethodInsnNode
                && "java/lang/invoke/MethodHandles$Lookup".equals(((MethodInsnNode) owner).owner)
                && "lookupClass".equals(((MethodInsnNode) owner).name)) {
            seedB = previousCode(previousCode(owner));
        } else {
            throw new IllegalStateException("unrecognized long-key owner argument");
        }
        AbstractInsnNode seedA = previousCode(seedB);
        Long a = longConstant(seedA);
        Long b = longConstant(seedB);
        if (a == null || b == null) throw new IllegalStateException("non-constant long-key seeds");
        return new SeedPair(a, b);
    }

    private static boolean isLongTransform(MethodInsnNode call) {
        return call.getOpcode() == Opcodes.INVOKEINTERFACE && STATE_INTERFACE.equals(call.owner)
                && "a".equals(call.name) && "(J)J".equals(call.desc);
    }

    private static boolean isStateResolve(MethodInsnNode call) {
        return call.getOpcode() == Opcodes.INVOKESTATIC && STATE.equals(call.owner)
                && "c".equals(call.name) && ("(J)L" + STATE_INTERFACE + ";").equals(call.desc);
    }

    private static int[] readMethodIntArray(MethodNode method) {
        int[] result = new int[64];
        boolean[] seen = new boolean[64];
        int writes = 0;
        for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null; insn = insn.getNext()) {
            if (insn.getOpcode() != Opcodes.IASTORE) continue;
            Integer value = intConstant(previousCode(insn));
            Integer index = intConstant(previousCode(previousCode(insn)));
            if (index == null || value == null || index < 0 || index >= 64) continue;
            result[index] = value;
            if (!seen[index]) {
                seen[index] = true;
                writes++;
            }
        }
        if (writes != 64) throw new IllegalStateException("expected 64 array writes in " + method.name
                + method.desc + ", got " + writes);
        return result;
    }

    private static int[] readIntArrayBefore(AbstractInsnNode end) {
        AbstractInsnNode start = end.getPrevious();
        while (start != null && start.getOpcode() != Opcodes.NEWARRAY) {
            start = start.getPrevious();
        }
        if (!(start instanceof IntInsnNode) || ((IntInsnNode) start).operand != Opcodes.T_INT) {
            throw new IllegalStateException("int array allocation not found");
        }
        Integer size = intConstant(previousCode(start));
        if (size == null || size <= 0) throw new IllegalStateException("non-constant int array size");
        int[] result = new int[size];
        boolean[] seen = new boolean[size];
        int writes = 0;
        for (AbstractInsnNode insn = start.getNext(); insn != null && insn != end; insn = insn.getNext()) {
            if (insn.getOpcode() != Opcodes.IASTORE) continue;
            Integer value = intConstant(previousCode(insn));
            Integer index = intConstant(previousCode(previousCode(insn)));
            if (index == null || value == null || index < 0 || index >= size) {
                throw new IllegalStateException("non-constant int array initializer");
            }
            result[index] = value;
            if (!seen[index]) {
                seen[index] = true;
                writes++;
            }
        }
        if (writes != size) throw new IllegalStateException("partial int array initializer " + writes + "/" + size);
        return result;
    }

    static int[] readIntArrayBeforeForTest(AbstractInsnNode end) {
        return readIntArrayBefore(end);
    }

    private static boolean isArrayClone(AbstractInsnNode put) {
        AbstractInsnNode cursor = previousCode(put);
        boolean clone = false;
        for (int i = 0; cursor != null && i < 5; i++, cursor = previousCode(cursor)) {
            if (cursor instanceof MethodInsnNode) {
                MethodInsnNode call = (MethodInsnNode) cursor;
                if (("[I".equals(call.owner) || "java/lang/Object".equals(call.owner))
                        && "clone".equals(call.name)
                        && "()Ljava/lang/Object;".equals(call.desc)) {
                    clone = true;
                }
            } else if (clone && cursor instanceof FieldInsnNode) {
                FieldInsnNode field = (FieldInsnNode) cursor;
                return field.getOpcode() == Opcodes.GETSTATIC
                        && STATE.equals(field.owner)
                        && "e".equals(field.name)
                        && "[I".equals(field.desc);
            }
        }
        return false;
    }

    private static void requirePermutation(int[] permutation, String label) {
        if (permutation == null || permutation.length != 64) {
            throw new IllegalStateException(label + " is not a 64-position permutation");
        }
    }

    static Map<String, ClassNode> readClasses(Path input) throws IOException {
        Map<String, ClassNode> result = new LinkedHashMap<>();
        try (ZipInputStream in = new ZipInputStream(Files.newInputStream(input))) {
            ZipEntry entry;
            while ((entry = in.getNextEntry()) != null) {
                if (entry.isDirectory() || !entry.getName().endsWith(".class")) continue;
                ClassNode node = new ClassNode(Opcodes.ASM9);
                new ClassReader(readAll(in)).accept(node, ClassReader.SKIP_FRAMES);
                result.put(node.name, node);
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

    private static ClassNode requireClass(Map<String, ClassNode> classes, String name) {
        ClassNode result = classes.get(name);
        if (result == null) throw new IllegalStateException("required class missing: " + name);
        return result;
    }

    private static MethodNode requireMethod(ClassNode owner, String name, String descriptor) {
        for (MethodNode method : owner.methods) {
            if (name.equals(method.name) && descriptor.equals(method.desc)) return method;
        }
        throw new IllegalStateException("required method missing: " + owner.name + "." + name + descriptor);
    }

    private static Integer intConstant(AbstractInsnNode insn) {
        if (insn == null) return null;
        int opcode = insn.getOpcode();
        if (opcode >= Opcodes.ICONST_M1 && opcode <= Opcodes.ICONST_5) {
            return opcode - Opcodes.ICONST_0;
        }
        if (insn instanceof IntInsnNode && (opcode == Opcodes.BIPUSH || opcode == Opcodes.SIPUSH)) {
            return ((IntInsnNode) insn).operand;
        }
        if (insn instanceof LdcInsnNode && ((LdcInsnNode) insn).cst instanceof Integer) {
            return (Integer) ((LdcInsnNode) insn).cst;
        }
        return null;
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

    private static AbstractInsnNode previousCode(AbstractInsnNode insn) {
        AbstractInsnNode cursor = insn == null ? null : insn.getPrevious();
        while (cursor != null && cursor.getOpcode() < 0) cursor = cursor.getPrevious();
        return cursor;
    }

    private static AbstractInsnNode nextCode(AbstractInsnNode insn) {
        AbstractInsnNode cursor = insn == null ? null : insn.getNext();
        while (cursor != null && cursor.getOpcode() < 0) cursor = cursor.getNext();
        return cursor;
    }

    private static String sanitize(String value) {
        return value.replace('\t', ' ').replace('\r', ' ').replace('\n', ' ');
    }

    private static String shortReason(Throwable failure) {
        String reason = failure.getClass().getSimpleName() + ":" + String.valueOf(failure.getMessage());
        return reason.substring(0, Math.min(reason.length(), 180));
    }

    static final class EvaluationSummary {
        int parsedClasses;
        int keySites;
        int evaluatedKeys;
        int failedKeys;
    }

    static final class StatefulKeySequence {
        private final Model model;
        private final Map<String, KeySite> sites;

        StatefulKeySequence(Model model, Map<String, KeySite> sites) {
            this.model = model;
            this.sites = sites;
        }

        long peek(String owner) {
            KeySite site = requireSite(owner);
            return model.peek(site.seedA, site.seedB, site.transformInput);
        }

        long commit(String owner) {
            KeySite site = requireSite(owner);
            return model.evaluate(site.seedA, site.seedB, site.transformInput);
        }

        StatefulKeySequence copy() {
            return new StatefulKeySequence(model.copy(), sites);
        }

        boolean hasSite(String owner) {
            return sites.containsKey(owner);
        }

        List<String> owners() {
            return new ArrayList<>(sites.keySet());
        }

        private KeySite requireSite(String owner) {
            KeySite site = sites.get(owner);
            if (site == null) throw new IllegalArgumentException("no class-key site for " + owner);
            return site;
        }
    }

    private static final class BuildStats {
        int populationStates;
        int populationPermutations;
        int populationClones;
        int mapPuts;
        int auxiliaryMapPuts;
        int permutationTargets;
        int permutationWrites;
        int chainLinks;
        int deltaSets;
    }

    private static final class SeedPair {
        final long seedA;
        final long seedB;

        SeedPair(long seedA, long seedB) {
            this.seedA = seedA;
            this.seedB = seedB;
        }
    }

    private static final class KeySite {
        final String owner;
        final String method;
        final int instruction;
        final long seedA;
        final long seedB;
        final long transformInput;

        KeySite(String owner, String method, int instruction, long seedA, long seedB,
                long transformInput) {
            this.owner = owner;
            this.method = method;
            this.instruction = instruction;
            this.seedA = seedA;
            this.seedB = seedB;
            this.transformInput = transformInput;
        }
    }

    private static final class MapEntry {
        final StateValue key;
        StateValue value;
        final int storedHash;

        MapEntry(StateValue key, StateValue value, int storedHash) {
            this.key = key;
            this.value = value;
            this.storedHash = storedHash;
        }
    }

    private static final class StateValue {
        final int id;
        long value;
        long delta;
        int[] permutation;
        StateValue next;

        StateValue(int id, long value, int[] permutation) {
            this.id = id;
            this.value = value;
            this.permutation = permutation;
        }
    }

    private static final class Model {
        final List<StateValue> states = new ArrayList<>();
        final List<MapEntry> mapEntries = new ArrayList<>();
        int[] currentPermutation;
        int[] graphPermutation;
        int limit;
        int nextId;

        void sortStates() {
            states.sort((left, right) -> Long.compare(
                    project(DIAGNOSTIC_DESCENDING_SORT ? right.value : left.value, 56, 63,
                            DIAGNOSTIC_DESCENDING_SORT ? right.permutation : left.permutation),
                    project(DIAGNOSTIC_DESCENDING_SORT ? left.value : right.value, 56, 63,
                            DIAGNOSTIC_DESCENDING_SORT ? left.permutation : right.permutation)));
        }

        StateValue resolve(long seed) {
            int index = (int) project(seed, 50, 63, currentPermutation);
            if (index < limit) return states.get(index);
            if (states.size() % 128 == 0) currentPermutation = currentPermutation.clone();
            StateValue created = new StateValue(nextId++, seed, currentPermutation);
            states.add(created);
            return created;
        }

        void mapPut(StateValue key, StateValue value) {
            int hash = stateHash(key);
            for (MapEntry entry : mapEntries) {
                if ((DIAGNOSTIC_IGNORE_MAP_HASH || entry.storedHash == hash)
                        && stateEquals(key, entry.key)) {
                    entry.value = value;
                    return;
                }
            }
            mapEntries.add(new MapEntry(key, value, hash));
        }

        StateValue mapGet(StateValue key) {
            int hash = stateHash(key);
            for (MapEntry entry : mapEntries) {
                if ((DIAGNOSTIC_IGNORE_MAP_HASH || entry.storedHash == hash)
                        && stateEquals(key, entry.key)) return entry.value;
            }
            return null;
        }

        long evaluate(long seedA, long seedB, long transformInput) {
            StateValue first = new StateValue(nextId++, seedA, currentPermutation);
            StateValue second = new StateValue(nextId++, seedB, currentPermutation);
            StateValue selected = mapGet(first);
            mapPut(second, first);
            return selected == null ? transformGraph(transformInput) : transform(selected, transformInput);
        }

        long peek(long seedA, long seedB, long transformInput) {
            StateValue first = new StateValue(-1, seedA, currentPermutation);
            StateValue selected = mapGet(first);
            if (selected != null) return project(selected.value, 8, 55, selected.permutation);
            int index = (int) project(transformInput, 50, 63, currentPermutation);
            StateValue graphState = index < limit ? states.get(index) : null;
            return graphState == null
                    ? project(transformInput, 8, 55, currentPermutation)
                    : project(graphState.value, 8, 55, graphState.permutation);
        }

        private long transformGraph(long input) {
            StateValue selected = resolve(input);
            long result = transform(selected, input);
            System.arraycopy(graphPermutation, 0, selected.permutation, 0, 64);
            return result;
        }

        private long transform(StateValue state, long input) {
            long result = project(state.value, 8, 55, state.permutation);
            state.value ^= input ^ state.delta;
            StateValue cursor = state.next;
            IdentityHashMap<StateValue, Boolean> seen = new IdentityHashMap<>();
            while (cursor != null) {
                if (seen.put(cursor, Boolean.TRUE) != null) {
                    throw new IllegalStateException("cycle in state transform chain");
                }
                project(cursor.value, 8, 55, cursor.permutation);
                cursor.value ^= input ^ cursor.delta;
                cursor = cursor.next;
            }
            return result;
        }

        Model copy() {
            Model copy = new Model();
            copy.limit = limit;
            copy.nextId = nextId;
            IdentityHashMap<int[], int[]> arrays = new IdentityHashMap<>();
            copy.currentPermutation = copyArray(currentPermutation, arrays);
            copy.graphPermutation = copyArray(graphPermutation, arrays);
            IdentityHashMap<StateValue, StateValue> values = new IdentityHashMap<>();
            for (StateValue state : states) {
                copy.states.add(copyState(state, arrays, values));
            }
            for (MapEntry entry : mapEntries) {
                copy.mapEntries.add(new MapEntry(copyState(entry.key, arrays, values),
                        copyState(entry.value, arrays, values), entry.storedHash));
            }
            return copy;
        }

        private static StateValue copyState(StateValue value,
                                             IdentityHashMap<int[], int[]> arrays,
                                             IdentityHashMap<StateValue, StateValue> values) {
            if (value == null) return null;
            StateValue result = values.get(value);
            if (result != null) return result;
            result = new StateValue(value.id, value.value, copyArray(value.permutation, arrays));
            result.delta = value.delta;
            values.put(value, result);
            result.next = copyState(value.next, arrays, values);
            return result;
        }

        private static int[] copyArray(int[] value, IdentityHashMap<int[], int[]> arrays) {
            if (value == null) return null;
            int[] result = arrays.get(value);
            if (result == null) {
                result = value.clone();
                arrays.put(value, result);
            }
            return result;
        }

        private static int stateHash(StateValue state) {
            return (int) project(state.value, 0, 7, state.permutation);
        }

        private static boolean stateEquals(StateValue left, StateValue right) {
            return project(left.value, 0, 55, left.permutation)
                    == project(right.value, 0, 55, right.permutation);
        }

        private static long project(long value, int first, int last, int[] permutation) {
            long permuted = 0L;
            for (int index = 0; index < 64; index++) {
                long bit = value & (1L << index);
                if (bit == 0L) continue;
                int shift = permutation[index];
                if (shift > 0) bit >>>= shift;
                else if (shift < 0) bit <<= -shift;
                permuted |= bit;
            }
            int leftShift = 63 - last;
            if (leftShift > 0) permuted <<= leftShift;
            int rightShift = first + 63 - last;
            if (rightShift > 0) permuted >>>= rightShift;
            return permuted;
        }
    }
}
