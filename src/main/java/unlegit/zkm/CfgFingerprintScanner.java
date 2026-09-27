package unlegit.zkm;

import org.objectweb.asm.ClassReader;
import org.objectweb.asm.Opcodes;
import org.objectweb.asm.Type;
import org.objectweb.asm.tree.*;
import org.objectweb.asm.tree.analysis.Analyzer;
import org.objectweb.asm.tree.analysis.BasicInterpreter;
import org.objectweb.asm.tree.analysis.BasicValue;
import org.objectweb.asm.tree.analysis.Frame;
import org.objectweb.asm.tree.analysis.SourceInterpreter;
import org.objectweb.asm.tree.analysis.SourceValue;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.security.MessageDigest;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.zip.ZipEntry;
import java.util.zip.ZipInputStream;

/**
 * Read-only CFG fingerprint inventory.  It parses class files with ASM tree
 * APIs and never defines, loads, or initializes an input class.
 */
public final class CfgFingerprintScanner {
    private static final String METHOD_HEADER = String.join("\t",
            "class", "method", "access", "instructions", "executable", "basic_blocks",
            "normal_edges", "exception_edges", "total_edges", "branches", "conditional_branches",
            "gotos", "switches", "switch_cases", "loop_sccs", "loop_blocks", "back_edges",
            "exception_handlers", "state_variable_candidates", "dispatcher_candidates",
            "opaque_predicate_candidates", "zkm_flow_candidates", "parse_status");
    private static final String CANDIDATE_HEADER = String.join("\t",
            "class", "method", "kind", "location", "signal", "confidence", "evidence");
    private static final String RECOVERY_HEADER = String.join("\t",
            "class", "method", "switch_location", "state_signal", "case_order", "case_key",
            "target_block", "target_start", "target_end", "normal_successors", "exception_successors",
            "back_edge", "loop_scc", "state_updates", "opaque_state_evidence", "recommendation");
    private static final String CLASS_HEADER = String.join("\t",
            "class", "entry", "methods", "methods_with_code", "parse_status");

    private CfgFingerprintScanner() { }

    public static void main(String[] args) throws Exception {
        if (args.length != 3) {
            System.err.println("usage: CfgFingerprintScanner <input.jar> <output-dir> <label>");
            System.exit(2);
        }
        Path input = Paths.get(args[0]).toAbsolutePath();
        Path out = Paths.get(args[1]).toAbsolutePath();
        String label = args[2];
        Files.createDirectories(out);
        ScanResult result = scan(input);
        write(result, input, out, label);
        System.out.println("classes=" + result.classEntries + " parsed=" + result.parsedClasses
                + " methods=" + result.methodCount + " output=" + out);
    }

    private static ScanResult scan(Path input) throws IOException {
        List<ClassBytes> entries = new ArrayList<>();
        try (ZipInputStream zin = new ZipInputStream(Files.newInputStream(input))) {
            ZipEntry e;
            while ((e = zin.getNextEntry()) != null) {
                if (e.getName().endsWith(".class")) entries.add(new ClassBytes(e.getName(), readAll(zin)));
            }
        }
        entries.sort(Comparator.comparing(a -> a.entry));
        ScanResult result = new ScanResult();
        result.classEntries = entries.size();
        for (ClassBytes entry : entries) {
            try {
                ClassNode cn = new ClassNode(Opcodes.ASM9);
                new ClassReader(entry.bytes).accept(cn, ClassReader.SKIP_DEBUG);
                result.parsedClasses++;
                result.classes.add(String.join("\t", cn.name, entry.entry,
                        Integer.toString(cn.methods.size()),
                        Integer.toString((int) cn.methods.stream().filter(m -> hasCode(m)).count()), "OK"));
                List<MethodNode> methods = new ArrayList<>(cn.methods);
                methods.sort(Comparator.comparing((MethodNode m) -> m.name + m.desc));
                for (MethodNode m : methods) analyze(cn, m, result);
            } catch (Throwable t) {
                result.malformedClasses++;
                result.classes.add(String.join("\t", entry.entry.substring(0, entry.entry.length() - 6),
                        entry.entry, "0", "0", "ERROR:" + reason(t)));
            }
        }
        result.methods.sort(Comparator.naturalOrder());
        result.candidates.sort(Comparator.naturalOrder());
        result.recovery.sort(Comparator.naturalOrder());
        result.classes.sort(Comparator.naturalOrder());
        return result;
    }

    private static boolean hasCode(MethodNode m) {
        return m.instructions != null && m.instructions.size() > 0;
    }

    private static void analyze(ClassNode ownerClass, MethodNode m, ScanResult out) {
        out.methodCount++;
        String owner = ownerClass.name;
        String method = m.name + m.desc;
        if (!hasCode(m)) {
            int handlers = m.tryCatchBlocks == null ? 0 : m.tryCatchBlocks.size();
            out.methods.add(row(owner, method, m.access,
                    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                    handlers, 0, 0, 0, 0, "OK"));
            return;
        }
        try {
            Graph g = Graph.build(m);
            List<Candidate> found = new ArrayList<>();
            Frame<BasicValue>[] frames = new Analyzer<BasicValue>(new BasicInterpreter()).analyze(owner, m);
            Frame<SourceValue>[] sourceFrames = new Analyzer<SourceValue>(new SourceInterpreter()).analyze(owner, m);
            detectState(owner, method, m, g, sourceFrames, found);
            detectOpaque(owner, method, m, g, found);
            detectZkmFlow(ownerClass, method, m, g, frames, sourceFrames, found);
            for (Candidate c : found) out.candidates.add(c.toRow());
            emitRecovery(owner, method, g, found, out.recovery);
            int opaque = count(found, "OPAQUE_PREDICATE");
            int zkm = count(found, "ZKM_FLOW_GUARD");
            int state = count(found, "STATE_VARIABLE");
            int dispatch = count(found, "DISPATCHER");
            out.methodsWithCode++;
            if (g.blocks > 0) out.methodsWithBlocks++;
            if (g.branches > 0) out.methodsWithBranches++;
            if (g.switches > 0) out.methodsWithSwitches++;
            if (g.loopSccs > 0) out.methodsWithLoops++;
            if (g.exceptionEdges > 0) out.methodsWithExceptionEdges++;
            if (state > 0) out.methodsWithState++;
            if (dispatch > 0) out.methodsWithDispatchers++;
            if (opaque > 0) out.methodsWithOpaque++;
            if (zkm > 0) out.methodsWithZkm++;
            out.methods.add(row(owner, method, m.access, m.instructions.size(), g.executable, g.blocks,
                    g.normalEdges, g.exceptionEdges, g.normalEdges + g.exceptionEdges, g.branches,
                    g.conditionalBranches, g.gotos, g.switches, g.switchCases, g.loopSccs, g.loopBlocks,
                    g.backEdges, m.tryCatchBlocks == null ? 0 : m.tryCatchBlocks.size(), state, dispatch,
                    opaque, zkm, "OK"));
        } catch (Throwable t) {
            out.analysisErrors++;
            out.methods.add(row(owner, method, m.access, m.instructions.size(), 0, 0, 0, 0, 0, 0, 0, 0,
                    0, 0, 0, 0, 0, m.tryCatchBlocks == null ? 0 : m.tryCatchBlocks.size(), 0, 0, 0,
                    0, "ERROR:" + reason(t)));
        }
    }

    private static String row(String owner, String method, int access, int instructions, int executable,
                              int blocks, int normalEdges, int exceptionEdges, int totalEdges, int branches,
                              int conditional, int gotos, int switches, int cases, int loopSccs, int loopBlocks,
                              int backEdges, int handlers, int state, int dispatch, int opaque, int zkm,
                              String status) {
        return String.join("\t", owner, method, Integer.toString(access), Integer.toString(instructions),
                Integer.toString(executable), Integer.toString(blocks), Integer.toString(normalEdges),
                Integer.toString(exceptionEdges), Integer.toString(totalEdges), Integer.toString(branches),
                Integer.toString(conditional), Integer.toString(gotos), Integer.toString(switches),
                Integer.toString(cases), Integer.toString(loopSccs), Integer.toString(loopBlocks),
                Integer.toString(backEdges), Integer.toString(handlers), Integer.toString(state),
                Integer.toString(dispatch), Integer.toString(opaque), Integer.toString(zkm), status);
    }

    private static int count(List<Candidate> list, String kind) {
        int n = 0; for (Candidate c : list) if (kind.equals(c.kind)) n++; return n;
    }

    /**
     * Emit a conservative, block-level recovery suggestion for each state-like
     * switch.  This is deliberately report-only: no bytecode is reordered or
     * rewritten, and every recommendation remains review_only.
     */
    private static void emitRecovery(String owner, String method, Graph g,
                                     List<Candidate> found, List<String> output) {
        int opaque = count(found, "OPAQUE_PREDICATE");
        for (SwitchInfo s : g.switchesInfo) {
            Candidate dispatcher = null;
            for (Candidate c : found) {
                if (!"DISPATCHER".equals(c.kind)) continue;
                if (!Integer.toString(s.location).equals(c.location)) continue;
                dispatcher = c;
                break;
            }
            if (dispatcher == null) continue;
            int updates = updateCount(dispatcher.evidence);
            String evidence = opaque == 0
                    ? "opaque_predicates=0;state_input_unknown=true"
                    : "opaque_predicates=" + opaque + ";state_input_unknown=true";
            String recommendation = recommendation(g, s, opaque, updates);
            List<SwitchTarget> targets = switchTargets(g, s.node);
            for (int i = 0; i < targets.size(); i++) {
                SwitchTarget target = targets.get(i);
                int block = target.block;
                Set<Integer> normal = g.normalAdj.get(block);
                Set<Integer> exceptional = g.exceptionAdj.get(block);
                String key = target.defaultTarget ? "default" : Integer.toString(target.key);
                output.add(String.join("\t", owner, method, Integer.toString(s.location), dispatcher.signal,
                        Integer.toString(i), key, Integer.toString(block),
                        Integer.toString(g.blockStarts.get(block)), Integer.toString(g.blockEnds.get(block)),
                        joinBlocks(normal, g), joinBlocks(exceptional, g),
                        Boolean.toString(g.hasBackEdgeFrom(block)),
                        Integer.toString(g.sccByBlock[block]), Integer.toString(updates), evidence,
                        recommendation));
            }
        }
    }

    private static String recommendation(Graph g, SwitchInfo s, int opaque, int updates) {
        List<String> reasons = new ArrayList<>();
        if (g.exceptionEdges > 0) reasons.add("exception_edges");
        if (g.loopSccs > 0) reasons.add("loops");
        if (s.uniqueCases != s.cases) reasons.add("merged_targets");
        if (opaque > 0) reasons.add("opaque_predicate");
        if (updates <= 0) reasons.add("no_state_update");
        if (reasons.isEmpty()) reasons.add("no_proof_of_unique_successor");
        return "review_only:" + String.join("+", reasons);
    }

    private static int updateCount(String evidence) {
        String marker = "updates=";
        int start = evidence.indexOf(marker);
        if (start < 0) return 0;
        start += marker.length();
        int end = start;
        while (end < evidence.length() && Character.isDigit(evidence.charAt(end))) end++;
        try { return Integer.parseInt(evidence.substring(start, end)); }
        catch (RuntimeException ignored) { return 0; }
    }

    private static String joinBlocks(Set<Integer> blocks, Graph g) {
        if (blocks == null || blocks.isEmpty()) return "-";
        List<String> values = new ArrayList<>();
        for (Integer block : blocks) values.add(Integer.toString(block));
        return String.join(",", values);
    }

    private static List<SwitchTarget> switchTargets(Graph g, AbstractInsnNode node) {
        List<SwitchTarget> targets = new ArrayList<>();
        if (node instanceof TableSwitchInsnNode) {
            TableSwitchInsnNode s = (TableSwitchInsnNode) node;
            for (int i = 0; i < s.labels.size(); i++) {
                targets.add(new SwitchTarget(s.min + i, g.targetBlock(s.labels.get(i)), false));
            }
            targets.add(new SwitchTarget(0, g.targetBlock(s.dflt), true));
        } else if (node instanceof LookupSwitchInsnNode) {
            LookupSwitchInsnNode s = (LookupSwitchInsnNode) node;
            for (int i = 0; i < s.labels.size(); i++) {
                targets.add(new SwitchTarget(s.keys.get(i), g.targetBlock(s.labels.get(i)), false));
            }
            targets.add(new SwitchTarget(0, g.targetBlock(s.dflt), true));
        }
        return targets;
    }

    private static void detectState(String owner, String method, MethodNode m, Graph g,
                                    Frame<SourceValue>[] sourceFrames, List<Candidate> out) {
        for (SwitchInfo s : g.switchesInfo) {
            AbstractInsnNode p = previousCode(s.node);
            Selector selector = null;
            if (p instanceof VarInsnNode && ((VarInsnNode) p).getOpcode() == Opcodes.ILOAD) {
                selector = Selector.local(((VarInsnNode) p).var);
            } else if (p instanceof FieldInsnNode && ((p.getOpcode() == Opcodes.GETFIELD)
                    || p.getOpcode() == Opcodes.GETSTATIC) && isIntDescriptor(((FieldInsnNode) p).desc)) {
                FieldInsnNode f = (FieldInsnNode) p;
                if (p.getOpcode() == Opcodes.GETSTATIC) {
                    selector = Selector.staticField(f);
                } else {
                    AbstractInsnNode receiver = previousCode(p);
                    if (receiver instanceof VarInsnNode && receiver.getOpcode() == Opcodes.ALOAD) {
                        selector = Selector.instanceField(f, ((VarInsnNode) receiver).var);
                    }
                }
            }
            if (selector == null) continue;
            int updates = selector.countWrites(m, sourceFrames);
            String evidence = "cases=" + s.cases + ",updates=" + updates + ",input=" + selector.signal;
            out.add(new Candidate(owner, method, "STATE_VARIABLE", Integer.toString(s.location), selector.signal,
                    "low", evidence));
            DispatcherEvidence dispatcher = proveDispatcher(m, g, s, selector, sourceFrames);
            if (dispatcher != null) {
                String dispatcherEvidence = evidence + ",unique_cases=" + s.uniqueCases
                        + ",transition_cases=" + dispatcher.transitionCases
                        + ",header_block=" + dispatcher.headerBlock
                        + ",case_private_reaching_writes=true"
                        + ",same_header_back_edges=true";
                out.add(new Candidate(owner, method, "DISPATCHER", Integer.toString(s.location), selector.signal,
                        "high", dispatcherEvidence));
            }
        }
    }

    /**
     * A switch is only a dispatcher candidate when an explicit case owns a
     * write to the selector and that definition reaches this exact switch
     * header on every normal return path from the case.  Writes in a shared
     * loop latch do not count: those are the usual shape of parser and
     * collection loops which happen to contain a business switch.
     */
    private static DispatcherEvidence proveDispatcher(MethodNode method, Graph graph, SwitchInfo info,
                                                       Selector selector,
                                                       Frame<SourceValue>[] sourceFrames) {
        if (info.cases < 3) return null;
        int header = graph.blockFor(info.node);
        Map<Integer, Boolean> targets = new LinkedHashMap<>();
        for (SwitchTarget target : switchTargets(graph, info.node)) {
            boolean explicit = !target.defaultTarget;
            targets.put(target.block, targets.getOrDefault(target.block, false) || explicit);
        }

        // Record which case entries can reach each block without crossing the
        // dispatcher header.  A write is case-private only when it has one owner.
        Map<Integer, Set<Integer>> owners = new HashMap<>();
        for (Integer target : targets.keySet()) {
            if (target == header) continue;
            ArrayDeque<Integer> queue = new ArrayDeque<>();
            Set<Integer> seen = new HashSet<>();
            queue.add(target);
            while (!queue.isEmpty()) {
                int block = queue.removeFirst();
                if (block == header || !seen.add(block)) continue;
                owners.computeIfAbsent(block, ignored -> new HashSet<Integer>()).add(target);
                for (Integer next : graph.normalAdj.get(block)) {
                    if (next != header) queue.addLast(next);
                }
            }
        }

        int transitionCases = 0;
        for (Map.Entry<Integer, Boolean> entry : targets.entrySet()) {
            if (!entry.getValue() || entry.getKey() == header) continue;
            if (hasCasePrivateReachingWrite(method, graph, header, entry.getKey(), owners,
                    selector, sourceFrames)) {
                transitionCases++;
            }
        }
        return transitionCases < 2 ? null : new DispatcherEvidence(header, transitionCases);
    }

    private static boolean hasCasePrivateReachingWrite(MethodNode method, Graph graph, int header,
                                                       int caseTarget, Map<Integer, Set<Integer>> owners,
                                                       Selector selector,
                                                       Frame<SourceValue>[] sourceFrames) {
        ArrayDeque<PathState> queue = new ArrayDeque<>();
        Set<String> seen = new HashSet<>();
        queue.add(new PathState(caseTarget, 0));
        boolean reachesWithPrivateWrite = false;
        boolean reachesWithoutPrivateWrite = false;
        while (!queue.isEmpty()) {
            PathState current = queue.removeFirst();
            String key = current.block + ":" + current.definition;
            if (!seen.add(key)) continue;
            int definition = current.definition;
            if (blockWritesSelector(method, graph, current.block, selector, sourceFrames)) {
                Set<Integer> blockOwners = owners.get(current.block);
                definition = blockOwners != null && blockOwners.size() == 1
                        && blockOwners.contains(caseTarget) ? 1 : 2;
            }
            for (Integer next : graph.normalAdj.get(current.block)) {
                if (next == header) {
                    if (definition == 1) reachesWithPrivateWrite = true;
                    else reachesWithoutPrivateWrite = true;
                } else {
                    queue.addLast(new PathState(next, definition));
                }
            }
        }
        return reachesWithPrivateWrite && !reachesWithoutPrivateWrite;
    }

    private static boolean blockWritesSelector(MethodNode method, Graph graph, int block,
                                               Selector selector,
                                               Frame<SourceValue>[] sourceFrames) {
        for (AbstractInsnNode n = method.instructions.getFirst(); n != null; n = n.getNext()) {
            Integer location = graph.instructionIndex.get(n);
            if (location == null || graph.blockAt[location] != block) continue;
            if (selector.matchesWrite(method, n, sourceFrames)) return true;
        }
        return false;
    }

    private static void detectOpaque(String owner, String method, MethodNode m, Graph g, List<Candidate> out) {
        for (AbstractInsnNode n = m.instructions.getFirst(); n != null; n = n.getNext()) {
            if (!(n instanceof JumpInsnNode) || !isConditional(n.getOpcode())) continue;
            AbstractInsnNode p1 = previousCode(n), p2 = previousCode(p1), p3 = previousCode(p2);
            String signal = null, evidence = null;
            Integer a = intConstant(p1), b = intConstant(p2);
            if (isBinaryInt(n.getOpcode()) && a != null && b != null) {
                signal = "constant-binary"; evidence = "left=" + b + ",right=" + a + ",op=" + n.getOpcode();
            } else if (!isBinaryInt(n.getOpcode()) && a != null) {
                signal = "constant-zero"; evidence = "value=" + a + ",op=" + n.getOpcode();
            } else if (p1 instanceof VarInsnNode && p2 instanceof VarInsnNode
                    && ((VarInsnNode) p1).getOpcode() == Opcodes.ILOAD
                    && ((VarInsnNode) p2).getOpcode() == Opcodes.ILOAD
                    && ((VarInsnNode) p1).var == ((VarInsnNode) p2).var && isBinaryInt(n.getOpcode())) {
                signal = "self-compare"; evidence = "local#" + ((VarInsnNode) p1).var + ",op=" + n.getOpcode();
            } else if (p1 != null && p1.getOpcode() == Opcodes.IAND && intConstant(p2) != null
                    && intConstant(p2) == 0) {
                signal = "zero-mask"; evidence = "IAND with zero mask";
            } else if ((n.getOpcode() == Opcodes.IFNULL || n.getOpcode() == Opcodes.IFNONNULL)
                    && p1 != null && p1.getOpcode() == Opcodes.ACONST_NULL) {
                signal = "null-constant"; evidence = "ACONST_NULL";
            }
            if (signal != null) out.add(new Candidate(owner, method, "OPAQUE_PREDICATE",
                    Integer.toString(g.location(n)), signal, "high", evidence));
        }
    }

    /**
     * Reports the stack shapes documented by the zkm-flow study. These are
     * review candidates, not rewrite proofs: valid bytecode can carry values
     * across a branch, and this pass does not know a long parameter's sign.
     */
    private static void detectZkmFlow(ClassNode ownerClass, String method, MethodNode m, Graph g,
                                      Frame<BasicValue>[] frames, Frame<SourceValue>[] sourceFrames,
                                      List<Candidate> out) {
        String owner = ownerClass.name;
        Map<String, List<StackedGuard>> stackedGroups = new LinkedHashMap<>();
        for (AbstractInsnNode n = m.instructions.getFirst(); n != null; n = n.getNext()) {
            if (!(n instanceof JumpInsnNode)) continue;
            int op = n.getOpcode();
            int frameIndex = m.instructions.indexOf(n);
            Frame<BasicValue> frame = frameIndex >= 0 && frameIndex < frames.length
                    ? frames[frameIndex] : null;
            AbstractInsnNode p1 = previousCode(n);

            if (frame != null && frame.getStackSize() > 1 && p1 instanceof VarInsnNode) {
                VarInsnNode load = (VarInsnNode) p1;
                if (load.getOpcode() == Opcodes.ILOAD && (op == Opcodes.IFEQ || op == Opcodes.IFNE)) {
                    addStackedGuard(stackedGroups, new StackedGuard(n, load.var, op,
                            frame.getStackSize(), "int"));
                } else if (load.getOpcode() == Opcodes.ALOAD
                        && (op == Opcodes.IFNULL || op == Opcodes.IFNONNULL)) {
                    addStackedGuard(stackedGroups, new StackedGuard(n, load.var, op,
                            frame.getStackSize(), "null"));
                }
            }

            if (op != Opcodes.IFLT && op != Opcodes.IFLE && op != Opcodes.IFGE && op != Opcodes.IFGT) {
                continue;
            }
            AbstractInsnNode cmp = p1;
            AbstractInsnNode zero = previousCode(cmp);
            AbstractInsnNode loadNode = previousCode(zero);
            if (cmp == null || cmp.getOpcode() != Opcodes.LCMP
                    || zero == null || zero.getOpcode() != Opcodes.LCONST_0
                    || !(loadNode instanceof VarInsnNode)
                    || loadNode.getOpcode() != Opcodes.LLOAD) {
                continue;
            }
            int local = ((VarInsnNode) loadNode).var;
            boolean parameter = isLongParameter(m, local);
            out.add(new Candidate(owner, method, "ZKM_FLOW_GUARD",
                    Integer.toString(g.location(n)), "long-zero-guard", parameter ? "medium" : "low",
                    "local#" + local + ",op=" + op + ",long_parameter=" + parameter
                            + ",review_only=true"));
        }

        for (List<StackedGuard> group : stackedGroups.values()) {
            if (group.size() < 2) continue;
            StackedGuard first = group.get(0);
            List<String> locations = new ArrayList<>();
            int maxStack = 0;
            for (StackedGuard site : group) {
                locations.add(Integer.toString(g.location(site.node)));
                maxStack = Math.max(maxStack, site.stackSize);
            }
            String parameterType = parameterType(m, first.local);
            int stores = countLocalStores(m, first.local);
            int opposite = countOppositeJumps(m, first.local, first.op, first.kind);
            String producer = localProducer(m, first.node, first.local, sourceFrames);
            String fieldProvenance = sameClassFieldProvenance(ownerClass, producer);
            String signal = opposite > 0 ? "zkm-replaced-goto-hint"
                    : "repeated-stacked-" + first.kind + "-guard";
            String confidence = opposite > 0 && (parameterType != null || stores <= 1)
                    ? "medium" : "low";
            out.add(new Candidate(owner, method, "ZKM_FLOW_GUARD",
                    String.join(",", locations), signal, confidence,
                    "local#" + first.local + ",op=" + first.op + ",occurrences="
                            + group.size() + ",max_stack_before=" + maxStack + ",parameter_type="
                            + (parameterType == null ? "none" : parameterType) + ",stores=" + stores
                            + ",opposite_jumps=" + opposite
                            + ",producer=" + producer
                            + ",field_provenance=" + fieldProvenance
                            + ",review_only=true"));
        }
    }

    private static void addStackedGuard(Map<String, List<StackedGuard>> groups, StackedGuard guard) {
        String key = guard.kind + ":" + guard.local + ":" + guard.op;
        groups.computeIfAbsent(key, ignored -> new ArrayList<StackedGuard>()).add(guard);
    }

    private static int countLocalStores(MethodNode method, int local) {
        int stores = 0;
        for (AbstractInsnNode n = method.instructions.getFirst(); n != null; n = n.getNext()) {
            if (n instanceof VarInsnNode && ((VarInsnNode) n).var == local) {
                int op = n.getOpcode();
                if (op >= Opcodes.ISTORE && op <= Opcodes.ASTORE) stores++;
            } else if (n instanceof IincInsnNode && ((IincInsnNode) n).var == local) {
                stores++;
            }
        }
        return stores;
    }

    private static String localProducer(MethodNode method, AbstractInsnNode guard, int local,
                                        Frame<SourceValue>[] sourceFrames) {
        AbstractInsnNode store = null;
        int stores = 0;
        for (AbstractInsnNode n = method.instructions.getFirst(); n != null; n = n.getNext()) {
            if (n instanceof VarInsnNode && ((VarInsnNode) n).var == local
                    && n.getOpcode() >= Opcodes.ISTORE && n.getOpcode() <= Opcodes.ASTORE) {
                stores++;
                store = n;
            } else if (n instanceof IincInsnNode && ((IincInsnNode) n).var == local) {
                stores++;
                store = n;
            }
        }
        if (stores == 0) return parameterType(method, local) == null ? "none" : "parameter";
        if (stores != 1 || store instanceof IincInsnNode) return "multiple";
        int index = method.instructions.indexOf(store);
        if (index < 0 || index >= sourceFrames.length || sourceFrames[index] == null
                || sourceFrames[index].getStackSize() == 0) {
            return "unavailable";
        }
        SourceValue value = sourceFrames[index].getStack(sourceFrames[index].getStackSize() - 1);
        if (value == null || value.insns == null || value.insns.isEmpty()) {
            return parameterType(method, local) == null ? "none" : "parameter";
        }
        if (value.insns.size() != 1) return "merged:" + value.insns.size();
        AbstractInsnNode producer = value.insns.iterator().next();
        if (producer instanceof MethodInsnNode) {
            MethodInsnNode call = (MethodInsnNode) producer;
            return "invoke:" + call.owner + "." + call.name + call.desc;
        }
        if (producer instanceof FieldInsnNode) {
            FieldInsnNode field = (FieldInsnNode) producer;
            return "field:" + field.owner + "." + field.name + ":" + field.desc;
        }
        if (producer instanceof VarInsnNode) {
            return "local#" + ((VarInsnNode) producer).var + ":op" + producer.getOpcode();
        }
        Integer intValue = intConstant(producer);
        if (intValue != null) return "int:" + intValue;
        if (producer.getOpcode() == Opcodes.ACONST_NULL) return "null";
        if (producer instanceof LdcInsnNode) {
            Object ldcValue = ((LdcInsnNode) producer).cst;
            return "ldc:" + String.valueOf(ldcValue).replace(',', '_');
        }
        return "opcode:" + producer.getOpcode();
    }

    private static String sameClassFieldProvenance(ClassNode ownerClass, String producer) {
        String prefix = "invoke:" + ownerClass.name + ".";
        if (!producer.startsWith(prefix)) return "none";
        String signature = producer.substring(prefix.length());
        int descriptorStart = signature.indexOf('(');
        if (descriptorStart <= 0) return "unparsed";
        String name = signature.substring(0, descriptorStart);
        String descriptor = signature.substring(descriptorStart);
        MethodNode getter = null;
        for (MethodNode candidate : ownerClass.methods) {
            if (candidate.name.equals(name) && candidate.desc.equals(descriptor)) {
                getter = candidate;
                break;
            }
        }
        if (getter == null) return "missing_getter";
        List<AbstractInsnNode> code = executableInstructions(getter);
        if (code.size() != 2 || !(code.get(0) instanceof FieldInsnNode)
                || code.get(0).getOpcode() != Opcodes.GETSTATIC
                || !isReturnOpcode(code.get(1).getOpcode())) {
            return "complex_getter";
        }
        FieldInsnNode field = (FieldInsnNode) code.get(0);
        List<String> writers = new ArrayList<>();
        for (MethodNode candidate : ownerClass.methods) {
            for (AbstractInsnNode n = candidate.instructions == null ? null
                    : candidate.instructions.getFirst(); n != null; n = n.getNext()) {
                if (!(n instanceof FieldInsnNode) || n.getOpcode() != Opcodes.PUTSTATIC) continue;
                FieldInsnNode write = (FieldInsnNode) n;
                if (write.owner.equals(field.owner) && write.name.equals(field.name)
                        && write.desc.equals(field.desc)) {
                    writers.add(candidate.name + candidate.desc);
                }
            }
        }
        Collections.sort(writers);
        return "field:" + field.owner + "." + field.name + ":" + field.desc
                + "|writers:" + (writers.isEmpty() ? "none" : String.join("|", writers));
    }

    private static List<AbstractInsnNode> executableInstructions(MethodNode method) {
        List<AbstractInsnNode> code = new ArrayList<>();
        if (method.instructions == null) return code;
        for (AbstractInsnNode n = method.instructions.getFirst(); n != null; n = n.getNext()) {
            if (n.getOpcode() >= 0) code.add(n);
        }
        return code;
    }

    private static boolean isReturnOpcode(int opcode) {
        return opcode >= Opcodes.IRETURN && opcode <= Opcodes.ARETURN;
    }

    private static int countOppositeJumps(MethodNode method, int local, int op, String kind) {
        int opposite = (op == Opcodes.IFEQ || op == Opcodes.IFNE)
                ? (op == Opcodes.IFEQ ? Opcodes.IFNE : Opcodes.IFEQ)
                : (op == Opcodes.IFNULL ? Opcodes.IFNONNULL : Opcodes.IFNULL);
        int count = 0;
        for (AbstractInsnNode n = method.instructions.getFirst(); n != null; n = n.getNext()) {
            if (!(n instanceof JumpInsnNode) || n.getOpcode() != opposite) continue;
            AbstractInsnNode load = previousCode(n);
            if (!(load instanceof VarInsnNode)) continue;
            int loadOpcode = ((VarInsnNode) load).getOpcode();
            boolean matchingLoad = "int".equals(kind) ? loadOpcode == Opcodes.ILOAD : loadOpcode == Opcodes.ALOAD;
            if (matchingLoad && ((VarInsnNode) load).var == local) count++;
        }
        return count;
    }

    private static String parameterType(MethodNode method, int local) {
        int slot = (method.access & Opcodes.ACC_STATIC) == 0 ? 1 : 0;
        for (Type argument : Type.getArgumentTypes(method.desc)) {
            if (slot == local) return argument.getDescriptor();
            slot += argument.getSize();
        }
        return null;
    }

    private static boolean isLongParameter(MethodNode method, int local) {
        return "J".equals(parameterType(method, local));
    }

    private static final class StackedGuard {
        final AbstractInsnNode node;
        final int local, op, stackSize;
        final String kind;

        StackedGuard(AbstractInsnNode node, int local, int op, int stackSize, String kind) {
            this.node = node;
            this.local = local;
            this.op = op;
            this.stackSize = stackSize;
            this.kind = kind;
        }
    }

    private static final class Selector {
        private static final int LOCAL = 0, STATIC_FIELD = 1, INSTANCE_FIELD = 2;
        final int kind, local, receiverLocal;
        final String owner, name, desc, signal;

        private Selector(int kind, int local, int receiverLocal,
                         String owner, String name, String desc, String signal) {
            this.kind = kind;
            this.local = local;
            this.receiverLocal = receiverLocal;
            this.owner = owner;
            this.name = name;
            this.desc = desc;
            this.signal = signal;
        }

        static Selector local(int local) {
            return new Selector(LOCAL, local, -1, null, null, null, "local#" + local);
        }

        static Selector staticField(FieldInsnNode field) {
            String signal = "field#" + field.owner + "." + field.name + ":" + field.desc;
            return new Selector(STATIC_FIELD, -1, -1, field.owner, field.name, field.desc, signal);
        }

        static Selector instanceField(FieldInsnNode field, int receiverLocal) {
            String signal = "field#" + field.owner + "." + field.name + ":" + field.desc
                    + "@local#" + receiverLocal;
            return new Selector(INSTANCE_FIELD, -1, receiverLocal,
                    field.owner, field.name, field.desc, signal);
        }

        int countWrites(MethodNode method, Frame<SourceValue>[] sourceFrames) {
            int count = 0;
            for (AbstractInsnNode n = method.instructions.getFirst(); n != null; n = n.getNext()) {
                if (matchesWrite(method, n, sourceFrames)) count++;
            }
            return count;
        }

        boolean matchesWrite(MethodNode method, AbstractInsnNode instruction,
                             Frame<SourceValue>[] sourceFrames) {
            if (kind == LOCAL) {
                if (instruction instanceof IincInsnNode) {
                    return ((IincInsnNode) instruction).var == local;
                }
                return instruction instanceof VarInsnNode
                        && instruction.getOpcode() == Opcodes.ISTORE
                        && ((VarInsnNode) instruction).var == local;
            }
            if (!(instruction instanceof FieldInsnNode)) return false;
            FieldInsnNode field = (FieldInsnNode) instruction;
            if (!owner.equals(field.owner) || !name.equals(field.name) || !desc.equals(field.desc)) {
                return false;
            }
            if (kind == STATIC_FIELD) return instruction.getOpcode() == Opcodes.PUTSTATIC;
            if (instruction.getOpcode() != Opcodes.PUTFIELD) return false;
            int index = method.instructions.indexOf(instruction);
            if (index < 0 || index >= sourceFrames.length) return false;
            Frame<SourceValue> frame = sourceFrames[index];
            if (frame == null || frame.getStackSize() < 2) return false;
            SourceValue receiver = frame.getStack(frame.getStackSize() - 2);
            if (receiver == null || receiver.insns == null || receiver.insns.isEmpty()) return false;
            for (AbstractInsnNode producer : receiver.insns) {
                if (!(producer instanceof VarInsnNode) || producer.getOpcode() != Opcodes.ALOAD
                        || ((VarInsnNode) producer).var != receiverLocal) {
                    return false;
                }
            }
            return true;
        }
    }

    private static final class DispatcherEvidence {
        final int headerBlock, transitionCases;
        DispatcherEvidence(int headerBlock, int transitionCases) {
            this.headerBlock = headerBlock;
            this.transitionCases = transitionCases;
        }
    }

    private static final class PathState {
        final int block, definition;
        PathState(int block, int definition) {
            this.block = block;
            this.definition = definition;
        }
    }

    private static final class Graph {
        int executable, blocks, normalEdges, exceptionEdges, branches, conditionalBranches, gotos,
                switches, switchCases, loopSccs, loopBlocks, backEdges;
        final List<SwitchInfo> switchesInfo = new ArrayList<>();
        final Map<AbstractInsnNode, Integer> locations = new IdentityHashMap<>();
        final Map<AbstractInsnNode, Integer> instructionIndex = new IdentityHashMap<>();
        final List<Integer> blockStarts = new ArrayList<>(), blockEnds = new ArrayList<>();
        final List<Set<Integer>> normalAdj = new ArrayList<>(), exceptionAdj = new ArrayList<>();
        int[] blockAt = new int[0], sccByBlock = new int[0];

        static Graph build(MethodNode m) {
            Graph g = new Graph();
            List<AbstractInsnNode> code = new ArrayList<>();
            Map<AbstractInsnNode, Integer> index = new IdentityHashMap<>();
            for (AbstractInsnNode n = m.instructions.getFirst(); n != null; n = n.getNext()) {
                if (n.getOpcode() >= 0) { index.put(n, code.size()); g.locations.put(n, code.size()); code.add(n); }
            }
            g.instructionIndex.putAll(index);
            g.executable = code.size();
            if (code.isEmpty()) return g;
            Set<Integer> starts = new TreeSet<>(); starts.add(0);
            for (AbstractInsnNode n : code) {
                int i = index.get(n), op = n.getOpcode();
                if (n instanceof JumpInsnNode) {
                    addTarget(starts, index, ((JumpInsnNode) n).label);
                    if (i + 1 < code.size()) starts.add(i + 1);
                } else if (n instanceof TableSwitchInsnNode) {
                    TableSwitchInsnNode s = (TableSwitchInsnNode) n;
                    addTarget(starts, index, s.dflt); for (LabelNode l : s.labels) addTarget(starts, index, l);
                    if (i + 1 < code.size()) starts.add(i + 1);
                } else if (n instanceof LookupSwitchInsnNode) {
                    LookupSwitchInsnNode s = (LookupSwitchInsnNode) n;
                    addTarget(starts, index, s.dflt); for (LabelNode l : s.labels) addTarget(starts, index, l);
                    if (i + 1 < code.size()) starts.add(i + 1);
                } else if (isTerminal(op) && i + 1 < code.size()) starts.add(i + 1);
            }
            if (m.tryCatchBlocks != null) for (TryCatchBlockNode t : m.tryCatchBlocks) {
                addTarget(starts, index, t.start); addTarget(starts, index, t.handler); addTarget(starts, index, t.end);
            }
            List<Integer> sorted = new ArrayList<>(starts); sorted.removeIf(i -> i < 0 || i >= code.size());
            Collections.sort(sorted); g.blocks = sorted.size();
            int[] blockAt = new int[code.size()];
            for (int b = 0; b < sorted.size(); b++) {
                int end = b + 1 < sorted.size() ? sorted.get(b + 1) : code.size();
                g.blockStarts.add(sorted.get(b)); g.blockEnds.add(end - 1);
                for (int i = sorted.get(b); i < end; i++) blockAt[i] = b;
            }
            g.blockAt = blockAt;
            List<Set<Integer>> adj = new ArrayList<>(); for (int i = 0; i < g.blocks; i++) adj.add(new TreeSet<>());
            for (int i = 0; i < g.blocks; i++) g.normalAdj.add(new TreeSet<>());
            for (int i = 0; i < g.blocks; i++) g.exceptionAdj.add(new TreeSet<>());
            Set<String> normal = new HashSet<>(), exception = new HashSet<>();
            for (int b = 0; b < g.blocks; b++) {
                int begin = sorted.get(b), end = b + 1 < sorted.size() ? sorted.get(b + 1) : code.size();
                AbstractInsnNode tail = code.get(end - 1); int op = tail.getOpcode();
                if (tail instanceof JumpInsnNode) {
                    g.branches++; if (isConditional(op)) g.conditionalBranches++; if (op == Opcodes.GOTO) g.gotos++;
                    addNormal(adj, normal, b, targetBlock(index, blockAt, ((JumpInsnNode) tail).label));
                    if (isConditional(op) && end < code.size()) addNormal(adj, normal, b, blockAt[end]);
                } else if (tail instanceof TableSwitchInsnNode) {
                    TableSwitchInsnNode s = (TableSwitchInsnNode) tail; g.switches++; g.switchCases += s.labels.size();
                    int loc = index.get(tail); Set<Integer> targets = new TreeSet<>();
                    targets.add(targetBlock(index, blockAt, s.dflt)); for (LabelNode l : s.labels) targets.add(targetBlock(index, blockAt, l));
                    for (int x : targets) addNormal(adj, normal, b, x);
                    g.switchesInfo.add(new SwitchInfo(tail, loc, s.labels.size(), targets.size()));
                } else if (tail instanceof LookupSwitchInsnNode) {
                    LookupSwitchInsnNode s = (LookupSwitchInsnNode) tail; g.switches++; g.switchCases += s.labels.size();
                    int loc = index.get(tail); Set<Integer> targets = new TreeSet<>();
                    targets.add(targetBlock(index, blockAt, s.dflt)); for (LabelNode l : s.labels) targets.add(targetBlock(index, blockAt, l));
                    for (int x : targets) addNormal(adj, normal, b, x);
                    g.switchesInfo.add(new SwitchInfo(tail, loc, s.labels.size(), targets.size()));
                } else if (!isTerminal(op) && end < code.size()) addNormal(adj, normal, b, blockAt[end]);
            }
            if (m.tryCatchBlocks != null) for (TryCatchBlockNode t : m.tryCatchBlocks) {
                Integer from = labelIndex(index, t.start), to = labelIndex(index, t.end), handler = labelIndex(index, t.handler);
                if (from == null || handler == null) continue; if (to == null) to = code.size();
                int hb = blockAt[Math.min(handler, code.size() - 1)];
                for (int b = 0; b < g.blocks; b++) {
                    int begin = sorted.get(b), end = b + 1 < sorted.size() ? sorted.get(b + 1) : code.size();
                    if (begin < to && end > from) {
                        String key = b + ":" + hb;
                        if (exception.add(key)) { g.exceptionEdges++; g.exceptionAdj.get(b).add(hb); }
                    }
                }
            }
            g.normalEdges = normal.size();
            for (int from = 0; from < adj.size(); from++) g.normalAdj.get(from).addAll(adj.get(from));
            g.backEdges = 0;
            for (String key : normal) { String[] p = key.split(":"); if (Integer.parseInt(p[1]) <= Integer.parseInt(p[0])) g.backEdges++; }
            List<List<Integer>> components = scc(adj);
            g.sccByBlock = new int[g.blocks]; Arrays.fill(g.sccByBlock, -1);
            for (int componentId = 0; componentId < components.size(); componentId++) {
                List<Integer> component = components.get(componentId);
                for (Integer block : component) g.sccByBlock[block] = componentId;
                boolean loop = component.size() > 1 || (component.size() == 1
                        && adj.get(component.get(0)).contains(component.get(0)));
                if (loop) { g.loopSccs++; g.loopBlocks += component.size(); }
            }
            return g;
        }

        int location(AbstractInsnNode n) { Integer i = locations.get(n); return i == null ? -1 : i; }
        int blockFor(AbstractInsnNode n) {
            Integer i = instructionIndex.get(n);
            return i == null || i < 0 || i >= blockAt.length ? 0 : blockAt[i];
        }
        int targetBlock(LabelNode label) {
            Integer i = labelIndex(instructionIndex, label);
            return i == null || i < 0 || i >= blockAt.length ? 0 : blockAt[i];
        }
        boolean hasBackEdgeFrom(int from) {
            for (Integer to : normalAdj.get(from)) if (to <= from) return true;
            return false;
        }
        private static void addTarget(Set<Integer> starts, Map<AbstractInsnNode, Integer> index, LabelNode l) {
            Integer i = labelIndex(index, l); if (i != null) starts.add(i);
        }
        private static Integer labelIndex(Map<AbstractInsnNode, Integer> index, LabelNode l) {
            AbstractInsnNode n = l; while (n != null && !index.containsKey(n)) n = n.getNext(); return n == null ? null : index.get(n);
        }
        private static int targetBlock(Map<AbstractInsnNode, Integer> index, int[] blockAt, LabelNode l) {
            Integer i = labelIndex(index, l); return i == null ? 0 : blockAt[i];
        }
        private static void addNormal(List<Set<Integer>> adj, Set<String> all, int from, int to) {
            if (to < 0 || to >= adj.size()) return; adj.get(from).add(to); all.add(from + ":" + to);
        }
        private static List<List<Integer>> scc(List<Set<Integer>> adj) {
            int n = adj.size(); int[] idx = new int[n], low = new int[n], next = {0};
            Arrays.fill(idx, -1); boolean[] on = new boolean[n]; ArrayDeque<Integer> stack = new ArrayDeque<>();
            List<List<Integer>> components = new ArrayList<>();
            for (int v = 0; v < n; v++) if (idx[v] < 0) tarjan(v, adj, idx, low, on, stack, next, components);
            return components;
        }
        private static void tarjan(int v, List<Set<Integer>> adj, int[] idx, int[] low, boolean[] on,
                                   ArrayDeque<Integer> stack, int[] next, List<List<Integer>> components) {
            idx[v] = low[v] = next[0]++; stack.push(v); on[v] = true;
            for (int w : adj.get(v)) {
                if (idx[w] < 0) tarjan(w, adj, idx, low, on, stack, next, components);
                if (on[w]) low[v] = Math.min(low[v], low[w]);
            }
            if (low[v] == idx[v]) {
                List<Integer> component = new ArrayList<>(); int w;
                do { w = stack.pop(); on[w] = false; component.add(w); } while (w != v);
                components.add(component);
            }
        }
    }

    private static final class SwitchInfo {
        final AbstractInsnNode node; final int location, cases, uniqueCases;
        SwitchInfo(AbstractInsnNode n, int l, int c, int u) { node = n; location = l; cases = c; uniqueCases = u; }
    }

    private static final class SwitchTarget {
        final int key, block; final boolean defaultTarget;
        SwitchTarget(int k, int b, boolean d) { key = k; block = b; defaultTarget = d; }
    }

    private static final class Candidate {
        final String owner, method, kind, location, signal, confidence, evidence;
        Candidate(String o, String m, String k, String l, String s, String c, String e) {
            owner=o; method=m; kind=k; location=l; signal=s; confidence=c; evidence=e;
        }
        String toRow() { return String.join("\t", owner, method, kind, location, signal, confidence, clean(evidence)); }
    }

    private static final class ClassBytes { final String entry; final byte[] bytes; ClassBytes(String e, byte[] b) { entry=e; bytes=b; } }
    private static final class ScanResult {
        int classEntries, parsedClasses, malformedClasses, methodCount, methodsWithCode, methodsWithBlocks,
                methodsWithBranches, methodsWithSwitches, methodsWithLoops, methodsWithExceptionEdges,
                methodsWithState, methodsWithDispatchers, methodsWithOpaque, methodsWithZkm, analysisErrors;
        final List<String> methods = new ArrayList<>(), candidates = new ArrayList<>(), recovery = new ArrayList<>(), classes = new ArrayList<>();
    }

    private static void write(ScanResult r, Path input, Path out, String label) throws Exception {
        List<String> methods = new ArrayList<>(); methods.add(METHOD_HEADER); methods.addAll(r.methods);
        List<String> candidates = new ArrayList<>(); candidates.add(CANDIDATE_HEADER); candidates.addAll(r.candidates);
        List<String> recovery = new ArrayList<>(); recovery.add(RECOVERY_HEADER); recovery.addAll(r.recovery);
        List<String> classes = new ArrayList<>(); classes.add(CLASS_HEADER); classes.addAll(r.classes);
        Files.write(out.resolve("methods.tsv"), methods, StandardCharsets.UTF_8);
        Files.write(out.resolve("candidates.tsv"), candidates, StandardCharsets.UTF_8);
        Files.write(out.resolve("recovery.tsv"), recovery, StandardCharsets.UTF_8);
        Files.write(out.resolve("classes.tsv"), classes, StandardCharsets.UTF_8);
        String sha = hex(MessageDigest.getInstance("SHA-256").digest(Files.readAllBytes(input)));
        List<String> audit = new ArrayList<>();
        audit.add("label=" + clean(label)); audit.add("input=" + input); audit.add("input_sha256=" + sha);
        audit.add("class_entries=" + r.classEntries); audit.add("parsed_classes=" + r.parsedClasses);
        audit.add("malformed_classes=" + r.malformedClasses); audit.add("methods=" + r.methodCount);
        audit.add("methods_with_code=" + r.methodsWithCode); audit.add("methods_with_blocks=" + r.methodsWithBlocks);
        audit.add("methods_with_branches=" + r.methodsWithBranches); audit.add("methods_with_switches=" + r.methodsWithSwitches);
        audit.add("methods_with_loops=" + r.methodsWithLoops); audit.add("methods_with_exception_edges=" + r.methodsWithExceptionEdges);
        audit.add("methods_with_state_candidates=" + r.methodsWithState); audit.add("methods_with_dispatcher_candidates=" + r.methodsWithDispatchers);
        audit.add("methods_with_opaque_candidates=" + r.methodsWithOpaque);
        audit.add("methods_with_zkm_flow_candidates=" + r.methodsWithZkm);
        audit.add("analysis_errors=" + r.analysisErrors);
        audit.add("candidate_rows=" + r.candidates.size()); audit.add("recovery_rows=" + r.recovery.size()); audit.add("read_only=true");
        Files.write(out.resolve("audit.txt"), audit, StandardCharsets.UTF_8);
        boolean pass = r.classEntries == r.parsedClasses && r.malformedClasses == 0 && r.analysisErrors == 0
                && new HashSet<String>(r.methods).size() == r.methods.size();
        Files.write(out.resolve("gate.txt"), Collections.singletonList(pass ? "PASS" : "FAIL"), StandardCharsets.UTF_8);
    }

    private static byte[] readAll(InputStream in) throws IOException { ByteArrayOutputStream b = new ByteArrayOutputStream(); byte[] buf = new byte[8192]; int n; while ((n = in.read(buf)) >= 0) b.write(buf, 0, n); return b.toByteArray(); }
    private static String hex(byte[] b) { StringBuilder s = new StringBuilder(); for (byte x : b) s.append(String.format("%02X", x)); return s.toString(); }
    private static String clean(String s) { return String.valueOf(s).replace('\t', ' ').replace('\r', ' ').replace('\n', ' '); }
    private static String reason(Throwable t) { String s = t.getClass().getSimpleName() + ":" + String.valueOf(t.getMessage()); return clean(s).substring(0, Math.min(180, clean(s).length())); }
    private static AbstractInsnNode previousCode(AbstractInsnNode n) { if (n == null) return null; AbstractInsnNode p = n.getPrevious(); while (p != null && p.getOpcode() < 0) p = p.getPrevious(); return p; }
    private static boolean isIntStore(int op) { return op == Opcodes.ISTORE; }
    private static boolean isIntDescriptor(String d) { return "I".equals(d) || "Z".equals(d) || "B".equals(d) || "S".equals(d) || "C".equals(d); }
    private static boolean isTerminal(int op) { return op >= Opcodes.IRETURN && op <= Opcodes.RETURN || op == Opcodes.ATHROW || op == Opcodes.RET; }
    private static boolean isConditional(int op) { return op >= Opcodes.IFEQ && op <= Opcodes.IFLE || op >= Opcodes.IF_ICMPEQ && op <= Opcodes.IF_ICMPLE || op == Opcodes.IF_ACMPEQ || op == Opcodes.IF_ACMPNE || op == Opcodes.IFNULL || op == Opcodes.IFNONNULL; }
    private static boolean isBinaryInt(int op) { return op >= Opcodes.IF_ICMPEQ && op <= Opcodes.IF_ICMPLE; }
    private static Integer intConstant(AbstractInsnNode n) { if (n == null) return null; int op=n.getOpcode(); if (op>=Opcodes.ICONST_M1 && op<=Opcodes.ICONST_5) return op-Opcodes.ICONST_0; if (n instanceof IntInsnNode && (op==Opcodes.BIPUSH || op==Opcodes.SIPUSH)) return ((IntInsnNode)n).operand; if (n instanceof LdcInsnNode && ((LdcInsnNode)n).cst instanceof Integer) return (Integer)((LdcInsnNode)n).cst; return null; }
}
