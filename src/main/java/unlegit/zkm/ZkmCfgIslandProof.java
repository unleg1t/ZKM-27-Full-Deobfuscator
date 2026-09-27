package unlegit.zkm;

import org.objectweb.asm.Opcodes;
import org.objectweb.asm.tree.AbstractInsnNode;
import org.objectweb.asm.tree.ClassNode;
import org.objectweb.asm.tree.FieldInsnNode;
import org.objectweb.asm.tree.IincInsnNode;
import org.objectweb.asm.tree.InvokeDynamicInsnNode;
import org.objectweb.asm.tree.JumpInsnNode;
import org.objectweb.asm.tree.LabelNode;
import org.objectweb.asm.tree.LookupSwitchInsnNode;
import org.objectweb.asm.tree.MethodInsnNode;
import org.objectweb.asm.tree.MethodNode;
import org.objectweb.asm.tree.TableSwitchInsnNode;
import org.objectweb.asm.tree.TryCatchBlockNode;
import org.objectweb.asm.tree.VarInsnNode;
import org.objectweb.asm.tree.analysis.Analyzer;
import org.objectweb.asm.tree.analysis.BasicValue;
import org.objectweb.asm.tree.analysis.BasicVerifier;
import org.objectweb.asm.tree.analysis.Frame;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Proves that a contiguous bytecode region is a replaceable control-flow
 * island. Crypto-template recognizers still have to validate the region's
 * effects; this class proves its graph, exception, stack and local boundaries.
 */
public final class ZkmCfgIslandProof {
    private ZkmCfgIslandProof() {
    }

    public static Result prove(ClassNode owner, MethodNode method,
                               AbstractInsnNode startInclusive,
                               AbstractInsnNode endExclusive) {
        return prove(owner, method, startInclusive, endExclusive,
                Contract.closedStackNeutral());
    }

    public static Result prove(ClassNode owner, MethodNode method,
                               AbstractInsnNode startInclusive,
                               AbstractInsnNode endExclusive,
                               Contract contract) {
        if (owner == null || method == null || startInclusive == null
                || contract == null) {
            throw new IllegalArgumentException("owner, method, start and contract are required");
        }
        Analysis analysis = new Analysis(owner, method, startInclusive,
                endExclusive, contract);
        return analysis.run();
    }

    /** Boundary values that a replacement promises to preserve. */
    public static final class Contract {
        private final int entryStack;
        private final int exitStack;
        private final boolean allowContainedExceptionHandlers;
        private final Set<Integer> allowedLiveOutLocals;

        private Contract(int entryStack, int exitStack,
                         boolean allowContainedExceptionHandlers,
                         Set<Integer> allowedLiveOutLocals) {
            if (entryStack < 0 || exitStack < 0) {
                throw new IllegalArgumentException("negative stack size");
            }
            this.entryStack = entryStack;
            this.exitStack = exitStack;
            this.allowContainedExceptionHandlers = allowContainedExceptionHandlers;
            this.allowedLiveOutLocals = Collections.unmodifiableSet(
                    new LinkedHashSet<Integer>(allowedLiveOutLocals));
        }

        public static Contract closedStackNeutral() {
            return new Contract(0, 0, false, Collections.<Integer>emptySet());
        }

        public Contract withAllowedLiveOut(int local) {
            if (local < 0) throw new IllegalArgumentException("negative local");
            Set<Integer> locals = new LinkedHashSet<Integer>(allowedLiveOutLocals);
            locals.add(local);
            return new Contract(entryStack, exitStack,
                    allowContainedExceptionHandlers, locals);
        }

        public Contract withContainedExceptionHandlers() {
            return new Contract(entryStack, exitStack, true,
                    allowedLiveOutLocals);
        }

        public Contract withStackBoundary(int entry, int exit) {
            return new Contract(entry, exit, allowContainedExceptionHandlers,
                    allowedLiveOutLocals);
        }
    }

    public static final class Result {
        private final boolean proven;
        private final List<String> reasons;
        private final int executableInstructions;
        private final int entryInstruction;
        private final int exitInstruction;
        private final Set<Integer> writtenLocals;
        private final Set<Integer> escapingLocals;
        private final Effects effects;

        private Result(boolean proven, List<String> reasons,
                       int executableInstructions, int entryInstruction,
                       int exitInstruction, Set<Integer> writtenLocals,
                       Set<Integer> escapingLocals, Effects effects) {
            this.proven = proven;
            this.reasons = Collections.unmodifiableList(new ArrayList<String>(reasons));
            this.executableInstructions = executableInstructions;
            this.entryInstruction = entryInstruction;
            this.exitInstruction = exitInstruction;
            this.writtenLocals = Collections.unmodifiableSet(
                    new LinkedHashSet<Integer>(writtenLocals));
            this.escapingLocals = Collections.unmodifiableSet(
                    new LinkedHashSet<Integer>(escapingLocals));
            this.effects = effects;
        }

        public boolean isProven() {
            return proven;
        }

        public List<String> reasons() {
            return reasons;
        }

        public int executableInstructions() {
            return executableInstructions;
        }

        public int entryInstruction() {
            return entryInstruction;
        }

        public int exitInstruction() {
            return exitInstruction;
        }

        public Set<Integer> writtenLocals() {
            return writtenLocals;
        }

        public Set<Integer> escapingLocals() {
            return escapingLocals;
        }

        public Effects effects() {
            return effects;
        }

        public String reason() {
            if (reasons.isEmpty()) return "PROVEN";
            StringBuilder result = new StringBuilder();
            for (int index = 0; index < reasons.size(); index++) {
                if (index != 0) result.append(';');
                result.append(reasons.get(index));
            }
            return result.toString();
        }
    }

    /** Inventory that the caller must compare with its exact DES template. */
    public static final class Effects {
        private final Map<String, Integer> methodCalls;
        private final Map<String, Integer> fieldReads;
        private final Map<String, Integer> fieldWrites;
        private final int invokedynamicCalls;
        private final int monitorOperations;

        private Effects(Map<String, Integer> methodCalls,
                        Map<String, Integer> fieldReads,
                        Map<String, Integer> fieldWrites,
                        int invokedynamicCalls, int monitorOperations) {
            this.methodCalls = immutableCopy(methodCalls);
            this.fieldReads = immutableCopy(fieldReads);
            this.fieldWrites = immutableCopy(fieldWrites);
            this.invokedynamicCalls = invokedynamicCalls;
            this.monitorOperations = monitorOperations;
        }

        private static Map<String, Integer> immutableCopy(Map<String, Integer> input) {
            return Collections.unmodifiableMap(new LinkedHashMap<String, Integer>(input));
        }

        public Map<String, Integer> methodCalls() {
            return methodCalls;
        }

        public Map<String, Integer> fieldReads() {
            return fieldReads;
        }

        public Map<String, Integer> fieldWrites() {
            return fieldWrites;
        }

        public int invokedynamicCalls() {
            return invokedynamicCalls;
        }

        public int monitorOperations() {
            return monitorOperations;
        }
    }

    private static final class Analysis {
        private final ClassNode owner;
        private final MethodNode method;
        private final AbstractInsnNode startNode;
        private final AbstractInsnNode endNode;
        private final Contract contract;
        private final List<AbstractInsnNode> all = new ArrayList<AbstractInsnNode>();
        private final List<AbstractInsnNode> code = new ArrayList<AbstractInsnNode>();
        private final IdentityHashMap<AbstractInsnNode, Integer> allIndexes =
                new IdentityHashMap<AbstractInsnNode, Integer>();
        private final IdentityHashMap<AbstractInsnNode, Integer> codeIndexes =
                new IdentityHashMap<AbstractInsnNode, Integer>();
        private final List<String> reasons = new ArrayList<String>();
        private final Map<AbstractInsnNode, List<AbstractInsnNode>> successors =
                new IdentityHashMap<AbstractInsnNode, List<AbstractInsnNode>>();
        private int startAll;
        private int endAll;
        private AbstractInsnNode entry;
        private AbstractInsnNode exit;

        Analysis(ClassNode owner, MethodNode method, AbstractInsnNode startNode,
                 AbstractInsnNode endNode, Contract contract) {
            this.owner = owner;
            this.method = method;
            this.startNode = startNode;
            this.endNode = endNode;
            this.contract = contract;
        }

        Result run() {
            indexInstructions();
            Effects effects = emptyEffects();
            if (reasons.isEmpty()) {
                buildNormalSuccessors();
                validateExceptionRanges();
                validateEdges();
                validateReachability();
                validateFrames();
                validateTerminals();
                effects = effects();
            }
            Set<Integer> written = writtenLocals();
            Set<Integer> escaping = escapingLocals(written);
            escaping.removeAll(contract.allowedLiveOutLocals);
            if (!escaping.isEmpty()) reasons.add("LIVE_OUT_LOCALS=" + escaping);
            return new Result(reasons.isEmpty(), reasons, countInside(),
                    entry == null ? -1 : codeIndexes.get(entry),
                    exit == null ? -1 : codeIndexes.get(exit), written,
                    escaping, effects);
        }

        private void indexInstructions() {
            int index = 0;
            for (AbstractInsnNode node = method.instructions.getFirst(); node != null;
                 node = node.getNext(), index++) {
                allIndexes.put(node, index);
                all.add(node);
                if (node.getOpcode() >= 0) {
                    codeIndexes.put(node, code.size());
                    code.add(node);
                }
            }
            Integer start = allIndexes.get(startNode);
            Integer end = endNode == null ? Integer.valueOf(all.size()) : allIndexes.get(endNode);
            if (start == null) reasons.add("START_NOT_IN_METHOD");
            if (end == null) reasons.add("END_NOT_IN_METHOD");
            if (!reasons.isEmpty()) return;
            startAll = start;
            endAll = end;
            if (startAll >= endAll) {
                reasons.add("EMPTY_OR_REVERSED_REGION");
                return;
            }
            entry = firstCodeAtOrAfter(startAll);
            exit = firstCodeAtOrAfter(endAll);
            if (entry == null || !inside(entry)) reasons.add("NO_EXECUTABLE_ENTRY");
        }

        private void buildNormalSuccessors() {
            for (AbstractInsnNode node : code) {
                List<AbstractInsnNode> next = new ArrayList<AbstractInsnNode>();
                int opcode = node.getOpcode();
                if (node instanceof JumpInsnNode) {
                    JumpInsnNode jump = (JumpInsnNode) node;
                    addUnique(next, labelTarget(jump.label));
                    if (opcode != Opcodes.GOTO && opcode != Opcodes.JSR) {
                        addUnique(next, nextCode(node));
                    }
                } else if (node instanceof TableSwitchInsnNode) {
                    TableSwitchInsnNode table = (TableSwitchInsnNode) node;
                    addUnique(next, labelTarget(table.dflt));
                    for (LabelNode label : table.labels) addUnique(next, labelTarget(label));
                } else if (node instanceof LookupSwitchInsnNode) {
                    LookupSwitchInsnNode lookup = (LookupSwitchInsnNode) node;
                    addUnique(next, labelTarget(lookup.dflt));
                    for (LabelNode label : lookup.labels) addUnique(next, labelTarget(label));
                } else if (!terminal(opcode)) {
                    addUnique(next, nextCode(node));
                }
                successors.put(node, next);
            }
        }

        private void validateExceptionRanges() {
            if (method.tryCatchBlocks == null) return;
            for (TryCatchBlockNode block : method.tryCatchBlocks) {
                Integer protectedStart = allIndexes.get(block.start);
                Integer protectedEnd = allIndexes.get(block.end);
                AbstractInsnNode handler = labelTarget(block.handler);
                if (protectedStart == null || protectedEnd == null || handler == null) {
                    reasons.add("INVALID_EXCEPTION_RANGE");
                    continue;
                }
                boolean protectedOverlap = protectedStart < endAll
                        && protectedEnd > startAll;
                boolean handlerInside = inside(handler);
                if (!protectedOverlap && !handlerInside) continue;
                if (!contract.allowContainedExceptionHandlers) {
                    reasons.add("EXCEPTION_RANGE_TOUCHES_ISLAND");
                    continue;
                }
                if (protectedStart < startAll || protectedEnd > endAll
                        || !handlerInside) {
                    reasons.add("CROSS_BOUNDARY_EXCEPTION_RANGE");
                    continue;
                }
                for (AbstractInsnNode node : code) {
                    int nodeIndex = allIndexes.get(node);
                    if (nodeIndex >= protectedStart && nodeIndex < protectedEnd) {
                        addUnique(successors.get(node), handler);
                    }
                }
            }
        }

        private void validateEdges() {
            for (Map.Entry<AbstractInsnNode, List<AbstractInsnNode>> edge
                    : successors.entrySet()) {
                AbstractInsnNode from = edge.getKey();
                for (AbstractInsnNode target : edge.getValue()) {
                    boolean fromInside = inside(from);
                    boolean targetInside = inside(target);
                    if (!fromInside && targetInside && target != entry) {
                        reasons.add("EXTERNAL_ENTRY=" + codeIndexes.get(from)
                                + "->" + codeIndexes.get(target));
                    }
                    if (fromInside && !targetInside && target != exit) {
                        reasons.add("NONUNIQUE_EXIT=" + codeIndexes.get(from)
                                + "->" + codeIndexes.get(target));
                    }
                }
            }
        }

        private void validateReachability() {
            if (entry == null) return;
            Set<AbstractInsnNode> reached = Collections.newSetFromMap(
                    new IdentityHashMap<AbstractInsnNode, Boolean>());
            ArrayDeque<AbstractInsnNode> queue = new ArrayDeque<AbstractInsnNode>();
            queue.add(entry);
            while (!queue.isEmpty()) {
                AbstractInsnNode current = queue.removeFirst();
                if (!inside(current) || !reached.add(current)) continue;
                List<AbstractInsnNode> next = successors.get(current);
                if (next == null) continue;
                for (AbstractInsnNode target : next) if (inside(target)) queue.addLast(target);
            }
            int expected = countInside();
            if (reached.size() != expected) {
                reasons.add("UNREACHABLE_ISLAND_CODE=" + reached.size() + "/" + expected);
            }
        }

        private void validateFrames() {
            if (entry == null) return;
            try {
                Analyzer<BasicValue> analyzer = new Analyzer<BasicValue>(new BasicVerifier());
                Frame<BasicValue>[] frames = analyzer.analyze(owner.name, method);
                Frame<BasicValue> before = frames[allIndexes.get(entry)];
                if (before == null) {
                    reasons.add("UNREACHABLE_ENTRY_FRAME");
                } else if (before.getStackSize() != contract.entryStack) {
                    reasons.add("ENTRY_STACK=" + before.getStackSize()
                            + "/" + contract.entryStack);
                }
                if (exit != null) {
                    Frame<BasicValue> after = frames[allIndexes.get(exit)];
                    if (after == null) {
                        reasons.add("UNREACHABLE_EXIT_FRAME");
                    } else if (after.getStackSize() != contract.exitStack) {
                        reasons.add("EXIT_STACK=" + after.getStackSize()
                                + "/" + contract.exitStack);
                    }
                }
            } catch (Throwable failure) {
                reasons.add("FRAME_ANALYSIS=" + failure.getClass().getSimpleName());
            }
        }

        private void validateTerminals() {
            if (exit == null) return;
            for (AbstractInsnNode node : code) {
                if (inside(node) && terminal(node.getOpcode())) {
                    reasons.add("TERMINAL_BEFORE_EXIT=" + codeIndexes.get(node));
                }
            }
        }

        private Effects effects() {
            Map<String, Integer> calls = new LinkedHashMap<String, Integer>();
            Map<String, Integer> reads = new LinkedHashMap<String, Integer>();
            Map<String, Integer> writes = new LinkedHashMap<String, Integer>();
            int indy = 0;
            int monitors = 0;
            for (AbstractInsnNode node : code) {
                if (!inside(node)) continue;
                if (node instanceof MethodInsnNode) {
                    MethodInsnNode call = (MethodInsnNode) node;
                    increment(calls, call.getOpcode() + ":" + call.owner + "."
                            + call.name + call.desc);
                } else if (node instanceof FieldInsnNode) {
                    FieldInsnNode field = (FieldInsnNode) node;
                    String key = field.owner + "." + field.name + field.desc;
                    if (field.getOpcode() == Opcodes.GETFIELD
                            || field.getOpcode() == Opcodes.GETSTATIC) increment(reads, key);
                    else increment(writes, key);
                } else if (node instanceof InvokeDynamicInsnNode) {
                    indy++;
                }
                if (node.getOpcode() == Opcodes.MONITORENTER
                        || node.getOpcode() == Opcodes.MONITOREXIT) monitors++;
            }
            return new Effects(calls, reads, writes, indy, monitors);
        }

        private Effects emptyEffects() {
            return new Effects(Collections.<String, Integer>emptyMap(),
                    Collections.<String, Integer>emptyMap(),
                    Collections.<String, Integer>emptyMap(), 0, 0);
        }

        private Set<Integer> writtenLocals() {
            Set<Integer> result = new LinkedHashSet<Integer>();
            if (entry == null) return result;
            for (AbstractInsnNode node : code) {
                if (!inside(node)) continue;
                if (node instanceof VarInsnNode && isStore(node.getOpcode())) {
                    result.add(((VarInsnNode) node).var);
                } else if (node instanceof IincInsnNode) {
                    result.add(((IincInsnNode) node).var);
                }
            }
            return result;
        }

        private Set<Integer> escapingLocals(Set<Integer> written) {
            Set<Integer> result = new LinkedHashSet<Integer>();
            if (written.isEmpty()) return result;
            for (AbstractInsnNode node : code) {
                if (allIndexes.get(node) < endAll || inside(node)) continue;
                if (node instanceof VarInsnNode && isLoad(node.getOpcode())) {
                    int local = ((VarInsnNode) node).var;
                    if (written.contains(local)) result.add(local);
                } else if (node instanceof IincInsnNode) {
                    int local = ((IincInsnNode) node).var;
                    if (written.contains(local)) result.add(local);
                }
            }
            return result;
        }

        private int countInside() {
            int count = 0;
            for (AbstractInsnNode node : code) if (inside(node)) count++;
            return count;
        }

        private boolean inside(AbstractInsnNode node) {
            Integer index = allIndexes.get(node);
            return index != null && index >= startAll && index < endAll;
        }

        private AbstractInsnNode firstCodeAtOrAfter(int allIndex) {
            for (int index = Math.max(0, allIndex); index < all.size(); index++) {
                AbstractInsnNode node = all.get(index);
                if (node.getOpcode() >= 0) return node;
            }
            return null;
        }

        private AbstractInsnNode nextCode(AbstractInsnNode node) {
            Integer index = codeIndexes.get(node);
            if (index == null || index + 1 >= code.size()) return null;
            return code.get(index + 1);
        }

        private AbstractInsnNode labelTarget(LabelNode label) {
            Integer index = allIndexes.get(label);
            return index == null ? null : firstCodeAtOrAfter(index);
        }
    }

    private static boolean terminal(int opcode) {
        return opcode >= Opcodes.IRETURN && opcode <= Opcodes.RETURN
                || opcode == Opcodes.ATHROW || opcode == Opcodes.RET;
    }

    private static boolean isStore(int opcode) {
        return opcode >= Opcodes.ISTORE && opcode <= Opcodes.ASTORE;
    }

    private static boolean isLoad(int opcode) {
        return opcode >= Opcodes.ILOAD && opcode <= Opcodes.ALOAD
                || opcode == Opcodes.RET;
    }

    private static void addUnique(List<AbstractInsnNode> values,
                                  AbstractInsnNode value) {
        if (values != null && value != null && !values.contains(value)) values.add(value);
    }

    private static void increment(Map<String, Integer> values, String key) {
        Integer old = values.get(key);
        values.put(key, old == null ? 1 : old + 1);
    }
}
