package unlegit.zkm;

import org.objectweb.asm.Opcodes;
import org.objectweb.asm.Type;
import org.objectweb.asm.tree.AbstractInsnNode;
import org.objectweb.asm.tree.ClassNode;
import org.objectweb.asm.tree.FrameNode;
import org.objectweb.asm.tree.IincInsnNode;
import org.objectweb.asm.tree.InsnList;
import org.objectweb.asm.tree.IntInsnNode;
import org.objectweb.asm.tree.InvokeDynamicInsnNode;
import org.objectweb.asm.tree.JumpInsnNode;
import org.objectweb.asm.tree.LabelNode;
import org.objectweb.asm.tree.LdcInsnNode;
import org.objectweb.asm.tree.LineNumberNode;
import org.objectweb.asm.tree.LookupSwitchInsnNode;
import org.objectweb.asm.tree.MethodInsnNode;
import org.objectweb.asm.tree.MethodNode;
import org.objectweb.asm.tree.MultiANewArrayInsnNode;
import org.objectweb.asm.tree.TableSwitchInsnNode;
import org.objectweb.asm.tree.VarInsnNode;
import org.objectweb.asm.tree.analysis.Analyzer;
import org.objectweb.asm.tree.analysis.BasicInterpreter;
import org.objectweb.asm.tree.analysis.BasicValue;
import org.objectweb.asm.tree.analysis.Frame;
import org.objectweb.asm.tree.analysis.SourceInterpreter;
import org.objectweb.asm.tree.analysis.SourceValue;

import java.util.ArrayList;
import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Specializes a closed method tail for the null and non-null domains of one
 * reference local. The runtime value is retained as an explicit two-way
 * dispatch; no value is assumed by this transformation.
 */
public final class ReferenceSentinelTailSpecializer {
    private static final int MIN_GUARDS = 2;
    private static final long CODE_LIMIT = 65535L;

    private ReferenceSentinelTailSpecializer() {
    }

    /** Scans, proves, and atomically rewrites at most one sentinel in a method. */
    public static Rewrite specialize(ClassNode owner, MethodNode method) {
        if (owner == null || method == null) {
            throw new IllegalArgumentException("owner and method are required");
        }
        String globalFailure = globalFailure(method);
        if (globalFailure != null) return Rewrite.skipped(method, globalFailure);

        Map<AbstractInsnNode, Integer> indexes = instructionIndexes(method);
        Frame<BasicValue>[] frames;
        try {
            frames = new Analyzer<BasicValue>(new BasicInterpreter())
                    .analyze(owner.name, method);
        } catch (Throwable failure) {
            return Rewrite.skipped(method, "analysis-failed:" + shortReason(failure));
        }

        Map<Integer, List<Guard>> guardsByLocal = guardsByLocal(method, indexes);
        List<Plan> proven = new ArrayList<Plan>();
        String firstFailure = null;
        for (Map.Entry<Integer, List<Guard>> entry : guardsByLocal.entrySet()) {
            if (entry.getValue().size() < MIN_GUARDS
                    && !"<init>".equals(method.name)) continue;
            PlanResult result = prove(owner, method, entry.getKey().intValue(),
                    entry.getValue(), indexes, frames);
            if (result.plan != null) proven.add(result.plan);
            else if (firstFailure == null) firstFailure = result.reason;
        }
        if (proven.isEmpty()) {
            return Rewrite.skipped(method, firstFailure == null
                    ? "no-repeated-reference-sentinel" : firstFailure);
        }
        if (proven.size() != 1) {
            return Rewrite.skipped(method, "ambiguous-sentinel-candidates="
                    + proven.size());
        }

        Plan plan = proven.get(0);
        apply(method, plan);
        return Rewrite.changed(method, plan);
    }

    /** Metadata suitable for an archive report adapter. */
    public static final class Rewrite {
        private final boolean changed;
        private final String method;
        private final String reason;
        private final int sentinelLocal;
        private final int guards;
        private final int splitInstruction;
        private final int tailInstructions;
        private final long codeSizeUpperBound;

        private Rewrite(boolean changed, String method, String reason,
                        int sentinelLocal, int guards, int splitInstruction,
                        int tailInstructions, long codeSizeUpperBound) {
            this.changed = changed;
            this.method = method;
            this.reason = reason;
            this.sentinelLocal = sentinelLocal;
            this.guards = guards;
            this.splitInstruction = splitInstruction;
            this.tailInstructions = tailInstructions;
            this.codeSizeUpperBound = codeSizeUpperBound;
        }

        static Rewrite skipped(MethodNode method, String reason) {
            return new Rewrite(false, method.name + method.desc, reason,
                    -1, 0, -1, 0, 0L);
        }

        static Rewrite changed(MethodNode method, Plan plan) {
            return new Rewrite(true, method.name + method.desc,
                    plan.singleDelayedConstructor
                            ? "exact-null-nonnull-delayed-constructor-specialization"
                            : "exact-null-nonnull-tail-specialization", plan.local,
                    plan.guards.size(), plan.splitInstruction,
                    plan.tailInstructions, plan.codeSizeUpperBound);
        }

        public boolean changed() {
            return changed;
        }

        public String method() {
            return method;
        }

        public String reason() {
            return reason;
        }

        public int sentinelLocal() {
            return sentinelLocal;
        }

        public int guards() {
            return guards;
        }

        public int splitInstruction() {
            return splitInstruction;
        }

        public int tailInstructions() {
            return tailInstructions;
        }

        public long codeSizeUpperBound() {
            return codeSizeUpperBound;
        }
    }

    private static PlanResult prove(ClassNode owner, MethodNode method, int local,
                                    List<Guard> guards,
                                    Map<AbstractInsnNode, Integer> indexes,
                                    Frame<BasicValue>[] frames) {
        if (local < firstFreeArgumentLocal(method)) {
            return PlanResult.failed("sentinel-is-parameter-local#" + local);
        }
        int firstGuard = indexes.get(guards.get(0).jump).intValue();
        for (Guard guard : guards) {
            Integer index = indexes.get(guard.jump);
            if (index == null || frames[index.intValue()] == null) {
                return PlanResult.failed("unreachable-guard-local#" + local);
            }
            firstGuard = Math.min(firstGuard, index.intValue());
        }

        VarInsnNode definition = null;
        for (AbstractInsnNode instruction = method.instructions.getFirst();
             instruction != null; instruction = instruction.getNext()) {
            if (!writesLocal(instruction, local)) continue;
            if (definition != null) {
                return PlanResult.failed("reference-local-written-more-than-once#"
                        + local);
            }
            if (!(instruction instanceof VarInsnNode)
                    || instruction.getOpcode() != Opcodes.ASTORE
                    || ((VarInsnNode) instruction).var != local) {
                return PlanResult.failed("non-reference-definition-local#" + local);
            }
            definition = (VarInsnNode) instruction;
        }
        if (definition == null) {
            return PlanResult.failed("missing-reference-definition-local#" + local);
        }
        boolean singleDelayedConstructor = guards.size() < MIN_GUARDS;
        boolean onlyGuardLoads = isUsedOnlyByGuards(method, local, guards);
        if (singleDelayedConstructor) {
            if (!isDelayedStaticConstructorSentinel(
                    owner, method, definition, indexes)) {
                return PlanResult.failed(
                        "single-reference-guard-without-delayed-static-source#"
                                + local);
            }
            if (!onlyGuardLoads) {
                return PlanResult.failed(
                        "single-reference-sentinel-has-non-guard-load#" + local);
            }
        }
        boolean consumeDefinitionAtDispatch = onlyGuardLoads;
        int splitIndex = indexes.get(definition).intValue();
        if (splitIndex >= firstGuard) {
            return PlanResult.failed("definition-not-before-first-guard#" + local);
        }

        AbstractInsnNode tailEntry = nextExecutable(definition);
        if (tailEntry == null) return PlanResult.failed("empty-tail");
        Frame<BasicValue> splitFrame = frames[indexes.get(tailEntry).intValue()];
        if (splitFrame == null || splitFrame.getStackSize() != 0) {
            return PlanResult.failed("non-empty-or-unreachable-split-stack");
        }
        if ("<init>".equals(method.name)
                && !initializedThisBefore(owner, method, definition, indexes)) {
            return PlanResult.failed("constructor-this-not-initialized-before-split");
        }

        Map<AbstractInsnNode, List<AbstractInsnNode>> successors =
                normalSuccessors(method);
        for (Map.Entry<AbstractInsnNode, List<AbstractInsnNode>> entry
                : successors.entrySet()) {
            int source = indexes.get(entry.getKey()).intValue();
            for (AbstractInsnNode target : entry.getValue()) {
                int targetIndex = indexes.get(target).intValue();
                if (source <= splitIndex && targetIndex > splitIndex) {
                    if (entry.getKey() != definition || target != tailEntry) {
                        return PlanResult.failed("prefix-external-entry-into-tail");
                    }
                } else if (source > splitIndex && targetIndex <= splitIndex) {
                    return PlanResult.failed("tail-edge-into-prefix");
                }
            }
        }
        for (Guard guard : guards) {
            Integer target = indexes.get(guard.jump.label);
            if (target == null || target.intValue() <= splitIndex) {
                return PlanResult.failed("guard-target-outside-tail");
            }
        }

        AbstractInsnNode last = previousExecutable(method.instructions.getLast());
        if (last == null || hasFallthrough(last)) {
            return PlanResult.failed("tail-can-fall-through-method-end");
        }
        long size = codeSizeUpperBound(method, definition);
        if (size >= CODE_LIMIT) {
            return PlanResult.failed("specialized-code-too-large=" + size);
        }
        int tailInstructions = 0;
        for (AbstractInsnNode instruction = definition.getNext();
             instruction != null; instruction = instruction.getNext()) {
            if (instruction.getOpcode() >= 0) tailInstructions++;
        }
        return PlanResult.proven(new Plan(local, definition, guards,
                splitIndex, tailInstructions, size, consumeDefinitionAtDispatch,
                singleDelayedConstructor));
    }

    private static boolean isUsedOnlyByGuards(
            MethodNode method, int local, List<Guard> guards) {
        Set<AbstractInsnNode> guardLoads = Collections.newSetFromMap(
                new IdentityHashMap<AbstractInsnNode, Boolean>());
        for (Guard guard : guards) guardLoads.add(guard.load);
        for (AbstractInsnNode instruction = method.instructions.getFirst();
             instruction != null; instruction = instruction.getNext()) {
            if (instruction instanceof VarInsnNode
                    && instruction.getOpcode() == Opcodes.ALOAD
                    && ((VarInsnNode) instruction).var == local
                    && !guardLoads.contains(instruction)) return false;
        }
        return true;
    }

    private static boolean isDelayedStaticConstructorSentinel(
            ClassNode owner,
            MethodNode method,
            VarInsnNode definition,
            Map<AbstractInsnNode, Integer> indexes) {
        if (!"<init>".equals(method.name)) return false;
        Frame<SourceValue>[] frames;
        try {
            frames = new Analyzer<SourceValue>(new SourceInterpreter())
                    .analyze(owner.name, method);
        } catch (Throwable failure) {
            return false;
        }
        Integer definitionIndex = indexes.get(definition);
        if (definitionIndex == null) return false;
        Frame<SourceValue> definitionFrame = frames[definitionIndex.intValue()];
        if (definitionFrame == null || definitionFrame.getStackSize() == 0) {
            return false;
        }
        SourceValue value = definitionFrame.getStack(
                definitionFrame.getStackSize() - 1);
        if (value == null || value.insns.size() != 1) return false;
        AbstractInsnNode source = value.insns.iterator().next();
        if (!(source instanceof MethodInsnNode)
                || source.getOpcode() != Opcodes.INVOKESTATIC) return false;
        MethodInsnNode call = (MethodInsnNode) source;
        Type returnType = Type.getReturnType(call.desc);
        int returnSort = returnType.getSort();
        if (Type.getArgumentTypes(call.desc).length != 0
                || returnSort != Type.OBJECT && returnSort != Type.ARRAY) {
            return false;
        }
        Integer sourceIndex = indexes.get(source);
        if (sourceIndex == null || sourceIndex.intValue() >= definitionIndex.intValue()) {
            return false;
        }

        int executableBetween = 0;
        for (AbstractInsnNode instruction = source.getNext();
             instruction != null && instruction != definition;
             instruction = instruction.getNext()) {
            if (instruction.getOpcode() >= 0) executableBetween++;
        }
        return executableBetween >= 2;
    }

    private static String globalFailure(MethodNode method) {
        if ((method.access & Opcodes.ACC_SYNCHRONIZED) != 0) {
            return "synchronized-method";
        }
        if (method.tryCatchBlocks != null && !method.tryCatchBlocks.isEmpty()) {
            return "try-catch-present";
        }
        if (method.localVariables != null && !method.localVariables.isEmpty()) {
            return "local-variable-table-present";
        }
        if ((method.visibleLocalVariableAnnotations != null
                && !method.visibleLocalVariableAnnotations.isEmpty())
                || (method.invisibleLocalVariableAnnotations != null
                && !method.invisibleLocalVariableAnnotations.isEmpty())) {
            return "local-variable-annotations-present";
        }
        for (AbstractInsnNode instruction = method.instructions.getFirst();
             instruction != null; instruction = instruction.getNext()) {
            int opcode = instruction.getOpcode();
            if (opcode == Opcodes.MONITORENTER || opcode == Opcodes.MONITOREXIT) {
                return "monitor-present";
            }
            if (opcode == Opcodes.JSR || opcode == Opcodes.RET) {
                return "subroutine-present";
            }
        }
        return null;
    }

    private static Map<Integer, List<Guard>> guardsByLocal(
            MethodNode method, Map<AbstractInsnNode, Integer> indexes) {
        Map<Integer, List<Guard>> result =
                new LinkedHashMap<Integer, List<Guard>>();
        for (AbstractInsnNode instruction = method.instructions.getFirst();
             instruction != null; instruction = instruction.getNext()) {
            if (!(instruction instanceof JumpInsnNode)) continue;
            if (instruction.getOpcode() != Opcodes.IFNULL
                    && instruction.getOpcode() != Opcodes.IFNONNULL) continue;
            AbstractInsnNode previous = instruction.getPrevious();
            if (!(previous instanceof VarInsnNode)
                    || previous.getOpcode() != Opcodes.ALOAD) continue;
            VarInsnNode load = (VarInsnNode) previous;
            List<Guard> guards = result.get(Integer.valueOf(load.var));
            if (guards == null) {
                guards = new ArrayList<Guard>();
                result.put(Integer.valueOf(load.var), guards);
            }
            guards.add(new Guard(load, (JumpInsnNode) instruction,
                    indexes.get(instruction).intValue()));
        }
        return result;
    }

    private static boolean initializedThisBefore(
            ClassNode owner, MethodNode method, AbstractInsnNode split,
            Map<AbstractInsnNode, Integer> indexes) {
        Frame<SourceValue>[] frames;
        try {
            frames = new Analyzer<SourceValue>(new SourceInterpreter())
                    .analyze(owner.name, method);
        } catch (Throwable failure) {
            return false;
        }
        int splitIndex = indexes.get(split).intValue();
        for (AbstractInsnNode instruction = method.instructions.getFirst();
             instruction != null; instruction = instruction.getNext()) {
            Integer index = indexes.get(instruction);
            if (index == null || index.intValue() >= splitIndex) break;
            if (!(instruction instanceof MethodInsnNode)
                    || instruction.getOpcode() != Opcodes.INVOKESPECIAL) continue;
            MethodInsnNode call = (MethodInsnNode) instruction;
            if (!"<init>".equals(call.name)
                    || (!owner.name.equals(call.owner)
                    && !owner.superName.equals(call.owner))) continue;
            Frame<SourceValue> frame = frames[index.intValue()];
            if (frame == null) continue;
            int receiverIndex = frame.getStackSize()
                    - Type.getArgumentTypes(call.desc).length - 1;
            if (receiverIndex < 0) continue;
            SourceValue receiver = frame.getStack(receiverIndex);
            if (receiver.insns.size() != 1) continue;
            AbstractInsnNode source = receiver.insns.iterator().next();
            if (source instanceof VarInsnNode
                    && source.getOpcode() == Opcodes.ALOAD
                    && ((VarInsnNode) source).var == 0) return true;
        }
        return false;
    }

    private static void apply(MethodNode method, Plan plan) {
        Clone nullTail = cloneTail(plan, true);
        Clone nonNullTail = cloneTail(plan, false);

        AbstractInsnNode instruction = plan.definition.getNext();
        while (instruction != null) {
            AbstractInsnNode next = instruction.getNext();
            method.instructions.remove(instruction);
            instruction = next;
        }

        JumpInsnNode dispatch = new JumpInsnNode(Opcodes.IFNULL, nullTail.entry);
        InsnList replacement = new InsnList();
        if (!plan.consumeDefinitionAtDispatch) {
            replacement.add(new VarInsnNode(Opcodes.ALOAD, plan.local));
            replacement.add(dispatch);
        }
        replacement.add(nonNullTail.instructions);
        replacement.add(nullTail.instructions);
        if (plan.consumeDefinitionAtDispatch) {
            method.instructions.set(plan.definition, dispatch);
            method.instructions.insert(dispatch, replacement);
        } else {
            method.instructions.insert(plan.definition, replacement);
        }
        removeFrames(method);
        method.maxStack = Math.max(method.maxStack, 1);
    }

    private static Clone cloneTail(Plan plan, boolean nullDomain) {
        Map<LabelNode, LabelNode> labels =
                new IdentityHashMap<LabelNode, LabelNode>();
        for (AbstractInsnNode instruction = plan.definition.getNext();
             instruction != null; instruction = instruction.getNext()) {
            if (instruction instanceof LabelNode) {
                labels.put((LabelNode) instruction, new LabelNode());
            }
        }
        Map<AbstractInsnNode, Guard> byLoad =
                new IdentityHashMap<AbstractInsnNode, Guard>();
        Set<AbstractInsnNode> guardJumps = Collections.newSetFromMap(
                new IdentityHashMap<AbstractInsnNode, Boolean>());
        for (Guard guard : plan.guards) {
            byLoad.put(guard.load, guard);
            guardJumps.add(guard.jump);
        }

        InsnList result = new InsnList();
        LabelNode entry = new LabelNode();
        result.add(entry);
        for (AbstractInsnNode instruction = plan.definition.getNext();
             instruction != null; instruction = instruction.getNext()) {
            if (instruction instanceof FrameNode) continue;
            Guard guard = byLoad.get(instruction);
            if (guard != null) {
                boolean taken = guard.jump.getOpcode() == Opcodes.IFNULL
                        ? nullDomain : !nullDomain;
                if (taken) {
                    LabelNode target = labels.get(guard.jump.label);
                    if (target == null) {
                        throw new IllegalStateException("unmapped guard target");
                    }
                    result.add(new JumpInsnNode(Opcodes.GOTO, target));
                }
                continue;
            }
            if (guardJumps.contains(instruction)) continue;
            if (instruction instanceof LineNumberNode
                    && !labels.containsKey(((LineNumberNode) instruction).start)) {
                continue;
            }
            result.add(instruction.clone(labels));
        }
        return new Clone(entry, result);
    }

    private static void removeFrames(MethodNode method) {
        AbstractInsnNode instruction = method.instructions.getFirst();
        while (instruction != null) {
            AbstractInsnNode next = instruction.getNext();
            if (instruction instanceof FrameNode) {
                method.instructions.remove(instruction);
            }
            instruction = next;
        }
    }

    private static Map<AbstractInsnNode, List<AbstractInsnNode>> normalSuccessors(
            MethodNode method) {
        Map<AbstractInsnNode, List<AbstractInsnNode>> result =
                new IdentityHashMap<AbstractInsnNode, List<AbstractInsnNode>>();
        for (AbstractInsnNode instruction = method.instructions.getFirst();
             instruction != null; instruction = instruction.getNext()) {
            if (instruction.getOpcode() < 0) continue;
            List<AbstractInsnNode> successors = new ArrayList<AbstractInsnNode>();
            if (instruction instanceof JumpInsnNode) {
                JumpInsnNode jump = (JumpInsnNode) instruction;
                addTarget(successors, jump.label);
                if (instruction.getOpcode() != Opcodes.GOTO) {
                    add(successors, nextExecutable(instruction));
                }
            } else if (instruction instanceof TableSwitchInsnNode) {
                TableSwitchInsnNode table = (TableSwitchInsnNode) instruction;
                addTarget(successors, table.dflt);
                for (LabelNode label : table.labels) addTarget(successors, label);
            } else if (instruction instanceof LookupSwitchInsnNode) {
                LookupSwitchInsnNode lookup = (LookupSwitchInsnNode) instruction;
                addTarget(successors, lookup.dflt);
                for (LabelNode label : lookup.labels) addTarget(successors, label);
            } else if (!isTerminal(instruction.getOpcode())) {
                add(successors, nextExecutable(instruction));
            }
            result.put(instruction, successors);
        }
        return result;
    }

    private static void addTarget(List<AbstractInsnNode> result,
                                  LabelNode label) {
        add(result, firstExecutable(label));
    }

    private static void add(List<AbstractInsnNode> result,
                            AbstractInsnNode instruction) {
        if (instruction != null && !result.contains(instruction)) {
            result.add(instruction);
        }
    }

    private static AbstractInsnNode firstExecutable(
            AbstractInsnNode instruction) {
        AbstractInsnNode current = instruction;
        while (current != null && current.getOpcode() < 0) {
            current = current.getNext();
        }
        return current;
    }

    private static AbstractInsnNode nextExecutable(
            AbstractInsnNode instruction) {
        return firstExecutable(instruction == null
                ? null : instruction.getNext());
    }

    private static AbstractInsnNode previousExecutable(
            AbstractInsnNode instruction) {
        AbstractInsnNode current = instruction;
        while (current != null && current.getOpcode() < 0) {
            current = current.getPrevious();
        }
        return current;
    }

    private static boolean hasFallthrough(AbstractInsnNode instruction) {
        int opcode = instruction.getOpcode();
        return !isTerminal(opcode) && opcode != Opcodes.GOTO
                && !(instruction instanceof TableSwitchInsnNode)
                && !(instruction instanceof LookupSwitchInsnNode);
    }

    private static boolean isTerminal(int opcode) {
        return opcode == Opcodes.IRETURN || opcode == Opcodes.LRETURN
                || opcode == Opcodes.FRETURN || opcode == Opcodes.DRETURN
                || opcode == Opcodes.ARETURN || opcode == Opcodes.RETURN
                || opcode == Opcodes.ATHROW;
    }

    private static boolean writesLocal(AbstractInsnNode instruction,
                                       int local) {
        if (instruction instanceof IincInsnNode) {
            return ((IincInsnNode) instruction).var == local;
        }
        if (!(instruction instanceof VarInsnNode)) return false;
        VarInsnNode variable = (VarInsnNode) instruction;
        int opcode = instruction.getOpcode();
        if (opcode == Opcodes.ISTORE || opcode == Opcodes.FSTORE
                || opcode == Opcodes.ASTORE) return variable.var == local;
        if (opcode == Opcodes.LSTORE || opcode == Opcodes.DSTORE) {
            return variable.var == local || variable.var + 1 == local;
        }
        return false;
    }

    private static int firstFreeArgumentLocal(MethodNode method) {
        int local = (method.access & Opcodes.ACC_STATIC) == 0 ? 1 : 0;
        for (Type argument : Type.getArgumentTypes(method.desc)) {
            local += argument.getSize();
        }
        return local;
    }

    private static Map<AbstractInsnNode, Integer> instructionIndexes(
            MethodNode method) {
        Map<AbstractInsnNode, Integer> result =
                new IdentityHashMap<AbstractInsnNode, Integer>();
        int index = 0;
        for (AbstractInsnNode instruction = method.instructions.getFirst();
             instruction != null; instruction = instruction.getNext()) {
            result.put(instruction, Integer.valueOf(index++));
        }
        return result;
    }

    private static long codeSizeUpperBound(MethodNode method,
                                           AbstractInsnNode definition) {
        long prefix = 0L;
        long tail = 0L;
        boolean inTail = false;
        for (AbstractInsnNode instruction = method.instructions.getFirst();
             instruction != null; instruction = instruction.getNext()) {
            long size = instructionSizeUpperBound(instruction);
            if (inTail) tail += size;
            else prefix += size;
            if (instruction == definition) inTail = true;
        }
        return prefix + 12L + tail * 2L;
    }

    private static long instructionSizeUpperBound(
            AbstractInsnNode instruction) {
        if (instruction.getOpcode() < 0) return 0L;
        if (instruction instanceof TableSwitchInsnNode) {
            return 16L + 4L * ((TableSwitchInsnNode) instruction).labels.size();
        }
        if (instruction instanceof LookupSwitchInsnNode) {
            return 12L + 8L * ((LookupSwitchInsnNode) instruction).labels.size();
        }
        if (instruction instanceof JumpInsnNode) return 8L;
        if (instruction instanceof IincInsnNode) return 6L;
        if (instruction instanceof VarInsnNode) return 4L;
        if (instruction instanceof InvokeDynamicInsnNode) return 5L;
        if (instruction instanceof MethodInsnNode) {
            return instruction.getOpcode() == Opcodes.INVOKEINTERFACE
                    ? 5L : 3L;
        }
        if (instruction instanceof MultiANewArrayInsnNode) return 4L;
        if (instruction instanceof LdcInsnNode) return 3L;
        if (instruction instanceof IntInsnNode) {
            return instruction.getOpcode() == Opcodes.SIPUSH ? 3L : 2L;
        }
        switch (instruction.getType()) {
            case AbstractInsnNode.TYPE_INSN:
            case AbstractInsnNode.FIELD_INSN:
                return 3L;
            default:
                return 1L;
        }
    }

    private static String shortReason(Throwable failure) {
        String message = failure.getMessage();
        if (message == null || message.trim().isEmpty()) {
            return failure.getClass().getSimpleName();
        }
        return failure.getClass().getSimpleName() + ':'
                + message.replace('\t', ' ').replace('\r', ' ')
                .replace('\n', ' ');
    }

    private static final class Guard {
        final VarInsnNode load;
        final JumpInsnNode jump;
        final int instruction;

        Guard(VarInsnNode load, JumpInsnNode jump, int instruction) {
            this.load = load;
            this.jump = jump;
            this.instruction = instruction;
        }
    }

    private static final class Plan {
        final int local;
        final VarInsnNode definition;
        final List<Guard> guards;
        final int splitInstruction;
        final int tailInstructions;
        final long codeSizeUpperBound;
        final boolean consumeDefinitionAtDispatch;
        final boolean singleDelayedConstructor;

        Plan(int local, VarInsnNode definition, List<Guard> guards,
             int splitInstruction, int tailInstructions,
             long codeSizeUpperBound, boolean consumeDefinitionAtDispatch,
             boolean singleDelayedConstructor) {
            this.local = local;
            this.definition = definition;
            this.guards = new ArrayList<Guard>(guards);
            this.splitInstruction = splitInstruction;
            this.tailInstructions = tailInstructions;
            this.codeSizeUpperBound = codeSizeUpperBound;
            this.consumeDefinitionAtDispatch = consumeDefinitionAtDispatch;
            this.singleDelayedConstructor = singleDelayedConstructor;
        }
    }

    private static final class PlanResult {
        final Plan plan;
        final String reason;

        private PlanResult(Plan plan, String reason) {
            this.plan = plan;
            this.reason = reason;
        }

        static PlanResult proven(Plan plan) {
            return new PlanResult(plan, null);
        }

        static PlanResult failed(String reason) {
            return new PlanResult(null, reason);
        }
    }

    private static final class Clone {
        final LabelNode entry;
        final InsnList instructions;

        Clone(LabelNode entry, InsnList instructions) {
            this.entry = entry;
            this.instructions = instructions;
        }
    }
}
