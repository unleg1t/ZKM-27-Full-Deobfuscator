package unlegit.zkm;

import org.objectweb.asm.Opcodes;
import org.objectweb.asm.Type;
import org.objectweb.asm.tree.AbstractInsnNode;
import org.objectweb.asm.tree.InsnList;
import org.objectweb.asm.tree.JumpInsnNode;
import org.objectweb.asm.tree.LabelNode;
import org.objectweb.asm.tree.MethodNode;
import org.objectweb.asm.tree.VarInsnNode;
import org.objectweb.asm.tree.analysis.Analyzer;
import org.objectweb.asm.tree.analysis.BasicInterpreter;
import org.objectweb.asm.tree.analysis.BasicValue;
import org.objectweb.asm.tree.analysis.Frame;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * Reifies values carried across unary conditional edges as fresh locals.
 * The conditional itself and both of its runtime outcomes are preserved.
 */
final class ResidualStackMaterializer {
    private ResidualStackMaterializer() {
    }

    static List<Rewrite> materialize(MethodNode method, String owner) throws Exception {
        if ("<init>".equals(method.name) || hasUnsupportedControlFlow(method)) {
            return java.util.Collections.emptyList();
        }

        Frame<BasicValue>[] frames = new Analyzer<>(new BasicInterpreter())
                .analyze(owner, method);
        Map<AbstractInsnNode, Integer> indexes = instructionIndexes(method);
        Map<String, Integer> residualCounts = new LinkedHashMap<>();
        List<Candidate> candidates = new ArrayList<>();

        for (AbstractInsnNode instruction = method.instructions.getFirst();
             instruction != null; instruction = instruction.getNext()) {
            if (!(instruction instanceof JumpInsnNode)
                    || !isUnaryConditional(instruction.getOpcode())) {
                continue;
            }
            AbstractInsnNode previous = previousCode(instruction);
            if (!(previous instanceof VarInsnNode)
                    || !matchingGuardLoad((VarInsnNode) previous,
                    instruction.getOpcode())) {
                continue;
            }
            Integer jumpIndex = indexes.get(instruction);
            Integer loadIndex = indexes.get(previous);
            if (jumpIndex == null || loadIndex == null
                    || jumpIndex < 0 || jumpIndex >= frames.length
                    || loadIndex < 0 || loadIndex >= frames.length) {
                continue;
            }
            Frame<BasicValue> jumpFrame = frames[jumpIndex];
            Frame<BasicValue> loadFrame = frames[loadIndex];
            if (jumpFrame == null || loadFrame == null
                    || jumpFrame.getStackSize() <= 1
                    || loadFrame.getStackSize() != jumpFrame.getStackSize() - 1
                    || loadFrame.getStackSize() == 0) {
                continue;
            }
            List<BasicValue> values = spillableValues(loadFrame);
            if (values == null) continue;
            VarInsnNode load = (VarInsnNode) previous;
            Candidate candidate = new Candidate(load, (JumpInsnNode) instruction,
                    values, guardKey(load, instruction.getOpcode()));
            candidates.add(candidate);
            residualCounts.put(candidate.group,
                    residualCounts.getOrDefault(candidate.group, 0) + 1);
        }

        List<Candidate> eligible = new ArrayList<>();
        for (Candidate candidate : candidates) {
            if (residualCounts.getOrDefault(candidate.group, 0) >= 2) {
                eligible.add(candidate);
            }
        }
        if (eligible.isEmpty()) return java.util.Collections.emptyList();

        int nextLocal = method.maxLocals;
        for (Candidate candidate : eligible) {
            candidate.locals = new int[candidate.values.size()];
            int firstLocal = nextLocal;
            for (int index = 0; index < candidate.values.size(); index++) {
                candidate.locals[index] = nextLocal;
                nextLocal += candidate.values.get(index).getSize();
            }
            candidate.localSlots = nextLocal - firstLocal;
        }

        List<Rewrite> rewrites = new ArrayList<>();
        for (Candidate candidate : eligible) {
            LabelNode originalTarget = candidate.jump.label;
            LabelNode takenTrampoline = new LabelNode();

            InsnList spill = new InsnList();
            for (int index = candidate.values.size() - 1; index >= 0; index--) {
                spill.add(new VarInsnNode(storeOpcode(candidate.values.get(index)),
                        candidate.locals[index]));
            }
            method.instructions.insertBefore(candidate.load, spill);

            InsnList fallthroughReload = reload(candidate.values, candidate.locals);
            method.instructions.insert(candidate.jump, fallthroughReload);

            candidate.jump.label = takenTrampoline;
            InsnList takenReload = new InsnList();
            // Ordinary predecessors skip the edge-specific reload. The rewritten
            // conditional enters at the trampoline and falls through to the
            // original target, avoiding an artificial method-end back edge.
            takenReload.add(new JumpInsnNode(Opcodes.GOTO, originalTarget));
            takenReload.add(takenTrampoline);
            takenReload.add(reload(candidate.values, candidate.locals));
            method.instructions.insertBefore(originalTarget, takenReload);

            rewrites.add(new Rewrite(candidate.jump, candidate.values.size(),
                    candidate.locals[0], candidate.localSlots,
                    valueKinds(candidate.values)));
        }
        method.maxLocals = Math.max(method.maxLocals, nextLocal);
        return rewrites;
    }

    private static boolean hasUnsupportedControlFlow(MethodNode method) {
        if ((method.access & Opcodes.ACC_SYNCHRONIZED) != 0) return true;
        for (AbstractInsnNode instruction = method.instructions.getFirst();
             instruction != null; instruction = instruction.getNext()) {
            int opcode = instruction.getOpcode();
            if (opcode == Opcodes.JSR || opcode == Opcodes.RET
                    || opcode == Opcodes.MONITORENTER || opcode == Opcodes.MONITOREXIT) {
                return true;
            }
        }
        return false;
    }

    private static List<BasicValue> spillableValues(Frame<BasicValue> frame) {
        List<BasicValue> values = new ArrayList<>();
        for (int index = 0; index < frame.getStackSize(); index++) {
            BasicValue value = frame.getStack(index);
            if (value == null || value == BasicValue.UNINITIALIZED_VALUE
                    || value == BasicValue.RETURNADDRESS_VALUE
                    || value.getType() == null) {
                return null;
            }
            int sort = value.getType().getSort();
            if (sort == Type.VOID || sort == Type.METHOD) return null;
            values.add(value);
        }
        return values;
    }

    private static InsnList reload(List<BasicValue> values, int[] locals) {
        InsnList result = new InsnList();
        for (int index = 0; index < values.size(); index++) {
            result.add(new VarInsnNode(loadOpcode(values.get(index)), locals[index]));
        }
        return result;
    }

    private static int storeOpcode(BasicValue value) {
        return value.getType().getOpcode(Opcodes.ISTORE);
    }

    private static int loadOpcode(BasicValue value) {
        return value.getType().getOpcode(Opcodes.ILOAD);
    }

    private static String valueKinds(List<BasicValue> values) {
        StringBuilder result = new StringBuilder();
        for (BasicValue value : values) {
            if (result.length() > 0) result.append(',');
            result.append(value.getType().getDescriptor());
        }
        return result.toString();
    }

    private static boolean isUnaryConditional(int opcode) {
        return opcode >= Opcodes.IFEQ && opcode <= Opcodes.IFLE
                || opcode == Opcodes.IFNULL || opcode == Opcodes.IFNONNULL;
    }

    private static boolean matchingGuardLoad(VarInsnNode load, int opcode) {
        if (opcode == Opcodes.IFNULL || opcode == Opcodes.IFNONNULL) {
            return load.getOpcode() == Opcodes.ALOAD;
        }
        return load.getOpcode() == Opcodes.ILOAD;
    }

    private static String guardKey(VarInsnNode load, int opcode) {
        return (opcode == Opcodes.IFNULL || opcode == Opcodes.IFNONNULL ? "ref" : "int")
                + ':' + load.var;
    }

    private static AbstractInsnNode previousCode(AbstractInsnNode instruction) {
        AbstractInsnNode current = instruction == null ? null : instruction.getPrevious();
        while (current != null && current.getOpcode() < 0) current = current.getPrevious();
        return current;
    }

    private static Map<AbstractInsnNode, Integer> instructionIndexes(MethodNode method) {
        Map<AbstractInsnNode, Integer> result = new java.util.IdentityHashMap<>();
        int index = 0;
        for (AbstractInsnNode instruction = method.instructions.getFirst();
             instruction != null; instruction = instruction.getNext()) {
            result.put(instruction, index++);
        }
        return result;
    }

    static final class Rewrite {
        final JumpInsnNode jump;
        final int values;
        final int firstLocal;
        final int localSlots;
        final String valueKinds;

        Rewrite(JumpInsnNode jump, int values, int firstLocal, int localSlots,
                String valueKinds) {
            this.jump = jump;
            this.values = values;
            this.firstLocal = firstLocal;
            this.localSlots = localSlots;
            this.valueKinds = valueKinds;
        }
    }

    private static final class Candidate {
        final VarInsnNode load;
        final JumpInsnNode jump;
        final List<BasicValue> values;
        final String group;
        int[] locals;
        int localSlots;

        Candidate(VarInsnNode load, JumpInsnNode jump, List<BasicValue> values,
                  String group) {
            this.load = load;
            this.jump = jump;
            this.values = values;
            this.group = group;
        }
    }
}
