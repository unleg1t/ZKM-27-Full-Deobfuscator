package unlegit.zkm;

import org.objectweb.asm.ClassReader;
import org.objectweb.asm.ClassWriter;
import org.objectweb.asm.ConstantDynamic;
import org.objectweb.asm.Handle;
import org.objectweb.asm.Opcodes;
import org.objectweb.asm.Type;
import org.objectweb.asm.tree.AbstractInsnNode;
import org.objectweb.asm.tree.ClassNode;
import org.objectweb.asm.tree.FieldInsnNode;
import org.objectweb.asm.tree.FieldNode;
import org.objectweb.asm.tree.FrameNode;
import org.objectweb.asm.tree.IincInsnNode;
import org.objectweb.asm.tree.InvokeDynamicInsnNode;
import org.objectweb.asm.tree.JumpInsnNode;
import org.objectweb.asm.tree.LookupSwitchInsnNode;
import org.objectweb.asm.tree.MethodInsnNode;
import org.objectweb.asm.tree.MethodNode;
import org.objectweb.asm.tree.TableSwitchInsnNode;
import org.objectweb.asm.tree.TryCatchBlockNode;
import org.objectweb.asm.tree.TypeInsnNode;
import org.objectweb.asm.tree.VarInsnNode;
import org.objectweb.asm.tree.analysis.Analyzer;
import org.objectweb.asm.tree.analysis.BasicVerifier;
import org.objectweb.asm.tree.analysis.Frame;
import org.objectweb.asm.tree.analysis.SourceInterpreter;
import org.objectweb.asm.tree.analysis.SourceValue;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.AtomicMoveNotSupportedException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.StandardCopyOption;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Set;
import java.util.zip.CRC32;
import java.util.zip.ZipEntry;
import java.util.zip.ZipInputStream;
import java.util.zip.ZipOutputStream;

/**
 * Removes archive-unreferenced ZKM bootstrap support after call-site rewriting.
 *
 * <p>The pass recognizes member, string, and integer bootstrap families from
 * descriptors and their private same-class dependency graphs. A family is
 * removed only when every archive reference is either inside that family or
 * inside a proven removable {@code <clinit>} producer slice. Input classes are
 * parsed as bytes and are never defined, loaded, or initialized.</p>
 */
public final class ZkmBootstrapSupportCleaner {
    private static final String BSM_DESC = "(Ljava/lang/invoke/MethodHandles$Lookup;"
            + "Ljava/lang/String;Ljava/lang/invoke/MethodType;)"
            + "Ljava/lang/invoke/CallSite;";
    private static final String MEMBER_LINK_DESC =
            "(Ljava/lang/invoke/MethodHandles$Lookup;"
                    + "Ljava/lang/invoke/MutableCallSite;Ljava/lang/String;"
                    + "Ljava/lang/invoke/MethodType;[Ljava/lang/Object;)"
                    + "Ljava/lang/Object;";
    private static final String MEMBER_RESOLVE_DESC =
            "(Ljava/lang/invoke/MethodHandles$Lookup;"
                    + "Ljava/lang/invoke/MutableCallSite;Ljava/lang/String;"
                    + "Ljava/lang/invoke/MethodType;JJ)Ljava/lang/invoke/MethodHandle;";
    private static final String STRING_LINK_DESC =
            "(Ljava/lang/invoke/MethodHandles$Lookup;"
                    + "Ljava/lang/invoke/MutableCallSite;Ljava/lang/String;"
                    + "[Ljava/lang/Object;)Ljava/lang/Object;";
    private static final String INTEGER_LINK_DESC =
            "(Ljava/lang/invoke/MethodHandles$Lookup;"
                    + "Ljava/lang/invoke/MutableCallSite;Ljava/lang/String;"
                    + "[Ljava/lang/Object;)I";

    private ZkmBootstrapSupportCleaner() {
    }

    public static void main(String[] args) throws Exception {
        if (args.length != 2 && args.length != 3) {
            System.err.println("usage: ZkmBootstrapSupportCleaner <input.jar>"
                    + " <report-dir> [rewritten.jar]");
            System.exit(2);
        }
        clean(Paths.get(args[0]), Paths.get(args[1]),
                args.length == 3 ? Paths.get(args[2]) : null);
    }

    static Summary clean(Path input, Path reportDirectory, Path rewrittenOutput)
            throws Exception {
        Files.createDirectories(reportDirectory);
        validatePaths(input, rewrittenOutput);
        List<EntryBytes> entries = readEntries(input);
        Map<String, byte[]> originalBytes = classBytes(entries);
        Map<String, ClassNode> classes = readClasses(originalBytes);
        Summary summary = new Summary();
        summary.parsedClasses = classes.size();

        ReferenceIndex references = ReferenceIndex.build(classes);
        List<Family> families = discoverFamilies(classes, summary);
        List<String> blockers = new ArrayList<>();
        blockers.add("class\tkind\tbootstrap\tmember\treference\treason");
        List<String> rewrite = new ArrayList<>();
        rewrite.add("class\tkind\tmethod\tstart\tend\taction\treason");
        List<String> members = new ArrayList<>();
        members.add("class\tkind\tmember_type\tname\tdesc\taction");

        for (Family family : families) {
            planInitializer(family, rewrite);
            if (family.reason == null) validateReferences(family, references, blockers);
        }
        rejectOverlaps(families, blockers);
        for (Family family : families) {
            if (family.reason == null) continue;
            if (family.externalReferences != 0) continue;
            boolean retainedField = family.reason.startsWith("non-private-static-field:");
            boolean retainedConditionalInitializer = family.reason.startsWith(
                    "clinit-slice:cfg-island-conditional-business-sink");
            if (!retainedField && !retainedConditionalInitializer) continue;
            if (!references.methodRefs.getOrDefault(family.root,
                    Collections.<RefSite>emptyList()).isEmpty()) continue;
            family.retainedReason = family.reason;
            family.reason = null;
            family.rootOnly = true;
        }

        Map<String, List<Family>> eligibleByClass = new LinkedHashMap<>();
        for (Family family : families) {
            if (family.reason == null) {
                eligibleByClass.computeIfAbsent(family.owner.name,
                        ignored -> new ArrayList<Family>()).add(family);
                family.status = "ELIGIBLE";
                summary.eligibleFamilies++;
            } else {
                family.status = "SKIP";
                summary.skippedFamilies++;
                countBlocked(summary, family);
            }
        }

        ArchiveHierarchy hierarchy = new ArchiveHierarchy(classes);
        Map<String, byte[]> replacements = new LinkedHashMap<>();
        for (Map.Entry<String, List<Family>> entry : eligibleByClass.entrySet()) {
            String ownerName = entry.getKey();
            ClassNode owner = classes.get(ownerName);
            try {
                applyFamilies(owner, entry.getValue(), summary, members, rewrite);
                byte[] bytes = writeClass(owner, hierarchy);
                verifyClass(bytes);
                verifyRemoved(bytes, entry.getValue());
                replacements.put(ownerName, bytes);
                summary.changedClasses++;
                for (Family family : entry.getValue()) {
                    family.status = family.rootOnly ? "VERIFIED_METHODS_ONLY" : "VERIFIED";
                    summary.verifiedFamilies++;
                }
            } catch (Throwable failure) {
                summary.classRollbacks++;
                classes.put(ownerName, readClass(originalBytes.get(ownerName)));
                for (Family family : entry.getValue()) {
                    family.status = "ROLLBACK";
                    family.reason = "class-verification:" + shortReason(failure);
                    summary.eligibleFamilies--;
                    summary.skippedFamilies++;
                }
                rewrite.add(tsv(ownerName, "<class>", "<verify>", -1, -1,
                        "rollback", shortReason(failure)));
            }
        }

        if (rewrittenOutput != null) {
            writeVerifiedArchive(entries, replacements, rewrittenOutput, summary);
        }
        writeReports(input, reportDirectory, rewrittenOutput, summary, families,
                blockers, rewrite, members);
        System.out.println("classes=" + summary.parsedClasses
                + " families=" + families.size()
                + " eligible=" + summary.eligibleFamilies
                + " verified=" + summary.verifiedFamilies
                + " changed_classes=" + summary.changedClasses
                + " report=" + reportDirectory);
        return summary;
    }

    private static void validatePaths(Path input, Path output) throws IOException {
        if (output == null) return;
        Path normalizedInput = input.toAbsolutePath().normalize();
        Path normalizedOutput = output.toAbsolutePath().normalize();
        if (normalizedInput.equals(normalizedOutput)) {
            throw new IllegalArgumentException("rewritten output must not replace input");
        }
        if (normalizedOutput.getParent() != null) {
            Files.createDirectories(normalizedOutput.getParent());
        }
    }

    private static List<Family> discoverFamilies(Map<String, ClassNode> classes,
                                                  Summary summary) {
        List<Family> result = new ArrayList<>();
        for (ClassNode owner : classes.values()) {
            Map<MethodRef, MethodNode> methods = methods(owner);
            for (MethodNode bootstrap : owner.methods) {
                if (!BSM_DESC.equals(bootstrap.desc)
                        || !isPrivateStatic(bootstrap.access)) continue;
                MethodRef root = new MethodRef(owner.name, bootstrap.name, bootstrap.desc);
                Set<MethodRef> closure = dependencyClosure(owner, root, methods);
                Kind kind = classify(closure);
                if (kind == null) continue;
                Family family = new Family(owner, kind, root, closure);
                validateFamilyShape(family, methods);
                if (family.reason == null) addTablePopulators(family, methods);
                result.add(family);
                if (kind == Kind.MEMBER) summary.memberCandidates++;
                else if (kind == Kind.STRING) summary.stringCandidates++;
                else summary.integerCandidates++;
            }
        }
        summary.candidateFamilies = result.size();
        return result;
    }

    private static Kind classify(Set<MethodRef> closure) {
        boolean memberLink = hasDescriptor(closure, MEMBER_LINK_DESC);
        boolean memberResolve = hasDescriptor(closure, MEMBER_RESOLVE_DESC);
        boolean memberIndex = hasDescriptor(closure, "(JJ)I");
        boolean memberTarget = hasDescriptor(closure, "(JJ)Ljava/lang/reflect/Field;")
                || hasDescriptor(closure, "(JJ)Ljava/lang/reflect/Method;");
        boolean stringLink = hasDescriptor(closure, STRING_LINK_DESC);
        boolean stringDecrypt = hasDescriptor(closure, "(IJ)Ljava/lang/String;");
        boolean integerLink = hasDescriptor(closure, INTEGER_LINK_DESC);
        boolean integerDecrypt = hasDescriptor(closure, "(IJ)I");
        int matches = 0;
        Kind result = null;
        if (memberLink && memberResolve && memberIndex && memberTarget) {
            matches++; result = Kind.MEMBER;
        }
        if (stringLink && stringDecrypt) { matches++; result = Kind.STRING; }
        if (integerLink && integerDecrypt) { matches++; result = Kind.INTEGER; }
        return matches == 1 ? result : null;
    }

    private static boolean hasDescriptor(Set<MethodRef> methods, String desc) {
        for (MethodRef method : methods) if (desc.equals(method.desc)) return true;
        return false;
    }

    private static void validateFamilyShape(Family family,
                                            Map<MethodRef, MethodNode> methods) {
        for (MethodRef ref : family.methods) {
            MethodNode method = methods.get(ref);
            if (method == null || !isPrivateStatic(method.access)) {
                family.reason = "non-private-static-method:" + ref.name + ref.desc;
                return;
            }
            collectFields(family, method);
        }
        Map<String, FieldNode> declared = fields(family.owner);
        for (FieldRef ref : family.fields) {
            FieldNode field = declared.get(ref.name + ref.desc);
            if (field == null || !isPrivateStatic(field.access)) {
                family.reason = "non-private-static-field:" + ref.name + ref.desc;
                return;
            }
        }
        if (!expectedFields(family)) family.reason = "support-field-shape";
    }

    private static boolean expectedFields(Family family) {
        int maps = 0, strings = 0, objects = 0, longs = 0, integers = 0;
        for (FieldRef field : family.fields) {
            if ("Ljava/util/Map;".equals(field.desc)) maps++;
            else if ("[Ljava/lang/String;".equals(field.desc)) strings++;
            else if ("[Ljava/lang/Object;".equals(field.desc)) objects++;
            else if ("[J".equals(field.desc)) longs++;
            else if ("[Ljava/lang/Integer;".equals(field.desc)) integers++;
        }
        if (family.kind == Kind.MEMBER) {
            return objects == 1 && strings == 1 && family.fields.size() == 2;
        }
        if (family.kind == Kind.STRING) {
            return maps == 1 && strings == 2 && family.fields.size() == 3;
        }
        return maps == 1 && longs == 1 && integers == 1
                && family.fields.size() == 3;
    }

    private static void addTablePopulators(Family family,
                                           Map<MethodRef, MethodNode> methods) {
        boolean changed;
        do {
            changed = false;
            for (Map.Entry<MethodRef, MethodNode> entry : methods.entrySet()) {
                MethodRef ref = entry.getKey();
                MethodNode method = entry.getValue();
                if (family.methods.contains(ref) || "<clinit>".equals(ref.name)
                        || !"()V".equals(ref.desc) || !isPrivateStatic(method.access)) {
                    continue;
                }
                if (!isTablePopulator(family, method)) continue;
                family.methods.add(ref);
                changed = true;
                for (MethodRef dependency : methodDependencies(family.owner.name, method)) {
                    MethodNode dependencyNode = methods.get(dependency);
                    if (dependencyNode != null && isPrivateStatic(dependencyNode.access)) {
                        family.methods.add(dependency);
                    }
                }
            }
        } while (changed);
    }

    private static boolean isTablePopulator(Family family, MethodNode method) {
        boolean candidateAccess = false;
        boolean arrayStore = false;
        for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
             insn = insn.getNext()) {
            if (insn instanceof FieldInsnNode) {
                FieldInsnNode field = (FieldInsnNode) insn;
                if (!family.owner.name.equals(field.owner)) continue;
                FieldRef ref = new FieldRef(field.owner, field.name, field.desc);
                if (!family.fields.contains(ref)) return false;
                candidateAccess = true;
            }
            if (insn.getOpcode() == Opcodes.AASTORE) arrayStore = true;
            if (insn instanceof InvokeDynamicInsnNode) return false;
        }
        return candidateAccess && arrayStore;
    }

    private static void collectFields(Family family, MethodNode method) {
        for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
             insn = insn.getNext()) {
            if (!(insn instanceof FieldInsnNode)) continue;
            FieldInsnNode field = (FieldInsnNode) insn;
            if (family.owner.name.equals(field.owner)) {
                family.fields.add(new FieldRef(field.owner, field.name, field.desc));
            }
        }
    }

    private static Set<MethodRef> dependencyClosure(ClassNode owner, MethodRef root,
                                                     Map<MethodRef, MethodNode> methods) {
        Set<MethodRef> result = new LinkedHashSet<>();
        ArrayDeque<MethodRef> queue = new ArrayDeque<>();
        queue.add(root);
        while (!queue.isEmpty()) {
            MethodRef current = queue.removeFirst();
            if (!result.add(current)) continue;
            MethodNode method = methods.get(current);
            if (method == null) continue;
            for (MethodRef dependency : methodDependencies(owner.name, method)) {
                if (methods.containsKey(dependency) && !result.contains(dependency)) {
                    queue.addLast(dependency);
                }
            }
        }
        return result;
    }

    private static Set<MethodRef> methodDependencies(String owner, MethodNode method) {
        Set<MethodRef> result = new LinkedHashSet<>();
        for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
             insn = insn.getNext()) {
            if (insn instanceof MethodInsnNode) {
                MethodInsnNode call = (MethodInsnNode) insn;
                if (owner.equals(call.owner)) {
                    result.add(new MethodRef(call.owner, call.name, call.desc));
                }
            } else if (insn instanceof InvokeDynamicInsnNode) {
                InvokeDynamicInsnNode indy = (InvokeDynamicInsnNode) insn;
                addHandleDependency(owner, indy.bsm, result);
                if (indy.bsmArgs != null) {
                    for (Object argument : indy.bsmArgs) {
                        addConstantDependencies(owner, argument, result);
                    }
                }
            } else if (insn instanceof org.objectweb.asm.tree.LdcInsnNode) {
                addConstantDependencies(owner,
                        ((org.objectweb.asm.tree.LdcInsnNode) insn).cst, result);
            }
        }
        return result;
    }

    private static void addConstantDependencies(String owner, Object value,
                                                Set<MethodRef> result) {
        if (value instanceof Handle) {
            addHandleDependency(owner, (Handle) value, result);
        } else if (value instanceof ConstantDynamic) {
            ConstantDynamic dynamic = (ConstantDynamic) value;
            addHandleDependency(owner, dynamic.getBootstrapMethod(), result);
            for (int i = 0; i < dynamic.getBootstrapMethodArgumentCount(); i++) {
                addConstantDependencies(owner, dynamic.getBootstrapMethodArgument(i), result);
            }
        }
    }

    private static void addHandleDependency(String owner, Handle handle,
                                            Set<MethodRef> result) {
        if (handle != null && owner.equals(handle.getOwner())
                && handle.getTag() >= Opcodes.H_INVOKEVIRTUAL) {
            result.add(new MethodRef(handle.getOwner(), handle.getName(), handle.getDesc()));
        }
    }

    private static void planInitializer(Family family, List<String> rewrite) {
        if (family.reason != null) return;
        MethodNode clinit = findMethod(family.owner, "<clinit>", "()V");
        if (clinit == null) {
            family.reason = "missing-clinit";
            return;
        }
        Frame<SourceValue>[] frames;
        ProducerDependencyInterpreter interpreter =
                new ProducerDependencyInterpreter();
        try {
            frames = new Analyzer<>(interpreter).analyze(
                    family.owner.name, clinit);
        } catch (Throwable failure) {
            family.reason = "clinit-analysis:" + shortReason(failure);
            return;
        }
        List<String> linearRewrite = new ArrayList<>();
        List<AbstractInsnNode> segment = new ArrayList<>();
        boolean linearPlan = true;
        for (AbstractInsnNode insn = clinit.instructions.getFirst(); insn != null;
             insn = insn.getNext()) {
            if (insn.getOpcode() < 0) continue;
            if (isBarrier(family, insn)) {
                if (!planSegment(family, clinit, frames, interpreter,
                        segment, linearRewrite)) {
                    linearPlan = false;
                    break;
                }
                segment.clear();
            } else {
                segment.add(insn);
            }
        }
        if (linearPlan && !planSegment(family, clinit, frames, interpreter,
                segment, linearRewrite)) linearPlan = false;
        if (!linearPlan) {
            String linearReason = family.reason;
            family.reason = null;
            family.clinitNodes.clear();
            family.ranges.clear();
            String islandReason = planCfgClosedSupportIsland(family, clinit,
                    frames, interpreter, rewrite);
            if (islandReason != null) {
                family.reason = "clinit-slice:" + islandReason;
                rewrite.add(tsv(family.owner.name,
                        family.kind.name().toLowerCase(Locale.ROOT),
                        "<clinit>()V", -1, -1, "skip-support-island",
                        islandReason + ";linear=" + linearReason));
                return;
            }
        } else {
            rewrite.addAll(linearRewrite);
        }
        if (family.clinitNodes.isEmpty()) {
            family.reason = "no-clinit-producer-slice";
            return;
        }
        for (AbstractInsnNode insn = clinit.instructions.getFirst(); insn != null;
             insn = insn.getNext()) {
            if (touchesFamily(family, insn) && !family.clinitNodes.contains(insn)) {
                family.reason = "uncovered-clinit-reference@"
                        + clinit.instructions.indexOf(insn);
                return;
            }
        }
    }

    private static boolean planSegment(Family family, MethodNode clinit,
                                       Frame<SourceValue>[] frames,
                                       ProducerDependencyInterpreter interpreter,
                                       List<AbstractInsnNode> segment,
                                       List<String> rewrite) {
        if (segment.isEmpty()) return true;
        int lastCandidate = -1;
        for (int i = 0; i < segment.size(); i++) {
            if (touchesFamily(family, segment.get(i))) lastCandidate = i;
        }
        if (lastCandidate < 0) return true;
        Set<AbstractInsnNode> nodes = null;
        AbstractInsnNode start = null;
        AbstractInsnNode end = null;
        String unsafe = "no-safe-cut";
        int finalCandidate = segment.size() - 1;
        for (int candidateEnd = lastCandidate; candidateEnd <= finalCandidate;
             candidateEnd++) {
            Set<AbstractInsnNode> attempt = identitySet();
            for (int i = 0; i <= candidateEnd; i++) attempt.add(segment.get(i));
            AbstractInsnNode attemptedEnd = segment.get(candidateEnd);
            unsafe = retainEscapingPureProducers(clinit, frames, interpreter,
                    attempt, attemptedEnd);
            if (unsafe != null) continue;
            AbstractInsnNode attemptedStart = firstInMethod(clinit, attempt);
            attemptedEnd = lastInMethod(clinit, attempt);
            if (attemptedStart == null || attemptedEnd == null) {
                unsafe = "no-removable-instructions";
                continue;
            }
            unsafe = validateSlice(clinit, frames, attempt, attemptedStart,
                    attemptedEnd);
            if (unsafe != null) continue;
            nodes = attempt;
            start = attemptedStart;
            end = attemptedEnd;
            break;
        }
        if (nodes == null) {
            family.reason = "clinit-slice:" + unsafe;
            return false;
        }
        family.clinitNodes.addAll(nodes);
        Range range = new Range(clinit.instructions.indexOf(start),
                clinit.instructions.indexOf(end), nodes.size());
        family.ranges.add(range);
        rewrite.add(tsv(family.owner.name, family.kind.name().toLowerCase(Locale.ROOT),
                "<clinit>()V", range.start, range.end, "plan-remove-support-slice",
                "empty-stack-no-cross-boundary"));
        return true;
    }

    /**
     * Plans a non-contiguous support island while retaining every observable
     * business sink and its complete data dependencies. The reduced business
     * sinks must form one unconditional, acyclic chain to the sole return.
     */
    private static String planCfgClosedSupportIsland(
            Family family, MethodNode method, Frame<SourceValue>[] frames,
            ProducerDependencyInterpreter interpreter, List<String> rewrite) {
        if (method.tryCatchBlocks != null && !method.tryCatchBlocks.isEmpty()) {
            return "cfg-island-exception-range";
        }
        List<AbstractInsnNode> code = codeInstructions(method);
        if (code.isEmpty()) return "cfg-island-empty";
        Map<AbstractInsnNode, Integer> indexes = new IdentityHashMap<>();
        for (int i = 0; i < code.size(); i++) indexes.put(code.get(i), i);

        int firstTouch = code.size();
        int lastTouch = -1;
        for (int i = 0; i < code.size(); i++) {
            AbstractInsnNode insn = code.get(i);
            int opcode = insn.getOpcode();
            if (opcode == Opcodes.MONITORENTER || opcode == Opcodes.MONITOREXIT
                    || opcode == Opcodes.JSR || opcode == Opcodes.RET) {
                return "cfg-island-monitor-or-subroutine@" + i;
            }
            if (touchesFamily(family, insn)) {
                firstTouch = Math.min(firstTouch, i);
                lastTouch = Math.max(lastTouch, i);
            }
        }
        if (lastTouch < 0) return "cfg-island-no-family-seed";

        // Include the complete producer chain of the first family write, but
        // do not absorb an unrelated support family that precedes this one.
        Set<AbstractInsnNode> familyProducers = identitySet();
        ArrayDeque<AbstractInsnNode> producerQueue = new ArrayDeque<>();
        for (AbstractInsnNode insn : code) {
            if (touchesFamily(family, insn)) producerQueue.addLast(insn);
        }
        while (!producerQueue.isEmpty()) {
            AbstractInsnNode current = producerQueue.removeFirst();
            if (!familyProducers.add(current)) continue;
            Set<AbstractInsnNode> inputs = interpreter.inputs.get(current);
            if (inputs != null) producerQueue.addAll(inputs);
        }
        int regionStart = firstTouch;
        for (AbstractInsnNode producer : familyProducers) {
            Integer index = indexes.get(producer);
            if (index != null) regionStart = Math.min(regionStart, index);
        }

        int returnIndex = -1;
        int returns = 0;
        for (int i = regionStart; i < code.size(); i++) {
            int opcode = code.get(i).getOpcode();
            if (opcode >= Opcodes.IRETURN && opcode <= Opcodes.RETURN) {
                returns++;
                returnIndex = i;
            } else if (opcode == Opcodes.ATHROW) {
                return "cfg-island-throw-exit@" + i;
            }
        }
        if (returns != 1 || returnIndex <= lastTouch) {
            return "cfg-island-exits=" + returns;
        }

        Set<AbstractInsnNode> remove = identitySet();
        Set<AbstractInsnNode> retained = identitySet();
        for (int i = regionStart; i < returnIndex; i++) {
            AbstractInsnNode insn = code.get(i);
            if (isBarrier(family, insn)) retained.add(insn);
            else remove.add(insn);
        }
        retained.add(code.get(returnIndex));
        retainDataDependencies(retained, remove, interpreter);
        retainEscapingMutations(method, frames, retained, remove, interpreter);

        for (AbstractInsnNode insn : code) {
            if (touchesFamily(family, insn) && !remove.contains(insn)) {
                return "cfg-island-family-value-escapes@" + indexes.get(insn);
            }
        }
        if (remove.isEmpty()) return "cfg-island-no-removable-instructions";

        String controlReason = validateRetainedControlChain(code, indexes,
                regionStart, returnIndex, retained, remove);
        if (controlReason != null) return controlReason;

        family.clinitNodes.addAll(remove);
        addRanges(method, family, remove);
        rewrite.add(tsv(family.owner.name,
                family.kind.name().toLowerCase(Locale.ROOT),
                "<clinit>()V", regionStart, returnIndex - 1,
                "plan-remove-cfg-support-island",
                "retained_sinks=" + observableSinks(retained).size()
                        + ",removed=" + remove.size()
                        + ",single_exit=" + returnIndex));
        return null;
    }

    private static List<AbstractInsnNode> codeInstructions(MethodNode method) {
        List<AbstractInsnNode> result = new ArrayList<>();
        for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
             insn = insn.getNext()) {
            if (insn.getOpcode() >= 0) result.add(insn);
        }
        return result;
    }

    private static void retainDataDependencies(
            Set<AbstractInsnNode> retained, Set<AbstractInsnNode> remove,
            ProducerDependencyInterpreter interpreter) {
        ArrayDeque<AbstractInsnNode> queue = new ArrayDeque<>(retained);
        while (!queue.isEmpty()) {
            AbstractInsnNode current = queue.removeFirst();
            Set<AbstractInsnNode> inputs = interpreter.inputs.get(current);
            if (inputs == null) continue;
            for (AbstractInsnNode input : inputs) {
                if (remove.remove(input) && retained.add(input)) queue.addLast(input);
            }
        }
    }

    private static void retainEscapingMutations(
            MethodNode method, Frame<SourceValue>[] frames,
            Set<AbstractInsnNode> retained, Set<AbstractInsnNode> remove,
            ProducerDependencyInterpreter interpreter) {
        boolean changed;
        do {
            changed = false;
            for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
                 insn = insn.getNext()) {
                if (!remove.contains(insn)) continue;
                SourceValue receiver = mutationReceiver(method, frames, insn);
                if (receiver == null
                        || !dependsOnRetained(receiver, retained, interpreter)) continue;
                remove.remove(insn);
                retained.add(insn);
                retainDataDependencies(retained, remove, interpreter);
                changed = true;
            }
        } while (changed);
    }

    private static SourceValue mutationReceiver(MethodNode method,
                                                Frame<SourceValue>[] frames,
                                                AbstractInsnNode insn) {
        int index = method.instructions.indexOf(insn);
        if (index < 0 || index >= frames.length || frames[index] == null) return null;
        Frame<SourceValue> frame = frames[index];
        int opcode = insn.getOpcode();
        if (opcode >= Opcodes.IASTORE && opcode <= Opcodes.SASTORE) {
            return frame.getStackSize() < 3
                    ? null : frame.getStack(frame.getStackSize() - 3);
        }
        if (insn instanceof MethodInsnNode && knownSupportCall((MethodInsnNode) insn)
                && opcode != Opcodes.INVOKESTATIC) {
            int arguments = Type.getArgumentTypes(((MethodInsnNode) insn).desc).length;
            return frame.getStackSize() <= arguments
                    ? null : frame.getStack(frame.getStackSize() - arguments - 1);
        }
        return null;
    }

    private static boolean dependsOnRetained(
            SourceValue value, Set<AbstractInsnNode> retained,
            ProducerDependencyInterpreter interpreter) {
        if (value == null || value.insns == null) return false;
        Set<AbstractInsnNode> seen = identitySet();
        ArrayDeque<AbstractInsnNode> queue = new ArrayDeque<>(value.insns);
        while (!queue.isEmpty()) {
            AbstractInsnNode current = queue.removeFirst();
            if (!seen.add(current)) continue;
            if (retained.contains(current)) return true;
            Set<AbstractInsnNode> inputs = interpreter.inputs.get(current);
            if (inputs != null) queue.addAll(inputs);
        }
        return false;
    }

    private static String validateRetainedControlChain(
            List<AbstractInsnNode> code, Map<AbstractInsnNode, Integer> indexes,
            int regionStart, int returnIndex, Set<AbstractInsnNode> retained,
            Set<AbstractInsnNode> remove) {
        List<Set<Integer>> successors = controlFlow(code, indexes);
        Set<Integer> reachable = reachable(successors, regionStart);
        if (!reachable.contains(returnIndex)) return "cfg-island-unreachable-exit";
        Set<Integer> canExit = reverseReachable(successors, returnIndex);
        if (!canExit.containsAll(reachable)) return "cfg-island-nonterminating-exit";
        List<Set<Integer>> dominators = dominators(successors, reachable, regionStart);
        List<Set<Integer>> postDominators = postDominators(
                successors, reachable, returnIndex);

        List<AbstractInsnNode> sinks = observableSinks(retained);
        Collections.sort(sinks, (left, right) ->
                Integer.compare(indexes.get(left), indexes.get(right)));
        int previous = regionStart;
        for (AbstractInsnNode sink : sinks) {
            int index = indexes.get(sink);
            if (index == returnIndex || index < regionStart) continue;
            if (!reachable.contains(index)
                    || !dominators.get(returnIndex).contains(index)) {
                return "cfg-island-conditional-business-sink@" + index;
            }
            if (!dominators.get(index).contains(previous)
                    || !postDominators.get(previous).contains(index)) {
                return "cfg-island-unordered-business-sink@" + index;
            }
            if (isCyclic(successors, index)) {
                return "cfg-island-cyclic-business-sink@" + index;
            }
            previous = index;
        }
        for (AbstractInsnNode insn : retained) {
            if (insn instanceof JumpInsnNode || insn instanceof TableSwitchInsnNode
                    || insn instanceof LookupSwitchInsnNode) {
                return "cfg-island-retained-control@" + indexes.get(insn);
            }
        }
        return null;
    }

    private static List<AbstractInsnNode> observableSinks(
            Set<AbstractInsnNode> retained) {
        List<AbstractInsnNode> result = new ArrayList<>();
        for (AbstractInsnNode insn : retained) {
            int opcode = insn.getOpcode();
            if (insn instanceof FieldInsnNode || insn instanceof MethodInsnNode
                    || insn instanceof InvokeDynamicInsnNode
                    || opcode >= Opcodes.IASTORE && opcode <= Opcodes.SASTORE
                    || opcode == Opcodes.MONITORENTER || opcode == Opcodes.MONITOREXIT
                    || opcode == Opcodes.ATHROW
                    || opcode >= Opcodes.IRETURN && opcode <= Opcodes.RETURN) {
                result.add(insn);
            }
        }
        return result;
    }

    private static List<Set<Integer>> controlFlow(
            List<AbstractInsnNode> code, Map<AbstractInsnNode, Integer> indexes) {
        List<Set<Integer>> result = new ArrayList<>();
        for (int i = 0; i < code.size(); i++) result.add(new LinkedHashSet<Integer>());
        for (int i = 0; i < code.size(); i++) {
            AbstractInsnNode insn = code.get(i);
            int opcode = insn.getOpcode();
            Set<Integer> out = result.get(i);
            if (insn instanceof JumpInsnNode) {
                addTarget(out, indexes, nextCode(((JumpInsnNode) insn).label));
                if (opcode != Opcodes.GOTO && opcode != Opcodes.JSR && i + 1 < code.size()) {
                    out.add(i + 1);
                }
            } else if (insn instanceof TableSwitchInsnNode) {
                TableSwitchInsnNode table = (TableSwitchInsnNode) insn;
                addTarget(out, indexes, nextCode(table.dflt));
                for (org.objectweb.asm.tree.LabelNode label : table.labels) {
                    addTarget(out, indexes, nextCode(label));
                }
            } else if (insn instanceof LookupSwitchInsnNode) {
                LookupSwitchInsnNode lookup = (LookupSwitchInsnNode) insn;
                addTarget(out, indexes, nextCode(lookup.dflt));
                for (org.objectweb.asm.tree.LabelNode label : lookup.labels) {
                    addTarget(out, indexes, nextCode(label));
                }
            } else if (!(opcode >= Opcodes.IRETURN && opcode <= Opcodes.RETURN)
                    && opcode != Opcodes.ATHROW && i + 1 < code.size()) {
                out.add(i + 1);
            }
        }
        return result;
    }

    private static void addTarget(Set<Integer> targets,
                                  Map<AbstractInsnNode, Integer> indexes,
                                  AbstractInsnNode target) {
        Integer index = indexes.get(target);
        if (index != null) targets.add(index);
    }

    private static Set<Integer> reachable(List<Set<Integer>> edges, int start) {
        Set<Integer> result = new LinkedHashSet<>();
        ArrayDeque<Integer> queue = new ArrayDeque<>();
        queue.add(start);
        while (!queue.isEmpty()) {
            int current = queue.removeFirst();
            if (!result.add(current)) continue;
            queue.addAll(edges.get(current));
        }
        return result;
    }

    private static Set<Integer> reverseReachable(List<Set<Integer>> edges, int exit) {
        List<Set<Integer>> reverse = reverseEdges(edges);
        return reachable(reverse, exit);
    }

    private static List<Set<Integer>> reverseEdges(List<Set<Integer>> edges) {
        List<Set<Integer>> result = new ArrayList<>();
        for (int i = 0; i < edges.size(); i++) result.add(new LinkedHashSet<Integer>());
        for (int i = 0; i < edges.size(); i++) {
            for (int target : edges.get(i)) result.get(target).add(i);
        }
        return result;
    }

    private static List<Set<Integer>> dominators(
            List<Set<Integer>> edges, Set<Integer> nodes, int entry) {
        return fixedDominators(reverseEdges(edges), nodes, entry);
    }

    private static List<Set<Integer>> postDominators(
            List<Set<Integer>> edges, Set<Integer> nodes, int exit) {
        return fixedDominators(edges, nodes, exit);
    }

    private static List<Set<Integer>> fixedDominators(
            List<Set<Integer>> predecessors, Set<Integer> nodes, int root) {
        List<Set<Integer>> result = new ArrayList<>();
        for (int i = 0; i < predecessors.size(); i++) {
            Set<Integer> initial = new LinkedHashSet<>();
            if (i == root) initial.add(root);
            else if (nodes.contains(i)) initial.addAll(nodes);
            result.add(initial);
        }
        boolean changed;
        do {
            changed = false;
            for (int node : nodes) {
                if (node == root) continue;
                Set<Integer> next = null;
                for (int predecessor : predecessors.get(node)) {
                    if (!nodes.contains(predecessor)) continue;
                    if (next == null) next = new LinkedHashSet<>(result.get(predecessor));
                    else next.retainAll(result.get(predecessor));
                }
                if (next == null) next = new LinkedHashSet<>();
                next.add(node);
                if (!next.equals(result.get(node))) {
                    result.set(node, next);
                    changed = true;
                }
            }
        } while (changed);
        return result;
    }

    private static boolean isCyclic(List<Set<Integer>> edges, int node) {
        for (int successor : edges.get(node)) {
            if (successor == node || reachable(edges, successor).contains(node)) return true;
        }
        return false;
    }

    private static void addRanges(MethodNode method, Family family,
                                  Set<AbstractInsnNode> nodes) {
        int start = -1;
        int end = -1;
        int count = 0;
        for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
             insn = insn.getNext()) {
            if (insn.getOpcode() < 0) continue;
            int index = method.instructions.indexOf(insn);
            if (nodes.contains(insn)) {
                if (start < 0) start = index;
                end = index;
                count++;
            } else if (start >= 0) {
                family.ranges.add(new Range(start, end, count));
                start = -1;
                count = 0;
            }
        }
        if (start >= 0) family.ranges.add(new Range(start, end, count));
    }

    /**
     * Keeps complete, side-effect-free producer chains evaluated below a
     * support block. This projects the retained stack through that block
     * without recreating or reordering the business value.
     */
    private static String retainEscapingPureProducers(MethodNode method,
                                                      Frame<SourceValue>[] frames,
                                                      ProducerDependencyInterpreter interpreter,
                                                      Set<AbstractInsnNode> nodes,
                                                      AbstractInsnNode end) {
        AbstractInsnNode next = nextCode(end);
        if (next == null) return null;
        Frame<SourceValue> frame = frames[method.instructions.indexOf(next)];
        if (frame == null) return "unreachable-exit";
        Set<AbstractInsnNode> keep = identitySet();
        ArrayDeque<AbstractInsnNode> queue = new ArrayDeque<>();
        for (int i = 0; i < frame.getStackSize(); i++) {
            SourceValue value = frame.getStack(i);
            if (value == null || value.insns == null) continue;
            for (AbstractInsnNode source : value.insns) {
                if (!nodes.contains(source)) continue;
                queue.addLast(source);
            }
        }
        while (!queue.isEmpty()) {
            AbstractInsnNode producer = queue.removeFirst();
            if (!nodes.contains(producer) || !keep.add(producer)) continue;
            if (!isPureRetainedProducer(producer)) {
                return "impure-stack-value-escapes@"
                        + method.instructions.indexOf(producer) + ":opcode="
                        + producer.getOpcode() + ":exit-stack=" + frame.getStackSize()
                        + ":end=" + method.instructions.indexOf(end)
                        + ":next=" + method.instructions.indexOf(next);
            }
            Set<AbstractInsnNode> inputs = interpreter.inputs.get(producer);
            if (inputs == null) continue;
            for (AbstractInsnNode input : inputs) {
                if (nodes.contains(input)) queue.addLast(input);
            }
        }
        nodes.removeAll(keep);
        return null;
    }

    private static boolean isPureRetainedProducer(AbstractInsnNode insn) {
        int opcode = insn.getOpcode();
        if (opcode == Opcodes.ACONST_NULL
                || opcode >= Opcodes.ICONST_M1 && opcode <= Opcodes.DCONST_1
                || opcode == Opcodes.BIPUSH || opcode == Opcodes.SIPUSH
                || opcode == Opcodes.LDC
                || opcode == Opcodes.NEWARRAY || opcode == Opcodes.ANEWARRAY
                || opcode == Opcodes.MULTIANEWARRAY) return true;
        return opcode >= Opcodes.IADD && opcode <= Opcodes.LXOR
                || opcode >= Opcodes.I2L && opcode <= Opcodes.I2S
                || opcode == Opcodes.LCMP
                || opcode >= Opcodes.FCMPL && opcode <= Opcodes.DCMPG;
    }

    /** Records the immediate data inputs of each producer instruction. */
    private static final class ProducerDependencyInterpreter
            extends SourceInterpreter {
        final Map<AbstractInsnNode, Set<AbstractInsnNode>> inputs =
                new IdentityHashMap<>();

        ProducerDependencyInterpreter() {
            super(Opcodes.ASM9);
        }

        @Override public SourceValue copyOperation(AbstractInsnNode insn,
                                                   SourceValue value) {
            record(insn, value);
            return super.copyOperation(insn, value);
        }

        @Override public SourceValue unaryOperation(AbstractInsnNode insn,
                                                    SourceValue value) {
            record(insn, value);
            return super.unaryOperation(insn, value);
        }

        @Override public SourceValue binaryOperation(AbstractInsnNode insn,
                                                     SourceValue left,
                                                     SourceValue right) {
            record(insn, left);
            record(insn, right);
            return super.binaryOperation(insn, left, right);
        }

        @Override public SourceValue ternaryOperation(AbstractInsnNode insn,
                                                      SourceValue first,
                                                      SourceValue second,
                                                      SourceValue third) {
            record(insn, first);
            record(insn, second);
            record(insn, third);
            return super.ternaryOperation(insn, first, second, third);
        }

        @Override public SourceValue naryOperation(AbstractInsnNode insn,
                                                   List<? extends SourceValue> values) {
            for (SourceValue value : values) record(insn, value);
            return super.naryOperation(insn, values);
        }

        private void record(AbstractInsnNode consumer, SourceValue value) {
            if (value == null || value.insns == null) return;
            Set<AbstractInsnNode> producers = inputs.get(consumer);
            if (producers == null) {
                producers = identitySet();
                inputs.put(consumer, producers);
            }
            producers.addAll(value.insns);
        }
    }

    private static AbstractInsnNode firstInMethod(MethodNode method,
                                                  Set<AbstractInsnNode> nodes) {
        for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
             insn = insn.getNext()) if (nodes.contains(insn)) return insn;
        return null;
    }

    private static AbstractInsnNode lastInMethod(MethodNode method,
                                                 Set<AbstractInsnNode> nodes) {
        for (AbstractInsnNode insn = method.instructions.getLast(); insn != null;
             insn = insn.getPrevious()) if (nodes.contains(insn)) return insn;
        return null;
    }

    private static String validateSlice(MethodNode method, Frame<SourceValue>[] frames,
                                        Set<AbstractInsnNode> nodes,
                                        AbstractInsnNode start, AbstractInsnNode end) {
        int startIndex = method.instructions.indexOf(start);
        int endIndex = method.instructions.indexOf(end);
        Frame<SourceValue> startFrame = frames[startIndex];
        if (startFrame == null) return "unreachable-entry@" + startIndex;
        AbstractInsnNode next = nextCode(end);
        if (next != null) {
            Frame<SourceValue> nextFrame = frames[method.instructions.indexOf(next)];
            if (nextFrame == null) return "unreachable-exit@" + endIndex;
            for (int i = 0; i < nextFrame.getStackSize(); i++) {
                if (hasSource(nextFrame.getStack(i), nodes)) {
                    return "stack-value-escapes@" + endIndex;
                }
            }
        }
        for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
             insn = insn.getNext()) {
            if (insn instanceof JumpInsnNode) {
                if (crosses(nodes, insn, nextCode(((JumpInsnNode) insn).label), next)) {
                    return "crossing-jump";
                }
            } else if (insn instanceof TableSwitchInsnNode) {
                TableSwitchInsnNode table = (TableSwitchInsnNode) insn;
                if (crosses(nodes, insn, nextCode(table.dflt), next)) {
                    return "crossing-switch";
                }
                for (org.objectweb.asm.tree.LabelNode label : table.labels) {
                    if (crosses(nodes, insn, nextCode(label), next)) {
                        return "crossing-switch";
                    }
                }
            } else if (insn instanceof LookupSwitchInsnNode) {
                LookupSwitchInsnNode lookup = (LookupSwitchInsnNode) insn;
                if (crosses(nodes, insn, nextCode(lookup.dflt), next)) {
                    return "crossing-switch";
                }
                for (org.objectweb.asm.tree.LabelNode label : lookup.labels) {
                    if (crosses(nodes, insn, nextCode(label), next)) {
                        return "crossing-switch";
                    }
                }
            }
        }
        for (TryCatchBlockNode block : method.tryCatchBlocks) {
            int from = method.instructions.indexOf(block.start);
            int to = method.instructions.indexOf(block.end);
            int handler = method.instructions.indexOf(block.handler);
            if (rangesOverlap(startIndex, endIndex, from, to - 1)
                    || handler >= startIndex && handler <= endIndex) {
                return "exception-range";
            }
        }
        for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
             insn = insn.getNext()) {
            if (nodes.contains(insn) || insn.getOpcode() < 0) continue;
            int index = method.instructions.indexOf(insn);
            Frame<SourceValue> frame = frames[index];
            if (frame == null) continue;
            for (int i = 0; i < frame.getStackSize(); i++) {
                if (hasSource(frame.getStack(i), nodes)) return "stack-value-escapes";
            }
            int local = loadedLocal(insn);
            if (local >= 0 && local < frame.getLocals()
                    && hasSource(frame.getLocal(local), nodes)) {
                return "local-value-escapes";
            }
        }
        return null;
    }

    private static boolean rangesOverlap(int aStart, int aEnd, int bStart, int bEnd) {
        return aStart <= bEnd && bStart <= aEnd;
    }

    private static boolean hasSource(SourceValue value, Set<AbstractInsnNode> nodes) {
        if (value == null || value.insns == null) return false;
        for (AbstractInsnNode source : value.insns) if (nodes.contains(source)) return true;
        return false;
    }

    private static int loadedLocal(AbstractInsnNode insn) {
        if (insn instanceof IincInsnNode) return ((IincInsnNode) insn).var;
        if (!(insn instanceof VarInsnNode)) return -1;
        int opcode = insn.getOpcode();
        return opcode >= Opcodes.ILOAD && opcode <= Opcodes.ALOAD
                || opcode == Opcodes.RET ? ((VarInsnNode) insn).var : -1;
    }

    private static boolean crosses(Set<AbstractInsnNode> nodes,
                                   AbstractInsnNode source, AbstractInsnNode target,
                                   AbstractInsnNode allowedExit) {
        if (target == null || nodes.contains(source) == nodes.contains(target)) return false;
        return !nodes.contains(source) || target != allowedExit;
    }

    private static boolean isBarrier(Family family, AbstractInsnNode insn) {
        if (insn instanceof FieldInsnNode) {
            FieldInsnNode field = (FieldInsnNode) insn;
            return !family.fields.contains(new FieldRef(field.owner, field.name, field.desc));
        }
        if (insn instanceof MethodInsnNode) {
            MethodInsnNode call = (MethodInsnNode) insn;
            MethodRef ref = new MethodRef(call.owner, call.name, call.desc);
            return !family.methods.contains(ref) && !knownSupportCall(call);
        }
        if (insn instanceof InvokeDynamicInsnNode) return true;
        if (insn instanceof TypeInsnNode && insn.getOpcode() == Opcodes.NEW) {
            return !knownSupportType(((TypeInsnNode) insn).desc);
        }
        int opcode = insn.getOpcode();
        return opcode == Opcodes.RETURN || opcode == Opcodes.IRETURN
                || opcode == Opcodes.LRETURN || opcode == Opcodes.FRETURN
                || opcode == Opcodes.DRETURN || opcode == Opcodes.ARETURN
                || opcode == Opcodes.ATHROW || opcode == Opcodes.MONITORENTER
                || opcode == Opcodes.MONITOREXIT;
    }

    private static boolean knownSupportCall(MethodInsnNode call) {
        String owner = call.owner;
        return owner.startsWith("javax/crypto/")
                || owner.startsWith("java/security/")
                || "java/lang/String".equals(owner)
                || "java/util/HashMap".equals(owner)
                || "java/util/Map".equals(owner)
                || knownSupportType(owner) && "<init>".equals(call.name);
    }

    private static boolean knownSupportType(String owner) {
        return owner.startsWith("javax/crypto/")
                || owner.startsWith("java/security/")
                || "java/util/HashMap".equals(owner);
    }

    private static boolean touchesFamily(Family family, AbstractInsnNode insn) {
        if (insn instanceof FieldInsnNode) {
            FieldInsnNode field = (FieldInsnNode) insn;
            return family.fields.contains(new FieldRef(field.owner, field.name, field.desc));
        }
        if (insn instanceof MethodInsnNode) {
            MethodInsnNode call = (MethodInsnNode) insn;
            return family.methods.contains(new MethodRef(call.owner, call.name, call.desc));
        }
        if (insn instanceof InvokeDynamicInsnNode) {
            InvokeDynamicInsnNode indy = (InvokeDynamicInsnNode) insn;
            return family.methods.contains(new MethodRef(indy.bsm.getOwner(),
                    indy.bsm.getName(), indy.bsm.getDesc()));
        }
        return false;
    }

    private static void validateReferences(Family family, ReferenceIndex references,
                                           List<String> blockers) {
        for (MethodRef method : family.methods) {
            for (RefSite site : references.methodRefs.getOrDefault(method,
                    Collections.<RefSite>emptyList())) {
                if (allowedReference(family, site)) continue;
                family.externalReferences++;
                if (site.kind.equals("BSM")) family.liveBootstrapReferences++;
                blockers.add(tsv(family.owner.name,
                        family.kind.name().toLowerCase(Locale.ROOT), family.root.name,
                        method.name + method.desc, site.describe(), "external-method-reference"));
            }
        }
        for (FieldRef field : family.fields) {
            for (RefSite site : references.fieldRefs.getOrDefault(field,
                    Collections.<RefSite>emptyList())) {
                if (allowedReference(family, site)) continue;
                family.externalReferences++;
                blockers.add(tsv(family.owner.name,
                        family.kind.name().toLowerCase(Locale.ROOT), family.root.name,
                        field.name + field.desc, site.describe(), "external-field-reference"));
            }
        }
        if (family.externalReferences != 0) {
            family.reason = family.liveBootstrapReferences != 0
                    ? "live-bootstrap-references=" + family.liveBootstrapReferences
                    : "external-references=" + family.externalReferences;
        }
    }

    private static boolean allowedReference(Family family, RefSite site) {
        if (family.methods.contains(site.source)) return true;
        return family.owner.name.equals(site.source.owner)
                && "<clinit>".equals(site.source.name)
                && family.clinitNodes.contains(site.instruction);
    }

    private static void rejectOverlaps(List<Family> families, List<String> blockers) {
        for (int i = 0; i < families.size(); i++) {
            Family left = families.get(i);
            if (left.reason != null) continue;
            for (int j = i + 1; j < families.size(); j++) {
                Family right = families.get(j);
                if (right.reason != null || left.owner != right.owner) continue;
                if (!disjoint(left.methods, right.methods)
                        || !disjoint(left.fields, right.fields)
                        || !disjointIdentity(left.clinitNodes, right.clinitNodes)) {
                    left.reason = "overlapping-support-families";
                    right.reason = "overlapping-support-families";
                    blockers.add(tsv(left.owner.name, left.kind.name(), left.root.name,
                            right.root.name, "<family>", "overlap"));
                }
            }
        }
    }

    private static <T> boolean disjoint(Set<T> left, Set<T> right) {
        for (T value : left) if (right.contains(value)) return false;
        return true;
    }

    private static boolean disjointIdentity(Set<AbstractInsnNode> left,
                                            Set<AbstractInsnNode> right) {
        for (AbstractInsnNode value : left) if (right.contains(value)) return false;
        return true;
    }

    private static void applyFamilies(ClassNode owner, List<Family> families,
                                      Summary summary, List<String> members,
                                      List<String> rewrite) {
        MethodNode clinit = findMethod(owner, "<clinit>", "()V");
        Set<AbstractInsnNode> remove = identitySet();
        Set<MethodRef> methods = new LinkedHashSet<>();
        Set<FieldRef> fields = new LinkedHashSet<>();
        for (Family family : families) {
            if (!family.rootOnly) remove.addAll(family.clinitNodes);
            Set<MethodRef> removedMethods = family.methods;
            methods.addAll(removedMethods);
            if (!family.rootOnly) fields.addAll(family.fields);
            for (MethodRef method : removedMethods) {
                members.add(tsv(owner.name, family.kind.name().toLowerCase(Locale.ROOT),
                        "method", method.name, method.desc, "remove"));
            }
            if (!family.rootOnly) {
                for (FieldRef field : family.fields) {
                    members.add(tsv(owner.name, family.kind.name().toLowerCase(Locale.ROOT),
                            "field", field.name, field.desc, "remove"));
                }
            }
        }
        if (!remove.isEmpty()) {
            for (AbstractInsnNode insn = clinit.instructions.getFirst(); insn != null; ) {
                AbstractInsnNode next = insn.getNext();
                if (remove.contains(insn)) clinit.instructions.remove(insn);
                insn = next;
            }
            for (AbstractInsnNode insn = clinit.instructions.getFirst(); insn != null; ) {
                AbstractInsnNode next = insn.getNext();
                if (insn instanceof FrameNode) clinit.instructions.remove(insn);
                insn = next;
            }
        }
        for (int i = owner.methods.size() - 1; i >= 0; i--) {
            MethodNode method = owner.methods.get(i);
            if (methods.contains(new MethodRef(owner.name, method.name, method.desc))) {
                owner.methods.remove(i);
                summary.methodsRemoved++;
            }
        }
        for (int i = owner.fields.size() - 1; i >= 0; i--) {
            FieldNode field = owner.fields.get(i);
            if (fields.contains(new FieldRef(owner.name, field.name, field.desc))) {
                owner.fields.remove(i);
                summary.fieldsRemoved++;
            }
        }
        summary.clinitInstructionsRemoved += remove.size();
        rewrite.add(tsv(owner.name, "<class>", "<clinit>()V", -1, -1,
                "apply-support-cleanup", "methods=" + methods.size()
                        + ",fields=" + fields.size() + ",instructions=" + remove.size()));
    }

    private static void verifyRemoved(byte[] bytes, List<Family> families) {
        ClassNode owner = readClass(bytes);
        Map<MethodRef, MethodNode> remainingMethods = methods(owner);
        Map<String, FieldNode> remainingFields = fields(owner);
        for (Family family : families) {
            Set<MethodRef> removedMethods = family.methods;
            for (MethodRef method : removedMethods) {
                if (remainingMethods.containsKey(method)) {
                    throw new IllegalStateException("method-remains:" + method);
                }
            }
            if (!family.rootOnly) {
                for (FieldRef field : family.fields) {
                    if (remainingFields.containsKey(field.name + field.desc)) {
                        throw new IllegalStateException("field-remains:" + field);
                    }
                }
            }
        }
    }

    private static void countBlocked(Summary summary, Family family) {
        if (family.liveBootstrapReferences != 0) {
            summary.liveBootstrapBlockedFamilies++;
            summary.liveBootstrapReferences += family.liveBootstrapReferences;
        } else if (family.reason != null && family.reason.startsWith("clinit")) {
            summary.clinitBoundaryBlockedFamilies++;
        } else {
            summary.referenceBlockedFamilies++;
        }
    }

    private static void writeReports(Path input, Path reportDirectory,
                                     Path output, Summary summary,
                                     List<Family> families, List<String> blockers,
                                     List<String> rewrite, List<String> members)
            throws IOException {
        List<String> familyRows = new ArrayList<>();
        familyRows.add("class\tkind\tbootstrap\tmethods\tfields\tclinit_ranges"
                + "\tclinit_instructions\tlive_bsm_refs\texternal_refs\tstatus\treason");
        for (Family family : families) {
            int instructions = 0;
            StringBuilder ranges = new StringBuilder();
            for (Range range : family.ranges) {
                if (ranges.length() != 0) ranges.append(',');
                ranges.append(range.start).append("..").append(range.end);
                instructions += range.instructions;
            }
            familyRows.add(tsv(family.owner.name,
                    family.kind.name().toLowerCase(Locale.ROOT),
                    family.root.name + family.root.desc, family.methods.size(),
                    family.fields.size(), ranges, instructions,
                    family.liveBootstrapReferences, family.externalReferences,
                    family.status, family.reason != null ? family.reason
                            : family.rootOnly ? "retained-support:" + family.retainedReason
                            : ""));
        }
        Files.write(reportDirectory.resolve("families.tsv"), familyRows,
                StandardCharsets.UTF_8);
        Files.write(reportDirectory.resolve("blockers.tsv"), blockers,
                StandardCharsets.UTF_8);
        Files.write(reportDirectory.resolve("rewrite.tsv"), rewrite,
                StandardCharsets.UTF_8);
        Files.write(reportDirectory.resolve("removed-members.tsv"), members,
                StandardCharsets.UTF_8);
        List<String> audit = new ArrayList<>();
        audit.add("input=" + input.toAbsolutePath());
        audit.add("parsed_classes=" + summary.parsedClasses);
        audit.add("candidate_families=" + summary.candidateFamilies);
        audit.add("member_candidates=" + summary.memberCandidates);
        audit.add("string_candidates=" + summary.stringCandidates);
        audit.add("integer_candidates=" + summary.integerCandidates);
        audit.add("eligible_families=" + summary.eligibleFamilies);
        audit.add("verified_families=" + summary.verifiedFamilies);
        audit.add("skipped_families=" + summary.skippedFamilies);
        audit.add("live_bootstrap_blocked_families="
                + summary.liveBootstrapBlockedFamilies);
        audit.add("live_bootstrap_references=" + summary.liveBootstrapReferences);
        audit.add("clinit_boundary_blocked_families="
                + summary.clinitBoundaryBlockedFamilies);
        audit.add("reference_blocked_families=" + summary.referenceBlockedFamilies);
        audit.add("changed_classes=" + summary.changedClasses);
        audit.add("methods_removed=" + summary.methodsRemoved);
        audit.add("fields_removed=" + summary.fieldsRemoved);
        audit.add("clinit_instructions_removed=" + summary.clinitInstructionsRemoved);
        audit.add("class_rollbacks=" + summary.classRollbacks);
        audit.add("rewritten_output=" + (output == null ? "" : output.toAbsolutePath()));
        audit.add("output_committed=" + summary.outputCommitted);
        audit.add("output_classes=" + summary.outputClasses);
        audit.add("output_verification_errors=" + summary.outputVerificationErrors);
        audit.add("input_classes_loaded=false");
        audit.add("gate=" + (summary.classRollbacks == 0
                && summary.outputVerificationErrors == 0 ? "PASS" : "FAIL"));
        Files.write(reportDirectory.resolve("audit.txt"), audit, StandardCharsets.UTF_8);
    }

    static final class Summary {
        int parsedClasses;
        int candidateFamilies;
        int memberCandidates;
        int stringCandidates;
        int integerCandidates;
        int eligibleFamilies;
        int verifiedFamilies;
        int skippedFamilies;
        int liveBootstrapBlockedFamilies;
        int liveBootstrapReferences;
        int clinitBoundaryBlockedFamilies;
        int referenceBlockedFamilies;
        int changedClasses;
        int methodsRemoved;
        int fieldsRemoved;
        int clinitInstructionsRemoved;
        int classRollbacks;
        int signaturesRemoved;
        int outputEntries;
        int outputClasses;
        int outputVerificationErrors;
        boolean outputCommitted;
    }

    private enum Kind { MEMBER, STRING, INTEGER }

    private static final class Family {
        final ClassNode owner;
        final Kind kind;
        final MethodRef root;
        final Set<MethodRef> methods;
        final Set<FieldRef> fields = new LinkedHashSet<>();
        final Set<AbstractInsnNode> clinitNodes = identitySet();
        final List<Range> ranges = new ArrayList<>();
        int externalReferences;
        int liveBootstrapReferences;
        boolean rootOnly;
        String retainedReason;
        String status = "CANDIDATE";
        String reason;

        Family(ClassNode owner, Kind kind, MethodRef root, Set<MethodRef> methods) {
            this.owner = owner;
            this.kind = kind;
            this.root = root;
            this.methods = new LinkedHashSet<>(methods);
        }
    }

    private static final class Range {
        final int start;
        final int end;
        final int instructions;

        Range(int start, int end, int instructions) {
            this.start = start;
            this.end = end;
            this.instructions = instructions;
        }
    }

    private static final class ReferenceIndex {
        final Map<MethodRef, List<RefSite>> methodRefs = new HashMap<>();
        final Map<FieldRef, List<RefSite>> fieldRefs = new HashMap<>();

        static ReferenceIndex build(Map<String, ClassNode> classes) {
            ReferenceIndex result = new ReferenceIndex();
            for (ClassNode owner : classes.values()) {
                for (MethodNode method : owner.methods) {
                    MethodRef source = new MethodRef(owner.name, method.name, method.desc);
                    int index = 0;
                    for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
                         insn = insn.getNext(), index++) {
                        if (insn instanceof MethodInsnNode) {
                            MethodInsnNode call = (MethodInsnNode) insn;
                            result.addMethod(new MethodRef(call.owner, call.name, call.desc),
                                    new RefSite(source, insn, index, "CALL"));
                        } else if (insn instanceof FieldInsnNode) {
                            FieldInsnNode field = (FieldInsnNode) insn;
                            result.addField(new FieldRef(field.owner, field.name, field.desc),
                                    new RefSite(source, insn, index, "FIELD"));
                        } else if (insn instanceof InvokeDynamicInsnNode) {
                            InvokeDynamicInsnNode indy = (InvokeDynamicInsnNode) insn;
                            result.addHandle(indy.bsm, source, insn, index, "BSM");
                            if (indy.bsmArgs != null) {
                                for (Object argument : indy.bsmArgs) {
                                    result.addConstant(argument, source, insn, index, "BSM_ARG");
                                }
                            }
                        } else if (insn instanceof org.objectweb.asm.tree.LdcInsnNode) {
                            result.addConstant(((org.objectweb.asm.tree.LdcInsnNode) insn).cst,
                                    source, insn, index, "LDC_HANDLE");
                        }
                    }
                }
            }
            return result;
        }

        void addConstant(Object value, MethodRef source, AbstractInsnNode insn,
                         int index, String kind) {
            if (value instanceof Handle) {
                addHandle((Handle) value, source, insn, index, kind);
            } else if (value instanceof ConstantDynamic) {
                ConstantDynamic dynamic = (ConstantDynamic) value;
                addHandle(dynamic.getBootstrapMethod(), source, insn, index, kind);
                for (int i = 0; i < dynamic.getBootstrapMethodArgumentCount(); i++) {
                    addConstant(dynamic.getBootstrapMethodArgument(i), source,
                            insn, index, kind);
                }
            }
        }

        void addHandle(Handle handle, MethodRef source, AbstractInsnNode insn,
                       int index, String kind) {
            if (handle == null) return;
            RefSite site = new RefSite(source, insn, index, kind);
            int tag = handle.getTag();
            if (tag >= Opcodes.H_GETFIELD && tag <= Opcodes.H_PUTSTATIC) {
                addField(new FieldRef(handle.getOwner(), handle.getName(),
                        handle.getDesc()), site);
            } else if (tag >= Opcodes.H_INVOKEVIRTUAL) {
                addMethod(new MethodRef(handle.getOwner(), handle.getName(),
                        handle.getDesc()), site);
            }
        }

        void addMethod(MethodRef target, RefSite site) {
            methodRefs.computeIfAbsent(target,
                    ignored -> new ArrayList<RefSite>()).add(site);
        }

        void addField(FieldRef target, RefSite site) {
            fieldRefs.computeIfAbsent(target,
                    ignored -> new ArrayList<RefSite>()).add(site);
        }
    }

    private static final class RefSite {
        final MethodRef source;
        final AbstractInsnNode instruction;
        final int index;
        final String kind;

        RefSite(MethodRef source, AbstractInsnNode instruction, int index, String kind) {
            this.source = source;
            this.instruction = instruction;
            this.index = index;
            this.kind = kind;
        }

        String describe() {
            return kind + " " + source.owner + "." + source.name + source.desc
                    + "@" + index;
        }
    }

    private static final class MethodRef {
        final String owner;
        final String name;
        final String desc;

        MethodRef(String owner, String name, String desc) {
            this.owner = owner; this.name = name; this.desc = desc;
        }

        @Override public boolean equals(Object other) {
            if (!(other instanceof MethodRef)) return false;
            MethodRef ref = (MethodRef) other;
            return owner.equals(ref.owner) && name.equals(ref.name) && desc.equals(ref.desc);
        }

        @Override public int hashCode() {
            return 31 * (31 * owner.hashCode() + name.hashCode()) + desc.hashCode();
        }

        @Override public String toString() { return owner + "." + name + desc; }
    }

    private static final class FieldRef {
        final String owner;
        final String name;
        final String desc;

        FieldRef(String owner, String name, String desc) {
            this.owner = owner; this.name = name; this.desc = desc;
        }

        @Override public boolean equals(Object other) {
            if (!(other instanceof FieldRef)) return false;
            FieldRef ref = (FieldRef) other;
            return owner.equals(ref.owner) && name.equals(ref.name) && desc.equals(ref.desc);
        }

        @Override public int hashCode() {
            return 31 * (31 * owner.hashCode() + name.hashCode()) + desc.hashCode();
        }

        @Override public String toString() { return owner + "." + name + desc; }
    }

    private static Map<MethodRef, MethodNode> methods(ClassNode owner) {
        Map<MethodRef, MethodNode> result = new LinkedHashMap<>();
        for (MethodNode method : owner.methods) {
            result.put(new MethodRef(owner.name, method.name, method.desc), method);
        }
        return result;
    }

    private static Map<String, FieldNode> fields(ClassNode owner) {
        Map<String, FieldNode> result = new LinkedHashMap<>();
        for (FieldNode field : owner.fields) result.put(field.name + field.desc, field);
        return result;
    }

    private static MethodNode findMethod(ClassNode owner, String name, String desc) {
        for (MethodNode method : owner.methods) {
            if (name.equals(method.name) && desc.equals(method.desc)) return method;
        }
        return null;
    }

    private static boolean isPrivateStatic(int access) {
        return (access & (Opcodes.ACC_PRIVATE | Opcodes.ACC_STATIC))
                == (Opcodes.ACC_PRIVATE | Opcodes.ACC_STATIC);
    }

    private static AbstractInsnNode nextCode(AbstractInsnNode insn) {
        AbstractInsnNode cursor = insn == null ? null : insn.getNext();
        while (cursor != null && cursor.getOpcode() < 0) cursor = cursor.getNext();
        return cursor;
    }

    private static <T> Set<T> identitySet() {
        return Collections.newSetFromMap(new IdentityHashMap<T, Boolean>());
    }

    private static List<EntryBytes> readEntries(Path input) throws IOException {
        List<EntryBytes> result = new ArrayList<>();
        try (ZipInputStream in = new ZipInputStream(Files.newInputStream(input))) {
            ZipEntry entry;
            while ((entry = in.getNextEntry()) != null) {
                result.add(new EntryBytes(entry, readAll(in)));
            }
        }
        return result;
    }

    private static Map<String, byte[]> classBytes(List<EntryBytes> entries) {
        Map<String, byte[]> result = new LinkedHashMap<>();
        for (EntryBytes entry : entries) {
            if (!entry.name.endsWith(".class")) continue;
            ClassReader reader = new ClassReader(entry.bytes);
            result.put(reader.getClassName(), entry.bytes);
        }
        return result;
    }

    private static Map<String, ClassNode> readClasses(Map<String, byte[]> bytes) {
        Map<String, ClassNode> result = new LinkedHashMap<>();
        for (Map.Entry<String, byte[]> entry : bytes.entrySet()) {
            result.put(entry.getKey(), readClass(entry.getValue()));
        }
        return result;
    }

    private static ClassNode readClass(byte[] bytes) {
        ClassNode owner = new ClassNode(Opcodes.ASM9);
        new ClassReader(bytes).accept(owner, 0);
        return owner;
    }

    private static byte[] writeClass(ClassNode owner, ArchiveHierarchy hierarchy) {
        ClassWriter writer = new ArchiveClassWriter(ClassWriter.COMPUTE_FRAMES, hierarchy);
        owner.accept(writer);
        return writer.toByteArray();
    }

    private static void verifyClass(byte[] bytes) throws Exception {
        ClassNode owner = readClass(bytes);
        for (MethodNode method : owner.methods) {
            if (method.instructions != null && method.instructions.size() != 0) {
                new Analyzer<>(new BasicVerifier()).analyze(owner.name, method);
            }
        }
    }

    private static void writeVerifiedArchive(List<EntryBytes> entries,
                                             Map<String, byte[]> replacements,
                                             Path output, Summary summary)
            throws IOException {
        Path parent = output.toAbsolutePath().getParent();
        if (parent == null) parent = Paths.get(".").toAbsolutePath();
        Files.createDirectories(parent);
        Path temporary = Files.createTempFile(parent,
                output.getFileName().toString() + ".", ".tmp");
        try {
            writeArchive(entries, replacements, temporary, summary);
            verifyArchive(temporary, summary);
            if (summary.outputVerificationErrors != 0) return;
            try {
                Files.move(temporary, output, StandardCopyOption.ATOMIC_MOVE,
                        StandardCopyOption.REPLACE_EXISTING);
            } catch (AtomicMoveNotSupportedException unsupported) {
                Files.move(temporary, output, StandardCopyOption.REPLACE_EXISTING);
            }
            summary.outputCommitted = true;
        } finally {
            Files.deleteIfExists(temporary);
        }
    }

    private static void writeArchive(List<EntryBytes> entries,
                                     Map<String, byte[]> replacements,
                                     Path output, Summary summary) throws IOException {
        try (ZipOutputStream out = new ZipOutputStream(Files.newOutputStream(output))) {
            for (EntryBytes entry : entries) {
                if (isSignatureEntry(entry.name) && !replacements.isEmpty()) {
                    summary.signaturesRemoved++;
                    continue;
                }
                byte[] bytes = entry.bytes;
                if (entry.name.endsWith(".class")) {
                    ClassReader reader = new ClassReader(bytes);
                    byte[] replacement = replacements.get(reader.getClassName());
                    if (replacement != null) bytes = replacement;
                }
                ZipEntry written = new ZipEntry(entry.name);
                if (entry.time >= 0) written.setTime(entry.time);
                if (entry.method == ZipEntry.STORED) {
                    CRC32 crc = new CRC32(); crc.update(bytes);
                    written.setMethod(ZipEntry.STORED);
                    written.setSize(bytes.length);
                    written.setCompressedSize(bytes.length);
                    written.setCrc(crc.getValue());
                }
                out.putNextEntry(written);
                out.write(bytes);
                out.closeEntry();
                summary.outputEntries++;
            }
        }
    }

    private static void verifyArchive(Path input, Summary summary) throws IOException {
        try (ZipInputStream in = new ZipInputStream(Files.newInputStream(input))) {
            ZipEntry entry;
            while ((entry = in.getNextEntry()) != null) {
                byte[] bytes = readAll(in);
                if (!entry.getName().endsWith(".class")) continue;
                summary.outputClasses++;
                try {
                    verifyClass(bytes);
                } catch (Throwable failure) {
                    summary.outputVerificationErrors++;
                }
            }
        }
    }

    private static boolean isSignatureEntry(String name) {
        String upper = name.toUpperCase(Locale.ROOT);
        return upper.startsWith("META-INF/")
                && (upper.endsWith(".SF") || upper.endsWith(".RSA")
                || upper.endsWith(".DSA") || upper.endsWith(".EC"));
    }

    private static byte[] readAll(InputStream input) throws IOException {
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        byte[] buffer = new byte[8192];
        int count;
        while ((count = input.read(buffer)) != -1) out.write(buffer, 0, count);
        return out.toByteArray();
    }

    private static String shortReason(Throwable failure) {
        String message = failure.getMessage();
        if (message == null || message.isEmpty()) message = failure.getClass().getSimpleName();
        return message.length() <= 180 ? message : message.substring(0, 180);
    }

    private static String tsv(Object... cells) {
        StringBuilder result = new StringBuilder();
        for (int i = 0; i < cells.length; i++) {
            if (i != 0) result.append('\t');
            if (cells[i] != null) result.append(String.valueOf(cells[i])
                    .replace("\t", "\\t").replace("\r", "\\r").replace("\n", "\\n"));
        }
        return result.toString();
    }

    private static final class EntryBytes {
        final String name;
        final byte[] bytes;
        final long time;
        final int method;

        EntryBytes(ZipEntry entry, byte[] bytes) {
            this.name = entry.getName();
            this.bytes = bytes;
            this.time = entry.getTime();
            this.method = entry.getMethod();
        }
    }

    private static final class ArchiveHierarchy {
        final Map<String, HierarchyType> types = new HashMap<>();

        ArchiveHierarchy(Map<String, ClassNode> classes) {
            for (ClassNode owner : classes.values()) {
                types.put(owner.name, new HierarchyType(owner.superName,
                        owner.interfaces == null ? Collections.<String>emptyList()
                                : new ArrayList<>(owner.interfaces),
                        (owner.access & Opcodes.ACC_INTERFACE) != 0));
            }
            types.put("java/lang/Object", new HierarchyType(null,
                    Collections.<String>emptyList(), false));
        }

        String commonSuperClass(String left, String right) {
            if (left.equals(right)) return left;
            if (isAssignableFrom(left, right)) return left;
            if (isAssignableFrom(right, left)) return right;
            HierarchyType leftType = types.get(left), rightType = types.get(right);
            if (leftType == null || rightType == null || leftType.isInterface
                    || rightType.isInterface) return "java/lang/Object";
            Set<String> supers = new LinkedHashSet<>();
            for (String current = left; current != null; current = superName(current)) {
                supers.add(current);
            }
            for (String current = right; current != null; current = superName(current)) {
                if (supers.contains(current)) return current;
            }
            return "java/lang/Object";
        }

        private boolean isAssignableFrom(String target, String source) {
            if (target.equals(source) || "java/lang/Object".equals(target)) return true;
            ArrayDeque<String> queue = new ArrayDeque<>();
            Set<String> seen = new HashSet<>();
            queue.add(source);
            while (!queue.isEmpty()) {
                String current = queue.removeFirst();
                if (!seen.add(current)) continue;
                if (target.equals(current)) return true;
                HierarchyType type = types.get(current);
                if (type == null) continue;
                if (type.superName != null) queue.addLast(type.superName);
                queue.addAll(type.interfaces);
            }
            return false;
        }

        private String superName(String name) {
            HierarchyType type = types.get(name);
            return type == null ? null : type.superName;
        }
    }

    private static final class HierarchyType {
        final String superName;
        final List<String> interfaces;
        final boolean isInterface;

        HierarchyType(String superName, List<String> interfaces, boolean isInterface) {
            this.superName = superName;
            this.interfaces = interfaces;
            this.isInterface = isInterface;
        }
    }

    private static final class ArchiveClassWriter extends ClassWriter {
        private final ArchiveHierarchy hierarchy;

        ArchiveClassWriter(int flags, ArchiveHierarchy hierarchy) {
            super(flags);
            this.hierarchy = hierarchy;
        }

        @Override protected String getCommonSuperClass(String left, String right) {
            return hierarchy.commonSuperClass(left, right);
        }
    }
}
