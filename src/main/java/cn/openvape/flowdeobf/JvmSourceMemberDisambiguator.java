package cn.openvape.flowdeobf;

import org.objectweb.asm.ClassReader;
import org.objectweb.asm.ClassWriter;
import org.objectweb.asm.ConstantDynamic;
import org.objectweb.asm.Handle;
import org.objectweb.asm.Opcodes;
import org.objectweb.asm.Type;
import org.objectweb.asm.tree.AbstractInsnNode;
import org.objectweb.asm.tree.AnnotationNode;
import org.objectweb.asm.tree.ClassNode;
import org.objectweb.asm.tree.FieldInsnNode;
import org.objectweb.asm.tree.FieldNode;
import org.objectweb.asm.tree.InvokeDynamicInsnNode;
import org.objectweb.asm.tree.LdcInsnNode;
import org.objectweb.asm.tree.MethodInsnNode;
import org.objectweb.asm.tree.MethodNode;
import org.objectweb.asm.tree.TypeAnnotationNode;
import org.objectweb.asm.tree.analysis.Analyzer;
import org.objectweb.asm.tree.analysis.BasicValue;
import org.objectweb.asm.tree.analysis.BasicVerifier;
import org.objectweb.asm.util.CheckClassAdapter;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.nio.charset.StandardCharsets;
import java.nio.file.AtomicMoveNotSupportedException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.StandardCopyOption;
import java.util.zip.ZipEntry;
import java.util.zip.ZipFile;
import java.util.zip.ZipOutputStream;
import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.util.Enumeration;

/**
 * Makes JVM members expressible in Java source without asking CFR to guess
 * across class hierarchies.  JVM method identity includes the return type,
 * while a Java source signature does not.  This pass only rewrites a member
 * when the distinction is proven across the complete known hierarchy.
 * Ambiguous full JVM descriptors fail the archive transaction.
 *
 * <p>The pass is deliberately archive-wide.  A class-local rename is unsafe
 * because method handles, invokedynamic bootstrap arguments, and calls whose
 * owner is a superclass may refer to the declaration from another class.</p>
 */
public final class JvmSourceMemberDisambiguator {
    public static final String ACTION_METHOD = "rename-duplicate-method";
    public static final String ACTION_FIELD = "rename-duplicate-field";
    public static final String ACTION_ALIAS = "remove-duplicate-alias";
    public static final String ACTION_ACCESS = "widen-override-access";
    public static final String ACTION_SKIP = "duplicate-member-skip";

    private JvmSourceMemberDisambiguator() {
    }

    /** Standalone whole-archive entry point used by the fixed-point pipeline. */
    public static void main(String[] args) throws Exception {
        if (args.length != 3) {
            System.err.println("usage: JvmSourceMemberDisambiguator <input.jar>"
                    + " <output.jar> <report.tsv>");
            System.exit(2);
        }
        Path input = Paths.get(args[0]).toAbsolutePath().normalize();
        Path output = Paths.get(args[1]).toAbsolutePath().normalize();
        Path report = Paths.get(args[2]).toAbsolutePath().normalize();
        if (input.equals(output) || Files.exists(output) && Files.isSameFile(input, output)) {
            throw new IllegalArgumentException("output must differ from input");
        }
        LinkedHashMap<String, byte[]> entries = new LinkedHashMap<>();
        LinkedHashMap<String, Long> times = new LinkedHashMap<>();
        try (ZipFile zip = new ZipFile(input.toFile())) {
            Enumeration<? extends ZipEntry> enumeration = zip.entries();
            while (enumeration.hasMoreElements()) {
                ZipEntry entry = enumeration.nextElement();
                if (entries.containsKey(entry.getName())) {
                    throw new IOException("duplicate ZIP entry: " + entry.getName());
                }
                try (InputStream stream = zip.getInputStream(entry)) {
                    entries.put(entry.getName(), readAll(stream));
                }
                times.put(entry.getName(), entry.getTime());
            }
        }
        ArchiveResult result = rewrite(entries);
        Path reportParent = report.getParent();
        if (reportParent != null) Files.createDirectories(reportParent);
        List<String> reportLines = new ArrayList<>();
        reportLines.add("kind\towner\tsignature\tnew_name\taction\treason");
        for (Change change : result.changes) {
            reportLines.add("change\t" + change.owner + "\t"
                    + change.oldName + change.descriptor + "\t" + change.newName
                    + "\t" + change.action + "\t" + change.reason);
        }
        for (Skip skip : result.skips) {
            reportLines.add("skip\t" + skip.owner + "\t" + skip.signature
                    + "\t\t" + ACTION_SKIP + "\t" + skip.reason);
        }
        reportLines.add("summary\t\t\t\tchanged=" + result.changes.size()
                + ",skipped=" + result.skips.size() + ",committed=" + result.committed);
        Files.write(report, reportLines, StandardCharsets.UTF_8);
        if (!result.committed) {
            System.err.println("duplicate-member rewrite rolled back: " + result.reason);
            System.exit(1);
        }
        Path parent = output.getParent();
        if (parent == null) throw new IOException("output has no parent");
        Files.createDirectories(parent);
        Path temporary = Files.createTempFile(parent, "." + output.getFileName(), ".tmp");
        boolean moved = false;
        try {
            try (ZipOutputStream stream = new ZipOutputStream(Files.newOutputStream(temporary))) {
                for (Map.Entry<String, byte[]> entry : result.bytes.entrySet()) {
                    ZipEntry target = new ZipEntry(entry.getKey());
                    Long time = times.get(entry.getKey());
                    if (time != null && time >= 0) target.setTime(time);
                    stream.putNextEntry(target);
                    stream.write(entry.getValue());
                    stream.closeEntry();
                }
            }
            try {
                Files.move(temporary, output, StandardCopyOption.ATOMIC_MOVE,
                        StandardCopyOption.REPLACE_EXISTING);
            } catch (AtomicMoveNotSupportedException unsupported) {
                throw new IOException("atomic publication unsupported", unsupported);
            }
            moved = true;
        } finally {
            if (!moved) Files.deleteIfExists(temporary);
        }
        System.out.println("changed=" + result.changes.size()
                + " skipped=" + result.skips.size() + " output=" + output);
        if (!result.skips.isEmpty()) System.exit(1);
    }

    /** Parses a class archive map and returns an atomic candidate map. */
    public static ArchiveResult rewrite(Map<String, byte[]> input) {
        Objects.requireNonNull(input, "input");
        LinkedHashMap<String, ClassNode> classes = new LinkedHashMap<>();
        for (Map.Entry<String, byte[]> entry : input.entrySet()) {
            if (!entry.getKey().endsWith(".class")) continue;
            try {
                ClassNode node = new ClassNode(Opcodes.ASM9);
                new ClassReader(entry.getValue()).accept(node, 0);
                String expectedPath = node.name + ".class";
                if (!entry.getKey().equals(expectedPath)) {
                    return ArchiveResult.failed(input, "class-path-mismatch "
                            + entry.getKey() + " != " + expectedPath);
                }
                if (classes.put(node.name, node) != null) {
                    return ArchiveResult.failed(input, "duplicate internal class name: "
                            + node.name);
                }
            } catch (Throwable failure) {
                return ArchiveResult.failed(input, "parse " + entry.getKey() + ": "
                        + shortReason(failure));
            }
        }
        Plan plan = plan(classes);
        if (!plan.skips.isEmpty()) {
            return ArchiveResult.failed(input, "planning-skips=" + plan.skips.size(),
                    plan.changes, plan.skips);
        }
        if (plan.changes.isEmpty()) {
            return new ArchiveResult(copyBytes(input), plan.changes, plan.skips,
                    true, "no-collisions");
        }
        Map<String, byte[]> output = copyBytes(input);
        try {
            for (ClassNode node : classes.values()) apply(node, plan);
            verifyAppliedPlan(classes, plan);
            verifySourceMemberCollisions(classes);
            for (Map.Entry<String, ClassNode> entry : classes.entrySet()) {
                String path = entry.getKey() + ".class";
                if (!input.containsKey(path)) continue;
                ClassNode node = entry.getValue();
                ClassWriter writer = new ClassWriter(0);
                node.accept(writer);
                byte[] bytes = writer.toByteArray();
                verifyClassBytes(bytes);
                output.put(path, bytes);
            }
            return new ArchiveResult(output, plan.changes, plan.skips,
                    true, "committed");
        } catch (Throwable failure) {
            return ArchiveResult.failed(input, "rewrite: " + shortReason(failure),
                    plan.changes, plan.skips);
        }
    }

    private static void verifyAppliedPlan(Map<String, ClassNode> classes, Plan plan) {
        for (Map.Entry<MethodId, String> rename : plan.methods.entrySet()) {
            MethodId id = rename.getKey();
            ClassNode owner = classes.get(id.owner);
            if (owner == null || !hasMethod(owner, rename.getValue(), id.descriptor)) {
                throw new IllegalStateException("missing renamed declaration " + id.owner
                        + "." + id.name + id.descriptor + " -> " + rename.getValue());
            }
        }
        for (Map.Entry<FieldId, String> rename : plan.fields.entrySet()) {
            FieldId id = rename.getKey();
            ClassNode owner = classes.get(id.owner);
            if (owner == null || !hasField(owner, rename.getValue(), id.descriptor)) {
                throw new IllegalStateException("missing renamed field " + id.owner
                        + "." + id.name + ":" + id.descriptor + " -> " + rename.getValue());
            }
        }
        for (ClassNode owner : classes.values()) {
            for (MethodNode removed : plan.removals) {
                if (owner.methods.contains(removed)) {
                    throw new IllegalStateException("alias occurrence still present in "
                            + owner.name);
                }
            }
            if (owner.outerClass != null && owner.outerMethod != null
                    && owner.outerMethodDesc != null) {
                requireCurrentMethodReference(owner.outerClass, owner.outerMethod,
                        owner.outerMethodDesc, plan, owner.name + ".EnclosingMethod");
            }
            for (MethodNode method : owner.methods) {
                for (AbstractInsnNode instruction : method.instructions) {
                    verifyInstructionReference(instruction, plan,
                            owner.name + "." + method.name + method.desc);
                }
            }
            for (FieldNode field : owner.fields) {
                verifyValueReference(field.value, plan,
                        owner.name + "." + field.name + ":" + field.desc);
            }
        }
    }

    private static void verifySourceMemberCollisions(Map<String, ClassNode> classes) {
        for (ClassNode owner : classes.values()) {
            Set<String> fieldNames = new HashSet<>();
            for (FieldNode field : owner.fields) {
                if (!fieldNames.add(field.name)) {
                    throw new IllegalStateException("remaining Java field collision: "
                            + owner.name + "." + field.name);
                }
            }
            Map<String, List<MethodNode>> methods = new LinkedHashMap<>();
            Set<String> exact = new HashSet<>();
            for (MethodNode method : owner.methods) {
                if (method.name.startsWith("<")) continue;
                if (!exact.add(method.name + method.desc)) {
                    throw new IllegalStateException("remaining exact method collision: "
                            + owner.name + "." + method.name + method.desc);
                }
                if ((method.access & Opcodes.ACC_BRIDGE) != 0
                        && strictBridgeTarget(owner, method) != null) {
                    continue;
                }
                methods.computeIfAbsent(sourceSignature(method),
                        ignored -> new ArrayList<>()).add(method);
            }
            for (Map.Entry<String, List<MethodNode>> collision : methods.entrySet()) {
                if (collision.getValue().size() > 1) {
                    throw new IllegalStateException("remaining Java method collision: "
                            + owner.name + "." + collision.getKey());
                }
            }
        }
    }

    private static boolean hasMethod(ClassNode owner, String name, String descriptor) {
        for (MethodNode method : owner.methods) {
            if (name.equals(method.name) && descriptor.equals(method.desc)) return true;
        }
        return false;
    }

    private static boolean hasField(ClassNode owner, String name, String descriptor) {
        for (FieldNode field : owner.fields) {
            if (name.equals(field.name) && descriptor.equals(field.desc)) return true;
        }
        return false;
    }

    private static void verifyInstructionReference(AbstractInsnNode instruction,
                                                   Plan plan, String location) {
        if (instruction instanceof MethodInsnNode) {
            MethodInsnNode method = (MethodInsnNode) instruction;
            requireCurrentMethodReference(method.owner, method.name, method.desc,
                    plan, location);
        } else if (instruction instanceof FieldInsnNode) {
            FieldInsnNode field = (FieldInsnNode) instruction;
            requireCurrentFieldReference(field.owner, field.name, field.desc,
                    plan, location);
        } else if (instruction instanceof InvokeDynamicInsnNode) {
            InvokeDynamicInsnNode indy = (InvokeDynamicInsnNode) instruction;
            if (indy.bsm != null
                    && "java/lang/invoke/LambdaMetafactory".equals(indy.bsm.getOwner())
                    && indy.bsmArgs.length > 0 && indy.bsmArgs[0] instanceof Type) {
                Type factoryReturn = Type.getReturnType(indy.desc);
                Type sam = (Type) indy.bsmArgs[0];
                if (factoryReturn.getSort() == Type.OBJECT
                        && sam.getSort() == Type.METHOD) {
                    requireCurrentMethodReference(factoryReturn.getInternalName(),
                            indy.name, sam.getDescriptor(), plan, location + ".lambda");
                }
            }
            verifyValueReference(indy.bsm, plan, location + ".bsm");
            for (Object argument : indy.bsmArgs) {
                verifyValueReference(argument, plan, location + ".bsmArg");
            }
        } else if (instruction instanceof LdcInsnNode) {
            verifyValueReference(((LdcInsnNode) instruction).cst, plan,
                    location + ".ldc");
        }
    }

    private static void verifyValueReference(Object value, Plan plan, String location) {
        if (value instanceof Handle) {
            Handle handle = (Handle) value;
            if (handle.getTag() <= Opcodes.H_PUTSTATIC) {
                requireCurrentFieldReference(handle.getOwner(), handle.getName(),
                        handle.getDesc(), plan, location);
            } else {
                requireCurrentMethodReference(handle.getOwner(), handle.getName(),
                        handle.getDesc(), plan, location);
            }
        } else if (value instanceof ConstantDynamic) {
            ConstantDynamic dynamic = (ConstantDynamic) value;
            verifyValueReference(dynamic.getBootstrapMethod(), plan, location + ".condyBsm");
            for (int i = 0; i < dynamic.getBootstrapMethodArgumentCount(); i++) {
                verifyValueReference(dynamic.getBootstrapMethodArgument(i), plan,
                        location + ".condyArg");
            }
        } else if (value instanceof List) {
            for (Object item : (List<?>) value) {
                verifyValueReference(item, plan, location + ".list");
            }
        }
    }

    private static void requireCurrentMethodReference(String owner, String name,
                                                      String descriptor, Plan plan,
                                                      String location) {
        String expected = plan.resolveMethod(owner, name, descriptor);
        if (expected != null && !expected.equals(name)) {
            throw new IllegalStateException("stale method reference at " + location
                    + ": " + owner + "." + name + descriptor + " -> " + expected);
        }
    }

    private static void requireCurrentFieldReference(String owner, String name,
                                                     String descriptor, Plan plan,
                                                     String location) {
        String expected = plan.resolveField(owner, name, descriptor);
        if (expected != null && !expected.equals(name)) {
            throw new IllegalStateException("stale field reference at " + location
                    + ": " + owner + "." + name + ":" + descriptor + " -> " + expected);
        }
    }

    /** Builds a deterministic rename plan without mutating any class node. */
    public static Plan plan(Map<String, ClassNode> classes) {
        Objects.requireNonNull(classes, "classes");
        Map<String, TypeInfo> hierarchy = new LinkedHashMap<>();
        for (ClassNode node : classes.values()) {
            hierarchy.put(node.name, new TypeInfo(node.superName,
                    node.interfaces == null ? Collections.<String>emptyList()
                            : new ArrayList<>(node.interfaces)));
        }
        Map<MethodId, String> methods = new LinkedHashMap<>();
        Map<FieldId, String> fields = new LinkedHashMap<>();
        Set<MethodNode> removals = Collections.newSetFromMap(
                new IdentityHashMap<MethodNode, Boolean>());
        Map<MethodNode, Integer> accessUpdates = new IdentityHashMap<>();
        List<Change> changes = new ArrayList<>();
        List<Skip> skips = new ArrayList<>();

        List<ClassNode> ordered = new ArrayList<>(classes.values());
        ordered.sort(Comparator.comparing(node -> node.name));
        pruneExactAliases(ordered, removals, changes, skips);
        planMethodFamilies(ordered, hierarchy, removals, methods,
                accessUpdates, changes, skips);
        for (ClassNode node : ordered) {
            planFields(node, fields, changes, skips);
        }
        Set<MethodId> methodDeclarations = new LinkedHashSet<>();
        Set<FieldId> fieldDeclarations = new LinkedHashSet<>();
        for (ClassNode node : ordered) {
            for (MethodNode method : node.methods) {
                if (!removals.contains(method)) {
                    methodDeclarations.add(new MethodId(node.name, method.name, method.desc));
                }
            }
            for (FieldNode field : node.fields) {
                fieldDeclarations.add(new FieldId(node.name, field.name, field.desc));
            }
        }
        return new Plan(methods, fields, removals, accessUpdates, changes, skips,
                hierarchy, methodDeclarations, fieldDeclarations);
    }

    private static void pruneExactAliases(List<ClassNode> classes,
                                          Set<MethodNode> removals,
                                          List<Change> changes,
                                          List<Skip> skips) {
        for (ClassNode owner : classes) {
            Map<String, List<MethodNode>> exact = new LinkedHashMap<>();
            for (MethodNode method : owner.methods) {
                if (method.name.startsWith("<")) continue;
                exact.computeIfAbsent(method.name + method.desc,
                        ignored -> new ArrayList<>()).add(method);
            }
            for (Map.Entry<String, List<MethodNode>> entry : exact.entrySet()) {
                List<MethodNode> group = entry.getValue();
                if (group.size() <= 1) continue;
                if (group.size() == 2) {
                    MethodNode first = group.get(0);
                    MethodNode second = group.get(1);
                    boolean firstAlias = isStrictAlias(owner, first);
                    boolean secondAlias = isStrictAlias(owner, second);
                    if (firstAlias ^ secondAlias) {
                        MethodNode alias = firstAlias ? first : second;
                        removals.add(alias);
                        changes.add(new Change(owner.name, alias.name, alias.desc,
                                "<removed>", ACTION_ALIAS,
                                "strict-self-forwarding-alias"));
                        continue;
                    }
                }
                skips.add(new Skip(owner.name, entry.getKey(),
                        "duplicate-full-jvm-descriptor"));
            }
        }
    }

    private static void planMethodFamilies(List<ClassNode> classes,
                                           Map<String, TypeInfo> hierarchy,
                                           Set<MethodNode> removals,
                                           Map<MethodId, String> renames,
                                           Map<MethodNode, Integer> accessUpdates,
                                           List<Change> changes,
                                           List<Skip> skips) {
        List<MethodDecl> declarations = new ArrayList<>();
        Map<MethodId, Integer> byId = new LinkedHashMap<>();
        Map<String, List<Integer>> byOwner = new LinkedHashMap<>();
        Map<String, List<Integer>> byOwnerSource = new LinkedHashMap<>();
        Set<MethodNode> standardBridges = Collections.newSetFromMap(
                new IdentityHashMap<MethodNode, Boolean>());
        for (ClassNode owner : classes) {
            for (MethodNode method : owner.methods) {
                if (method.name.startsWith("<") || removals.contains(method)) continue;
                MethodDecl declaration = new MethodDecl(owner, method);
                int index = declarations.size();
                declarations.add(declaration);
                byId.putIfAbsent(declaration.id, index);
                byOwner.computeIfAbsent(owner.name,
                        ignored -> new ArrayList<>()).add(index);
                byOwnerSource.computeIfAbsent(owner.name + "\u0000"
                                + sourceSignature(method),
                        ignored -> new ArrayList<>()).add(index);
                if ((method.access & Opcodes.ACC_BRIDGE) != 0
                        && strictBridgeTarget(owner, method) != null) {
                    standardBridges.add(method);
                }
            }
        }
        DisjointSet sameFamily = new DisjointSet(declarations.size());
        List<IntPair> conflicts = new ArrayList<>();

        // A normal bridge and its covariant target must retain one source name
        // so javac can recreate the bridge when the CFR source is rebuilt.
        for (int i = 0; i < declarations.size(); i++) {
            MethodDecl bridge = declarations.get(i);
            if (!standardBridges.contains(bridge.method)) continue;
            MethodNode target = strictBridgeTarget(bridge.owner, bridge.method);
            if (target == null || !bridge.method.name.equals(target.name)) continue;
            Integer targetIndex = byId.get(new MethodId(bridge.owner.name,
                    target.name, target.desc));
            if (targetIndex != null) sameFamily.union(i, targetIndex);
        }

        // Join actual dispatch declarations.  Different return descriptors are
        // joined only when Java covariance proves the override relationship.
        for (int childIndex = 0; childIndex < declarations.size(); childIndex++) {
            MethodDecl child = declarations.get(childIndex);
            for (String ancestorName : allAncestors(child.owner.name, hierarchy)) {
                List<Integer> candidates = byOwnerSource.get(ancestorName + "\u0000"
                        + sourceSignature(child.method));
                if (candidates == null) continue;
                for (Integer parentIndex : candidates) {
                    MethodDecl parent = declarations.get(parentIndex);
                    if (!isInheritedBy(parent, child.owner.name)) continue;
                    boolean childBridge = standardBridges.contains(child.method);
                    boolean parentBridge = standardBridges.contains(parent.method);
                    boolean exactDescriptor = child.method.desc.equals(parent.method.desc);
                    boolean virtualPair = isVirtual(child.method) && isVirtual(parent.method);
                    boolean covariant = isCovariantReturn(child.method.desc,
                            parent.method.desc, hierarchy);
                    if (virtualPair && (parent.method.access & Opcodes.ACC_FINAL) == 0
                            && exactDescriptor) {
                        sameFamily.union(childIndex, parentIndex);
                        widenOverrideAccess(child, parent, accessUpdates, changes);
                    } else if (!childBridge && !parentBridge
                            && isJavaInheritanceConflict(child.method, parent.method,
                            exactDescriptor, covariant)) {
                        conflicts.add(new IntPair(childIndex, parentIndex));
                    }
                }
            }
        }

        // A class may inherit two unrelated interface/source families without
        // declaring either method itself.  Java still requires those visible
        // signatures to be compatible, so model that conflict explicitly.
        for (ClassNode receiver : classes) {
            Map<String, List<Integer>> visible = new LinkedHashMap<>();
            for (String ancestorName : allAncestors(receiver.name, hierarchy)) {
                for (Integer index : byOwner.getOrDefault(ancestorName,
                        Collections.<Integer>emptyList())) {
                    MethodDecl declaration = declarations.get(index);
                    if (!isInheritedBy(declaration, receiver.name)
                            || !isVirtual(declaration.method)
                            || standardBridges.contains(declaration.method)) {
                        continue;
                    }
                    visible.computeIfAbsent(sourceSignature(declaration.method),
                            ignored -> new ArrayList<>()).add(index);
                }
            }
            for (List<Integer> group : visible.values()) {
                for (int left = 0; left < group.size(); left++) {
                    for (int right = left + 1; right < group.size(); right++) {
                        int leftIndex = group.get(left);
                        int rightIndex = group.get(right);
                        if (sameFamily.find(leftIndex) == sameFamily.find(rightIndex)) {
                            continue;
                        }
                        MethodNode leftMethod = declarations.get(leftIndex).method;
                        MethodNode rightMethod = declarations.get(rightIndex).method;
                        boolean distinctOwners = !declarations.get(leftIndex).owner.name
                                .equals(declarations.get(rightIndex).owner.name);
                        boolean compatible = isCovariantReturn(leftMethod.desc,
                                rightMethod.desc, hierarchy)
                                || isCovariantReturn(rightMethod.desc,
                                leftMethod.desc, hierarchy);
                        boolean exactDescriptor = leftMethod.desc.equals(rightMethod.desc);
                        if (exactDescriptor && distinctOwners) {
                            sameFamily.union(leftIndex, rightIndex);
                        } else if (!compatible || !distinctOwners) {
                            conflicts.add(new IntPair(leftIndex, rightIndex));
                        }
                    }
                }
            }
        }

        // Local return-only collisions are the direct classfile/JLS mismatch.
        for (ClassNode owner : classes) {
            Map<String, List<Integer>> local = new LinkedHashMap<>();
            for (MethodNode method : owner.methods) {
                if (method.name.startsWith("<") || removals.contains(method)
                        || standardBridges.contains(method)) continue;
                Integer index = byId.get(new MethodId(owner.name, method.name, method.desc));
                if (index != null) {
                    local.computeIfAbsent(sourceSignature(method),
                            ignored -> new ArrayList<>()).add(index);
                }
            }
            for (List<Integer> group : local.values()) {
                for (int left = 0; left < group.size(); left++) {
                    for (int right = left + 1; right < group.size(); right++) {
                        if (sameFamily.find(group.get(left))
                                == sameFamily.find(group.get(right))) {
                            MethodDecl member = declarations.get(group.get(left));
                            skips.add(new Skip(owner.name, sourceSignature(member.method),
                                    "dispatch-family-contains-local-source-collision"));
                        } else {
                            conflicts.add(new IntPair(group.get(left), group.get(right)));
                        }
                    }
                }
            }
        }

        Map<Integer, List<Integer>> membersByFamily = new LinkedHashMap<>();
        for (int i = 0; i < declarations.size(); i++) {
            membersByFamily.computeIfAbsent(sameFamily.find(i),
                    ignored -> new ArrayList<>()).add(i);
        }
        Map<Integer, Set<Integer>> conflictGraph = new LinkedHashMap<>();
        for (IntPair pair : conflicts) {
            int left = sameFamily.find(pair.left);
            int right = sameFamily.find(pair.right);
            if (left == right) continue;
            conflictGraph.computeIfAbsent(left, ignored -> new LinkedHashSet<>()).add(right);
            conflictGraph.computeIfAbsent(right, ignored -> new LinkedHashSet<>()).add(left);
        }

        Set<String> occupied = new HashSet<>();
        for (MethodDecl declaration : declarations) {
            occupied.add(declaration.method.name
                    + argumentDescriptor(declaration.method.desc));
        }
        Set<Integer> visited = new HashSet<>();
        List<Integer> graphRoots = new ArrayList<>(conflictGraph.keySet());
        graphRoots.sort(Comparator.comparing(root -> familyKey(
                membersByFamily.get(root), declarations)));
        for (Integer start : graphRoots) {
            if (!visited.add(start)) continue;
            List<Integer> component = new ArrayList<>();
            ArrayDeque<Integer> queue = new ArrayDeque<>();
            queue.add(start);
            while (!queue.isEmpty()) {
                int family = queue.removeFirst();
                component.add(family);
                for (Integer adjacent : conflictGraph.getOrDefault(family,
                        Collections.<Integer>emptySet())) {
                    if (visited.add(adjacent)) queue.addLast(adjacent);
                }
            }
            int canonical = component.get(0);
            for (Integer candidate : component) {
                if (compareFamilies(candidate, canonical, membersByFamily,
                        declarations) > 0) canonical = candidate;
            }
            component.sort(Comparator.comparing(root -> familyKey(
                    membersByFamily.get(root), declarations)));
            for (Integer family : component) {
                if (family == canonical) continue;
                List<Integer> members = membersByFamily.get(family);
                MethodDecl representative = declarations.get(members.get(0));
                String args = argumentDescriptor(representative.method.desc);
                String signature = familyKey(members, declarations);
                String proposed = representative.method.name + "$src$"
                        + returnToken(representative.method.desc) + "$"
                        + Integer.toUnsignedString(signature.hashCode(), 36);
                String newName = proposed;
                int suffix = 2;
                while (occupied.contains(newName + args)) {
                    newName = proposed + "$" + suffix++;
                }
                occupied.add(newName + args);
                for (Integer member : members) {
                    MethodDecl declaration = declarations.get(member);
                    renames.put(declaration.id, newName);
                    changes.add(new Change(declaration.owner.name,
                            declaration.method.name, declaration.method.desc,
                            newName, ACTION_METHOD,
                            "hierarchy-source-signature-conflict"));
                }
            }
        }
    }

    private static String sourceSignature(MethodNode method) {
        return method.name + argumentDescriptor(method.desc);
    }

    private static List<String> allAncestors(String owner,
                                             Map<String, TypeInfo> hierarchy) {
        LinkedHashSet<String> result = new LinkedHashSet<>();
        ArrayDeque<String> queue = new ArrayDeque<>();
        TypeInfo initial = hierarchy.get(owner);
        if (initial == null) return new ArrayList<>();
        if (initial.superName != null) queue.add(initial.superName);
        queue.addAll(initial.interfaces);
        while (!queue.isEmpty()) {
            String current = queue.removeFirst();
            if (!result.add(current)) continue;
            TypeInfo info = hierarchy.get(current);
            if (info == null) continue;
            if (info.superName != null) queue.addLast(info.superName);
            queue.addAll(info.interfaces);
        }
        return new ArrayList<>(result);
    }

    private static boolean isInheritedBy(MethodDecl parent, String childOwner) {
        int access = parent.method.access;
        if ((access & Opcodes.ACC_PRIVATE) != 0) return false;
        if ((access & (Opcodes.ACC_PUBLIC | Opcodes.ACC_PROTECTED)) != 0) return true;
        return packageName(parent.owner.name).equals(packageName(childOwner));
    }

    private static String packageName(String owner) {
        int separator = owner.lastIndexOf('/');
        return separator < 0 ? "" : owner.substring(0, separator);
    }

    private static boolean isVirtual(MethodNode method) {
        return (method.access & (Opcodes.ACC_STATIC | Opcodes.ACC_PRIVATE)) == 0;
    }

    private static boolean isJavaInheritanceConflict(MethodNode child,
                                                     MethodNode parent,
                                                     boolean exactDescriptor,
                                                     boolean covariantReturn) {
        boolean childStatic = (child.access & Opcodes.ACC_STATIC) != 0;
        boolean parentStatic = (parent.access & Opcodes.ACC_STATIC) != 0;
        if (childStatic != parentStatic) return true;
        if ((parent.access & Opcodes.ACC_FINAL) != 0) return true;
        if ((child.access & Opcodes.ACC_PRIVATE) != 0) return true;
        if (childStatic) return !(exactDescriptor || covariantReturn);
        return !(exactDescriptor || covariantReturn);
    }

    private static boolean isCovariantReturn(String childDescriptor,
                                             String parentDescriptor,
                                             Map<String, TypeInfo> hierarchy) {
        Type child = Type.getReturnType(childDescriptor);
        Type parent = Type.getReturnType(parentDescriptor);
        if (child.equals(parent)) return true;
        if (!isReferenceType(child) || !isReferenceType(parent)) return false;
        return isAssignable(child, parent, hierarchy);
    }

    private static boolean isReferenceType(Type type) {
        return type.getSort() == Type.OBJECT || type.getSort() == Type.ARRAY;
    }

    private static boolean isAssignable(Type child, Type parent,
                                        Map<String, TypeInfo> hierarchy) {
        if (child.equals(parent)) return true;
        if (parent.getSort() == Type.OBJECT) {
            String parentName = parent.getInternalName();
            if ("java/lang/Object".equals(parentName)) return true;
            if (child.getSort() == Type.ARRAY) {
                return "java/lang/Cloneable".equals(parentName)
                        || "java/io/Serializable".equals(parentName);
            }
            if (isKnownSubtype(child.getInternalName(), parentName, hierarchy)) return true;
        }
        if (child.getSort() == Type.ARRAY && parent.getSort() == Type.ARRAY) {
            Type childElement = child.getElementType();
            Type parentElement = parent.getElementType();
            if (!isReferenceType(childElement) || !isReferenceType(parentElement)) {
                return childElement.equals(parentElement)
                        && child.getDimensions() == parent.getDimensions();
            }
            return child.getDimensions() == parent.getDimensions()
                    && isAssignable(childElement, parentElement, hierarchy);
        }
        try {
            ClassLoader loader = JvmSourceMemberDisambiguator.class.getClassLoader();
            Class<?> childClass = Class.forName(binaryName(child), false, loader);
            Class<?> parentClass = Class.forName(binaryName(parent), false, loader);
            return parentClass.isAssignableFrom(childClass);
        } catch (Throwable ignored) {
            return false;
        }
    }

    private static String binaryName(Type type) {
        if (type.getSort() == Type.ARRAY) {
            return type.getDescriptor().replace('/', '.');
        }
        return type.getClassName();
    }

    private static boolean isKnownSubtype(String child, String parent,
                                          Map<String, TypeInfo> hierarchy) {
        if (child.equals(parent)) return true;
        Set<String> seen = new HashSet<>();
        ArrayDeque<String> queue = new ArrayDeque<>();
        queue.add(child);
        while (!queue.isEmpty()) {
            String current = queue.removeFirst();
            if (!seen.add(current)) continue;
            TypeInfo info = hierarchy.get(current);
            if (info == null) continue;
            if (parent.equals(info.superName) || info.interfaces.contains(parent)) return true;
            if (info.superName != null) queue.addLast(info.superName);
            queue.addAll(info.interfaces);
        }
        return false;
    }

    private static void widenOverrideAccess(MethodDecl child, MethodDecl parent,
                                            Map<MethodNode, Integer> accessUpdates,
                                            List<Change> changes) {
        int current = accessUpdates.getOrDefault(child.method, child.method.access);
        int required = visibilityRank(parent.method.access);
        if (visibilityRank(current) >= required) return;
        int visibility = visibilityBits(parent.method.access);
        int updated = (current & ~(Opcodes.ACC_PUBLIC | Opcodes.ACC_PROTECTED
                | Opcodes.ACC_PRIVATE)) | visibility;
        accessUpdates.put(child.method, updated);
        changes.add(new Change(child.owner.name, child.method.name, child.method.desc,
                child.method.name, ACTION_ACCESS, "override-visibility"));
    }

    private static int visibilityRank(int access) {
        if ((access & Opcodes.ACC_PUBLIC) != 0) return 3;
        if ((access & Opcodes.ACC_PROTECTED) != 0) return 2;
        if ((access & Opcodes.ACC_PRIVATE) != 0) return 0;
        return 1;
    }

    private static int visibilityBits(int access) {
        if ((access & Opcodes.ACC_PUBLIC) != 0) return Opcodes.ACC_PUBLIC;
        if ((access & Opcodes.ACC_PROTECTED) != 0) return Opcodes.ACC_PROTECTED;
        if ((access & Opcodes.ACC_PRIVATE) != 0) return Opcodes.ACC_PRIVATE;
        return 0;
    }

    private static int compareFamilies(int left, int right,
                                       Map<Integer, List<Integer>> membersByFamily,
                                       List<MethodDecl> declarations) {
        long leftScore = familyScore(membersByFamily.get(left), declarations);
        long rightScore = familyScore(membersByFamily.get(right), declarations);
        int scoreComparison = Long.compare(leftScore, rightScore);
        if (scoreComparison != 0) return scoreComparison;
        String leftKey = familyKey(membersByFamily.get(left), declarations);
        String rightKey = familyKey(membersByFamily.get(right), declarations);
        return rightKey.compareTo(leftKey);
    }

    private static long familyScore(List<Integer> members,
                                    List<MethodDecl> declarations) {
        long result = members.size() * 32L;
        for (Integer index : members) {
            MethodNode method = declarations.get(index).method;
            result += score(method);
            if ((method.access & Opcodes.ACC_FINAL) != 0) result += 100_000L;
            if ((method.access & Opcodes.ACC_NATIVE) != 0) result += 1_000_000L;
            if ((method.access & Opcodes.ACC_ABSTRACT) != 0) result += 4L;
        }
        return result;
    }

    private static String familyKey(List<Integer> members,
                                    List<MethodDecl> declarations) {
        List<String> keys = new ArrayList<>();
        for (Integer index : members) {
            MethodDecl declaration = declarations.get(index);
            keys.add(declaration.owner.name + "." + declaration.method.name
                    + declaration.method.desc);
        }
        Collections.sort(keys);
        StringBuilder result = new StringBuilder();
        for (String key : keys) result.append(key).append(';');
        return result.toString();
    }

    private static void planFields(ClassNode owner,
                                   Map<FieldId, String> renames,
                                   List<Change> changes,
                                   List<Skip> skips) {
        Map<String, List<FieldNode>> groups = new LinkedHashMap<>();
        for (FieldNode field : owner.fields) {
            groups.computeIfAbsent(field.name, ignored -> new ArrayList<>()).add(field);
        }
        for (Map.Entry<String, List<FieldNode>> entry : groups.entrySet()) {
            List<FieldNode> group = entry.getValue();
            Set<String> descriptors = new LinkedHashSet<>();
            for (FieldNode field : group) descriptors.add(field.desc);
            if (descriptors.size() <= 1) continue;
            if (group.size() != descriptors.size()
                    || hasNativeField(group)) {
                skips.add(new Skip(owner.name, entry.getKey(),
                        group.size() != descriptors.size()
                                ? "duplicate-full-jvm-descriptor" : "native-member"));
                continue;
            }
            FieldNode canonical = group.get(0);
            Set<String> occupied = new HashSet<>();
            for (FieldNode field : owner.fields) occupied.add(field.name);
            for (FieldNode field : group) {
                if (field == canonical) continue;
                String proposed = entry.getKey() + "$dup$" + typeToken(field.desc);
                String name = proposed;
                int suffix = 2;
                while (occupied.contains(name)) name = proposed + "$" + suffix++;
                occupied.add(name);
                FieldId id = new FieldId(owner.name, field.name, field.desc);
                renames.put(id, name);
                changes.add(new Change(owner.name, field.name, field.desc,
                        name, ACTION_FIELD, "owner-local-type-collision"));
            }
        }
    }

    private static void apply(ClassNode node, Plan plan) {
        if (node.outerClass != null && node.outerMethod != null
                && node.outerMethodDesc != null) {
            String renamed = plan.resolveMethod(node.outerClass, node.outerMethod,
                    node.outerMethodDesc);
            if (renamed != null) node.outerMethod = renamed;
        }
        for (MethodNode method : new ArrayList<>(node.methods)) {
            if (plan.removals.contains(method)) {
                node.methods.remove(method);
                continue;
            }
            Integer updatedAccess = plan.accessUpdates.get(method);
            if (updatedAccess != null) method.access = updatedAccess;
            String renamed = plan.methods.get(new MethodId(node.name, method.name, method.desc));
            if (renamed != null) method.name = renamed;
            rewriteMethodAnnotations(method, plan);
            for (AbstractInsnNode insn : method.instructions) rewriteInstruction(insn, plan);
        }
        for (FieldNode field : node.fields) {
            String renamed = plan.fields.get(new FieldId(node.name, field.name, field.desc));
            if (renamed != null) field.name = renamed;
            field.value = rewriteValue(field.value, plan);
            rewriteAnnotations(field.visibleAnnotations, plan);
            rewriteAnnotations(field.invisibleAnnotations, plan);
            rewriteTypeAnnotations(field.visibleTypeAnnotations, plan);
            rewriteTypeAnnotations(field.invisibleTypeAnnotations, plan);
        }
        rewriteAnnotations(node.visibleAnnotations, plan);
        rewriteAnnotations(node.invisibleAnnotations, plan);
        rewriteTypeAnnotations(node.visibleTypeAnnotations, plan);
        rewriteTypeAnnotations(node.invisibleTypeAnnotations, plan);
    }

    private static void rewriteMethodAnnotations(MethodNode method, Plan plan) {
        rewriteAnnotations(method.visibleAnnotations, plan);
        rewriteAnnotations(method.invisibleAnnotations, plan);
        rewriteTypeAnnotations(method.visibleTypeAnnotations, plan);
        rewriteTypeAnnotations(method.invisibleTypeAnnotations, plan);
        method.annotationDefault = rewriteValue(method.annotationDefault, plan);
        if (method.visibleParameterAnnotations != null) {
            for (List<AnnotationNode> annotations : method.visibleParameterAnnotations) {
                rewriteAnnotations(annotations, plan);
            }
        }
        if (method.invisibleParameterAnnotations != null) {
            for (List<AnnotationNode> annotations : method.invisibleParameterAnnotations) {
                rewriteAnnotations(annotations, plan);
            }
        }
    }

    private static void rewriteInstruction(AbstractInsnNode insn, Plan plan) {
        if (insn instanceof MethodInsnNode) {
            MethodInsnNode method = (MethodInsnNode) insn;
            String name = plan.resolveMethod(method.owner, method.name, method.desc);
            if (name != null) method.name = name;
        } else if (insn instanceof FieldInsnNode) {
            FieldInsnNode field = (FieldInsnNode) insn;
            String name = plan.resolveField(field.owner, field.name, field.desc);
            if (name != null) field.name = name;
        } else if (insn instanceof InvokeDynamicInsnNode) {
            InvokeDynamicInsnNode indy = (InvokeDynamicInsnNode) insn;
            rewriteLambdaName(indy, plan);
            indy.bsm = rewriteHandle(indy.bsm, plan);
            for (int i = 0; i < indy.bsmArgs.length; i++) {
                indy.bsmArgs[i] = rewriteValue(indy.bsmArgs[i], plan);
            }
        } else if (insn instanceof LdcInsnNode) {
            LdcInsnNode ldc = (LdcInsnNode) insn;
            ldc.cst = rewriteValue(ldc.cst, plan);
        }
    }

    private static void rewriteLambdaName(InvokeDynamicInsnNode indy, Plan plan) {
        if (indy.bsm == null
                || !"java/lang/invoke/LambdaMetafactory".equals(indy.bsm.getOwner())
                || !("metafactory".equals(indy.bsm.getName())
                || "altMetafactory".equals(indy.bsm.getName()))
                || indy.bsmArgs.length == 0 || !(indy.bsmArgs[0] instanceof Type)) {
            return;
        }
        Type samType = (Type) indy.bsmArgs[0];
        if (samType.getSort() != Type.METHOD) return;
        Type factoryReturn = Type.getReturnType(indy.desc);
        if (factoryReturn.getSort() != Type.OBJECT) return;
        String renamed = plan.resolveMethod(factoryReturn.getInternalName(), indy.name,
                samType.getDescriptor());
        if (renamed != null) indy.name = renamed;
    }

    private static Object rewriteValue(Object value, Plan plan) {
        if (value instanceof Handle) return rewriteHandle((Handle) value, plan);
        if (value instanceof ConstantDynamic) {
            ConstantDynamic dynamic = (ConstantDynamic) value;
            Object[] args = new Object[dynamic.getBootstrapMethodArgumentCount()];
            for (int i = 0; i < args.length; i++) {
                args[i] = rewriteValue(dynamic.getBootstrapMethodArgument(i), plan);
            }
            return new ConstantDynamic(dynamic.getName(), dynamic.getDescriptor(),
                    rewriteHandle(dynamic.getBootstrapMethod(), plan), args);
        }
        if (value instanceof List) {
            List<?> source = (List<?>) value;
            List<Object> result = new ArrayList<>(source.size());
            for (Object item : source) result.add(rewriteValue(item, plan));
            return result;
        }
        return value;
    }

    private static Handle rewriteHandle(Handle handle, Plan plan) {
        if (handle == null) return null;
        boolean field = handle.getTag() <= Opcodes.H_PUTSTATIC;
        String name = field ? plan.resolveField(handle.getOwner(), handle.getName(),
                handle.getDesc()) : plan.resolveMethod(handle.getOwner(), handle.getName(),
                handle.getDesc());
        if (name == null || name.equals(handle.getName())) return handle;
        return new Handle(handle.getTag(), handle.getOwner(), name, handle.getDesc(),
                handle.isInterface());
    }

    private static void rewriteAnnotations(List<AnnotationNode> annotations, Plan plan) {
        if (annotations == null) return;
        for (AnnotationNode annotation : annotations) {
            if (annotation.values == null) continue;
            for (int i = 1; i < annotation.values.size(); i += 2) {
                Object key = annotation.values.get(i - 1);
                if (key instanceof String) {
                    String renamed = plan.resolveAnnotationElement(annotation.desc,
                            (String) key);
                    if (renamed != null) annotation.values.set(i - 1, renamed);
                }
                annotation.values.set(i, rewriteValue(annotation.values.get(i), plan));
            }
        }
    }

    private static void rewriteTypeAnnotations(List<TypeAnnotationNode> annotations,
                                               Plan plan) {
        if (annotations == null) return;
        for (TypeAnnotationNode annotation : annotations) {
            if (annotation.values == null) continue;
            for (int i = 1; i < annotation.values.size(); i += 2) {
                annotation.values.set(i, rewriteValue(annotation.values.get(i), plan));
            }
        }
    }

    private static String argumentDescriptor(String methodDescriptor) {
        Type method = Type.getMethodType(methodDescriptor);
        return Type.getMethodDescriptor(Type.VOID_TYPE, method.getArgumentTypes());
    }

    private static int score(MethodNode method) {
        int score = 0;
        if ((method.access & Opcodes.ACC_SYNTHETIC) == 0) score += 8;
        if ((method.access & Opcodes.ACC_BRIDGE) == 0) score += 8;
        if ((method.access & Opcodes.ACC_PRIVATE) == 0) score += 2;
        if ((method.access & (Opcodes.ACC_PUBLIC | Opcodes.ACC_PROTECTED)) != 0) score++;
        return score;
    }

    private static MethodNode strictBridgeTarget(ClassNode owner, MethodNode bridge) {
        if ((bridge.access & Opcodes.ACC_BRIDGE) == 0
                || bridge.tryCatchBlocks != null && !bridge.tryCatchBlocks.isEmpty()) {
            return null;
        }
        List<AbstractInsnNode> code = executableInstructions(bridge);
        Type bridgeType = Type.getMethodType(bridge.desc);
        boolean isStatic = (bridge.access & Opcodes.ACC_STATIC) != 0;
        int index = 0;
        int local = 0;
        if (!isStatic) {
            if (index >= code.size()) return null;
            if (!isLoad(code.get(index++), Opcodes.ALOAD, 0)) return null;
            local = 1;
        }
        for (Type argument : bridgeType.getArgumentTypes()) {
            if (index >= code.size()) return null;
            if (!isLoad(code.get(index++), loadOpcode(argument), local)) return null;
            if (index < code.size() && code.get(index).getOpcode() == Opcodes.CHECKCAST) {
                index++;
            }
            local += argument.getSize();
        }
        if (code.size() != index + 2) return null;
        if (!(code.get(index) instanceof MethodInsnNode)) return null;
        MethodInsnNode call = (MethodInsnNode) code.get(index++);
        if (!owner.name.equals(call.owner)
                || Type.getArgumentTypes(bridge.desc).length
                != Type.getArgumentTypes(call.desc).length) {
            return null;
        }
        if (code.get(index).getOpcode() != returnOpcode(bridgeType.getReturnType())) {
            return null;
        }
        for (MethodNode candidate : owner.methods) {
            if (candidate != bridge && candidate.name.equals(call.name)
                    && candidate.desc.equals(call.desc)) {
                return candidate;
            }
        }
        return null;
    }

    private static boolean hasNativeField(List<FieldNode> fields) {
        // Fields have no ACC_NATIVE; keep this helper to make the policy
        // explicit and to leave room for JVMTI metadata checks.
        return false;
    }

    /** Exact forwarding shape used by the mapping overlay's duplicate aliases. */
    private static boolean isStrictAlias(ClassNode owner, MethodNode method) {
        if (method.tryCatchBlocks != null && !method.tryCatchBlocks.isEmpty()) return false;
        List<AbstractInsnNode> code = executableInstructions(method);
        Type methodType = Type.getMethodType(method.desc);
        boolean isStatic = (method.access & Opcodes.ACC_STATIC) != 0;
        int expectedLoads = methodType.getArgumentTypes().length + (isStatic ? 0 : 1);
        if (code.size() != expectedLoads + 2) return false;
        int index = 0;
        int local = isStatic ? 0 : 0;
        if (!isStatic) {
            if (!isLoad(code.get(index), Opcodes.ALOAD, 0)) return false;
            index++;
            local = 1;
        }
        for (Type argument : methodType.getArgumentTypes()) {
            int expectedOpcode = loadOpcode(argument);
            if (!isLoad(code.get(index), expectedOpcode, local)) return false;
            index++;
            local += argument.getSize();
        }
        if (!(code.get(index) instanceof MethodInsnNode)) return false;
        MethodInsnNode call = (MethodInsnNode) code.get(index++);
        int expectedInvoke = isStatic ? Opcodes.INVOKESTATIC : Opcodes.INVOKEVIRTUAL;
        if (call.getOpcode() != expectedInvoke || call.itf
                || !owner.name.equals(call.owner)
                || !method.name.equals(call.name) || !method.desc.equals(call.desc)) {
            return false;
        }
        return code.get(index).getOpcode() == returnOpcode(methodType.getReturnType());
    }

    private static List<AbstractInsnNode> executableInstructions(MethodNode method) {
        List<AbstractInsnNode> code = new ArrayList<>();
        for (AbstractInsnNode insn : method.instructions) {
            if (insn.getOpcode() >= 0) code.add(insn);
        }
        return code;
    }

    private static boolean isLoad(AbstractInsnNode instruction, int opcode, int local) {
        return instruction instanceof org.objectweb.asm.tree.VarInsnNode
                && instruction.getOpcode() == opcode
                && ((org.objectweb.asm.tree.VarInsnNode) instruction).var == local;
    }

    private static int loadOpcode(Type type) {
        switch (type.getSort()) {
            case Type.LONG: return Opcodes.LLOAD;
            case Type.FLOAT: return Opcodes.FLOAD;
            case Type.DOUBLE: return Opcodes.DLOAD;
            case Type.OBJECT:
            case Type.ARRAY: return Opcodes.ALOAD;
            default: return Opcodes.ILOAD;
        }
    }

    private static int returnOpcode(Type type) {
        switch (type.getSort()) {
            case Type.VOID: return Opcodes.RETURN;
            case Type.LONG: return Opcodes.LRETURN;
            case Type.FLOAT: return Opcodes.FRETURN;
            case Type.DOUBLE: return Opcodes.DRETURN;
            case Type.OBJECT:
            case Type.ARRAY: return Opcodes.ARETURN;
            default: return Opcodes.IRETURN;
        }
    }

    private static String returnToken(String descriptor) {
        return typeToken(Type.getMethodType(descriptor).getReturnType().getDescriptor());
    }

    private static String typeToken(String descriptor) {
        String token = descriptor.replace('[', 'A').replace('/', '_')
                .replace(';', '_').replace('(', 'P').replace(')', 'Q');
        if (token.length() > 48) token = token.substring(0, 48);
        return token;
    }

    private static Map<String, byte[]> copyBytes(Map<String, byte[]> source) {
        LinkedHashMap<String, byte[]> copy = new LinkedHashMap<>();
        for (Map.Entry<String, byte[]> entry : source.entrySet()) {
            copy.put(entry.getKey(), entry.getValue().clone());
        }
        return copy;
    }

    private static void verifyClassBytes(byte[] bytes) throws Exception {
        ClassReader reader = new ClassReader(bytes);
        reader.accept(new CheckClassAdapter(new ClassWriter(0), false), 0);
        ClassNode owner = new ClassNode(Opcodes.ASM9);
        reader.accept(owner, 0);
        for (MethodNode method : owner.methods) {
            if ((method.access & (Opcodes.ACC_ABSTRACT | Opcodes.ACC_NATIVE)) != 0) {
                continue;
            }
            new Analyzer<BasicValue>(new BasicVerifier()).analyze(owner.name, method);
        }
    }

    private static String shortReason(Throwable failure) {
        String message = failure.getMessage();
        return failure.getClass().getSimpleName()
                + (message == null ? "" : ":" + message.replace('\n', ' '));
    }

    private static byte[] readAll(InputStream input) throws IOException {
        ByteArrayOutputStream output = new ByteArrayOutputStream();
        byte[] buffer = new byte[8192];
        int count;
        while ((count = input.read(buffer)) >= 0) output.write(buffer, 0, count);
        return output.toByteArray();
    }

    public static final class Plan {
        private final Map<MethodId, String> methods;
        private final Map<FieldId, String> fields;
        private final Set<MethodNode> removals;
        private final Map<MethodNode, Integer> accessUpdates;
        private final Map<String, TypeInfo> hierarchy;
        private final Set<MethodId> methodDeclarations;
        private final Set<FieldId> fieldDeclarations;
        public final List<Change> changes;
        public final List<Skip> skips;

        private Plan(Map<MethodId, String> methods, Map<FieldId, String> fields,
                     Set<MethodNode> removals,
                     Map<MethodNode, Integer> accessUpdates,
                     List<Change> changes, List<Skip> skips,
                     Map<String, TypeInfo> hierarchy,
                     Set<MethodId> methodDeclarations,
                     Set<FieldId> fieldDeclarations) {
            this.methods = Collections.unmodifiableMap(new LinkedHashMap<>(methods));
            this.fields = Collections.unmodifiableMap(new LinkedHashMap<>(fields));
            Set<MethodNode> removalCopy = Collections.newSetFromMap(
                    new IdentityHashMap<MethodNode, Boolean>());
            removalCopy.addAll(removals);
            this.removals = Collections.unmodifiableSet(removalCopy);
            Map<MethodNode, Integer> accessCopy = new IdentityHashMap<>();
            accessCopy.putAll(accessUpdates);
            this.accessUpdates = Collections.unmodifiableMap(accessCopy);
            this.hierarchy = Collections.unmodifiableMap(new LinkedHashMap<>(hierarchy));
            this.methodDeclarations = Collections.unmodifiableSet(
                    new LinkedHashSet<>(methodDeclarations));
            this.fieldDeclarations = Collections.unmodifiableSet(
                    new LinkedHashSet<>(fieldDeclarations));
            this.changes = Collections.unmodifiableList(new ArrayList<>(changes));
            this.skips = Collections.unmodifiableList(new ArrayList<>(skips));
        }

        private String resolveMethod(String owner, String name, String desc) {
            MethodId declaration = resolveMethodDeclaration(owner, name, desc);
            return declaration == null ? null : methods.get(declaration);
        }

        private String resolveField(String owner, String name, String desc) {
            FieldId declaration = resolveFieldDeclaration(owner, name, desc);
            return declaration == null ? null : fields.get(declaration);
        }

        private String resolveAnnotationElement(String annotationDescriptor,
                                                String name) {
            Type annotationType;
            try {
                annotationType = Type.getType(annotationDescriptor);
            } catch (IllegalArgumentException invalid) {
                return null;
            }
            if (annotationType.getSort() != Type.OBJECT) return null;
            String owner = annotationType.getInternalName();
            String result = null;
            int matches = 0;
            for (MethodId declaration : methodDeclarations) {
                if (!owner.equals(declaration.owner) || !name.equals(declaration.name)
                        || Type.getArgumentTypes(declaration.descriptor).length != 0) {
                    continue;
                }
                matches++;
                String renamed = methods.get(declaration);
                if (renamed != null) result = renamed;
            }
            return matches == 1 ? result : null;
        }

        private MethodId resolveMethodDeclaration(String owner, String name,
                                                  String desc) {
            MethodId direct = new MethodId(owner, name, desc);
            if (methodDeclarations.contains(direct)) return direct;
            Set<String> visited = new HashSet<>();
            String current = owner;
            while (current != null && visited.add(current)) {
                TypeInfo info = hierarchy.get(current);
                if (info == null) break;
                current = info.superName;
                if (current != null) {
                    MethodId inherited = new MethodId(current, name, desc);
                    if (methodDeclarations.contains(inherited)) return inherited;
                }
            }
            ArrayDeque<String> interfaces = new ArrayDeque<>();
            current = owner;
            visited.clear();
            while (current != null && visited.add(current)) {
                TypeInfo info = hierarchy.get(current);
                if (info == null) break;
                interfaces.addAll(info.interfaces);
                current = info.superName;
            }
            visited.clear();
            while (!interfaces.isEmpty()) {
                String candidate = interfaces.removeFirst();
                if (!visited.add(candidate)) continue;
                MethodId inherited = new MethodId(candidate, name, desc);
                if (methodDeclarations.contains(inherited)) return inherited;
                TypeInfo info = hierarchy.get(candidate);
                if (info != null) interfaces.addAll(info.interfaces);
            }
            return null;
        }

        private FieldId resolveFieldDeclaration(String owner, String name,
                                                String desc) {
            Set<String> visited = new HashSet<>();
            ArrayDeque<String> queue = new ArrayDeque<>();
            queue.add(owner);
            while (!queue.isEmpty()) {
                String current = queue.removeFirst();
                if (!visited.add(current)) continue;
                FieldId direct = new FieldId(current, name, desc);
                if (fieldDeclarations.contains(direct)) return direct;
                TypeInfo info = hierarchy.get(current);
                if (info == null) continue;
                if (info.superName != null) queue.addLast(info.superName);
                queue.addAll(info.interfaces);
            }
            return null;
        }
    }

    public static final class ArchiveResult {
        public final Map<String, byte[]> bytes;
        public final List<Change> changes;
        public final List<Skip> skips;
        public final boolean committed;
        public final String reason;

        private ArchiveResult(Map<String, byte[]> bytes, List<Change> changes,
                              List<Skip> skips, boolean committed, String reason) {
            this.bytes = Collections.unmodifiableMap(copyBytes(bytes));
            this.changes = Collections.unmodifiableList(new ArrayList<>(changes));
            this.skips = Collections.unmodifiableList(new ArrayList<>(skips));
            this.committed = committed;
            this.reason = reason;
        }

        private static ArchiveResult failed(Map<String, byte[]> input, String reason) {
            return failed(input, reason, Collections.<Change>emptyList(),
                    Collections.<Skip>emptyList());
        }

        private static ArchiveResult failed(Map<String, byte[]> input, String reason,
                                            List<Change> changes, List<Skip> skips) {
            return new ArchiveResult(input, changes, skips, false, reason);
        }
    }

    public static final class Change {
        public final String owner;
        public final String oldName;
        public final String descriptor;
        public final String newName;
        public final String action;
        public final String reason;

        Change(String owner, String oldName, String descriptor, String newName,
               String action, String reason) {
            this.owner = owner;
            this.oldName = oldName;
            this.descriptor = descriptor;
            this.newName = newName;
            this.action = action;
            this.reason = reason;
        }
    }

    public static final class Skip {
        public final String owner;
        public final String signature;
        public final String reason;

        Skip(String owner, String signature, String reason) {
            this.owner = owner;
            this.signature = signature;
            this.reason = reason;
        }
    }

    private static final class MethodDecl {
        final ClassNode owner;
        final MethodNode method;
        final MethodId id;

        MethodDecl(ClassNode owner, MethodNode method) {
            this.owner = owner;
            this.method = method;
            this.id = new MethodId(owner.name, method.name, method.desc);
        }
    }

    private static final class IntPair {
        final int left;
        final int right;

        IntPair(int left, int right) {
            this.left = left;
            this.right = right;
        }
    }

    private static final class DisjointSet {
        final int[] parent;
        final byte[] rank;

        DisjointSet(int size) {
            parent = new int[size];
            rank = new byte[size];
            for (int i = 0; i < size; i++) parent[i] = i;
        }

        int find(int value) {
            int root = value;
            while (parent[root] != root) root = parent[root];
            while (parent[value] != value) {
                int next = parent[value];
                parent[value] = root;
                value = next;
            }
            return root;
        }

        void union(int left, int right) {
            int leftRoot = find(left);
            int rightRoot = find(right);
            if (leftRoot == rightRoot) return;
            if (rank[leftRoot] < rank[rightRoot]) {
                parent[leftRoot] = rightRoot;
            } else if (rank[leftRoot] > rank[rightRoot]) {
                parent[rightRoot] = leftRoot;
            } else {
                parent[rightRoot] = leftRoot;
                rank[leftRoot]++;
            }
        }
    }

    private static final class MethodId {
        final String owner;
        final String name;
        final String descriptor;

        MethodId(String owner, String name, String descriptor) {
            this.owner = owner;
            this.name = name;
            this.descriptor = descriptor;
        }

        @Override public boolean equals(Object other) {
            if (!(other instanceof MethodId)) return false;
            MethodId that = (MethodId) other;
            return owner.equals(that.owner) && name.equals(that.name)
                    && descriptor.equals(that.descriptor);
        }

        @Override public int hashCode() {
            return Objects.hash(owner, name, descriptor);
        }
    }

    private static final class FieldId {
        final String owner;
        final String name;
        final String descriptor;

        FieldId(String owner, String name, String descriptor) {
            this.owner = owner;
            this.name = name;
            this.descriptor = descriptor;
        }

        @Override public boolean equals(Object other) {
            if (!(other instanceof FieldId)) return false;
            FieldId that = (FieldId) other;
            return owner.equals(that.owner) && name.equals(that.name)
                    && descriptor.equals(that.descriptor);
        }

        @Override public int hashCode() {
            return Objects.hash(owner, name, descriptor);
        }
    }

    private static final class TypeInfo {
        final String superName;
        final List<String> interfaces;

        TypeInfo(String superName, List<String> interfaces) {
            this.superName = superName;
            this.interfaces = interfaces;
        }
    }
}
