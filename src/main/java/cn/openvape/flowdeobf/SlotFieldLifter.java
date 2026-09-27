package cn.openvape.flowdeobf;

import org.objectweb.asm.ClassReader;
import org.objectweb.asm.ClassWriter;
import org.objectweb.asm.Opcodes;
import org.objectweb.asm.Type;
import org.objectweb.asm.tree.AbstractInsnNode;
import org.objectweb.asm.tree.ClassNode;
import org.objectweb.asm.tree.FieldInsnNode;
import org.objectweb.asm.tree.FieldNode;
import org.objectweb.asm.tree.FrameNode;
import org.objectweb.asm.tree.InsnList;
import org.objectweb.asm.tree.InsnNode;
import org.objectweb.asm.tree.IntInsnNode;
import org.objectweb.asm.tree.LdcInsnNode;
import org.objectweb.asm.tree.MethodInsnNode;
import org.objectweb.asm.tree.MethodNode;
import org.objectweb.asm.tree.TypeInsnNode;
import org.objectweb.asm.tree.VarInsnNode;
import org.objectweb.asm.tree.analysis.Analyzer;
import org.objectweb.asm.tree.analysis.BasicInterpreter;
import org.objectweb.asm.tree.analysis.BasicValue;
import org.objectweb.asm.tree.analysis.BasicVerifier;
import org.objectweb.asm.tree.analysis.Frame;
import org.objectweb.asm.tree.analysis.SourceInterpreter;
import org.objectweb.asm.tree.analysis.SourceValue;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Set;
import java.util.zip.ZipEntry;
import java.util.zip.ZipInputStream;
import java.util.zip.ZipOutputStream;

/**
 * Promotes fixed elements of obfuscator-owned instance or static array buckets
 * to fields.
 *
 * <p>This pass deliberately assigns structural names such as
 * {@code slot_D_383_350}. It does not infer domain semantics. A root is changed
 * only when every use of that root in the declaring class is either a proven
 * fixed nested access or storage initialization. Static roots use a stricter
 * policy: their root and bucket storage must be fully proven in
 * {@code <clinit>} before any slot is changed.</p>
 */
public final class SlotFieldLifter {
    private static final String ROOT_DESC = "[Ljava/lang/Object;";

    private SlotFieldLifter() {
    }

    public static void main(String[] args) throws Exception {
        if (args.length != 2 && args.length != 3) {
            System.err.println("usage: SlotFieldLifter <input.jar> <report-dir> [rewritten.jar]");
            System.exit(2);
        }
        Path output = args.length == 3 ? Paths.get(args[2]) : null;
        liftArchive(Paths.get(args[0]), Paths.get(args[1]), output);
    }

    static ArchiveResult liftArchive(Path input, Path reportDirectory, Path rewrittenOutput)
            throws Exception {
        Files.createDirectories(reportDirectory);
        if (rewrittenOutput != null) {
            Path normalizedInput = input.toAbsolutePath().normalize();
            Path normalizedOutput = rewrittenOutput.toAbsolutePath().normalize();
            if (normalizedInput.equals(normalizedOutput)) {
                throw new IllegalArgumentException("rewritten output must not replace input");
            }
            if (normalizedOutput.getParent() != null) {
                Files.createDirectories(normalizedOutput.getParent());
            }
        }

        List<EntryBytes> entries = readEntries(input);
        List<String> rows = new ArrayList<>();
        rows.add("class\tmethod\tinstruction\taction\troot\tbucket\tslot\tfield\tdescriptor\treason");
        ArchiveResult result = new ArchiveResult();
        Map<String, byte[]> replacements = new LinkedHashMap<>();

        for (EntryBytes entry : entries) {
            if (!entry.name.endsWith(".class")) continue;
            result.classes++;
            ClassNode owner = new ClassNode(Opcodes.ASM9);
            try {
                new ClassReader(entry.bytes).accept(owner, 0);
            } catch (Throwable failure) {
                result.parseErrors++;
                rows.add(tsv("<unknown>", "<class>", -1, "skip", "", "", "", "", "",
                        "parse:" + shortReason(failure)));
                continue;
            }

            ClassNode candidate = new ClassNode(Opcodes.ASM9);
            new ClassReader(entry.bytes).accept(candidate, 0);
            int rowStart = rows.size();
            try {
                Result transformed = transformClass(candidate, rows);
                result.candidateRoots += transformed.candidateRoots;
                result.rejectedRoots += transformed.rejectedRoots;
                result.liftedSlots += transformed.liftedSlots;
                result.rewrittenReads += transformed.rewrittenReads;
                result.rewrittenWrites += transformed.rewrittenWrites;
                result.removedInitializers += transformed.removedInitializers;
                result.removedDeadKeyLocals += transformed.removedDeadKeyLocals;
                if (!transformed.changed) continue;
                byte[] bytes = writeAndVerify(candidate);
                replacements.put(candidate.name, bytes);
                result.changedClasses++;
            } catch (Throwable failure) {
                while (rows.size() > rowStart) rows.remove(rows.size() - 1);
                result.rollbackClasses++;
                rows.add(tsv(owner.name, "<class>", -1, "rollback", "", "", "", "", "",
                        "verification:" + shortReason(failure)));
            }
        }

        if (rewrittenOutput != null) {
            writeArchive(entries, replacements, rewrittenOutput, result);
            verifyArchive(rewrittenOutput, result);
        }
        Files.write(reportDirectory.resolve("slots.tsv"), rows, StandardCharsets.UTF_8);
        List<String> audit = new ArrayList<>();
        audit.add("input=" + input.toAbsolutePath());
        audit.add("classes=" + result.classes);
        audit.add("parse_errors=" + result.parseErrors);
        audit.add("candidate_roots=" + result.candidateRoots);
        audit.add("rejected_roots=" + result.rejectedRoots);
        audit.add("lifted_slots=" + result.liftedSlots);
        audit.add("rewritten_reads=" + result.rewrittenReads);
        audit.add("rewritten_writes=" + result.rewrittenWrites);
        audit.add("removed_initializers=" + result.removedInitializers);
        audit.add("removed_dead_key_locals=" + result.removedDeadKeyLocals);
        audit.add("changed_classes=" + result.changedClasses);
        audit.add("rollback_classes=" + result.rollbackClasses);
        audit.add("output_classes=" + result.outputClasses);
        audit.add("output_verification_errors=" + result.outputVerificationErrors);
        audit.add("semantic_names_inferred=false");
        audit.add("gate=" + (result.parseErrors == 0 && result.rollbackClasses == 0
                && result.outputVerificationErrors == 0 ? "PASS" : "FAIL"));
        Files.write(reportDirectory.resolve("audit.txt"), audit, StandardCharsets.UTF_8);
        Files.write(reportDirectory.resolve("gate.txt"), Collections.singletonList(
                audit.get(audit.size() - 1).substring("gate=".length())), StandardCharsets.UTF_8);
        System.out.println("classes=" + result.classes + " changed=" + result.changedClasses
                + " slots=" + result.liftedSlots + " reads=" + result.rewrittenReads
                + " writes=" + result.rewrittenWrites + " rejected_roots="
                + result.rejectedRoots + " report=" + reportDirectory);
        return result;
    }

    /** Class-local entry point used by focused tests and manual tooling. */
    static Result transformClass(ClassNode owner, List<String> audit) throws Exception {
        Result result = new Result();
        Map<String, FieldNode> roots = candidateRoots(owner);
        result.candidateRoots = roots.size();
        if (roots.isEmpty()) return result;

        Map<MethodNode, MethodAnalysis> analyses = new IdentityHashMap<>();
        for (MethodNode method : owner.methods) {
            if (method.instructions == null || method.instructions.size() == 0) continue;
            try {
                analyses.put(method, MethodAnalysis.analyze(owner.name, method));
            } catch (Throwable failure) {
                for (String root : roots.keySet()) {
                    audit.add(tsv(owner.name, method.name + method.desc, -1, "reject-root",
                            root, "", "", "", "", "analysis:" + shortReason(failure)));
                }
                result.rejectedRoots += roots.size();
                return result;
            }
        }

        for (Map.Entry<String, FieldNode> rootEntry : roots.entrySet()) {
            RootPlan plan = planRoot(owner, rootEntry.getValue(), analyses, audit);
            if (!plan.accepted) {
                result.rejectedRoots++;
                continue;
            }
            applyPlan(owner, plan, audit, result);
        }
        if (result.liftedSlots > 0) {
            result.removedDeadKeyLocals = removeDeadKeyLocals(owner, audit);
        }
        result.changed = result.liftedSlots > 0;
        return result;
    }

    /**
     * Removes the exact class-key XOR prologue left behind when all consumers
     * of a method-local long key were eliminated by earlier constant rewrites.
     * The local must have one store, no reads, and a four-instruction producer
     * made only from a same-class static long field and a long constant.
     */
    private static int removeDeadKeyLocals(ClassNode owner, List<String> audit) {
        int removed = 0;
        for (MethodNode method : owner.methods) {
            if (method.instructions == null || method.instructions.size() == 0) continue;
            Map<Integer, List<VarInsnNode>> stores = new LinkedHashMap<>();
            Set<Integer> reads = new HashSet<>();
            for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
                 insn = insn.getNext()) {
                if (!(insn instanceof VarInsnNode)) continue;
                VarInsnNode variable = (VarInsnNode) insn;
                if (variable.getOpcode() == Opcodes.LSTORE) {
                    stores.computeIfAbsent(variable.var, ignored -> new ArrayList<>()).add(variable);
                } else if (variable.getOpcode() == Opcodes.LLOAD) {
                    reads.add(variable.var);
                }
            }
            for (Map.Entry<Integer, List<VarInsnNode>> entry : stores.entrySet()) {
                if (entry.getValue().size() != 1 || reads.contains(entry.getKey())) continue;
                VarInsnNode store = entry.getValue().get(0);
                AbstractInsnNode xor = previousCode(store);
                AbstractInsnNode constant = previousCode(xor);
                AbstractInsnNode field = previousCode(constant);
                if (xor == null || xor.getOpcode() != Opcodes.LXOR
                        || !(constant instanceof LdcInsnNode)
                        || !(((LdcInsnNode) constant).cst instanceof Long)
                        || !(field instanceof FieldInsnNode)) continue;
                FieldInsnNode keyField = (FieldInsnNode) field;
                if (keyField.getOpcode() != Opcodes.GETSTATIC
                        || !keyField.owner.equals(owner.name)
                        || !"J".equals(keyField.desc)) continue;
                if (nextCode(field) != constant || nextCode(constant) != xor
                        || nextCode(xor) != store) continue;
                method.instructions.remove(field);
                method.instructions.remove(constant);
                method.instructions.remove(xor);
                method.instructions.remove(store);
                removed++;
                audit.add(tsv(owner.name, method.name + method.desc, -1,
                        "remove-dead-key-local", "", "", "", "", "J",
                        "single-store-no-load-static-long-xor"));
            }
        }
        return removed;
    }

    private static Map<String, FieldNode> candidateRoots(ClassNode owner) {
        Map<String, FieldNode> result = new LinkedHashMap<>();
        for (FieldNode field : owner.fields) {
            if (ROOT_DESC.equals(field.desc)
                    && (field.access & Opcodes.ACC_PRIVATE) != 0) {
                result.put(field.name, field);
            }
        }
        return result;
    }

    private static RootPlan planRoot(ClassNode owner, FieldNode root,
                                     Map<MethodNode, MethodAnalysis> analyses,
                                     List<String> audit) {
        RootPlan plan = new RootPlan(root);
        boolean staticRoot = isStatic(root);
        int readOpcode = staticRoot ? Opcodes.GETSTATIC : Opcodes.GETFIELD;
        int writeOpcode = staticRoot ? Opcodes.PUTSTATIC : Opcodes.PUTFIELD;
        Set<FieldInsnNode> classifiedReads = Collections.newSetFromMap(new IdentityHashMap<FieldInsnNode, Boolean>());
        Set<FieldInsnNode> rootReads = Collections.newSetFromMap(new IdentityHashMap<FieldInsnNode, Boolean>());

        for (Map.Entry<MethodNode, MethodAnalysis> entry : analyses.entrySet()) {
            MethodNode method = entry.getKey();
            MethodAnalysis analysis = entry.getValue();
            int instruction = 0;
            for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
                 insn = insn.getNext(), instruction++) {
                if (insn instanceof FieldInsnNode) {
                    FieldInsnNode field = (FieldInsnNode) insn;
                    if (field.owner.equals(owner.name) && field.name.equals(root.name)
                            && field.desc.equals(root.desc)) {
                        if (field.getOpcode() == readOpcode) {
                            rootReads.add(field);
                        } else if (field.getOpcode() == writeOpcode) {
                            RootInitialization initialization = rootInitialization(
                                    root, method, field, instruction, analysis);
                            if (initialization == null) {
                                return reject(plan, owner, method, instruction, audit,
                                        staticRoot ? "unproved-static-root-write"
                                                : "root-write-outside-constructor");
                            }
                            plan.rootInitializations.add(initialization);
                        } else {
                            return reject(plan, owner, method, instruction, audit,
                                    "unexpected-root-field-opcode");
                        }
                    }
                }

                int opcode = insn.getOpcode();
                if (!isArrayLoad(opcode) && !isArrayStore(opcode)) continue;
                Access access = parseNestedAccess(owner, root, method, insn, instruction, analysis);
                if (access != null) {
                    plan.accesses.add(access);
                    classifiedReads.add(access.rootRead);
                    continue;
                }
                FieldInsnNode initializerRead = directRootArrayRead(owner, root, method,
                        insn, analysis);
                if (initializerRead != null) {
                    BucketInitialization initialization = bucketInitialization(
                            root, method, insn, instruction, initializerRead, analysis);
                    if (initialization != null) {
                        classifiedReads.add(initializerRead);
                        plan.bucketInitializations.add(initialization);
                    }
                }
            }
        }

        if (staticRoot && plan.rootInitializations.size() != 1) {
            return reject(plan, owner, null, -1, audit,
                    "static-root-requires-single-clinit-initializer");
        }
        for (FieldInsnNode read : rootReads) {
            if (!classifiedReads.contains(read)) {
                return reject(plan, owner, findMethod(owner, read), -1, audit,
                        "dynamic-index-or-escaping-root");
            }
        }
        if (plan.accesses.isEmpty()) {
            return reject(plan, owner, null, -1, audit, "no-fixed-nested-accesses");
        }

        Map<SlotKey, List<Access>> grouped = new LinkedHashMap<>();
        for (Access access : plan.accesses) {
            grouped.computeIfAbsent(access.key, ignored -> new ArrayList<>()).add(access);
        }
        plan.accessGroups = grouped.size();
        for (Map.Entry<SlotKey, List<Access>> entry : grouped.entrySet()) {
            String descriptor = unifyDescriptor(entry.getValue());
            if (descriptor == null) {
                Access first = entry.getValue().get(0);
                audit.add(tsv(owner.name, first.method.name + first.method.desc,
                        first.instruction, "reject-slot", root.name, first.key.bucket,
                        first.key.slot, "", "", "type-conflict"));
                plan.rejectedSlots++;
                continue;
            }
            String fieldName = uniqueFieldName(owner, structuralName(root.name,
                    entry.getKey().bucket, entry.getKey().slot));
            plan.slots.put(entry.getKey(), new SlotPlan(entry.getKey(), fieldName,
                    descriptor, entry.getValue()));
        }
        if (staticRoot && plan.rejectedSlots != 0) {
            return reject(plan, owner, null, -1, audit,
                    "static-root-has-type-conflicting-slot");
        }
        if (plan.slots.isEmpty()) {
            return reject(plan, owner, null, -1, audit, "no-type-consistent-slots");
        }
        if (staticRoot) {
            String staticProofFailure = validateStaticStorage(plan);
            if (staticProofFailure != null) {
                return reject(plan, owner, null, -1, audit, staticProofFailure);
            }
        }
        plan.accepted = true;
        return plan;
    }

    private static RootPlan reject(RootPlan plan, ClassNode owner, MethodNode method,
                                   int instruction, List<String> audit, String reason) {
        audit.add(tsv(owner.name, method == null ? "<class>" : method.name + method.desc,
                instruction, "reject-root", plan.root.name, "", "", "", "", reason));
        plan.accepted = false;
        return plan;
    }

    /**
     * Static roots are accepted only as a closed storage model. Besides fixed
     * indexes, this proves that the one root allocation and the relevant bucket
     * allocations cover every projected access and have compatible array
     * descriptors. This is intentionally stricter than the legacy instance
     * path.
     */
    private static String validateStaticStorage(RootPlan plan) {
        RootInitialization rootInitialization = plan.rootInitializations.get(0);
        int rootLength = rootInitialization.arrayLength;
        Map<Integer, List<BucketInitialization>> buckets = new LinkedHashMap<>();
        for (BucketInitialization initialization : plan.bucketInitializations) {
            if (initialization.bucket < 0 || initialization.bucket >= rootLength) {
                return "static-bucket-outside-proven-root-length";
            }
            if (!ordered(initialization.method, rootInitialization.operation,
                    initialization.rootRead, initialization.indexProducer,
                    initialization.operation)) {
                return "static-bucket-initializer-not-after-root-initializer";
            }
            buckets.computeIfAbsent(initialization.bucket,
                    ignored -> new ArrayList<>()).add(initialization);
        }

        Map<Integer, String> bucketDescriptors = new LinkedHashMap<>();
        for (Access access : plan.accesses) {
            if (access.key.bucket < 0 || access.key.bucket >= rootLength) {
                return "static-access-outside-proven-root-length";
            }
            String previous = bucketDescriptors.putIfAbsent(access.key.bucket,
                    access.key.bucketDescriptor);
            if (previous != null && !previous.equals(access.key.bucketDescriptor)) {
                return "static-bucket-descriptor-conflict";
            }
            List<BucketInitialization> initializations = buckets.get(access.key.bucket);
            if (initializations == null || initializations.size() != 1) {
                return "static-access-requires-single-bucket-initializer";
            }
            BucketInitialization bucket = initializations.get(0);
            if (bucket.arrayDescriptor == null
                    || !bucket.arrayDescriptor.equals(access.key.bucketDescriptor)) {
                return "static-bucket-allocation-type-unproved";
            }
            if (access.key.slot < 0 || access.key.slot >= bucket.arrayLength) {
                return "static-slot-outside-proven-bucket-length";
            }
            if ("<clinit>".equals(access.method.name)
                    && !ordered(access.method, bucket.operation, access.rootRead,
                    access.indexProducer, access.operation)) {
                return "static-clinit-access-not-after-bucket-initializer";
            }
        }
        return null;
    }

    private static boolean isStatic(FieldNode field) {
        return (field.access & Opcodes.ACC_STATIC) != 0;
    }

    private static Access parseNestedAccess(ClassNode owner, FieldNode root,
                                            MethodNode method, AbstractInsnNode operation,
                                            int instruction, MethodAnalysis analysis) {
        boolean staticRoot = isStatic(root);
        int opcode = operation.getOpcode();
        boolean write = isArrayStore(opcode);
        Frame<SourceValue> sourceFrame = analysis.sourceFrame(operation);
        if (sourceFrame == null) return null;
        AbstractInsnNode indexProducer = uniqueProducer(sourceFrame, write ? 1 : 0);
        AbstractInsnNode arrayProducer = uniqueProducer(sourceFrame, write ? 2 : 1);
        Integer slot = intConstant(indexProducer);
        if (slot == null || !(arrayProducer instanceof TypeInsnNode)
                || arrayProducer.getOpcode() != Opcodes.CHECKCAST) return null;
        TypeInsnNode bucketCast = (TypeInsnNode) arrayProducer;
        String bucketDescriptor = bucketCast.desc;
        if (!bucketDescriptor.startsWith("[")) return null;
        if (!opcodeMatchesArray(opcode, bucketDescriptor)) return null;

        AbstractInsnNode outerLoad = uniqueProducer(analysis.sourceFrame(bucketCast), 0);
        if (outerLoad == null || outerLoad.getOpcode() != Opcodes.AALOAD) return null;
        Frame<SourceValue> outerFrame = analysis.sourceFrame(outerLoad);
        AbstractInsnNode bucketProducer = uniqueProducer(outerFrame, 0);
        AbstractInsnNode rootProducer = uniqueProducer(outerFrame, 1);
        Integer bucket = intConstant(bucketProducer);
        if (bucket == null || !(rootProducer instanceof FieldInsnNode)) return null;
        FieldInsnNode rootRead = (FieldInsnNode) rootProducer;
        int rootReadOpcode = staticRoot ? Opcodes.GETSTATIC : Opcodes.GETFIELD;
        if (rootRead.getOpcode() != rootReadOpcode || !rootRead.owner.equals(owner.name)
                || !rootRead.name.equals(root.name) || !rootRead.desc.equals(root.desc)) return null;

        VarInsnNode receiver = null;
        AbstractInsnNode prefixStart = rootRead;
        if (!staticRoot) {
            AbstractInsnNode receiverProducer = uniqueProducer(analysis.sourceFrame(rootRead), 0);
            if (!(receiverProducer instanceof VarInsnNode)
                    || receiverProducer.getOpcode() != Opcodes.ALOAD) return null;
            receiver = (VarInsnNode) receiverProducer;
            prefixStart = receiver;
            if (previousCode(rootRead) != receiver) return null;
        }
        if (staticRoot) {
            if (!ordered(method, rootRead, bucketProducer, outerLoad, bucketCast,
                    indexProducer, operation)) return null;
        } else if (!ordered(method, receiver, rootRead, bucketProducer, outerLoad,
                bucketCast, indexProducer, operation)) return null;
        if (!removablePrefix(prefixStart, indexProducer, rootRead, bucketProducer,
                outerLoad, bucketCast, operation, write)) return null;

        String provenWriteDescriptor = staticRoot && opcode == Opcodes.AASTORE
                ? provenReferenceWriteDescriptor(operation, analysis) : null;
        String descriptor = provenWriteDescriptor != null ? provenWriteDescriptor
                : descriptorForAccess(operation, bucketDescriptor, analysis);
        boolean referenceTypeFallback = staticRoot && opcode == Opcodes.AASTORE
                && provenWriteDescriptor == null
                && "Ljava/lang/Object;".equals(descriptor);
        return new Access(method, operation, instruction, receiver,
                rootRead, indexProducer, new SlotKey(root.name, bucket, slot,
                bucketDescriptor), descriptor, write, referenceTypeFallback);
    }

    private static String provenReferenceWriteDescriptor(AbstractInsnNode operation,
                                                          MethodAnalysis analysis) {
        AbstractInsnNode value = uniqueProducer(analysis.sourceFrame(operation), 0);
        return provenReferenceDescriptor(value, analysis,
                Collections.newSetFromMap(new IdentityHashMap<AbstractInsnNode, Boolean>()));
    }

    private static String provenReferenceDescriptor(AbstractInsnNode producer,
                                                    MethodAnalysis analysis,
                                                    Set<AbstractInsnNode> visiting) {
        if (producer == null || !visiting.add(producer)) return null;
        try {
            int opcode = producer.getOpcode();
            if (producer instanceof TypeInsnNode) {
                TypeInsnNode type = (TypeInsnNode) producer;
                if (opcode == Opcodes.NEW) return "L" + type.desc + ";";
                if (opcode == Opcodes.ANEWARRAY) {
                    return type.desc.startsWith("[") ? "[" + type.desc
                            : "[L" + type.desc + ";";
                }
                if (opcode == Opcodes.CHECKCAST) return descriptor(type);
            }
            if (producer instanceof IntInsnNode && opcode == Opcodes.NEWARRAY) {
                return allocatedArrayDescriptor(producer, analysis);
            }
            if (producer instanceof FieldInsnNode
                    && (opcode == Opcodes.GETFIELD || opcode == Opcodes.GETSTATIC)) {
                String fieldDescriptor = ((FieldInsnNode) producer).desc;
                Type type = Type.getType(fieldDescriptor);
                return type.getSort() == Type.OBJECT || type.getSort() == Type.ARRAY
                        ? fieldDescriptor : null;
            }
            if (producer instanceof MethodInsnNode) {
                Type type = Type.getReturnType(((MethodInsnNode) producer).desc);
                return type.getSort() == Type.OBJECT || type.getSort() == Type.ARRAY
                        ? type.getDescriptor() : null;
            }
            if (producer instanceof LdcInsnNode) {
                Object constant = ((LdcInsnNode) producer).cst;
                if (constant instanceof String) return "Ljava/lang/String;";
                if (constant instanceof Type) {
                    return ((Type) constant).getSort() == Type.METHOD
                            ? "Ljava/lang/invoke/MethodType;"
                            : "Ljava/lang/Class;";
                }
            }
            if (opcode == Opcodes.DUP) {
                return provenReferenceDescriptor(
                        uniqueProducer(analysis.sourceFrame(producer), 0),
                        analysis, visiting);
            }
            if (producer instanceof VarInsnNode && opcode == Opcodes.ALOAD) {
                VarInsnNode load = (VarInsnNode) producer;
                Frame<SourceValue> frame = analysis.sourceFrame(load);
                if (frame == null || load.var >= frame.getLocals()) return null;
                AbstractInsnNode localSource = uniqueSource(frame.getLocal(load.var));
                if (localSource == null) return null;
                if (localSource instanceof VarInsnNode
                        && localSource.getOpcode() == Opcodes.ASTORE) {
                    AbstractInsnNode storedValue = uniqueProducer(
                            analysis.sourceFrame(localSource), 0);
                    return provenReferenceDescriptor(storedValue, analysis, visiting);
                }
                return provenReferenceDescriptor(localSource, analysis, visiting);
            }
            return null;
        } finally {
            visiting.remove(producer);
        }
    }

    private static AbstractInsnNode uniqueSource(SourceValue value) {
        return value != null && value.insns.size() == 1
                ? value.insns.iterator().next() : null;
    }

    private static RootInitialization rootInitialization(FieldNode root,
                                                         MethodNode method,
                                                         FieldInsnNode write,
                                                         int instruction,
                                                         MethodAnalysis analysis) {
        boolean staticRoot = isStatic(root);
        if (staticRoot ? !"<clinit>".equals(method.name)
                : !"<init>".equals(method.name)) return null;
        AbstractInsnNode value = uniqueProducer(analysis.sourceFrame(write), 0);
        if (!(value instanceof TypeInsnNode) || value.getOpcode() != Opcodes.ANEWARRAY
                || !"java/lang/Object".equals(((TypeInsnNode) value).desc)) return null;
        Integer arrayLength = intConstant(uniqueProducer(analysis.sourceFrame(value), 0));
        if (staticRoot && (arrayLength == null || arrayLength < 0)) return null;
        VarInsnNode receiver = null;
        if (!staticRoot) {
            AbstractInsnNode receiverProducer = uniqueProducer(analysis.sourceFrame(write), 1);
            if (!(receiverProducer instanceof VarInsnNode)
                    || receiverProducer.getOpcode() != Opcodes.ALOAD
                    || ((VarInsnNode) receiverProducer).var != 0) return null;
            receiver = (VarInsnNode) receiverProducer;
        }
        return new RootInitialization(method, receiver, write, instruction, arrayLength);
    }

    private static FieldInsnNode directRootArrayRead(ClassNode owner, FieldNode root,
                                                     MethodNode method,
                                                     AbstractInsnNode operation,
                                                     MethodAnalysis analysis) {
        boolean write = isArrayStore(operation.getOpcode());
        Frame<SourceValue> frame = analysis.sourceFrame(operation);
        AbstractInsnNode producer = uniqueProducer(frame, write ? 2 : 1);
        if (!(producer instanceof FieldInsnNode)) return null;
        FieldInsnNode field = (FieldInsnNode) producer;
        int readOpcode = isStatic(root) ? Opcodes.GETSTATIC : Opcodes.GETFIELD;
        return field.getOpcode() == readOpcode && field.owner.equals(owner.name)
                && field.name.equals(root.name) && field.desc.equals(root.desc) ? field : null;
    }

    private static BucketInitialization bucketInitialization(FieldNode root,
                                                             MethodNode method,
                                                             AbstractInsnNode operation,
                                                             int instruction,
                                                             FieldInsnNode rootRead,
                                                             MethodAnalysis analysis) {
        boolean staticRoot = isStatic(root);
        if ((staticRoot ? !"<clinit>".equals(method.name) : !"<init>".equals(method.name))
                || operation.getOpcode() != Opcodes.AASTORE) return null;
        Frame<SourceValue> frame = analysis.sourceFrame(operation);
        AbstractInsnNode indexProducer = uniqueProducer(frame, 1);
        Integer bucket = intConstant(indexProducer);
        if (bucket == null) return null;
        VarInsnNode receiver = null;
        if (!staticRoot) {
            AbstractInsnNode receiverProducer = uniqueProducer(
                    analysis.sourceFrame(rootRead), 0);
            if (!(receiverProducer instanceof VarInsnNode)
                    || receiverProducer.getOpcode() != Opcodes.ALOAD
                    || ((VarInsnNode) receiverProducer).var != 0
                    || previousCode(rootRead) != receiverProducer) return null;
            receiver = (VarInsnNode) receiverProducer;
        }
        AbstractInsnNode value = uniqueProducer(frame, 0);
        Integer arrayLength = staticRoot ? allocatedArrayLength(value, analysis) : null;
        String arrayDescriptor = staticRoot ? allocatedArrayDescriptor(value, analysis) : null;
        if (staticRoot && (arrayLength == null || arrayLength < 0)) return null;
        return new BucketInitialization(method, receiver, rootRead,
                indexProducer, operation, instruction, bucket, arrayLength,
                arrayDescriptor);
    }

    private static Integer allocatedArrayLength(AbstractInsnNode allocation,
                                                MethodAnalysis analysis) {
        if (allocation == null) return null;
        if (allocation.getOpcode() == Opcodes.ANEWARRAY
                || allocation.getOpcode() == Opcodes.NEWARRAY) {
            return intConstant(uniqueProducer(analysis.sourceFrame(allocation), 0));
        }
        if (isReflectiveArrayAllocation(allocation)) {
            return intConstant(uniqueProducer(analysis.sourceFrame(allocation), 0));
        }
        return null;
    }

    private static String allocatedArrayDescriptor(AbstractInsnNode allocation,
                                                   MethodAnalysis analysis) {
        if (allocation instanceof TypeInsnNode
                && allocation.getOpcode() == Opcodes.ANEWARRAY) {
            String element = ((TypeInsnNode) allocation).desc;
            return element.startsWith("[") ? "[" + element : "[L" + element + ";";
        }
        if (allocation instanceof IntInsnNode
                && allocation.getOpcode() == Opcodes.NEWARRAY) {
            switch (((IntInsnNode) allocation).operand) {
                case Opcodes.T_BOOLEAN: return "[Z";
                case Opcodes.T_CHAR: return "[C";
                case Opcodes.T_FLOAT: return "[F";
                case Opcodes.T_DOUBLE: return "[D";
                case Opcodes.T_BYTE: return "[B";
                case Opcodes.T_SHORT: return "[S";
                case Opcodes.T_INT: return "[I";
                case Opcodes.T_LONG: return "[J";
                default: return null;
            }
        }
        if (!isReflectiveArrayAllocation(allocation)) return null;
        AbstractInsnNode classProducer = uniqueProducer(
                analysis.sourceFrame(allocation), 1);
        String component = classObjectDescriptor(classProducer, analysis);
        return component == null ? null : "[" + component;
    }

    private static boolean isReflectiveArrayAllocation(AbstractInsnNode instruction) {
        if (!(instruction instanceof MethodInsnNode)) return false;
        MethodInsnNode method = (MethodInsnNode) instruction;
        return method.getOpcode() == Opcodes.INVOKESTATIC
                && "java/lang/reflect/Array".equals(method.owner)
                && "newInstance".equals(method.name)
                && "(Ljava/lang/Class;I)Ljava/lang/Object;".equals(method.desc);
    }

    private static String classObjectDescriptor(AbstractInsnNode producer,
                                                MethodAnalysis analysis) {
        if (producer instanceof LdcInsnNode
                && ((LdcInsnNode) producer).cst instanceof Type) {
            return ((Type) ((LdcInsnNode) producer).cst).getDescriptor();
        }
        if (producer instanceof FieldInsnNode) {
            FieldInsnNode field = (FieldInsnNode) producer;
            if (field.getOpcode() == Opcodes.GETSTATIC && "TYPE".equals(field.name)
                    && "Ljava/lang/Class;".equals(field.desc)) {
                if ("java/lang/Boolean".equals(field.owner)) return "Z";
                if ("java/lang/Character".equals(field.owner)) return "C";
                if ("java/lang/Float".equals(field.owner)) return "F";
                if ("java/lang/Double".equals(field.owner)) return "D";
                if ("java/lang/Byte".equals(field.owner)) return "B";
                if ("java/lang/Short".equals(field.owner)) return "S";
                if ("java/lang/Integer".equals(field.owner)) return "I";
                if ("java/lang/Long".equals(field.owner)) return "J";
            }
        }
        if (producer instanceof MethodInsnNode) {
            MethodInsnNode method = (MethodInsnNode) producer;
            if (method.getOpcode() == Opcodes.INVOKESTATIC
                    && "java/lang/Class".equals(method.owner)
                    && "forName".equals(method.name)
                    && "(Ljava/lang/String;)Ljava/lang/Class;".equals(method.desc)) {
                AbstractInsnNode nameProducer = uniqueProducer(
                        analysis.sourceFrame(method), 0);
                if (!(nameProducer instanceof LdcInsnNode)
                        || !(((LdcInsnNode) nameProducer).cst instanceof String)) return null;
                String name = (String) ((LdcInsnNode) nameProducer).cst;
                if (name.startsWith("[")) return name.replace('.', '/');
                return "L" + name.replace('.', '/') + ";";
            }
        }
        return null;
    }

    private static void applyPlan(ClassNode owner, RootPlan plan, List<String> audit,
                                  Result result) {
        List<SlotPlan> slots = new ArrayList<>(plan.slots.values());
        slots.sort(Comparator.comparingInt((SlotPlan slot) -> slot.key.bucket)
                .thenComparingInt(slot -> slot.key.slot));
        for (SlotPlan slot : slots) {
            int fieldAccess = Opcodes.ACC_PRIVATE
                    | (isStatic(plan.root) ? Opcodes.ACC_STATIC : 0);
            owner.fields.add(new FieldNode(fieldAccess, slot.fieldName,
                    slot.descriptor, null, null));
            result.liftedSlots++;
            boolean referenceTypeFallback = false;
            for (Access access : slot.accesses) {
                rewriteAccess(owner.name, access, slot);
                boolean objectFallback = access.referenceTypeFallback
                        && "Ljava/lang/Object;".equals(slot.descriptor);
                referenceTypeFallback |= objectFallback;
                if (access.write) result.rewrittenWrites++; else result.rewrittenReads++;
                audit.add(tsv(owner.name, access.method.name + access.method.desc,
                        access.instruction, access.write ? "rewrite-write" : "rewrite-read",
                        plan.root.name, access.key.bucket, access.key.slot, slot.fieldName,
                        slot.descriptor, objectFallback
                                ? "proven-fixed-slot;reference-write-type-fallback-object"
                                : "proven-fixed-slot"));
            }
            audit.add(tsv(owner.name, "<class>", -1, "add-field", plan.root.name,
                    slot.key.bucket, slot.key.slot, slot.fieldName, slot.descriptor,
                    referenceTypeFallback
                            ? "structural-name;reference-write-type-fallback-object"
                            : "structural-name"));
        }
        if (plan.rejectedSlots == 0 && plan.slots.size() == plan.accessGroups) {
            removeCoveredStorage(owner, plan, audit, result);
        }
    }

    /**
     * Removes only the storage receiver and index. Allocation/reflection
     * expressions are still evaluated and popped, preserving their observable
     * exceptions and side effects.
     */
    private static void removeCoveredStorage(ClassNode owner, RootPlan plan,
                                             List<String> audit, Result result) {
        for (BucketInitialization initialization : plan.bucketInitializations) {
            MethodNode method = initialization.method;
            if (initialization.receiver != null) {
                method.instructions.remove(initialization.receiver);
            }
            method.instructions.remove(initialization.rootRead);
            method.instructions.remove(initialization.indexProducer);
            method.instructions.set(initialization.operation, new InsnNode(Opcodes.POP));
            result.removedInitializers++;
            audit.add(tsv(owner.name, method.name + method.desc,
                    initialization.instruction, "remove-bucket-storage",
                    plan.root.name, initialization.bucket, "", "", "",
                    "value-evaluation-preserved"));
        }
        for (RootInitialization initialization : plan.rootInitializations) {
            MethodNode method = initialization.method;
            if (initialization.receiver != null) {
                method.instructions.remove(initialization.receiver);
            }
            method.instructions.set(initialization.operation, new InsnNode(Opcodes.POP));
            result.removedInitializers++;
            audit.add(tsv(owner.name, method.name + method.desc,
                    initialization.instruction, "remove-root-storage",
                    plan.root.name, "", "", "", plan.root.desc,
                    "allocation-preserved"));
        }
        if (!hasFieldAccess(owner, plan.root)) {
            owner.fields.remove(plan.root);
            audit.add(tsv(owner.name, "<class>", -1, "remove-root-field",
                    plan.root.name, "", "", "", plan.root.desc,
                    "zero-remaining-references"));
        }
        if (isStatic(plan.root) && hasFieldAccess(owner, plan.root)) {
            throw new IllegalStateException("static root retained after closed rewrite: "
                    + owner.name + "." + plan.root.name);
        }
    }

    private static boolean hasFieldAccess(ClassNode owner, FieldNode target) {
        for (MethodNode method : owner.methods) {
            if (method.instructions == null) continue;
            for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
                 insn = insn.getNext()) {
                if (!(insn instanceof FieldInsnNode)) continue;
                FieldInsnNode field = (FieldInsnNode) insn;
                if (field.owner.equals(owner.name) && field.name.equals(target.name)
                        && field.desc.equals(target.desc)) return true;
            }
        }
        return false;
    }

    private static void rewriteAccess(String owner, Access access, SlotPlan slot) {
        MethodNode method = access.method;
        boolean staticRoot = access.receiver == null;
        AbstractInsnNode redundantCast = null;
        if (!access.write) {
            AbstractInsnNode candidate = nextCode(access.operation);
            if (candidate instanceof TypeInsnNode && candidate.getOpcode() == Opcodes.CHECKCAST
                    && slot.descriptor.equals(descriptor((TypeInsnNode) candidate))) {
                redundantCast = candidate;
            }
        }
        InsnList replacement = new InsnList();
        if (!staticRoot) {
            replacement.add(new VarInsnNode(Opcodes.ALOAD, access.receiver.var));
        }
        if (!access.write) {
            replacement.add(new FieldInsnNode(staticRoot ? Opcodes.GETSTATIC
                            : Opcodes.GETFIELD, owner,
                    slot.fieldName, slot.descriptor));
        }
        AbstractInsnNode prefixStart = staticRoot ? access.rootRead : access.receiver;
        method.instructions.insertBefore(prefixStart, replacement);
        removeCodeRange(method, prefixStart, access.indexProducer);
        if (access.write) {
            method.instructions.set(access.operation, new FieldInsnNode(
                    staticRoot ? Opcodes.PUTSTATIC : Opcodes.PUTFIELD,
                    owner, slot.fieldName, slot.descriptor));
        } else {
            method.instructions.remove(access.operation);
            if (redundantCast != null) method.instructions.remove(redundantCast);
        }
    }

    private static void removeCodeRange(MethodNode method, AbstractInsnNode start,
                                        AbstractInsnNode end) {
        AbstractInsnNode cursor = start;
        while (cursor != null) {
            AbstractInsnNode next = cursor.getNext();
            if (cursor.getOpcode() >= 0 || cursor instanceof FrameNode) {
                method.instructions.remove(cursor);
            }
            if (cursor == end) break;
            cursor = next;
        }
    }

    private static boolean removablePrefix(AbstractInsnNode start, AbstractInsnNode end,
                                           AbstractInsnNode rootRead,
                                           AbstractInsnNode bucketIndex,
                                           AbstractInsnNode outerLoad,
                                           AbstractInsnNode bucketCast,
                                           AbstractInsnNode operation,
                                           boolean write) {
        Set<AbstractInsnNode> structural = Collections.newSetFromMap(
                new IdentityHashMap<AbstractInsnNode, Boolean>());
        Collections.addAll(structural, start, rootRead, bucketIndex, outerLoad,
                bucketCast, end);
        int depth = 0;
        for (AbstractInsnNode cursor = start; cursor != null; cursor = cursor.getNext()) {
            if (cursor.getOpcode() >= 0 && !structural.contains(cursor)) {
                if (!safeResidual(cursor)) return false;
                depth += stackDelta(cursor);
                if (depth < 0) return false;
            }
            if (cursor == end) break;
        }
        // Structural nodes account for the receiver/array/index spine. Residual
        // instructions must not leave a value interleaved with that spine.
        return depth == 0 && (write || end.getNext() != null || operation != null);
    }

    private static boolean safeResidual(AbstractInsnNode insn) {
        int opcode = insn.getOpcode();
        if (intConstant(insn) != null || insn instanceof LdcInsnNode) return true;
        if (insn instanceof VarInsnNode) {
            return opcode >= Opcodes.ILOAD && opcode <= Opcodes.ALOAD;
        }
        if (opcode == Opcodes.POP || opcode == Opcodes.POP2 || opcode == Opcodes.DUP
                || opcode == Opcodes.DUP_X1 || opcode == Opcodes.DUP_X2
                || opcode == Opcodes.DUP2 || opcode == Opcodes.DUP2_X1
                || opcode == Opcodes.DUP2_X2 || opcode == Opcodes.SWAP) return true;
        return opcode >= Opcodes.IADD && opcode <= Opcodes.LXOR
                && opcode != Opcodes.IDIV && opcode != Opcodes.LDIV
                && opcode != Opcodes.IREM && opcode != Opcodes.LREM;
    }

    private static int stackDelta(AbstractInsnNode insn) {
        int opcode = insn.getOpcode();
        if (intConstant(insn) != null) return 1;
        if (insn instanceof LdcInsnNode) {
            Object value = ((LdcInsnNode) insn).cst;
            return value instanceof Long || value instanceof Double ? 2 : 1;
        }
        if (insn instanceof VarInsnNode) {
            return opcode == Opcodes.LLOAD || opcode == Opcodes.DLOAD ? 2 : 1;
        }
        if (opcode == Opcodes.POP) return -1;
        if (opcode == Opcodes.POP2) return -2;
        if (opcode == Opcodes.DUP || opcode == Opcodes.DUP_X1
                || opcode == Opcodes.DUP_X2) return 1;
        if (opcode == Opcodes.DUP2 || opcode == Opcodes.DUP2_X1
                || opcode == Opcodes.DUP2_X2) return 2;
        if (opcode == Opcodes.SWAP) return 0;
        if (opcode >= Opcodes.IADD && opcode <= Opcodes.DREM) {
            return opcode == Opcodes.LADD || opcode == Opcodes.DADD
                    || opcode == Opcodes.LSUB || opcode == Opcodes.DSUB
                    || opcode == Opcodes.LMUL || opcode == Opcodes.DMUL
                    || opcode == Opcodes.LDIV || opcode == Opcodes.DDIV
                    || opcode == Opcodes.LREM || opcode == Opcodes.DREM ? -2 : -1;
        }
        if (opcode >= Opcodes.INEG && opcode <= Opcodes.DNEG) return 0;
        if (opcode >= Opcodes.ISHL && opcode <= Opcodes.LXOR) {
            return opcode == Opcodes.LSHL || opcode == Opcodes.LSHR
                    || opcode == Opcodes.LUSHR ? -1
                    : opcode == Opcodes.LAND || opcode == Opcodes.LOR
                    || opcode == Opcodes.LXOR ? -2 : -1;
        }
        return 0;
    }

    private static String descriptorForAccess(AbstractInsnNode operation,
                                              String bucketDescriptor,
                                              MethodAnalysis analysis) {
        switch (operation.getOpcode()) {
            case Opcodes.BALOAD:
            case Opcodes.BASTORE:
                return "[Z".equals(bucketDescriptor) ? "Z" : "B";
            case Opcodes.CALOAD:
            case Opcodes.CASTORE: return "C";
            case Opcodes.SALOAD:
            case Opcodes.SASTORE: return "S";
            case Opcodes.IALOAD:
            case Opcodes.IASTORE: return "I";
            case Opcodes.LALOAD:
            case Opcodes.LASTORE: return "J";
            case Opcodes.FALOAD:
            case Opcodes.FASTORE: return "F";
            case Opcodes.DALOAD:
            case Opcodes.DASTORE: return "D";
            case Opcodes.AALOAD:
                AbstractInsnNode cast = nextCode(operation);
                return cast instanceof TypeInsnNode && cast.getOpcode() == Opcodes.CHECKCAST
                        ? descriptor((TypeInsnNode) cast) : "Ljava/lang/Object;";
            case Opcodes.AASTORE:
                Frame<BasicValue> frame = analysis.basicFrame(operation);
                if (frame == null || frame.getStackSize() == 0) return "Ljava/lang/Object;";
                BasicValue value = frame.getStack(frame.getStackSize() - 1);
                Type type = value == null ? null : value.getType();
                return type == null || type.getSort() < Type.ARRAY
                        ? "Ljava/lang/Object;" : type.getDescriptor();
            default:
                return null;
        }
    }

    private static String unifyDescriptor(List<Access> accesses) {
        String primitive = null;
        Set<String> references = new LinkedHashSet<>();
        for (Access access : accesses) {
            String descriptor = access.descriptor;
            if (descriptor == null) return null;
            boolean reference = descriptor.startsWith("L") || descriptor.startsWith("[");
            if (!reference) {
                if (!references.isEmpty() || primitive != null && !primitive.equals(descriptor)) {
                    return null;
                }
                primitive = descriptor;
            } else {
                if (primitive != null) return null;
                if (!"Ljava/lang/Object;".equals(descriptor)) references.add(descriptor);
            }
        }
        if (primitive != null) return primitive;
        if (references.size() == 1) return references.iterator().next();
        return references.isEmpty() ? "Ljava/lang/Object;" : null;
    }

    private static boolean opcodeMatchesArray(int opcode, String descriptor) {
        if (descriptor.length() < 2 || descriptor.charAt(0) != '[') return false;
        char element = descriptor.charAt(1);
        switch (opcode) {
            case Opcodes.AALOAD:
            case Opcodes.AASTORE: return element == 'L' || element == '[';
            case Opcodes.BALOAD:
            case Opcodes.BASTORE: return element == 'B' || element == 'Z';
            case Opcodes.CALOAD:
            case Opcodes.CASTORE: return element == 'C';
            case Opcodes.SALOAD:
            case Opcodes.SASTORE: return element == 'S';
            case Opcodes.IALOAD:
            case Opcodes.IASTORE: return element == 'I';
            case Opcodes.LALOAD:
            case Opcodes.LASTORE: return element == 'J';
            case Opcodes.FALOAD:
            case Opcodes.FASTORE: return element == 'F';
            case Opcodes.DALOAD:
            case Opcodes.DASTORE: return element == 'D';
            default: return false;
        }
    }

    private static boolean isArrayLoad(int opcode) {
        return opcode >= Opcodes.IALOAD && opcode <= Opcodes.SALOAD;
    }

    private static boolean isArrayStore(int opcode) {
        return opcode >= Opcodes.IASTORE && opcode <= Opcodes.SASTORE;
    }

    private static AbstractInsnNode uniqueProducer(Frame<SourceValue> frame, int fromTop) {
        if (frame == null || frame.getStackSize() <= fromTop) return null;
        SourceValue value = frame.getStack(frame.getStackSize() - 1 - fromTop);
        return value != null && value.insns.size() == 1 ? value.insns.iterator().next() : null;
    }

    private static Integer intConstant(AbstractInsnNode insn) {
        if (insn == null) return null;
        int opcode = insn.getOpcode();
        if (opcode >= Opcodes.ICONST_M1 && opcode <= Opcodes.ICONST_5) {
            return opcode - Opcodes.ICONST_0;
        }
        if (insn instanceof IntInsnNode
                && (opcode == Opcodes.BIPUSH || opcode == Opcodes.SIPUSH)) {
            return ((IntInsnNode) insn).operand;
        }
        if (insn instanceof LdcInsnNode && ((LdcInsnNode) insn).cst instanceof Integer) {
            return (Integer) ((LdcInsnNode) insn).cst;
        }
        return null;
    }

    private static boolean ordered(MethodNode method, AbstractInsnNode... nodes) {
        Map<AbstractInsnNode, Integer> indexes = new IdentityHashMap<>();
        int index = 0;
        for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
             insn = insn.getNext(), index++) indexes.put(insn, index);
        int previous = -1;
        for (AbstractInsnNode node : nodes) {
            Integer current = indexes.get(node);
            if (current == null || current <= previous) return false;
            previous = current;
        }
        return true;
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

    private static String descriptor(TypeInsnNode cast) {
        return cast.desc.startsWith("[") ? cast.desc : "L" + cast.desc + ";";
    }

    private static String structuralName(String root, int bucket, int slot) {
        String clean = root.replaceAll("[^A-Za-z0-9_$]", "_");
        return "slot_" + clean + "_" + bucket + "_" + slot;
    }

    private static String uniqueFieldName(ClassNode owner, String base) {
        Set<String> names = new HashSet<>();
        for (FieldNode field : owner.fields) names.add(field.name);
        if (!names.contains(base)) return base;
        int suffix = 2;
        while (names.contains(base + "_" + suffix)) suffix++;
        return base + "_" + suffix;
    }

    private static MethodNode findMethod(ClassNode owner, AbstractInsnNode target) {
        for (MethodNode method : owner.methods) {
            if (method.instructions != null && method.instructions.contains(target)) return method;
        }
        return null;
    }

    private static byte[] writeAndVerify(ClassNode owner) throws Exception {
        ClassWriter writer = new ClassWriter(ClassWriter.COMPUTE_FRAMES) {
            @Override protected String getCommonSuperClass(String left, String right) {
                return "java/lang/Object";
            }
        };
        owner.accept(writer);
        byte[] bytes = writer.toByteArray();
        ClassNode verified = new ClassNode(Opcodes.ASM9);
        new ClassReader(bytes).accept(verified, 0);
        for (MethodNode method : verified.methods) {
            if (method.instructions != null && method.instructions.size() > 0) {
                new Analyzer<>(new BasicVerifier()).analyze(verified.name, method);
            }
        }
        return bytes;
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

    private static void writeArchive(List<EntryBytes> entries, Map<String, byte[]> replacements,
                                     Path output, ArchiveResult result) throws IOException {
        try (ZipOutputStream out = new ZipOutputStream(Files.newOutputStream(output))) {
            for (EntryBytes entry : entries) {
                if (isSignatureEntry(entry.name) && !replacements.isEmpty()) continue;
                byte[] bytes = entry.bytes;
                if (entry.name.endsWith(".class")) {
                    String name = entry.name.substring(0, entry.name.length() - 6);
                    byte[] replacement = replacements.get(name);
                    if (replacement != null) bytes = replacement;
                }
                ZipEntry written = new ZipEntry(entry.name);
                if (entry.time >= 0) written.setTime(entry.time);
                out.putNextEntry(written);
                out.write(bytes);
                out.closeEntry();
            }
        }
    }

    private static void verifyArchive(Path archive, ArchiveResult result) throws IOException {
        try (ZipInputStream in = new ZipInputStream(Files.newInputStream(archive))) {
            ZipEntry entry;
            while ((entry = in.getNextEntry()) != null) {
                byte[] bytes = readAll(in);
                if (!entry.getName().endsWith(".class")) continue;
                result.outputClasses++;
                try {
                    ClassNode owner = new ClassNode(Opcodes.ASM9);
                    new ClassReader(bytes).accept(owner, 0);
                    for (MethodNode method : owner.methods) {
                        if (method.instructions != null && method.instructions.size() > 0) {
                            new Analyzer<>(new BasicVerifier()).analyze(owner.name, method);
                        }
                    }
                } catch (Throwable failure) {
                    result.outputVerificationErrors++;
                }
            }
        }
    }

    private static byte[] readAll(InputStream input) throws IOException {
        ByteArrayOutputStream output = new ByteArrayOutputStream();
        byte[] buffer = new byte[8192];
        int read;
        while ((read = input.read(buffer)) >= 0) output.write(buffer, 0, read);
        return output.toByteArray();
    }

    private static boolean isSignatureEntry(String name) {
        String upper = name.replace('\\', '/').toUpperCase(Locale.ROOT);
        if (!upper.startsWith("META-INF/")) return false;
        String leaf = upper.substring("META-INF/".length());
        return leaf.startsWith("SIG-") || leaf.endsWith(".SF") || leaf.endsWith(".RSA")
                || leaf.endsWith(".DSA") || leaf.endsWith(".EC");
    }

    private static String tsv(Object... values) {
        StringBuilder result = new StringBuilder();
        for (int index = 0; index < values.length; index++) {
            if (index != 0) result.append('\t');
            if (values[index] != null) result.append(values[index]);
        }
        return result.toString();
    }

    private static String shortReason(Throwable failure) {
        String result = failure.getClass().getSimpleName() + ":" + failure.getMessage();
        result = result.replace('\t', ' ').replace('\r', ' ').replace('\n', ' ');
        return result.substring(0, Math.min(180, result.length()));
    }

    static class Result {
        boolean changed;
        int candidateRoots;
        int rejectedRoots;
        int liftedSlots;
        int rewrittenReads;
        int rewrittenWrites;
        int removedInitializers;
        int removedDeadKeyLocals;
    }

    static final class ArchiveResult extends Result {
        int classes;
        int parseErrors;
        int changedClasses;
        int rollbackClasses;
        int outputClasses;
        int outputVerificationErrors;
    }

    private static final class EntryBytes {
        final String name;
        final long time;
        final byte[] bytes;

        EntryBytes(ZipEntry entry, byte[] bytes) {
            this.name = entry.getName();
            this.time = entry.getTime();
            this.bytes = bytes;
        }
    }

    private static final class MethodAnalysis {
        final MethodNode method;
        final Map<AbstractInsnNode, Integer> indexes = new IdentityHashMap<>();
        final Frame<SourceValue>[] sourceFrames;
        final Frame<BasicValue>[] basicFrames;

        private MethodAnalysis(MethodNode method, Frame<SourceValue>[] sourceFrames,
                               Frame<BasicValue>[] basicFrames) {
            this.method = method;
            this.sourceFrames = sourceFrames;
            this.basicFrames = basicFrames;
            int index = 0;
            for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
                 insn = insn.getNext(), index++) indexes.put(insn, index);
        }

        static MethodAnalysis analyze(String owner, MethodNode method) throws Exception {
            return new MethodAnalysis(method,
                    new Analyzer<SourceValue>(new SourceInterpreter()).analyze(owner, method),
                    new Analyzer<BasicValue>(new BasicInterpreter()).analyze(owner, method));
        }

        Frame<SourceValue> sourceFrame(AbstractInsnNode insn) {
            Integer index = indexes.get(insn);
            return index == null || index < 0 || index >= sourceFrames.length
                    ? null : sourceFrames[index];
        }

        Frame<BasicValue> basicFrame(AbstractInsnNode insn) {
            Integer index = indexes.get(insn);
            return index == null || index < 0 || index >= basicFrames.length
                    ? null : basicFrames[index];
        }
    }

    private static final class SlotKey {
        final String root;
        final int bucket;
        final int slot;
        final String bucketDescriptor;

        SlotKey(String root, int bucket, int slot, String bucketDescriptor) {
            this.root = root;
            this.bucket = bucket;
            this.slot = slot;
            this.bucketDescriptor = bucketDescriptor;
        }

        @Override public boolean equals(Object other) {
            if (!(other instanceof SlotKey)) return false;
            SlotKey key = (SlotKey) other;
            return bucket == key.bucket && slot == key.slot && root.equals(key.root)
                    && bucketDescriptor.equals(key.bucketDescriptor);
        }

        @Override public int hashCode() {
            int result = root.hashCode();
            result = 31 * result + bucket;
            result = 31 * result + slot;
            return 31 * result + bucketDescriptor.hashCode();
        }
    }

    private static final class Access {
        final MethodNode method;
        final AbstractInsnNode operation;
        final int instruction;
        final VarInsnNode receiver;
        final FieldInsnNode rootRead;
        final AbstractInsnNode indexProducer;
        final SlotKey key;
        final String descriptor;
        final boolean write;
        final boolean referenceTypeFallback;

        Access(MethodNode method, AbstractInsnNode operation, int instruction,
               VarInsnNode receiver, FieldInsnNode rootRead,
               AbstractInsnNode indexProducer, SlotKey key, String descriptor,
               boolean write, boolean referenceTypeFallback) {
            this.method = method;
            this.operation = operation;
            this.instruction = instruction;
            this.receiver = receiver;
            this.rootRead = rootRead;
            this.indexProducer = indexProducer;
            this.key = key;
            this.descriptor = descriptor;
            this.write = write;
            this.referenceTypeFallback = referenceTypeFallback;
        }
    }

    private static final class SlotPlan {
        final SlotKey key;
        final String fieldName;
        final String descriptor;
        final List<Access> accesses;

        SlotPlan(SlotKey key, String fieldName, String descriptor,
                 List<Access> accesses) {
            this.key = key;
            this.fieldName = fieldName;
            this.descriptor = descriptor;
            this.accesses = accesses;
        }
    }

    private static final class RootInitialization {
        final MethodNode method;
        final VarInsnNode receiver;
        final FieldInsnNode operation;
        final int instruction;
        final Integer arrayLength;

        RootInitialization(MethodNode method, VarInsnNode receiver,
                           FieldInsnNode operation, int instruction,
                           Integer arrayLength) {
            this.method = method;
            this.receiver = receiver;
            this.operation = operation;
            this.instruction = instruction;
            this.arrayLength = arrayLength;
        }
    }

    private static final class BucketInitialization {
        final MethodNode method;
        final VarInsnNode receiver;
        final FieldInsnNode rootRead;
        final AbstractInsnNode indexProducer;
        final AbstractInsnNode operation;
        final int instruction;
        final int bucket;
        final Integer arrayLength;
        final String arrayDescriptor;

        BucketInitialization(MethodNode method, VarInsnNode receiver,
                             FieldInsnNode rootRead,
                             AbstractInsnNode indexProducer,
                             AbstractInsnNode operation, int instruction,
                             int bucket, Integer arrayLength,
                             String arrayDescriptor) {
            this.method = method;
            this.receiver = receiver;
            this.rootRead = rootRead;
            this.indexProducer = indexProducer;
            this.operation = operation;
            this.instruction = instruction;
            this.bucket = bucket;
            this.arrayLength = arrayLength;
            this.arrayDescriptor = arrayDescriptor;
        }
    }

    private static final class RootPlan {
        final FieldNode root;
        final List<Access> accesses = new ArrayList<>();
        final Map<SlotKey, SlotPlan> slots = new LinkedHashMap<>();
        final List<RootInitialization> rootInitializations = new ArrayList<>();
        final List<BucketInitialization> bucketInitializations = new ArrayList<>();
        boolean accepted;
        int rejectedSlots;
        int accessGroups;

        RootPlan(FieldNode root) {
            this.root = root;
        }
    }
}
