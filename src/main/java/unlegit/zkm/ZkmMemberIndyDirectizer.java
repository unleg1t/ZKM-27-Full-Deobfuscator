package unlegit.zkm;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.AtomicMoveNotSupportedException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.StandardCopyOption;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
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

import org.objectweb.asm.ClassReader;
import org.objectweb.asm.ClassWriter;
import org.objectweb.asm.Handle;
import org.objectweb.asm.Opcodes;
import org.objectweb.asm.Type;
import org.objectweb.asm.tree.AbstractInsnNode;
import org.objectweb.asm.tree.ClassNode;
import org.objectweb.asm.tree.FrameNode;
import org.objectweb.asm.tree.IincInsnNode;
import org.objectweb.asm.tree.InsnList;
import org.objectweb.asm.tree.InvokeDynamicInsnNode;
import org.objectweb.asm.tree.LabelNode;
import org.objectweb.asm.tree.LdcInsnNode;
import org.objectweb.asm.tree.LineNumberNode;
import org.objectweb.asm.tree.LocalVariableNode;
import org.objectweb.asm.tree.MethodInsnNode;
import org.objectweb.asm.tree.MethodNode;
import org.objectweb.asm.tree.TypeInsnNode;
import org.objectweb.asm.tree.VarInsnNode;
import org.objectweb.asm.tree.analysis.Analyzer;
import org.objectweb.asm.tree.analysis.BasicVerifier;
import org.objectweb.asm.tree.analysis.Frame;
import org.objectweb.asm.tree.analysis.SourceInterpreter;
import org.objectweb.asm.tree.analysis.SourceValue;
import org.objectweb.asm.util.CheckClassAdapter;

/**
 * Replaces proven same-owner ZKM member invokedynamic sites with direct method
 * instructions. Input classes are parsed as bytes and are never defined,
 * initialized, or executed.
 */
public final class ZkmMemberIndyDirectizer {
    private static final String BSM_DESC = "(Ljava/lang/invoke/MethodHandles$Lookup;"
            + "Ljava/lang/String;Ljava/lang/invoke/MethodType;)"
            + "Ljava/lang/invoke/CallSite;";

    private ZkmMemberIndyDirectizer() {
    }

    public static void main(String[] args) throws Exception {
        if (args.length != 4 && args.length != 5) {
            System.err.println("usage: ZkmMemberIndyDirectizer <input.jar> <report-dir>"
                    + " <class-map.tsv> <method-map.tsv> [output.jar]");
            System.exit(2);
        }
        directize(Paths.get(args[0]), Paths.get(args[1]), Paths.get(args[2]),
                Paths.get(args[3]), args.length == 5 ? Paths.get(args[4]) : null);
    }

    static Summary directize(Path input, Path reportDirectory, Path classMap,
                             Path methodMap, Path output) throws Exception {
        return directize(input, reportDirectory, classMap, methodMap, output,
                ZkmMemberProjection.load(classMap, methodMap), "mapped");
    }

    static Summary directizeIdentity(Path input, Path reportDirectory,
                                     Path output) throws Exception {
        return directize(input, reportDirectory, null, null, output,
                ZkmMemberProjection.identity(), "identity-raw-symbols");
    }

    private static Summary directize(Path input, Path reportDirectory,
                                     Path classMap, Path methodMap, Path output,
                                     ZkmMemberProjection.Mapping mapping,
                                     String projectionMode) throws Exception {
        validatePaths(input, output);
        Files.createDirectories(reportDirectory);
        List<EntryBytes> entries = readEntries(input);
        Map<String, byte[]> originalBytes = classBytes(entries);
        Map<String, ClassNode> classes = readClasses(originalBytes);
        InterfaceIndex interfaces = new InterfaceIndex(classes);
        Summary summary = new Summary();
        summary.parsedClasses = classes.size();
        summary.outputRequested = output != null;
        List<SiteResult> results = new ArrayList<>();
        List<String> verifierRows = new ArrayList<>();
        verifierRows.add("scope\tclass\tstatus\treason");
        Map<String, byte[]> replacements = new LinkedHashMap<>();

        for (ClassNode owner : new ArrayList<>(classes.values())) {
            List<SiteLocation> locations = memberSites(owner);
            if (locations.isEmpty()) continue;
            summary.siteClasses++;
            ZkmMemberIndyDeobfuscator.ResolverModel model = null;
            String modelFailure = null;
            try {
                model = ZkmMemberIndyDeobfuscator.ResolverModel.build(owner);
                summary.resolverModels++;
            } catch (Throwable failure) {
                summary.modelFailures++;
                modelFailure = "resolver-model:" + shortReason(failure);
            }

            Map<MethodNode, MethodAnalysis> analyses = analyzeMethods(owner, locations);
            Set<AbstractInsnNode> claimedTailConstants = identitySet();
            List<SiteResult> ownerResults = new ArrayList<>();
            List<SiteResult> planned = new ArrayList<>();
            for (SiteLocation location : locations) {
                summary.sites++;
                SiteResult result = plan(owner, location, model, modelFailure,
                        analyses.get(location.method), mapping, classes, interfaces,
                        claimedTailConstants, summary);
                ownerResults.add(result);
                if (result.plan != null) planned.add(result);
            }

            if (!planned.isEmpty()) {
                try {
                    for (SiteResult result : planned) {
                        apply(result.plan);
                    }
                    byte[] candidate = writeClass(owner);
                    verifyClass(candidate);
                    replacements.put(owner.name, candidate);
                    summary.changedClasses++;
                    summary.rewrittenSites += planned.size();
                    for (SiteResult result : planned) result.action = "REWRITE";
                    verifierRows.add(tsv("class-transaction", owner.name, "PASS", ""));
                } catch (Throwable failure) {
                    String reason = "class-rollback:" + shortReason(failure);
                    summary.classRollbacks++;
                    summary.rollbackSites += planned.size();
                    classes.put(owner.name, readClass(originalBytes.get(owner.name)));
                    for (SiteResult result : planned) {
                        result.action = "ROLLBACK";
                        result.reason = appendReason(result.reason, reason);
                    }
                    verifierRows.add(tsv("class-transaction", owner.name,
                            "ROLLBACK", reason));
                }
            }
            results.addAll(ownerResults);
        }

        summary.externalClassResourcesRead = interfaces.externalResourcesRead;
        summary.skippedSites = summary.sites - summary.rewrittenSites;
        summary.remainingMemberSites = summary.skippedSites;
        ZkmMemberProjection.Audit projectionAudit = mapping.audit();

        if (output != null) {
            try {
                writeVerifiedArchive(entries, replacements, output, summary, verifierRows);
            } catch (Throwable failure) {
                summary.outputVerificationErrors++;
                verifierRows.add(tsv("archive", "<archive>", "FAIL",
                        "write:" + shortReason(failure)));
            }
        }
        writeReports(input, reportDirectory, classMap, methodMap, output, summary,
                projectionAudit, results, verifierRows, projectionMode);
        System.out.println("sites=" + summary.sites
                + " planned=" + summary.plannedSites
                + " rewritten=" + summary.rewrittenSites
                + " remaining=" + summary.remainingMemberSites
                + " rollbacks=" + summary.classRollbacks
                + " output_committed=" + summary.outputCommitted
                + " gate=" + gate(summary));
        return summary;
    }

    private static SiteResult plan(
            ClassNode owner, SiteLocation location,
            ZkmMemberIndyDeobfuscator.ResolverModel model, String modelFailure,
            MethodAnalysis analysis, ZkmMemberProjection.Mapping mapping,
            Map<String, ClassNode> classes, InterfaceIndex interfaces,
            Set<AbstractInsnNode> claimedTailConstants, Summary summary) {
        SiteResult result = new SiteResult(owner.name, location.method,
                location.indy, location.index);
        if (model == null) return result.skip(modelFailure);
        if (analysis == null || analysis.failure != null) {
            summary.sourceFailures++;
            return result.skip(analysis == null ? "missing-method-analysis"
                    : analysis.failure);
        }

        TailProof tail = proveTail(location.method, location.indy,
                analysis.frames, analysis.indexes);
        if (!tail.proven) {
            summary.sourceFailures++;
            return result.skip(tail.reason);
        }
        summary.sourceProvenSites++;
        result.firstKey = tail.first;
        result.secondKey = tail.second;
        if (!claimedTailConstants.add(tail.firstNode)
                || !claimedTailConstants.add(tail.secondNode)) {
            summary.sourceFailures++;
            return result.skip("shared-tail-constant-producer");
        }

        ZkmMemberIndyDeobfuscator.MemberTarget raw;
        try {
            raw = model.resolve(location.indy.name, tail.first, tail.second);
            summary.decodedSites++;
            result.raw = raw;
        } catch (Throwable failure) {
            summary.decodeFailures++;
            return result.skip("decode:" + shortReason(failure));
        }

        ZkmMemberProjection.ProjectedTarget projected;
        try {
            projected = mapping.project(raw, classes);
            result.projected = projected;
        } catch (Throwable failure) {
            summary.projectionFailures++;
            return result.skip("projection:" + shortReason(failure));
        }
        if (!projected.isResolved()) {
            summary.projectionFailures++;
            return result.skip("projection-" + projected.status + ":"
                    + projected.evidence);
        }
        summary.projectedSites++;

        String stripped;
        Adaptation adaptation;
        try {
            stripped = stripTrailingKeys(location.indy.desc);
            adaptation = Adaptation.between(stripped,
                    handleDescriptor(projected.kind, projected.owner, projected.desc));
        } catch (Throwable failure) {
            summary.conversionFailures++;
            return result.skip("conversion:" + shortReason(failure));
        }
        result.strippedDescriptor = stripped;
        result.adaptation = adaptation;
        if (!adaptation.compatible) {
            summary.conversionFailures++;
            return result.skip("conversion:" + adaptation.reason);
        }
        summary.compatibleSites++;
        for (Type cast : adaptation.argumentCasts) {
            if (cast == null) summary.argumentExact++;
            else summary.argumentReferenceCasts++;
        }
        if (adaptation.returnCast == null) summary.returnExact++;
        else summary.returnReferenceCasts++;

        InterfaceInfo interfaceInfo = interfaces.resolve(projected.owner);
        if (!interfaceInfo.resolved) {
            summary.interfaceFailures++;
            return result.skip("interface-owner:" + interfaceInfo.reason);
        }
        try {
            int opcode = invocationOpcode(projected.kind, interfaceInfo.isInterface);
            result.plan = new RewritePlan(location.method, location.indy,
                    tail.firstNode, tail.secondNode, adaptation, opcode,
                    projected.owner, projected.name, projected.desc,
                    interfaceInfo.isInterface);
            result.action = "PLANNED";
            result.reason = "";
            summary.plannedSites++;
            countKind(summary, projected.kind);
            return result;
        } catch (Throwable failure) {
            summary.kindFailures++;
            return result.skip("kind:" + shortReason(failure));
        }
    }

    private static Map<MethodNode, MethodAnalysis> analyzeMethods(
            ClassNode owner, List<SiteLocation> sites) {
        Map<MethodNode, MethodAnalysis> result = new IdentityHashMap<>();
        for (SiteLocation site : sites) {
            if (result.containsKey(site.method)) continue;
            Map<AbstractInsnNode, Integer> indexes = instructionIndexes(site.method);
            try {
                Analyzer<SourceValue> analyzer = new Analyzer<>(new SourceInterpreter());
                Frame<SourceValue>[] frames = analyzer.analyze(owner.name, site.method);
                result.put(site.method, new MethodAnalysis(indexes, frames, null));
            } catch (Throwable failure) {
                result.put(site.method, new MethodAnalysis(indexes, null,
                        "source-analysis:" + shortReason(failure)));
            }
        }
        return result;
    }

    static TailProof proveTail(String owner, MethodNode method,
                               InvokeDynamicInsnNode indy) {
        Map<AbstractInsnNode, Integer> indexes = instructionIndexes(method);
        try {
            Analyzer<SourceValue> analyzer = new Analyzer<>(new SourceInterpreter());
            return proveTail(method, indy, analyzer.analyze(owner, method), indexes);
        } catch (Throwable failure) {
            return TailProof.failure("source-analysis:" + shortReason(failure));
        }
    }

    private static TailProof proveTail(MethodNode method, InvokeDynamicInsnNode indy,
                                       Frame<SourceValue>[] frames,
                                       Map<AbstractInsnNode, Integer> indexes) {
        AbstractInsnNode secondNode = previousCode(indy);
        AbstractInsnNode firstNode = previousCode(secondNode);
        Long first = longConstant(firstNode);
        Long second = longConstant(secondNode);
        if (first == null || second == null) {
            return TailProof.failure("non-adjacent-long-constants");
        }
        Integer index = indexes.get(indy);
        if (index == null || frames == null || index < 0 || index >= frames.length) {
            return TailProof.failure("missing-indy-frame");
        }
        Frame<SourceValue> frame = frames[index];
        if (frame == null || frame.getStackSize() < 2) {
            return TailProof.failure("missing-tail-stack-values");
        }
        SourceValue firstValue = frame.getStack(frame.getStackSize() - 2);
        SourceValue secondValue = frame.getStack(frame.getStackSize() - 1);
        if (firstValue == null || firstValue.getSize() != 2
                || firstValue.insns.size() != 1
                || !firstValue.insns.contains(firstNode)) {
            return TailProof.failure("non-unique-first-tail-producer");
        }
        if (secondValue == null || secondValue.getSize() != 2
                || secondValue.insns.size() != 1
                || !secondValue.insns.contains(secondNode)) {
            return TailProof.failure("non-unique-second-tail-producer");
        }
        return TailProof.proven(firstNode, secondNode, first, second);
    }

    static Adaptation adaptation(String callSiteDescriptor, String kind,
                                 String owner, String targetDescriptor) {
        return Adaptation.between(callSiteDescriptor,
                handleDescriptor(kind, owner, targetDescriptor));
    }

    static void rewriteForTest(MethodNode method, InvokeDynamicInsnNode indy,
                               AbstractInsnNode firstKey, AbstractInsnNode secondKey,
                               Adaptation adaptation, int opcode, String owner,
                               String name, String descriptor, boolean isInterface) {
        apply(new RewritePlan(method, indy, firstKey, secondKey, adaptation,
                opcode, owner, name, descriptor, isInterface));
    }

    private static void apply(RewritePlan plan) {
        MethodNode method = plan.method;
        Type[] sources = plan.adaptation.sourceArguments;
        InsnList replacement = new InsnList();
        if (plan.adaptation.hasArgumentCasts()) {
            ensureMaxLocals(method);
            int[] locals = new int[sources.length];
            for (int i = sources.length - 1; i >= 0; i--) {
                locals[i] = method.maxLocals;
                method.maxLocals += sources[i].getSize();
                replacement.add(new VarInsnNode(
                        sources[i].getOpcode(Opcodes.ISTORE), locals[i]));
            }
            for (int i = 0; i < sources.length; i++) {
                replacement.add(new VarInsnNode(
                        sources[i].getOpcode(Opcodes.ILOAD), locals[i]));
                Type cast = plan.adaptation.argumentCasts[i];
                if (cast != null) replacement.add(checkcast(cast));
            }
        }
        replacement.add(new MethodInsnNode(plan.opcode, plan.owner, plan.name,
                plan.descriptor, plan.isInterface));
        if (plan.adaptation.returnCast != null) {
            replacement.add(checkcast(plan.adaptation.returnCast));
        }
        method.instructions.insertBefore(plan.indy, replacement);
        method.instructions.remove(plan.firstKey);
        method.instructions.remove(plan.secondKey);
        method.instructions.remove(plan.indy);
    }

    private static TypeInsnNode checkcast(Type type) {
        String operand = type.getSort() == Type.ARRAY
                ? type.getDescriptor() : type.getInternalName();
        return new TypeInsnNode(Opcodes.CHECKCAST, operand);
    }

    private static void ensureMaxLocals(MethodNode method) {
        int required = (method.access & Opcodes.ACC_STATIC) == 0 ? 1 : 0;
        for (Type argument : Type.getArgumentTypes(method.desc)) required += argument.getSize();
        for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
             insn = insn.getNext()) {
            if (insn instanceof VarInsnNode) {
                VarInsnNode variable = (VarInsnNode) insn;
                int size = variable.getOpcode() == Opcodes.LLOAD
                        || variable.getOpcode() == Opcodes.LSTORE
                        || variable.getOpcode() == Opcodes.DLOAD
                        || variable.getOpcode() == Opcodes.DSTORE ? 2 : 1;
                required = Math.max(required, variable.var + size);
            } else if (insn instanceof IincInsnNode) {
                required = Math.max(required, ((IincInsnNode) insn).var + 1);
            }
        }
        if (method.localVariables != null) {
            for (LocalVariableNode local : method.localVariables) {
                required = Math.max(required,
                        local.index + Type.getType(local.desc).getSize());
            }
        }
        method.maxLocals = Math.max(method.maxLocals, required);
    }

    private static int invocationOpcode(String kind, boolean isInterface) {
        if ("INVOKESTATIC".equals(kind)) return Opcodes.INVOKESTATIC;
        if ("INVOKESPECIAL".equals(kind)) return Opcodes.INVOKESPECIAL;
        if ("INVOKEVIRTUAL".equals(kind)) {
            return isInterface ? Opcodes.INVOKEINTERFACE : Opcodes.INVOKEVIRTUAL;
        }
        throw new IllegalArgumentException("unsupported-member-kind=" + kind);
    }

    private static String handleDescriptor(String kind, String owner,
                                           String descriptor) {
        if ("INVOKESTATIC".equals(kind)) return descriptor;
        if (!"INVOKEVIRTUAL".equals(kind) && !"INVOKESPECIAL".equals(kind)) {
            throw new IllegalArgumentException("unsupported-member-kind=" + kind);
        }
        Type method = Type.getMethodType(descriptor);
        Type[] declared = method.getArgumentTypes();
        Type[] arguments = new Type[declared.length + 1];
        arguments[0] = Type.getObjectType(owner);
        System.arraycopy(declared, 0, arguments, 1, declared.length);
        return Type.getMethodDescriptor(method.getReturnType(), arguments);
    }

    private static String stripTrailingKeys(String descriptor) {
        Type method = Type.getMethodType(descriptor);
        Type[] arguments = method.getArgumentTypes();
        if (arguments.length < 2
                || !Type.LONG_TYPE.equals(arguments[arguments.length - 2])
                || !Type.LONG_TYPE.equals(arguments[arguments.length - 1])) {
            throw new IllegalArgumentException("descriptor-without-trailing-JJ="
                    + descriptor);
        }
        return Type.getMethodDescriptor(method.getReturnType(),
                Arrays.copyOf(arguments, arguments.length - 2));
    }

    private static List<SiteLocation> memberSites(ClassNode owner) {
        List<SiteLocation> result = new ArrayList<>();
        for (MethodNode method : owner.methods) {
            int index = 0;
            for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
                 insn = insn.getNext(), index++) {
                if (insn instanceof InvokeDynamicInsnNode
                        && isMemberSite(owner.name, (InvokeDynamicInsnNode) insn)) {
                    result.add(new SiteLocation(method,
                            (InvokeDynamicInsnNode) insn, index));
                }
            }
        }
        return result;
    }

    private static boolean isMemberSite(String owner, InvokeDynamicInsnNode indy) {
        Handle bootstrap = indy.bsm;
        Type[] arguments = Type.getArgumentTypes(indy.desc);
        return arguments.length >= 2
                && Type.LONG_TYPE.equals(arguments[arguments.length - 2])
                && Type.LONG_TYPE.equals(arguments[arguments.length - 1])
                && bootstrap != null && bootstrap.getTag() == Opcodes.H_INVOKESTATIC
                && owner.equals(bootstrap.getOwner())
                && BSM_DESC.equals(bootstrap.getDesc())
                && (indy.bsmArgs == null || indy.bsmArgs.length == 0);
    }

    private static void validatePaths(Path input, Path output) {
        if (output == null) return;
        if (input.toAbsolutePath().normalize().equals(
                output.toAbsolutePath().normalize())) {
            throw new IllegalArgumentException("output must not replace input");
        }
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

    private static byte[] writeClass(ClassNode owner) {
        ClassWriter writer = new ClassWriter(ClassWriter.COMPUTE_MAXS);
        owner.accept(writer);
        return writer.toByteArray();
    }

    private static void verifyClass(byte[] bytes) throws Exception {
        ClassReader reader = new ClassReader(bytes);
        reader.accept(new CheckClassAdapter(new ClassWriter(0), false), 0);
        ClassNode owner = new ClassNode(Opcodes.ASM9);
        reader.accept(owner, 0);
        for (MethodNode method : owner.methods) {
            if (method.instructions != null && method.instructions.size() != 0) {
                new Analyzer<>(new BasicVerifier()).analyze(owner.name, method);
            }
        }
    }

    private static void writeVerifiedArchive(
            List<EntryBytes> entries, Map<String, byte[]> replacements, Path output,
            Summary summary, List<String> verifierRows) throws IOException {
        Path parent = output.toAbsolutePath().getParent();
        if (parent == null) parent = Paths.get(".").toAbsolutePath();
        Files.createDirectories(parent);
        Path temporary = Files.createTempFile(parent,
                output.getFileName().toString() + ".", ".tmp");
        summary.temporaryOutput = temporary.toAbsolutePath().toString();
        try {
            writeArchive(entries, replacements, temporary, summary);
            ArchiveVerification verification = verifyArchive(temporary, verifierRows);
            summary.outputClasses = verification.classes;
            summary.outputVerificationErrors = verification.errors;
            summary.outputRemainingMemberSites = verification.memberSites;
            if (verification.classes != summary.parsedClasses) {
                summary.outputVerificationErrors++;
                verifierRows.add(tsv("archive", "<archive>", "FAIL",
                        "class-count=" + verification.classes + "/"
                                + summary.parsedClasses));
            }
            if (verification.memberSites != summary.remainingMemberSites) {
                summary.outputVerificationErrors++;
                verifierRows.add(tsv("archive", "<archive>", "FAIL",
                        "remaining-member-sites=" + verification.memberSites + "/"
                                + summary.remainingMemberSites));
            }
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
                                     Map<String, byte[]> replacements, Path output,
                                     Summary summary) throws IOException {
        Set<String> applied = new LinkedHashSet<>();
        try (ZipOutputStream out = new ZipOutputStream(Files.newOutputStream(output))) {
            for (EntryBytes entry : entries) {
                if (isSignatureEntry(entry.name) && !replacements.isEmpty()) {
                    summary.signaturesRemoved++;
                    continue;
                }
                byte[] bytes = entry.bytes;
                if (entry.name.endsWith(".class")) {
                    String className = new ClassReader(bytes).getClassName();
                    byte[] replacement = replacements.get(className);
                    if (replacement != null) {
                        bytes = replacement;
                        applied.add(className);
                    }
                }
                ZipEntry written = new ZipEntry(entry.name);
                if (entry.time >= 0) written.setTime(entry.time);
                if (entry.comment != null) written.setComment(entry.comment);
                if (entry.extra != null) written.setExtra(entry.extra);
                if (entry.method == ZipEntry.STORED) {
                    CRC32 crc = new CRC32();
                    crc.update(bytes);
                    written.setMethod(ZipEntry.STORED);
                    written.setSize(bytes.length);
                    written.setCompressedSize(bytes.length);
                    written.setCrc(crc.getValue());
                } else {
                    written.setMethod(ZipEntry.DEFLATED);
                }
                out.putNextEntry(written);
                out.write(bytes);
                out.closeEntry();
                summary.outputEntries++;
            }
        }
        if (applied.size() != replacements.size()) {
            throw new IOException("applied-replacements=" + applied.size() + "/"
                    + replacements.size());
        }
    }

    private static ArchiveVerification verifyArchive(
            Path archive, List<String> verifierRows) throws IOException {
        ArchiveVerification result = new ArchiveVerification();
        try (ZipInputStream in = new ZipInputStream(Files.newInputStream(archive))) {
            ZipEntry entry;
            while ((entry = in.getNextEntry()) != null) {
                byte[] bytes = readAll(in);
                if (!entry.getName().endsWith(".class")) continue;
                result.classes++;
                String name = entry.getName().substring(0,
                        entry.getName().length() - 6);
                try {
                    ClassNode owner = readClass(bytes);
                    name = owner.name;
                    verifyClass(bytes);
                    result.memberSites += memberSites(owner).size();
                    verifierRows.add(tsv("archive", name, "PASS", ""));
                } catch (Throwable failure) {
                    result.errors++;
                    verifierRows.add(tsv("archive", name, "FAIL",
                            shortReason(failure)));
                }
            }
        }
        return result;
    }

    private static void writeReports(
            Path input, Path reportDirectory, Path classMap, Path methodMap,
            Path output, Summary summary, ZkmMemberProjection.Audit projectionAudit,
            List<SiteResult> results, List<String> verifierRows,
            String projectionMode) throws IOException {
        List<String> siteRows = new ArrayList<>();
        siteRows.add("class\tmethod\tinstruction\tindy_name\tindy_desc\tfirst_key"
                + "\tsecond_key\traw_index\traw_kind\traw_owner\traw_name\traw_desc"
                + "\tprojected_owner\tprojected_name\tprojected_desc"
                + "\tprojection_status\tprojection_evidence\tstripped_desc"
                + "\targument_conversions\treturn_conversion\taction\treason");
        List<String> rewriteRows = new ArrayList<>();
        rewriteRows.add("class\tmethod\tinstruction\taction\tprojected_kind"
                + "\tprojected_owner\tprojected_name\tprojected_desc\treason");
        for (SiteResult result : results) {
            siteRows.add(result.siteRow());
            rewriteRows.add(result.rewriteRow());
        }
        Files.write(reportDirectory.resolve("sites.tsv"), siteRows,
                StandardCharsets.UTF_8);
        Files.write(reportDirectory.resolve("rewrite.tsv"), rewriteRows,
                StandardCharsets.UTF_8);
        Files.write(reportDirectory.resolve("verifier.tsv"), verifierRows,
                StandardCharsets.UTF_8);
        projectionAudit.write(reportDirectory.resolve("projection-audit.txt"));

        List<String> audit = new ArrayList<>();
        audit.add("input=" + input.toAbsolutePath());
        audit.add("projection_mode=" + projectionMode);
        audit.add("class_map=" + (classMap == null ? "" : classMap.toAbsolutePath()));
        audit.add("method_map=" + (methodMap == null ? "" : methodMap.toAbsolutePath()));
        audit.add("parsed_classes=" + summary.parsedClasses);
        audit.add("site_classes=" + summary.siteClasses);
        audit.add("sites=" + summary.sites);
        audit.add("resolver_models=" + summary.resolverModels);
        audit.add("model_failures=" + summary.modelFailures);
        audit.add("source_proven_sites=" + summary.sourceProvenSites);
        audit.add("source_failures=" + summary.sourceFailures);
        audit.add("decoded_sites=" + summary.decodedSites);
        audit.add("decode_failures=" + summary.decodeFailures);
        audit.add("projected_sites=" + summary.projectedSites);
        audit.add("projection_failures=" + summary.projectionFailures);
        audit.add("compatible_sites=" + summary.compatibleSites);
        audit.add("conversion_failures=" + summary.conversionFailures);
        audit.add("interface_failures=" + summary.interfaceFailures);
        audit.add("kind_failures=" + summary.kindFailures);
        audit.add("planned_sites=" + summary.plannedSites);
        audit.add("rewritten_sites=" + summary.rewrittenSites);
        audit.add("skipped_sites=" + summary.skippedSites);
        audit.add("remaining_member_sites=" + summary.remainingMemberSites);
        audit.add("invokevirtual_sites=" + summary.virtualSites);
        audit.add("invokestatic_sites=" + summary.staticSites);
        audit.add("invokespecial_sites=" + summary.specialSites);
        audit.add("argument_exact=" + summary.argumentExact);
        audit.add("argument_reference_casts=" + summary.argumentReferenceCasts);
        audit.add("return_exact=" + summary.returnExact);
        audit.add("return_reference_casts=" + summary.returnReferenceCasts);
        audit.add("changed_classes=" + summary.changedClasses);
        audit.add("class_rollbacks=" + summary.classRollbacks);
        audit.add("rollback_sites=" + summary.rollbackSites);
        audit.add("external_class_resources_read="
                + summary.externalClassResourcesRead);
        audit.add("output_requested=" + summary.outputRequested);
        audit.add("output=" + (output == null ? "" : output.toAbsolutePath()));
        audit.add("temporary_output=" + value(summary.temporaryOutput));
        audit.add("output_entries=" + summary.outputEntries);
        audit.add("output_classes=" + summary.outputClasses);
        audit.add("output_verification_errors=" + summary.outputVerificationErrors);
        audit.add("output_remaining_member_sites="
                + summary.outputRemainingMemberSites);
        audit.add("signatures_removed=" + summary.signaturesRemoved);
        audit.add("output_committed=" + summary.outputCommitted);
        audit.add("input_classes_loaded=false");
        audit.add("input_classes_initialized=false");
        int conservative = 0;
        for (SiteResult result : results) {
            if ("REWRITE".equals(result.action)) continue;
            conservative++;
            audit.add("conservative_unresolved." + conservative + "="
                    + result.owner + "." + result.method + " -> "
                    + (result.raw == null ? "<undecoded>"
                    : result.raw.kind + " " + result.raw.owner + "."
                    + result.raw.name + result.raw.desc)
                    + " [" + (result.projected == null ? "UNRESOLVED"
                    : result.projected.status) + "] " + result.reason);
        }
        audit.add("conservative_unresolved_sites=" + conservative);
        audit.add("gate=" + gate(summary));
        Files.write(reportDirectory.resolve("audit.txt"), audit,
                StandardCharsets.UTF_8);
        Files.write(reportDirectory.resolve("gate.txt"),
                Collections.singletonList(gate(summary)), StandardCharsets.UTF_8);
    }

    private static String gate(Summary summary) {
        if (summary.classRollbacks != 0 || summary.outputVerificationErrors != 0
                || summary.outputRequested && !summary.outputCommitted) return "FAIL";
        return summary.remainingMemberSites == 0 ? "PASS" : "PARTIAL";
    }

    private static void countKind(Summary summary, String kind) {
        if ("INVOKEVIRTUAL".equals(kind)) summary.virtualSites++;
        else if ("INVOKESTATIC".equals(kind)) summary.staticSites++;
        else if ("INVOKESPECIAL".equals(kind)) summary.specialSites++;
    }

    private static Map<AbstractInsnNode, Integer> instructionIndexes(MethodNode method) {
        Map<AbstractInsnNode, Integer> result = new IdentityHashMap<>();
        int index = 0;
        for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
             insn = insn.getNext(), index++) result.put(insn, index);
        return result;
    }

    private static Long longConstant(AbstractInsnNode insn) {
        if (insn == null) return null;
        if (insn.getOpcode() == Opcodes.LCONST_0) return 0L;
        if (insn.getOpcode() == Opcodes.LCONST_1) return 1L;
        return insn instanceof LdcInsnNode && ((LdcInsnNode) insn).cst instanceof Long
                ? (Long) ((LdcInsnNode) insn).cst : null;
    }

    private static AbstractInsnNode previousCode(AbstractInsnNode insn) {
        AbstractInsnNode cursor = insn == null ? null : insn.getPrevious();
        while (cursor != null && cursor.getOpcode() < 0) cursor = cursor.getPrevious();
        return cursor;
    }

    private static <T> Set<T> identitySet() {
        return Collections.newSetFromMap(new IdentityHashMap<T, Boolean>());
    }

    private static byte[] readAll(InputStream input) throws IOException {
        ByteArrayOutputStream output = new ByteArrayOutputStream();
        byte[] buffer = new byte[8192];
        int read;
        while ((read = input.read(buffer)) != -1) output.write(buffer, 0, read);
        return output.toByteArray();
    }

    private static boolean isSignatureEntry(String name) {
        String upper = name.replace('\\', '/').toUpperCase(Locale.ROOT);
        if (!upper.startsWith("META-INF/")) return false;
        String leaf = upper.substring("META-INF/".length());
        return leaf.startsWith("SIG-") || leaf.endsWith(".SF")
                || leaf.endsWith(".RSA") || leaf.endsWith(".DSA")
                || leaf.endsWith(".EC");
    }

    private static String appendReason(String current, String added) {
        return current == null || current.isEmpty() ? added : current + ";" + added;
    }

    private static String value(Object value) {
        return value == null ? "" : String.valueOf(value);
    }

    private static String hex(Long value) {
        return value == null ? "" : String.format(Locale.ROOT, "%016X", value);
    }

    private static String shortReason(Throwable failure) {
        String text = failure.getClass().getSimpleName() + ":"
                + String.valueOf(failure.getMessage());
        text = text.replace('\t', ' ').replace('\r', ' ').replace('\n', ' ');
        return text.substring(0, Math.min(200, text.length()));
    }

    private static String tsv(Object... cells) {
        StringBuilder result = new StringBuilder();
        for (int i = 0; i < cells.length; i++) {
            if (i != 0) result.append('\t');
            if (cells[i] != null) result.append(String.valueOf(cells[i])
                    .replace('\t', ' ').replace('\r', ' ').replace('\n', ' '));
        }
        return result.toString();
    }

    static final class Adaptation {
        final boolean compatible;
        final Type[] sourceArguments;
        final Type[] destinationArguments;
        final Type[] argumentCasts;
        final Type sourceReturn;
        final Type destinationReturn;
        final Type returnCast;
        final String reason;

        private Adaptation(boolean compatible, Type[] sourceArguments,
                           Type[] destinationArguments, Type[] argumentCasts,
                           Type sourceReturn, Type destinationReturn, Type returnCast,
                           String reason) {
            this.compatible = compatible;
            this.sourceArguments = sourceArguments;
            this.destinationArguments = destinationArguments;
            this.argumentCasts = argumentCasts;
            this.sourceReturn = sourceReturn;
            this.destinationReturn = destinationReturn;
            this.returnCast = returnCast;
            this.reason = reason;
        }

        static Adaptation between(String callSiteDescriptor,
                                  String targetHandleDescriptor) {
            try {
                Type callSite = Type.getMethodType(callSiteDescriptor);
                Type target = Type.getMethodType(targetHandleDescriptor);
                Type[] sources = callSite.getArgumentTypes();
                Type[] destinations = target.getArgumentTypes();
                if (sources.length != destinations.length) {
                    return failure(sources, destinations, callSite.getReturnType(),
                            target.getReturnType(), "argument-count=" + sources.length
                                    + "/" + destinations.length);
                }
                Type[] casts = new Type[sources.length];
                for (int i = 0; i < sources.length; i++) {
                    if (sources[i].equals(destinations[i])) continue;
                    if (!reference(sources[i]) || !reference(destinations[i])) {
                        return failure(sources, destinations, callSite.getReturnType(),
                                target.getReturnType(), "argument-" + i + "="
                                        + sources[i].getDescriptor() + "->"
                                        + destinations[i].getDescriptor());
                    }
                    casts[i] = destinations[i];
                }
                Type sourceReturn = target.getReturnType();
                Type destinationReturn = callSite.getReturnType();
                Type returnCast = null;
                if (!sourceReturn.equals(destinationReturn)) {
                    if (!reference(sourceReturn) || !reference(destinationReturn)) {
                        return failure(sources, destinations, destinationReturn,
                                sourceReturn, "return=" + sourceReturn.getDescriptor()
                                        + "->" + destinationReturn.getDescriptor());
                    }
                    returnCast = destinationReturn;
                }
                return new Adaptation(true, sources, destinations, casts,
                        sourceReturn, destinationReturn, returnCast, "");
            } catch (RuntimeException failure) {
                return new Adaptation(false, new Type[0], new Type[0], new Type[0],
                        Type.VOID_TYPE, Type.VOID_TYPE, null,
                        "descriptor:" + shortReason(failure));
            }
        }

        private static Adaptation failure(Type[] sources, Type[] destinations,
                                          Type callSiteReturn, Type targetReturn,
                                          String reason) {
            return new Adaptation(false, sources, destinations,
                    new Type[sources.length], targetReturn, callSiteReturn,
                    null, reason);
        }

        String argumentSummary() {
            if (!compatible) return "<incompatible>";
            if (sourceArguments.length == 0) return "<none>";
            StringBuilder result = new StringBuilder();
            for (int i = 0; i < sourceArguments.length; i++) {
                if (i != 0) result.append(',');
                result.append(i).append(':');
                if (argumentCasts[i] == null) {
                    result.append("exact:").append(sourceArguments[i].getDescriptor());
                } else {
                    result.append("reference-cast:")
                            .append(sourceArguments[i].getDescriptor()).append("->")
                            .append(destinationArguments[i].getDescriptor());
                }
            }
            return result.toString();
        }

        String returnSummary() {
            if (!compatible) return "<incompatible>";
            if (returnCast == null) return "exact:" + sourceReturn.getDescriptor();
            return "reference-cast:" + sourceReturn.getDescriptor() + "->"
                    + destinationReturn.getDescriptor();
        }

        boolean hasArgumentCasts() {
            for (Type cast : argumentCasts) if (cast != null) return true;
            return false;
        }

        private static boolean reference(Type type) {
            return type.getSort() == Type.OBJECT || type.getSort() == Type.ARRAY;
        }
    }

    static final class TailProof {
        final boolean proven;
        final AbstractInsnNode firstNode;
        final AbstractInsnNode secondNode;
        final Long first;
        final Long second;
        final String reason;

        private TailProof(boolean proven, AbstractInsnNode firstNode,
                          AbstractInsnNode secondNode, Long first, Long second,
                          String reason) {
            this.proven = proven;
            this.firstNode = firstNode;
            this.secondNode = secondNode;
            this.first = first;
            this.second = second;
            this.reason = reason;
        }

        static TailProof proven(AbstractInsnNode firstNode,
                                AbstractInsnNode secondNode, long first, long second) {
            return new TailProof(true, firstNode, secondNode, first, second, "");
        }

        static TailProof failure(String reason) {
            return new TailProof(false, null, null, null, null, reason);
        }
    }

    static final class Summary {
        int parsedClasses;
        int siteClasses;
        int sites;
        int resolverModels;
        int modelFailures;
        int sourceProvenSites;
        int sourceFailures;
        int decodedSites;
        int decodeFailures;
        int projectedSites;
        int projectionFailures;
        int compatibleSites;
        int conversionFailures;
        int interfaceFailures;
        int kindFailures;
        int plannedSites;
        int rewrittenSites;
        int skippedSites;
        int remainingMemberSites;
        int virtualSites;
        int staticSites;
        int specialSites;
        int argumentExact;
        int argumentReferenceCasts;
        int returnExact;
        int returnReferenceCasts;
        int changedClasses;
        int classRollbacks;
        int rollbackSites;
        int externalClassResourcesRead;
        boolean outputRequested;
        String temporaryOutput;
        int outputEntries;
        int outputClasses;
        int outputVerificationErrors;
        int outputRemainingMemberSites;
        int signaturesRemoved;
        boolean outputCommitted;
    }

    private static final class RewritePlan {
        final MethodNode method;
        final InvokeDynamicInsnNode indy;
        final AbstractInsnNode firstKey;
        final AbstractInsnNode secondKey;
        final Adaptation adaptation;
        final int opcode;
        final String owner;
        final String name;
        final String descriptor;
        final boolean isInterface;

        RewritePlan(MethodNode method, InvokeDynamicInsnNode indy,
                    AbstractInsnNode firstKey, AbstractInsnNode secondKey,
                    Adaptation adaptation, int opcode, String owner, String name,
                    String descriptor, boolean isInterface) {
            this.method = method;
            this.indy = indy;
            this.firstKey = firstKey;
            this.secondKey = secondKey;
            this.adaptation = adaptation;
            this.opcode = opcode;
            this.owner = owner;
            this.name = name;
            this.descriptor = descriptor;
            this.isInterface = isInterface;
        }
    }

    private static final class SiteLocation {
        final MethodNode method;
        final InvokeDynamicInsnNode indy;
        final int index;

        SiteLocation(MethodNode method, InvokeDynamicInsnNode indy, int index) {
            this.method = method;
            this.indy = indy;
            this.index = index;
        }
    }

    private static final class SiteResult {
        final String owner;
        final String method;
        final int instruction;
        final String indyName;
        final String indyDescriptor;
        Long firstKey;
        Long secondKey;
        ZkmMemberIndyDeobfuscator.MemberTarget raw;
        ZkmMemberProjection.ProjectedTarget projected;
        String strippedDescriptor = "";
        Adaptation adaptation;
        RewritePlan plan;
        String action = "SKIP";
        String reason = "";

        SiteResult(String owner, MethodNode method, InvokeDynamicInsnNode indy,
                   int instruction) {
            this.owner = owner;
            this.method = method.name + method.desc;
            this.instruction = instruction;
            this.indyName = indy.name;
            this.indyDescriptor = indy.desc;
        }

        SiteResult skip(String reason) {
            this.action = "SKIP";
            this.reason = value(reason);
            return this;
        }

        String siteRow() {
            return tsv(owner, method, instruction, indyName, indyDescriptor,
                    hex(firstKey), hex(secondKey), raw == null ? "" : raw.index,
                    raw == null ? "" : raw.kind, raw == null ? "" : raw.owner,
                    raw == null ? "" : raw.name, raw == null ? "" : raw.desc,
                    projected == null ? "" : projected.owner,
                    projected == null ? "" : projected.name,
                    projected == null ? "" : projected.desc,
                    projected == null ? "" : projected.status,
                    projected == null ? "" : projected.evidence,
                    strippedDescriptor,
                    adaptation == null ? "" : adaptation.argumentSummary(),
                    adaptation == null ? "" : adaptation.returnSummary(),
                    action, reason);
        }

        String rewriteRow() {
            return tsv(owner, method, instruction, action,
                    projected == null ? "" : projected.kind,
                    projected == null ? "" : projected.owner,
                    projected == null ? "" : projected.name,
                    projected == null ? "" : projected.desc, reason);
        }
    }

    private static final class MethodAnalysis {
        final Map<AbstractInsnNode, Integer> indexes;
        final Frame<SourceValue>[] frames;
        final String failure;

        MethodAnalysis(Map<AbstractInsnNode, Integer> indexes,
                       Frame<SourceValue>[] frames, String failure) {
            this.indexes = indexes;
            this.frames = frames;
            this.failure = failure;
        }
    }

    private static final class InterfaceIndex {
        final Map<String, ClassNode> classes;
        final Map<String, InterfaceInfo> cache = new HashMap<>();
        int externalResourcesRead;

        InterfaceIndex(Map<String, ClassNode> classes) {
            this.classes = classes;
        }

        InterfaceInfo resolve(String owner) {
            ClassNode local = classes.get(owner);
            if (local != null) {
                return InterfaceInfo.resolved(
                        (local.access & Opcodes.ACC_INTERFACE) != 0);
            }
            InterfaceInfo known = cache.get(owner);
            if (known != null) return known;
            String resource = owner + ".class";
            try (InputStream input = ClassLoader.getSystemResourceAsStream(resource)) {
                if (input == null) {
                    known = InterfaceInfo.failure("class-resource-not-found=" + resource);
                } else {
                    externalResourcesRead++;
                    ClassReader reader = new ClassReader(input);
                    known = InterfaceInfo.resolved(
                            (reader.getAccess() & Opcodes.ACC_INTERFACE) != 0);
                }
            } catch (Throwable failure) {
                known = InterfaceInfo.failure(shortReason(failure));
            }
            cache.put(owner, known);
            return known;
        }
    }

    private static final class InterfaceInfo {
        final boolean resolved;
        final boolean isInterface;
        final String reason;

        private InterfaceInfo(boolean resolved, boolean isInterface, String reason) {
            this.resolved = resolved;
            this.isInterface = isInterface;
            this.reason = reason;
        }

        static InterfaceInfo resolved(boolean value) {
            return new InterfaceInfo(true, value, "");
        }

        static InterfaceInfo failure(String reason) {
            return new InterfaceInfo(false, false, reason);
        }
    }

    private static final class EntryBytes {
        final String name;
        final byte[] bytes;
        final long time;
        final int method;
        final String comment;
        final byte[] extra;

        EntryBytes(ZipEntry entry, byte[] bytes) {
            this.name = entry.getName();
            this.bytes = bytes;
            this.time = entry.getTime();
            this.method = entry.getMethod();
            this.comment = entry.getComment();
            this.extra = entry.getExtra();
        }
    }

    private static final class ArchiveVerification {
        int classes;
        int errors;
        int memberSites;
    }
}
