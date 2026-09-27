package unlegit.zkm;

import org.objectweb.asm.ClassReader;
import org.objectweb.asm.ClassWriter;
import org.objectweb.asm.Opcodes;
import org.objectweb.asm.Type;
import org.objectweb.asm.tree.*;
import org.objectweb.asm.tree.analysis.Analyzer;
import org.objectweb.asm.tree.analysis.BasicInterpreter;
import org.objectweb.asm.tree.analysis.BasicVerifier;
import org.objectweb.asm.tree.analysis.Frame;
import org.objectweb.asm.tree.analysis.SourceInterpreter;
import org.objectweb.asm.tree.analysis.SourceValue;
import org.objectweb.asm.util.CheckClassAdapter;

import java.io.*;
import java.nio.charset.StandardCharsets;
import java.nio.file.*;
import java.util.*;
import java.util.zip.*;

/** Offline control-flow reductions for JVM class archives. */
public final class ControlFlowDeobfuscator {
    private static final String[] REPORT_HEADER = {"class", "method", "offset", "action", "reason"};
    private static final int MAX_FIXED_POINT_ROUNDS = 12;
    private static final String ASSUME_ZKM_SENTINELS = "--assume-zkm-sentinels";
    private static final String NORMALIZE_EXCEPTION_RANGES = "--normalize-exception-ranges";
    private static final String REMOVE_IDENTITY_RETHROWS = "--remove-identity-rethrows";
    private static final String NORMALIZE_ZKM_SHARED_TAILS = "--normalize-zkm-shared-tails";
    private static final String MATERIALIZE_RESIDUAL_STACKS = "--materialize-residual-stacks";
    private static final String SPECIALIZE_BINARY_SENTINEL_TAILS =
            "--specialize-binary-sentinel-tails";
    private static final String CLEAN_CONSTANT_RESIDUAL_ISLANDS =
            "--clean-constant-residual-islands";

    public static void main(String[] args) throws Exception {
        if (args.length < 3 || args.length > 10) {
            System.err.println("usage: ControlFlowDeobfuscator <input.jar> <output.jar> <report.tsv> "
                    + "[--assume-zkm-sentinels] [--remove-identity-rethrows] "
                    + "[--normalize-exception-ranges] [--normalize-zkm-shared-tails] "
                    + "[--materialize-residual-stacks] "
                    + "[--specialize-binary-sentinel-tails] "
                    + "[--clean-constant-residual-islands]");
            System.exit(2);
        }
        boolean assumeZkmSentinels = false;
        boolean normalizeExceptionRanges = false;
        boolean removeIdentityRethrows = false;
        boolean normalizeZkmSharedTails = false;
        boolean materializeResidualStacks = false;
        boolean specializeBinarySentinelTails = false;
        boolean cleanConstantResidualIslands = false;
        for (int index = 3; index < args.length; index++) {
            if (ASSUME_ZKM_SENTINELS.equals(args[index])) {
                if (assumeZkmSentinels) throw new IllegalArgumentException("duplicate " + args[index]);
                assumeZkmSentinels = true;
            } else if (NORMALIZE_EXCEPTION_RANGES.equals(args[index])) {
                if (normalizeExceptionRanges) throw new IllegalArgumentException("duplicate " + args[index]);
                normalizeExceptionRanges = true;
            } else if (REMOVE_IDENTITY_RETHROWS.equals(args[index])) {
                if (removeIdentityRethrows) throw new IllegalArgumentException("duplicate " + args[index]);
                removeIdentityRethrows = true;
            } else if (NORMALIZE_ZKM_SHARED_TAILS.equals(args[index])) {
                if (normalizeZkmSharedTails) throw new IllegalArgumentException("duplicate " + args[index]);
                normalizeZkmSharedTails = true;
            } else if (MATERIALIZE_RESIDUAL_STACKS.equals(args[index])) {
                if (materializeResidualStacks) throw new IllegalArgumentException("duplicate " + args[index]);
                materializeResidualStacks = true;
            } else if (SPECIALIZE_BINARY_SENTINEL_TAILS.equals(args[index])) {
                if (specializeBinarySentinelTails) {
                    throw new IllegalArgumentException("duplicate " + args[index]);
                }
                specializeBinarySentinelTails = true;
            } else if (CLEAN_CONSTANT_RESIDUAL_ISLANDS.equals(args[index])) {
                if (cleanConstantResidualIslands) {
                    throw new IllegalArgumentException("duplicate " + args[index]);
                }
                cleanConstantResidualIslands = true;
            } else {
                throw new IllegalArgumentException("unknown option: " + args[index]);
            }
        }
        Path input = Paths.get(args[0]), output = Paths.get(args[1]), report = Paths.get(args[2]);
        Summary summary = rewrite(input, output, report, assumeZkmSentinels,
                removeIdentityRethrows, normalizeExceptionRanges,
                normalizeZkmSharedTails, materializeResidualStacks,
                specializeBinarySentinelTails, cleanConstantResidualIslands);
        System.out.println("classes=" + summary.classes + " changed=" + summary.changed
                + " rounds=" + summary.rounds + " failures=" + summary.failures
                + " mode=" + (assumeZkmSentinels ? "zkm-analysis" : "safe")
                + " identity_rethrows=" + (removeIdentityRethrows ? "removed" : "preserved")
                + " exception_ranges=" + (normalizeExceptionRanges ? "normalized" : "preserved")
                + " zkm_shared_tails=" + (normalizeZkmSharedTails ? "normalized" : "preserved")
                + " residual_stacks=" + (materializeResidualStacks ? "materialized" : "preserved")
                + " binary_sentinel_tails="
                + (specializeBinarySentinelTails ? "specialized" : "preserved")
                + " reference_sentinel_tails="
                + (specializeBinarySentinelTails ? "specialized" : "preserved")
                + " constant_residual_islands="
                + (cleanConstantResidualIslands ? "cleaned" : "preserved")
                + " report=" + report);
    }

    static Summary rewrite(Path input, Path output, Path report,
                           boolean assumeZkmSentinels,
                           boolean removeIdentityRethrows,
                           boolean normalizeExceptionRanges,
                           boolean normalizeZkmSharedTails) throws Exception {
        return rewrite(input, output, report, assumeZkmSentinels,
                removeIdentityRethrows, normalizeExceptionRanges,
                normalizeZkmSharedTails, false, false, false);
    }

    static Summary rewrite(Path input, Path output, Path report,
                           boolean assumeZkmSentinels,
                           boolean removeIdentityRethrows,
                           boolean normalizeExceptionRanges,
                           boolean normalizeZkmSharedTails,
                           boolean materializeResidualStacks) throws Exception {
        return rewrite(input, output, report, assumeZkmSentinels,
                removeIdentityRethrows, normalizeExceptionRanges,
                normalizeZkmSharedTails, materializeResidualStacks, false, false);
    }

    static Summary rewrite(Path input, Path output, Path report,
                           boolean assumeZkmSentinels,
                           boolean removeIdentityRethrows,
                           boolean normalizeExceptionRanges,
                           boolean normalizeZkmSharedTails,
                           boolean materializeResidualStacks,
                           boolean specializeBinarySentinelTails) throws Exception {
        return rewrite(input, output, report, assumeZkmSentinels,
                removeIdentityRethrows, normalizeExceptionRanges,
                normalizeZkmSharedTails, materializeResidualStacks,
                specializeBinarySentinelTails, false);
    }

    static Summary rewrite(Path input, Path output, Path report,
                           boolean assumeZkmSentinels,
                           boolean removeIdentityRethrows,
                           boolean normalizeExceptionRanges,
                           boolean normalizeZkmSharedTails,
                           boolean materializeResidualStacks,
                           boolean specializeBinarySentinelTails,
                           boolean cleanConstantResidualIslands) throws Exception {
        Path source = input.toAbsolutePath().normalize();
        Path target = output.toAbsolutePath().normalize();
        Path audit = report.toAbsolutePath().normalize();
        if (source.equals(target)
                || Files.exists(target) && Files.isSameFile(source, target)) {
            throw new IllegalArgumentException("output must not replace input");
        }
        Path outputParent = target.getParent();
        Path reportParent = audit.getParent();
        if (outputParent == null) throw new IOException("output has no parent: " + target);
        if (reportParent == null) throw new IOException("report has no parent: " + audit);
        Files.createDirectories(outputParent);
        Files.createDirectories(reportParent);
        List<String> rows = new ArrayList<>();
        rows.add(String.join("\t", REPORT_HEADER));
        Summary summary = new Summary();
        List<EntryBytes> entries = new ArrayList<>();
        try (ZipInputStream jis = new ZipInputStream(Files.newInputStream(source))) {
            ZipEntry e;
            while ((e = jis.getNextEntry()) != null) {
                entries.add(new EntryBytes(e, readAll(jis)));
            }
        }
        for (EntryBytes entry : entries) {
            if (entry.name.endsWith(".class")) summary.classes++;
        }

        Set<String> changedEntries = new LinkedHashSet<>();
        boolean converged = false;
        for (int round = 1; round <= MAX_FIXED_POINT_ROUNDS; round++) {
            summary.rounds = round;
            Map<String, ClassNode> proofClasses = proofClasses(entries);
            ZkmProvenanceIndex provenance = ZkmProvenanceIndex.build(proofClasses);
            ArchiveHierarchy hierarchy = new ArchiveHierarchy(proofClasses);
            int changedThisRound = 0;
            int failuresBeforeRound = summary.failures;
            for (EntryBytes entry : entries) {
                if (!entry.name.endsWith(".class")) continue;
                Result result = processClass(entry.bytes, rows, provenance, hierarchy,
                        assumeZkmSentinels, removeIdentityRethrows,
                        normalizeExceptionRanges, normalizeZkmSharedTails,
                        materializeResidualStacks, specializeBinarySentinelTails);
                summary.failures += result.failures;
                byte[] rewritten = result.bytes;
                boolean classChanged = result.changed;
                if (cleanConstantResidualIslands) {
                    ConstantResidualIslandCleaner.ClassResult islands =
                            ConstantResidualIslandCleaner.rewriteClass(rewritten);
                    appendConstantIslandRows(rows, islands);
                    if (islands.isCommitted() && islands.removed() > 0) {
                        rewritten = islands.bytes();
                        classChanged = true;
                    } else if (!islands.isCommitted() && islands.removed() > 0) {
                        summary.failures++;
                    }
                }
                if (classChanged) {
                    entry.bytes = rewritten;
                    changedEntries.add(entry.name);
                    changedThisRound++;
                }
            }
            rows.add(row("<archive>", "fixed-point-round-" + round, -1,
                    "fixed-point-round",
                    "changed_classes=" + changedThisRound
                            + ",failures="
                            + (summary.failures - failuresBeforeRound)));
            if (summary.failures != failuresBeforeRound) break;
            if (changedThisRound == 0) {
                converged = true;
                break;
            }
        }
        summary.changed = changedEntries.size();
        deduplicateDiagnosticRows(rows);
        Files.write(audit, rows, StandardCharsets.UTF_8);
        if (summary.failures != 0) {
            throw new IOException("control-flow fixed point rejected "
                    + summary.failures + " method/class transaction(s); report=" + audit);
        }
        if (!converged) {
            throw new IOException("control-flow fixed point did not converge within "
                    + MAX_FIXED_POINT_ROUNDS + " rounds; report=" + audit);
        }

        boolean modifiedAnyClass = !changedEntries.isEmpty();

        Path temporary = Files.createTempFile(outputParent,
                "." + target.getFileName().toString() + ".flow-", ".tmp");
        boolean moved = false;
        try {
            try (ZipOutputStream jos = new ZipOutputStream(Files.newOutputStream(temporary))) {
                for (EntryBytes entry : entries) {
                    if (modifiedAnyClass && isSignatureEntry(entry.name)) {
                        continue;
                    }
                    ZipEntry out = new ZipEntry(entry.name);
                    out.setTime(entry.time);
                    jos.putNextEntry(out);
                    jos.write(entry.bytes);
                    jos.closeEntry();
                }
            }
            verifyArchive(temporary, summary.classes);
            try {
                Files.move(temporary, target, StandardCopyOption.ATOMIC_MOVE,
                        StandardCopyOption.REPLACE_EXISTING);
            } catch (AtomicMoveNotSupportedException unsupported) {
                throw new IOException("atomic control-flow stage publication is not supported for "
                        + target, unsupported);
            }
            moved = true;
            summary.outputCommitted = true;
            return summary;
        } finally {
            if (!moved) Files.deleteIfExists(temporary);
        }
    }

    private static void verifyArchive(Path archive, int expectedClasses) throws Exception {
        int classes = 0;
        Set<String> names = new HashSet<>();
        try (ZipFile zip = new ZipFile(archive.toFile())) {
            Enumeration<? extends ZipEntry> entries = zip.entries();
            while (entries.hasMoreElements()) {
                ZipEntry entry = entries.nextElement();
                if (!names.add(entry.getName())) {
                    throw new IOException("duplicate archive entry: " + entry.getName());
                }
                if (entry.isDirectory() || !entry.getName().endsWith(".class")) continue;
                byte[] bytes;
                try (InputStream input = zip.getInputStream(entry)) {
                    bytes = readAll(input);
                }
                ClassNode owner = new ClassNode(Opcodes.ASM9);
                new ClassReader(bytes).accept(owner, 0);
                if (!(owner.name + ".class").equals(entry.getName())
                        && !entry.getName().matches("META-INF/versions/[^/]+/"
                        + java.util.regex.Pattern.quote(owner.name) + "\\.class")) {
                    throw new IOException("class entry/name mismatch: " + entry.getName()
                            + " != " + owner.name);
                }
                if (!structurallyValid(bytes)) {
                    throw new IOException("archive verifier rejected " + owner.name);
                }
                classes++;
            }
        }
        if (classes != expectedClasses) {
            throw new IOException("class count changed: expected=" + expectedClasses
                    + ", actual=" + classes);
        }
    }

    private static boolean isSignatureEntry(String name) {
        String upper = name.replace('\\', '/').toUpperCase(Locale.ROOT);
        if (!upper.startsWith("META-INF/")) return false;
        String leaf = upper.substring("META-INF/".length());
        if (leaf.indexOf('/') >= 0) return false;
        return leaf.endsWith(".SF") || leaf.endsWith(".RSA")
                || leaf.endsWith(".DSA") || leaf.endsWith(".EC")
                || leaf.startsWith("SIG-");
    }

    private static void deduplicateDiagnosticRows(List<String> rows) {
        Set<String> seen = new HashSet<>();
        for (int index = 1; index < rows.size(); ) {
            String line = rows.get(index);
            String[] columns = line.split("\t", 5);
            boolean diagnostic = columns.length >= 4
                    && columns[3].contains("skip");
            if (diagnostic && !seen.add(line)) {
                rows.remove(index);
            } else {
                index++;
            }
        }
    }

    private static void appendConstantIslandRows(
            List<String> rows,
            ConstantResidualIslandCleaner.ClassResult result) {
        for (ConstantResidualIslandCleaner.IslandLocation island
                : result.islands()) {
            boolean removed = island.isProven() && result.isCommitted();
            String reason = removed
                    ? "pure_constant_stack_effect=identity,pass=" + island.pass()
                    : island.reason() + ",stage=" + result.stage()
                            + ",transaction=" + result.reason();
            rows.add(row(island.owner(), island.method() + island.descriptor(),
                    island.rawStart(), removed
                            ? "clean-constant-residual-island"
                            : "constant-residual-island-skip", reason));
        }
    }

    static final class Summary {
        int classes;
        int changed;
        int rounds;
        int failures;
        boolean outputCommitted;
    }

    private static byte[] readAll(InputStream in) throws IOException {
        ByteArrayOutputStream b = new ByteArrayOutputStream();
        byte[] buf = new byte[8192]; int n;
        while ((n = in.read(buf)) >= 0) b.write(buf, 0, n);
        return b.toByteArray();
    }

    private static Map<String, ClassNode> proofClasses(List<EntryBytes> entries) {
        Map<String, ClassNode> result = new LinkedHashMap<>();
        for (EntryBytes entry : entries) {
            if (!entry.name.endsWith(".class")) continue;
            try {
                ClassNode node = new ClassNode(Opcodes.ASM9);
                new ClassReader(entry.bytes).accept(node, 0);
                result.put(node.name, node);
            } catch (Throwable ignored) {
                // processClass records malformed entries and makes publication fail closed.
            }
        }
        return result;
    }

    private static final class EntryBytes {
        final String name; final long time; byte[] bytes;
        EntryBytes(ZipEntry e, byte[] b) { name=e.getName(); time=e.getTime(); bytes=b; }
    }

    private static Result processClass(byte[] original, List<String> rows,
                                       ZkmProvenanceIndex provenance,
                                       ArchiveHierarchy hierarchy,
                                       boolean assumeZkmSentinels,
                                       boolean removeIdentityRethrows,
                                       boolean normalizeExceptionRanges,
                                       boolean normalizeZkmSharedTails,
                                       boolean materializeResidualStacks,
                                       boolean specializeBinarySentinelTails) {
        ClassNode cn = new ClassNode(Opcodes.ASM9);
        try { new ClassReader(original).accept(cn, 0); }
        catch (Throwable t) { rows.add(row("<unknown>", "<class>", -1, "skip", "parse:" + shortReason(t))); return new Result(original, false, 1); }
        boolean changed = false;
        int failures = 0;
        for (MethodNode method : new ArrayList<>(cn.methods)) {
            if (method.instructions == null || method.instructions.size() == 0) continue;
            MethodNode backup = cloneMethod(method);
            String owner = cn.name;
            Map<AbstractInsnNode,Integer> offsets = originalOffsets(method);
            int rowStart = rows.size();
            try {
                Analyzer<org.objectweb.asm.tree.analysis.BasicValue> analyzer = new Analyzer<>(new BasicInterpreter());
                boolean local = false;
                local |= removeUnreachable(method, analyzer.analyze(owner, method), owner, rows, offsets);
                local |= foldConstants(method, owner, rows, offsets);
                local |= removeUnreachable(method, analyzer.analyze(owner, method), owner, rows, offsets);
                if (normalizeZkmSharedTails) {
                    boolean normalizedSharedTails = normalizeZkmSharedTails(method,
                            owner, rows, offsets);
                    local |= normalizedSharedTails;
                    if (normalizedSharedTails) {
                        local |= removeUnreachable(method, analyzer.analyze(owner, method),
                                owner, rows, offsets);
                    }
                }
                local |= removeGotoNext(method, owner, rows, offsets);
                local |= coalesceLabels(method, owner, rows, offsets);
                Frame<org.objectweb.asm.tree.analysis.BasicValue>[] guardFrames =
                        analyzer.analyze(owner, method);
                List<ZkmAssumptionPlan> assumptionPlans = assumeZkmSentinels
                        ? collectZkmAssumptionPlans(method, guardFrames, provenance, owner)
                        : Collections.<ZkmAssumptionPlan>emptyList();
                local |= rewritePathProvenZkmGuards(method, guardFrames, owner, rows,
                        offsets, provenance);
                if (assumeZkmSentinels) {
                    local |= rewriteAssumedZkmSentinels(method, assumptionPlans, owner,
                            rows, offsets);
                }
                if (local && assumeZkmSentinels) {
                    local |= foldConstants(method, owner, rows, offsets);
                    local |= removeUnreachable(method, analyzer.analyze(owner, method),
                            owner, rows, offsets);
                    local |= removeGotoNext(method, owner, rows, offsets);
                    local |= coalesceLabels(method, owner, rows, offsets);
                }
                if (materializeResidualStacks) {
                    List<ResidualStackMaterializer.Rewrite> materialized =
                            ResidualStackMaterializer.materialize(method, owner);
                    for (ResidualStackMaterializer.Rewrite rewrite : materialized) {
                        rows.add(row(owner, method.name + method.desc,
                                offsetOf(rewrite.jump, offsets, method),
                                "materialize-residual-stack",
                                "values=" + rewrite.values
                                        + ",fresh_local_start=" + rewrite.firstLocal
                                        + ",local_slots=" + rewrite.localSlots
                                        + ",types=" + rewrite.valueKinds
                                        + ",branch_outcomes=preserved"));
                    }
                    local |= !materialized.isEmpty();
                }
                if (removeIdentityRethrows) {
                    boolean removedRethrows = removeIdentityRethrowHandlers(method,
                            provenance, hierarchy, owner, rows, offsets);
                    local |= removedRethrows;
                    if (removedRethrows) {
                        boolean cleanupChanged;
                        do {
                            cleanupChanged = removeUnreachable(method,
                                    analyzer.analyze(owner, method), owner, rows, offsets);
                            cleanupChanged |= removeGotoNext(method, owner, rows, offsets);
                            cleanupChanged |= coalesceLabels(method, owner, rows, offsets);
                            cleanupChanged |= removeEmptyTryCatchBlocks(method, owner,
                                    rows, offsets);
                            local |= cleanupChanged;
                        } while (cleanupChanged);
                    }
                }
                if (normalizeExceptionRanges) {
                    local |= normalizeCrossingExceptionRanges(method, owner, rows, offsets);
                }
                if (specializeBinarySentinelTails) {
                    BinarySentinelTailSpecializer.Rewrite specialized =
                            BinarySentinelTailSpecializer.specialize(cn, method);
                    if (specialized.changed()) {
                        rows.add(row(owner, method.name + method.desc, -1,
                                "binary-sentinel-tail-specialize",
                                "local#" + specialized.sentinelLocal()
                                        + ",guards=" + specialized.guards()
                                        + ",split_instruction="
                                        + specialized.splitInstruction()
                                        + ",tail_instructions="
                                        + specialized.tailInstructions()
                                        + ",code_upper_bound="
                                        + specialized.codeSizeUpperBound()
                                        + ",semantics=exact-zero-or-nonzero"));
                        local = true;
                        boolean cleanupChanged;
                        do {
                            cleanupChanged = removeUnreachable(method,
                                    analyzer.analyze(owner, method), owner, rows, offsets);
                            cleanupChanged |= removeGotoNext(method, owner, rows, offsets);
                            cleanupChanged |= coalesceLabels(method, owner, rows, offsets);
                            local |= cleanupChanged;
                        } while (cleanupChanged);
                    }

                    ReferenceSentinelTailSpecializer.Rewrite referenceSpecialized =
                            ReferenceSentinelTailSpecializer.specialize(cn, method);
                    if (referenceSpecialized.changed()) {
                        rows.add(row(owner, method.name + method.desc, -1,
                                "reference-sentinel-tail-specialize",
                                "local#" + referenceSpecialized.sentinelLocal()
                                        + ",guards=" + referenceSpecialized.guards()
                                        + ",split_instruction="
                                        + referenceSpecialized.splitInstruction()
                                        + ",tail_instructions="
                                        + referenceSpecialized.tailInstructions()
                                        + ",code_upper_bound="
                                        + referenceSpecialized.codeSizeUpperBound()
                                        + ",semantics=exact-null-or-nonnull"));
                        local = true;
                        boolean cleanupChanged;
                        do {
                            cleanupChanged = removeUnreachable(method,
                                    analyzer.analyze(owner, method), owner, rows,
                                    offsets);
                            cleanupChanged |= removeGotoNext(method, owner, rows,
                                    offsets);
                            cleanupChanged |= coalesceLabels(method, owner, rows,
                                    offsets);
                            local |= cleanupChanged;
                        } while (cleanupChanged);
                    }
                }
                if (local) {
                    local |= removeEmptyTryCatchBlocks(method, owner, rows, offsets);
                    local |= removeDeadLineNumbers(method, owner, rows, offsets);
                    local |= removeInvalidLocalVariableMetadata(method, owner, rows,
                            offsets);
                }
                if (!local) continue;
                // Re-run analysis after edits. Invalid stack/control flow is never emitted.
                new Analyzer<>(new BasicInterpreter()).analyze(owner, method);
                cn.methods.set(cn.methods.indexOf(method), method);
                // Every rule above may change normal or exceptional CFG edges.
                // Reusing stale StackMapTable frames is invalid even in safe mode.
                byte[] candidate = writeClass(cn, hierarchy, shouldComputeFrames(cn));
                String validationFailure = structuralValidationFailure(candidate);
                if (validationFailure != null) {
                    throw new IllegalStateException("class-validation:" + validationFailure);
                }
                changed = true;
            } catch (Throwable t) {
                failures++;
                while (rows.size() > rowStart) rows.remove(rows.size() - 1);
                int idx = cn.methods.indexOf(method);
                if (idx >= 0) cn.methods.set(idx, backup);
                rows.add(row(owner, method.name + method.desc, -1, "skip", "verification:" + shortReason(t)));
            }
        }
        return new Result(changed ? writeClass(cn, hierarchy, shouldComputeFrames(cn))
                : original, changed, failures);
    }

    /**
     * Splits a shared ZKM straight-line tail only when the switch selector is
     * proven to be the untouched integer constant pushed at every incoming
     * GOTO. Methods with exception handlers are deliberately out of scope:
     * moving a possibly-throwing instruction across a protected range would
     * otherwise change handler selection.
     */
    private static boolean normalizeZkmSharedTails(
            MethodNode method,
            String owner,
            List<String> rows,
            Map<AbstractInsnNode, Integer> offsets) {
        if (method.tryCatchBlocks != null && !method.tryCatchBlocks.isEmpty()) return false;
        for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
             insn = insn.getNext()) {
            if (insn.getOpcode() == Opcodes.JSR || insn.getOpcode() == Opcodes.RET) return false;
        }

        Frame<SourceValue>[] frames;
        try {
            frames = new Analyzer<>(new CopyTransparentSourceInterpreter())
                    .analyze(owner, method);
        } catch (Throwable failure) {
            rows.add(row(owner, method.name + method.desc, -1,
                    "zkm-shared-tail-skip-method",
                    "source_analysis=" + shortReason(failure)));
            return false;
        }
        Map<AbstractInsnNode, Integer> indexes = instructionIndexes(method);
        Map<LabelNode, List<JumpInsnNode>> gotosByTarget = new IdentityHashMap<>();
        for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
             insn = insn.getNext()) {
            if (insn instanceof JumpInsnNode && insn.getOpcode() == Opcodes.GOTO) {
                JumpInsnNode jump = (JumpInsnNode) insn;
                gotosByTarget.computeIfAbsent(jump.label, ignored -> new ArrayList<>())
                        .add(jump);
            }
        }

        List<ZkmSharedTailPlan> plans = new ArrayList<>();
        Set<AbstractInsnNode> claimed = Collections.newSetFromMap(
                new IdentityHashMap<AbstractInsnNode, Boolean>());
        for (Map.Entry<LabelNode, List<JumpInsnNode>> entry : gotosByTarget.entrySet()) {
            if (entry.getValue().size() < 2) continue;
            LabelNode shared = entry.getKey();
            List<ZkmSharedTailSite> sites = new ArrayList<>();
            Set<Integer> values = new LinkedHashSet<>();
            Set<AbstractInsnNode> constants = Collections.newSetFromMap(
                    new IdentityHashMap<AbstractInsnNode, Boolean>());
            boolean proven = true;
            for (JumpInsnNode jump : entry.getValue()) {
                AbstractInsnNode constant = prevCode(jump);
                Integer value = intConstant(constant);
                Integer jumpIndex = indexes.get(jump);
                Frame<SourceValue> jumpFrame = jumpIndex == null
                        || jumpIndex >= frames.length ? null : frames[jumpIndex];
                if (value == null || !values.add(value)
                        || !hasExactTopSources(jumpFrame,
                                Collections.singleton(constant))) {
                    proven = false;
                    break;
                }
                constants.add(constant);
                sites.add(new ZkmSharedTailSite(jump, constant, value));
            }
            if (!proven) continue;

            ZkmSharedTail tail = findZkmSharedTail(shared);
            if (tail == null || hasUnexpectedSharedTailEntry(method, tail,
                    entry.getValue())) continue;
            Integer switchIndex = indexes.get(tail.switchInsn);
            Frame<SourceValue> switchFrame = switchIndex == null
                    || switchIndex >= frames.length ? null : frames[switchIndex];
            if (!hasExactTopSources(switchFrame, constants)) continue;

            for (ZkmSharedTailSite site : sites) {
                site.target = zkmSwitchTarget(tail.switchInsn, site.value);
                if (site.target == null) {
                    proven = false;
                    break;
                }
            }
            if (proven && !overlapsClaimedTail(tail, sites, claimed)) {
                ZkmSharedTailPlan plan = new ZkmSharedTailPlan(tail, sites);
                plans.add(plan);
                claimed.add(tail.switchInsn);
                claimed.addAll(tail.body);
                for (ZkmSharedTailSite site : sites) {
                    claimed.add(site.constant);
                    claimed.add(site.jump);
                }
            }
        }

        for (ZkmSharedTailPlan plan : plans) {
            for (ZkmSharedTailSite site : plan.sites) {
                InsnList copy = cloneZkmSharedTail(plan.tail);
                copy.add(new InsnNode(Opcodes.POP));
                method.instructions.insertBefore(site.jump, copy);
                site.jump.label = site.target;
            }
            rows.add(row(owner, method.name + method.desc,
                    offsetOf(plan.tail.shared, offsets, method),
                    "normalize-zkm-shared-tail",
                    "sites=" + plan.sites.size()
                            + ",tail_instructions=" + plan.tail.executableCount
                            + ",switch=" + (plan.tail.switchInsn instanceof TableSwitchInsnNode
                                    ? "TABLESWITCH" : "LOOKUPSWITCH")
                            + ",selector_sources=exact_int_constants,try_catch=none"));
        }
        return !plans.isEmpty();
    }

    private static boolean overlapsClaimedTail(
            ZkmSharedTail tail,
            List<ZkmSharedTailSite> sites,
            Set<AbstractInsnNode> claimed) {
        if (claimed.contains(tail.switchInsn)) return true;
        for (AbstractInsnNode insn : tail.body) if (claimed.contains(insn)) return true;
        for (ZkmSharedTailSite site : sites) {
            if (claimed.contains(site.constant) || claimed.contains(site.jump)) return true;
        }
        return false;
    }

    private static boolean hasExactTopSources(
            Frame<SourceValue> frame, Collection<AbstractInsnNode> expected) {
        if (frame == null || frame.getStackSize() == 0) return false;
        SourceValue source = frame.getStack(frame.getStackSize() - 1);
        return source != null && source.getSize() == 1
                && source.insns.size() == expected.size()
                && source.insns.containsAll(expected);
    }

    /** Keeps provenance through DUP/SWAP stack motion used by ZKM tails. */
    private static final class CopyTransparentSourceInterpreter
            extends SourceInterpreter {
        CopyTransparentSourceInterpreter() {
            super(Opcodes.ASM9);
        }

        @Override public SourceValue copyOperation(
                AbstractInsnNode insn, SourceValue value) {
            return value;
        }
    }

    private static ZkmSharedTail findZkmSharedTail(LabelNode shared) {
        List<AbstractInsnNode> body = new ArrayList<>();
        int executableCount = 0;
        for (AbstractInsnNode insn = shared.getNext(); insn != null;
             insn = insn.getNext()) {
            if (insn instanceof TableSwitchInsnNode
                    || insn instanceof LookupSwitchInsnNode) {
                return new ZkmSharedTail(shared, body, insn, executableCount);
            }
            int opcode = insn.getOpcode();
            if (insn instanceof JumpInsnNode || opcode == Opcodes.RET
                    || opcode == Opcodes.ATHROW
                    || opcode >= Opcodes.IRETURN && opcode <= Opcodes.RETURN) {
                return null;
            }
            body.add(insn);
            if (opcode >= 0) executableCount++;
        }
        return null;
    }

    private static boolean hasUnexpectedSharedTailEntry(
            MethodNode method,
            ZkmSharedTail tail,
            Collection<JumpInsnNode> allowedGotos) {
        Set<LabelNode> labels = Collections.newSetFromMap(
                new IdentityHashMap<LabelNode, Boolean>());
        labels.add(tail.shared);
        for (AbstractInsnNode insn : tail.body) {
            if (insn instanceof LabelNode) labels.add((LabelNode) insn);
        }
        Set<JumpInsnNode> allowed = Collections.newSetFromMap(
                new IdentityHashMap<JumpInsnNode, Boolean>());
        allowed.addAll(allowedGotos);

        AbstractInsnNode predecessor = prevCode(tail.shared);
        if (predecessor == null || canFallThrough(predecessor)) return true;
        for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
             insn = insn.getNext()) {
            if (insn instanceof JumpInsnNode) {
                JumpInsnNode jump = (JumpInsnNode) insn;
                if (labels.contains(jump.label)
                        && !(jump.label == tail.shared && jump.getOpcode() == Opcodes.GOTO
                                && allowed.contains(jump))) return true;
            } else if (insn instanceof TableSwitchInsnNode) {
                TableSwitchInsnNode table = (TableSwitchInsnNode) insn;
                if (labels.contains(table.dflt)) return true;
                for (LabelNode label : table.labels) if (labels.contains(label)) return true;
            } else if (insn instanceof LookupSwitchInsnNode) {
                LookupSwitchInsnNode lookup = (LookupSwitchInsnNode) insn;
                if (labels.contains(lookup.dflt)) return true;
                for (LabelNode label : lookup.labels) if (labels.contains(label)) return true;
            }
        }
        return false;
    }

    private static boolean canFallThrough(AbstractInsnNode insn) {
        int opcode = insn.getOpcode();
        return !(opcode == Opcodes.GOTO || opcode == Opcodes.JSR
                || opcode == Opcodes.RET || opcode == Opcodes.ATHROW
                || opcode >= Opcodes.IRETURN && opcode <= Opcodes.RETURN
                || insn instanceof TableSwitchInsnNode
                || insn instanceof LookupSwitchInsnNode);
    }

    private static LabelNode zkmSwitchTarget(AbstractInsnNode switchInsn, int value) {
        if (switchInsn instanceof TableSwitchInsnNode) {
            TableSwitchInsnNode table = (TableSwitchInsnNode) switchInsn;
            long index = (long) value - table.min;
            return index >= 0 && index < table.labels.size()
                    ? table.labels.get((int) index) : table.dflt;
        }
        if (switchInsn instanceof LookupSwitchInsnNode) {
            LookupSwitchInsnNode lookup = (LookupSwitchInsnNode) switchInsn;
            for (int index = 0; index < lookup.keys.size(); index++) {
                if (lookup.keys.get(index).intValue() == value) {
                    return lookup.labels.get(index);
                }
            }
            return lookup.dflt;
        }
        return null;
    }

    private static InsnList cloneZkmSharedTail(ZkmSharedTail tail) {
        Map<LabelNode, LabelNode> labels = new IdentityHashMap<>();
        labels.put(tail.shared, new LabelNode());
        for (AbstractInsnNode insn : tail.body) {
            if (insn instanceof LabelNode) {
                labels.put((LabelNode) insn, new LabelNode());
            }
        }
        InsnList result = new InsnList();
        result.add(labels.get(tail.shared));
        for (AbstractInsnNode insn : tail.body) {
            if (insn instanceof FrameNode) continue;
            if (insn instanceof LineNumberNode
                    && !labels.containsKey(((LineNumberNode) insn).start)) continue;
            result.add(insn.clone(labels));
        }
        return result;
    }

    private static final class ZkmSharedTail {
        final LabelNode shared;
        final List<AbstractInsnNode> body;
        final AbstractInsnNode switchInsn;
        final int executableCount;

        ZkmSharedTail(LabelNode shared, List<AbstractInsnNode> body,
                      AbstractInsnNode switchInsn, int executableCount) {
            this.shared = shared;
            this.body = body;
            this.switchInsn = switchInsn;
            this.executableCount = executableCount;
        }
    }

    private static final class ZkmSharedTailSite {
        final JumpInsnNode jump;
        final AbstractInsnNode constant;
        final int value;
        LabelNode target;

        ZkmSharedTailSite(JumpInsnNode jump, AbstractInsnNode constant, int value) {
            this.jump = jump;
            this.constant = constant;
            this.value = value;
        }
    }

    private static final class ZkmSharedTailPlan {
        final ZkmSharedTail tail;
        final List<ZkmSharedTailSite> sites;

        ZkmSharedTailPlan(ZkmSharedTail tail, List<ZkmSharedTailSite> sites) {
            this.tail = tail;
            this.sites = sites;
        }
    }

    /**
     * Runs a branch-sensitive zero/nonzero or null/non-null fixed point over a
     * method. Every local guard may be rewritten, but only when one successor
     * is unreachable in the abstract state at that exact instruction. The
     * older repeated residual-stack filter is retained only for skip-report
     * diagnostics, not as an artificial restriction on a semantic proof.
     */
    private static boolean rewritePathProvenZkmGuards(
            MethodNode method,
            Frame<org.objectweb.asm.tree.analysis.BasicValue>[] basicFrames,
            String owner,
            List<String> rows,
            Map<AbstractInsnNode, Integer> offsets,
            ZkmProvenanceIndex provenance) {
        for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
             insn = insn.getNext()) {
            if (insn.getOpcode() == Opcodes.JSR || insn.getOpcode() == Opcodes.RET) return false;
        }

        Map<String, List<ZkmGuardSite>> allByLocal = new LinkedHashMap<>();
        Map<String, Integer> residualCounts = new LinkedHashMap<>();
        int instructionIndex = 0;
        for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
             insn = insn.getNext(), instructionIndex++) {
            if (!(insn instanceof JumpInsnNode)) continue;
            String kind = zkmGuardKind(insn.getOpcode());
            if (kind == null || !(insn.getPrevious() instanceof VarInsnNode)) continue;
            VarInsnNode load = (VarInsnNode) insn.getPrevious();
            if (load.getOpcode() != zkmLoadOpcode(kind)) continue;
            Frame<?> frame = instructionIndex < basicFrames.length
                    ? basicFrames[instructionIndex] : null;
            if (frame == null || frame.getStackSize() < 1) continue;
            ZkmGuardSite site = new ZkmGuardSite(load, (JumpInsnNode) insn, kind,
                    load.var, insn.getOpcode(), frame.getStackSize());
            allByLocal.computeIfAbsent(site.localKey(), ignored -> new ArrayList<>()).add(site);
            if (site.residual()) {
                String group = site.groupKey();
                residualCounts.put(group, residualCounts.getOrDefault(group, 0) + 1);
            }
        }

        List<ZkmGuardSite> eligible = new ArrayList<>();
        Set<ZkmGuardSite> diagnosticSites = Collections.newSetFromMap(
                new IdentityHashMap<ZkmGuardSite, Boolean>());
        for (Map.Entry<String, List<ZkmGuardSite>> entry : allByLocal.entrySet()) {
            boolean repeatedResidual = false;
            for (ZkmGuardSite site : entry.getValue()) {
                if (residualCounts.getOrDefault(site.groupKey(), 0) >= 2) {
                    repeatedResidual = true;
                    break;
                }
            }
            eligible.addAll(entry.getValue());
            if (repeatedResidual) diagnosticSites.addAll(entry.getValue());
        }
        if (eligible.isEmpty()) return false;

        Frame<SourceValue>[] sourceFrames;
        try {
            sourceFrames = new Analyzer<>(new SourceInterpreter()).analyze(owner, method);
        } catch (Throwable failure) {
            rows.add(row(owner, method.name + method.desc, -1, "zkm-path-skip-method",
                    "source_analysis=" + shortReason(failure)));
            return false;
        }
        Map<AbstractInsnNode, Integer> indexes = instructionIndexes(method);
        Map<AbstractInsnNode, List<LabelNode>> handlers =
                ZkmProvenanceIndex.exceptionHandlers(method, indexes);
        Map<String, GuardPathFacts> facts = new LinkedHashMap<>();
        for (ZkmGuardSite site : eligible) {
            if (!facts.containsKey(site.localKey())) {
                facts.put(site.localKey(), analyzeGuardLocal(method, site.kind, site.local,
                        indexes, handlers, sourceFrames, provenance, owner));
            }
        }

        List<PathGuardDecision> decisions = new ArrayList<>();
        for (ZkmGuardSite site : eligible) {
            GuardPathFacts localFacts = facts.get(site.localKey());
            Integer index = indexes.get(site.jump);
            int domain = localFacts == null || index == null ? GuardDomain.UNREACHED
                    : localFacts.before[index];
            int truth = GuardDomain.truthMask(site.opcode);
            int falsehood = GuardDomain.falseMask(site.opcode);
            boolean initialized = domain != GuardDomain.UNREACHED
                    && (domain & GuardDomain.UNINITIALIZED) == 0;
            boolean canTake = (domain & truth) != 0;
            boolean canFall = (domain & falsehood) != 0;
            if (!initialized || canTake == canFall) {
                if (diagnosticSites.contains(site)) {
                    rows.add(row(owner, method.name + method.desc,
                            offsetOf(site.jump, offsets, method),
                            "zkm-path-skip-unproven",
                            "kind=" + site.kind + ",local#" + site.local
                                    + ",opcode=" + zkmOpcodeName(site.opcode)
                                    + ",domain=" + GuardDomain.describe(domain)));
                }
                continue;
            }
            decisions.add(new PathGuardDecision(site, canTake, domain));
        }

        boolean changed = false;
        for (PathGuardDecision decision : decisions) {
            ZkmGuardSite site = decision.site;
            int offset = offsetOf(site.jump, offsets, method);
            String reason = "kind=" + site.kind + ",local#" + site.local + ",opcode="
                    + zkmOpcodeName(site.opcode) + ",domain="
                    + GuardDomain.describe(decision.domain)
                    + ",gate=" + (diagnosticSites.contains(site)
                    ? "repeated_residual_group+" : "local_guard+")
                    + "path_fixed_point+exception_edges";
            if (!decision.taken) {
                method.instructions.remove(site.load);
                method.instructions.remove(site.jump);
                rows.add(row(owner, method.name + method.desc, offset,
                        site.residual() ? "zkm-path-remove-residual-guard"
                                : "zkm-path-remove-false-guard", reason));
            } else if (hasFallthroughFrame(site.jump)) {
                JumpInsnNode replacement = new JumpInsnNode(Opcodes.GOTO, site.jump.label);
                method.instructions.insertBefore(site.load, replacement);
                offsets.put(replacement, offset);
                method.instructions.remove(site.load);
                method.instructions.remove(site.jump);
                rows.add(row(owner, method.name + method.desc, offset,
                        "zkm-path-restore-goto", reason + ",fallthrough_frame=present"));
            } else {
                AbstractInsnNode replacement = takenGuardConstant(site.opcode);
                method.instructions.set(site.load, replacement);
                offsets.put(replacement, offsetOf(site.load, offsets, method));
                rows.add(row(owner, method.name + method.desc, offset,
                        "zkm-path-pin-taken-guard",
                        reason + ",fallthrough_frame=absent,preserved_stackmap_shape=true"));
            }
            changed = true;
        }
        return changed;
    }

    /**
     * Collects the narrow structural sentinel shape used by ZKM. These plans
     * are never consumed by the default mode because structure alone does not
     * prove a mutable sentinel's runtime value.
     */
    private static List<ZkmAssumptionPlan> collectZkmAssumptionPlans(
            MethodNode method,
            Frame<org.objectweb.asm.tree.analysis.BasicValue>[] frames,
            ZkmProvenanceIndex provenance,
            String owner) {
        Map<String, List<ZkmGuardSite>> byLocal = new LinkedHashMap<>();
        int instructionIndex = 0;
        for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
             insn = insn.getNext(), instructionIndex++) {
            if (!(insn instanceof JumpInsnNode)) continue;
            String kind = zkmGuardKind(insn.getOpcode());
            if (kind == null || !(insn.getPrevious() instanceof VarInsnNode)) continue;
            VarInsnNode load = (VarInsnNode) insn.getPrevious();
            if (load.getOpcode() != zkmLoadOpcode(kind)) continue;
            Frame<?> frame = instructionIndex < frames.length ? frames[instructionIndex] : null;
            if (frame == null || frame.getStackSize() < 1) continue;
            ZkmGuardSite site = new ZkmGuardSite(load, (JumpInsnNode) insn, kind,
                    load.var, insn.getOpcode(), frame.getStackSize());
            byLocal.computeIfAbsent(site.localKey(), ignored -> new ArrayList<>()).add(site);
        }

        List<ZkmAssumptionPlan> result = new ArrayList<>();
        for (List<ZkmGuardSite> sites : byLocal.values()) {
            ZkmGuardSite first = sites.get(0);
            if (isParameterSlot(method, first.local)) continue;
            Map<Integer, Integer> residualCounts = new LinkedHashMap<>();
            for (ZkmGuardSite site : sites) {
                if (site.residual()) {
                    residualCounts.put(site.opcode,
                            residualCounts.getOrDefault(site.opcode, 0) + 1);
                }
            }
            Integer assumedFalseOpcode = null;
            String evidence = "repeated_residual_unique_opcode";
            for (Map.Entry<Integer, Integer> count : residualCounts.entrySet()) {
                if (count.getValue() < 2) continue;
                if (assumedFalseOpcode != null) {
                    assumedFalseOpcode = null;
                    break;
                }
                assumedFalseOpcode = count.getKey();
            }
            boolean valid = true, hasOpposite = false;
            int stores = 0;
            VarInsnNode sentinelStore = null;
            Map<AbstractInsnNode, Integer> positions = instructionIndexes(method);
            int lastGuardPosition = -1;
            Set<AbstractInsnNode> guardLoads = Collections.newSetFromMap(
                    new IdentityHashMap<AbstractInsnNode, Boolean>());
            for (ZkmGuardSite site : sites) {
                guardLoads.add(site.load);
                Integer position = positions.get(site.jump);
                if (position != null) lastGuardPosition = Math.max(lastGuardPosition, position);
            }
            if (hasControlFlowBackIntoPrefix(method, positions, lastGuardPosition)) continue;
            int expectedStore = "int".equals(first.kind) ? Opcodes.ISTORE : Opcodes.ASTORE;
            int expectedLoad = zkmLoadOpcode(first.kind);
            for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
                 insn = insn.getNext()) {
                Integer position = positions.get(insn);
                if (position != null && position > lastGuardPosition) continue;
                if (insn instanceof IincInsnNode
                        && ((IincInsnNode) insn).var == first.local) {
                    valid = false;
                    break;
                }
                if (!(insn instanceof VarInsnNode)) continue;
                VarInsnNode var = (VarInsnNode) insn;
                if ((var.getOpcode() == Opcodes.LSTORE
                        || var.getOpcode() == Opcodes.DSTORE)
                        && var.var + 1 == first.local) {
                    valid = false;
                    break;
                }
                if (var.var != first.local) continue;
                if (var.getOpcode() == expectedStore) {
                    stores++;
                    sentinelStore = var;
                } else if (var.getOpcode() != expectedLoad || !guardLoads.contains(var)) {
                    valid = false;
                    break;
                }
            }
            if (valid && stores == 1) {
                ZkmSentinelSeedDecision seed = provenance.initializerHintForStore(
                        owner, method, sentinelStore, lastGuardPosition);
                int hintedOpcode = falseOpcodeForValue(first.kind, seed.value);
                if (hintedOpcode != -1
                        && residualCounts.getOrDefault(hintedOpcode, 0) >= 2) {
                    assumedFalseOpcode = hintedOpcode;
                    evidence = "archive_clinit_seed=" + seed.value
                            + "+post_guard_self_write";
                }
            }
            if (assumedFalseOpcode == null) continue;
            int opposite = oppositeZkmOpcode(assumedFalseOpcode);
            for (ZkmGuardSite site : sites) {
                if (site.residual() && site.opcode != assumedFalseOpcode
                        && !evidence.startsWith("archive_clinit_seed=")) {
                    valid = false;
                }
                if (site.opcode == opposite) hasOpposite = true;
            }
            if (valid && stores == 1 && hasOpposite) {
                result.add(new ZkmAssumptionPlan(first.kind, first.local,
                        assumedFalseOpcode, sites, evidence,
                        evidence.startsWith("archive_clinit_seed=")
                                ? "clinit-seed+post-guard-self-write;"
                                + "integer-overflow/repeated-invocation-not-formally-excluded"
                                : "structural_zkm_sentinel_not_semantic_proof"));
            }
        }
        return result;
    }

    private static boolean hasControlFlowBackIntoPrefix(
            MethodNode method, Map<AbstractInsnNode, Integer> positions,
            int lastPrefixPosition) {
        for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
             insn = insn.getNext()) {
            Integer source = positions.get(insn);
            if (source == null || source <= lastPrefixPosition) continue;
            if (insn instanceof JumpInsnNode) {
                Integer target = positions.get(((JumpInsnNode) insn).label);
                if (target != null && target <= lastPrefixPosition) return true;
            } else if (insn instanceof TableSwitchInsnNode) {
                TableSwitchInsnNode table = (TableSwitchInsnNode) insn;
                if (targetsPrefix(table.dflt, table.labels, positions,
                        lastPrefixPosition)) return true;
            } else if (insn instanceof LookupSwitchInsnNode) {
                LookupSwitchInsnNode lookup = (LookupSwitchInsnNode) insn;
                if (targetsPrefix(lookup.dflt, lookup.labels, positions,
                        lastPrefixPosition)) return true;
            }
        }
        for (TryCatchBlockNode block : method.tryCatchBlocks) {
            Integer start = positions.get(block.start);
            Integer end = positions.get(block.end);
            Integer handler = positions.get(block.handler);
            if (start != null && end != null && handler != null
                    && end > lastPrefixPosition + 1
                    && handler <= lastPrefixPosition) return true;
        }
        return false;
    }

    private static boolean targetsPrefix(
            LabelNode dflt, List<LabelNode> labels,
            Map<AbstractInsnNode, Integer> positions, int lastPrefixPosition) {
        Integer target = positions.get(dflt);
        if (target != null && target <= lastPrefixPosition) return true;
        for (LabelNode label : labels) {
            target = positions.get(label);
            if (target != null && target <= lastPrefixPosition) return true;
        }
        return false;
    }

    private static int falseOpcodeForValue(String kind, ProvenValue value) {
        if (value == null || value.isUnknown()) return -1;
        if ("int".equals(kind) && value.isInteger()) {
            return value.integer == 0 ? Opcodes.IFNE : Opcodes.IFEQ;
        }
        if ("null".equals(kind)) {
            if (value.kind == ProvenValue.NULL_KIND) return Opcodes.IFNONNULL;
            if (value.kind == ProvenValue.NONNULL_KIND) return Opcodes.IFNULL;
        }
        return -1;
    }

    private static boolean rewriteAssumedZkmSentinels(
            MethodNode method,
            List<ZkmAssumptionPlan> plans,
            String owner,
            List<String> rows,
            Map<AbstractInsnNode, Integer> offsets) {
        boolean changed = false;
        for (ZkmAssumptionPlan plan : plans) {
            String reason = "kind=" + plan.kind + ",local#" + plan.local
                    + ",assumed_false_opcode=" + zkmOpcodeName(plan.assumedFalseOpcode)
                    + ",gate=non_parameter+single_store+guard_only+"
                    + "repeated_residual+opposite_guard"
                    + ",evidence=" + plan.evidence
                    + ",assumption=" + plan.assumption;
            for (ZkmGuardSite site : plan.sites) {
                if (method.instructions.indexOf(site.load) < 0
                        || method.instructions.indexOf(site.jump) < 0) continue;
                int offset = offsetOf(site.jump, offsets, method);
                if (site.opcode == plan.assumedFalseOpcode) {
                    method.instructions.remove(site.load);
                    method.instructions.remove(site.jump);
                    rows.add(row(owner, method.name + method.desc, offset,
                            site.residual() ? "zkm-assumed-remove-residual-guard"
                                    : "zkm-assumed-remove-false-guard", reason));
                } else if (site.opcode == oppositeZkmOpcode(plan.assumedFalseOpcode)) {
                    if (hasFallthroughFrame(site.jump)) {
                        JumpInsnNode replacement = new JumpInsnNode(Opcodes.GOTO,
                                site.jump.label);
                        method.instructions.insertBefore(site.load, replacement);
                        offsets.put(replacement, offset);
                        method.instructions.remove(site.load);
                        method.instructions.remove(site.jump);
                        rows.add(row(owner, method.name + method.desc, offset,
                                "zkm-assumed-restore-goto", reason));
                    } else {
                        AbstractInsnNode replacement = takenGuardConstant(site.opcode);
                        method.instructions.set(site.load, replacement);
                        offsets.put(replacement, offsetOf(site.load, offsets, method));
                        rows.add(row(owner, method.name + method.desc, offset,
                                "zkm-assumed-pin-taken-guard",
                                reason + ",preserved_stackmap_shape=true"));
                    }
                } else {
                    continue;
                }
                changed = true;
            }
        }
        return changed;
    }

    /**
     * Splits crossing protected intervals at existing boundaries. For every
     * executable instruction the ordered handler list remains byte-for-byte
     * equivalent; only the interval representation becomes laminar.
     */
    private static boolean normalizeCrossingExceptionRanges(
            MethodNode method,
            String owner,
            List<String> rows,
            Map<AbstractInsnNode, Integer> offsets) {
        if (method.tryCatchBlocks == null || method.tryCatchBlocks.size() < 2) return false;
        for (TryCatchBlockNode block : method.tryCatchBlocks) {
            if (block.visibleTypeAnnotations != null && !block.visibleTypeAnnotations.isEmpty()
                    || block.invisibleTypeAnnotations != null
                            && !block.invisibleTypeAnnotations.isEmpty()) {
                rows.add(row(owner, method.name + method.desc, -1,
                        "exception-range-skip-annotations",
                        "try_catch_type_annotations_present=true"));
                return false;
            }
        }
        Map<AbstractInsnNode, Integer> positions = instructionIndexes(method);
        boolean crossing = false;
        for (int left = 0; left < method.tryCatchBlocks.size() && !crossing; left++) {
            TryCatchBlockNode a = method.tryCatchBlocks.get(left);
            Integer as = positions.get(a.start), ae = positions.get(a.end);
            if (as == null || ae == null) continue;
            for (int right = left + 1; right < method.tryCatchBlocks.size(); right++) {
                TryCatchBlockNode b = method.tryCatchBlocks.get(right);
                Integer bs = positions.get(b.start), be = positions.get(b.end);
                if (bs == null || be == null) continue;
                if (as < bs && bs < ae && ae < be
                        || bs < as && as < be && be < ae) {
                    crossing = true;
                    break;
                }
            }
        }
        if (!crossing) return false;

        List<LabelNode> boundaries = new ArrayList<>();
        Set<LabelNode> seen = Collections.newSetFromMap(
                new IdentityHashMap<LabelNode, Boolean>());
        for (TryCatchBlockNode block : method.tryCatchBlocks) {
            if (seen.add(block.start)) boundaries.add(block.start);
            if (seen.add(block.end)) boundaries.add(block.end);
        }
        boundaries.sort(Comparator.comparingInt(label -> positions.get(label)));

        List<TryCatchBlockNode> original = new ArrayList<>(method.tryCatchBlocks);
        List<TryCatchBlockNode> split = new ArrayList<>();
        for (int boundary = 0; boundary + 1 < boundaries.size(); boundary++) {
            LabelNode start = boundaries.get(boundary);
            LabelNode end = boundaries.get(boundary + 1);
            int startPosition = positions.get(start);
            int endPosition = positions.get(end);
            if (startPosition >= endPosition || !containsExecutable(start, end)) continue;
            for (TryCatchBlockNode block : original) {
                int blockStart = positions.get(block.start);
                int blockEnd = positions.get(block.end);
                if (blockStart <= startPosition && endPosition <= blockEnd) {
                    split.add(new TryCatchBlockNode(start, end, block.handler, block.type));
                }
            }
        }
        if (!sameExceptionCoverage(method, original, split, positions)) {
            throw new IllegalStateException("exception coverage changed during normalization");
        }
        method.tryCatchBlocks.clear();
        method.tryCatchBlocks.addAll(split);
        rows.add(row(owner, method.name + method.desc,
                offsetOf(boundaries.get(0), offsets, method),
                "normalize-exception-ranges",
                "crossing=true,original_ranges=" + original.size()
                        + ",atomic_ranges=" + split.size()
                        + ",ordered_instruction_coverage=equal"));
        return true;
    }

    private static boolean removeIdentityRethrowHandlers(
            MethodNode method,
            ZkmProvenanceIndex provenance,
            ArchiveHierarchy hierarchy,
            String owner,
            List<String> rows,
            Map<AbstractInsnNode, Integer> offsets) {
        if (method.tryCatchBlocks == null || method.tryCatchBlocks.isEmpty()) return false;
        Map<AbstractInsnNode, Integer> positions = instructionIndexes(method);
        List<IdentityRethrowHandler> handlers = new ArrayList<>();
        for (TryCatchBlockNode block : method.tryCatchBlocks) {
            handlers.add(identityRethrowHandler(method, block, positions, provenance,
                    hierarchy, owner));
        }

        List<Set<Integer>> interactions = new ArrayList<>();
        for (int index = 0; index < handlers.size(); index++) {
            interactions.add(new LinkedHashSet<Integer>());
        }
        for (int left = 0; left < handlers.size(); left++) {
            for (int right = left + 1; right < handlers.size(); right++) {
                if (!handlersInteract(method, handlers.get(left), handlers.get(right),
                        positions)) continue;
                interactions.get(left).add(right);
                interactions.get(right).add(left);
            }
        }

        boolean synchronizedMethod = (method.access & Opcodes.ACC_SYNCHRONIZED) != 0;
        boolean explicitMonitor = containsMonitorInstruction(method);
        Set<Integer> visited = new HashSet<>();
        List<TryCatchBlockNode> removable = new ArrayList<>();
        for (int seed = 0; seed < handlers.size(); seed++) {
            if (!handlers.get(seed).identity || visited.contains(seed)) continue;
            Set<Integer> component = handlerInteractionClosure(seed, interactions);
            visited.addAll(component);

            int identities = 0;
            boolean catchAll = false;
            boolean annotated = false;
            Set<Integer> identityIndexes = new LinkedHashSet<>();
            for (Integer index : component) {
                IdentityRethrowHandler handler = handlers.get(index);
                if (handler.identity) {
                    identities++;
                    identityIndexes.add(index);
                }
                catchAll |= handler.block.type == null;
                annotated |= handler.annotated;
            }
            boolean allIdentity = identities == component.size();
            boolean externalEntry = hasExternalHandlerEntry(method, handlers,
                    identityIndexes);
            boolean rethrowCycle = hasIdentityRethrowCycle(handlers, identityIndexes,
                    positions, hierarchy);
            boolean monitorTransparent = identityBodiesAreMonitorTransparent(
                    handlers, identityIndexes);
            IdentityBypassProof bypass = allIdentity
                    ? IdentityBypassProof.proven(0)
                    : proveEquivalentIdentityBypass(method, handlers, identityIndexes,
                            positions, hierarchy);
            if (!bypass.equivalent || rethrowCycle || annotated || externalEntry
                    || !monitorTransparent) {
                rows.add(row(owner, method.name + method.desc,
                        offsetOf(handlers.get(seed).block.start, offsets, method),
                        "identity-rethrow-component-skip",
                        "handlers=" + component.size()
                                + ",identity_handlers=" + identities
                                + ",catch_all=" + catchAll
                                + ",annotated=" + annotated
                                + ",external_entry=" + externalEntry
                                + ",identity_rethrow_cycle=" + rethrowCycle
                                + ",synchronized=" + synchronizedMethod
                                + ",monitor=" + explicitMonitor
                                + ",monitor_transparent=" + monitorTransparent
                                + ",ordered_residual_handlers="
                                + (bypass.equivalent ? "equal" : "different")
                                + ",checked_instructions=" + bypass.checkedInstructions
                                + (bypass.equivalent ? ""
                                : ",mismatch_instruction=" + bypass.mismatchPosition)));
                continue;
            }
            for (Integer index : identityIndexes) {
                removable.add(handlers.get(index).block);
            }
            rows.add(row(owner, method.name + method.desc,
                    offsetOf(handlers.get(seed).block.start, offsets, method),
                    "remove-identity-rethrow-handlers",
                    "handlers=" + identityIndexes.size()
                            + ",component_handlers=" + component.size()
                            + ",component_closure=complete"
                            + ",helper=proven_same_class_aload0_areturn"
                            + ",ordered_residual_handlers="
                            + (allIdentity ? "empty_component" : "equal")
                            + ",checked_instructions=" + bypass.checkedInstructions
                            + ",catch_all=" + catchAll
                            + ",catch_all_retained=" + catchAll
                            + ",external_entry=false"
                            + ",identity_rethrow_cycle=false,synchronized="
                            + synchronizedMethod + ",monitor=" + explicitMonitor
                            + ",monitor_transparent=true"));
        }
        if (removable.isEmpty()) return false;
        method.tryCatchBlocks.removeAll(removable);
        return true;
    }

    /**
     * An identity handler may be removed from a synchronized/monitoring method
     * only when its own body cannot change monitor ownership. The residual
     * handler-vector proof then compares the original throw site with the
     * identity ATHROW site, so real catch-all/finally monitor exits remain.
     */
    private static boolean identityBodiesAreMonitorTransparent(
            List<IdentityRethrowHandler> handlers,
            Set<Integer> selected) {
        for (Integer index : selected) {
            IdentityRethrowHandler handler = handlers.get(index);
            for (AbstractInsnNode instruction : handler.body) {
                int opcode = instruction.getOpcode();
                if (opcode == Opcodes.MONITORENTER
                        || opcode == Opcodes.MONITOREXIT
                        || opcode == Opcodes.JSR
                        || opcode == Opcodes.RET) {
                    return false;
                }
            }
        }
        return true;
    }

    private static boolean hasIdentityRethrowCycle(
            List<IdentityRethrowHandler> handlers,
            Set<Integer> selected,
            Map<AbstractInsnNode, Integer> positions,
            ArchiveHierarchy hierarchy) {
        Map<Integer, Set<Integer>> edges = new LinkedHashMap<>();
        for (Integer sourceIndex : selected) {
            IdentityRethrowHandler source = handlers.get(sourceIndex);
            Set<Integer> targets = new LinkedHashSet<>();
            for (Integer targetIndex : selected) {
                IdentityRethrowHandler target = handlers.get(targetIndex);
                if (protects(target, source.rethrow, positions)
                        && hierarchy.mayShareThrowableSubtype(
                                source.block.type, target.block.type)) {
                    targets.add(targetIndex);
                }
            }
            edges.put(sourceIndex, targets);
        }
        Set<Integer> visiting = new HashSet<>();
        Set<Integer> complete = new HashSet<>();
        for (Integer node : selected) {
            if (identityRethrowCycleFrom(node, edges, visiting, complete)) return true;
        }
        return false;
    }

    private static boolean identityRethrowCycleFrom(
            Integer node,
            Map<Integer, Set<Integer>> edges,
            Set<Integer> visiting,
            Set<Integer> complete) {
        if (complete.contains(node)) return false;
        if (!visiting.add(node)) return true;
        for (Integer target : edges.getOrDefault(node,
                Collections.<Integer>emptySet())) {
            if (identityRethrowCycleFrom(target, edges, visiting, complete)) return true;
        }
        visiting.remove(node);
        complete.add(node);
        return false;
    }

    private static IdentityBypassProof proveEquivalentIdentityBypass(
            MethodNode method,
            List<IdentityRethrowHandler> handlers,
            Set<Integer> selected,
            Map<AbstractInsnNode, Integer> positions,
            ArchiveHierarchy hierarchy) {
        Set<TryCatchBlockNode> removed = Collections.newSetFromMap(
                new IdentityHashMap<TryCatchBlockNode, Boolean>());
        for (Integer index : selected) removed.add(handlers.get(index).block);
        List<TryCatchBlockNode> residual = new ArrayList<>();
        for (TryCatchBlockNode block : method.tryCatchBlocks) {
            if (!removed.contains(block)) residual.add(block);
        }

        int checked = 0;
        for (Integer index : selected) {
            IdentityRethrowHandler handler = handlers.get(index);
            Integer rethrowPosition = positions.get(handler.rethrow);
            if (rethrowPosition == null) {
                return IdentityBypassProof.mismatch(checked, -1);
            }
            List<String> rethrowHandlers = handlerSignature(residual,
                    rethrowPosition, positions, handler.block.type, hierarchy);
            for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
                 insn = insn.getNext()) {
                if (insn.getOpcode() < 0) continue;
                Integer position = positions.get(insn);
                if (position == null || position < handler.start
                        || position >= handler.end) continue;
                checked++;
                if (!handlerSignature(residual, position, positions,
                        handler.block.type, hierarchy)
                        .equals(rethrowHandlers)) {
                    return IdentityBypassProof.mismatch(checked, position);
                }
            }
        }
        return IdentityBypassProof.proven(checked);
    }

    private static IdentityRethrowHandler identityRethrowHandler(
            MethodNode method,
            TryCatchBlockNode block,
            Map<AbstractInsnNode, Integer> positions,
            ZkmProvenanceIndex provenance,
            ArchiveHierarchy hierarchy,
            String owner) {
        Integer start = positions.get(block.start);
        Integer end = positions.get(block.end);
        AbstractInsnNode first = nextCode(block.handler);
        MethodInsnNode call = first instanceof MethodInsnNode
                ? (MethodInsnNode) first : null;
        AbstractInsnNode rethrow = call == null ? null : nextCode(call);
        List<AbstractInsnNode> identityBody = new ArrayList<>();
        if (call != null) {
            identityBody.add(call);
            if (rethrow != null) identityBody.add(rethrow);
        } else if (first instanceof VarInsnNode
                && first.getOpcode() == Opcodes.ASTORE) {
            VarInsnNode store = (VarInsnNode) first;
            AbstractInsnNode loadInsn = nextCode(store);
            AbstractInsnNode callInsn = loadInsn == null ? null : nextCode(loadInsn);
            AbstractInsnNode throwInsn = callInsn == null ? null : nextCode(callInsn);
            if (loadInsn instanceof VarInsnNode
                    && loadInsn.getOpcode() == Opcodes.ALOAD
                    && ((VarInsnNode) loadInsn).var == store.var
                    && callInsn instanceof MethodInsnNode
                    && throwInsn != null && throwInsn.getOpcode() == Opcodes.ATHROW) {
                call = (MethodInsnNode) callInsn;
                rethrow = throwInsn;
                identityBody.add(store);
                identityBody.add(loadInsn);
                identityBody.add(callInsn);
                identityBody.add(throwInsn);
            }
        }
        boolean annotated = block.visibleTypeAnnotations != null
                && !block.visibleTypeAnnotations.isEmpty()
                || block.invisibleTypeAnnotations != null
                        && !block.invisibleTypeAnnotations.isEmpty();
        boolean identity = start != null && end != null && start < end
                && block.type != null && !annotated
                && call != null && call.getOpcode() == Opcodes.INVOKESTATIC
                && rethrow != null && rethrow.getOpcode() == Opcodes.ATHROW;
        if (identity) {
            Type[] arguments = Type.getArgumentTypes(call.desc);
            Type result = Type.getReturnType(call.desc);
            boolean matchingReference = arguments.length == 1
                    && arguments[0].getSort() == Type.OBJECT
                    && arguments[0].equals(result);
            String identityType = matchingReference ? arguments[0].getInternalName() : null;
            identity = matchingReference
                    && hierarchy.isAssignableFrom(identityType, block.type)
                    && owner.equals(call.owner)
                    && provenance.identityReferenceMethods.contains(
                            new MethodRef(call.owner, call.name, call.desc));
        }
        if (!identity) {
            identityBody.clear();
            if (first != null) identityBody.add(first);
        }
        return new IdentityRethrowHandler(block,
                start == null ? -1 : start,
                end == null ? -1 : end,
                first, identity ? rethrow : null, identityBody, annotated, identity);
    }

    private static boolean handlersInteract(
            MethodNode method,
            IdentityRethrowHandler left,
            IdentityRethrowHandler right,
            Map<AbstractInsnNode, Integer> positions) {
        if (left.start < 0 || right.start < 0) return true;
        int overlapStart = Math.max(left.start, right.start);
        int overlapEnd = Math.min(left.end, right.end);
        if (overlapStart < overlapEnd
                && containsExecutable(method, overlapStart, overlapEnd, positions)) return true;
        if (left.first != null && right.first != null && left.first == right.first) return true;
        return protectsAny(left, right.body, positions)
                || protectsAny(right, left.body, positions);
    }

    private static boolean protectsAny(
            IdentityRethrowHandler handler,
            List<AbstractInsnNode> instructions,
            Map<AbstractInsnNode, Integer> positions) {
        for (AbstractInsnNode instruction : instructions) {
            if (protects(handler, instruction, positions)) return true;
        }
        return false;
    }

    private static boolean protects(
            IdentityRethrowHandler handler,
            AbstractInsnNode instruction,
            Map<AbstractInsnNode, Integer> positions) {
        if (instruction == null || handler.start < 0) return false;
        Integer position = positions.get(instruction);
        return position != null && handler.start <= position && position < handler.end;
    }

    private static boolean containsExecutable(
            MethodNode method,
            int start,
            int end,
            Map<AbstractInsnNode, Integer> positions) {
        for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
             insn = insn.getNext()) {
            Integer position = positions.get(insn);
            if (position != null && position >= end) return false;
            if (position != null && position >= start && insn.getOpcode() >= 0) return true;
        }
        return false;
    }

    private static Set<Integer> handlerInteractionClosure(
            int seed,
            List<Set<Integer>> interactions) {
        Set<Integer> component = new LinkedHashSet<>();
        ArrayDeque<Integer> work = new ArrayDeque<>();
        work.add(seed);
        while (!work.isEmpty()) {
            Integer current = work.removeFirst();
            if (!component.add(current)) continue;
            work.addAll(interactions.get(current));
        }
        return component;
    }

    private static boolean hasExternalHandlerEntry(
            MethodNode method,
            List<IdentityRethrowHandler> handlers,
            Set<Integer> component) {
        Set<AbstractInsnNode> body = Collections.newSetFromMap(
                new IdentityHashMap<AbstractInsnNode, Boolean>());
        Set<TryCatchBlockNode> componentBlocks = Collections.newSetFromMap(
                new IdentityHashMap<TryCatchBlockNode, Boolean>());
        for (Integer index : component) {
            IdentityRethrowHandler handler = handlers.get(index);
            body.addAll(handler.body);
            componentBlocks.add(handler.block);
        }
        for (IdentityRethrowHandler handler : handlers) {
            if (!componentBlocks.contains(handler.block) && body.contains(handler.first)) {
                return true;
            }
        }
        for (Integer index : component) {
            AbstractInsnNode first = handlers.get(index).first;
            AbstractInsnNode previous = previousCode(first);
            if (previous == null || canFallThrough(previous) && !body.contains(previous)) {
                return true;
            }
        }
        for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
             insn = insn.getNext()) {
            if (insn instanceof JumpInsnNode) {
                if (body.contains(nextCode(((JumpInsnNode) insn).label))) return true;
            } else if (insn instanceof TableSwitchInsnNode) {
                TableSwitchInsnNode table = (TableSwitchInsnNode) insn;
                if (body.contains(nextCode(table.dflt))) return true;
                for (LabelNode label : table.labels) {
                    if (body.contains(nextCode(label))) return true;
                }
            } else if (insn instanceof LookupSwitchInsnNode) {
                LookupSwitchInsnNode lookup = (LookupSwitchInsnNode) insn;
                if (body.contains(nextCode(lookup.dflt))) return true;
                for (LabelNode label : lookup.labels) {
                    if (body.contains(nextCode(label))) return true;
                }
            }
        }
        return false;
    }

    private static AbstractInsnNode previousCode(AbstractInsnNode instruction) {
        if (instruction == null) return null;
        AbstractInsnNode previous = instruction.getPrevious();
        while (previous != null && previous.getOpcode() < 0) previous = previous.getPrevious();
        return previous;
    }

    private static boolean containsMonitorInstruction(MethodNode method) {
        for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
             insn = insn.getNext()) {
            if (insn.getOpcode() == Opcodes.MONITORENTER
                    || insn.getOpcode() == Opcodes.MONITOREXIT) return true;
        }
        return false;
    }

    private static final class IdentityRethrowHandler {
        final TryCatchBlockNode block;
        final int start;
        final int end;
        final AbstractInsnNode first;
        final AbstractInsnNode rethrow;
        final List<AbstractInsnNode> body;
        final boolean annotated;
        final boolean identity;

        IdentityRethrowHandler(
                TryCatchBlockNode block,
                int start,
                int end,
                AbstractInsnNode first,
                AbstractInsnNode rethrow,
                List<AbstractInsnNode> body,
                boolean annotated,
                boolean identity) {
            this.block = block;
            this.start = start;
            this.end = end;
            this.first = first;
            this.rethrow = rethrow;
            this.body = body;
            this.annotated = annotated;
            this.identity = identity;
        }
    }

    private static final class IdentityBypassProof {
        final boolean equivalent;
        final int checkedInstructions;
        final int mismatchPosition;

        private IdentityBypassProof(
                boolean equivalent, int checkedInstructions, int mismatchPosition) {
            this.equivalent = equivalent;
            this.checkedInstructions = checkedInstructions;
            this.mismatchPosition = mismatchPosition;
        }

        static IdentityBypassProof proven(int checkedInstructions) {
            return new IdentityBypassProof(true, checkedInstructions, -1);
        }

        static IdentityBypassProof mismatch(int checkedInstructions,
                                            int mismatchPosition) {
            return new IdentityBypassProof(false, checkedInstructions,
                    mismatchPosition);
        }
    }

    private static boolean containsExecutable(LabelNode start, LabelNode end) {
        for (AbstractInsnNode insn = start; insn != null && insn != end;
             insn = insn.getNext()) {
            if (insn.getOpcode() >= 0) return true;
        }
        return false;
    }

    private static boolean removeEmptyTryCatchBlocks(
            MethodNode method,
            String owner,
            List<String> rows,
            Map<AbstractInsnNode, Integer> offsets) {
        List<TryCatchBlockNode> empty = new ArrayList<>();
        for (TryCatchBlockNode block : method.tryCatchBlocks) {
            if (!containsExecutable(block.start, block.end)) empty.add(block);
        }
        if (empty.isEmpty()) return false;
        int firstOffset = offsetOf(empty.get(0).start, offsets, method);
        method.tryCatchBlocks.removeAll(empty);
        rows.add(row(owner, method.name + method.desc, firstOffset,
                "remove-empty-exception-ranges",
                "ranges=" + empty.size() + ",executable_instructions=0"));
        return true;
    }

    private static boolean sameExceptionCoverage(
            MethodNode method,
            List<TryCatchBlockNode> before,
            List<TryCatchBlockNode> after,
            Map<AbstractInsnNode, Integer> positions) {
        for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
             insn = insn.getNext()) {
            if (insn.getOpcode() < 0) continue;
            int position = positions.get(insn);
            List<String> left = handlerSignature(before, position, positions);
            List<String> right = handlerSignature(after, position, positions);
            if (!left.equals(right)) return false;
        }
        return true;
    }

    private static List<String> handlerSignature(
            List<TryCatchBlockNode> blocks,
            int position,
            Map<AbstractInsnNode, Integer> positions) {
        List<String> result = new ArrayList<>();
        for (TryCatchBlockNode block : blocks) {
            Integer start = positions.get(block.start), end = positions.get(block.end);
            if (start != null && end != null && start <= position && position < end) {
                result.add((block.type == null ? "*" : block.type) + "@"
                        + positions.get(block.handler));
            }
        }
        return result;
    }

    private static List<String> handlerSignature(
            List<TryCatchBlockNode> blocks,
            int position,
            Map<AbstractInsnNode, Integer> positions,
            String thrownType,
            ArchiveHierarchy hierarchy) {
        List<String> result = new ArrayList<>();
        for (TryCatchBlockNode block : blocks) {
            Integer start = positions.get(block.start), end = positions.get(block.end);
            if (start == null || end == null || position < start || position >= end) {
                continue;
            }
            if (block.type != null
                    && !hierarchy.mayShareThrowableSubtype(thrownType, block.type)) {
                continue;
            }
            result.add((block.type == null ? "*" : block.type) + "@"
                    + positions.get(block.handler));
        }
        return result;
    }

    private static GuardPathFacts analyzeGuardLocal(
            MethodNode method, String kind, int local,
            Map<AbstractInsnNode, Integer> indexes,
            Map<AbstractInsnNode, List<LabelNode>> handlers,
            Frame<SourceValue>[] sourceFrames,
            ZkmProvenanceIndex provenance,
            String owner) {
        AbstractInsnNode[] instructions = method.instructions.toArray();
        int[] before = new int[instructions.length];
        ArrayDeque<Integer> work = new ArrayDeque<>();
        AbstractInsnNode first = ZkmProvenanceIndex.firstCode(method);
        Integer firstIndex = indexes.get(first);
        if (firstIndex == null) return new GuardPathFacts(before);
        before[firstIndex] = isParameterSlot(method, local)
                ? GuardDomain.BOTH : GuardDomain.UNINITIALIZED;
        work.add(firstIndex);
        int iterations = 0;
        while (!work.isEmpty()) {
            if (++iterations > Math.max(4096, instructions.length * 64)) {
                return new GuardPathFacts(new int[instructions.length]);
            }
            int index = work.removeFirst();
            AbstractInsnNode insn = instructions[index];
            int input = before[index];

            List<LabelNode> catches = handlers.get(insn);
            if (catches != null) {
                for (LabelNode handler : catches) {
                    propagate(before, work, indexes.get(nextCode(handler)), input);
                }
            }

            int output = input;
            if (insn instanceof VarInsnNode) {
                VarInsnNode var = (VarInsnNode) insn;
                if (var.var == local && (var.getOpcode() == Opcodes.ISTORE
                        || var.getOpcode() == Opcodes.ASTORE)) {
                    boolean matching = "int".equals(kind)
                            ? var.getOpcode() == Opcodes.ISTORE
                            : var.getOpcode() == Opcodes.ASTORE;
                    ProvenValue value = matching
                            ? provenance.valueForStore(owner, method, var, sourceFrames, indexes)
                            : null;
                    output = matching && value != null
                            ? GuardDomain.fromValue(value) : GuardDomain.BOTH;
                } else if (overwritesLocal(var, local)) {
                    output = GuardDomain.ALL;
                }
            } else if (insn instanceof IincInsnNode
                    && ((IincInsnNode) insn).var == local) {
                output = GuardDomain.BOTH;
            }

            int opcode = insn.getOpcode();
            if (opcode == Opcodes.ATHROW || opcode >= Opcodes.IRETURN
                    && opcode <= Opcodes.RETURN) continue;
            if (insn instanceof JumpInsnNode) {
                JumpInsnNode jump = (JumpInsnNode) insn;
                if (opcode == Opcodes.GOTO) {
                    propagate(before, work, indexes.get(nextCode(jump.label)), output);
                    continue;
                }
                boolean tracksLocal = insn.getPrevious() instanceof VarInsnNode
                        && ((VarInsnNode) insn.getPrevious()).var == local
                        && ((VarInsnNode) insn.getPrevious()).getOpcode()
                                == zkmLoadOpcode(kind)
                        && kind.equals(zkmGuardKind(opcode));
                if (tracksLocal) {
                    int uninitialized = output & GuardDomain.UNINITIALIZED;
                    int taken = output & GuardDomain.truthMask(opcode) | uninitialized;
                    int fall = output & GuardDomain.falseMask(opcode) | uninitialized;
                    propagate(before, work, indexes.get(nextCode(jump.label)), taken);
                    propagate(before, work, indexes.get(nextCode(insn)), fall);
                } else {
                    propagate(before, work, indexes.get(nextCode(jump.label)), output);
                    propagate(before, work, indexes.get(nextCode(insn)), output);
                }
            } else if (insn instanceof TableSwitchInsnNode) {
                TableSwitchInsnNode table = (TableSwitchInsnNode) insn;
                propagate(before, work, indexes.get(nextCode(table.dflt)), output);
                for (LabelNode label : table.labels) {
                    propagate(before, work, indexes.get(nextCode(label)), output);
                }
            } else if (insn instanceof LookupSwitchInsnNode) {
                LookupSwitchInsnNode lookup = (LookupSwitchInsnNode) insn;
                propagate(before, work, indexes.get(nextCode(lookup.dflt)), output);
                for (LabelNode label : lookup.labels) {
                    propagate(before, work, indexes.get(nextCode(label)), output);
                }
            } else {
                propagate(before, work, indexes.get(nextCode(insn)), output);
            }
        }
        return new GuardPathFacts(before);
    }

    private static boolean overwritesLocal(VarInsnNode insn, int local) {
        int opcode = insn.getOpcode();
        if (opcode >= Opcodes.ISTORE && opcode <= Opcodes.ASTORE) {
            if (insn.var == local) return true;
            return (opcode == Opcodes.LSTORE || opcode == Opcodes.DSTORE)
                    && insn.var + 1 == local;
        }
        return false;
    }

    private static void propagate(int[] states, ArrayDeque<Integer> work,
                                  Integer target, int domain) {
        if (target == null || domain == GuardDomain.UNREACHED) return;
        int merged = states[target] | domain;
        if (merged != states[target]) {
            states[target] = merged;
            work.addLast(target);
        }
    }

    private static Map<AbstractInsnNode, Integer> instructionIndexes(MethodNode method) {
        Map<AbstractInsnNode, Integer> result = new IdentityHashMap<>();
        int index = 0;
        for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
             insn = insn.getNext(), index++) result.put(insn, index);
        return result;
    }

    private static final class GuardDomain {
        static final int UNREACHED = 0;
        static final int FALSE_VALUE = 1; // zero or null
        static final int TRUE_VALUE = 2;  // nonzero or non-null
        static final int UNINITIALIZED = 4;
        static final int BOTH = FALSE_VALUE | TRUE_VALUE;
        static final int ALL = BOTH | UNINITIALIZED;

        static int truthMask(int opcode) {
            return opcode == Opcodes.IFEQ || opcode == Opcodes.IFNULL
                    ? FALSE_VALUE : TRUE_VALUE;
        }

        static int falseMask(int opcode) {
            return truthMask(opcode) == FALSE_VALUE ? TRUE_VALUE : FALSE_VALUE;
        }

        static int fromValue(ProvenValue value) {
            if (value == null || value.isUnknown()) return BOTH;
            if (value.kind == ProvenValue.NULL_KIND) return FALSE_VALUE;
            if (value.kind == ProvenValue.NONNULL_KIND) return TRUE_VALUE;
            return value.isInteger() && value.integer == 0 ? FALSE_VALUE : TRUE_VALUE;
        }

        static String describe(int domain) {
            if (domain == UNREACHED) return "unreached";
            List<String> values = new ArrayList<>();
            if ((domain & FALSE_VALUE) != 0) values.add("zero_or_null");
            if ((domain & TRUE_VALUE) != 0) values.add("nonzero_or_nonnull");
            if ((domain & UNINITIALIZED) != 0) values.add("uninitialized");
            return String.join("|", values);
        }
    }

    private static final class GuardPathFacts {
        final int[] before;
        GuardPathFacts(int[] before) { this.before = before; }
    }

    private static final class PathGuardDecision {
        final ZkmGuardSite site;
        final boolean taken;
        final int domain;
        PathGuardDecision(ZkmGuardSite site, boolean taken, int domain) {
            this.site = site; this.taken = taken; this.domain = domain;
        }
    }

    private static boolean isParameterSlot(MethodNode method, int local) {
        int firstLocal = (method.access & Opcodes.ACC_STATIC) == 0 ? 1 : 0;
        for (Type argument : Type.getArgumentTypes(method.desc)) firstLocal += argument.getSize();
        return local < firstLocal;
    }

    private static String zkmGuardKind(int opcode) {
        if (opcode == Opcodes.IFEQ || opcode == Opcodes.IFNE) return "int";
        if (opcode == Opcodes.IFNULL || opcode == Opcodes.IFNONNULL) return "null";
        return null;
    }

    private static int zkmLoadOpcode(String kind) {
        return "int".equals(kind) ? Opcodes.ILOAD : Opcodes.ALOAD;
    }

    private static int oppositeZkmOpcode(int opcode) {
        switch (opcode) {
            case Opcodes.IFEQ: return Opcodes.IFNE;
            case Opcodes.IFNE: return Opcodes.IFEQ;
            case Opcodes.IFNULL: return Opcodes.IFNONNULL;
            case Opcodes.IFNONNULL: return Opcodes.IFNULL;
            default: throw new IllegalArgumentException("not a ZKM guard opcode: " + opcode);
        }
    }

    private static String zkmOpcodeName(int opcode) {
        switch (opcode) {
            case Opcodes.IFEQ: return "IFEQ";
            case Opcodes.IFNE: return "IFNE";
            case Opcodes.IFNULL: return "IFNULL";
            case Opcodes.IFNONNULL: return "IFNONNULL";
            default: return Integer.toString(opcode);
        }
    }

    private static boolean hasFallthroughFrame(JumpInsnNode jump) {
        for (AbstractInsnNode n = jump.getNext(); n != null && n.getOpcode() < 0; n = n.getNext()) {
            if (n instanceof FrameNode) return true;
        }
        return false;
    }

    private static AbstractInsnNode takenGuardConstant(int opcode) {
        switch (opcode) {
            case Opcodes.IFEQ: return new InsnNode(Opcodes.ICONST_0);
            case Opcodes.IFNE: return new InsnNode(Opcodes.ICONST_1);
            case Opcodes.IFNULL: return new InsnNode(Opcodes.ACONST_NULL);
            case Opcodes.IFNONNULL: return new LdcInsnNode("");
            default: throw new IllegalArgumentException("not a ZKM guard opcode: " + opcode);
        }
    }

    private static final class ZkmGuardSite {
        final VarInsnNode load;
        final JumpInsnNode jump;
        final String kind;
        final int local, opcode, stackSize;

        ZkmGuardSite(VarInsnNode load, JumpInsnNode jump, String kind, int local, int opcode, int stackSize) {
            this.load = load;
            this.jump = jump;
            this.kind = kind;
            this.local = local;
            this.opcode = opcode;
            this.stackSize = stackSize;
        }

        boolean residual() { return stackSize > 1; }
        String localKey() { return kind + ":" + local; }
        String groupKey() { return localKey() + ":" + opcode; }
    }

    private static final class ZkmAssumptionPlan {
        final String kind;
        final int local, assumedFalseOpcode;
        final List<ZkmGuardSite> sites;
        final String evidence;
        final String assumption;

        ZkmAssumptionPlan(String kind, int local, int assumedFalseOpcode,
                          List<ZkmGuardSite> sites, String evidence,
                          String assumption) {
            this.kind = kind;
            this.local = local;
            this.assumedFalseOpcode = assumedFalseOpcode;
            this.sites = sites;
            this.evidence = evidence;
            this.assumption = assumption;
        }
    }

    /** Closed-world proof index used by every class in the input archive. */
    private static final class ZkmProvenanceIndex {
        private final Map<MethodRef, ProvenValue> constantMethods;
        private final Map<MethodRef, StableFieldProof> stableGetters;
        private final Map<MethodRef, ZkmSentinelSeedHint> initializerHints;
        private final Map<MethodRef, String> rejectedGetters;
        private final Set<MethodRef> identityReferenceMethods;

        private ZkmProvenanceIndex(Map<MethodRef, ProvenValue> constantMethods,
                                   Map<MethodRef, StableFieldProof> stableGetters,
                                   Map<MethodRef, ZkmSentinelSeedHint> initializerHints,
                                   Map<MethodRef, String> rejectedGetters,
                                   Set<MethodRef> identityReferenceMethods) {
            this.constantMethods = constantMethods;
            this.stableGetters = stableGetters;
            this.initializerHints = initializerHints;
            this.rejectedGetters = rejectedGetters;
            this.identityReferenceMethods = identityReferenceMethods;
        }

        static ZkmProvenanceIndex build(Map<String, ClassNode> classes) {
            Map<MethodRef, MethodNode> methods = new LinkedHashMap<>();
            Map<FieldRef, FieldNode> fields = new LinkedHashMap<>();
            Map<MethodRef, FieldRef> getters = new LinkedHashMap<>();
            Map<FieldRef, List<MethodRef>> setters = new LinkedHashMap<>();
            Map<MethodRef, ProvenValue> constants = new LinkedHashMap<>();
            Set<MethodRef> identityReferences = new HashSet<>();
            Map<FieldRef, List<WriteSite>> writes = new LinkedHashMap<>();
            Map<MethodRef, List<CallSite>> calls = new LinkedHashMap<>();
            Set<MethodRef> methodHandleReferences = new HashSet<>();
            Set<FieldRef> fieldHandleReferences = new HashSet<>();

            for (ClassNode owner : classes.values()) {
                for (FieldNode field : owner.fields) {
                    fields.put(new FieldRef(owner.name, field.name, field.desc), field);
                }
                for (MethodNode method : owner.methods) {
                    MethodRef ref = new MethodRef(owner.name, method.name, method.desc);
                    methods.put(ref, method);
                    FieldRef getter = trivialGetter(method);
                    if (getter != null) getters.put(ref, getter);
                    FieldRef setter = trivialSetter(method);
                    if (setter != null) {
                        setters.computeIfAbsent(setter, ignored -> new ArrayList<>()).add(ref);
                    }
                    ProvenValue constant = trivialConstantReturn(method);
                    if (constant != null) constants.put(ref, constant);
                    if (isIdentityReferenceMethod(method)) identityReferences.add(ref);
                }
            }

            for (ClassNode owner : classes.values()) {
                for (MethodNode method : owner.methods) {
                    MethodRef caller = new MethodRef(owner.name, method.name, method.desc);
                    for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
                         insn = insn.getNext()) {
                        if (insn instanceof FieldInsnNode
                                && insn.getOpcode() == Opcodes.PUTSTATIC) {
                            FieldInsnNode field = (FieldInsnNode) insn;
                            FieldRef ref = new FieldRef(field.owner, field.name, field.desc);
                            writes.computeIfAbsent(ref, ignored -> new ArrayList<>())
                                    .add(new WriteSite(caller, field));
                        } else if (insn instanceof MethodInsnNode) {
                            MethodInsnNode call = (MethodInsnNode) insn;
                            MethodRef target = new MethodRef(call.owner, call.name, call.desc);
                            calls.computeIfAbsent(target, ignored -> new ArrayList<>())
                                    .add(new CallSite(caller, call));
                        } else if (insn instanceof LdcInsnNode) {
                            collectHandleReference(((LdcInsnNode) insn).cst,
                                    methodHandleReferences, fieldHandleReferences);
                        } else if (insn instanceof InvokeDynamicInsnNode) {
                            InvokeDynamicInsnNode indy = (InvokeDynamicInsnNode) insn;
                            collectHandleReference(indy.bsm, methodHandleReferences,
                                    fieldHandleReferences);
                            if (indy.bsmArgs != null) {
                                for (Object argument : indy.bsmArgs) {
                                    collectHandleReference(argument, methodHandleReferences,
                                            fieldHandleReferences);
                                }
                            }
                        }
                    }
                }
            }

            Map<MethodRef, StableFieldProof> stable = new LinkedHashMap<>();
            Map<MethodRef, ZkmSentinelSeedHint> initializerHints =
                    new LinkedHashMap<>();
            Map<MethodRef, String> rejected = new LinkedHashMap<>();
            for (Map.Entry<MethodRef, FieldRef> getterEntry : getters.entrySet()) {
                MethodRef getter = getterEntry.getKey();
                FieldRef field = getterEntry.getValue();
                FieldNode fieldNode = fields.get(field);
                if (fieldNode == null) {
                    rejected.put(getter, "backing_field_missing");
                    continue;
                }
                if (fieldHandleReferences.contains(field)) {
                    rejected.put(getter, "backing_field_has_method_handle_reference");
                    continue;
                }
                ProvenValue initial = defaultFieldValue(fieldNode);
                if (initial == null) {
                    rejected.put(getter, "unsupported_backing_field_type");
                    continue;
                }
                List<WriteSite> fieldWrites = writes.getOrDefault(field,
                        Collections.<WriteSite>emptyList());
                if (fieldWrites.isEmpty()) {
                    stable.put(getter, new StableFieldProof(field, getter, null, initial,
                            "archive_static_default"));
                    continue;
                }
                if (fieldWrites.size() != 1) {
                    rejected.put(getter, "backing_field_writes=" + fieldWrites.size());
                    continue;
                }
                List<MethodRef> fieldSetters = setters.getOrDefault(field,
                        Collections.<MethodRef>emptyList());
                if (fieldSetters.size() != 1
                        || !fieldSetters.get(0).equals(fieldWrites.get(0).method)) {
                    rejected.put(getter, "unique_write_not_in_unique_trivial_setter");
                    continue;
                }
                MethodRef setter = fieldSetters.get(0);
                if (methodHandleReferences.contains(setter)) {
                    rejected.put(getter, "setter_has_method_handle_reference");
                    continue;
                }
                List<CallSite> setterCalls = calls.getOrDefault(setter,
                        Collections.<CallSite>emptyList());
                ClassNode fieldOwner = classes.get(field.owner);
                MethodNode clinit = fieldOwner == null ? null
                        : findMethod(fieldOwner, "<clinit>", "()V");
                if (clinit != null) {
                    ProvenValue initialized = analyzeClinit(field.owner, clinit, field,
                            setter, initial, getters, constants);
                    if (initialized != null && !initialized.isUnknown()) {
                        initializerHints.put(getter, new ZkmSentinelSeedHint(
                                initialized, setter, setterCalls));
                    }
                }
                if (setterCalls.size() != 1) {
                    rejected.put(getter, "setter_direct_calls=" + setterCalls.size());
                    continue;
                }
                CallSite setterCall = setterCalls.get(0);
                if (!field.owner.equals(setterCall.caller.owner)
                        || !"<clinit>".equals(setterCall.caller.name)
                        || !"()V".equals(setterCall.caller.desc)) {
                    rejected.put(getter, "setter_call_outside_owner_clinit="
                            + setterCall.caller);
                    continue;
                }
                if (clinit == null) {
                    rejected.put(getter, "owner_clinit_missing");
                    continue;
                }
                ProvenValue finalValue = analyzeClinit(field.owner, clinit, field, setter,
                        initial, getters, constants);
                if (finalValue == null || finalValue.isUnknown()) {
                    rejected.put(getter, "clinit_final_value_unproven");
                    continue;
                }
                stable.put(getter, new StableFieldProof(field, getter, setter, finalValue,
                        "archive_clinit_fixed"));
            }
            return new ZkmProvenanceIndex(constants, stable, initializerHints, rejected,
                    identityReferences);
        }

        ZkmSentinelSeedDecision initializerHintForStore(
                String owner, MethodNode method, VarInsnNode store,
                int lastGuardPosition) {
            if (store == null) return ZkmSentinelSeedDecision.UNRECOGNIZED;
            try {
                Frame<SourceValue>[] frames = new Analyzer<>(new SourceInterpreter())
                        .analyze(owner, method);
                Map<AbstractInsnNode, Integer> indexes = instructionIndexes(method);
                AbstractInsnNode producer = uniqueStackProducer(method, frames, indexes,
                        store, 0);
                if (!(producer instanceof MethodInsnNode)) {
                    return ZkmSentinelSeedDecision.UNRECOGNIZED;
                }
                MethodInsnNode call = (MethodInsnNode) producer;
                ZkmSentinelSeedHint hint = initializerHints.get(
                        new MethodRef(call.owner, call.name, call.desc));
                if (hint == null) return ZkmSentinelSeedDecision.UNRECOGNIZED;
                MethodRef current = new MethodRef(owner, method.name, method.desc);
                int expectedSelfWrites = 0;
                for (CallSite setterCall : hint.setterCalls) {
                    if (setterCall.caller.owner.equals(hint.setter.owner)
                            && "<clinit>".equals(setterCall.caller.name)
                            && "()V".equals(setterCall.caller.desc)) {
                        continue;
                    }
                    if (!current.equals(setterCall.caller)) {
                        return ZkmSentinelSeedDecision.REJECTED;
                    }
                    expectedSelfWrites++;
                }
                int observedSelfWrites = 0;
                for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
                     insn = insn.getNext()) {
                    if (!(insn instanceof MethodInsnNode)) continue;
                    MethodInsnNode candidate = (MethodInsnNode) insn;
                    if (!hint.setter.equals(new MethodRef(candidate.owner,
                            candidate.name, candidate.desc))) continue;
                    Integer position = indexes.get(insn);
                    if (position == null || position <= lastGuardPosition) {
                        return ZkmSentinelSeedDecision.REJECTED;
                    }
                    observedSelfWrites++;
                }
                return observedSelfWrites == expectedSelfWrites
                        ? new ZkmSentinelSeedDecision(true, hint.value)
                        : ZkmSentinelSeedDecision.REJECTED;
            } catch (Throwable failure) {
                return ZkmSentinelSeedDecision.REJECTED;
            }
        }

        ProvenValue valueForStore(
                String owner, MethodNode method, VarInsnNode store,
                Frame<SourceValue>[] frames,
                Map<AbstractInsnNode, Integer> indexes) {
            AbstractInsnNode producer = uniqueStackProducer(method, frames, indexes, store, 0);
            ProvenValue value = directValue(producer);
            if (value == null && producer instanceof MethodInsnNode) {
                MethodInsnNode call = (MethodInsnNode) producer;
                MethodRef ref = new MethodRef(call.owner, call.name, call.desc);
                value = constantMethods.get(ref);
                if (value == null) {
                    StableFieldProof fieldProof = stableGetters.get(ref);
                    value = fieldProof == null ? null : fieldProof.value;
                }
            }
            if (store.getOpcode() == Opcodes.ISTORE) {
                return value != null && value.isInteger() ? value : null;
            }
            if (store.getOpcode() == Opcodes.ASTORE) {
                return value != null && (value.kind == ProvenValue.NULL_KIND
                        || value.kind == ProvenValue.NONNULL_KIND) ? value : null;
            }
            return null;
        }

        private static ProvenValue analyzeClinit(
                String owner, MethodNode clinit, FieldRef field, MethodRef setter,
                ProvenValue initial, Map<MethodRef, FieldRef> getters,
                Map<MethodRef, ProvenValue> constants) {
            try {
                Frame<SourceValue>[] frames = new Analyzer<>(new SourceInterpreter())
                        .analyze(owner, clinit);
                Map<AbstractInsnNode, Integer> indexes = new IdentityHashMap<>();
                int position = 0;
                for (AbstractInsnNode insn = clinit.instructions.getFirst(); insn != null;
                     insn = insn.getNext()) indexes.put(insn, position++);
                Map<AbstractInsnNode, List<LabelNode>> handlers = exceptionHandlers(clinit,
                        indexes);
                Map<AbstractInsnNode, ProvenValue> reached = new IdentityHashMap<>();
                ArrayDeque<FlowState> work = new ArrayDeque<>();
                AbstractInsnNode first = firstCode(clinit);
                if (first == null) return null;
                work.add(new FlowState(first, initial));
                ProvenValue exits = null;
                int iterations = 0;
                while (!work.isEmpty()) {
                    if (++iterations > Math.max(1024, clinit.instructions.size() * 32)) {
                        return null;
                    }
                    FlowState state = work.removeFirst();
                    ProvenValue previous = reached.get(state.insn);
                    ProvenValue merged = previous == null ? state.value
                            : previous.merge(state.value);
                    if (previous != null && previous.equals(merged)) continue;
                    reached.put(state.insn, merged);
                    ProvenValue value = merged;
                    AbstractInsnNode insn = state.insn;

                    List<LabelNode> catches = handlers.get(insn);
                    if (catches != null) {
                        for (LabelNode handler : catches) {
                            enqueue(work, nextCode(handler), value);
                        }
                    }

                    if (insn instanceof MethodInsnNode) {
                        MethodInsnNode call = (MethodInsnNode) insn;
                        if (setter.equals(new MethodRef(call.owner, call.name, call.desc))) {
                            AbstractInsnNode producer = uniqueStackProducer(clinit, frames,
                                    indexes, insn, 0);
                            ProvenValue assigned = valueFromProducer(producer, value, field,
                                    getters, constants);
                            value = assigned == null ? ProvenValue.UNKNOWN : assigned;
                        }
                    }

                    int opcode = insn.getOpcode();
                    if (opcode == Opcodes.RETURN) {
                        exits = exits == null ? value : exits.merge(value);
                        continue;
                    }
                    if (opcode == Opcodes.ATHROW) continue;
                    if (insn instanceof JumpInsnNode) {
                        JumpInsnNode jump = (JumpInsnNode) insn;
                        if (opcode == Opcodes.GOTO) {
                            enqueue(work, nextCode(jump.label), value);
                        } else {
                            AbstractInsnNode producer = uniqueStackProducer(clinit, frames,
                                    indexes, insn, 0);
                            ProvenValue condition = valueFromProducer(producer, value, field,
                                    getters, constants);
                            Boolean taken = branchTaken(opcode, condition);
                            if (taken == null || taken) {
                                enqueue(work, nextCode(jump.label), value);
                            }
                            if (taken == null || !taken) {
                                enqueue(work, nextCode(insn), value);
                            }
                        }
                    } else if (insn instanceof TableSwitchInsnNode) {
                        TableSwitchInsnNode table = (TableSwitchInsnNode) insn;
                        enqueue(work, nextCode(table.dflt), value);
                        for (LabelNode label : table.labels) enqueue(work, nextCode(label), value);
                    } else if (insn instanceof LookupSwitchInsnNode) {
                        LookupSwitchInsnNode lookup = (LookupSwitchInsnNode) insn;
                        enqueue(work, nextCode(lookup.dflt), value);
                        for (LabelNode label : lookup.labels) enqueue(work, nextCode(label), value);
                    } else {
                        enqueue(work, nextCode(insn), value);
                    }
                }
                return exits;
            } catch (Throwable failure) {
                return null;
            }
        }

        private static Map<AbstractInsnNode, List<LabelNode>> exceptionHandlers(
                MethodNode method, Map<AbstractInsnNode, Integer> indexes) {
            Map<AbstractInsnNode, List<LabelNode>> result = new IdentityHashMap<>();
            for (TryCatchBlockNode block : method.tryCatchBlocks) {
                Integer start = indexes.get(block.start);
                Integer end = indexes.get(block.end);
                if (start == null || end == null) continue;
                int index = 0;
                for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
                     insn = insn.getNext(), index++) {
                    if (index >= start && index < end && insn.getOpcode() >= 0) {
                        result.computeIfAbsent(insn, ignored -> new ArrayList<>())
                                .add(block.handler);
                    }
                }
            }
            return result;
        }

        private static AbstractInsnNode uniqueStackProducer(
                MethodNode method, Frame<SourceValue>[] frames,
                Map<AbstractInsnNode, Integer> indexes, AbstractInsnNode consumer,
                int fromTop) {
            Integer index = indexes.get(consumer);
            if (index == null || index < 0 || index >= frames.length) return null;
            Frame<SourceValue> frame = frames[index];
            if (frame == null || frame.getStackSize() <= fromTop) return null;
            SourceValue source = frame.getStack(frame.getStackSize() - 1 - fromTop);
            return source != null && source.insns.size() == 1
                    ? source.insns.iterator().next() : null;
        }

        private static ProvenValue valueFromProducer(
                AbstractInsnNode producer, ProvenValue fieldValue, FieldRef targetField,
                Map<MethodRef, FieldRef> getters,
                Map<MethodRef, ProvenValue> constants) {
            ProvenValue direct = directValue(producer);
            if (direct != null) return direct;
            if (producer instanceof FieldInsnNode && producer.getOpcode() == Opcodes.GETSTATIC) {
                FieldInsnNode field = (FieldInsnNode) producer;
                if (targetField.equals(new FieldRef(field.owner, field.name, field.desc))) {
                    return fieldValue;
                }
            }
            if (producer instanceof MethodInsnNode) {
                MethodInsnNode call = (MethodInsnNode) producer;
                MethodRef ref = new MethodRef(call.owner, call.name, call.desc);
                if (targetField.equals(getters.get(ref))) return fieldValue;
                return constants.get(ref);
            }
            return null;
        }

        private static void enqueue(ArrayDeque<FlowState> work, AbstractInsnNode insn,
                                    ProvenValue value) {
            if (insn != null) work.addLast(new FlowState(insn, value));
        }

        private static FieldRef trivialGetter(MethodNode method) {
            if ((method.access & Opcodes.ACC_STATIC) == 0
                    || Type.getArgumentTypes(method.desc).length != 0
                    || Type.getReturnType(method.desc).getSort() == Type.VOID) return null;
            List<AbstractInsnNode> code = code(method);
            if (code.size() != 2 || !(code.get(0) instanceof FieldInsnNode)
                    || code.get(0).getOpcode() != Opcodes.GETSTATIC
                    || code.get(1).getOpcode() != returnOpcode(
                            Type.getReturnType(method.desc))) return null;
            FieldInsnNode field = (FieldInsnNode) code.get(0);
            if (!field.desc.equals(Type.getReturnType(method.desc).getDescriptor())) return null;
            return new FieldRef(field.owner, field.name, field.desc);
        }

        private static FieldRef trivialSetter(MethodNode method) {
            Type[] arguments = Type.getArgumentTypes(method.desc);
            if ((method.access & Opcodes.ACC_STATIC) == 0 || arguments.length != 1
                    || Type.getReturnType(method.desc).getSort() != Type.VOID) return null;
            List<AbstractInsnNode> code = code(method);
            if (code.size() != 3 || !(code.get(0) instanceof VarInsnNode)
                    || !(code.get(1) instanceof FieldInsnNode)
                    || code.get(1).getOpcode() != Opcodes.PUTSTATIC
                    || code.get(2).getOpcode() != Opcodes.RETURN) return null;
            VarInsnNode load = (VarInsnNode) code.get(0);
            FieldInsnNode field = (FieldInsnNode) code.get(1);
            if (load.var != 0 || load.getOpcode() != arguments[0].getOpcode(Opcodes.ILOAD)
                    || !field.desc.equals(arguments[0].getDescriptor())) return null;
            return new FieldRef(field.owner, field.name, field.desc);
        }

        private static ProvenValue trivialConstantReturn(MethodNode method) {
            if ((method.access & Opcodes.ACC_STATIC) == 0
                    || Type.getArgumentTypes(method.desc).length != 0) return null;
            Type result = Type.getReturnType(method.desc);
            if (result.getSort() == Type.VOID) return null;
            List<AbstractInsnNode> code = code(method);
            if (code.size() != 2 || code.get(1).getOpcode() != returnOpcode(result)) return null;
            ProvenValue value = directValue(code.get(0));
            return matchesType(value, result) ? value : null;
        }

        private static boolean isIdentityReferenceMethod(MethodNode method) {
            Type[] arguments = Type.getArgumentTypes(method.desc);
            Type result = Type.getReturnType(method.desc);
            if ((method.access & Opcodes.ACC_STATIC) == 0 || arguments.length != 1
                    || (method.access & Opcodes.ACC_SYNCHRONIZED) != 0
                    || arguments[0].getSort() != Type.OBJECT
                    || !arguments[0].equals(result)) return false;
            List<AbstractInsnNode> instructions = code(method);
            return instructions.size() == 2
                    && instructions.get(0) instanceof VarInsnNode
                    && instructions.get(0).getOpcode() == Opcodes.ALOAD
                    && ((VarInsnNode) instructions.get(0)).var == 0
                    && instructions.get(1).getOpcode() == Opcodes.ARETURN;
        }

        private static List<AbstractInsnNode> code(MethodNode method) {
            List<AbstractInsnNode> result = new ArrayList<>();
            for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
                 insn = insn.getNext()) if (insn.getOpcode() >= 0) result.add(insn);
            return result;
        }

        private static int returnOpcode(Type type) {
            return type.getOpcode(Opcodes.IRETURN);
        }

        private static ProvenValue defaultFieldValue(FieldNode field) {
            Type type = Type.getType(field.desc);
            if (type.getSort() == Type.OBJECT || type.getSort() == Type.ARRAY) {
                return field.value == null ? ProvenValue.NULL : ProvenValue.NONNULL;
            }
            if (type.getSort() >= Type.BOOLEAN && type.getSort() <= Type.INT) {
                return ProvenValue.integer(field.value instanceof Number
                        ? ((Number) field.value).intValue() : 0);
            }
            return null;
        }

        private static ProvenValue directValue(AbstractInsnNode insn) {
            if (insn == null) return null;
            Integer integer = intConstant(insn);
            if (integer != null) return ProvenValue.integer(integer);
            int opcode = insn.getOpcode();
            if (opcode == Opcodes.ACONST_NULL) return ProvenValue.NULL;
            if (opcode == Opcodes.NEW || opcode == Opcodes.NEWARRAY
                    || opcode == Opcodes.ANEWARRAY || opcode == Opcodes.MULTIANEWARRAY) {
                return ProvenValue.NONNULL;
            }
            if (insn instanceof LdcInsnNode) {
                Object value = ((LdcInsnNode) insn).cst;
                if (value instanceof String || value instanceof Type
                        || value instanceof org.objectweb.asm.Handle) {
                    return ProvenValue.NONNULL;
                }
            }
            return null;
        }

        private static Boolean branchTaken(int opcode, ProvenValue value) {
            if (value == null || value.isUnknown()) return null;
            switch (opcode) {
                case Opcodes.IFEQ:
                    return value.isInteger() ? value.integer == 0 : null;
                case Opcodes.IFNE:
                    return value.isInteger() ? value.integer != 0 : null;
                case Opcodes.IFLT:
                    return value.isInteger() ? value.integer < 0 : null;
                case Opcodes.IFGE:
                    return value.isInteger() ? value.integer >= 0 : null;
                case Opcodes.IFGT:
                    return value.isInteger() ? value.integer > 0 : null;
                case Opcodes.IFLE:
                    return value.isInteger() ? value.integer <= 0 : null;
                case Opcodes.IFNULL:
                    return value.kind == ProvenValue.NULL_KIND ? Boolean.TRUE
                            : value.kind == ProvenValue.NONNULL_KIND ? Boolean.FALSE : null;
                case Opcodes.IFNONNULL:
                    return value.kind == ProvenValue.NONNULL_KIND ? Boolean.TRUE
                            : value.kind == ProvenValue.NULL_KIND ? Boolean.FALSE : null;
                default:
                    return null;
            }
        }

        private static boolean matchesType(ProvenValue value, Type type) {
            if (value == null) return false;
            if (type.getSort() >= Type.BOOLEAN && type.getSort() <= Type.INT) {
                return value.isInteger();
            }
            return (type.getSort() == Type.OBJECT || type.getSort() == Type.ARRAY)
                    && (value.kind == ProvenValue.NULL_KIND
                            || value.kind == ProvenValue.NONNULL_KIND);
        }

        private static void collectHandleReference(
                Object value, Set<MethodRef> methods, Set<FieldRef> fields) {
            if (!(value instanceof org.objectweb.asm.Handle)) return;
            org.objectweb.asm.Handle handle = (org.objectweb.asm.Handle) value;
            int tag = handle.getTag();
            if (tag >= Opcodes.H_GETFIELD && tag <= Opcodes.H_PUTSTATIC) {
                fields.add(new FieldRef(handle.getOwner(), handle.getName(), handle.getDesc()));
            } else {
                methods.add(new MethodRef(handle.getOwner(), handle.getName(), handle.getDesc()));
            }
        }

        private static MethodNode findMethod(ClassNode owner, String name, String desc) {
            for (MethodNode method : owner.methods) {
                if (name.equals(method.name) && desc.equals(method.desc)) return method;
            }
            return null;
        }

        private static AbstractInsnNode firstCode(MethodNode method) {
            AbstractInsnNode insn = method.instructions.getFirst();
            while (insn != null && insn.getOpcode() < 0) insn = insn.getNext();
            return insn;
        }
    }

    private static final class ProvenValue {
        static final int UNKNOWN_KIND = 0;
        static final int NULL_KIND = 1;
        static final int NONNULL_KIND = 2;
        static final int INTEGER_KIND = 3;
        static final ProvenValue UNKNOWN = new ProvenValue(UNKNOWN_KIND, 0);
        static final ProvenValue NULL = new ProvenValue(NULL_KIND, 0);
        static final ProvenValue NONNULL = new ProvenValue(NONNULL_KIND, 0);
        final int kind;
        final int integer;

        private ProvenValue(int kind, int integer) {
            this.kind = kind;
            this.integer = integer;
        }

        static ProvenValue integer(int value) { return new ProvenValue(INTEGER_KIND, value); }
        boolean isInteger() { return kind == INTEGER_KIND; }
        boolean isUnknown() { return kind == UNKNOWN_KIND; }
        ProvenValue merge(ProvenValue other) { return equals(other) ? this : UNKNOWN; }

        @Override public boolean equals(Object value) {
            if (!(value instanceof ProvenValue)) return false;
            ProvenValue other = (ProvenValue) value;
            return kind == other.kind && integer == other.integer;
        }

        @Override public int hashCode() { return kind * 31 + integer; }
        @Override public String toString() {
            if (kind == NULL_KIND) return "null";
            if (kind == NONNULL_KIND) return "nonnull";
            if (kind == INTEGER_KIND) return "int(" + integer + ")";
            return "unknown";
        }
    }

    private static final class StableFieldProof {
        final FieldRef field;
        final MethodRef getter;
        final MethodRef setter;
        final ProvenValue value;
        final String source;

        StableFieldProof(FieldRef field, MethodRef getter, MethodRef setter,
                         ProvenValue value, String source) {
            this.field = field;
            this.getter = getter;
            this.setter = setter;
            this.value = value;
            this.source = source;
        }

        String description() {
            return source + ":getter=" + getter + ",field=" + field + ",setter="
                    + (setter == null ? "none" : setter.toString()) + ",value=" + value
                    + ",scope=archive_closed_world";
        }
    }

    /** Seed evidence consumed only by the explicit mutable-sentinel mode. */
    private static final class ZkmSentinelSeedHint {
        final ProvenValue value;
        final MethodRef setter;
        final List<CallSite> setterCalls;

        ZkmSentinelSeedHint(ProvenValue value, MethodRef setter,
                            List<CallSite> setterCalls) {
            this.value = value;
            this.setter = setter;
            this.setterCalls = Collections.unmodifiableList(
                    new ArrayList<CallSite>(setterCalls));
        }
    }

    private static final class ZkmSentinelSeedDecision {
        static final ZkmSentinelSeedDecision UNRECOGNIZED =
                new ZkmSentinelSeedDecision(false, null);
        static final ZkmSentinelSeedDecision REJECTED =
                new ZkmSentinelSeedDecision(true, null);
        final boolean recognized;
        final ProvenValue value;

        ZkmSentinelSeedDecision(boolean recognized, ProvenValue value) {
            this.recognized = recognized;
            this.value = value;
        }
    }

    private static final class MethodRef {
        final String owner, name, desc;
        MethodRef(String owner, String name, String desc) {
            this.owner = owner; this.name = name; this.desc = desc;
        }
        @Override public boolean equals(Object value) {
            if (!(value instanceof MethodRef)) return false;
            MethodRef other = (MethodRef) value;
            return owner.equals(other.owner) && name.equals(other.name) && desc.equals(other.desc);
        }
        @Override public int hashCode() { return Objects.hash(owner, name, desc); }
        @Override public String toString() { return owner + "." + name + desc; }
    }

    private static final class FieldRef {
        final String owner, name, desc;
        FieldRef(String owner, String name, String desc) {
            this.owner = owner; this.name = name; this.desc = desc;
        }
        @Override public boolean equals(Object value) {
            if (!(value instanceof FieldRef)) return false;
            FieldRef other = (FieldRef) value;
            return owner.equals(other.owner) && name.equals(other.name) && desc.equals(other.desc);
        }
        @Override public int hashCode() { return Objects.hash(owner, name, desc); }
        @Override public String toString() { return owner + "." + name + ":" + desc; }
    }

    private static final class WriteSite {
        final MethodRef method;
        final FieldInsnNode node;
        WriteSite(MethodRef method, FieldInsnNode node) { this.method = method; this.node = node; }
    }

    private static final class CallSite {
        final MethodRef caller;
        final MethodInsnNode node;
        CallSite(MethodRef caller, MethodInsnNode node) { this.caller = caller; this.node = node; }
    }

    private static final class FlowState {
        final AbstractInsnNode insn;
        final ProvenValue value;
        FlowState(AbstractInsnNode insn, ProvenValue value) {
            this.insn = insn; this.value = value;
        }
    }

    private static MethodNode cloneMethod(MethodNode src) {
        MethodNode dst = new MethodNode(Opcodes.ASM9, src.access, src.name, src.desc, src.signature,
                src.exceptions == null ? null : src.exceptions.toArray(new String[0]));
        src.accept(dst); return dst;
    }

    private static byte[] writeClass(ClassNode cn, ArchiveHierarchy hierarchy,
                                     boolean computeFrames) {
        ClassWriter cw = computeFrames
                ? new ArchiveClassWriter(ClassWriter.COMPUTE_FRAMES, hierarchy)
                : new ClassWriter(ClassWriter.COMPUTE_MAXS);
        cn.accept(cw); return cw.toByteArray();
    }

    private static boolean shouldComputeFrames(ClassNode owner) {
        if (owner.version > Opcodes.V1_6) return true;
        for (MethodNode method : owner.methods) {
            for (AbstractInsnNode instruction = method.instructions.getFirst();
                 instruction != null; instruction = instruction.getNext()) {
                int opcode = instruction.getOpcode();
                if (opcode == Opcodes.JSR || opcode == Opcodes.RET) return false;
            }
        }
        return true;
    }

    /** Closed-world hierarchy resolver; it never loads a class from the archive. */
    private static final class ArchiveHierarchy {
        private final Map<String, HierarchyType> types = new HashMap<>();

        ArchiveHierarchy(Map<String, ClassNode> classes) {
            for (ClassNode node : classes.values()) {
                types.put(node.name, new HierarchyType(node.superName,
                        node.interfaces == null ? Collections.<String>emptyList()
                                : new ArrayList<>(node.interfaces),
                        (node.access & Opcodes.ACC_INTERFACE) != 0));
            }
            types.put("java/lang/Object", new HierarchyType(null,
                    Collections.<String>emptyList(), false));
            addPlatformClass("java/lang/Throwable", "java/lang/Object");
            addPlatformClass("java/lang/Exception", "java/lang/Throwable");
            addPlatformClass("java/lang/RuntimeException", "java/lang/Exception");
            addPlatformClass("java/lang/UnsupportedOperationException",
                    "java/lang/RuntimeException");
            addPlatformClass("java/lang/IllegalArgumentException",
                    "java/lang/RuntimeException");
            addPlatformClass("java/lang/NumberFormatException",
                    "java/lang/IllegalArgumentException");
            addPlatformClass("java/lang/IllegalStateException",
                    "java/lang/RuntimeException");
            addPlatformClass("java/lang/NullPointerException",
                    "java/lang/RuntimeException");
            addPlatformClass("java/lang/IndexOutOfBoundsException",
                    "java/lang/RuntimeException");
            addPlatformClass("java/lang/ArrayIndexOutOfBoundsException",
                    "java/lang/IndexOutOfBoundsException");
            addPlatformClass("java/lang/StringIndexOutOfBoundsException",
                    "java/lang/IndexOutOfBoundsException");
            addPlatformClass("java/lang/ClassCastException",
                    "java/lang/RuntimeException");
            addPlatformClass("java/io/IOException", "java/lang/Exception");
            addPlatformClass("java/io/FileNotFoundException", "java/io/IOException");
            addPlatformClass("java/lang/InterruptedException", "java/lang/Exception");
            addPlatformClass("java/lang/ReflectiveOperationException",
                    "java/lang/Exception");
            addPlatformClass("java/lang/ClassNotFoundException",
                    "java/lang/ReflectiveOperationException");
            addPlatformClass("java/lang/IllegalAccessException",
                    "java/lang/ReflectiveOperationException");
            addPlatformClass("java/lang/InstantiationException",
                    "java/lang/ReflectiveOperationException");
            addPlatformClass("java/lang/NoSuchFieldException",
                    "java/lang/ReflectiveOperationException");
            addPlatformClass("java/lang/NoSuchMethodException",
                    "java/lang/ReflectiveOperationException");
            addPlatformClass("java/text/ParseException", "java/lang/Exception");
        }

        private void addPlatformClass(String name, String superName) {
            types.putIfAbsent(name, new HierarchyType(superName,
                    Collections.<String>emptyList(), false));
        }

        String commonSuperClass(String left, String right) {
            if (left.equals(right)) return left;
            if (isAssignableFrom(left, right)) return left;
            if (isAssignableFrom(right, left)) return right;
            HierarchyType leftType = types.get(left);
            HierarchyType rightType = types.get(right);
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

        boolean mayShareThrowableSubtype(String left, String right) {
            if (left == null || right == null) return true;
            HierarchyType leftType = types.get(left);
            HierarchyType rightType = types.get(right);
            if (leftType == null || rightType == null
                    || leftType.isInterface || rightType.isInterface
                    || !hasCompleteClassLineage(left)
                    || !hasCompleteClassLineage(right)) return true;
            return isAssignableFrom(left, right) || isAssignableFrom(right, left);
        }

        private boolean hasCompleteClassLineage(String name) {
            Set<String> seen = new HashSet<>();
            String current = name;
            while (current != null) {
                if (!seen.add(current)) return false;
                HierarchyType type = types.get(current);
                if (type == null || type.isInterface) return false;
                current = type.superName;
            }
            return seen.contains("java/lang/Object");
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

    private static boolean structurallyValid(byte[] bytes) {
        return structuralValidationFailure(bytes) == null;
    }

    private static String structuralValidationFailure(byte[] bytes) {
        try {
            ClassReader reader = new ClassReader(bytes);
            reader.accept(new CheckClassAdapter(new ClassWriter(0), false), 0);
            ClassNode node = new ClassNode(Opcodes.ASM9); reader.accept(node, 0);
            for (MethodNode method : node.methods) if (method.instructions.size() > 0) {
                if (!hasValidLineNumberTargets(method)) {
                    return "invalid-line-number-target:" + method.name + method.desc;
                }
                new Analyzer<>(new BasicVerifier()).analyze(node.name, method);
            }
            return null;
        } catch (Throwable failure) {
            return shortReason(failure);
        }
    }

    private static boolean foldConstants(MethodNode m, String owner, List<String> rows, Map<AbstractInsnNode,Integer> offsets) {
        boolean changed = false;
        for (AbstractInsnNode n = m.instructions.getFirst(); n != null; ) {
            AbstractInsnNode next = n.getNext();
            if (n instanceof JumpInsnNode && isConditional(n.getOpcode())) {
                int op = n.getOpcode();
                AbstractInsnNode p1 = prevCode(n), p2 = p1 == null ? null : prevCode(p1);
                Integer a = intConstant(p1), b = intConstant(p2);
                Boolean result = null;
                String conditionKind = "integer";
                int offset = offsetOf(n, offsets, m);
                if ((op == Opcodes.IFNULL || op == Opcodes.IFNONNULL)
                        && p1 != null && p1.getOpcode() == Opcodes.ACONST_NULL
                        && p1.getNext() == n) {
                    result = op == Opcodes.IFNULL;
                    conditionKind = "null";
                } else if ((op == Opcodes.IFNULL || op == Opcodes.IFNONNULL)
                        && p1 instanceof LdcInsnNode
                        && ((LdcInsnNode) p1).cst instanceof String
                        && p1.getNext() == n) {
                    // A CONSTANT_String entry always produces a non-null
                    // interned String. Restrict this proof to String constants;
                    // ConstantDynamic may legally resolve to null.
                    result = op == Opcodes.IFNONNULL;
                    conditionKind = "nonnull-string";
                } else if (isBinaryInt(op) && a != null && b != null
                        && p2.getNext() == p1 && p1.getNext() == n) {
                    result = compareInt(op, b, a);
                } else if (!isBinaryInt(op) && a != null && p1.getNext() == n) {
                    result = compareZero(op, a);
                }
                AbstractInsnNode cmp = null, right = null, left = null;
                if (result == null && !isBinaryInt(op) && isNumericCmp(p1)) {
                    cmp = p1; right = prevCode(cmp); left = right == null ? null : prevCode(right);
                    Integer cmpResult = constantNumericCompare(cmp.getOpcode(), numericConstant(left), numericConstant(right));
                    if (cmpResult != null && left.getNext() == right && right.getNext() == cmp && cmp.getNext() == n) {
                        result = compareZero(op, cmpResult);
                    }
                }
                if (result != null) {
                    if (cmp != null) {
                        m.instructions.remove(left); m.instructions.remove(right); m.instructions.remove(cmp);
                    } else {
                        m.instructions.remove(p1);
                        if (isBinaryInt(op)) m.instructions.remove(p2);
                    }
                    if (result) {
                        JumpInsnNode replacement = new JumpInsnNode(Opcodes.GOTO, ((JumpInsnNode)n).label);
                        m.instructions.set(n, replacement); offsets.put(replacement, offset);
                    }
                    else m.instructions.remove(n);
                    rows.add(row(owner, m.name + m.desc, offset, "fold-constant",
                            (cmp == null ? conditionKind : opcodeName(cmp.getOpcode()))
                                    + " constant condition=" + result));
                    changed = true;
                }
            }
            n = next;
        }
        return changed;
    }

    private static boolean removeUnreachable(MethodNode m, org.objectweb.asm.tree.analysis.Frame<?>[] frames,
                                             String owner, List<String> rows, Map<AbstractInsnNode,Integer> offsets) {
        boolean changed = false;
        List<AbstractInsnNode> snapshot = new ArrayList<>();
        for (AbstractInsnNode n = m.instructions.getFirst(); n != null; n = n.getNext()) snapshot.add(n);
        List<AbstractInsnNode> dead = new ArrayList<>();
        for (int i = 0; i < snapshot.size() && i < frames.length; i++) {
            AbstractInsnNode n = snapshot.get(i); if (frames[i] == null && n.getOpcode() >= 0) dead.add(n);
        }
        for (AbstractInsnNode n : dead) {
            rows.add(row(owner, m.name + m.desc, offsetOf(n, offsets, m), "remove-unreachable", "analyzer frame is null"));
            m.instructions.remove(n); changed = true;
        }
        return changed;
    }

    private static boolean removeDeadLineNumbers(
            MethodNode method,
            String owner,
            List<String> rows,
            Map<AbstractInsnNode, Integer> offsets) {
        List<LineNumberNode> dead = new ArrayList<>();
        for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
             insn = insn.getNext()) {
            if (insn instanceof LineNumberNode
                    && nextCode(((LineNumberNode) insn).start) == null) {
                dead.add((LineNumberNode) insn);
            }
        }
        if (dead.isEmpty()) return false;
        int firstOffset = offsetOf(dead.get(0), offsets, method);
        for (LineNumberNode line : dead) method.instructions.remove(line);
        rows.add(row(owner, method.name + method.desc, firstOffset,
                "remove-dead-line-numbers",
                "count=" + dead.size() + ",target_has_executable_instruction=false"));
        return true;
    }

    private static boolean removeInvalidLocalVariableMetadata(
            MethodNode method,
            String owner,
            List<String> rows,
            Map<AbstractInsnNode, Integer> offsets) {
        Map<LabelNode, Integer> labelIndexes = new IdentityHashMap<>();
        int instructionIndex = 0;
        for (AbstractInsnNode instruction = method.instructions.getFirst();
             instruction != null; instruction = instruction.getNext()) {
            if (instruction instanceof LabelNode) {
                labelIndexes.put((LabelNode) instruction,
                        Integer.valueOf(instructionIndex));
            }
            instructionIndex++;
        }

        int tableEntries = 0;
        int annotationRanges = 0;
        if (method.localVariables != null) {
            for (Iterator<LocalVariableNode> iterator = method.localVariables.iterator();
                 iterator.hasNext(); ) {
                LocalVariableNode variable = iterator.next();
                if (hasExecutableRange(variable.start, variable.end, labelIndexes)) {
                    continue;
                }
                iterator.remove();
                tableEntries++;
            }
        }
        annotationRanges += removeInvalidLocalVariableAnnotationRanges(
                method.visibleLocalVariableAnnotations, labelIndexes);
        annotationRanges += removeInvalidLocalVariableAnnotationRanges(
                method.invisibleLocalVariableAnnotations, labelIndexes);
        removeEmptyLocalVariableAnnotations(method.visibleLocalVariableAnnotations);
        removeEmptyLocalVariableAnnotations(method.invisibleLocalVariableAnnotations);

        if (tableEntries == 0 && annotationRanges == 0) return false;
        rows.add(row(owner, method.name + method.desc,
                offsetOf(method.instructions.getFirst(), offsets, method),
                "remove-invalid-local-variable-metadata",
                "table_entries=" + tableEntries
                        + ",annotation_ranges=" + annotationRanges
                        + ",requirement=start_before_end_with_executable_instruction"));
        return true;
    }

    private static int removeInvalidLocalVariableAnnotationRanges(
            List<LocalVariableAnnotationNode> annotations,
            Map<LabelNode, Integer> labelIndexes) {
        if (annotations == null) return 0;
        int removed = 0;
        for (LocalVariableAnnotationNode annotation : annotations) {
            for (int index = annotation.start.size() - 1; index >= 0; index--) {
                if (hasExecutableRange(annotation.start.get(index),
                        annotation.end.get(index), labelIndexes)) continue;
                annotation.start.remove(index);
                annotation.end.remove(index);
                annotation.index.remove(index);
                removed++;
            }
        }
        return removed;
    }

    private static void removeEmptyLocalVariableAnnotations(
            List<LocalVariableAnnotationNode> annotations) {
        if (annotations == null) return;
        for (Iterator<LocalVariableAnnotationNode> iterator = annotations.iterator();
             iterator.hasNext(); ) {
            if (iterator.next().start.isEmpty()) iterator.remove();
        }
    }

    private static boolean hasExecutableRange(
            LabelNode start,
            LabelNode end,
            Map<LabelNode, Integer> labelIndexes) {
        Integer startIndex = labelIndexes.get(start);
        Integer endIndex = labelIndexes.get(end);
        if (startIndex == null || endIndex == null
                || startIndex.intValue() >= endIndex.intValue()) return false;
        for (AbstractInsnNode instruction = start.getNext();
             instruction != null && instruction != end;
             instruction = instruction.getNext()) {
            if (instruction.getOpcode() >= 0) return true;
        }
        return false;
    }

    private static boolean hasValidLineNumberTargets(MethodNode method) {
        for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
             insn = insn.getNext()) {
            if (insn instanceof LineNumberNode
                    && nextCode(((LineNumberNode) insn).start) == null) return false;
        }
        return true;
    }

    private static boolean removeGotoNext(MethodNode m, String owner, List<String> rows, Map<AbstractInsnNode,Integer> offsets) {
        boolean changed = false;
        for (AbstractInsnNode n = m.instructions.getFirst(); n != null; ) {
            AbstractInsnNode next = n.getNext();
            if (n instanceof JumpInsnNode && n.getOpcode() == Opcodes.GOTO) {
                AbstractInsnNode target = nextCode(((JumpInsnNode)n).label);
                AbstractInsnNode after = nextCode(n);
                if (target != null && target == after) {
                    int off = offsetOf(n, offsets, m); m.instructions.remove(n);
                    rows.add(row(owner, m.name + m.desc, off, "remove-goto", "target is next executable instruction")); changed = true;
                }
            }
            n = next;
        }
        return changed;
    }

    private static boolean coalesceLabels(MethodNode m, String owner, List<String> rows, Map<AbstractInsnNode,Integer> offsets) {
        Map<LabelNode, LabelNode> aliases = new IdentityHashMap<>(); boolean changed = false;
        int firstOffset = -1;
        for (AbstractInsnNode n = m.instructions.getFirst(); n != null; n = n.getNext()) {
            if (!(n instanceof LabelNode)) continue;
            while (true) {
                AbstractInsnNode x = n.getNext();
                while (x instanceof LineNumberNode || x instanceof FrameNode) x = x.getNext();
                if (!(x instanceof LabelNode)) break;
                aliases.put((LabelNode)x, (LabelNode)n);
                if(firstOffset<0)firstOffset=offsetOf(x,offsets,m);
                m.instructions.remove(x); changed = true;
            }
        }
        if (!aliases.isEmpty()) {
            for (AbstractInsnNode n = m.instructions.getFirst(); n != null; n = n.getNext()) {
                if (n instanceof JumpInsnNode) ((JumpInsnNode)n).label = alias(((JumpInsnNode)n).label, aliases);
                else if (n instanceof TableSwitchInsnNode) { TableSwitchInsnNode t=(TableSwitchInsnNode)n; t.dflt=alias(t.dflt,aliases); for(int i=0;i<t.labels.size();i++) t.labels.set(i,alias(t.labels.get(i),aliases)); }
                else if (n instanceof LookupSwitchInsnNode) { LookupSwitchInsnNode t=(LookupSwitchInsnNode)n; t.dflt=alias(t.dflt,aliases); for(int i=0;i<t.labels.size();i++) t.labels.set(i,alias(t.labels.get(i),aliases)); }
                else if (n instanceof FrameNode) {
                    FrameNode f=(FrameNode)n; replaceFrameLabels(f.local, aliases); replaceFrameLabels(f.stack, aliases);
                }
            }
            for (TryCatchBlockNode t : m.tryCatchBlocks) {
                t.start = alias(t.start, aliases); t.end = alias(t.end, aliases); t.handler = alias(t.handler, aliases);
            }
            if (m.localVariables != null) for (LocalVariableNode v : m.localVariables) {
                v.start = alias(v.start, aliases); v.end = alias(v.end, aliases);
            }
            if (m.visibleLocalVariableAnnotations != null) for (LocalVariableAnnotationNode a : m.visibleLocalVariableAnnotations) updateAnnotationLabels(a, aliases);
            if (m.invisibleLocalVariableAnnotations != null) for (LocalVariableAnnotationNode a : m.invisibleLocalVariableAnnotations) updateAnnotationLabels(a, aliases);
            for (AbstractInsnNode n = m.instructions.getFirst(); n != null; n = n.getNext()) if (n instanceof LineNumberNode) {
                ((LineNumberNode)n).start = alias(((LineNumberNode)n).start, aliases);
            }
            rows.add(row(owner, m.name + m.desc, firstOffset, "coalesce-labels", "merged " + aliases.size() + " consecutive labels"));
        }
        return changed;
    }

    private static void updateAnnotationLabels(LocalVariableAnnotationNode a, Map<LabelNode,LabelNode> aliases) {
        for (int i = 0; i < a.start.size(); i++) a.start.set(i, alias(a.start.get(i), aliases));
        for (int i = 0; i < a.end.size(); i++) a.end.set(i, alias(a.end.get(i), aliases));
    }

    private static void replaceFrameLabels(List<Object> values, Map<LabelNode,LabelNode> aliases) {
        if (values == null) return;
        for (int i=0; i<values.size(); i++) if (values.get(i) instanceof LabelNode) values.set(i, alias((LabelNode) values.get(i), aliases));
    }
    private static Map<AbstractInsnNode,Integer> originalOffsets(MethodNode m) {
        Map<AbstractInsnNode,Integer> result=new IdentityHashMap<>(); int i=0;
        for(AbstractInsnNode n=m.instructions.getFirst();n!=null;n=n.getNext())result.put(n,i++);
        return result;
    }
    private static int offsetOf(AbstractInsnNode n, Map<AbstractInsnNode,Integer> offsets, MethodNode m) {
        Integer value=offsets.get(n); return value == null ? m.instructions.indexOf(n) : value;
    }

    private static LabelNode alias(LabelNode l, Map<LabelNode,LabelNode> a) { LabelNode x=l,y; while ((y=a.get(x)) != null && y != x) x=y; return x; }
    private static AbstractInsnNode prevCode(AbstractInsnNode n) { AbstractInsnNode x=n.getPrevious(); while(x!=null && x.getOpcode()<0)x=x.getPrevious(); return x; }
    private static AbstractInsnNode nextCode(AbstractInsnNode n) { AbstractInsnNode x=n.getNext(); while(x!=null && x.getOpcode()<0)x=x.getNext(); return x; }
    private static boolean isConditional(int op) { return op >= Opcodes.IFEQ && op <= Opcodes.IFLE || op >= Opcodes.IF_ICMPEQ && op <= Opcodes.IF_ICMPLE || op == Opcodes.IF_ACMPEQ || op == Opcodes.IF_ACMPNE || op == Opcodes.IFNULL || op == Opcodes.IFNONNULL; }
    private static boolean isBinaryInt(int op) { return op >= Opcodes.IF_ICMPEQ && op <= Opcodes.IF_ICMPLE; }
    private static Integer intConstant(AbstractInsnNode n) {
        if (n == null) return null; int op=n.getOpcode();
        if (op>=Opcodes.ICONST_M1 && op<=Opcodes.ICONST_5) return op-Opcodes.ICONST_0;
        if (n instanceof IntInsnNode && (op==Opcodes.BIPUSH || op==Opcodes.SIPUSH)) return ((IntInsnNode)n).operand;
        if (n instanceof LdcInsnNode && ((LdcInsnNode)n).cst instanceof Integer) return (Integer)((LdcInsnNode)n).cst;
        return null;
    }
    private static Number numericConstant(AbstractInsnNode n) {
        if (n == null) return null; int op=n.getOpcode();
        if (op==Opcodes.LCONST_0 || op==Opcodes.LCONST_1) return Long.valueOf(op-Opcodes.LCONST_0);
        if (op>=Opcodes.FCONST_0 && op<=Opcodes.FCONST_2) return Float.valueOf(op-Opcodes.FCONST_0);
        if (op==Opcodes.DCONST_0 || op==Opcodes.DCONST_1) return Double.valueOf(op-Opcodes.DCONST_0);
        if (n instanceof LdcInsnNode && ((LdcInsnNode)n).cst instanceof Number) return (Number)((LdcInsnNode)n).cst;
        return null;
    }
    private static boolean isNumericCmp(AbstractInsnNode n) {
        if(n==null)return false; int op=n.getOpcode();
        return op==Opcodes.LCMP || op==Opcodes.FCMPL || op==Opcodes.FCMPG || op==Opcodes.DCMPL || op==Opcodes.DCMPG;
    }
    private static Integer constantNumericCompare(int op, Number left, Number right) {
        if(left==null || right==null)return null;
        if(op==Opcodes.LCMP && left instanceof Long && right instanceof Long) return Long.compare(left.longValue(),right.longValue());
        if((op==Opcodes.FCMPL || op==Opcodes.FCMPG) && left instanceof Float && right instanceof Float) {
            float a=left.floatValue(),b=right.floatValue(); if(Float.isNaN(a)||Float.isNaN(b))return op==Opcodes.FCMPL?-1:1;
            return a<b?-1:(a>b?1:0);
        }
        if((op==Opcodes.DCMPL || op==Opcodes.DCMPG) && left instanceof Double && right instanceof Double) {
            double a=left.doubleValue(),b=right.doubleValue(); if(Double.isNaN(a)||Double.isNaN(b))return op==Opcodes.DCMPL?-1:1;
            return a<b?-1:(a>b?1:0);
        }
        return null;
    }
    private static String opcodeName(int op) {
        switch(op){case Opcodes.LCMP:return "LCMP";case Opcodes.FCMPL:return "FCMPL";case Opcodes.FCMPG:return "FCMPG";case Opcodes.DCMPL:return "DCMPL";case Opcodes.DCMPG:return "DCMPG";default:return "numeric";}
    }
    private static Boolean compareInt(int op,int a,int b) { switch(op){case Opcodes.IF_ICMPEQ:return a==b;case Opcodes.IF_ICMPNE:return a!=b;case Opcodes.IF_ICMPLT:return a<b;case Opcodes.IF_ICMPGE:return a>=b;case Opcodes.IF_ICMPGT:return a>b;case Opcodes.IF_ICMPLE:return a<=b;default:return null;} }
    private static Boolean compareZero(int op,int a) { switch(op){case Opcodes.IFEQ:return a==0;case Opcodes.IFNE:return a!=0;case Opcodes.IFLT:return a<0;case Opcodes.IFGE:return a>=0;case Opcodes.IFGT:return a>0;case Opcodes.IFLE:return a<=0;default:return null;} }
    private static String row(String c,String m,int o,String a,String r){return c+"\t"+m+"\t"+o+"\t"+a+"\t"+r.replace('\t',' ');}
    private static String shortReason(Throwable t){String s=t.getClass().getSimpleName()+":"+String.valueOf(t.getMessage()); return s.replace('\t',' ').replace('\n',' ').substring(0,Math.min(180,s.length()));}
    private static final class Result {
        final byte[] bytes;
        final boolean changed;
        final int failures;

        Result(byte[] bytes, boolean changed, int failures) {
            this.bytes = bytes;
            this.changed = changed;
            this.failures = failures;
        }
    }
}
