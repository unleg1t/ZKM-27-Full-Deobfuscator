package cn.openvape.flowdeobf;

import org.objectweb.asm.ClassReader;
import org.objectweb.asm.Opcodes;
import org.objectweb.asm.tree.AbstractInsnNode;
import org.objectweb.asm.tree.ClassNode;
import org.objectweb.asm.tree.LdcInsnNode;
import org.objectweb.asm.tree.MethodInsnNode;
import org.objectweb.asm.tree.MethodNode;

import java.io.BufferedReader;
import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.SimpleFileVisitor;
import java.nio.file.FileVisitResult;
import java.nio.file.attribute.BasicFileAttributes;
import java.security.MessageDigest;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Comparator;
import java.util.List;
import java.util.Locale;
import java.util.zip.ZipEntry;
import java.util.zip.ZipInputStream;

/**
 * Unified archive-wide DES recovery pipeline.
 *
 * <p>Each stage is proof-driven and archive-transactional.  A stage receives
 * the previous stage's archive, writes a new archive, and records its own
 * candidates, rejections and verifier gate.  No stage loads or initializes a
 * sample class.  The pipeline is deliberately additive: a future DES
 * template can be inserted as another stage without weakening the proofs of
 * existing stages.</p>
 */
public final class ZkmDesPipelineDeobfuscator {
    private static final int MAX_FIXED_POINT_ROUNDS = 8;

    private ZkmDesPipelineDeobfuscator() {
    }

    public static void main(String[] args) throws Exception {
        if (args.length < 2) {
            usage();
            System.exit(2);
        }
        Path input = Paths.get(args[0]);
        Path report = Paths.get(args[1]);
        Path output = null;
        Path authority = null;
        Path semanticEvidence = null;
        int index = 2;
        if (index < args.length && !args[index].startsWith("--")) {
            output = Paths.get(args[index++]);
        }
        while (index < args.length) {
            String option = args[index++];
            if (index >= args.length) {
                throw new IllegalArgumentException("missing value for " + option);
            }
            if ("--runtime-authority".equals(option)) {
                if (authority != null) throw new IllegalArgumentException("duplicate " + option);
                authority = Paths.get(args[index++]);
            } else if ("--runtime-semantic-overrides".equals(option)) {
                if (semanticEvidence != null) {
                    throw new IllegalArgumentException("duplicate " + option);
                }
                semanticEvidence = Paths.get(args[index++]);
            } else {
                throw new IllegalArgumentException("unknown option: " + option);
            }
        }
        Summary summary = run(input, report, output, authority, semanticEvidence);
        System.out.println("stages=" + summary.stageCount
                + " rounds=" + summary.fixedPointRounds
                + " proven=" + summary.provenCandidates
                + " changed=" + summary.changedClasses
                + " failures=" + summary.failures
                + " des_removed=" + summary.desCallsRemoved
                + " des_remaining=" + summary.outputDesCalls
                + " assumption_rewrites=" + summary.assumptionRewrites
                + " proof_mode=" + summary.runtimeProofMode
                + " gate=" + (summary.gatePass ? "PASS" : "FAIL"));
        if (!summary.gatePass || output != null && !summary.outputCommitted) {
            throw new IllegalStateException("archive deobfuscation/publication failed closed; "
                    + "requested output was not published; reason=" + summary.failureReason);
        }
    }

    private static void usage() {
        System.err.println("usage: ZkmDesPipelineDeobfuscator <input.jar> <report-dir>"
                + " [output.jar] [--runtime-authority <pre-removal.jar>]"
                + " [--runtime-semantic-overrides <evidence.tsv>]");
    }

    static Summary run(Path input, Path reportDirectory, Path output)
            throws Exception {
        return run(input, reportDirectory, output, null, null);
    }

    static Summary run(Path input, Path reportDirectory, Path output,
                       Path runtimeAuthority, Path semanticEvidence) throws Exception {
        Path source = input.toAbsolutePath().normalize();
        Path report = reportDirectory.toAbsolutePath().normalize();
        Path target = output == null ? null : output.toAbsolutePath().normalize();
        Path authority = runtimeAuthority == null
                ? source : runtimeAuthority.toAbsolutePath().normalize();
        Path evidence = semanticEvidence == null
                ? null : semanticEvidence.toAbsolutePath().normalize();
        validatePaths(source, report, target, authority, evidence);
        Files.createDirectories(report);
        Summary summary = new Summary();
        summary.input = source.toString();
        summary.output = target == null ? null : target.toString();
        summary.runtimeAuthority = authority.toString();
        summary.runtimeProofMode = evidence == null
                ? "AUTO_PROOF" : "MANUAL_SEMANTIC_EVIDENCE";
        summary.semanticEvidence = evidence == null ? "" : evidence.toString();
        summary.integrityPass = true;
        List<StageResult> stages = new ArrayList<>();
        Path staging = Files.createTempDirectory(report, ".atomic-pipeline-");
        Path current = source;
        try {
            ZkmAtomicPublicationGate.Summary inputAudit =
                    ZkmAtomicPublicationGate.audit(source, report.resolve("input-audit"));
            summary.inputDesCalls = inputAudit.desCipherFactories;
            DeobfuscationResidueScanner.ScanSummary inputGeneral =
                    DeobfuscationResidueScanner.scan(source,
                            report.resolve("input-general-residue"));
            summary.inputIdentityRethrows = inputGeneral.identityRethrowHandlers;
            summary.inputTypedIdentityRethrows =
                    inputGeneral.typedIdentityRethrowHandlers;

            for (int round = 1; round <= MAX_FIXED_POINT_ROUNDS; round++) {
                int beforeChanges = totalChanges(stages);
                String beforeHash = sha256(current);
                current = runFixedPointRound(current, report, staging, round,
                        stages, authority);
                summary.fixedPointRounds = round;
                int roundChanges = totalChanges(stages) - beforeChanges;
                String afterHash = sha256(current);
                if (roundChanges == 0 || beforeHash.equals(afterHash)) {
                    summary.fixedPointConverged = true;
                    break;
                }
            }
            if (!summary.fixedPointConverged) {
                fail(summary, "fixed point did not converge within "
                        + MAX_FIXED_POINT_ROUNDS + " rounds");
                finishSummary(summary, stages);
                writePipelineReport(report, summary, stages);
                return summary;
            }

            ZkmAtomicPublicationGate.Summary preClosure = ZkmAtomicPublicationGate.audit(
                    current, report.resolve("pre-runtime-closure-audit"));
            captureResidue(summary, preClosure);
            DeobfuscationResidueScanner.ScanSummary preGeneral =
                    DeobfuscationResidueScanner.scan(current,
                            report.resolve("pre-runtime-general-residue"));
            captureGeneralResidue(summary, preGeneral);
            summary.automaticPathsExhausted = summary.fixedPointConverged;
            summary.automaticControlFlowClosed = generalControlFlowClosed(preGeneral);
            updateManualRecoveryRequired(summary);
            summary.coverageComplete = preClosure.desResidues() == 0;
            summary.runtimeClosureRequired = requiresRuntimeClosure(preClosure);
            if (summary.runtimeClosureRequired) {
                Path runtimeOutput = staging.resolve("runtime-closure.jar");
                ZkmRuntimeClosureDeobfuscator.Summary runtime = evidence == null
                        ? ZkmRuntimeClosureDeobfuscator.close(current, authority,
                        report.resolve("runtime-closure"), runtimeOutput)
                        : ZkmRuntimeClosureDeobfuscator.close(current, authority,
                        report.resolve("runtime-closure"), runtimeOutput, evidence);
                StageResult runtimeStage = new StageResult("runtime-closure", current,
                        runtimeOutput, runtime.provenClassKeys, runtime.changedClasses,
                        runtime.failures.size() + runtime.outputVerificationErrors,
                        runtime.outputCommitted && runtime.failures.isEmpty()
                                && runtime.outputVerificationErrors == 0);
                stages.add(runtimeStage);
                if (!runtimeStage.gate) {
                    fail(summary, "runtime closure failed; proof_mode="
                            + summary.runtimeProofMode);
                    finishSummary(summary, stages);
                    writePipelineReport(report, summary, stages);
                    return summary;
                }
                current = runtimeOutput;
                summary.runtimeClosureCommitted = true;
                summary.semanticEvidenceRows = runtime.semanticEvidenceRows;
                summary.semanticEvidenceOwners = runtime.semanticEvidenceOwners;
                summary.semanticSitesDirectized = runtime.semanticSitesDirectized;

                // Runtime closure materializes the validated long-key consumers
                // and removes their invokedynamic/bootstrap references.  Only
                // that committed archive is authoritative for deciding that a
                // now-unreferenced DES integer helper can be removed.
                Path postRuntimeHelperOutput = staging.resolve(
                        "post-runtime-nopadding-helper.jar");
                StageExecution postRuntimeHelper = stageHelperDirectization(
                        current, report.resolve("post-runtime-nopadding-helper"),
                        postRuntimeHelperOutput, "post-runtime-nopadding-helper");
                stages.add(postRuntimeHelper.result);
                if (!postRuntimeHelper.result.gate) {
                    fail(summary, "post-runtime NoPadding helper stage failed");
                    finishSummary(summary, stages);
                    writePipelineReport(report, summary, stages);
                    return summary;
                }
                current = postRuntimeHelper.nextInput;
            }

            Path finalFlowOutput = staging.resolve("post-runtime-flow.jar");
            StageExecution finalFlow = stageControlFlow(current,
                    report.resolve("post-runtime-control-flow"), finalFlowOutput);
            stages.add(finalFlow.result);
            if (!finalFlow.result.gate) {
                fail(summary, "post-runtime control-flow stage failed");
                finishSummary(summary, stages);
                writePipelineReport(report, summary, stages);
                return summary;
            }
            current = finalFlow.nextInput;

            Path cleanerOutput = staging.resolve("bootstrap-cleanup.jar");
            StageExecution cleaner = stageBootstrapCleanup(current,
                    report.resolve("bootstrap-cleanup"), cleanerOutput);
            stages.add(cleaner.result);
            if (!cleaner.result.gate) {
                fail(summary, "bootstrap support cleanup failed");
                finishSummary(summary, stages);
                writePipelineReport(report, summary, stages);
                return summary;
            }
            current = cleaner.nextInput;

            ZkmAtomicPublicationGate.Summary finalAudit = ZkmAtomicPublicationGate.audit(
                    current, report.resolve("final-gate-audit"));
            captureResidue(summary, finalAudit);
            DeobfuscationResidueScanner.ScanSummary finalGeneral =
                    DeobfuscationResidueScanner.scan(current,
                            report.resolve("final-general-residue"));
            captureGeneralResidue(summary, finalGeneral);
            summary.automaticPathsExhausted = summary.fixedPointConverged;
            summary.automaticControlFlowClosed = generalControlFlowClosed(finalGeneral);
            updateManualRecoveryRequired(summary);
            summary.desCallsRemoved = summary.inputDesCalls - summary.outputDesCalls;
            summary.coverageComplete = finalAudit.desResidues() == 0;
            summary.integrityPass = finalAudit.integrityPass;
            summary.residueClosurePass = finalAudit.eligible;
            summary.publishableBytecodeCandidate = finalAudit.eligible;
            finishSummary(summary, stages);
            if (!summary.assumptionRewriteGate) {
                summary.manualRecoveryRequired = true;
                appendFailureReason(summary, "control-flow assumption rewrites prevent "
                        + "publication; count=" + summary.assumptionRewrites);
            }
            summary.gatePass = summary.fixedPointConverged && summary.integrityPass
                    && summary.coverageComplete && summary.residueClosurePass
                    && summary.automaticPathsExhausted
                    && summary.automaticControlFlowClosed
                    && summary.assumptionRewriteGate && summary.failures == 0;
            writePipelineReport(report, summary, stages);
            if (!summary.gatePass || target == null) return summary;

            ZkmAtomicPublicationGate.Summary publication =
                    ZkmAtomicPublicationGate.publish(current,
                            report.resolve("final-publication"), target);
            summary.outputCommitted = publication.published;
            if (!summary.outputCommitted) {
                fail(summary, "final atomic publication gate declined candidate");
                summary.gatePass = false;
            }
            writePipelineReportBestEffort(report, summary, stages);
            return summary;
        } catch (Throwable failure) {
            fail(summary, failure.getClass().getSimpleName() + ":"
                    + String.valueOf(failure.getMessage()));
            finishSummary(summary, stages);
            writePipelineReport(report, summary, stages);
            return summary;
        } finally {
            deleteOwnedTree(staging);
        }
    }

    private static Path runFixedPointRound(Path input, Path report, Path staging,
                                           int round, List<StageResult> stages,
                                           Path authority)
            throws Exception {
        Path roundReport = report.resolve(String.format(Locale.ROOT, "round-%02d", round));
        Files.createDirectories(roundReport);
        Path current = input;
        int stage = 1;
        current = accept(stageConstant(current,
                stageReport(roundReport, stage, "pkcs5-constant"),
                stageOutput(staging, round, stage++, "pkcs5-constant")), stages);
        current = accept(stageArray(current,
                stageReport(roundReport, stage, "pkcs5-array"),
                stageOutput(staging, round, stage++, "pkcs5-array")), stages);
        current = accept(stageFragment(current,
                stageReport(roundReport, stage, "pkcs5-fragment"),
                stageOutput(staging, round, stage++, "pkcs5-fragment")), stages);
        current = accept(stageScalar(current,
                stageReport(roundReport, stage, "nopadding-scalar"),
                stageOutput(staging, round, stage++, "nopadding-scalar")), stages);
        current = accept(stageLongArray(current,
                stageReport(roundReport, stage, "nopadding-long-array"),
                stageOutput(staging, round, stage++, "nopadding-long-array"),
                authority), stages);
        current = accept(stageLiteralFragment(current,
                stageReport(roundReport, stage, "nopadding-literal-fragment"),
                stageOutput(staging, round, stage++, "nopadding-literal-fragment")), stages);
        current = accept(stageStringHelperDirectization(current,
                stageReport(roundReport, stage, "pkcs5-helper"),
                stageOutput(staging, round, stage++, "pkcs5-helper")), stages);
        current = accept(stageHelperDirectization(current,
                stageReport(roundReport, stage, "nopadding-helper"),
                stageOutput(staging, round, stage++, "nopadding-helper")), stages);
        current = accept(stageStateFragment(current,
                stageReport(roundReport, stage, "nopadding-state-fragment"),
                stageOutput(staging, round, stage++, "nopadding-state-fragment")), stages);
        current = accept(stageStateArray(current,
                stageReport(roundReport, stage, "pkcs5-state-array"),
                stageOutput(staging, round, stage++, "pkcs5-state-array")), stages);
        if (containsRuntimeState(current)) {
            current = accept(stageStateSwitchHelper(current,
                    stageReport(roundReport, stage, "pkcs5-state-switch-helper"),
                    stageOutput(staging, round, stage, "pkcs5-state-switch-helper")), stages);
        }
        stage++;
        current = accept(stageNoPaddingException(current,
                stageReport(roundReport, stage, "nopadding-exception-fragment"),
                stageOutput(staging, round, stage++, "nopadding-exception-fragment")), stages);
        if (containsRuntimeState(current)) {
            current = accept(stagePkcs5ScalarResult(current,
                    stageReport(roundReport, stage, "pkcs5-scalar-result"),
                    stageOutput(staging, round, stage++, "pkcs5-scalar-result"),
                    authority), stages);
        }
        current = accept(stageFlexibleArray(current,
                stageReport(roundReport, stage, "pkcs5-array-materialization"),
                stageOutput(staging, round, stage++,
                        "pkcs5-array-materialization"), authority), stages);
        current = accept(stageControlFlow(current,
                stageReport(roundReport, stage, "control-flow"),
                stageOutput(staging, round, stage, "control-flow")), stages);
        return current;
    }

    private static Path accept(StageExecution execution, List<StageResult> stages)
            throws IOException {
        stages.add(execution.result);
        if (!execution.result.gate || !Files.isRegularFile(execution.nextInput)) {
            throw new IOException("stage failed closed: " + execution.result.name
                    + "; failures=" + execution.result.failures);
        }
        return execution.nextInput;
    }

    private static Path stageReport(Path roundReport, int index, String name) {
        return roundReport.resolve(String.format(Locale.ROOT, "stage-%02d-%s", index, name));
    }

    private static Path stageOutput(Path staging, int round, int index, String name) {
        return staging.resolve(String.format(Locale.ROOT, "r%02d-s%02d-%s.jar",
                round, index, name));
    }

    private static int totalChanges(List<StageResult> stages) {
        int result = 0;
        for (StageResult stage : stages) result += stage.changed;
        return result;
    }

    private static int countAssumptionRewrites(Path rewriteReport) throws IOException {
        if (!Files.isRegularFile(rewriteReport)) {
            throw new IOException("control-flow rewrite report is missing: " + rewriteReport);
        }
        int count = 0;
        try (BufferedReader reader = Files.newBufferedReader(rewriteReport,
                StandardCharsets.UTF_8)) {
            String line;
            while ((line = reader.readLine()) != null) {
                String[] columns = line.split("\\t", 5);
                if (columns.length >= 4 && columns[3].startsWith("zkm-assumed-")) {
                    count = Math.addExact(count, 1);
                }
            }
        }
        return count;
    }

    private static boolean containsRuntimeState(Path archive) throws IOException {
        boolean state = false;
        boolean graph = false;
        try (ZipInputStream input = new ZipInputStream(Files.newInputStream(archive))) {
            ZipEntry entry;
            while ((entry = input.getNextEntry()) != null) {
                if (ObfRuntimeNames.STATE_CLASS
                        .equals(entry.getName())) state = true;
                if (ObfRuntimeNames.GRAPH_BOOTSTRAP_CLASS
                        .equals(entry.getName())) graph = true;
                if (state && graph) return true;
            }
        }
        return false;
    }

    private static boolean requiresRuntimeClosure(ZkmAtomicPublicationGate.Summary summary) {
        return summary.runtimeDefinitions != 0 || summary.runtimeReferences != 0
                || summary.zkmIndySites != 0;
    }

    private static void captureResidue(Summary target,
                                       ZkmAtomicPublicationGate.Summary source) {
        target.residualDes = source.desResidues();
        target.residualDesTransformationLiterals = source.desTransformationLiterals;
        target.residualDesCipherFactories = source.desCipherFactories;
        target.residualUnresolvedCipherFactories = source.unresolvedCipherFactories;
        target.residualRuntimeDefinitions = source.runtimeDefinitions;
        target.residualRuntimeReferences = source.runtimeReferences;
        target.residualZkmIndy = source.zkmIndySites;
        target.residualSupportReferences = source.zkmSupportReferences;
        target.residualBootstrapFamilies = source.bootstrapSupportFamilies;
        target.outputDesCalls = source.desCipherFactories;
    }

    private static void captureGeneralResidue(
            Summary target, DeobfuscationResidueScanner.ScanSummary source) {
        target.residualIdentityRethrows = source.identityRethrowHandlers;
        target.residualTypedIdentityRethrows = source.typedIdentityRethrowHandlers;
        target.residualLongKeyBootstraps = source.zkmLongKeyBootstraps;
        target.residualLongKeyFields = source.zkmLongKeyFields;
        target.residualLongKeyReads = source.zkmLongKeyReads;
        target.residualLongKeyTransforms = source.zkmLongKeyTransforms;
        target.residualStringIndy = source.stringIndySites;
        target.residualIntegerIndy = source.integerIndySites;
        target.residualMemberIndy = source.memberIndySites;
    }

    private static boolean generalControlFlowClosed(
            DeobfuscationResidueScanner.ScanSummary summary) {
        return summary.malformedClasses == 0 && summary.identityRethrowHandlers == 0
                && summary.typedIdentityRethrowHandlers == 0;
    }

    private static void updateManualRecoveryRequired(Summary summary) {
        boolean residue = summary.residualDes != 0
                || summary.residualRuntimeDefinitions != 0
                || summary.residualRuntimeReferences != 0
                || summary.residualZkmIndy != 0
                || summary.residualSupportReferences != 0
                || summary.residualBootstrapFamilies != 0
                || summary.residualIdentityRethrows != 0
                || summary.residualTypedIdentityRethrows != 0
                || summary.residualLongKeyBootstraps != 0
                || summary.residualLongKeyFields != 0
                || summary.residualLongKeyReads != 0
                || summary.residualLongKeyTransforms != 0
                || summary.residualStringIndy != 0
                || summary.residualIntegerIndy != 0
                || summary.residualMemberIndy != 0;
        summary.manualRecoveryRequired = summary.automaticPathsExhausted && residue;
    }

    private static void validatePaths(Path input, Path report, Path output,
                                      Path authority, Path evidence) throws IOException {
        if (!Files.isRegularFile(input)) {
            throw new IOException("input is not a regular file: " + input);
        }
        if (!Files.isRegularFile(authority)) {
            throw new IOException("runtime authority is not a regular file: " + authority);
        }
        if (evidence != null && !Files.isRegularFile(evidence)) {
            throw new IOException("semantic evidence is not a regular file: " + evidence);
        }
        if (input.equals(report) || output != null && output.equals(report)) {
            throw new IllegalArgumentException("report directory aliases archive path");
        }
        if (output != null && (input.equals(output)
                || Files.exists(output) && Files.isSameFile(input, output))) {
            throw new IllegalArgumentException("output must not replace input");
        }
    }

    private static void finishSummary(Summary summary, List<StageResult> stages) {
        summary.stageCount = stages.size();
        summary.provenCandidates = 0;
        summary.changedClasses = 0;
        summary.assumptionRewrites = 0;
        int stageFailures = 0;
        boolean stageIntegrity = true;
        for (StageResult stage : stages) {
            summary.provenCandidates += stage.proven;
            summary.changedClasses += stage.changed;
            summary.assumptionRewrites += stage.assumptionRewrites;
            stageFailures += stage.failures;
            stageIntegrity &= stage.gate;
        }
        summary.assumptionRewriteGate = summary.assumptionRewrites == 0;
        summary.failures = summary.pipelineFailures + stageFailures;
        summary.integrityPass &= stageIntegrity;
        summary.desCallsRemoved = summary.inputDesCalls - summary.outputDesCalls;
    }

    private static void fail(Summary summary, String reason) {
        summary.pipelineFailures++;
        summary.gatePass = false;
        appendFailureReason(summary, reason);
    }

    private static void appendFailureReason(Summary summary, String reason) {
        String clean = reason == null ? "unknown" : reason.replace('\t', ' ')
                .replace('\r', ' ').replace('\n', ' ');
        summary.failureReason = summary.failureReason.isEmpty()
                ? clean : summary.failureReason + " | " + clean;
    }

    private static void writePipelineReport(Path report, Summary summary,
                                            List<StageResult> stages)
            throws IOException {
        List<String> lines = new ArrayList<>();
        lines.add("stage\tinput\toutput\tproven\tchanged\tfailures\t"
                + "assumption_rewrites\tintegrity_gate");
        for (StageResult stage : stages) {
            lines.add(stage.name + "\t" + stage.input + "\t" + stage.output
                    + "\t" + stage.proven + "\t" + stage.changed + "\t"
                    + stage.failures + "\t" + stage.assumptionRewrites + "\t"
                    + pass(stage.gate));
        }
        lines.add("input=" + summary.input);
        lines.add("output=" + value(summary.output));
        lines.add("fixed_point_rounds=" + summary.fixedPointRounds);
        lines.add("fixed_point_converged=" + summary.fixedPointConverged);
        lines.add("automatic_paths_exhausted=" + summary.automaticPathsExhausted);
        lines.add("automatic_control_flow_closed="
                + summary.automaticControlFlowClosed);
        lines.add("manual_recovery_required=" + summary.manualRecoveryRequired);
        lines.add("publishable_bytecode_candidate="
                + summary.publishableBytecodeCandidate);
        lines.add("runtime_closure_required=" + summary.runtimeClosureRequired);
        lines.add("runtime_closure_committed=" + summary.runtimeClosureCommitted);
        lines.add("runtime_proof_mode=" + summary.runtimeProofMode);
        lines.add("runtime_authority=" + summary.runtimeAuthority);
        lines.add("semantic_evidence=" + summary.semanticEvidence);
        lines.add("semantic_evidence_rows=" + summary.semanticEvidenceRows);
        lines.add("semantic_evidence_owners=" + summary.semanticEvidenceOwners);
        lines.add("semantic_sites_directized=" + summary.semanticSitesDirectized);
        lines.add("residual_des_gate_signals=" + summary.residualDes);
        lines.add("residual_des_transformation_literals="
                + summary.residualDesTransformationLiterals);
        lines.add("residual_des_cipher_factories="
                + summary.residualDesCipherFactories);
        lines.add("residual_unresolved_cipher_factories="
                + summary.residualUnresolvedCipherFactories);
        lines.add("residual_runtime_definitions=" + summary.residualRuntimeDefinitions);
        lines.add("residual_runtime_references=" + summary.residualRuntimeReferences);
        lines.add("residual_zkm_indy=" + summary.residualZkmIndy);
        lines.add("residual_support_references=" + summary.residualSupportReferences);
        lines.add("residual_bootstrap_families=" + summary.residualBootstrapFamilies);
        lines.add("residual_identity_rethrows=" + summary.residualIdentityRethrows);
        lines.add("residual_typed_identity_rethrows="
                + summary.residualTypedIdentityRethrows);
        lines.add("input_identity_rethrows=" + summary.inputIdentityRethrows);
        lines.add("input_typed_identity_rethrows="
                + summary.inputTypedIdentityRethrows);
        lines.add("identity_rethrow_delta="
                + (summary.residualIdentityRethrows - summary.inputIdentityRethrows));
        lines.add("typed_identity_rethrow_delta="
                + (summary.residualTypedIdentityRethrows
                - summary.inputTypedIdentityRethrows));
        lines.add("residual_long_key_bootstraps=" + summary.residualLongKeyBootstraps);
        lines.add("residual_long_key_fields=" + summary.residualLongKeyFields);
        lines.add("residual_long_key_reads=" + summary.residualLongKeyReads);
        lines.add("residual_long_key_transforms=" + summary.residualLongKeyTransforms);
        lines.add("residual_string_indy=" + summary.residualStringIndy);
        lines.add("residual_integer_indy=" + summary.residualIntegerIndy);
        lines.add("residual_member_indy=" + summary.residualMemberIndy);
        lines.add("proven_candidates=" + summary.provenCandidates);
        lines.add("changed_classes=" + summary.changedClasses);
        lines.add("assumption_rewrites=" + summary.assumptionRewrites);
        lines.add("failures=" + summary.failures);
        lines.add("failure_reason=" + summary.failureReason);
        lines.add("input_des_calls=" + summary.inputDesCalls);
        lines.add("output_des_calls=" + summary.outputDesCalls);
        lines.add("des_calls_removed=" + summary.desCallsRemoved);
        lines.add("integrity_gate=" + pass(summary.integrityPass));
        lines.add("coverage_gate=" + pass(summary.coverageComplete));
        lines.add("residue_closure_gate=" + pass(summary.residueClosurePass));
        lines.add("assumption_rewrite_gate=" + pass(summary.assumptionRewriteGate));
        lines.add("output_committed=" + summary.outputCommitted);
        lines.add("publication_policy=single-candidate; same-filesystem atomic move required");
        lines.add("staging_policy=owned temporary archives; removed after completion");
        lines.add("input_classes_loaded=false");
        lines.add("input_classes_initialized=false");
        lines.add("gate=" + pass(summary.gatePass));
        Files.write(report.resolve("pipeline.tsv"), lines, StandardCharsets.UTF_8);
        Files.write(report.resolve("gate.txt"),
                Collections.singletonList(pass(summary.gatePass)), StandardCharsets.UTF_8);
    }

    private static void writePipelineReportBestEffort(Path report, Summary summary,
                                                      List<StageResult> stages) {
        try {
            writePipelineReport(report, summary, stages);
        } catch (IOException ignored) {
            // All required reports were written before the final atomic publication.
        }
    }

    private static String pass(boolean value) {
        return value ? "PASS" : "FAIL";
    }

    private static String value(String value) {
        return value == null ? "" : value;
    }

    private static String sha256(Path archive) throws Exception {
        MessageDigest digest = MessageDigest.getInstance("SHA-256");
        try (java.io.InputStream input = Files.newInputStream(archive)) {
            byte[] buffer = new byte[8192];
            int count;
            while ((count = input.read(buffer)) >= 0) {
                if (count != 0) digest.update(buffer, 0, count);
            }
        }
        StringBuilder result = new StringBuilder();
        for (byte value : digest.digest()) {
            result.append(String.format(Locale.ROOT, "%02X", value & 0xff));
        }
        return result.toString();
    }

    private static void deleteOwnedTree(Path root) {
        if (root == null || !Files.exists(root)) return;
        try {
            Files.walkFileTree(root, new SimpleFileVisitor<Path>() {
                @Override public FileVisitResult visitFile(Path file,
                                                           BasicFileAttributes attrs)
                        throws IOException {
                    Files.deleteIfExists(file);
                    return FileVisitResult.CONTINUE;
                }

                @Override public FileVisitResult postVisitDirectory(Path directory,
                                                                    IOException failure)
                        throws IOException {
                    if (failure != null) throw failure;
                    Files.deleteIfExists(directory);
                    return FileVisitResult.CONTINUE;
                }
            });
        } catch (IOException ignored) {
            // A staging cleanup failure cannot make a partial archive become the target.
        }
    }

    private static StageExecution stageConstant(Path input, Path report, Path output)
            throws Exception {
        ZkmDirectStringConstantDeobfuscator.Summary result =
                ZkmDirectStringConstantDeobfuscator.deobfuscate(input, report, output);
        StageResult stage = new StageResult("pkcs5-constant", input, output,
                result.provenCandidates, result.changedClasses,
                result.classRollbacks + result.outputVerificationErrors,
                result.classRollbacks == 0 && result.outputVerificationErrors == 0
                        && (output == null || result.outputCommitted));
        return new StageExecution(output == null ? input : output, stage);
    }

    private static StageExecution stageArray(Path input, Path report, Path output)
            throws Exception {
        ZkmDirectStringArrayDeobfuscator.Summary result =
                ZkmDirectStringArrayDeobfuscator.deobfuscate(input, report, output);
        StageResult stage = new StageResult("pkcs5-array", input, output,
                result.provenCandidates, result.changedClasses,
                result.classRollbacks + result.outputVerificationErrors,
                result.classRollbacks == 0 && result.outputVerificationErrors == 0
                        && (output == null || result.outputCommitted));
        return new StageExecution(output == null ? input : output, stage);
    }

    private static StageExecution stageFragment(Path input, Path report, Path output)
            throws Exception {
        ZkmDirectStringFragmentDeobfuscator.Summary result =
                ZkmDirectStringFragmentDeobfuscator.deobfuscate(input, report, output);
        StageResult stage = new StageResult("pkcs5-fragment", input, output,
                result.provenCandidates, result.changedClasses,
                result.classRollbacks + result.outputVerificationErrors,
                result.classRollbacks == 0 && result.outputVerificationErrors == 0
                        && (output == null || result.outputCommitted));
        return new StageExecution(output == null ? input : output, stage);
    }

    private static StageExecution stageScalar(Path input, Path report, Path output)
            throws Exception {
        ZkmNoPaddingScalarDeobfuscator.Summary result =
                ZkmNoPaddingScalarDeobfuscator.rewrite(input, report, output);
        StageResult stage = new StageResult("nopadding-scalar", input, output,
                result.proven, result.changedClasses,
                result.rollbacks + result.outputVerificationErrors,
                result.rollbacks == 0 && result.outputVerificationErrors == 0
                        && (output == null || result.outputCommitted));
        return new StageExecution(output == null ? input : output, stage);
    }

    private static StageExecution stageLongArray(Path input, Path report, Path output,
                                                 Path authority)
            throws Exception {
        ZkmNoPaddingLongArrayDeobfuscator.Summary result =
                ZkmNoPaddingLongArrayDeobfuscator.rewrite(input, report, output,
                        authority);
        StageResult stage = new StageResult("nopadding-long-array", input, output,
                result.proven, result.changedClasses,
                result.rollbacks + result.outputVerificationErrors,
                result.rollbacks == 0 && result.outputVerificationErrors == 0
                        && (output == null || result.outputCommitted));
        return new StageExecution(output == null ? input : output, stage);
    }

    private static StageExecution stageLiteralFragment(Path input, Path report,
                                                       Path output) throws Exception {
        ZkmNoPaddingLiteralFragmentDeobfuscator.Summary result =
                ZkmNoPaddingLiteralFragmentDeobfuscator.rewrite(input, report, output);
        StageResult stage = new StageResult("nopadding-literal-fragment", input,
                output, result.proven, result.changedClasses,
                result.rollbacks + result.outputVerificationErrors,
                result.rollbacks == 0 && result.outputVerificationErrors == 0
                        && (output == null || result.outputCommitted));
        return new StageExecution(output == null ? input : output, stage);
    }

    private static StageExecution stageHelperDirectization(Path input, Path report,
                                                            Path output)
            throws Exception {
        return stageHelperDirectization(input, report, output, "nopadding-helper");
    }

    private static StageExecution stageHelperDirectization(Path input, Path report,
                                                            Path output,
                                                            String stageName)
            throws Exception {
        ZkmDesHelperDeobfuscator.Summary result =
                ZkmDesHelperDeobfuscator.rewrite(input, report, output);
        StageResult stage = new StageResult(stageName, input, output,
                result.helpersRemoved, result.changedClasses,
                result.rollbacks + result.outputVerificationErrors,
                result.rollbacks == 0 && result.outputVerificationErrors == 0
                        && (output == null || result.outputCommitted));
        return new StageExecution(output == null ? input : output, stage);
    }

    private static StageExecution stageStringHelperDirectization(Path input,
                                                                  Path report,
                                                                  Path output)
            throws Exception {
        ZkmDirectStringHelperDeobfuscator.Summary result =
                ZkmDirectStringHelperDeobfuscator.rewrite(input, report, output);
        StageResult stage = new StageResult("pkcs5-helper", input, output,
                result.provenClasses, result.changedClasses,
                result.classRollbacks + result.outputVerificationErrors,
                result.classRollbacks == 0 && result.outputVerificationErrors == 0
                        && (output == null || result.outputCommitted));
        return new StageExecution(output == null ? input : output, stage);
    }

    private static StageExecution stageStateFragment(Path input, Path report,
                                                     Path output) throws Exception {
        ZkmNoPaddingLiteralFragmentDeobfuscator.Summary result =
                ZkmNoPaddingStateFragmentDeobfuscator.rewrite(input, report, output);
        StageResult stage = new StageResult("nopadding-state-fragment", input,
                output, result.proven, result.changedClasses,
                result.rollbacks + result.outputVerificationErrors,
                result.rollbacks == 0 && result.outputVerificationErrors == 0
                        && (output == null || result.outputCommitted));
        return new StageExecution(output == null ? input : output, stage);
    }

    private static StageExecution stageControlFlow(Path input, Path report,
                                                   Path output) throws Exception {
        Path rewriteReport = report.resolve("rewrite.tsv");
        ControlFlowDeobfuscator.Summary result = ControlFlowDeobfuscator.rewrite(
                input, output, rewriteReport, true, true, true, true, true,
                true, true);
        int assumptionRewrites = countAssumptionRewrites(rewriteReport);
        StageResult stage = new StageResult("control-flow", input, output,
                result.changed, result.changed, result.failures,
                result.failures == 0 && result.outputCommitted, assumptionRewrites);
        return new StageExecution(output, stage);
    }

    private static StageExecution stageFlexibleArray(Path input, Path report,
                                                      Path output, Path authority)
            throws Exception {
        ZkmDirectStringArrayDeobfuscator.Summary result =
                ZkmDirectStringArrayDeobfuscator.deobfuscateFlexibleMaterialization(
                        input, report, output, authority);
        StageResult stage = new StageResult("pkcs5-array-materialization", input,
                output, result.provenCandidates, result.changedClasses,
                result.classRollbacks + result.outputVerificationErrors,
                result.classRollbacks == 0 && result.outputVerificationErrors == 0
                        && result.outputCommitted
                        && (result.provenCandidates == 0
                        || result.outputPkcs5ClinitClasses
                        < result.pkcs5ClinitClasses));
        return new StageExecution(output, stage);
    }

    private static StageExecution stageStateArray(Path input, Path report, Path output)
            throws Exception {
        ZkmDirectStringArrayDeobfuscator.Summary result =
                ZkmPkcs5StateArrayDeobfuscator.rewrite(input, report, output);
        StageResult stage = new StageResult("pkcs5-state-array", input, output,
                result.provenCandidates, result.changedClasses,
                result.classRollbacks + result.outputVerificationErrors,
                result.classRollbacks == 0 && result.outputVerificationErrors == 0
                        && result.outputCommitted);
        return new StageExecution(output, stage);
    }

    private static StageExecution stageStateSwitchHelper(Path input, Path report,
                                                         Path output) throws Exception {
        ZkmDirectStringHelperDeobfuscator.Summary result =
                ZkmPkcs5StateSwitchHelperDeobfuscator.rewrite(input, report, output);
        StageResult stage = new StageResult("pkcs5-state-switch-helper", input, output,
                result.provenClasses, result.changedClasses,
                result.classRollbacks + result.outputVerificationErrors,
                result.classRollbacks == 0 && result.outputVerificationErrors == 0
                        && result.outputCommitted);
        return new StageExecution(output, stage);
    }

    private static StageExecution stageNoPaddingException(Path input, Path report,
                                                          Path output) throws Exception {
        ZkmNoPaddingExceptionFragmentDeobfuscator.Summary result =
                ZkmNoPaddingExceptionFragmentDeobfuscator.rewrite(input, report, output);
        StageResult stage = new StageResult("nopadding-exception-fragment", input,
                output, result.proven, result.changedClasses,
                result.rollbacks + result.outputVerificationErrors,
                result.rollbacks == 0 && result.outputVerificationErrors == 0
                        && result.outputCommitted);
        return new StageExecution(output, stage);
    }

    private static StageExecution stagePkcs5ScalarResult(Path input, Path report,
                                                         Path output,
                                                         Path authority) throws Exception {
        ZkmPkcs5ScalarResultDeobfuscator.Summary result =
                ZkmPkcs5ScalarResultDeobfuscator.rewrite(input, report, output,
                        authority);
        StageResult stage = new StageResult("pkcs5-scalar-result", input, output,
                result.proven, result.changedClasses,
                result.rollbacks + result.outputVerificationErrors,
                result.rollbacks == 0 && result.outputVerificationErrors == 0
                        && result.outputCommitted);
        return new StageExecution(output, stage);
    }

    private static StageExecution stageBootstrapCleanup(Path input, Path report,
                                                        Path output) throws Exception {
        ZkmBootstrapSupportCleaner.Summary result =
                ZkmBootstrapSupportCleaner.clean(input, report, output);
        StageResult stage = new StageResult("bootstrap-cleanup", input, output,
                result.verifiedFamilies, result.changedClasses,
                result.classRollbacks + result.outputVerificationErrors,
                result.classRollbacks == 0 && result.outputVerificationErrors == 0
                        && result.outputCommitted);
        return new StageExecution(output, stage);
    }

    static final class Summary {
        String input;
        String output;
        String runtimeAuthority = "";
        String runtimeProofMode = "AUTO_PROOF";
        String semanticEvidence = "";
        String failureReason = "";
        int stageCount;
        int fixedPointRounds;
        int provenCandidates;
        int changedClasses;
        int assumptionRewrites;
        int failures;
        int pipelineFailures;
        int inputDesCalls;
        int inputIdentityRethrows;
        int inputTypedIdentityRethrows;
        int outputDesCalls;
        int desCallsRemoved;
        int semanticEvidenceRows;
        int semanticEvidenceOwners;
        int semanticSitesDirectized;
        int residualDes;
        int residualDesTransformationLiterals;
        int residualDesCipherFactories;
        int residualUnresolvedCipherFactories;
        int residualRuntimeDefinitions;
        int residualRuntimeReferences;
        int residualZkmIndy;
        int residualSupportReferences;
        int residualBootstrapFamilies;
        int residualIdentityRethrows;
        int residualTypedIdentityRethrows;
        int residualLongKeyBootstraps;
        int residualLongKeyFields;
        int residualLongKeyReads;
        int residualLongKeyTransforms;
        int residualStringIndy;
        int residualIntegerIndy;
        int residualMemberIndy;
        boolean integrityPass;
        boolean coverageComplete;
        boolean fixedPointConverged;
        boolean automaticPathsExhausted;
        boolean automaticControlFlowClosed;
        boolean manualRecoveryRequired;
        boolean runtimeClosureRequired;
        boolean runtimeClosureCommitted;
        boolean residueClosurePass;
        boolean assumptionRewriteGate = true;
        boolean publishableBytecodeCandidate;
        boolean gatePass;
        boolean outputCommitted;
    }

    private static final class StageResult {
        final String name;
        final String input;
        final String output;
        final int proven;
        final int changed;
        final int failures;
        final boolean gate;
        final int assumptionRewrites;

        StageResult(String name, Path input, Path output, int proven, int changed,
                    int failures, boolean gate) {
            this(name, input, output, proven, changed, failures, gate, 0);
        }

        StageResult(String name, Path input, Path output, int proven, int changed,
                    int failures, boolean gate, int assumptionRewrites) {
            this.name = name;
            this.input = input.toAbsolutePath().normalize().toString();
            this.output = output == null ? "" : output.toAbsolutePath().normalize().toString();
            this.proven = proven;
            this.changed = changed;
            this.failures = failures;
            this.gate = gate;
            this.assumptionRewrites = assumptionRewrites;
        }
    }

    private static final class StageExecution {
        final Path nextInput;
        final StageResult result;

        StageExecution(Path nextInput, StageResult result) {
            this.nextInput = nextInput;
            this.result = result;
        }
    }
}
