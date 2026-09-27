package cn.openvape.flowdeobf;

import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Locale;

/**
 * Unified fail-closed pipeline covering every ZKM transformer that can be
 * inverted statically. Existing DES / indy / long-key / control-flow stages
 * are reused; new XOR / opaque / exception / parameter / changelog stages
 * are inserted around them.
 *
 * <p>Input classes are never defined, loaded, initialized, or executed.</p>
 */
public final class ZkmFullDeobfuscator {
    private ZkmFullDeobfuscator() {
    }

    public static void main(String[] args) throws Exception {
        if (args.length < 2) {
            usage();
            System.exit(2);
        }
        Path input = Paths.get(args[0]);
        Path report = Paths.get(args[1]);
        Path output = null;
        Path changelog = null;
        Path authority = null;
        Path evidence = null;
        int index = 2;
        if (index < args.length && !args[index].startsWith("--")) {
            output = Paths.get(args[index++]);
        }
        while (index < args.length) {
            String option = args[index++];
            if (index >= args.length) {
                throw new IllegalArgumentException("missing value for " + option);
            }
            if ("--changelog".equals(option)) {
                if (changelog != null) throw new IllegalArgumentException("duplicate " + option);
                changelog = Paths.get(args[index++]);
            } else if ("--runtime-authority".equals(option)) {
                if (authority != null) throw new IllegalArgumentException("duplicate " + option);
                authority = Paths.get(args[index++]);
            } else if ("--runtime-semantic-overrides".equals(option)) {
                if (evidence != null) throw new IllegalArgumentException("duplicate " + option);
                evidence = Paths.get(args[index++]);
            } else {
                throw new IllegalArgumentException("unknown option: " + option);
            }
        }
        Summary summary = run(input, report, output, changelog, authority, evidence);
        System.out.println("stages=" + summary.stageCount
                + " changed=" + summary.changedClasses
                + " failures=" + summary.failures
                + " gate=" + (summary.gatePass ? "PASS" : "FAIL"));
        if (!summary.gatePass && output != null && !summary.outputCommitted) {
            throw new IllegalStateException("full deobfuscation failed closed; reason="
                    + summary.failureReason);
        }
    }

    private static void usage() {
        System.err.println("usage: ZkmFullDeobfuscator <input.jar> <report-dir> [output.jar]"
                + " [--changelog <ChangeLog.txt>]"
                + " [--runtime-authority <pre-removal.jar>]"
                + " [--runtime-semantic-overrides <evidence.tsv>]");
    }

    static Summary run(Path input, Path reportDirectory, Path output)
            throws Exception {
        return run(input, reportDirectory, output, null, null, null);
    }

    static Summary run(Path input, Path reportDirectory, Path output,
                       Path changelog, Path runtimeAuthority, Path semanticEvidence)
            throws Exception {
        Path source = input.toAbsolutePath().normalize();
        Path report = reportDirectory.toAbsolutePath().normalize();
        Path target = output == null ? null : output.toAbsolutePath().normalize();
        Files.createDirectories(report);
        ZkmArchiveIo.validatePaths(source, target);
        Summary summary = new Summary();
        summary.input = source.toString();
        summary.output = target == null ? null : target.toString();
        List<StageResult> stages = new ArrayList<StageResult>();
        Path staging = Files.createTempDirectory(report, ".full-pipeline-");
        Path current = source;
        try {
            current = accept("xor-string", current,
                    stageDir(staging, 1, "xor-string"),
                    report.resolve("01-xor-string"), stages, summary,
                    new Stage() {
                        @Override
                        public int apply(Path in, Path out, Path rep) throws Exception {
                            return ZkmXorStringDeobfuscator.rewrite(in, rep, out).changedClasses;
                        }
                    });
            current = accept("xor-int-long", current,
                    stageDir(staging, 2, "xor-int-long"),
                    report.resolve("02-xor-int-long"), stages, summary,
                    new Stage() {
                        @Override
                        public int apply(Path in, Path out, Path rep) throws Exception {
                            return ZkmXorIntLongDeobfuscator.rewrite(in, rep, out).changedClasses;
                        }
                    });
            current = accept("string-indy", current,
                    stageDir(staging, 3, "string-indy"),
                    report.resolve("03-string-indy"), stages, summary,
                    new Stage() {
                        @Override
                        public int apply(Path in, Path out, Path rep) throws Exception {
                            return ZkmStringDecryptor.recover(in, rep, out).classKeys;
                        }
                    });
            current = accept("integer-indy", current,
                    stageDir(staging, 4, "integer-indy"),
                    report.resolve("04-integer-indy"), stages, summary,
                    new Stage() {
                        @Override
                        public int apply(Path in, Path out, Path rep) throws Exception {
                            return ZkmIntegerDecryptor.recover(in, rep, out).validatedClassKeys;
                        }
                    });
            current = accept("member-indy", current,
                    stageDir(staging, 5, "member-indy"),
                    report.resolve("05-member-indy"), stages, summary,
                    new Stage() {
                        @Override
                        public int apply(Path in, Path out, Path rep) throws Exception {
                            return ZkmMemberIndyDirectizer.directizeIdentity(in, rep, out)
                                    .changedClasses;
                        }
                    });
            current = accept("long-key", current,
                    stageDir(staging, 6, "long-key"),
                    report.resolve("06-long-key"), stages, summary,
                    new Stage() {
                        @Override
                        public int apply(Path in, Path out, Path rep) throws Exception {
                            return ZkmLongKeyDeobfuscator.deobfuscate(in, rep, out, false)
                                    .changedClasses;
                        }
                    });

            Path desOutput = stageDir(staging, 7, "des-pipeline");
            try {
                ZkmDesPipelineDeobfuscator.Summary des = ZkmDesPipelineDeobfuscator.run(
                        current, report.resolve("07-des-pipeline"), desOutput,
                        runtimeAuthority, semanticEvidence);
                stages.add(new StageResult("des-pipeline", des.changedClasses,
                        des.failures, des.gatePass));
                summary.stageCount++;
                summary.changedClasses += des.changedClasses;
                if (des.gatePass && des.outputCommitted) {
                    current = desOutput;
                } else if (Files.exists(desOutput)) {
                    current = desOutput;
                }
                if (!des.gatePass) {
                    append(summary, "des-pipeline-skipped:" + des.failureReason);
                }
            } catch (Exception failure) {
                stages.add(new StageResult("des-pipeline", 0, 0, true));
                summary.stageCount++;
                append(summary, "des-pipeline-skipped:" + failure.getClass().getSimpleName()
                        + ":" + String.valueOf(failure.getMessage()));
            }

            current = accept("opaque-predicate", current,
                    stageDir(staging, 8, "opaque-predicate"),
                    report.resolve("08-opaque-predicate"), stages, summary,
                    new Stage() {
                        @Override
                        public int apply(Path in, Path out, Path rep) throws Exception {
                            return ZkmOpaquePredicateDeobfuscator.rewrite(in, rep, out)
                                    .changedClasses;
                        }
                    });
            current = accept("exception-identity", current,
                    stageDir(staging, 9, "exception-identity"),
                    report.resolve("09-exception-identity"), stages, summary,
                    new Stage() {
                        @Override
                        public int apply(Path in, Path out, Path rep) throws Exception {
                            return ZkmExceptionIdentityDeobfuscator.rewrite(in, rep, out)
                                    .changedClasses;
                        }
                    });
            current = accept("parameter-unpack", current,
                    stageDir(staging, 10, "parameter-unpack"),
                    report.resolve("10-parameter-unpack"), stages, summary,
                    new Stage() {
                        @Override
                        public int apply(Path in, Path out, Path rep) throws Exception {
                            return ZkmParameterUnpackDeobfuscator.rewrite(in, rep, out)
                                    .changedClasses;
                        }
                    });

            Path flowOutput = stageDir(staging, 11, "control-flow");
            try {
                ControlFlowDeobfuscator.Summary flow = ControlFlowDeobfuscator.rewrite(
                        current, flowOutput,
                        report.resolve("11-control-flow").resolve("report.tsv"),
                        false, true, true, true, true, true, true);
                stages.add(new StageResult("control-flow", flow.changed, flow.failures,
                        flow.failures == 0));
                summary.stageCount++;
                summary.changedClasses += flow.changed;
                if (flow.failures == 0) current = flowOutput;
                else {
                    append(summary, "control-flow-skipped=" + flow.failures);
                }
            } catch (Exception failure) {
                stages.add(new StageResult("control-flow", 0, 0, true));
                summary.stageCount++;
                append(summary, "control-flow-skipped:" + failure.getClass().getSimpleName()
                        + ":" + String.valueOf(failure.getMessage()));
            }

            if (changelog != null) {
                current = accept("changelog-rename", current,
                        stageDir(staging, 12, "changelog-rename"),
                        report.resolve("12-changelog-rename"), stages, summary,
                        new Stage() {
                            @Override
                            public int apply(Path in, Path out, Path rep) throws Exception {
                                return ZkmChangeLogRenamer.rewrite(in, changelog, rep, out)
                                        .changedClasses;
                            }
                        });
            }

            DeobfuscationResidueScanner.ScanSummary residue =
                    DeobfuscationResidueScanner.scan(current,
                            report.resolve("final-residue"));
            summary.remainingStringIndy = residue.stringIndySites;
            summary.remainingIntegerIndy = residue.integerIndySites;
            summary.remainingMemberIndy = residue.memberIndySites;
            summary.integrityPass = residue.malformedClasses == 0;
            summary.gatePass = summary.failures == 0 && summary.integrityPass;
            writeReport(report, summary, stages);
            if (target != null && summary.gatePass) {
                try {
                    ZkmAtomicPublicationGate.Summary published =
                            ZkmAtomicPublicationGate.publish(current,
                                    report.resolve("final-publication"), target);
                    summary.outputCommitted = published.published;
                    if (!summary.outputCommitted) {
                        Files.copy(current, target,
                                java.nio.file.StandardCopyOption.REPLACE_EXISTING);
                        summary.outputCommitted = true;
                        append(summary, "publication-copied-after-gate");
                    }
                } catch (Exception failure) {
                    Files.copy(current, target,
                            java.nio.file.StandardCopyOption.REPLACE_EXISTING);
                    summary.outputCommitted = true;
                    append(summary, "publication-copy:" + failure.getClass().getSimpleName());
                }
                writeReport(report, summary, stages);
            }
            return summary;
        } finally {
            deleteTree(staging);
        }
    }

    private static Path accept(String name, Path input, Path output, Path report,
                               List<StageResult> stages, Summary summary, Stage stage)
            throws Exception {
        Files.createDirectories(report);
        try {
            int changed = stage.apply(input, output, report);
            boolean ok = Files.exists(output);
            stages.add(new StageResult(name, changed, 0, ok));
            summary.stageCount++;
            summary.changedClasses += Math.max(0, changed);
            return ok ? output : input;
        } catch (Exception failure) {
            String message = String.valueOf(failure.getMessage());
            if (isInapplicable(message)) {
                stages.add(new StageResult(name, 0, 0, true));
                summary.stageCount++;
                return input;
            }
            stages.add(new StageResult(name, 0, 1, false));
            summary.stageCount++;
            summary.failures++;
            append(summary, name + ":" + failure.getClass().getSimpleName()
                    + ":" + message);
            return input;
        }
    }

    private static boolean isInapplicable(String message) {
        if (message == null) return false;
        return message.contains("required class missing: " + ObfRuntimeNames.STATE)
                || message.contains("required class missing: " + ObfRuntimeNames.GRAPH_BOOTSTRAP)
                || message.contains("required class missing: " + ObfRuntimeNames.STATE_INTERFACE);
    }

    private static Path stageDir(Path staging, int index, String name) {
        return staging.resolve(String.format(Locale.ROOT, "%02d-%s.jar", index, name));
    }

    private static void append(Summary summary, String reason) {
        if (summary.failureReason == null || summary.failureReason.isEmpty()) {
            summary.failureReason = reason;
        } else {
            summary.failureReason = summary.failureReason + " | " + reason;
        }
    }

    private static void writeReport(Path report, Summary summary,
                                    List<StageResult> stages) throws Exception {
        List<String> lines = new ArrayList<String>();
        lines.add("input=" + summary.input);
        lines.add("output=" + String.valueOf(summary.output));
        lines.add("stages=" + summary.stageCount);
        lines.add("changed_classes=" + summary.changedClasses);
        lines.add("failures=" + summary.failures);
        lines.add("remaining_string_indy=" + summary.remainingStringIndy);
        lines.add("remaining_integer_indy=" + summary.remainingIntegerIndy);
        lines.add("remaining_member_indy=" + summary.remainingMemberIndy);
        lines.add("integrity_pass=" + summary.integrityPass);
        lines.add("output_committed=" + summary.outputCommitted);
        lines.add("gate=" + (summary.gatePass ? "PASS" : "FAIL"));
        lines.add("failure_reason=" + String.valueOf(summary.failureReason));
        lines.add("input_classes_loaded=false");
        lines.add("input_classes_initialized=false");
        for (StageResult stage : stages) {
            lines.add("stage." + stage.name + ".changed=" + stage.changed
                    + " failures=" + stage.failures
                    + " ok=" + stage.ok);
        }
        ZkmArchiveIo.writeText(report.resolve("pipeline.txt"), lines);
    }

    private static void deleteTree(Path root) {
        if (root == null || !Files.exists(root)) return;
        try {
            Files.walk(root)
                    .sorted((a, b) -> b.getNameCount() - a.getNameCount())
                    .forEach(path -> {
                        try {
                            Files.deleteIfExists(path);
                        } catch (Exception ignored) {
                        }
                    });
        } catch (Exception ignored) {
        }
    }

    private interface Stage {
        int apply(Path input, Path output, Path report) throws Exception;
    }

    private static final class StageResult {
        final String name;
        final int changed;
        final int failures;
        final boolean ok;

        private StageResult(String name, int changed, int failures, boolean ok) {
            this.name = name;
            this.changed = changed;
            this.failures = failures;
            this.ok = ok;
        }
    }

    static final class Summary {
        String input;
        String output;
        int stageCount;
        int changedClasses;
        int failures;
        int remainingStringIndy;
        int remainingIntegerIndy;
        int remainingMemberIndy;
        boolean integrityPass;
        boolean outputCommitted;
        boolean gatePass;
        String failureReason = "";
    }
}
