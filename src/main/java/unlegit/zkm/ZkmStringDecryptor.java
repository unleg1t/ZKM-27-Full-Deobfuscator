package unlegit.zkm;

import org.objectweb.asm.ClassReader;
import org.objectweb.asm.ClassWriter;
import org.objectweb.asm.Opcodes;
import org.objectweb.asm.Type;
import org.objectweb.asm.tree.AbstractInsnNode;
import org.objectweb.asm.tree.FieldInsnNode;
import org.objectweb.asm.tree.FieldNode;
import org.objectweb.asm.tree.InvokeDynamicInsnNode;
import org.objectweb.asm.tree.LdcInsnNode;
import org.objectweb.asm.tree.MethodInsnNode;
import org.objectweb.asm.tree.MethodNode;
import org.objectweb.asm.tree.ClassNode;
import org.objectweb.asm.tree.IntInsnNode;
import org.objectweb.asm.tree.TypeInsnNode;
import org.objectweb.asm.tree.VarInsnNode;
import org.objectweb.asm.tree.analysis.Analyzer;
import org.objectweb.asm.tree.analysis.BasicVerifier;
import org.objectweb.asm.tree.analysis.Frame;
import org.objectweb.asm.tree.analysis.SourceInterpreter;
import org.objectweb.asm.tree.analysis.SourceValue;
import org.objectweb.asm.util.CheckClassAdapter;

import javax.crypto.Cipher;
import javax.crypto.SecretKey;
import javax.crypto.SecretKeyFactory;
import javax.crypto.spec.DESKeySpec;
import javax.crypto.spec.IvParameterSpec;
import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.nio.ByteBuffer;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.security.Key;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.zip.ZipEntry;
import java.util.zip.ZipInputStream;
import java.util.zip.ZipOutputStream;

/** Offline two-layer DES recovery and optional verified string-site rewriting. */
public final class ZkmStringDecryptor {
    private static final String STRING_DESC = "(IJ)Ljava/lang/String;";
    private static final String BOOTSTRAP_DESC = "(Ljava/lang/invoke/MethodHandles$Lookup;"
            + "Ljava/lang/String;Ljava/lang/invoke/MethodType;)Ljava/lang/invoke/CallSite;";

    private ZkmStringDecryptor() {
    }

    public static void main(String[] args) throws Exception {
        if (args.length != 2 && args.length != 3) {
            System.err.println("usage: ZkmStringDecryptor <input.jar> <output-dir> [rewritten.jar]");
            System.exit(2);
        }
        recover(Paths.get(args[0]), Paths.get(args[1]),
                args.length == 3 ? Paths.get(args[2]) : null);
    }

    static RecoverySummary recover(Path input, Path outputDirectory) throws Exception {
        return recover(input, outputDirectory, null);
    }

    static RecoverySummary recover(Path input, Path outputDirectory, Path rewrittenOutput)
            throws Exception {
        Files.createDirectories(outputDirectory);
        if (rewrittenOutput != null) {
            Path inputPath = input.toAbsolutePath().normalize();
            Path outputPath = rewrittenOutput.toAbsolutePath().normalize();
            if (inputPath.equals(outputPath)) {
                throw new IllegalArgumentException("rewritten output must not replace input");
            }
            Path parent = outputPath.getParent();
            if (parent != null) Files.createDirectories(parent);
        }
        Map<String, ClassNode> classes = ZkmLongKeyEvaluator.readClasses(input);
        RecoverySummary summary = new RecoverySummary();
        summary.parsedClasses = classes.size();
        for (ClassNode owner : classes.values()) {
            summary.totalStandardIndySites += standardIndySites(owner).size();
        }
        summary.remainingStandardIndySites = summary.totalStandardIndySites;
        KeyOrderResult keyOrder = solveClassKeyOrder(classes);
        Map<String, Long> classKeys = keyOrder.keys;
        summary.sequencePasses = keyOrder.passes;
        summary.unresolvedClassKeys = keyOrder.unresolved;
        summary.prerequisiteClassKeys = keyOrder.prerequisites;
        summary.transactionalClassKeys = keyOrder.transactionalKeys;
        summary.hierarchyClassKeys = keyOrder.hierarchyKeys;
        summary.hierarchyPasses = keyOrder.hierarchyPasses;
        summary.keyConflicts = Math.max(0, keyOrder.ambiguities.size() - 1);
        List<String> rows = new ArrayList<>();
        List<String> tableRows = new ArrayList<>();
        List<String> rewriteRows = new ArrayList<>();
        Map<String, byte[]> rewrittenClasses = new LinkedHashMap<>();
        rows.add("class\tmethod\tinstruction\tcall_int\tcall_long\ttable_index\tplaintext\tstatus");
        tableRows.add("class\tclass_key_hex\touter_mask_hex\touter_key_hex\touter_candidates"
                + "\touter_literal_instructions\tinitial_chunks\tpacked_literals"
                + "\texpected_entries\tentries\tindy_sites"
                + "\tresolved_arguments\tdecrypted_sites\tplausible_sites\tstatus");
        rewriteRows.add("class\tmethod\tinstruction\tplaintext\taction\treason");
        summary.classKeys = classKeys.size();

        for (Map.Entry<String, Long> keyed : classKeys.entrySet()) {
            ClassNode owner = classes.get(keyed.getKey());
            if (owner == null) continue;
            MethodNode clinit = method(owner, "<clinit>", "()V");
            if (clinit == null) continue;
            KeyField keyField = keyField(owner, clinit, keyed.getValue());
            DecryptSpec spec = decryptSpec(owner);
            List<IndySite> indySites = standardIndySites(owner);
            summary.standardIndySites += indySites.size();
            if (indySites.isEmpty() || keyField == null) continue;
            summary.standardIndyClasses++;

            Long outerMask = outerMask(clinit, keyField);
            if (outerMask == null) {
                tableRows.add(tsv(owner.name, hex(keyed.getValue()), "", "", 0,
                        "", "", 0, "", "", indySites.size(),
                        0, 0, 0, "NO_OUTER_KEY_MASK"));
                summary.tableFailures++;
                continue;
            }
            long outerKey = keyed.getValue() ^ outerMask;
            TableLayout layout;
            List<TableCandidate> candidates;
            boolean genericInnerSearch = spec == null;
            if (spec != null) {
                layout = tableLayout(owner, clinit, spec.tableField);
                candidates = layout == null ? new ArrayList<>()
                        : outerCandidates(clinit, outerKey, layout);
            } else {
                InferredTable inferred = inferOuterTable(owner, clinit, outerKey);
                layout = inferred == null ? null : inferred.layout;
                candidates = inferred == null ? new ArrayList<>() : inferred.candidates;
            }
            if (layout == null) {
                tableRows.add(tsv(owner.name, hex(keyed.getValue()), hex(outerMask),
                        hex(outerKey), 0, "", "", 0, "", "", indySites.size(),
                        0, 0, 0, "NO_TABLE_LAYOUT"));
                summary.tableFailures++;
                continue;
            }
            CandidateScore best = null;
            for (TableCandidate candidate : candidates) {
                CandidateScore score = genericInnerSearch
                        ? scoreCandidateByIndexSearch(owner, keyField, indySites, candidate)
                        : scoreCandidate(owner, clinit, keyField, spec, indySites, candidate);
                if (best == null || score.compareTo(best) > 0) best = score;
            }
            if (best == null || best.decrypted == 0) {
                String candidateLocations = best == null ? "" : best.candidate.instructions();
                String candidateChunks = best == null ? "" : best.candidate.initialChunks();
                int candidateLiterals = best == null ? 0 : best.candidate.literalInstructions.size();
                String candidateEntries = best == null ? "" : String.valueOf(best.candidate.entries.size());
                int resolved = best == null ? 0 : best.resolved;
                int decrypted = best == null ? 0 : best.decrypted;
                int plausible = best == null ? 0 : best.plausible;
                tableRows.add(tsv(owner.name, hex(keyed.getValue()), hex(outerMask),
                        hex(outerKey), candidates.size(), candidateLocations, candidateChunks,
                        candidateLiterals, layout.expectedEntries, candidateEntries,
                        indySites.size(), resolved, decrypted, plausible, "NO_VALID_TABLE"));
                summary.tableFailures++;
                if (best != null) {
                    for (SiteResult result : best.results) {
                        rows.add(owner.name + "\t" + result.site.method.name + result.site.method.desc
                                + "\t" + result.site.instruction + "\t" + value(result.callInt)
                                + "\t" + value(result.callLong) + "\t" + value(result.tableIndex)
                                + "\t" + escape(result.plaintext) + "\t" + result.status);
                    }
                } else {
                    for (IndySite site : indySites) {
                        rows.add(owner.name + "\t" + site.method.name + site.method.desc + "\t"
                                + site.instruction + "\t\t\t\t\tNO_VALID_TABLE");
                    }
                }
                continue;
            }

            summary.tableClasses++;
            summary.resolvedArguments += best.resolved;
            summary.decryptedSites += best.decrypted;
            summary.plausibleSites += best.plausible;
            if (genericInnerSearch) {
                summary.genericInnerClasses++;
                summary.genericInnerSites += best.decrypted;
            }
            tableRows.add(tsv(owner.name, hex(keyed.getValue()), hex(outerMask), hex(outerKey),
                    candidates.size(), best.candidate.instructions(), best.candidate.initialChunks(),
                    best.candidate.literalInstructions.size(), layout.expectedEntries,
                    best.candidate.entries.size(), indySites.size(), best.resolved, best.decrypted,
                    best.plausible, genericInnerSearch
                            ? "OK_GENERIC_INDEX_XOR_" + best.genericIndexXor : "OK"));
            for (SiteResult result : best.results) {
                rows.add(owner.name + "\t" + result.site.method.name + result.site.method.desc + "\t"
                        + result.site.instruction + "\t" + value(result.callInt) + "\t"
                        + value(result.callLong) + "\t" + value(result.tableIndex) + "\t"
                        + escape(result.plaintext) + "\t" + result.status);
            }
            if (rewrittenOutput != null) {
                RewriteClassResult rewrite = rewriteClass(owner, best.results,
                        candidates.size() == 1);
                summary.rewritePlannedSites += rewrite.plannedSites;
                summary.rewriteAppliedSites += rewrite.appliedSites;
                summary.rewriteSkippedSites += rewrite.skippedSites;
                if (rewrite.rolledBack) summary.rewriteRollbackClasses++;
                if (rewrite.bytes != null) {
                    rewrittenClasses.put(owner.name, rewrite.bytes);
                    summary.rewriteClasses++;
                    summary.rewriteMethods += rewrite.changedMethods;
                }
                for (RewriteRecord record : rewrite.records) {
                    rewriteRows.add(tsv(owner.name, record.method, record.instruction,
                            escape(record.plaintext), record.action, record.reason));
                }
            }
        }

        rows.subList(1, rows.size()).sort(Comparator.naturalOrder());
        tableRows.subList(1, tableRows.size()).sort(Comparator.naturalOrder());
        rewriteRows.subList(1, rewriteRows.size()).sort(Comparator.naturalOrder());
        Files.write(outputDirectory.resolve("strings.tsv"), rows, StandardCharsets.UTF_8);
        Files.write(outputDirectory.resolve("tables.tsv"), tableRows, StandardCharsets.UTF_8);
        Files.write(outputDirectory.resolve("ambiguous-keys.tsv"), keyOrder.ambiguities,
                StandardCharsets.UTF_8);
        if (rewrittenOutput != null) {
            Files.write(outputDirectory.resolve("rewrite.tsv"), rewriteRows, StandardCharsets.UTF_8);
            ArchiveWriteResult archive = writeRewrittenArchive(input, rewrittenOutput,
                    rewrittenClasses);
            summary.archiveEntries = archive.entries;
            summary.archiveResources = archive.resources;
            summary.signaturesRemoved = archive.signaturesRemoved;
            ArchiveVerification verification = verifyArchive(rewrittenOutput);
            summary.outputClasses = verification.classes;
            summary.outputVerificationErrors = verification.errors;
            summary.remainingStandardIndySites = verification.standardIndySites;
        }
        List<String> audit = new ArrayList<>();
        audit.add("input=" + input.toAbsolutePath());
        audit.add("parsed_classes=" + summary.parsedClasses);
        audit.add("total_standard_indy_sites=" + summary.totalStandardIndySites);
        audit.add("class_keys=" + summary.classKeys);
        audit.add("transactional_class_keys=" + summary.transactionalClassKeys);
        audit.add("hierarchy_class_keys=" + summary.hierarchyClassKeys);
        audit.add("sequence_passes=" + summary.sequencePasses);
        audit.add("hierarchy_passes=" + summary.hierarchyPasses);
        audit.add("prerequisite_class_keys=" + summary.prerequisiteClassKeys);
        audit.add("key_conflicts=" + summary.keyConflicts);
        audit.add("unresolved_class_keys=" + summary.unresolvedClassKeys);
        audit.add("standard_indy_classes=" + summary.standardIndyClasses);
        audit.add("standard_indy_sites=" + summary.standardIndySites);
        audit.add("table_classes=" + summary.tableClasses);
        audit.add("table_failures=" + summary.tableFailures);
        audit.add("resolved_arguments=" + summary.resolvedArguments);
        audit.add("decrypted_sites=" + summary.decryptedSites);
        audit.add("plausible_sites=" + summary.plausibleSites);
        audit.add("generic_inner_classes=" + summary.genericInnerClasses);
        audit.add("generic_inner_sites=" + summary.genericInnerSites);
        audit.add("rewrite_requested=" + (rewrittenOutput != null));
        audit.add("rewrite_output=" + (rewrittenOutput == null ? "" : rewrittenOutput.toAbsolutePath()));
        audit.add("rewrite_classes=" + summary.rewriteClasses);
        audit.add("rewrite_methods=" + summary.rewriteMethods);
        audit.add("rewrite_planned_sites=" + summary.rewritePlannedSites);
        audit.add("rewrite_applied_sites=" + summary.rewriteAppliedSites);
        audit.add("rewrite_skipped_sites=" + summary.rewriteSkippedSites);
        audit.add("rewrite_rollback_classes=" + summary.rewriteRollbackClasses);
        audit.add("remaining_standard_indy_sites=" + summary.remainingStandardIndySites);
        audit.add("output_classes=" + summary.outputClasses);
        audit.add("output_verification_errors=" + summary.outputVerificationErrors);
        audit.add("archive_entries=" + summary.archiveEntries);
        audit.add("archive_resources=" + summary.archiveResources);
        audit.add("signatures_removed=" + summary.signaturesRemoved);
        audit.add("input_modified=false");
        audit.add("input_classes_loaded=false");
        Files.write(outputDirectory.resolve("audit.txt"), audit, StandardCharsets.UTF_8);
        String gate;
        if (rewrittenOutput == null) {
            gate = summary.decryptedSites > 0 ? "PASS\n" : "FAIL\n";
        } else {
            boolean integrity = summary.outputClasses == summary.parsedClasses
                    && summary.outputVerificationErrors == 0
                    && summary.rewriteRollbackClasses == 0;
            Files.write(outputDirectory.resolve("integrity_gate.txt"),
                    (integrity ? "PASS\n" : "FAIL\n").getBytes(StandardCharsets.UTF_8));
            Files.write(outputDirectory.resolve("coverage_gate.txt"),
                    (summary.remainingStandardIndySites == 0 ? "PASS\n" : "PARTIAL\n")
                            .getBytes(StandardCharsets.UTF_8));
            gate = !integrity ? "FAIL\n"
                    : summary.remainingStandardIndySites == 0 ? "PASS\n" : "PASS_PARTIAL\n";
        }
        Files.write(outputDirectory.resolve("gate.txt"), gate.getBytes(StandardCharsets.UTF_8));
        System.out.println("indy_sites=" + summary.standardIndySites + " decrypted="
                + summary.decryptedSites + " tables=" + summary.tableClasses + "/"
                + summary.standardIndyClasses + " report=" + outputDirectory);
        return summary;
    }

    private static RewriteClassResult rewriteClass(ClassNode owner, List<SiteResult> results,
                                                     boolean uniqueTable) {
        RewriteClassResult rewrite = new RewriteClassResult();
        Map<MethodNode, Boolean> changedMethods = new IdentityHashMap<>();
        for (SiteResult result : results) {
            String method = result.site.method.name + result.site.method.desc;
            if (!"OK".equals(result.status) || result.plaintext == null) {
                rewrite.skippedSites++;
                rewrite.records.add(new RewriteRecord(method, result.site.instruction,
                        result.plaintext, "skip", "recovery_status=" + result.status));
                continue;
            }
            rewrite.plannedSites++;
            if (!uniqueTable) {
                rewrite.skippedSites++;
                rewrite.records.add(new RewriteRecord(method, result.site.instruction,
                        result.plaintext, "skip", "table_candidate_not_unique"));
                continue;
            }
            InvokeDynamicInsnNode indy = result.site.node;
            if (result.site.method.instructions.indexOf(indy) < 0
                    || !isStandardStringIndy(owner, indy)) {
                rewrite.skippedSites++;
                rewrite.records.add(new RewriteRecord(method, result.site.instruction,
                        result.plaintext, "skip", "bootstrap_or_site_mismatch"));
                continue;
            }

            rewriteSiteToLdc(result.site.method, indy, result.plaintext);
            changedMethods.put(result.site.method, true);
            rewrite.records.add(new RewriteRecord(method, result.site.instruction,
                    result.plaintext, "rewrite", "unique_table+standard_bsm+preserved_arguments"));
        }
        if (changedMethods.isEmpty()) return rewrite;

        try {
            byte[] candidate = writeClass(owner);
            verifyClass(candidate);
            rewrite.bytes = candidate;
            rewrite.appliedSites = changedRecordCount(rewrite.records);
            rewrite.changedMethods = changedMethods.size();
        } catch (Throwable failure) {
            rewrite.rolledBack = true;
            String reason = "class_verification=" + shortReason(failure);
            for (RewriteRecord record : rewrite.records) {
                if ("rewrite".equals(record.action)) {
                    record.action = "rollback";
                    record.reason = reason;
                    rewrite.skippedSites++;
                }
            }
        }
        return rewrite;
    }

    static boolean rewriteSiteToLdc(MethodNode method, InvokeDynamicInsnNode indy,
                                    String plaintext) {
        if (method.instructions.indexOf(indy) < 0 || plaintext == null
                || !STRING_DESC.equals(indy.desc)) return false;
        // Preserve argument evaluation and consume the original (int,long) stack values.
        method.instructions.insertBefore(indy, new org.objectweb.asm.tree.InsnNode(Opcodes.POP2));
        method.instructions.insertBefore(indy, new org.objectweb.asm.tree.InsnNode(Opcodes.POP));
        method.instructions.set(indy, new LdcInsnNode(plaintext));
        return true;
    }

    private static int changedRecordCount(List<RewriteRecord> records) {
        int count = 0;
        for (RewriteRecord record : records) if ("rewrite".equals(record.action)) count++;
        return count;
    }

    private static byte[] writeClass(ClassNode owner) {
        // POP2/POP/LDC never exceeds the original three-slot (int,long) indy peak.
        ClassWriter writer = new ClassWriter(0);
        owner.accept(writer);
        return writer.toByteArray();
    }

    private static boolean structurallyValid(byte[] bytes) {
        try {
            verifyClass(bytes);
            return true;
        } catch (Throwable failure) {
            return false;
        }
    }

    private static void verifyClass(byte[] bytes) throws Exception {
        ClassReader reader = new ClassReader(bytes);
        reader.accept(new CheckClassAdapter(new ClassWriter(0), false), 0);
        ClassNode owner = new ClassNode(Opcodes.ASM9);
        reader.accept(owner, 0);
        for (MethodNode method : owner.methods) {
            if (method.instructions != null && method.instructions.size() > 0) {
                new Analyzer<>(new BasicVerifier()).analyze(owner.name, method);
            }
        }
    }

    private static ArchiveWriteResult writeRewrittenArchive(
            Path input, Path output, Map<String, byte[]> replacements) throws IOException {
        ArchiveWriteResult result = new ArchiveWriteResult();
        Map<String, Boolean> applied = new LinkedHashMap<>();
        try (ZipInputStream in = new ZipInputStream(Files.newInputStream(input));
             ZipOutputStream out = new ZipOutputStream(Files.newOutputStream(output))) {
            ZipEntry entry;
            while ((entry = in.getNextEntry()) != null) {
                byte[] bytes = readAll(in);
                if (isSignatureEntry(entry.getName()) && !replacements.isEmpty()) {
                    result.signaturesRemoved++;
                    continue;
                }
                String className = entry.getName().endsWith(".class")
                        ? entry.getName().substring(0, entry.getName().length() - 6) : null;
                byte[] replacement = className == null ? null : replacements.get(className);
                if (replacement != null) {
                    bytes = replacement;
                    applied.put(className, true);
                } else if (className == null) {
                    result.resources++;
                }
                ZipEntry written = new ZipEntry(entry.getName());
                if (entry.getTime() >= 0) written.setTime(entry.getTime());
                if (entry.getComment() != null) written.setComment(entry.getComment());
                if (entry.getExtra() != null) written.setExtra(entry.getExtra());
                if (entry.getMethod() == ZipEntry.STORED) {
                    java.util.zip.CRC32 crc = new java.util.zip.CRC32();
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
                result.entries++;
            }
        }
        if (applied.size() != replacements.size()) {
            throw new IOException("only applied " + applied.size() + "/" + replacements.size()
                    + " rewritten classes");
        }
        return result;
    }

    private static ArchiveVerification verifyArchive(Path archive) throws IOException {
        ArchiveVerification result = new ArchiveVerification();
        try (ZipInputStream in = new ZipInputStream(Files.newInputStream(archive))) {
            ZipEntry entry;
            while ((entry = in.getNextEntry()) != null) {
                byte[] bytes = readAll(in);
                if (!entry.getName().endsWith(".class")) continue;
                result.classes++;
                try {
                    ClassReader reader = new ClassReader(bytes);
                    ClassNode owner = new ClassNode(Opcodes.ASM9);
                    reader.accept(owner, 0);
                    if (!structurallyValid(bytes)) result.errors++;
                    result.standardIndySites += standardIndySites(owner).size();
                } catch (Throwable failure) {
                    result.errors++;
                }
            }
        }
        return result;
    }

    private static byte[] readAll(InputStream input) throws IOException {
        ByteArrayOutputStream output = new ByteArrayOutputStream();
        byte[] buffer = new byte[8192];
        int read;
        while ((read = input.read(buffer)) >= 0) output.write(buffer, 0, read);
        return output.toByteArray();
    }

    private static boolean isSignatureEntry(String name) {
        String upper = name.replace('\\', '/').toUpperCase(java.util.Locale.ROOT);
        if (!upper.startsWith("META-INF/")) return false;
        String leaf = upper.substring("META-INF/".length());
        return leaf.startsWith("SIG-") || leaf.endsWith(".SF") || leaf.endsWith(".RSA")
                || leaf.endsWith(".DSA") || leaf.endsWith(".EC");
    }

    private static String shortReason(Throwable failure) {
        String text = failure.getClass().getSimpleName() + ":" + String.valueOf(failure.getMessage());
        text = text.replace('\t', ' ').replace('\r', ' ').replace('\n', ' ');
        return text.substring(0, Math.min(160, text.length()));
    }

    static Map<String, Long> solveValidatedClassKeys(Map<String, ClassNode> classes) {
        return new LinkedHashMap<>(solveClassKeyOrder(classes).keys);
    }

    private static KeyOrderResult solveClassKeyOrder(Map<String, ClassNode> classes) {
        KeyOrderResult transactional = solveTransactionalClassKeyOrder(classes);
        KeyOrderResult hierarchy = solveHierarchyClassKeyOrder(classes);
        Map<String, Long> merged = new LinkedHashMap<>(transactional.keys);
        List<String> ambiguities = new ArrayList<>();
        ambiguities.add("class\ttransactional_key_hex\thierarchy_key_hex\tstatus");
        for (Map.Entry<String, Long> entry : hierarchy.keys.entrySet()) {
            Long existing = merged.get(entry.getKey());
            if (existing == null) {
                merged.put(entry.getKey(), entry.getValue());
            } else if (!existing.equals(entry.getValue())) {
                merged.remove(entry.getKey());
                ambiguities.add(tsv(entry.getKey(), hex(existing), hex(entry.getValue()),
                        "CONFLICT_REJECTED"));
            }
        }
        int totalSites = transactional.keys.size() + transactional.unresolved;
        KeyOrderResult result = new KeyOrderResult(merged,
                transactional.passes, totalSites - merged.size(), transactional.prerequisites);
        result.transactionalKeys = transactional.keys.size();
        result.hierarchyKeys = hierarchy.keys.size();
        result.hierarchyPasses = hierarchy.passes;
        result.ambiguities.addAll(ambiguities);
        return result;
    }

    private static KeyOrderResult solveTransactionalClassKeyOrder(Map<String, ClassNode> classes) {
        ZkmLongKeyEvaluator.StatefulKeySequence sequence =
                ZkmLongKeyEvaluator.newStatefulKeySequence(classes);
        List<String> remaining = sequence.owners();
        Map<String, Long> result = new LinkedHashMap<>();
        int passes = 0;
        int prerequisiteCommits = 0;
        boolean progress;
        do {
            progress = false;
            passes++;
            for (int position = 0; position < remaining.size(); ) {
                String name = remaining.get(position);
                ClassNode owner = classes.get(name);
                MethodNode clinit = owner == null ? null : method(owner, "<clinit>", "()V");
                KeyField shape = clinit == null ? null : keyField(owner, clinit, 0L);
                Long mask = shape == null ? null : outerMask(clinit, shape);
                if (mask == null) {
                    position++;
                    continue;
                }
                DecryptSpec spec = decryptSpec(owner);
                if (spec == null) {
                    position++;
                    continue;
                }
                TableLayout layout = tableLayout(owner, clinit, spec.tableField);
                if (layout == null) {
                    position++;
                    continue;
                }
                List<String> prerequisites = superclassPrerequisites(name, classes, sequence, result);
                ZkmLongKeyEvaluator.StatefulKeySequence trial = prerequisites.isEmpty()
                        ? sequence : sequence.copy();
                Map<String, Long> prerequisiteKeys = new LinkedHashMap<>();
                for (String prerequisite : prerequisites) {
                    prerequisiteKeys.put(prerequisite, trial.commit(prerequisite));
                }
                long key = trial.peek(name);
                if (!acceptsClassKey(owner, key, clinit, shape, mask, spec, layout, false)) {
                    position++;
                    continue;
                }

                long committed = trial.commit(name);
                if (committed != key) {
                    throw new IllegalStateException("peek/commit key mismatch for " + name);
                }
                sequence = trial;
                for (Map.Entry<String, Long> prerequisite : prerequisiteKeys.entrySet()) {
                    result.put(prerequisite.getKey(), prerequisite.getValue());
                    remaining.remove(prerequisite.getKey());
                    prerequisiteCommits++;
                }
                result.put(name, key);
                remaining.remove(name);
                progress = true;
                position = 0;
            }
        } while (progress && !remaining.isEmpty() && passes <= 64);
        return new KeyOrderResult(result, passes, remaining.size(), prerequisiteCommits);
    }

    private static KeyOrderResult solveHierarchyClassKeyOrder(Map<String, ClassNode> classes) {
        ZkmLongKeyEvaluator.StatefulKeySequence sequence =
                ZkmLongKeyEvaluator.newStatefulKeySequence(classes);
        List<String> order = hierarchyOrder(classes, sequence);
        Map<String, Long> result = new LinkedHashMap<>();
        int passes = 0;
        boolean progress;
        do {
            progress = false;
            passes++;
            for (String name : order) {
                if (result.containsKey(name)) continue;
                if (!superclassPrerequisites(name, classes, sequence, result).isEmpty()) continue;
                ClassNode owner = classes.get(name);
                MethodNode clinit = owner == null ? null : method(owner, "<clinit>", "()V");
                KeyField shape = clinit == null ? null : keyField(owner, clinit, 0L);
                Long mask = shape == null ? null : outerMask(clinit, shape);
                DecryptSpec spec = owner == null ? null : decryptSpec(owner);
                TableLayout layout = spec == null || clinit == null ? null
                        : tableLayout(owner, clinit, spec.tableField);
                if (shape == null || mask == null) continue;
                long key = sequence.peek(name);
                boolean accepted = spec != null && layout != null
                        ? acceptsClassKey(owner, key, clinit, shape, mask, spec, layout, true)
                        : hasStrongOuterCandidate(genericOuterCandidates(clinit, key ^ mask), true);
                if (!accepted) continue;
                long committed = sequence.commit(name);
                if (committed != key) {
                    throw new IllegalStateException("hierarchy peek/commit mismatch for " + name);
                }
                result.put(name, key);
                progress = true;
            }
        } while (progress && result.size() < order.size() && passes <= 64);
        return new KeyOrderResult(result, passes, order.size() - result.size(), 0);
    }

    private static boolean acceptsClassKey(ClassNode owner, long key, MethodNode clinit,
                                           KeyField shape, long mask, DecryptSpec spec,
                                           TableLayout layout, boolean allowSingleDirect) {
        KeyField keyField = new KeyField(shape.owner, shape.name, key);
        List<TableCandidate> candidates = outerCandidates(clinit, key ^ mask, layout);
        if (candidates.isEmpty()) return false;
        List<IndySite> sites = standardIndySites(owner);
        if (!sites.isEmpty()) {
            CandidateScore best = null;
            for (TableCandidate candidate : candidates) {
                CandidateScore score = scoreCandidate(owner, clinit, keyField, spec, sites, candidate);
                if (best == null || score.compareTo(best) > 0) best = score;
            }
            return best != null && best.decrypted > 0;
        }
        return hasStrongOuterCandidate(candidates, allowSingleDirect);
    }

    static List<TableCandidate> genericOuterCandidates(MethodNode clinit, long key) {
        List<TableCandidate> result = new ArrayList<>();
        int instruction = 0;
        for (AbstractInsnNode insn = clinit.instructions.getFirst(); insn != null;
             insn = insn.getNext(), instruction++) {
            if (!(insn instanceof LdcInsnNode) || !(((LdcInsnNode) insn).cst instanceof String)) continue;
            String packed = (String) ((LdcInsnNode) insn).cst;
            if (packed.length() < 8 || isKnownLiteral(packed)) continue;
            Integer initial = initialChunk(insn);
            if (initial == null && (packed.length() & 7) == 0) initial = packed.length();
            if (initial == null || initial <= 0 || (initial & 7) != 0) continue;
            List<String> entries = unpack(packed, initial, key);
            if (entries != null && !entries.isEmpty()) {
                result.add(new TableCandidate().append(
                        new TableFragment(instruction, initial, entries)));
            }
        }
        return result;
    }

    private static List<String> hierarchyOrder(
            Map<String, ClassNode> classes, ZkmLongKeyEvaluator.StatefulKeySequence sequence) {
        List<String> result = new ArrayList<>();
        Set<String> sites = new HashSet<>(sequence.owners());
        Set<String> visited = new HashSet<>();
        Set<String> active = new HashSet<>();
        for (String owner : sequence.owners()) {
            visitHierarchy(owner, classes, sites, visited, active, result);
        }
        return result;
    }

    private static void visitHierarchy(String name, Map<String, ClassNode> classes,
                                       Set<String> sites, Set<String> visited,
                                       Set<String> active, List<String> result) {
        if (visited.contains(name)) return;
        if (!active.add(name)) throw new IllegalStateException("initialization cycle at " + name);
        ClassNode owner = classes.get(name);
        if (owner != null && (owner.access & Opcodes.ACC_INTERFACE) == 0
                && owner.superName != null && classes.containsKey(owner.superName)) {
            visitHierarchy(owner.superName, classes, sites, visited, active, result);
        }
        active.remove(name);
        visited.add(name);
        if (sites.contains(name)) result.add(name);
    }

    private static List<String> superclassPrerequisites(
            String owner, Map<String, ClassNode> classes,
            ZkmLongKeyEvaluator.StatefulKeySequence sequence, Map<String, Long> committed) {
        List<String> result = new ArrayList<>();
        ClassNode current = classes.get(owner);
        String parent = current == null ? null : current.superName;
        while (parent != null) {
            if (sequence.hasSite(parent) && !committed.containsKey(parent)) result.add(0, parent);
            ClassNode parentClass = classes.get(parent);
            parent = parentClass == null ? null : parentClass.superName;
        }
        return result;
    }

    private static boolean hasStrongOuterCandidate(List<TableCandidate> candidates,
                                                   boolean allowSingleDirect) {
        int strongestEntries = 0;
        int strongestCount = 0;
        for (TableCandidate candidate : candidates) {
            int entries = candidate.entries.size();
            if (entries > strongestEntries) {
                strongestEntries = entries;
                strongestCount = 1;
            } else if (entries == strongestEntries) {
                strongestCount++;
            }
        }
        if (strongestCount != 1) return false;
        if (strongestEntries >= 2) return true;
        return allowSingleDirect && strongestEntries == 1
                && isPlausibleDirect(candidates.get(0).entries.get(0));
    }

    private static boolean isPlausibleDirect(String value) {
        if (value == null || value.isEmpty()) return false;
        int printable = 0;
        for (int i = 0; i < value.length(); i++) {
            char c = value.charAt(i);
            if (c >= 0x20 && c <= 0x7e || c == '\n' || c == '\r' || c == '\t') printable++;
        }
        return printable * 5 >= value.length() * 4;
    }

    private static CandidateScore scoreCandidate(ClassNode owner, MethodNode clinit, KeyField keyField,
                                                   DecryptSpec spec, List<IndySite> sites,
                                                   TableCandidate candidate) {
        CandidateScore score = new CandidateScore(candidate);
        Map<MethodNode, Frame<SourceValue>[]> sourceFrames = new IdentityHashMap<>();
        Map<MethodNode, Boolean> sourceFailures = new IdentityHashMap<>();
        for (IndySite site : sites) {
            ArgumentExpressions arguments = resolveArguments(owner.name, site, keyField,
                    sourceFrames, sourceFailures);
            if (arguments == null) {
                score.results.add(SiteResult.failure(site, "UNRESOLVED_ARGUMENTS"));
                continue;
            }
            LongExpression longArgument = arguments.longArgument;
            IntExpression intArgument = arguments.intArgument;
            score.resolved++;
            int index = intArgument.value ^ (int) (longArgument.value & spec.indexMask) ^ spec.indexXor;
            if (index < 0 || index >= candidate.entries.size()) {
                score.results.add(SiteResult.indexFailure(site, intArgument.value,
                        longArgument.value, index));
                continue;
            }
            try {
                String plaintext = decodeZkmUtf8(decrypt(
                        latin1(candidate.entries.get(index)), longArgument.value));
                boolean plausible = isPlausible(plaintext);
                score.decrypted++;
                if (plausible) score.plausible++;
                score.results.add(SiteResult.success(site, intArgument.value, longArgument.value,
                        index, plaintext, plausible));
            } catch (Exception failure) {
                score.results.add(SiteResult.decryptFailure(site, intArgument.value,
                        longArgument.value, index));
            }
        }
        return score;
    }

    private static CandidateScore scoreCandidateByIndexSearch(
            ClassNode owner, KeyField keyField, List<IndySite> sites, TableCandidate candidate) {
        CandidateScore score = new CandidateScore(candidate);
        Map<MethodNode, Frame<SourceValue>[]> sourceFrames = new IdentityHashMap<>();
        Map<MethodNode, Boolean> sourceFailures = new IdentityHashMap<>();
        List<GenericSiteMatches> recovered = new ArrayList<>();
        Map<IndySite, String> failures = new IdentityHashMap<>();
        Map<Integer, Integer> xorCoverage = new LinkedHashMap<>();
        for (IndySite site : sites) {
            ArgumentExpressions arguments = resolveArguments(owner.name, site, keyField,
                    sourceFrames, sourceFailures);
            if (arguments == null) {
                failures.put(site, "UNRESOLVED_ARGUMENTS");
                continue;
            }
            score.resolved++;
            GenericSiteMatches siteMatches = new GenericSiteMatches(site, arguments);
            for (int index = 0; index < candidate.entries.size(); index++) {
                try {
                    String plaintext = decodeZkmUtf8(decrypt(
                            latin1(candidate.entries.get(index)), arguments.longArgument.value));
                    if (!isStrongPlaintext(plaintext)) continue;
                    int indexXor = arguments.intArgument.value
                            ^ (int) (arguments.longArgument.value & 0x7fffL) ^ index;
                    siteMatches.matches.add(new GenericMatch(index, indexXor, plaintext));
                    xorCoverage.put(indexXor, xorCoverage.containsKey(indexXor)
                            ? xorCoverage.get(indexXor) + 1 : 1);
                } catch (Exception ignored) {
                    // Wrong table entries normally fail PKCS#5 padding.
                }
            }
            if (siteMatches.matches.isEmpty()) failures.put(site, "GENERIC_NO_INNER_MATCH");
            recovered.add(siteMatches);
        }

        Integer selectedXor = null;
        int selectedCoverage = 0;
        boolean tied = false;
        for (Map.Entry<Integer, Integer> entry : xorCoverage.entrySet()) {
            if (entry.getValue() > selectedCoverage) {
                selectedXor = entry.getKey();
                selectedCoverage = entry.getValue();
                tied = false;
            } else if (entry.getValue() == selectedCoverage) {
                tied = true;
            }
        }
        if (selectedXor == null || tied || selectedCoverage != sites.size()) {
            for (IndySite site : sites) {
                score.results.add(SiteResult.failure(site,
                        failures.containsKey(site) ? failures.get(site) : "GENERIC_INDEX_XOR_UNPROVEN"));
            }
            return score;
        }

        score.genericIndexXor = selectedXor;
        for (GenericSiteMatches siteMatches : recovered) {
            GenericMatch selected = null;
            for (GenericMatch match : siteMatches.matches) {
                if (match.indexXor != selectedXor) continue;
                if (selected != null) {
                    selected = null;
                    break;
                }
                selected = match;
            }
            if (selected == null) {
                score.results.add(SiteResult.failure(siteMatches.site,
                        "GENERIC_INDEX_XOR_AMBIGUOUS"));
                continue;
            }
            score.decrypted++;
            score.plausible++;
            score.results.add(SiteResult.success(siteMatches.site,
                    siteMatches.arguments.intArgument.value,
                    siteMatches.arguments.longArgument.value, selected.index,
                    selected.plaintext, true));
        }
        return score;
    }

    private static ArgumentExpressions resolveArguments(
            String owner, IndySite site, KeyField keyField,
            Map<MethodNode, Frame<SourceValue>[]> sourceFrames,
            Map<MethodNode, Boolean> sourceFailures) {
        ArgumentExpressions arguments = sourceArguments(owner, site, keyField,
                sourceFrames, sourceFailures);
        if (arguments != null) return arguments;
        LongExpression longArgument = evalLong(previousCode(site.node), site.method, keyField);
        IntExpression intArgument = longArgument == null ? null
                : evalInt(previousCode(longArgument.start), site.method, keyField);
        return longArgument == null || intArgument == null ? null
                : new ArgumentExpressions(intArgument, longArgument);
    }

    private static ArgumentExpressions sourceArguments(
            String owner, IndySite site, KeyField keyField,
            Map<MethodNode, Frame<SourceValue>[]> sourceFrames,
            Map<MethodNode, Boolean> sourceFailures) {
        if (Boolean.TRUE.equals(sourceFailures.get(site.method))) return null;
        Frame<SourceValue>[] frames = sourceFrames.get(site.method);
        if (frames == null) {
            try {
                frames = new Analyzer<>(new SourceInterpreter()).analyze(owner, site.method);
                sourceFrames.put(site.method, frames);
            } catch (Exception failure) {
                sourceFailures.put(site.method, true);
                return null;
            }
        }
        int index = site.method.instructions.indexOf(site.node);
        if (index < 0 || index >= frames.length) return null;
        Frame<SourceValue> frame = frames[index];
        AbstractInsnNode[] producers = uniqueArgumentProducers(frame);
        if (producers == null) return null;
        AbstractInsnNode intProducer = producers[0];
        AbstractInsnNode longProducer = producers[1];
        IntExpression intArgument = evalInt(intProducer, site.method, keyField);
        LongExpression longArgument = evalLong(longProducer, site.method, keyField);
        return intArgument == null || longArgument == null ? null
                : new ArgumentExpressions(intArgument, longArgument);
    }

    static AbstractInsnNode[] uniqueArgumentProducers(String owner, MethodNode method,
                                                       InvokeDynamicInsnNode indy) throws Exception {
        Frame<SourceValue>[] frames = new Analyzer<>(new SourceInterpreter()).analyze(owner, method);
        int index = method.instructions.indexOf(indy);
        return index < 0 || index >= frames.length ? null : uniqueArgumentProducers(frames[index]);
    }

    private static AbstractInsnNode[] uniqueArgumentProducers(Frame<SourceValue> frame) {
        if (frame == null || frame.getStackSize() < 2) return null;
        SourceValue intSource = frame.getStack(frame.getStackSize() - 2);
        SourceValue longSource = frame.getStack(frame.getStackSize() - 1);
        if (intSource == null || longSource == null || intSource.getSize() != 1
                || longSource.getSize() != 2 || intSource.insns.size() != 1
                || longSource.insns.size() != 1) return null;
        return new AbstractInsnNode[] {intSource.insns.iterator().next(),
                longSource.insns.iterator().next()};
    }

    static List<TableCandidate> outerCandidates(MethodNode clinit, long key, TableLayout layout) {
        List<List<TableFragment>> fragments = new ArrayList<>();
        int instruction = 0;
        boolean inTableInitializer = false;
        for (AbstractInsnNode insn = clinit.instructions.getFirst(); insn != null;
             insn = insn.getNext(), instruction++) {
            if (insn == layout.allocationStore) {
                inTableInitializer = true;
                continue;
            }
            if (insn == layout.tableStore) break;
            if (!inTableInitializer) continue;
            if (!(insn instanceof LdcInsnNode) || !(((LdcInsnNode) insn).cst instanceof String)) continue;
            String packed = (String) ((LdcInsnNode) insn).cst;
            if (packed.length() < 8 || isKnownLiteral(packed)) continue;
            Integer initial = initialChunk(insn);
            if (initial == null || initial <= 0 || (initial & 7) != 0) continue;
            List<TableFragment> alternatives = new ArrayList<>();
            List<String> entries = unpack(packed, initial, key);
            if (entries != null && !entries.isEmpty()
                    && entries.size() <= layout.expectedEntries) {
                alternatives.add(new TableFragment(instruction, initial, entries));
            }
            if (!alternatives.isEmpty()) fragments.add(alternatives);
        }
        if (fragments.isEmpty()) return new ArrayList<>();

        List<TableCandidate> partials = new ArrayList<>();
        partials.add(new TableCandidate());
        for (List<TableFragment> alternatives : fragments) {
            List<TableCandidate> next = new ArrayList<>();
            for (TableCandidate partial : partials) {
                for (TableFragment fragment : alternatives) {
                    if (partial.entries.size() + fragment.entries.size() > layout.expectedEntries) continue;
                    next.add(partial.append(fragment));
                }
            }
            if (next.isEmpty()) return next;
            partials = next;
        }
        List<TableCandidate> result = new ArrayList<>();
        for (TableCandidate candidate : partials) {
            if (candidate.entries.size() == layout.expectedEntries) result.add(candidate);
        }
        return result;
    }

    private static InferredTable inferOuterTable(ClassNode owner, MethodNode clinit, long key) {
        InferredTable accepted = null;
        for (FieldNode field : owner.fields) {
            if (!"[Ljava/lang/String;".equals(field.desc)) continue;
            TableLayout layout = tableLayout(owner, clinit, field.name);
            if (layout == null) continue;
            List<TableCandidate> candidates = outerCandidates(clinit, key, layout);
            if (candidates.isEmpty()) continue;
            if (accepted != null) return null;
            accepted = new InferredTable(layout, candidates);
        }
        return accepted;
    }

    private static Integer initialChunk(AbstractInsnNode packedLiteral) {
        AbstractInsnNode cursor = nextCode(packedLiteral);
        for (int scanned = 0; cursor != null && scanned < 12; scanned++, cursor = nextCode(cursor)) {
            if (cursor instanceof VarInsnNode && cursor.getOpcode() == Opcodes.ISTORE) {
                Integer constant = intConstant(previousCode(cursor));
                if (constant != null) return constant;
            }
            if (cursor instanceof LdcInsnNode || cursor instanceof FieldInsnNode) break;
        }
        return null;
    }

    static TableLayout tableLayout(ClassNode owner, MethodNode clinit, String tableField) {
        TableLayout result = null;
        for (AbstractInsnNode insn = clinit.instructions.getFirst(); insn != null; insn = insn.getNext()) {
            if (!(insn instanceof FieldInsnNode)) continue;
            FieldInsnNode field = (FieldInsnNode) insn;
            if (field.getOpcode() != Opcodes.PUTSTATIC || !owner.name.equals(field.owner)
                    || !tableField.equals(field.name) || !"[Ljava/lang/String;".equals(field.desc)) continue;

            TableLayout candidate = null;
            AbstractInsnNode value = previousCode(field);
            if (value instanceof TypeInsnNode && value.getOpcode() == Opcodes.ANEWARRAY
                    && "java/lang/String".equals(((TypeInsnNode) value).desc)) {
                Integer size = intConstant(previousCode(value));
                if (size != null && size > 0) candidate = new TableLayout(value, field, size);
            }
            if (candidate == null && value instanceof VarInsnNode && value.getOpcode() == Opcodes.ALOAD) {
                int local = ((VarInsnNode) value).var;
                VarInsnNode definition = null;
                int definitions = 0;
                for (AbstractInsnNode cursor = clinit.instructions.getFirst(); cursor != null;
                     cursor = cursor.getNext()) {
                    if (cursor instanceof VarInsnNode && cursor.getOpcode() == Opcodes.ASTORE
                            && ((VarInsnNode) cursor).var == local) {
                        definitions++;
                        definition = (VarInsnNode) cursor;
                    }
                }
                if (definitions == 1 && definition != null) {
                    AbstractInsnNode array = previousCode(definition);
                    if (array instanceof TypeInsnNode && array.getOpcode() == Opcodes.ANEWARRAY
                            && "java/lang/String".equals(((TypeInsnNode) array).desc)) {
                        Integer size = intConstant(previousCode(array));
                        if (size != null && size > 0) candidate = new TableLayout(definition, field, size);
                    }
                }
            }
            if (candidate == null || result != null) return null;
            result = candidate;
        }
        return result;
    }

    private static List<String> unpack(String packed, int initialLength, long key) {
        List<String> result = new ArrayList<>();
        int position = 0;
        int length = initialLength;
        try {
            while (position < packed.length()) {
                if (length <= 0 || (length & 7) != 0 || position + length > packed.length()) return null;
                String chunk = packed.substring(position, position + length);
                if (!isLatin1(chunk)) return null;
                byte[] encrypted = latin1(chunk);
                result.add(decodeZkmUtf8(decrypt(encrypted, key)));
                position += length;
                if (position == packed.length()) return result;
                length = packed.charAt(position++);
            }
        } catch (Exception failure) {
            return null;
        }
        return position == packed.length() ? result : null;
    }

    private static DecryptSpec decryptSpec(ClassNode owner) {
        for (MethodNode method : owner.methods) {
            if ((method.access & Opcodes.ACC_STATIC) == 0 || !STRING_DESC.equals(method.desc)) continue;
            Long mask = null;
            Integer xor = null;
            String tableField = null;
            boolean cipher = false;
            for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null; insn = insn.getNext()) {
                if (insn.getOpcode() == Opcodes.LAND) {
                    Long value = longConstant(previousCode(insn));
                    if (value != null) mask = value;
                } else if (insn.getOpcode() == Opcodes.IXOR) {
                    Integer value = intConstant(previousCode(insn));
                    if (value != null) xor = value;
                } else if (insn instanceof MethodInsnNode) {
                    MethodInsnNode call = (MethodInsnNode) insn;
                    if ("javax/crypto/Cipher".equals(call.owner) && "doFinal".equals(call.name)) {
                        cipher = true;
                    }
                    if ("java/lang/String".equals(call.owner) && "getBytes".equals(call.name)) {
                        AbstractInsnNode cursor = previousCode(call);
                        for (int i = 0; cursor != null && i < 8; i++, cursor = previousCode(cursor)) {
                            if (cursor instanceof FieldInsnNode) {
                                FieldInsnNode field = (FieldInsnNode) cursor;
                                if (field.getOpcode() == Opcodes.GETSTATIC && owner.name.equals(field.owner)
                                        && "[Ljava/lang/String;".equals(field.desc)) {
                                    tableField = field.name;
                                    break;
                                }
                            }
                        }
                    }
                }
            }
            if (cipher && mask != null && xor != null && tableField != null) {
                return new DecryptSpec(method, mask, xor, tableField);
            }
        }
        return null;
    }

    private static List<IndySite> standardIndySites(ClassNode owner) {
        List<IndySite> result = new ArrayList<>();
        for (MethodNode method : owner.methods) {
            int instruction = 0;
            for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
                 insn = insn.getNext(), instruction++) {
                if (insn instanceof InvokeDynamicInsnNode) {
                    InvokeDynamicInsnNode indy = (InvokeDynamicInsnNode) insn;
                    if (isStandardStringIndy(owner, indy)) {
                        result.add(new IndySite(method, indy, instruction));
                    }
                }
            }
        }
        return result;
    }

    private static boolean isStandardStringIndy(ClassNode owner, InvokeDynamicInsnNode indy) {
        return STRING_DESC.equals(indy.desc) && indy.bsm != null
                && indy.bsm.getTag() == Opcodes.H_INVOKESTATIC
                && owner.name.equals(indy.bsm.getOwner())
                && BOOTSTRAP_DESC.equals(indy.bsm.getDesc());
    }

    private static KeyField keyField(ClassNode owner, MethodNode clinit, long key) {
        for (AbstractInsnNode insn = clinit.instructions.getFirst(); insn != null; insn = insn.getNext()) {
            if (!(insn instanceof FieldInsnNode)) continue;
            FieldInsnNode field = (FieldInsnNode) insn;
            if (field.getOpcode() != Opcodes.PUTSTATIC || !owner.name.equals(field.owner)
                    || !"J".equals(field.desc)) continue;
            AbstractInsnNode previous = previousCode(field);
            if (previous instanceof MethodInsnNode) {
                MethodInsnNode call = (MethodInsnNode) previous;
                if (call.getOpcode() == Opcodes.INVOKEINTERFACE && "(J)J".equals(call.desc)) {
                    return new KeyField(owner.name, field.name, key);
                }
            }
        }
        return null;
    }

    private static Long outerMask(MethodNode clinit, KeyField keyField) {
        for (AbstractInsnNode insn = clinit.instructions.getFirst(); insn != null; insn = insn.getNext()) {
            if (insn.getOpcode() != Opcodes.LXOR) continue;
            AbstractInsnNode right = previousCode(insn);
            AbstractInsnNode left = previousCode(right);
            Long constant = longConstant(right);
            if (constant != null && isKeyField(left, keyField)) return constant;
            constant = longConstant(left);
            if (constant != null && isKeyField(right, keyField)) return constant;
        }
        return null;
    }

    private static boolean isKeyField(AbstractInsnNode insn, KeyField keyField) {
        if (!(insn instanceof FieldInsnNode)) return false;
        FieldInsnNode field = (FieldInsnNode) insn;
        return field.getOpcode() == Opcodes.GETSTATIC && keyField.owner.equals(field.owner)
                && keyField.name.equals(field.name) && "J".equals(field.desc);
    }

    private static LongExpression evalLong(AbstractInsnNode end, MethodNode method, KeyField keyField) {
        if (end == null) return null;
        Long constant = longConstant(end);
        if (constant != null) return new LongExpression(constant, end);
        if (isKeyField(end, keyField)) return new LongExpression(keyField.value, end);
        if (end instanceof VarInsnNode && end.getOpcode() == Opcodes.LLOAD) {
            AbstractInsnNode store = findStore(end, method, ((VarInsnNode) end).var, Opcodes.LSTORE);
            LongExpression stored = store == null ? null
                    : evalLong(previousCode(store), method, keyField);
            return stored == null ? null : new LongExpression(stored.value, end);
        }
        int opcode = end.getOpcode();
        if (opcode == Opcodes.LXOR || opcode == Opcodes.LAND || opcode == Opcodes.LOR
                || opcode == Opcodes.LADD || opcode == Opcodes.LSUB) {
            LongExpression right = evalLong(previousCode(end), method, keyField);
            LongExpression left = right == null ? null
                    : evalLong(previousCode(right.start), method, keyField);
            if (left == null || right == null) return null;
            long value;
            if (opcode == Opcodes.LXOR) value = left.value ^ right.value;
            else if (opcode == Opcodes.LAND) value = left.value & right.value;
            else if (opcode == Opcodes.LOR) value = left.value | right.value;
            else if (opcode == Opcodes.LADD) value = left.value + right.value;
            else value = left.value - right.value;
            return new LongExpression(value, left.start);
        }
        if (opcode == Opcodes.LNEG) {
            LongExpression value = evalLong(previousCode(end), method, keyField);
            return value == null ? null : new LongExpression(-value.value, value.start);
        }
        return null;
    }

    private static IntExpression evalInt(AbstractInsnNode end, MethodNode method, KeyField keyField) {
        if (end == null) return null;
        Integer constant = intConstant(end);
        if (constant != null) return new IntExpression(constant, end);
        if (end instanceof VarInsnNode && end.getOpcode() == Opcodes.ILOAD) {
            AbstractInsnNode store = findStore(end, method, ((VarInsnNode) end).var, Opcodes.ISTORE);
            IntExpression stored = store == null ? null
                    : evalInt(previousCode(store), method, keyField);
            return stored == null ? null : new IntExpression(stored.value, end);
        }
        int opcode = end.getOpcode();
        if (opcode == Opcodes.IXOR || opcode == Opcodes.IAND || opcode == Opcodes.IOR
                || opcode == Opcodes.IADD || opcode == Opcodes.ISUB) {
            IntExpression right = evalInt(previousCode(end), method, keyField);
            IntExpression left = right == null ? null
                    : evalInt(previousCode(right.start), method, keyField);
            if (left == null || right == null) return null;
            int value;
            if (opcode == Opcodes.IXOR) value = left.value ^ right.value;
            else if (opcode == Opcodes.IAND) value = left.value & right.value;
            else if (opcode == Opcodes.IOR) value = left.value | right.value;
            else if (opcode == Opcodes.IADD) value = left.value + right.value;
            else value = left.value - right.value;
            return new IntExpression(value, left.start);
        }
        if (opcode == Opcodes.L2I) {
            LongExpression value = evalLong(previousCode(end), method, keyField);
            return value == null ? null : new IntExpression((int) value.value, value.start);
        }
        return null;
    }

    private static AbstractInsnNode findStore(AbstractInsnNode load, MethodNode method, int local, int opcode) {
        for (AbstractInsnNode cursor = load.getPrevious(); cursor != null; cursor = cursor.getPrevious()) {
            if (cursor instanceof VarInsnNode && cursor.getOpcode() == opcode
                    && ((VarInsnNode) cursor).var == local) return cursor;
        }
        return null;
    }

    private static byte[] decrypt(byte[] encrypted, long keyValue) throws Exception {
        byte[] keyBytes = ByteBuffer.allocate(8).putLong(keyValue).array();
        Cipher cipher = Cipher.getInstance("DES/CBC/PKCS5Padding");
        SecretKeyFactory factory = SecretKeyFactory.getInstance("DES");
        SecretKey key = factory.generateSecret(new DESKeySpec(keyBytes));
        cipher.init(Cipher.DECRYPT_MODE, (Key) key, new IvParameterSpec(new byte[8]));
        return cipher.doFinal(encrypted);
    }

    private static byte[] latin1(String value) {
        byte[] result = new byte[value.length()];
        for (int i = 0; i < value.length(); i++) result[i] = (byte) value.charAt(i);
        return result;
    }

    private static String decodeZkmUtf8(byte[] bytes) {
        int output = 0;
        char[] chars = new char[bytes.length];
        for (int index = 0; index < bytes.length; index++) {
            int value = bytes[index] & 0xff;
            if (value < 192) {
                chars[output++] = (char) value;
            } else if (value < 224 && index + 1 < bytes.length) {
                char decoded = (char) ((value & 0x1f) << 6);
                decoded |= (char) (bytes[++index] & 0x3f);
                chars[output++] = decoded;
            } else if (index < bytes.length - 2) {
                char decoded = (char) ((value & 0xf) << 12);
                decoded |= (char) ((bytes[++index] & 0x3f) << 6);
                decoded |= (char) (bytes[++index] & 0x3f);
                chars[output++] = decoded;
            }
        }
        return new String(chars, 0, output);
    }

    private static boolean isPlausible(String value) {
        if (value.isEmpty()) return true;
        int acceptable = 0;
        for (int i = 0; i < value.length(); i++) {
            char c = value.charAt(i);
            if (c == '\t' || c == '\n' || c == '\r' || c >= 0x20 && c != 0x7f) acceptable++;
        }
        return acceptable * 5 >= value.length() * 4;
    }

    private static boolean isStrongPlaintext(String value) {
        if (value == null) return false;
        if (value.isEmpty()) return true;
        int acceptable = 0;
        for (int i = 0; i < value.length(); i++) {
            char c = value.charAt(i);
            if (c == '\t' || c == '\n' || c == '\r'
                    || c >= 0x20 && (c < 0x7f || c > 0x9f)) acceptable++;
        }
        return acceptable * 10 >= value.length() * 9;
    }

    private static boolean isLatin1(String value) {
        for (int i = 0; i < value.length(); i++) if (value.charAt(i) > 0xff) return false;
        return true;
    }

    private static boolean isKnownLiteral(String value) {
        return "DES/CBC/PKCS5Padding".equals(value) || "DES/CBC/NoPadding".equals(value)
                || "DES".equals(value) || "ISO-8859-1".equals(value);
    }

    private static String escape(String value) {
        if (value == null) return "";
        StringBuilder result = new StringBuilder();
        for (int i = 0; i < value.length(); i++) {
            char c = value.charAt(i);
            if (c == '\\') result.append("\\\\");
            else if (c == '\t') result.append("\\t");
            else if (c == '\n') result.append("\\n");
            else if (c == '\r') result.append("\\r");
            else if (c < 0x20 || c == 0x7f) result.append(String.format("\\u%04X", (int) c));
            else result.append(c);
        }
        return result.toString();
    }

    private static String value(Object value) {
        return value == null ? "" : String.valueOf(value);
    }

    private static String tsv(Object... values) {
        StringBuilder row = new StringBuilder();
        for (int i = 0; i < values.length; i++) {
            if (i != 0) row.append('\t');
            if (values[i] != null) row.append(values[i]);
        }
        return row.toString();
    }

    private static String hex(long value) {
        return String.format("%016X", value);
    }

    private static MethodNode method(ClassNode owner, String name, String descriptor) {
        for (MethodNode method : owner.methods) {
            if (name.equals(method.name) && descriptor.equals(method.desc)) return method;
        }
        return null;
    }

    private static Integer intConstant(AbstractInsnNode insn) {
        if (insn == null) return null;
        int opcode = insn.getOpcode();
        if (opcode >= Opcodes.ICONST_M1 && opcode <= Opcodes.ICONST_5) {
            return opcode - Opcodes.ICONST_0;
        }
        if (insn instanceof IntInsnNode && (opcode == Opcodes.BIPUSH || opcode == Opcodes.SIPUSH)) {
            return ((IntInsnNode) insn).operand;
        }
        if (insn instanceof LdcInsnNode && ((LdcInsnNode) insn).cst instanceof Integer) {
            return (Integer) ((LdcInsnNode) insn).cst;
        }
        return null;
    }

    private static Long longConstant(AbstractInsnNode insn) {
        if (insn == null) return null;
        if (insn.getOpcode() == Opcodes.LCONST_0) return 0L;
        if (insn.getOpcode() == Opcodes.LCONST_1) return 1L;
        if (insn instanceof LdcInsnNode && ((LdcInsnNode) insn).cst instanceof Long) {
            return (Long) ((LdcInsnNode) insn).cst;
        }
        return null;
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

    static final class RecoverySummary {
        int parsedClasses;
        int totalStandardIndySites;
        int classKeys;
        int transactionalClassKeys;
        int hierarchyClassKeys;
        int hierarchyPasses;
        int keyConflicts;
        int standardIndyClasses;
        int standardIndySites;
        int tableClasses;
        int tableFailures;
        int resolvedArguments;
        int decryptedSites;
        int plausibleSites;
        int genericInnerClasses;
        int genericInnerSites;
        int sequencePasses;
        int prerequisiteClassKeys;
        int unresolvedClassKeys;
        int rewriteClasses;
        int rewriteMethods;
        int rewritePlannedSites;
        int rewriteAppliedSites;
        int rewriteSkippedSites;
        int rewriteRollbackClasses;
        int remainingStandardIndySites;
        int outputClasses;
        int outputVerificationErrors;
        int archiveEntries;
        int archiveResources;
        int signaturesRemoved;
    }

    private static final class RewriteClassResult {
        final List<RewriteRecord> records = new ArrayList<>();
        byte[] bytes;
        int plannedSites;
        int appliedSites;
        int skippedSites;
        int changedMethods;
        boolean rolledBack;
    }

    private static final class RewriteRecord {
        final String method;
        final int instruction;
        final String plaintext;
        String action;
        String reason;

        RewriteRecord(String method, int instruction, String plaintext, String action,
                      String reason) {
            this.method = method;
            this.instruction = instruction;
            this.plaintext = plaintext;
            this.action = action;
            this.reason = reason;
        }
    }

    private static final class ArchiveWriteResult {
        int entries;
        int resources;
        int signaturesRemoved;
    }

    private static final class ArchiveVerification {
        int classes;
        int errors;
        int standardIndySites;
    }

    private static final class KeyOrderResult {
        final Map<String, Long> keys;
        final int passes;
        final int unresolved;
        final int prerequisites;
        int transactionalKeys;
        int hierarchyKeys;
        int hierarchyPasses;
        final List<String> ambiguities = new ArrayList<>();

        KeyOrderResult(Map<String, Long> keys, int passes, int unresolved, int prerequisites) {
            this.keys = keys;
            this.passes = passes;
            this.unresolved = unresolved;
            this.prerequisites = prerequisites;
        }
    }

    private static final class KeyField {
        final String owner;
        final String name;
        final long value;

        KeyField(String owner, String name, long value) {
            this.owner = owner;
            this.name = name;
            this.value = value;
        }
    }

    private static final class DecryptSpec {
        final MethodNode method;
        final long indexMask;
        final int indexXor;
        final String tableField;

        DecryptSpec(MethodNode method, long indexMask, int indexXor, String tableField) {
            this.method = method;
            this.indexMask = indexMask;
            this.indexXor = indexXor;
            this.tableField = tableField;
        }
    }

    static final class TableLayout {
        final AbstractInsnNode allocationStore;
        final AbstractInsnNode tableStore;
        final int expectedEntries;

        TableLayout(AbstractInsnNode allocationStore, AbstractInsnNode tableStore,
                    int expectedEntries) {
            this.allocationStore = allocationStore;
            this.tableStore = tableStore;
            this.expectedEntries = expectedEntries;
        }
    }

    private static final class InferredTable {
        final TableLayout layout;
        final List<TableCandidate> candidates;

        InferredTable(TableLayout layout, List<TableCandidate> candidates) {
            this.layout = layout;
            this.candidates = candidates;
        }
    }

    private static final class TableFragment {
        final int instruction;
        final int initialChunk;
        final List<String> entries;

        TableFragment(int instruction, int initialChunk, List<String> entries) {
            this.instruction = instruction;
            this.initialChunk = initialChunk;
            this.entries = entries;
        }
    }

    static final class TableCandidate {
        final List<Integer> literalInstructions;
        final List<Integer> initialChunkSizes;
        final List<String> entries;

        TableCandidate() {
            this(new ArrayList<>(), new ArrayList<>(), new ArrayList<>());
        }

        private TableCandidate(List<Integer> literalInstructions, List<Integer> initialChunkSizes,
                               List<String> entries) {
            this.literalInstructions = literalInstructions;
            this.initialChunkSizes = initialChunkSizes;
            this.entries = entries;
        }

        TableCandidate append(TableFragment fragment) {
            List<Integer> instructions = new ArrayList<>(literalInstructions);
            instructions.add(fragment.instruction);
            List<Integer> chunks = new ArrayList<>(initialChunkSizes);
            chunks.add(fragment.initialChunk);
            List<String> combinedEntries = new ArrayList<>(entries);
            combinedEntries.addAll(fragment.entries);
            return new TableCandidate(instructions, chunks, combinedEntries);
        }

        String instructions() {
            return joinInts(literalInstructions);
        }

        String initialChunks() {
            return joinInts(initialChunkSizes);
        }

        private static String joinInts(List<Integer> values) {
            StringBuilder result = new StringBuilder();
            for (int i = 0; i < values.size(); i++) {
                if (i != 0) result.append(',');
                result.append(values.get(i));
            }
            return result.toString();
        }
    }

    private static final class IndySite {
        final MethodNode method;
        final InvokeDynamicInsnNode node;
        final int instruction;

        IndySite(MethodNode method, InvokeDynamicInsnNode node, int instruction) {
            this.method = method;
            this.node = node;
            this.instruction = instruction;
        }
    }

    private static final class LongExpression {
        final long value;
        final AbstractInsnNode start;

        LongExpression(long value, AbstractInsnNode start) {
            this.value = value;
            this.start = start;
        }
    }

    private static final class IntExpression {
        final int value;
        final AbstractInsnNode start;

        IntExpression(int value, AbstractInsnNode start) {
            this.value = value;
            this.start = start;
        }
    }

    private static final class ArgumentExpressions {
        final IntExpression intArgument;
        final LongExpression longArgument;

        ArgumentExpressions(IntExpression intArgument, LongExpression longArgument) {
            this.intArgument = intArgument;
            this.longArgument = longArgument;
        }
    }

    private static final class GenericSiteMatches {
        final IndySite site;
        final ArgumentExpressions arguments;
        final List<GenericMatch> matches = new ArrayList<>();

        GenericSiteMatches(IndySite site, ArgumentExpressions arguments) {
            this.site = site;
            this.arguments = arguments;
        }
    }

    private static final class GenericMatch {
        final int index;
        final int indexXor;
        final String plaintext;

        GenericMatch(int index, int indexXor, String plaintext) {
            this.index = index;
            this.indexXor = indexXor;
            this.plaintext = plaintext;
        }
    }

    private static final class SiteResult {
        final IndySite site;
        final Integer callInt;
        final Long callLong;
        final Integer tableIndex;
        final String plaintext;
        final String status;

        SiteResult(IndySite site, Integer callInt, Long callLong, Integer tableIndex,
                   String plaintext, String status) {
            this.site = site;
            this.callInt = callInt;
            this.callLong = callLong;
            this.tableIndex = tableIndex;
            this.plaintext = plaintext;
            this.status = status;
        }

        static SiteResult failure(IndySite site, String status) {
            return new SiteResult(site, null, null, null, null, status);
        }

        static SiteResult indexFailure(IndySite site, int callInt, long callLong, int index) {
            return new SiteResult(site, callInt, callLong, index, null, "INDEX_OUT_OF_RANGE");
        }

        static SiteResult decryptFailure(IndySite site, int callInt, long callLong, int index) {
            return new SiteResult(site, callInt, callLong, index, null, "INNER_DES_FAILED");
        }

        static SiteResult success(IndySite site, int callInt, long callLong, int index,
                                  String plaintext, boolean plausible) {
            return new SiteResult(site, callInt, callLong, index, plaintext,
                    plausible ? "OK" : "OK_NONPRINTABLE");
        }
    }

    private static final class CandidateScore implements Comparable<CandidateScore> {
        final TableCandidate candidate;
        final List<SiteResult> results = new ArrayList<>();
        int resolved;
        int decrypted;
        int plausible;
        Integer genericIndexXor;

        CandidateScore(TableCandidate candidate) {
            this.candidate = candidate;
        }

        @Override
        public int compareTo(CandidateScore other) {
            int result = Integer.compare(decrypted, other.decrypted);
            if (result != 0) return result;
            result = Integer.compare(plausible, other.plausible);
            if (result != 0) return result;
            result = Integer.compare(resolved, other.resolved);
            if (result != 0) return result;
            return Integer.compare(candidate.entries.size(), other.candidate.entries.size());
        }
    }
}
