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
import org.objectweb.asm.tree.TryCatchBlockNode;
import org.objectweb.asm.tree.TypeInsnNode;
import org.objectweb.asm.tree.VarInsnNode;
import org.objectweb.asm.tree.analysis.Analyzer;
import org.objectweb.asm.tree.analysis.BasicValue;
import org.objectweb.asm.tree.analysis.BasicVerifier;
import org.objectweb.asm.tree.analysis.Frame;
import org.objectweb.asm.tree.analysis.SourceInterpreter;
import org.objectweb.asm.tree.analysis.SourceValue;
import org.objectweb.asm.util.CheckClassAdapter;

import java.io.ByteArrayOutputStream;
import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.nio.charset.StandardCharsets;
import java.nio.ByteBuffer;
import java.nio.file.AtomicMoveNotSupportedException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.StandardCopyOption;
import java.security.MessageDigest;
import java.util.ArrayList;
import java.util.ArrayDeque;
import java.util.Arrays;
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
 * Atomically closes and removes the complete ZKM long-key runtime dependency.
 *
 * <p>The public output is all-or-nothing. Class keys are proved from an isolated
 * per-owner JVM initialization chain, all {@code (IJ)I} sites are proved and
 * directized, all long-key bootstraps are folded, removable key fields are
 * inlined, the three central runtime classes are deleted, and dead bootstrap
 * families are cleaned in a private staging archive. The requested output is
 * published only after an archive-wide zero-reference scan succeeds. Input
 * classes are parsed as bytes and are never defined or initialized.</p>
 */
public final class ZkmRuntimeClosureDeobfuscator {
    static final String STATE = ObfRuntimeNames.STATE;
    static final String STATE_INTERFACE =
            ObfRuntimeNames.STATE_INTERFACE;
    static final String GRAPH =
            ObfRuntimeNames.GRAPH_BOOTSTRAP;
    static final String PAIR_CONSTANTS =
            ObfRuntimeNames.STRING_PAIR_CONSTANTS;
    private static final String KEY_BOOTSTRAP_DESC =
            ObfRuntimeNames.BOOTSTRAP_DESC;
    private static final String BSM_DESC = "(Ljava/lang/invoke/MethodHandles$Lookup;"
            + "Ljava/lang/String;Ljava/lang/invoke/MethodType;)"
            + "Ljava/lang/invoke/CallSite;";
    private static final String INTEGER_DESC = "(IJ)I";
    private static final Set<String> RUNTIME_CLASSES = new LinkedHashSet<>(
            Arrays.asList(STATE, STATE_INTERFACE, GRAPH, PAIR_CONSTANTS));

    private ZkmRuntimeClosureDeobfuscator() {
    }

    public static void main(String[] args) throws Exception {
        if (args.length != 3 && args.length != 4 && args.length != 5) {
            System.err.println("usage: ZkmRuntimeClosureDeobfuscator <input.jar>"
                    + " <report-dir> <output.jar> [pre-removal-authority.jar]"
                    + " [semantic-evidence.tsv]");
            System.exit(2);
        }
        Summary summary;
        if (args.length == 3) {
            summary = close(Paths.get(args[0]), Paths.get(args[1]),
                    Paths.get(args[2]));
        } else if (args.length == 4) {
            summary = close(Paths.get(args[0]), Paths.get(args[3]),
                    Paths.get(args[1]), Paths.get(args[2]));
        } else {
            summary = close(Paths.get(args[0]), Paths.get(args[3]),
                    Paths.get(args[1]), Paths.get(args[2]), Paths.get(args[4]));
        }
        System.out.println("classes=" + summary.parsedClasses + " keys="
                + summary.provenClassKeys + " integer=" + summary.integerSitesDirectized
                + "/" + summary.integerSites + " bootstraps="
                + summary.keyBootstrapsRemoved + " runtime_classes="
                + summary.runtimeClassesRemoved + " committed=" + summary.outputCommitted
                + " report=" + args[1]);
        if (!summary.outputCommitted) {
            throw new IllegalStateException("runtime closure failed; see " + args[1]);
        }
    }

    static Summary close(Path input, Path reportDirectory, Path output) throws Exception {
        List<ArchiveEntry> entries = readEntries(input);
        ParsedArchive archive = parse(entries);
        ProofSet proofs = proveJvmInitializationChains(archive.classes);
        return close(input, reportDirectory, output, entries, archive, proofs,
                "per-owner-jvm-initialization-chain");
    }

    static Summary close(Path input, Path authority, Path reportDirectory,
                         Path output) throws Exception {
        List<ArchiveEntry> entries = readEntries(input);
        ParsedArchive archive = parse(entries);
        ProofSet proofs = proveJvmInitializationChains(archive.classes);
        Map<String, ClassNode> authorityClasses =
                ZkmLongKeyEvaluator.readClasses(authority);
        proofs.authorityClasses.putAll(authorityClasses);
        addAuthorityCandidates(proofs, authorityClasses);
        proofs.authority = authority.toAbsolutePath().normalize().toString();
        return close(input, reportDirectory, output, entries, archive, proofs,
                "per-owner-jvm-chain+pre-removal-authority-candidates");
    }

    /**
     * Closes the runtime with explicit, separately audited semantic evidence.
     * The four-path overload never reads this evidence implicitly.
     */
    static Summary close(Path input, Path authority, Path reportDirectory,
                         Path output, Path semanticEvidence) throws Exception {
        List<ArchiveEntry> entries = readEntries(input);
        ParsedArchive archive = parse(entries);
        ProofSet proofs = proveJvmInitializationChains(archive.classes);
        Map<String, ClassNode> authorityClasses =
                ZkmLongKeyEvaluator.readClasses(authority);
        proofs.authorityClasses.putAll(authorityClasses);
        addAuthorityCandidates(proofs, authorityClasses);
        proofs.authority = authority.toAbsolutePath().normalize().toString();
        proofs.semanticEvidence = semanticEvidence.toAbsolutePath().normalize().toString();
        return close(input, reportDirectory, output, entries, archive, proofs,
                "per-owner-jvm-chain+pre-removal-authority-candidates"
                        + "+explicit-semantic-evidence");
    }

    /** Test-only entry that exercises closure and publication with supplied proofs. */
    static Summary closeWithProvenKeys(Path input, Path reportDirectory, Path output,
                                       Map<String, Long> provenKeys) throws Exception {
        List<ArchiveEntry> entries = readEntries(input);
        ParsedArchive archive = parse(entries);
        ProofSet proofs = new ProofSet();
        for (Map.Entry<String, Long> entry : provenKeys.entrySet()) {
            proofs.keys.put(entry.getKey(), entry.getValue());
            proofs.addCandidate(entry.getKey(), entry.getValue());
            proofs.rows.add(tsv(entry.getKey(), hex(entry.getValue()), entry.getKey(),
                    "test-supplied-proof"));
        }
        return close(input, reportDirectory, output, entries, archive, proofs,
                "test-supplied-proof");
    }

    private static Summary close(Path input, Path reportDirectory, Path output,
                                 List<ArchiveEntry> entries, ParsedArchive archive,
                                 ProofSet proofs, String proofSource) throws Exception {
        Files.createDirectories(reportDirectory);
        validatePaths(input, output);
        Summary summary = new Summary();
        summary.parsedClasses = archive.classes.size();
        summary.inputEntries = entries.size();
        summary.provenClassKeys = proofs.keys.size();
        summary.proofSource = proofSource;
        summary.authority = proofs.authority;
        summary.provenanceRows.addAll(proofs.rows);
        Path firstStage = null;
        Path memberStage = null;
        Path cleanedStage = null;
        try {
            for (String runtime : RUNTIME_CLASSES) {
                if (!archive.classes.containsKey(runtime)) {
                    fail(summary, "inventory", runtime, "<class>",
                            "missing-runtime-class", "required runtime entity is absent");
                }
            }

            summary.integerSites = countIntegerSites(archive.classes);
            List<SemanticOverride> semanticOverrides = Collections.emptyList();
            if (!proofs.semanticEvidence.isEmpty()) {
                summary.semanticEvidencePath = proofs.semanticEvidence;
                try {
                    semanticOverrides = loadSemanticOverrides(
                            Paths.get(proofs.semanticEvidence));
                } catch (Throwable failure) {
                    fail(summary, "semantic-evidence", "<archive>", "<input>",
                            "invalid-evidence", shortReason(failure));
                    writeReports(input, output, reportDirectory, summary);
                    return summary;
                }
            }
            ManualPlan manual = planManualOverrides(archive.classes, proofs,
                    semanticOverrides, summary);
            if (!summary.failures.isEmpty()) {
                invalidateUncoveredIntegerKeys(archive.classes, proofs,
                        manual.coveredOwners);
                summary.provenClassKeys = proofs.keys.size();
                syncProvenance(summary, proofs);
                writeReports(input, output, reportDirectory, summary);
                return summary;
            }
            refineIntegerClassKeys(archive.classes, proofs, manual.coveredOwners,
                    summary);
            summary.provenClassKeys = proofs.keys.size();
            syncProvenance(summary, proofs);
            if (!summary.failures.isEmpty()) {
                writeReports(input, output, reportDirectory, summary);
                return summary;
            }

            List<IntegerPlan> integerPlans = proveIntegerSites(archive.classes,
                    proofs.keys, manual.coveredOwners, summary);
            integerPlans.addAll(manual.plans);
            if (!summary.failures.isEmpty()) {
                writeReports(input, output, reportDirectory, summary);
                return summary;
            }

            List<KeyPlan> keyPlans = discoverKeyPlans(archive.classes, proofs.keys,
                    summary);
            validateKeyFields(archive.classes, keyPlans, summary);
            if (!summary.failures.isEmpty()) {
                writeReports(input, output, reportDirectory, summary);
                return summary;
            }

            applyIntegerPlans(integerPlans, summary);

            Set<String> changedOwners = applyKeyPlans(archive.classes, keyPlans,
                    summary);

            Map<String, byte[]> replacements = emitChangedClasses(archive.classes,
                    changedOwners, summary);
            if (!summary.failures.isEmpty()) {
                writeReports(input, output, reportDirectory, summary);
                return summary;
            }

            Path outputParent = output.toAbsolutePath().normalize().getParent();
            if (outputParent == null) outputParent = Paths.get(".").toAbsolutePath();
            Files.createDirectories(outputParent);
            firstStage = Files.createTempFile(outputParent,
                    ".zkm-runtime-closure-key-", ".jar");
            memberStage = Files.createTempFile(outputParent,
                    ".zkm-runtime-closure-member-", ".jar");
            Files.deleteIfExists(memberStage);
            cleanedStage = Files.createTempFile(outputParent,
                    ".zkm-runtime-closure-bootstrap-", ".jar");
            Files.deleteIfExists(cleanedStage);
            writeArchive(entries, replacements, firstStage, summary);

            Residue stageResidue = scanResidue(firstStage);
            summary.keyStageCentralReferences = stageResidue.centralRawReferences;
            summary.keyStageIntegerIndy = stageResidue.integerIndy;
            if (stageResidue.runtimeClassEntries != 0
                    || stageResidue.centralRawReferences != 0
                    || stageResidue.integerIndy != 0
                    || summary.integerSitesDirectized != summary.integerSites) {
                appendResidueFailures(summary, "key-stage", stageResidue);
                if (summary.integerSitesDirectized != summary.integerSites) {
                    fail(summary, "key-stage", "<archive>", "<semantic-overrides>",
                            "incomplete-integer-directization", "directized="
                                    + summary.integerSitesDirectized + "/"
                                    + summary.integerSites);
                }
                writeReports(input, output, reportDirectory, summary);
                return summary;
            }

            ZkmMemberIndyDirectizer.Summary member =
                    ZkmMemberIndyDirectizer.directizeIdentity(firstStage,
                            reportDirectory.resolve("member-directization"),
                            memberStage);
            summary.helperTotalDirectizedSites = member.rewrittenSites;
            if (!member.outputCommitted || member.remainingMemberSites != 0
                    || !Files.isRegularFile(memberStage)) {
                fail(summary, "member-directization", "<archive>", "<output>",
                        "member-directizer-not-closed", "rewritten="
                                + member.rewrittenSites + ";remaining="
                                + member.remainingMemberSites + ";rollbacks="
                                + member.classRollbacks);
                writeReports(input, output, reportDirectory, summary);
                return summary;
            }

            ZkmBootstrapSupportCleaner.Summary cleaner =
                    ZkmBootstrapSupportCleaner.clean(memberStage,
                            reportDirectory.resolve("bootstrap-cleanup"), cleanedStage);
            summary.bootstrapFamiliesRemoved = cleaner.verifiedFamilies;
            summary.bootstrapMethodsRemoved = cleaner.methodsRemoved;
            summary.bootstrapFieldsRemoved = cleaner.fieldsRemoved;
            if (!cleaner.outputCommitted || !Files.isRegularFile(cleanedStage)) {
                fail(summary, "bootstrap-cleanup", "<archive>", "<output>",
                        "cleaner-not-committed", "bootstrap cleaner did not commit staging");
                writeReports(input, output, reportDirectory, summary);
                return summary;
            }

            Residue residue = scanResidue(cleanedStage);
            copyResidue(summary, residue);
            int expectedClasses = summary.parsedClasses - RUNTIME_CLASSES.size();
            if (residue.parsedClasses != expectedClasses || residue.parseErrors != 0) {
                fail(summary, "final-gate", "<archive>", "<classes>",
                        "class-integrity", "expected=" + expectedClasses + ";parsed="
                                + residue.parsedClasses + ";errors=" + residue.parseErrors);
            }
            appendResidueFailures(summary, "final-gate", residue);
            if (!summary.failures.isEmpty()) {
                writeReports(input, output, reportDirectory, summary);
                return summary;
            }

            atomicMove(cleanedStage, output);
            cleanedStage = null;
            summary.outputCommitted = true;
            summary.outputSha256 = sha256(output);
            writeReports(input, output, reportDirectory, summary);
            return summary;
        } catch (Throwable failure) {
            fail(summary, "exception", "<archive>", "<transaction>",
                    failure.getClass().getSimpleName(), stackReason(failure));
            writeReports(input, output, reportDirectory, summary);
            return summary;
        } finally {
            if (firstStage != null) Files.deleteIfExists(firstStage);
            if (memberStage != null) Files.deleteIfExists(memberStage);
            if (cleanedStage != null) Files.deleteIfExists(cleanedStage);
        }
    }

    private static List<SemanticOverride> loadSemanticOverrides(Path path)
            throws IOException {
        if (!Files.isRegularFile(path)) {
            throw new IllegalArgumentException("semantic evidence is not a file: "
                    + path);
        }
        List<String> lines = Files.readAllLines(path, StandardCharsets.UTF_8);
        String header = "class\tmethod\tdescriptor\tinstruction\tint_argument"
                + "\tlong_literal_hex\tkey_mask_hex\texpected_int\tevidence";
        if (lines.isEmpty() || !header.equals(lines.get(0))) {
            throw new IllegalArgumentException("semantic evidence header mismatch");
        }
        List<SemanticOverride> result = new ArrayList<>();
        Set<String> identities = new LinkedHashSet<>();
        for (int line = 1; line < lines.size(); line++) {
            String text = lines.get(line);
            if (text.trim().isEmpty()) continue;
            String[] cells = text.split("\t", -1);
            if (cells.length != 9) {
                throw new IllegalArgumentException("semantic evidence line "
                        + (line + 1) + " has " + cells.length + " columns");
            }
            int instruction;
            int intArgument;
            int expected;
            try {
                instruction = Integer.parseInt(cells[3]);
                intArgument = Integer.parseInt(cells[4]);
                expected = Integer.parseInt(cells[7]);
            } catch (NumberFormatException failure) {
                throw new IllegalArgumentException("invalid integer on semantic evidence line "
                        + (line + 1), failure);
            }
            if (cells[0].isEmpty() || cells[1].isEmpty() || cells[2].isEmpty()
                    || cells[8].trim().isEmpty() || instruction < 0) {
                throw new IllegalArgumentException("incomplete semantic evidence line "
                        + (line + 1));
            }
            SemanticOverride row = new SemanticOverride(cells[0], cells[1], cells[2],
                    instruction, intArgument, parseUnsignedHex(cells[5], line + 1),
                    parseUnsignedHex(cells[6], line + 1), expected, cells[8],
                    line + 1);
            if (!identities.add(row.identity())) {
                throw new IllegalArgumentException("duplicate semantic evidence site: "
                        + row.identity());
            }
            result.add(row);
        }
        if (result.isEmpty()) {
            throw new IllegalArgumentException("semantic evidence contains no rows");
        }
        return result;
    }

    static int validateSemanticEvidence(Path path) throws IOException {
        return loadSemanticOverrides(path).size();
    }

    private static long parseUnsignedHex(String text, int line) {
        if (!text.matches("[0-9A-Fa-f]{16}")) {
            throw new IllegalArgumentException("semantic evidence line " + line
                    + " requires a 16-digit hexadecimal long");
        }
        return Long.parseUnsignedLong(text, 16);
    }

    /**
     * Converts explicit human semantic observations into a cryptographic key
     * discriminator. The evidence is accepted only when it covers every integer
     * site in an owner and leaves exactly one pre-removal authority candidate.
     */
    private static ManualPlan planManualOverrides(
            Map<String, ClassNode> classes, ProofSet proofs,
            List<SemanticOverride> overrides, Summary summary) {
        ManualPlan result = new ManualPlan();
        summary.semanticEvidenceRows = overrides.size();
        if (overrides.isEmpty()) return result;

        Map<String, List<SemanticOverride>> byOwner = new LinkedHashMap<>();
        for (SemanticOverride row : overrides) {
            byOwner.computeIfAbsent(row.owner,
                    ignored -> new ArrayList<SemanticOverride>()).add(row);
        }

        for (Map.Entry<String, List<SemanticOverride>> ownerEntry
                : byOwner.entrySet()) {
            String ownerName = ownerEntry.getKey();
            ClassNode owner = classes.get(ownerName);
            if (owner == null) {
                fail(summary, "semantic-evidence", ownerName, "<class>",
                        "missing-owner", "owner is absent from input archive");
                continue;
            }
            List<IntegerSite> sites = integerSites(owner);
            List<SemanticOverride> rows = ownerEntry.getValue();
            Map<String, IntegerSite> sitesByIdentity = new LinkedHashMap<>();
            for (IntegerSite site : sites) {
                sitesByIdentity.put(siteIdentity(owner.name, site.method,
                        evidenceInstructionIndex(site.method, site.node)), site);
            }
            if (sites.size() != rows.size()) {
                fail(summary, "semantic-evidence", ownerName, "<class>",
                        "incomplete-owner-coverage", "sites=" + sites.size()
                                + ";evidence=" + rows.size());
                continue;
            }

            Map<String, SemanticOverride> rowsByIdentity = new LinkedHashMap<>();
            Map<MethodNode, Frame<SourceValue>[]> frames = new IdentityHashMap<>();
            boolean shapeValid = true;
            MethodNode clinit = method(owner, "<clinit>", "()V");
            String keyField = keyField(owner, clinit);
            LiteralIntegerSpec spec = literalIntegerSpec(owner);
            List<Long> table = spec == null || clinit == null || keyField == null
                    ? null : literalLongTable(owner, clinit, spec.tableField);
            if (keyField == null || spec == null || table == null || table.isEmpty()) {
                fail(summary, "semantic-evidence", ownerName, "<class>",
                        "integer-shape", "key-field=" + keyField + ";spec="
                                + (spec != null) + ";table="
                                + (table == null ? "null" : table.size()));
                continue;
            }
            for (SemanticOverride row : rows) {
                IntegerSite site = sitesByIdentity.get(row.identity());
                MethodNode declaredMethod = method(owner, row.method, row.descriptor);
                if (site == null || declaredMethod == null
                        || evidenceInstructionAt(declaredMethod, row.instruction)
                        != site.node) {
                    fail(summary, "semantic-evidence", ownerName,
                            row.method + row.descriptor, "site-fingerprint-mismatch",
                            "instruction=" + row.instruction + ";site-found="
                                    + (site != null) + ";method-found="
                                    + (declaredMethod != null) + ";actual="
                                    + (site == null ? -1
                                    : site.method.instructions.indexOf(site.node))
                                    + ";available=" + describeSites(sites)
                                    + ";line=" + row.line);
                    shapeValid = false;
                    continue;
                }
                if (!matchesSemanticLongShape(ownerName, site, keyField, row, frames)) {
                    fail(summary, "semantic-evidence", ownerName,
                            row.method + row.descriptor, "long-expression-mismatch",
                            "instruction=" + row.instruction + ";literal="
                                    + hex(row.longLiteral) + ";mask="
                                    + hex(row.keyMask) + ";line=" + row.line);
                    shapeValid = false;
                    continue;
                }
                rowsByIdentity.put(row.identity(), row);
            }
            if (!shapeValid || rowsByIdentity.size() != sites.size()) continue;

            Set<Long> available = proofs.candidates.get(ownerName);
            if (available == null || available.isEmpty()) {
                fail(summary, "semantic-evidence", ownerName, "<class>",
                        "no-authority-candidates", "authority candidates are required");
                continue;
            }
            Set<Long> expanded = expandLowKeyBits(available);
            List<Long> passing = new ArrayList<>();
            for (Long candidate : expanded) {
                if (candidateMatchesSemanticEvidence(owner, keyField, candidate,
                        sites, rowsByIdentity, spec, table, frames)) {
                    passing.add(candidate);
                }
            }
            if (passing.size() != 1) {
                recordSemanticEvidenceAudit(owner, sites, rowsByIdentity, null,
                        passing.isEmpty() ? "FINGERPRINT_PASS_NO_CANDIDATE"
                                : "FINGERPRINT_PASS_AMBIGUOUS_CANDIDATE",
                        summary);
                fail(summary, "semantic-evidence", ownerName, "<class>",
                        "non-unique-semantic-candidate", "available="
                                + available.size() + ";expanded=" + expanded.size()
                                + ";passing=" + passing.size() + ";keys="
                                + joinHex(passing));
                continue;
            }

            long selected = passing.get(0);
            List<Integer> values = new ArrayList<>();
            for (IntegerSite site : sites) {
                SemanticOverride row = rowsByIdentity.get(siteIdentity(owner.name,
                        site.method, evidenceInstructionIndex(site.method, site.node)));
                values.add(row.expectedInt);
            }
            recordSemanticEvidenceAudit(owner, sites, rowsByIdentity, selected,
                    "PASS", summary);
            proofs.keys.put(ownerName, selected);
            replaceProvenanceRow(proofs.rows, ownerName,
                    tsv(ownerName, hex(selected), ownerName + ";authority="
                                    + joinHex(new ArrayList<Long>(available)),
                            "explicit-semantic-evidence-unique-authority-candidate"));
            result.coveredOwners.add(ownerName);
            result.plans.add(new IntegerPlan(owner, sites, values, true));
            summary.semanticEvidenceOwners++;
            summary.integerProofRows.add(tsv(ownerName, hex(selected), sites.size(),
                    sites.size(), sites.size(), sites.size(),
                    "PASS_EXPLICIT_SEMANTIC_EVIDENCE", "authority="
                            + available.size() + ";expanded=" + expanded.size()
                            + ";unique=" + hex(selected)));
        }
        return result;
    }

    private static void recordSemanticEvidenceAudit(
            ClassNode owner, List<IntegerSite> sites,
            Map<String, SemanticOverride> rows, Long selectedKey, String status,
            Summary summary) {
        for (IntegerSite site : sites) {
            int stableInstruction = evidenceInstructionIndex(site.method, site.node);
            SemanticOverride row = rows.get(siteIdentity(owner.name, site.method,
                    stableInstruction));
            if (row == null) continue;
            summary.semanticEvidenceAuditRows.add(tsv(owner.name,
                    site.method.name, site.method.desc, stableInstruction,
                    site.instruction, row.intArgument, hex(row.longLiteral),
                    hex(row.keyMask), row.expectedInt,
                    selectedKey == null ? "" : hex(selectedKey), status,
                    row.evidence));
        }
    }

    private static Set<Long> expandLowKeyBits(Set<Long> candidates) {
        Set<Long> result = new LinkedHashSet<>();
        for (Long candidate : candidates) {
            long prefix = candidate & ~0x7fffL;
            for (int low = 0; low <= 0x7fff; low++) result.add(prefix | low);
        }
        return result;
    }

    private static boolean candidateMatchesSemanticEvidence(
            ClassNode owner, String keyField, long key, List<IntegerSite> sites,
            Map<String, SemanticOverride> rows, LiteralIntegerSpec spec,
            List<Long> table, Map<MethodNode, Frame<SourceValue>[]> frames) {
        Set<Integer> indexes = new LinkedHashSet<>();
        Map<Integer, Integer> valuesByIndex = new LinkedHashMap<>();
        try {
            for (IntegerSite site : sites) {
                SemanticOverride row = rows.get(siteIdentity(owner.name, site.method,
                        evidenceInstructionIndex(site.method, site.node)));
                if (row == null) return false;
                LiteralArguments arguments = resolveLiteralArguments(owner.name, site,
                        owner.name, keyField, key, frames);
                if (arguments == null || arguments.intValue != row.intArgument
                        || arguments.longValue
                        != (row.longLiteral ^ row.keyMask ^ key)) return false;
                int index = arguments.intValue
                        ^ (int) (arguments.longValue & spec.indexMask)
                        ^ spec.indexXor;
                if (index < 0 || index >= table.size()) return false;
                int value = ZkmIntegerDecryptor.decryptInteger(table.get(index),
                        arguments.longValue);
                if (value != row.expectedInt) return false;
                Integer previous = valuesByIndex.put(index, value);
                if (previous != null && previous.intValue() != value) return false;
                indexes.add(index);
            }
            return indexes.size() == table.size();
        } catch (Throwable ignored) {
            return false;
        }
    }

    private static boolean matchesSemanticLongShape(
            String owner, IntegerSite site, String keyField, SemanticOverride row,
            Map<MethodNode, Frame<SourceValue>[]> cachedFrames) {
        try {
            Frame<SourceValue>[] frames = cachedFrames.get(site.method);
            if (frames == null) {
                frames = new Analyzer<SourceValue>(new SourceInterpreter())
                        .analyze(owner, site.method);
                cachedFrames.put(site.method, frames);
            }
            int index = site.method.instructions.indexOf(site.node);
            if (index < 0 || frames[index] == null
                    || frames[index].getStackSize() < 2) return false;
            SourceValue source = frames[index].getStack(
                    frames[index].getStackSize() - 1);
            if (source == null || source.getSize() != 2 || source.insns.size() != 1) {
                return false;
            }
            XorFingerprint fingerprint = new XorFingerprint();
            if (collectXorTerms(source.insns.iterator().next(), site.method, owner,
                    keyField, fingerprint, new LinkedHashSet<Integer>()) == null) {
                return false;
            }
            List<Long> expected = new ArrayList<>(
                    Arrays.asList(row.longLiteral, row.keyMask));
            for (Long constant : fingerprint.constants) {
                if (!expected.remove(constant)) return false;
            }
            return expected.isEmpty() && fingerprint.constants.size() == 2
                    && fingerprint.keyReads == 1 && fingerprint.xorOperations == 2;
        } catch (Throwable ignored) {
            return false;
        }
    }

    private static LongExpression collectXorTerms(
            AbstractInsnNode end, MethodNode method, String keyOwner,
            String keyField, XorFingerprint fingerprint, Set<Integer> activeLocals) {
        if (end == null) return null;
        Long constant = longConstant(end);
        if (constant != null) {
            fingerprint.constants.add(constant);
            return new LongExpression(0L, end);
        }
        if (end instanceof FieldInsnNode && end.getOpcode() == Opcodes.GETSTATIC) {
            FieldInsnNode field = (FieldInsnNode) end;
            if (!keyOwner.equals(field.owner) || !keyField.equals(field.name)
                    || !"J".equals(field.desc)) return null;
            fingerprint.keyReads++;
            return new LongExpression(0L, end);
        }
        if (end instanceof VarInsnNode && end.getOpcode() == Opcodes.LLOAD) {
            int local = ((VarInsnNode) end).var;
            if (!activeLocals.add(local)) return null;
            AbstractInsnNode store = uniqueStore(method, end, local, Opcodes.LSTORE);
            LongExpression value = store == null ? null : collectXorTerms(
                    previousCode(store), method, keyOwner, keyField, fingerprint,
                    activeLocals);
            activeLocals.remove(local);
            return value == null ? null : new LongExpression(0L, end);
        }
        if (end.getOpcode() != Opcodes.LXOR) return null;
        fingerprint.xorOperations++;
        LongExpression right = collectXorTerms(previousCode(end), method, keyOwner,
                keyField, fingerprint, activeLocals);
        LongExpression left = right == null ? null : collectXorTerms(
                previousCode(right.start), method, keyOwner, keyField, fingerprint,
                activeLocals);
        return left == null ? null : new LongExpression(0L, left.start);
    }

    private static AbstractInsnNode uniqueStore(MethodNode method,
                                                AbstractInsnNode load,
                                                int local, int opcode) {
        AbstractInsnNode result = null;
        for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
             insn = insn.getNext()) {
            if (!(insn instanceof VarInsnNode) || insn.getOpcode() != opcode
                    || ((VarInsnNode) insn).var != local) continue;
            if (method.instructions.indexOf(insn) >= method.instructions.indexOf(load)
                    || result != null) return null;
            result = insn;
        }
        return result;
    }

    private static String siteIdentity(String owner, MethodNode method,
                                       int instruction) {
        return owner + "\t" + method.name + "\t" + method.desc + "\t" + instruction;
    }

    /** Matches the residue scanner's frame-independent instruction coordinate. */
    static int evidenceInstructionIndex(MethodNode method,
                                        AbstractInsnNode target) {
        int index = 0;
        for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
             insn = insn.getNext()) {
            if (insn instanceof FrameNode) continue;
            if (insn == target) return index;
            index++;
        }
        return -1;
    }

    static AbstractInsnNode evidenceInstructionAt(MethodNode method,
                                                  int expectedIndex) {
        int index = 0;
        for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
             insn = insn.getNext()) {
            if (insn instanceof FrameNode) continue;
            if (index == expectedIndex) return insn;
            index++;
        }
        return null;
    }

    private static String describeSites(List<IntegerSite> sites) {
        StringBuilder result = new StringBuilder();
        for (IntegerSite site : sites) {
            if (result.length() != 0) result.append('|');
            result.append(site.method.name).append(site.method.desc).append('@')
                    .append(evidenceInstructionIndex(site.method, site.node))
                    .append("(raw:").append(site.instruction).append(')');
        }
        return result.toString();
    }

    private static String joinHex(List<Long> values) {
        StringBuilder result = new StringBuilder();
        for (Long value : values) {
            if (result.length() != 0) result.append(',');
            result.append(hex(value));
        }
        return result.toString();
    }

    /**
     * Selects one pre-removal state-model candidate by requiring every
     * class-local integer site to select and decrypt its explicit table entry.
     */
    private static void refineIntegerClassKeys(Map<String, ClassNode> classes,
                                               ProofSet proofs,
                                               Set<String> manuallyCoveredOwners,
                                               Summary summary) {
        for (ClassNode owner : classes.values()) {
            List<IntegerSite> sites = integerSites(owner);
            if (sites.isEmpty()) continue;
            if (manuallyCoveredOwners.contains(owner.name)) continue;
            Long baseKey = proofs.keys.get(owner.name);
            LiteralIntegerSpec spec = literalIntegerSpec(owner);
            MethodNode clinit = method(owner, "<clinit>", "()V");
            String field = keyField(owner, clinit);
            List<Long> table = spec == null || clinit == null || field == null
                    ? null : literalLongTable(owner, clinit, spec.tableField);
            ClassNode authorityOwner = proofs.authorityClasses.get(owner.name);
            ZkmIntegerDecryptor.IntegerProof authorityShape = authorityOwner == null
                    || baseKey == null ? null
                    : ZkmIntegerDecryptor.proveClassKey(authorityOwner, baseKey);
            int authorityTableSize = authorityShape == null
                    ? 0 : authorityShape.tableEntries;
            boolean authorityTable = (table == null || table.isEmpty())
                    && authorityOwner != null && authorityTableSize > 0;
            if (baseKey == null || spec == null || field == null
                    || ((table == null || table.isEmpty()) && !authorityTable)) {
                invalidateIntegerKey(proofs, owner.name);
                fail(summary, "integer-key-oracle", owner.name, "<class>",
                        "oracle-shape", "base=" + (baseKey != null) + ";spec="
                                + (spec != null) + ";field=" + field + ";table="
                                + (table == null ? "null" : table.size())
                                + ";authority-table=" + authorityTableSize);
                continue;
            }
            Set<Long> available = proofs.candidates.get(owner.name);
            Set<Long> expanded = new LinkedHashSet<>();
            if (available != null) {
                for (Long authorityCandidate : available) {
                    long prefix = authorityCandidate & ~0x7fffL;
                    for (int low = 0; low <= 0x7fff; low++) {
                        expanded.add(prefix | low);
                    }
                }
            }
            List<Long> passing = new ArrayList<>();
            Map<Long, List<Integer>> passingValues = new LinkedHashMap<>();
            Map<MethodNode, Frame<SourceValue>[]> frames = new IdentityHashMap<>();
            if (!expanded.isEmpty()) {
                for (Long candidate : expanded) {
                    if (!integerIndexesInRange(owner, field, candidate, sites, spec,
                            authorityTable ? authorityTableSize : table.size(), frames)) {
                        continue;
                    }
                    if (authorityTable) {
                        ZkmIntegerDecryptor.IntegerProof proof =
                                ZkmIntegerDecryptor.proveClassKey(authorityOwner,
                                        candidate);
                        if (proof.passes() && proof.values.size() == sites.size()) {
                            passing.add(candidate);
                            passingValues.put(candidate,
                                    new ArrayList<Integer>(proof.values));
                        }
                    } else {
                        List<Integer> values = decryptIntegerSites(owner, field,
                                candidate, sites, spec, table, frames);
                        if (values != null && values.size() == sites.size()) {
                            passing.add(candidate);
                            passingValues.put(candidate, values);
                        }
                    }
                }
            }
            Long selected = selectProvenBaseKey(baseKey, passing);
            if (selected == null) {
                invalidateIntegerKey(proofs, owner.name);
                fail(summary, "integer-key-oracle", owner.name, "<class>",
                        "non-unique-authority-candidate", "available="
                                + (available == null ? 0 : available.size())
                                + ";expanded=" + expanded.size() + ";passing="
                                + passing.size() + ";base=" + hex(baseKey)
                                + ";passing-values="
                                + describePassingValues(passing, passingValues) + ";"
                                + (authorityTable ? "authority-table="
                                + authorityTableSize : describeIntegerCandidates(owner,
                                field, passing, sites, spec, table, frames)));
                continue;
            }
            List<Integer> values = passingValues.get(selected);
            if (values == null || values.size() != sites.size()) {
                invalidateIntegerKey(proofs, owner.name);
                fail(summary, "integer-key-oracle", owner.name, "<class>",
                        "inner-des-proof", "values="
                                + (values == null ? 0 : values.size()) + "/"
                                + sites.size());
                continue;
            }
            proofs.keys.put(owner.name, selected);
            replaceProvenanceRow(proofs.rows, owner.name,
                    tsv(owner.name, hex(selected), owner.name + ";base=" + hex(baseKey),
                    passing.size() == 1
                            ? "pre-removal-authority+explicit-integer-table-unique"
                            : "jvm-init-chain-exact+authority-table-all-sites-pass"));
            summary.integerProofRows.add(tsv(owner.name, hex(selected), sites.size(),
                    sites.size(), sites.size(), values.size(), "PASS_AUTHORITY_ORACLE",
                    "base=" + hex(baseKey) + ";table="
                            + (authorityTable ? authorityTableSize : table.size())
                            + ";available=" + available.size() + ";passing="
                            + passing.size() + ";values="
                            + joinIntegers(values)));
        }
    }

    static Long selectProvenBaseKey(Long baseKey, List<Long> passing) {
        if (passing.size() == 1) return passing.get(0);
        return baseKey != null && passing.contains(baseKey) ? baseKey : null;
    }

    private static String describePassingValues(
            List<Long> passing, Map<Long, List<Integer>> passingValues) {
        StringBuilder result = new StringBuilder();
        for (Long candidate : passing) {
            if (result.length() != 0) result.append('|');
            result.append(hex(candidate)).append(':')
                    .append(joinIntegers(passingValues.get(candidate)));
        }
        return result.toString();
    }

    private static void invalidateUncoveredIntegerKeys(
            Map<String, ClassNode> classes, ProofSet proofs,
            Set<String> coveredOwners) {
        for (ClassNode owner : classes.values()) {
            if (!integerSites(owner).isEmpty() && !coveredOwners.contains(owner.name)) {
                invalidateIntegerKey(proofs, owner.name);
            }
        }
    }

    private static void invalidateIntegerKey(ProofSet proofs, String owner) {
        proofs.keys.remove(owner);
        for (int index = proofs.rows.size() - 1; index >= 0; index--) {
            String row = proofs.rows.get(index);
            if (row.equals(owner) || row.startsWith(owner + "\t")) {
                proofs.rows.remove(index);
            }
        }
    }

    private static void syncProvenance(Summary summary, ProofSet proofs) {
        summary.provenanceRows.clear();
        summary.provenanceRows.addAll(proofs.rows);
    }

    private static String describeIntegerCandidates(
            ClassNode owner, String field, List<Long> candidates,
            List<IntegerSite> sites, LiteralIntegerSpec spec, List<Long> table,
            Map<MethodNode, Frame<SourceValue>[]> frames) {
        StringBuilder result = new StringBuilder();
        for (Long candidate : candidates) {
            if (result.length() != 0) result.append('|');
            List<Integer> values = decryptIntegerSites(owner, field, candidate,
                    sites, spec, table, frames);
            result.append(hex(candidate)).append(':')
                    .append(values == null ? "FAIL" : joinIntegers(values));
        }
        return result.toString();
    }

    private static boolean integerIndexesInRange(
            ClassNode owner, String keyField, long key, List<IntegerSite> sites,
            LiteralIntegerSpec spec, int tableSize,
            Map<MethodNode, Frame<SourceValue>[]> frames) {
        try {
            for (IntegerSite site : sites) {
                LiteralArguments arguments = resolveLiteralArguments(owner.name,
                        site, owner.name, keyField, key, frames);
                if (arguments == null) return false;
                int index = arguments.intValue
                        ^ (int) (arguments.longValue & spec.indexMask)
                        ^ spec.indexXor;
                if (index < 0 || index >= tableSize) return false;
            }
            return true;
        } catch (Throwable failure) {
            return false;
        }
    }

    private static List<Integer> decryptIntegerSites(
            ClassNode owner, String keyField, long key, List<IntegerSite> sites,
            LiteralIntegerSpec spec, List<Long> table,
            Map<MethodNode, Frame<SourceValue>[]> frames) {
        List<Integer> result = new ArrayList<>();
        Map<Integer, Integer> valuesByIndex = new LinkedHashMap<>();
        try {
            for (IntegerSite site : sites) {
                LiteralArguments arguments = resolveLiteralArguments(owner.name,
                        site, owner.name, keyField, key, frames);
                if (arguments == null) return null;
                int index = arguments.intValue
                        ^ (int) (arguments.longValue & spec.indexMask)
                        ^ spec.indexXor;
                if (index < 0 || index >= table.size()) return null;
                int value = ZkmIntegerDecryptor.decryptInteger(table.get(index),
                        arguments.longValue);
                Integer previous = valuesByIndex.put(index, value);
                if (previous != null && previous.intValue() != value) return null;
                result.add(value);
            }
            return valuesByIndex.size() == table.size() ? result : null;
        } catch (Throwable failure) {
            return null;
        }
    }

    private static void replaceProvenanceRow(List<String> rows, String owner,
                                             String replacement) {
        String prefix = owner + "\t";
        for (int index = 0; index < rows.size(); index++) {
            if (rows.get(index).startsWith(prefix)) {
                rows.set(index, replacement);
                return;
            }
        }
        rows.add(replacement);
    }

    private static String joinIntegers(List<Integer> values) {
        StringBuilder result = new StringBuilder();
        for (Integer value : values) {
            if (result.length() != 0) result.append(',');
            result.append(value);
        }
        return result.toString();
    }

    private static ProofSet proveJvmInitializationChains(
            Map<String, ClassNode> classes) {
        ZkmLongKeyEvaluator.StatefulKeySequence base =
                ZkmLongKeyEvaluator.newStatefulKeySequence(classes);
        ProofSet result = new ProofSet();
        for (String owner : base.owners()) {
            ZkmLongKeyEvaluator.StatefulKeySequence sequence = base.copy();
            List<String> order = new ArrayList<>();
            collectInitializationOrder(owner, classes, new HashSet<String>(),
                    new HashSet<String>(), order);
            List<String> committed = new ArrayList<>();
            Long selected = null;
            for (String current : order) {
                if (!sequence.hasSite(current)) continue;
                long value = sequence.commit(current);
                committed.add(current);
                if (owner.equals(current)) selected = value;
            }
            if (selected == null) {
                throw new IllegalStateException("no JVM initialization-chain key for "
                        + owner);
            }
            result.keys.put(owner, selected);
            result.addCandidate(owner, selected);
            result.rows.add(tsv(owner, hex(selected), String.join(">", committed),
                    "per-owner-jvm-initialization-chain"));
        }
        return result;
    }

    private static void addAuthorityCandidates(ProofSet proofs,
                                               Map<String, ClassNode> classes) {
        addCandidates(proofs, ZkmLongKeyEvaluator.evaluateClassKeys(classes));
        addCandidates(proofs,
                ZkmLongKeyEvaluator.evaluateClassKeysSequential(classes));
        ZkmLongKeyEvaluator.StatefulKeySequence sequence =
                ZkmLongKeyEvaluator.newStatefulKeySequence(classes);
        addCandidates(proofs, evaluateOrder(classes,
                hierarchyOrder(classes, sequence.owners())));
        try {
            ZkmClassKeySelector.Selection selected = ZkmClassKeySelector.select(classes);
            for (Map.Entry<String, Long> entry : selected.selectedKeys().entrySet()) {
                if (!proofs.keys.containsKey(entry.getKey())) continue;
                proofs.addCandidate(entry.getKey(), entry.getValue());
                proofs.keys.put(entry.getKey(), entry.getValue());
                replaceProvenanceRow(proofs.rows, entry.getKey(),
                        tsv(entry.getKey(), hex(entry.getValue()), entry.getKey(),
                                "pre-removal-authority-independent-selection"));
            }
        } catch (Throwable ignored) {
            // Model candidates remain available; the final consumer gate is mandatory.
        }
        ProofSet authorityChains = proveJvmInitializationChains(classes);
        for (Map.Entry<String, Long> entry : authorityChains.keys.entrySet()) {
            if (!proofs.keys.containsKey(entry.getKey())) continue;
            proofs.addCandidate(entry.getKey(), entry.getValue());
            proofs.keys.put(entry.getKey(), entry.getValue());
            replaceProvenanceRow(proofs.rows, entry.getKey(),
                    tsv(entry.getKey(), hex(entry.getValue()), entry.getKey(),
                            "pre-removal-authority-jvm-initialization-chain"));
        }
    }

    private static void addCandidates(ProofSet proofs, Map<String, Long> values) {
        for (Map.Entry<String, Long> entry : values.entrySet()) {
            if (proofs.keys.containsKey(entry.getKey())) {
                proofs.addCandidate(entry.getKey(), entry.getValue());
            }
        }
    }

    private static Map<String, Long> evaluateOrder(Map<String, ClassNode> classes,
                                                   List<String> order) {
        ZkmLongKeyEvaluator.StatefulKeySequence sequence =
                ZkmLongKeyEvaluator.newStatefulKeySequence(classes);
        Map<String, Long> result = new LinkedHashMap<>();
        for (String owner : order) {
            if (sequence.hasSite(owner)) result.put(owner, sequence.commit(owner));
        }
        return result;
    }

    private static List<String> hierarchyOrder(Map<String, ClassNode> classes,
                                               List<String> keyOwners) {
        Set<String> keys = new HashSet<>(keyOwners);
        Set<String> visited = new HashSet<>();
        Set<String> active = new HashSet<>();
        List<String> result = new ArrayList<>();
        for (String owner : keyOwners) {
            visitHierarchy(owner, classes, keys, visited, active, result);
        }
        return result;
    }

    private static void visitHierarchy(String owner,
                                       Map<String, ClassNode> classes,
                                       Set<String> keys, Set<String> visited,
                                       Set<String> active, List<String> result) {
        if (visited.contains(owner)) return;
        if (!active.add(owner)) {
            throw new IllegalStateException("hierarchy-cycle=" + owner);
        }
        ClassNode node = classes.get(owner);
        if (node != null && (node.access & Opcodes.ACC_INTERFACE) == 0
                && node.superName != null && classes.containsKey(node.superName)) {
            visitHierarchy(node.superName, classes, keys, visited, active, result);
        }
        active.remove(owner);
        visited.add(owner);
        if (keys.contains(owner)) result.add(owner);
    }

    private static void collectInitializationOrder(
            String name, Map<String, ClassNode> classes, Set<String> visited,
            Set<String> active, List<String> result) {
        if (visited.contains(name)) return;
        if (!active.add(name)) {
            throw new IllegalStateException("initialization-cycle=" + name);
        }
        ClassNode owner = classes.get(name);
        if (owner != null && (owner.access & Opcodes.ACC_INTERFACE) == 0
                && owner.superName != null && classes.containsKey(owner.superName)) {
            collectInitializationOrder(owner.superName, classes, visited, active,
                    result);
        }
        if (owner != null) {
            for (String iface : owner.interfaces) {
                if (declaresOrInheritsDefaultMethod(iface, classes,
                        new LinkedHashSet<String>())) {
                    collectInitializationOrder(iface, classes, visited, active,
                            result);
                }
            }
        }
        active.remove(name);
        visited.add(name);
        result.add(name);
    }

    private static boolean declaresOrInheritsDefaultMethod(
            String name, Map<String, ClassNode> classes, Set<String> visited) {
        if (!visited.add(name)) return false;
        ClassNode owner = classes.get(name);
        if (owner == null || (owner.access & Opcodes.ACC_INTERFACE) == 0) return false;
        for (MethodNode method : owner.methods) {
            if ("<clinit>".equals(method.name) || "<init>".equals(method.name)) continue;
            if ((method.access & (Opcodes.ACC_ABSTRACT | Opcodes.ACC_STATIC)) == 0) {
                return true;
            }
        }
        for (String parent : owner.interfaces) {
            if (declaresOrInheritsDefaultMethod(parent, classes, visited)) return true;
        }
        return false;
    }

    private static List<KeyPlan> discoverKeyPlans(
            Map<String, ClassNode> classes, Map<String, Long> keys,
            Summary summary) {
        List<KeyPlan> plans = new ArrayList<>();
        Set<String> owners = new LinkedHashSet<>();
        for (ClassNode owner : classes.values()) {
            for (MethodNode method : owner.methods) {
                int instruction = 0;
                for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
                     insn = insn.getNext(), instruction++) {
                    if (!isKeyBootstrap(insn)) continue;
                    Long key = keys.get(owner.name);
                    if (key == null) {
                        fail(summary, "key-plan", owner.name,
                                method.name + method.desc, "unproved-key",
                                "instruction=" + instruction);
                        continue;
                    }
                    AbstractInsnNode start = bootstrapStart(insn);
                    AbstractInsnNode input = nextCode(insn);
                    AbstractInsnNode transform = nextCode(input);
                    if (start == null || longConstant(input) == null
                            || !isKeyTransform(transform)
                            || !isExactBootstrapSequence(start, transform)) {
                        fail(summary, "key-plan", owner.name,
                                method.name + method.desc, "unrecognized-bootstrap-shape",
                                "instruction=" + instruction);
                        continue;
                    }
                    if (!owners.add(owner.name)) {
                        fail(summary, "key-plan", owner.name,
                                method.name + method.desc, "multiple-key-bootstraps",
                                "instruction=" + instruction);
                        continue;
                    }
                    AbstractInsnNode after = nextCode(transform);
                    FieldInsnNode fieldWrite = after instanceof FieldInsnNode
                            && after.getOpcode() == Opcodes.PUTSTATIC
                            && owner.name.equals(((FieldInsnNode) after).owner)
                            && "J".equals(((FieldInsnNode) after).desc)
                            ? (FieldInsnNode) after : null;
                    AbstractInsnNode end = fieldWrite == null ? transform : fieldWrite;
                    if (hasControlBoundary(method, start, end)) {
                        fail(summary, "key-plan", owner.name,
                                method.name + method.desc, "control-boundary-in-key-slice",
                                "instruction=" + instruction);
                        continue;
                    }
                    plans.add(new KeyPlan(owner, method, start, transform,
                            fieldWrite, key, instruction));
                    summary.actions.add(tsv(owner.name, method.name + method.desc,
                            instruction, fieldWrite == null ? "fold-key-chain"
                                    : "inline-key-field", fieldWrite == null ? ""
                                    : fieldWrite.name, hex(key),
                            "per-owner-jvm-initialization-chain"));
                }
            }
        }
        for (String owner : keys.keySet()) {
            if (!owners.contains(owner)) {
                fail(summary, "key-plan", owner, "<archive>",
                        "proved-key-without-bootstrap", "no matching key chain");
            }
        }
        summary.keyBootstraps = plans.size();
        return plans;
    }

    private static List<IntegerPlan> proveIntegerSites(
            Map<String, ClassNode> classes, Map<String, Long> keys,
            Set<String> excludedOwners, Summary summary) {
        List<IntegerPlan> plans = new ArrayList<>();
        for (ClassNode owner : classes.values()) {
            List<IntegerSite> sites = integerSites(owner);
            if (sites.isEmpty()) continue;
            if (excludedOwners.contains(owner.name)) continue;
            Long key = keys.get(owner.name);
            if (key == null) {
                fail(summary, "integer-proof", owner.name, "<class>",
                        "integer-owner-without-key", "sites=" + sites.size());
                continue;
            }
            ZkmIntegerDecryptor.IntegerProof proof =
                    ZkmIntegerDecryptor.proveClassKey(owner, key);
            List<Integer> values = proof.passes() ? proof.values
                    : proveLiteralIntegerTable(owner, key, sites, summary);
            boolean literal = !proof.passes() && values != null;
            String status = literal ? "PASS_LITERAL_LONG_TABLE" : proof.status;
            String reason = literal ? "post-DES explicit long[] table; all sites proven"
                    : proof.reason;
            int resolved = literal ? sites.size() : proof.resolvedArguments;
            int indexed = literal ? sites.size() : proof.indexedSites;
            int decrypted = literal ? sites.size() : proof.decryptedSites;
            summary.integerProofRows.add(tsv(owner.name, hex(key), sites.size(),
                    resolved, indexed, decrypted, status, reason));
            if (values == null || values.size() != sites.size()) {
                fail(summary, "integer-proof", owner.name, "<class>", proof.status,
                        proof.reason + ";literal-table-proof=failed;values="
                                + (values == null ? 0 : values.size()) + "/"
                                + sites.size());
                continue;
            }
            plans.add(new IntegerPlan(owner, sites, values, false));
        }
        return plans;
    }

    /** Proves integer sites after an earlier DES pass materialized the outer table. */
    private static List<Integer> proveLiteralIntegerTable(
            ClassNode owner, long classKey, List<IntegerSite> sites,
            Summary summary) {
        try {
            LiteralIntegerSpec spec = literalIntegerSpec(owner);
            MethodNode clinit = method(owner, "<clinit>", "()V");
            String keyField = keyField(owner, clinit);
            List<Long> table = spec == null || clinit == null || keyField == null
                    ? null : literalLongTable(owner, clinit, spec.tableField);
            if (spec == null || clinit == null || keyField == null
                    || table == null || table.isEmpty()) {
                summary.integerProofRows.add(tsv(owner.name, hex(classKey),
                        sites.size(), 0, 0, 0, "LITERAL_TABLE_SHAPE_FAIL",
                        "spec=" + (spec != null) + ";clinit=" + (clinit != null)
                                + ";key-field=" + keyField + ";table="
                                + (table == null ? "null" : table.size())));
                return null;
            }
            List<Integer> values = new ArrayList<>();
            Map<MethodNode, Frame<SourceValue>[]> frames = new IdentityHashMap<>();
            for (IntegerSite site : sites) {
                LiteralArguments arguments = resolveLiteralArguments(owner.name,
                        site, owner.name, keyField, classKey, frames);
                if (arguments == null) {
                    summary.integerProofRows.add(tsv(owner.name, hex(classKey),
                            sites.size(), values.size(), 0, 0,
                            "LITERAL_ARGUMENT_FAIL", site.method.name
                                    + site.method.desc + "@" + site.instruction));
                    return null;
                }
                int tableIndex = arguments.intValue
                        ^ (int) (arguments.longValue & spec.indexMask)
                        ^ spec.indexXor;
                if (tableIndex < 0 || tableIndex >= table.size()) {
                    summary.integerProofRows.add(tsv(owner.name, hex(classKey),
                            sites.size(), values.size() + 1, values.size(), 0,
                            "LITERAL_INDEX_FAIL", "index=" + tableIndex
                                    + ";table=" + table.size() + ";int="
                                    + arguments.intValue + ";long="
                                    + arguments.longValue + ";mask=" + spec.indexMask
                                    + ";xor=" + spec.indexXor));
                    return null;
                }
                values.add(ZkmIntegerDecryptor.decryptInteger(
                        table.get(tableIndex), arguments.longValue));
            }
            return values;
        } catch (Throwable failure) {
            summary.integerProofRows.add(tsv(owner.name, hex(classKey), sites.size(),
                    0, 0, 0, "LITERAL_TABLE_ERROR", shortReason(failure)));
            return null;
        }
    }

    private static LiteralIntegerSpec literalIntegerSpec(ClassNode owner) {
        List<LiteralIntegerSpec> result = new ArrayList<>();
        for (MethodNode method : owner.methods) {
            if ((method.access & Opcodes.ACC_STATIC) == 0
                    || !INTEGER_DESC.equals(method.desc)) continue;
            Long mask = null;
            Integer xor = null;
            String tableField = null;
            boolean cipher = false;
            boolean lowInt = false;
            for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
                 insn = insn.getNext()) {
                if (insn.getOpcode() == Opcodes.LAND) {
                    Long constant = longConstant(previousCode(insn));
                    if (constant != null) mask = constant;
                } else if (insn.getOpcode() == Opcodes.IXOR) {
                    Integer constant = intConstant(previousCode(insn));
                    if (constant != null) xor = constant;
                } else if (insn instanceof FieldInsnNode) {
                    FieldInsnNode field = (FieldInsnNode) insn;
                    if (field.getOpcode() == Opcodes.GETSTATIC
                            && owner.name.equals(field.owner)
                            && "[J".equals(field.desc)) {
                        AbstractInsnNode cursor = nextCode(insn);
                        for (int scanned = 0; cursor != null && scanned < 5;
                             scanned++, cursor = nextCode(cursor)) {
                            if (cursor.getOpcode() == Opcodes.LALOAD) {
                                tableField = field.name;
                                break;
                            }
                        }
                    }
                } else if (insn instanceof MethodInsnNode) {
                    MethodInsnNode call = (MethodInsnNode) insn;
                    if ("javax/crypto/Cipher".equals(call.owner)
                            && "doFinal".equals(call.name)) cipher = true;
                }
                if (insn.getOpcode() == Opcodes.BALOAD) {
                    Integer index = intConstant(previousCode(insn));
                    if (index != null && index == 7) lowInt = true;
                }
            }
            if (mask != null && xor != null && tableField != null
                    && cipher && lowInt) {
                result.add(new LiteralIntegerSpec(mask, xor, tableField));
            }
        }
        return result.size() == 1 ? result.get(0) : null;
    }

    private static String keyField(ClassNode owner, MethodNode clinit) {
        if (clinit == null) return null;
        String result = null;
        for (AbstractInsnNode insn = clinit.instructions.getFirst(); insn != null;
             insn = insn.getNext()) {
            if (!(insn instanceof FieldInsnNode)
                    || insn.getOpcode() != Opcodes.PUTSTATIC) continue;
            FieldInsnNode field = (FieldInsnNode) insn;
            if (!owner.name.equals(field.owner) || !"J".equals(field.desc)
                    || !isKeyTransform(previousCode(field))) continue;
            if (result != null) return null;
            result = field.name;
        }
        return result;
    }

    private static List<Long> literalLongTable(ClassNode owner, MethodNode clinit,
                                               String tableField) {
        FieldInsnNode store = null;
        for (AbstractInsnNode insn = clinit.instructions.getFirst(); insn != null;
             insn = insn.getNext()) {
            if (insn instanceof FieldInsnNode && insn.getOpcode() == Opcodes.PUTSTATIC) {
                FieldInsnNode field = (FieldInsnNode) insn;
                if (owner.name.equals(field.owner) && tableField.equals(field.name)
                        && "[J".equals(field.desc)) {
                    if (store != null) return null;
                    store = field;
                }
            }
        }
        if (store == null) return null;
        AbstractInsnNode value = previousCode(store);
        if (!(value instanceof VarInsnNode) || value.getOpcode() != Opcodes.ALOAD) {
            return null;
        }
        int local = ((VarInsnNode) value).var;
        VarInsnNode definition = null;
        int definitions = 0;
        for (AbstractInsnNode insn = clinit.instructions.getFirst(); insn != null;
             insn = insn.getNext()) {
            if (insn instanceof VarInsnNode && insn.getOpcode() == Opcodes.ASTORE
                    && ((VarInsnNode) insn).var == local) {
                definitions++;
                definition = (VarInsnNode) insn;
            }
        }
        if (definitions != 1 || definition == null) return null;
        AbstractInsnNode allocation = previousCode(definition);
        Integer size = allocation instanceof IntInsnNode
                && allocation.getOpcode() == Opcodes.NEWARRAY
                && ((IntInsnNode) allocation).operand == Opcodes.T_LONG
                ? intConstant(previousCode(allocation)) : null;
        if (size == null || size <= 0) return null;
        Long[] values = new Long[size];
        for (AbstractInsnNode insn = definition.getNext(); insn != null && insn != store;
             insn = insn.getNext()) {
            if (insn.getOpcode() != Opcodes.LASTORE) continue;
            AbstractInsnNode valueNode = previousCode(insn);
            AbstractInsnNode indexNode = previousCode(valueNode);
            AbstractInsnNode arrayNode = previousCode(indexNode);
            Long literal = longConstant(valueNode);
            Integer index = intConstant(indexNode);
            if (literal == null || index == null || index < 0 || index >= size
                    || !(arrayNode instanceof VarInsnNode)
                    || arrayNode.getOpcode() != Opcodes.ALOAD
                    || ((VarInsnNode) arrayNode).var != local
                    || values[index] != null) return null;
            values[index] = literal;
        }
        List<Long> result = new ArrayList<>();
        for (Long valueEntry : values) {
            if (valueEntry == null) return null;
            result.add(valueEntry);
        }
        return result;
    }

    private static LiteralArguments resolveLiteralArguments(
            String owner, IntegerSite site, String keyOwner, String keyField,
            long classKey, Map<MethodNode, Frame<SourceValue>[]> cachedFrames)
            throws Exception {
        Frame<SourceValue>[] frames = cachedFrames.get(site.method);
        if (frames == null) {
            frames = new Analyzer<SourceValue>(new SourceInterpreter())
                    .analyze(owner, site.method);
            cachedFrames.put(site.method, frames);
        }
        int index = site.method.instructions.indexOf(site.node);
        if (index < 0 || index >= frames.length || frames[index] == null
                || frames[index].getStackSize() < 2) return null;
        Frame<SourceValue> frame = frames[index];
        SourceValue intSource = frame.getStack(frame.getStackSize() - 2);
        SourceValue longSource = frame.getStack(frame.getStackSize() - 1);
        if (intSource == null || longSource == null || intSource.getSize() != 1
                || longSource.getSize() != 2 || intSource.insns.size() != 1
                || longSource.insns.size() != 1) return null;
        IntExpression intValue = evalInt(intSource.insns.iterator().next(),
                site.method, keyOwner, keyField, classKey);
        LongExpression longValue = evalLong(longSource.insns.iterator().next(),
                site.method, keyOwner, keyField, classKey);
        return intValue == null || longValue == null ? null
                : new LiteralArguments(intValue.value, longValue.value);
    }

    private static LongExpression evalLong(AbstractInsnNode end, MethodNode method,
                                           String keyOwner, String keyField,
                                           long classKey) {
        if (end == null) return null;
        Long constant = longConstant(end);
        if (constant != null) return new LongExpression(constant, end);
        if (end instanceof FieldInsnNode && end.getOpcode() == Opcodes.GETSTATIC) {
            FieldInsnNode field = (FieldInsnNode) end;
            if (keyOwner.equals(field.owner) && keyField.equals(field.name)
                    && "J".equals(field.desc)) {
                return new LongExpression(classKey, end);
            }
        }
        if (end instanceof VarInsnNode && end.getOpcode() == Opcodes.LLOAD) {
            AbstractInsnNode store = findStore(end, ((VarInsnNode) end).var,
                    Opcodes.LSTORE);
            LongExpression value = store == null ? null : evalLong(previousCode(store),
                    method, keyOwner, keyField, classKey);
            return value == null ? null : new LongExpression(value.value, end);
        }
        int opcode = end.getOpcode();
        if (opcode == Opcodes.LXOR || opcode == Opcodes.LAND || opcode == Opcodes.LOR
                || opcode == Opcodes.LADD || opcode == Opcodes.LSUB) {
            LongExpression right = evalLong(previousCode(end), method, keyOwner,
                    keyField, classKey);
            LongExpression left = right == null ? null
                    : evalLong(previousCode(right.start), method, keyOwner,
                    keyField, classKey);
            if (left == null || right == null) return null;
            long value = opcode == Opcodes.LXOR ? left.value ^ right.value
                    : opcode == Opcodes.LAND ? left.value & right.value
                    : opcode == Opcodes.LOR ? left.value | right.value
                    : opcode == Opcodes.LADD ? left.value + right.value
                    : left.value - right.value;
            return new LongExpression(value, left.start);
        }
        if (opcode == Opcodes.LNEG) {
            LongExpression value = evalLong(previousCode(end), method, keyOwner,
                    keyField, classKey);
            return value == null ? null : new LongExpression(-value.value, value.start);
        }
        return null;
    }

    private static IntExpression evalInt(AbstractInsnNode end, MethodNode method,
                                         String keyOwner, String keyField,
                                         long classKey) {
        if (end == null) return null;
        Integer constant = intConstant(end);
        if (constant != null) return new IntExpression(constant, end);
        if (end instanceof VarInsnNode && end.getOpcode() == Opcodes.ILOAD) {
            AbstractInsnNode store = findStore(end, ((VarInsnNode) end).var,
                    Opcodes.ISTORE);
            IntExpression value = store == null ? null : evalInt(previousCode(store),
                    method, keyOwner, keyField, classKey);
            return value == null ? null : new IntExpression(value.value, end);
        }
        int opcode = end.getOpcode();
        if (opcode == Opcodes.IXOR || opcode == Opcodes.IAND || opcode == Opcodes.IOR
                || opcode == Opcodes.IADD || opcode == Opcodes.ISUB) {
            IntExpression right = evalInt(previousCode(end), method, keyOwner,
                    keyField, classKey);
            IntExpression left = right == null ? null
                    : evalInt(previousCode(right.start), method, keyOwner,
                    keyField, classKey);
            if (left == null || right == null) return null;
            int value = opcode == Opcodes.IXOR ? left.value ^ right.value
                    : opcode == Opcodes.IAND ? left.value & right.value
                    : opcode == Opcodes.IOR ? left.value | right.value
                    : opcode == Opcodes.IADD ? left.value + right.value
                    : left.value - right.value;
            return new IntExpression(value, left.start);
        }
        if (opcode == Opcodes.L2I) {
            LongExpression value = evalLong(previousCode(end), method, keyOwner,
                    keyField, classKey);
            return value == null ? null : new IntExpression((int) value.value,
                    value.start);
        }
        return null;
    }

    private static AbstractInsnNode findStore(AbstractInsnNode load, int local,
                                              int opcode) {
        for (AbstractInsnNode cursor = load.getPrevious(); cursor != null;
             cursor = cursor.getPrevious()) {
            if (cursor instanceof VarInsnNode && cursor.getOpcode() == opcode
                    && ((VarInsnNode) cursor).var == local) return cursor;
        }
        return null;
    }

    private static MethodNode method(ClassNode owner, String name, String desc) {
        if (owner == null) return null;
        for (MethodNode method : owner.methods) {
            if (name.equals(method.name) && desc.equals(method.desc)) return method;
        }
        return null;
    }

    private static void validateKeyFields(Map<String, ClassNode> classes,
                                          List<KeyPlan> plans, Summary summary) {
        for (KeyPlan plan : plans) {
            if (plan.fieldWrite == null) continue;
            FieldNode declaration = null;
            for (FieldNode field : plan.owner.fields) {
                if (plan.fieldWrite.name.equals(field.name)
                        && "J".equals(field.desc)
                        && (field.access & Opcodes.ACC_STATIC) != 0) {
                    declaration = field;
                }
            }
            if (declaration == null) {
                fail(summary, "field-proof", plan.owner.name,
                        plan.fieldWrite.name + "J", "missing-field-declaration", "");
                continue;
            }
            int writes = 0;
            List<FieldInsnNode> reads = new ArrayList<>();
            boolean unsupportedReference = false;
            for (ClassNode owner : classes.values()) {
                for (MethodNode method : owner.methods) {
                    for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
                         insn = insn.getNext()) {
                        if (insn instanceof FieldInsnNode) {
                            FieldInsnNode field = (FieldInsnNode) insn;
                            if (!plan.owner.name.equals(field.owner)
                                    || !plan.fieldWrite.name.equals(field.name)
                                    || !"J".equals(field.desc)) continue;
                            if (field.getOpcode() == Opcodes.GETSTATIC) reads.add(field);
                            else if (field.getOpcode() == Opcodes.PUTSTATIC) {
                                writes++;
                                if (field != plan.fieldWrite) unsupportedReference = true;
                            } else unsupportedReference = true;
                        }
                        if (referencesFieldHandle(insn, plan.owner.name,
                                plan.fieldWrite.name, "J")) unsupportedReference = true;
                    }
                }
            }
            if (writes != 1 || unsupportedReference) {
                fail(summary, "field-proof", plan.owner.name,
                        plan.fieldWrite.name + "J", "field-reference-closure",
                        "writes=" + writes + ";unsupported=" + unsupportedReference);
                continue;
            }
            plan.field = declaration;
            plan.fieldReads.addAll(reads);
        }
    }

    private static void applyIntegerPlans(List<IntegerPlan> plans, Summary summary) {
        for (IntegerPlan plan : plans) {
            for (int index = 0; index < plan.sites.size(); index++) {
                IntegerSite site = plan.sites.get(index);
                int value = plan.values.get(index);
                if (!ZkmIntegerDecryptor.rewriteSiteToLdc(site.method, site.node, value)) {
                    throw new IllegalStateException("integer directization mismatch: "
                            + plan.owner.name + "." + site.method.name + site.method.desc
                            + "@" + site.instruction);
                }
                summary.integerSitesDirectized++;
                if (plan.semanticEvidence) summary.semanticSitesDirectized++;
                summary.actions.add(tsv(plan.owner.name,
                        site.method.name + site.method.desc, site.instruction,
                        "directize-integer-indy", "", value,
                        plan.semanticEvidence ? "explicit-semantic-evidence"
                                : "all-sites-class-key-proof"));
            }
        }
    }

    private static Set<String> applyKeyPlans(Map<String, ClassNode> classes,
                                              List<KeyPlan> plans,
                                              Summary summary) {
        Set<String> changed = new LinkedHashSet<>();
        for (KeyPlan plan : plans) {
            if (plan.fieldWrite != null) {
                if (plan.field == null) {
                    throw new IllegalStateException("unvalidated key field: "
                            + plan.owner.name + "." + plan.fieldWrite.name);
                }
                for (FieldInsnNode read : plan.fieldReads) {
                    MethodNode method = containingMethod(classes.get(read.owner), read);
                    if (method == null) {
                        method = containingMethod(classes, read);
                    }
                    if (method == null) {
                        throw new IllegalStateException("key field read owner not found");
                    }
                    method.instructions.set(read, new LdcInsnNode(plan.key));
                    summary.keyFieldReadsInlined++;
                    changed.add(ownerOf(classes, method));
                }
                removeCodeRange(plan.method, plan.start, plan.fieldWrite);
                plan.owner.fields.remove(plan.field);
                summary.keyFieldsRemoved++;
            } else {
                replaceRangeWithLong(plan.method, plan.start, plan.transform, plan.key);
            }
            summary.keyBootstrapsRemoved++;
            changed.add(plan.owner.name);
        }
        summary.runtimeClassesRemoved = RUNTIME_CLASSES.size();
        return changed;
    }

    private static MethodNode containingMethod(ClassNode owner, AbstractInsnNode target) {
        if (owner == null) return null;
        for (MethodNode method : owner.methods) {
            for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
                 insn = insn.getNext()) {
                if (insn == target) return method;
            }
        }
        return null;
    }

    private static MethodNode containingMethod(Map<String, ClassNode> classes,
                                               AbstractInsnNode target) {
        for (ClassNode owner : classes.values()) {
            MethodNode result = containingMethod(owner, target);
            if (result != null) return result;
        }
        return null;
    }

    private static String ownerOf(Map<String, ClassNode> classes, MethodNode target) {
        for (ClassNode owner : classes.values()) {
            if (owner.methods.contains(target)) return owner.name;
        }
        throw new IllegalStateException("method owner not found");
    }

    private static Map<String, byte[]> emitChangedClasses(
            Map<String, ClassNode> classes, Set<String> changedOwners,
            Summary summary) {
        Map<String, byte[]> result = new LinkedHashMap<>();
        for (String name : changedOwners) {
            if (RUNTIME_CLASSES.contains(name)) continue;
            ClassNode owner = classes.get(name);
            try {
                int flags = containsLegacySubroutine(owner)
                        ? ClassWriter.COMPUTE_MAXS
                        : ClassWriter.COMPUTE_FRAMES | ClassWriter.COMPUTE_MAXS;
                ClassWriter writer = flags == ClassWriter.COMPUTE_MAXS
                        ? new ClassWriter(flags)
                        : new HierarchyClassWriter(flags, classes);
                owner.accept(writer);
                byte[] bytes = writer.toByteArray();
                verifyClass(bytes);
                result.put(name, bytes);
            } catch (Throwable failure) {
                fail(summary, "class-verify", name, "<class>",
                        failure.getClass().getSimpleName(), shortReason(failure));
            }
        }
        summary.changedClasses = result.size();
        return result;
    }

    private static boolean containsLegacySubroutine(ClassNode owner) {
        for (MethodNode method : owner.methods) {
            for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
                 insn = insn.getNext()) {
                if (insn.getOpcode() == Opcodes.JSR || insn.getOpcode() == Opcodes.RET) {
                    return true;
                }
            }
        }
        return false;
    }

    private static void verifyClass(byte[] bytes) throws Exception {
        ClassReader reader = new ClassReader(bytes);
        reader.accept(new CheckClassAdapter(new ClassWriter(0), false), 0);
        ClassNode owner = new ClassNode(Opcodes.ASM9);
        reader.accept(owner, 0);
        for (MethodNode method : owner.methods) {
            if (method.instructions != null && method.instructions.size() != 0) {
                new Analyzer<BasicValue>(new BasicVerifier()).analyze(owner.name, method);
            }
        }
    }

    private static List<IntegerSite> integerSites(ClassNode owner) {
        List<IntegerSite> result = new ArrayList<>();
        for (MethodNode method : owner.methods) {
            int instruction = 0;
            for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
                 insn = insn.getNext(), instruction++) {
                if (insn instanceof InvokeDynamicInsnNode
                        && INTEGER_DESC.equals(((InvokeDynamicInsnNode) insn).desc)) {
                    result.add(new IntegerSite(method, (InvokeDynamicInsnNode) insn,
                            instruction));
                }
            }
        }
        result.sort(new Comparator<IntegerSite>() {
            @Override public int compare(IntegerSite left, IntegerSite right) {
                String a = left.method.name + left.method.desc + "\t" + left.instruction;
                String b = right.method.name + right.method.desc + "\t" + right.instruction;
                return a.compareTo(b);
            }
        });
        return result;
    }

    private static int countIntegerSites(Map<String, ClassNode> classes) {
        int result = 0;
        for (ClassNode owner : classes.values()) result += integerSites(owner).size();
        return result;
    }

    private static boolean isExactBootstrapSequence(AbstractInsnNode start,
                                                     AbstractInsnNode transform) {
        List<AbstractInsnNode> code = new ArrayList<>();
        for (AbstractInsnNode cursor = start; cursor != null; cursor = cursor.getNext()) {
            if (cursor.getOpcode() >= 0) code.add(cursor);
            if (cursor == transform) break;
        }
        if (code.size() != 6 && code.size() != 7) return false;
        if (longConstant(code.get(0)) == null || longConstant(code.get(1)) == null) {
            return false;
        }
        int bootstrapIndex;
        if (code.size() == 6) {
            if (code.get(2).getOpcode() != Opcodes.ACONST_NULL) return false;
            bootstrapIndex = 3;
        } else {
            if (!isLookup(code.get(2)) || !isLookupClass(code.get(3))) return false;
            bootstrapIndex = 4;
        }
        return isKeyBootstrap(code.get(bootstrapIndex))
                && longConstant(code.get(bootstrapIndex + 1)) != null
                && code.get(bootstrapIndex + 2) == transform
                && isKeyTransform(transform);
    }

    private static AbstractInsnNode bootstrapStart(AbstractInsnNode bootstrap) {
        AbstractInsnNode owner = previousCode(bootstrap);
        AbstractInsnNode seedB;
        if (owner != null && owner.getOpcode() == Opcodes.ACONST_NULL) {
            seedB = previousCode(owner);
        } else if (isLookupClass(owner)) {
            AbstractInsnNode lookup = previousCode(owner);
            if (!isLookup(lookup)) return null;
            seedB = previousCode(lookup);
        } else return null;
        AbstractInsnNode seedA = previousCode(seedB);
        return longConstant(seedA) != null && longConstant(seedB) != null
                ? seedA : null;
    }

    private static boolean isKeyBootstrap(AbstractInsnNode insn) {
        if (!(insn instanceof MethodInsnNode)) return false;
        MethodInsnNode call = (MethodInsnNode) insn;
        return call.getOpcode() == Opcodes.INVOKESTATIC && STATE.equals(call.owner)
                && "a".equals(call.name) && KEY_BOOTSTRAP_DESC.equals(call.desc);
    }

    private static boolean isKeyTransform(AbstractInsnNode insn) {
        if (!(insn instanceof MethodInsnNode)) return false;
        MethodInsnNode call = (MethodInsnNode) insn;
        return call.getOpcode() == Opcodes.INVOKEINTERFACE
                && STATE_INTERFACE.equals(call.owner) && "a".equals(call.name)
                && "(J)J".equals(call.desc);
    }

    private static boolean isLookup(AbstractInsnNode insn) {
        if (!(insn instanceof MethodInsnNode)) return false;
        MethodInsnNode call = (MethodInsnNode) insn;
        return call.getOpcode() == Opcodes.INVOKESTATIC
                && "java/lang/invoke/MethodHandles".equals(call.owner)
                && "lookup".equals(call.name)
                && "()Ljava/lang/invoke/MethodHandles$Lookup;".equals(call.desc);
    }

    private static boolean isLookupClass(AbstractInsnNode insn) {
        if (!(insn instanceof MethodInsnNode)) return false;
        MethodInsnNode call = (MethodInsnNode) insn;
        return call.getOpcode() == Opcodes.INVOKEVIRTUAL
                && "java/lang/invoke/MethodHandles$Lookup".equals(call.owner)
                && "lookupClass".equals(call.name)
                && "()Ljava/lang/Class;".equals(call.desc);
    }

    private static boolean hasControlBoundary(MethodNode method,
                                              AbstractInsnNode start,
                                              AbstractInsnNode end) {
        Set<LabelNode> protectedLabels = Collections.newSetFromMap(
                new IdentityHashMap<LabelNode, Boolean>());
        for (TryCatchBlockNode block : method.tryCatchBlocks) {
            protectedLabels.add(block.start);
            protectedLabels.add(block.end);
            protectedLabels.add(block.handler);
        }
        for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
             insn = insn.getNext()) {
            if (insn instanceof JumpInsnNode) {
                protectedLabels.add(((JumpInsnNode) insn).label);
            } else if (insn instanceof TableSwitchInsnNode) {
                TableSwitchInsnNode value = (TableSwitchInsnNode) insn;
                protectedLabels.add(value.dflt);
                protectedLabels.addAll(value.labels);
            } else if (insn instanceof LookupSwitchInsnNode) {
                LookupSwitchInsnNode value = (LookupSwitchInsnNode) insn;
                protectedLabels.add(value.dflt);
                protectedLabels.addAll(value.labels);
            }
        }
        boolean inside = false;
        for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
             insn = insn.getNext()) {
            if (insn == start) inside = true;
            if (inside && (insn instanceof FrameNode
                    || insn instanceof LabelNode && protectedLabels.contains(insn))) {
                return true;
            }
            if (insn == end) return false;
        }
        return true;
    }

    private static void replaceRangeWithLong(MethodNode method,
                                             AbstractInsnNode start,
                                             AbstractInsnNode end, long value) {
        AbstractInsnNode replacement = new LdcInsnNode(value);
        method.instructions.set(start, replacement);
        boolean inside = false;
        for (AbstractInsnNode insn = replacement.getNext(); insn != null; ) {
            AbstractInsnNode next = insn.getNext();
            if (insn.getOpcode() >= 0) method.instructions.remove(insn);
            if (insn == end) return;
            inside = true;
            insn = next;
        }
        if (!inside) throw new IllegalStateException("key range end was not found");
    }

    private static void removeCodeRange(MethodNode method, AbstractInsnNode start,
                                        AbstractInsnNode end) {
        boolean found = false;
        for (AbstractInsnNode insn = start; insn != null; ) {
            AbstractInsnNode next = insn.getNext();
            if (insn.getOpcode() >= 0) method.instructions.remove(insn);
            if (insn == end) {
                found = true;
                break;
            }
            insn = next;
        }
        if (!found) throw new IllegalStateException("key removal range end was not found");
    }

    private static boolean referencesFieldHandle(AbstractInsnNode insn, String owner,
                                                 String name, String desc) {
        if (insn instanceof LdcInsnNode) {
            return constantReferencesField(((LdcInsnNode) insn).cst, owner, name, desc);
        }
        if (insn instanceof InvokeDynamicInsnNode) {
            InvokeDynamicInsnNode indy = (InvokeDynamicInsnNode) insn;
            if (handleReferencesField(indy.bsm, owner, name, desc)) return true;
            for (Object argument : indy.bsmArgs) {
                if (constantReferencesField(argument, owner, name, desc)) return true;
            }
        }
        return false;
    }

    private static boolean constantReferencesField(Object value, String owner,
                                                   String name, String desc) {
        if (value instanceof Handle) {
            return handleReferencesField((Handle) value, owner, name, desc);
        }
        if (value instanceof ConstantDynamic) {
            ConstantDynamic dynamic = (ConstantDynamic) value;
            if (handleReferencesField(dynamic.getBootstrapMethod(), owner, name, desc)) {
                return true;
            }
            for (int i = 0; i < dynamic.getBootstrapMethodArgumentCount(); i++) {
                if (constantReferencesField(dynamic.getBootstrapMethodArgument(i),
                        owner, name, desc)) return true;
            }
        }
        return false;
    }

    private static boolean handleReferencesField(Handle handle, String owner,
                                                 String name, String desc) {
        if (handle == null || !owner.equals(handle.getOwner())
                || !name.equals(handle.getName()) || !desc.equals(handle.getDesc())) {
            return false;
        }
        int tag = handle.getTag();
        return tag == Opcodes.H_GETFIELD || tag == Opcodes.H_GETSTATIC
                || tag == Opcodes.H_PUTFIELD || tag == Opcodes.H_PUTSTATIC;
    }

    private static Residue scanResidue(Path input) throws IOException {
        Residue result = new Residue();
        try (ZipInputStream in = new ZipInputStream(Files.newInputStream(input))) {
            ZipEntry entry;
            while ((entry = in.getNextEntry()) != null) {
                if (entry.isDirectory() || !entry.getName().endsWith(".class")) continue;
                byte[] bytes = readAll(in);
                String entryOwner = entry.getName().substring(0,
                        entry.getName().length() - 6);
                if (RUNTIME_CLASSES.contains(entryOwner)) result.runtimeClassEntries++;
                for (String runtime : RUNTIME_CLASSES) {
                    result.centralRawReferences += countAscii(bytes, runtime);
                }
                try {
                    ClassNode owner = new ClassNode(Opcodes.ASM9);
                    new ClassReader(bytes).accept(owner, 0);
                    result.parsedClasses++;
                    scanClassResidue(owner, result);
                } catch (Throwable failure) {
                    result.parseErrors++;
                    result.details.add(tsv(entryOwner, "PARSE_ERROR",
                            shortReason(failure)));
                }
            }
        }
        return result;
    }

    private static void scanClassResidue(ClassNode owner, Residue result) {
        result.centralDescriptorReferences += countRuntimeMetadata(owner);
        for (MethodNode method : owner.methods) {
            if (BSM_DESC.equals(method.desc)
                    && (method.access & (Opcodes.ACC_PRIVATE | Opcodes.ACC_STATIC))
                    == (Opcodes.ACC_PRIVATE | Opcodes.ACC_STATIC)) {
                result.privateBootstrapMethods++;
                result.details.add(tsv(owner.name, "PRIVATE_BOOTSTRAP_METHOD",
                        method.name + method.desc));
            }
            for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
                 insn = insn.getNext()) {
                if (insn instanceof MethodInsnNode) {
                    MethodInsnNode call = (MethodInsnNode) insn;
                    if (RUNTIME_CLASSES.contains(call.owner)) {
                        result.centralMethodReferences++;
                        result.details.add(tsv(owner.name, "RUNTIME_METHOD_REF",
                                call.owner + "." + call.name + call.desc));
                    }
                    if ("java/lang/invoke/MutableCallSite".equals(call.owner)) {
                        result.mutableCallSiteCalls++;
                        result.details.add(tsv(owner.name, "MUTABLE_CALL_SITE",
                                call.name + call.desc));
                    }
                } else if (insn instanceof FieldInsnNode) {
                    FieldInsnNode field = (FieldInsnNode) insn;
                    if (RUNTIME_CLASSES.contains(field.owner)) {
                        result.centralFieldReferences++;
                        result.details.add(tsv(owner.name, "RUNTIME_FIELD_REF",
                                field.owner + "." + field.name + field.desc));
                    }
                } else if (insn instanceof InvokeDynamicInsnNode) {
                    InvokeDynamicInsnNode indy = (InvokeDynamicInsnNode) insn;
                    if (INTEGER_DESC.equals(indy.desc)) {
                        result.integerIndy++;
                        result.details.add(tsv(owner.name, "INTEGER_INDY",
                                method.name + method.desc));
                    }
                    if (indy.bsm != null && owner.name.equals(indy.bsm.getOwner())
                            && BSM_DESC.equals(indy.bsm.getDesc())) {
                        result.sameOwnerBootstrapIndy++;
                        result.details.add(tsv(owner.name, "SELF_BOOTSTRAP_INDY",
                                indy.name + indy.desc));
                    }
                    result.centralHandleReferences += countRuntimeHandle(indy.bsm);
                    for (Object argument : indy.bsmArgs) {
                        result.centralHandleReferences += countRuntimeConstant(argument);
                    }
                } else if (insn instanceof LdcInsnNode) {
                    result.centralHandleReferences +=
                            countRuntimeConstant(((LdcInsnNode) insn).cst);
                }
            }
        }
    }

    private static int countRuntimeMetadata(ClassNode owner) {
        int result = countRuntime(owner.superName) + countRuntime(owner.signature)
                + countRuntime(owner.outerClass) + countRuntime(owner.outerMethodDesc)
                + countRuntime(owner.nestHostClass);
        for (String iface : owner.interfaces) result += countRuntime(iface);
        if (owner.nestMembers != null) {
            for (String member : owner.nestMembers) result += countRuntime(member);
        }
        if (owner.permittedSubclasses != null) {
            for (String member : owner.permittedSubclasses) result += countRuntime(member);
        }
        for (FieldNode field : owner.fields) {
            result += countRuntime(field.desc) + countRuntime(field.signature);
            if (field.value instanceof Type) {
                result += countRuntime(((Type) field.value).getDescriptor());
            }
        }
        for (MethodNode method : owner.methods) {
            result += countRuntime(method.desc) + countRuntime(method.signature);
            for (String exception : method.exceptions) result += countRuntime(exception);
            for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
                 insn = insn.getNext()) {
                if (insn instanceof TypeInsnNode) {
                    result += countRuntime(((TypeInsnNode) insn).desc);
                } else if (insn instanceof MultiANewArrayInsnNode) {
                    result += countRuntime(((MultiANewArrayInsnNode) insn).desc);
                } else if (insn instanceof MethodInsnNode) {
                    result += countRuntime(((MethodInsnNode) insn).desc);
                } else if (insn instanceof FieldInsnNode) {
                    result += countRuntime(((FieldInsnNode) insn).desc);
                } else if (insn instanceof InvokeDynamicInsnNode) {
                    result += countRuntime(((InvokeDynamicInsnNode) insn).desc);
                } else if (insn instanceof LdcInsnNode
                        && ((LdcInsnNode) insn).cst instanceof Type) {
                    result += countRuntime(
                            ((Type) ((LdcInsnNode) insn).cst).getDescriptor());
                }
            }
        }
        return result;
    }

    private static int countRuntime(String value) {
        if (value == null) return 0;
        int result = 0;
        for (String runtime : RUNTIME_CLASSES) {
            if (value.contains(runtime)) result++;
        }
        return result;
    }

    private static int countRuntimeHandle(Handle handle) {
        if (handle == null) return 0;
        return countRuntime(handle.getOwner()) + countRuntime(handle.getDesc());
    }

    private static int countRuntimeConstant(Object value) {
        if (value instanceof Handle) return countRuntimeHandle((Handle) value);
        if (value instanceof Type) return countRuntime(((Type) value).getDescriptor());
        if (value instanceof ConstantDynamic) {
            ConstantDynamic dynamic = (ConstantDynamic) value;
            int result = countRuntime(dynamic.getDescriptor())
                    + countRuntimeHandle(dynamic.getBootstrapMethod());
            for (int index = 0; index < dynamic.getBootstrapMethodArgumentCount(); index++) {
                result += countRuntimeConstant(dynamic.getBootstrapMethodArgument(index));
            }
            return result;
        }
        return 0;
    }

    private static int countAscii(byte[] bytes, String text) {
        byte[] target = text.getBytes(StandardCharsets.US_ASCII);
        int count = 0;
        for (int offset = 0; offset <= bytes.length - target.length; offset++) {
            int index = 0;
            while (index < target.length && bytes[offset + index] == target[index]) index++;
            if (index == target.length) count++;
        }
        return count;
    }

    private static void appendResidueFailures(Summary summary, String phase,
                                              Residue residue) {
        if (residue.runtimeClassEntries != 0) {
            fail(summary, phase, "<archive>", "<classes>",
                    "runtime-class-entities", String.valueOf(residue.runtimeClassEntries));
        }
        if (residue.centralMethodReferences != 0) {
            fail(summary, phase, "<archive>", "<methods>",
                    "runtime-method-references",
                    String.valueOf(residue.centralMethodReferences));
        }
        if (residue.centralFieldReferences != 0) {
            fail(summary, phase, "<archive>", "<fields>",
                    "runtime-field-references",
                    String.valueOf(residue.centralFieldReferences));
        }
        if (residue.centralDescriptorReferences != 0) {
            fail(summary, phase, "<archive>", "<descriptors>",
                    "runtime-descriptor-references",
                    String.valueOf(residue.centralDescriptorReferences));
        }
        if (residue.centralHandleReferences != 0) {
            fail(summary, phase, "<archive>", "<handles>",
                    "runtime-handle-references",
                    String.valueOf(residue.centralHandleReferences));
        }
        if (residue.centralRawReferences != 0) {
            fail(summary, phase, "<archive>", "<constant-pool>",
                    "runtime-raw-references",
                    String.valueOf(residue.centralRawReferences));
        }
        if (residue.integerIndy != 0 || residue.sameOwnerBootstrapIndy != 0) {
            fail(summary, phase, "<archive>", "<invokedynamic>",
                    "zkm-indy-references", "integer=" + residue.integerIndy
                            + ";self-bootstrap=" + residue.sameOwnerBootstrapIndy);
        }
        if ("final-gate".equals(phase)
                && (residue.privateBootstrapMethods != 0
                || residue.mutableCallSiteCalls != 0)) {
            fail(summary, phase, "<archive>", "<bootstrap-support>",
                    "zkm-bootstrap-support", "methods="
                            + residue.privateBootstrapMethods + ";mutable-calls="
                            + residue.mutableCallSiteCalls);
        }
        for (String detail : residue.details) {
            summary.residueRows.add(phase + "\t" + detail);
        }
    }

    private static void copyResidue(Summary summary, Residue residue) {
        summary.outputClasses = residue.parsedClasses;
        summary.outputVerificationErrors = residue.parseErrors;
        summary.remainingRuntimeClasses = residue.runtimeClassEntries;
        summary.remainingRuntimeMethodReferences = residue.centralMethodReferences;
        summary.remainingRuntimeFieldReferences = residue.centralFieldReferences;
        summary.remainingRuntimeDescriptorReferences = residue.centralDescriptorReferences;
        summary.remainingRuntimeHandleReferences = residue.centralHandleReferences;
        summary.remainingRuntimeRawReferences = residue.centralRawReferences;
        summary.remainingIntegerIndy = residue.integerIndy;
        summary.remainingSelfBootstrapIndy = residue.sameOwnerBootstrapIndy;
        summary.remainingPrivateBootstrapMethods = residue.privateBootstrapMethods;
        summary.remainingMutableCallSiteCalls = residue.mutableCallSiteCalls;
    }

    private static void writeReports(Path input, Path output, Path reportDirectory,
                                     Summary summary) throws Exception {
        Files.createDirectories(reportDirectory);
        List<String> provenance = new ArrayList<>();
        provenance.add("class\tkey_hex\tcommitted_key_owners\tsource");
        provenance.addAll(summary.provenanceRows);
        Files.write(reportDirectory.resolve("key-provenance.tsv"), provenance,
                StandardCharsets.UTF_8);

        List<String> integers = new ArrayList<>();
        integers.add("class\tkey_hex\tsites\tresolved_arguments\tindexed_sites"
                + "\tdecrypted_sites\tstatus\treason");
        integers.addAll(summary.integerProofRows);
        Files.write(reportDirectory.resolve("integer-proofs.tsv"), integers,
                StandardCharsets.UTF_8);

        List<String> semanticEvidence = new ArrayList<>();
        semanticEvidence.add("class\tmethod\tdescriptor\tinstruction\traw_instruction"
                + "\tint_argument"
                + "\tlong_literal_hex\tkey_mask_hex\texpected_int\tselected_key_hex"
                + "\tstatus\tevidence");
        semanticEvidence.addAll(summary.semanticEvidenceAuditRows);
        Files.write(reportDirectory.resolve("semantic-evidence.tsv"),
                semanticEvidence, StandardCharsets.UTF_8);

        List<String> actions = new ArrayList<>();
        actions.add("class\tmethod\tinstruction\taction\tmember\tvalue\treason");
        actions.addAll(summary.actions);
        Files.write(reportDirectory.resolve("actions.tsv"), actions,
                StandardCharsets.UTF_8);

        List<String> failures = new ArrayList<>();
        failures.add("phase\tclass\tmember\tkind\tdetail");
        failures.addAll(summary.failures);
        Files.write(reportDirectory.resolve("failures.tsv"), failures,
                StandardCharsets.UTF_8);

        List<String> residue = new ArrayList<>();
        residue.add("phase\tclass\tkind\tdetail");
        residue.addAll(summary.residueRows);
        Files.write(reportDirectory.resolve("residue.tsv"), residue,
                StandardCharsets.UTF_8);

        List<String> audit = new ArrayList<>();
        audit.add("input=" + input.toAbsolutePath());
        audit.add("input_sha256=" + sha256(input));
        audit.add("output=" + output.toAbsolutePath());
        audit.add("pre_removal_authority=" + summary.authority);
        audit.add("semantic_evidence=" + summary.semanticEvidencePath);
        audit.add("proof_source=" + summary.proofSource);
        audit.add("parsed_classes=" + summary.parsedClasses);
        audit.add("proven_class_keys=" + summary.provenClassKeys);
        audit.add("key_bootstraps=" + summary.keyBootstraps);
        audit.add("key_bootstraps_removed=" + summary.keyBootstrapsRemoved);
        audit.add("key_fields_removed=" + summary.keyFieldsRemoved);
        audit.add("key_field_reads_inlined=" + summary.keyFieldReadsInlined);
        audit.add("integer_sites=" + summary.integerSites);
        audit.add("integer_sites_directized=" + summary.integerSitesDirectized);
        audit.add("semantic_evidence_rows=" + summary.semanticEvidenceRows);
        audit.add("semantic_evidence_owners=" + summary.semanticEvidenceOwners);
        audit.add("semantic_sites_directized=" + summary.semanticSitesDirectized);
        audit.add("helper_total_directized_sites="
                + summary.helperTotalDirectizedSites);
        audit.add("integer_helpers_removed=" + summary.integerHelpersRemoved);
        audit.add("integer_support_methods_removed="
                + summary.integerSupportMethodsRemoved);
        audit.add("runtime_classes_removed=" + summary.runtimeClassesRemoved);
        audit.add("bootstrap_families_removed=" + summary.bootstrapFamiliesRemoved);
        audit.add("bootstrap_methods_removed=" + summary.bootstrapMethodsRemoved);
        audit.add("bootstrap_fields_removed=" + summary.bootstrapFieldsRemoved);
        audit.add("changed_classes=" + summary.changedClasses);
        audit.add("key_stage_central_references="
                + summary.keyStageCentralReferences);
        audit.add("key_stage_integer_indy=" + summary.keyStageIntegerIndy);
        audit.add("remaining_runtime_classes=" + summary.remainingRuntimeClasses);
        audit.add("remaining_runtime_method_references="
                + summary.remainingRuntimeMethodReferences);
        audit.add("remaining_runtime_field_references="
                + summary.remainingRuntimeFieldReferences);
        audit.add("remaining_runtime_descriptor_references="
                + summary.remainingRuntimeDescriptorReferences);
        audit.add("remaining_runtime_handle_references="
                + summary.remainingRuntimeHandleReferences);
        audit.add("remaining_runtime_raw_references="
                + summary.remainingRuntimeRawReferences);
        audit.add("remaining_integer_indy=" + summary.remainingIntegerIndy);
        audit.add("remaining_self_bootstrap_indy="
                + summary.remainingSelfBootstrapIndy);
        audit.add("remaining_private_bootstrap_methods="
                + summary.remainingPrivateBootstrapMethods);
        audit.add("remaining_mutable_callsite_calls="
                + summary.remainingMutableCallSiteCalls);
        audit.add("output_classes=" + summary.outputClasses);
        audit.add("output_verification_errors="
                + summary.outputVerificationErrors);
        audit.add("failures=" + summary.failures.size());
        audit.add("output_committed=" + summary.outputCommitted);
        audit.add("output_sha256=" + summary.outputSha256);
        audit.add("input_classes_loaded=false");
        audit.add("input_classes_initialized=false");
        audit.add("gate=" + (summary.outputCommitted ? "PASS" : "FAIL"));
        Files.write(reportDirectory.resolve("audit.txt"), audit,
                StandardCharsets.UTF_8);
        Files.write(reportDirectory.resolve("gate.txt"),
                ((summary.outputCommitted ? "PASS" : "FAIL") + "\n")
                        .getBytes(StandardCharsets.UTF_8));
    }

    private static void fail(Summary summary, String phase, String owner,
                             String member, String kind, String detail) {
        summary.failures.add(tsv(phase, owner, member, kind, detail));
    }

    private static void validatePaths(Path input, Path output) throws IOException {
        Path normalizedInput = input.toAbsolutePath().normalize();
        Path normalizedOutput = output.toAbsolutePath().normalize();
        if (normalizedInput.equals(normalizedOutput)) {
            throw new IllegalArgumentException("output must not replace input");
        }
        if (!Files.isRegularFile(normalizedInput)) {
            throw new IllegalArgumentException("input is not a regular file: " + input);
        }
        if (normalizedOutput.getParent() != null) {
            Files.createDirectories(normalizedOutput.getParent());
        }
    }

    private static List<ArchiveEntry> readEntries(Path input) throws IOException {
        List<ArchiveEntry> result = new ArrayList<>();
        try (ZipInputStream in = new ZipInputStream(Files.newInputStream(input))) {
            ZipEntry entry;
            while ((entry = in.getNextEntry()) != null) {
                result.add(new ArchiveEntry(entry.getName(), entry.isDirectory(),
                        entry.isDirectory() ? new byte[0] : readAll(in)));
            }
        }
        return result;
    }

    private static ParsedArchive parse(List<ArchiveEntry> entries) {
        ParsedArchive result = new ParsedArchive();
        for (ArchiveEntry entry : entries) {
            if (entry.directory || !entry.name.endsWith(".class")) continue;
            ClassNode owner = new ClassNode(Opcodes.ASM9);
            new ClassReader(entry.bytes).accept(owner, 0);
            if (result.classes.put(owner.name, owner) != null) {
                throw new IllegalStateException("duplicate class owner: " + owner.name);
            }
            result.entryNames.put(owner.name, entry.name);
        }
        return result;
    }

    private static void writeArchive(List<ArchiveEntry> entries,
                                     Map<String, byte[]> replacements,
                                     Path output, Summary summary) throws IOException {
        try (ZipOutputStream out = new ZipOutputStream(Files.newOutputStream(output))) {
            for (ArchiveEntry entry : entries) {
                if (isSignature(entry.name)) continue;
                String owner = entry.name.endsWith(".class")
                        ? entry.name.substring(0, entry.name.length() - 6) : null;
                if (owner != null && RUNTIME_CLASSES.contains(owner)) continue;
                out.putNextEntry(new ZipEntry(entry.name));
                if (!entry.directory) {
                    byte[] bytes = owner == null ? entry.bytes
                            : replacements.containsKey(owner)
                            ? replacements.get(owner) : entry.bytes;
                    out.write(bytes);
                }
                out.closeEntry();
            }
        }
    }

    private static boolean isSignature(String name) {
        String upper = name.toUpperCase(Locale.ROOT);
        if (!upper.startsWith("META-INF/")) return false;
        return upper.endsWith(".SF") || upper.endsWith(".RSA")
                || upper.endsWith(".DSA") || upper.endsWith(".EC");
    }

    private static void atomicMove(Path source, Path output) throws IOException {
        try {
            Files.move(source, output, StandardCopyOption.ATOMIC_MOVE,
                    StandardCopyOption.REPLACE_EXISTING);
        } catch (AtomicMoveNotSupportedException ignored) {
            Files.move(source, output, StandardCopyOption.REPLACE_EXISTING);
        }
    }

    private static byte[] readAll(InputStream input) throws IOException {
        ByteArrayOutputStream output = new ByteArrayOutputStream();
        byte[] buffer = new byte[8192];
        int count;
        while ((count = input.read(buffer)) >= 0) output.write(buffer, 0, count);
        return output.toByteArray();
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
        if (insn instanceof LdcInsnNode
                && ((LdcInsnNode) insn).cst instanceof Integer) {
            return (Integer) ((LdcInsnNode) insn).cst;
        }
        return null;
    }

    private static Long longConstant(AbstractInsnNode insn) {
        if (insn == null) return null;
        if (insn.getOpcode() == Opcodes.LCONST_0) return 0L;
        if (insn.getOpcode() == Opcodes.LCONST_1) return 1L;
        if (insn instanceof LdcInsnNode
                && ((LdcInsnNode) insn).cst instanceof Long) {
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

    private static String tsv(Object... values) {
        StringBuilder result = new StringBuilder();
        for (Object value : values) {
            if (result.length() != 0) result.append('\t');
            result.append(String.valueOf(value).replace('\t', ' ')
                    .replace('\r', ' ').replace('\n', ' '));
        }
        return result.toString();
    }

    private static String hex(long value) {
        return String.format(Locale.ROOT, "%016X", value);
    }

    private static String shortReason(Throwable failure) {
        String text = failure.getClass().getSimpleName() + ":"
                + String.valueOf(failure.getMessage());
        text = text.replace('\t', ' ').replace('\r', ' ').replace('\n', ' ');
        return text.substring(0, Math.min(text.length(), 220));
    }

    private static String stackReason(Throwable failure) {
        StringBuilder result = new StringBuilder(shortReason(failure));
        StackTraceElement[] stack = failure.getStackTrace();
        for (int index = 0; index < Math.min(4, stack.length); index++) {
            result.append(" <- ").append(stack[index]);
        }
        return result.toString();
    }

    private static String sha256(Path path) throws Exception {
        MessageDigest digest = MessageDigest.getInstance("SHA-256");
        try (InputStream input = Files.newInputStream(path)) {
            byte[] buffer = new byte[8192];
            int count;
            while ((count = input.read(buffer)) >= 0) digest.update(buffer, 0, count);
        }
        StringBuilder result = new StringBuilder();
        for (byte value : digest.digest()) {
            result.append(String.format(Locale.ROOT, "%02X", value & 0xff));
        }
        return result.toString();
    }

    static final class Summary {
        int inputEntries;
        int parsedClasses;
        int provenClassKeys;
        int keyBootstraps;
        int keyBootstrapsRemoved;
        int keyFieldsRemoved;
        int keyFieldReadsInlined;
        int integerSites;
        int integerSitesDirectized;
        int semanticEvidenceRows;
        int semanticEvidenceOwners;
        int semanticSitesDirectized;
        int helperTotalDirectizedSites;
        int integerHelpersRemoved;
        int integerSupportMethodsRemoved;
        int runtimeClassesRemoved;
        int bootstrapFamiliesRemoved;
        int bootstrapMethodsRemoved;
        int bootstrapFieldsRemoved;
        int changedClasses;
        int keyStageCentralReferences;
        int keyStageIntegerIndy;
        int outputClasses;
        int outputVerificationErrors;
        int remainingRuntimeClasses;
        int remainingRuntimeMethodReferences;
        int remainingRuntimeFieldReferences;
        int remainingRuntimeDescriptorReferences;
        int remainingRuntimeHandleReferences;
        int remainingRuntimeRawReferences;
        int remainingIntegerIndy;
        int remainingSelfBootstrapIndy;
        int remainingPrivateBootstrapMethods;
        int remainingMutableCallSiteCalls;
        boolean outputCommitted;
        String proofSource = "";
        String authority = "";
        String semanticEvidencePath = "";
        String outputSha256 = "";
        final List<String> provenanceRows = new ArrayList<>();
        final List<String> integerProofRows = new ArrayList<>();
        final List<String> actions = new ArrayList<>();
        final List<String> failures = new ArrayList<>();
        final List<String> residueRows = new ArrayList<>();
        final List<String> semanticEvidenceAuditRows = new ArrayList<>();
    }

    private static final class ProofSet {
        final Map<String, Long> keys = new LinkedHashMap<>();
        final Map<String, Set<Long>> candidates = new LinkedHashMap<>();
        final Map<String, ClassNode> authorityClasses = new LinkedHashMap<>();
        final List<String> rows = new ArrayList<>();
        String authority = "";
        String semanticEvidence = "";

        void addCandidate(String owner, long value) {
            candidates.computeIfAbsent(owner, ignored -> new LinkedHashSet<Long>())
                    .add(value);
        }
    }

    private static final class KeyPlan {
        final ClassNode owner;
        final MethodNode method;
        final AbstractInsnNode start;
        final AbstractInsnNode transform;
        final FieldInsnNode fieldWrite;
        final long key;
        final int instruction;
        FieldNode field;
        final List<FieldInsnNode> fieldReads = new ArrayList<>();

        KeyPlan(ClassNode owner, MethodNode method, AbstractInsnNode start,
                AbstractInsnNode transform, FieldInsnNode fieldWrite, long key,
                int instruction) {
            this.owner = owner;
            this.method = method;
            this.start = start;
            this.transform = transform;
            this.fieldWrite = fieldWrite;
            this.key = key;
            this.instruction = instruction;
        }
    }

    private static final class IntegerPlan {
        final ClassNode owner;
        final List<IntegerSite> sites;
        final List<Integer> values;
        final boolean semanticEvidence;

        IntegerPlan(ClassNode owner, List<IntegerSite> sites, List<Integer> values,
                    boolean semanticEvidence) {
            this.owner = owner;
            this.sites = sites;
            this.values = values;
            this.semanticEvidence = semanticEvidence;
        }
    }

    private static final class ManualPlan {
        final Set<String> coveredOwners = new LinkedHashSet<>();
        final List<IntegerPlan> plans = new ArrayList<>();
    }

    private static final class SemanticOverride {
        final String owner;
        final String method;
        final String descriptor;
        final int instruction;
        final int intArgument;
        final long longLiteral;
        final long keyMask;
        final int expectedInt;
        final String evidence;
        final int line;

        SemanticOverride(String owner, String method, String descriptor,
                         int instruction, int intArgument, long longLiteral,
                         long keyMask, int expectedInt, String evidence, int line) {
            this.owner = owner;
            this.method = method;
            this.descriptor = descriptor;
            this.instruction = instruction;
            this.intArgument = intArgument;
            this.longLiteral = longLiteral;
            this.keyMask = keyMask;
            this.expectedInt = expectedInt;
            this.evidence = evidence;
            this.line = line;
        }

        String identity() {
            return owner + "\t" + method + "\t" + descriptor + "\t" + instruction;
        }
    }

    private static final class XorFingerprint {
        final List<Long> constants = new ArrayList<>();
        int keyReads;
        int xorOperations;
    }

    private static final class IntegerSite {
        final MethodNode method;
        final InvokeDynamicInsnNode node;
        final int instruction;

        IntegerSite(MethodNode method, InvokeDynamicInsnNode node, int instruction) {
            this.method = method;
            this.node = node;
            this.instruction = instruction;
        }
    }

    private static final class LiteralIntegerSpec {
        final long indexMask;
        final int indexXor;
        final String tableField;

        LiteralIntegerSpec(long indexMask, int indexXor, String tableField) {
            this.indexMask = indexMask;
            this.indexXor = indexXor;
            this.tableField = tableField;
        }
    }

    private static final class LiteralArguments {
        final int intValue;
        final long longValue;

        LiteralArguments(int intValue, long longValue) {
            this.intValue = intValue;
            this.longValue = longValue;
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

    private static final class ParsedArchive {
        final Map<String, ClassNode> classes = new LinkedHashMap<>();
        final Map<String, String> entryNames = new LinkedHashMap<>();
    }

    private static final class HierarchyClassWriter extends ClassWriter {
        private final Map<String, ClassNode> classes;

        HierarchyClassWriter(int flags, Map<String, ClassNode> classes) {
            super(flags);
            this.classes = classes;
        }

        @Override
        protected String getCommonSuperClass(String left, String right) {
            if (left.equals(right)) return left;
            if (left.startsWith("[") || right.startsWith("[")) {
                return commonArray(left, right);
            }
            if (isAssignable(left, right)) return left;
            if (isAssignable(right, left)) return right;
            Set<String> rightTypes = new LinkedHashSet<>(orderedSupertypes(right));
            for (String type : orderedSupertypes(left)) {
                if (rightTypes.contains(type)) return type;
            }
            return "java/lang/Object";
        }

        private String commonArray(String left, String right) {
            if (!left.startsWith("[") || !right.startsWith("[")) return "java/lang/Object";
            Type a = Type.getType(left);
            Type b = Type.getType(right);
            if (a.getDimensions() != b.getDimensions()) return "java/lang/Object";
            Type ea = a.getElementType();
            Type eb = b.getElementType();
            if (ea.getSort() != Type.OBJECT || eb.getSort() != Type.OBJECT) {
                return left.equals(right) ? left : "java/lang/Object";
            }
            String common = getCommonSuperClass(ea.getInternalName(), eb.getInternalName());
            StringBuilder descriptor = new StringBuilder();
            for (int index = 0; index < a.getDimensions(); index++) descriptor.append('[');
            return descriptor.append('L').append(common).append(';').toString();
        }

        private boolean isAssignable(String target, String source) {
            return "java/lang/Object".equals(target)
                    || orderedSupertypes(source).contains(target);
        }

        private List<String> orderedSupertypes(String type) {
            List<String> result = new ArrayList<>();
            Set<String> seen = new HashSet<>();
            ArrayDeque<String> queue = new ArrayDeque<>();
            queue.add(type);
            while (!queue.isEmpty()) {
                String current = queue.removeFirst();
                if (!seen.add(current)) continue;
                result.add(current);
                ClassNode node = classes.get(current);
                if (node != null) {
                    if (node.superName != null) queue.addLast(node.superName);
                    if (node.interfaces != null) queue.addAll(node.interfaces);
                } else if (!"java/lang/Object".equals(current)) {
                    queue.addLast("java/lang/Object");
                }
            }
            if (!seen.contains("java/lang/Object")) result.add("java/lang/Object");
            return result;
        }
    }

    private static final class ArchiveEntry {
        final String name;
        final boolean directory;
        final byte[] bytes;

        ArchiveEntry(String name, boolean directory, byte[] bytes) {
            this.name = name;
            this.directory = directory;
            this.bytes = bytes;
        }
    }

    private static final class Residue {
        int parsedClasses;
        int parseErrors;
        int runtimeClassEntries;
        int centralMethodReferences;
        int centralFieldReferences;
        int centralDescriptorReferences;
        int centralHandleReferences;
        int centralRawReferences;
        int integerIndy;
        int sameOwnerBootstrapIndy;
        int privateBootstrapMethods;
        int mutableCallSiteCalls;
        final List<String> details = new ArrayList<>();
    }
}
