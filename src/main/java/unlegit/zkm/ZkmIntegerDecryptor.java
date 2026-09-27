package unlegit.zkm;

import org.objectweb.asm.ClassReader;
import org.objectweb.asm.ClassWriter;
import org.objectweb.asm.Handle;
import org.objectweb.asm.Opcodes;
import org.objectweb.asm.tree.AbstractInsnNode;
import org.objectweb.asm.tree.ClassNode;
import org.objectweb.asm.tree.FieldInsnNode;
import org.objectweb.asm.tree.FieldNode;
import org.objectweb.asm.tree.InsnNode;
import org.objectweb.asm.tree.IntInsnNode;
import org.objectweb.asm.tree.InvokeDynamicInsnNode;
import org.objectweb.asm.tree.LdcInsnNode;
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
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.IdentityHashMap;
import java.util.LinkedHashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Set;
import java.util.zip.ZipEntry;
import java.util.zip.ZipInputStream;
import java.util.zip.ZipOutputStream;

/** Offline recovery and optional constant rewriting for ZKM {@code (IJ)I} sites. */
public final class ZkmIntegerDecryptor {
    private static final String INTEGER_DESC = "(IJ)I";
    private static final String BOOTSTRAP_DESC = "(Ljava/lang/invoke/MethodHandles$Lookup;"
            + "Ljava/lang/String;Ljava/lang/invoke/MethodType;)Ljava/lang/invoke/CallSite;";

    private ZkmIntegerDecryptor() {
    }

    public static void main(String[] args) throws Exception {
        if (args.length != 2 && args.length != 3) {
            System.err.println("usage: ZkmIntegerDecryptor <input.jar> <report-dir> [rewritten.jar]");
            System.exit(2);
        }
        recover(Paths.get(args[0]), Paths.get(args[1]),
                args.length == 3 ? Paths.get(args[2]) : null);
    }

    static RecoverySummary recover(Path input, Path reportDirectory) throws Exception {
        return recover(input, reportDirectory, null);
    }

    static RecoverySummary recover(Path input, Path reportDirectory, Path rewrittenOutput)
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

        Map<String, ClassNode> classes = ZkmLongKeyEvaluator.readClasses(input);
        Map<String, Long> validatedKeys = ZkmStringDecryptor.solveValidatedClassKeys(classes);
        Map<String, Long> isolatedKeys = ZkmLongKeyEvaluator.evaluateClassKeys(classes);
        Map<String, Long> sequentialKeys = ZkmLongKeyEvaluator.evaluateClassKeysSequential(classes);
        RecoverySummary summary = new RecoverySummary();
        summary.parsedClasses = classes.size();
        summary.validatedClassKeys = validatedKeys.size();

        List<String> siteRows = new ArrayList<>();
        List<String> tableRows = new ArrayList<>();
        List<String> rewriteRows = new ArrayList<>();
        siteRows.add("class\tmethod\tinstruction\tcall_int\tcall_long\ttable_index"
                + "\tvalue\tstatus");
        tableRows.add("class\tclass_key_hex\tkey_source\touter_mask_hex\touter_key_hex"
                + "\ttable_field\texpected_entries\tentries\tpacked_literals"
                + "\tresolved_sites\tdecrypted_sites\tstatus");
        rewriteRows.add("class\tmethod\tinstruction\tvalue\taction\treason");
        Map<String, byte[]> replacements = new LinkedHashMap<>();

        for (ClassNode owner : classes.values()) {
            List<IndySite> sites = integerIndySites(owner);
            summary.totalIntegerSites += sites.size();
            if (sites.isEmpty()) continue;
            summary.integerClasses++;

            MethodNode clinit = method(owner, "<clinit>", "()V");
            IntegerSpec spec = integerSpec(owner);
            KeyField keyShape = clinit == null ? null : keyField(owner, clinit, 0L);
            Long outerMask = keyShape == null ? null : outerMask(clinit, keyShape);
            Long inlinedOuterKey = keyShape == null && clinit != null
                    ? inlinedOuterKey(clinit) : null;
            boolean inlinedOuterKeyMode = keyShape == null && inlinedOuterKey != null;
            LongTableLayout layout = spec == null || clinit == null ? null
                    : longTableLayout(owner, clinit, spec.tableField);
            if (clinit == null || spec == null
                    || (!inlinedOuterKeyMode && (keyShape == null || outerMask == null))
                    || layout == null) {
                String reason = clinit == null ? "NO_CLINIT"
                        : spec == null ? "NO_INTEGER_SPEC"
                        : keyShape == null ? "NO_KEY_FIELD_OR_INLINED_OUTER_KEY"
                        : outerMask == null ? "NO_OUTER_KEY_MASK" : "NO_TABLE_LAYOUT";
                tableRows.add(tsv(owner.name, "", "", value(outerMask),
                        value(inlinedOuterKey),
                        spec == null ? "" : spec.tableField,
                        layout == null ? "" : layout.expectedEntries, "", "", 0, 0, reason));
                for (IndySite site : sites) siteRows.add(siteFailure(owner, site, reason));
                summary.tableFailures++;
                summary.unresolvedSites += sites.size();
                continue;
            }

            List<KeyCandidate> keyCandidates = classKeyCandidates(owner.name,
                    validatedKeys, isolatedKeys, sequentialKeys);
            CandidateResult best = null;
            boolean keyTie = false;
            Long validatedKey = validatedKeys.get(owner.name);
            boolean trustedKey = validatedKey != null;
            if (inlinedOuterKeyMode) {
                best = recoverCandidateWithOuterKey(owner, sites, null, inlinedOuterKey,
                        layout, spec, new KeyCandidate(0L, "inlined-outer-key"));
            } else {
                for (KeyCandidate keyCandidate : keyCandidates) {
                    CandidateResult candidate = recoverCandidate(owner, sites, keyShape, outerMask,
                            layout, spec, keyCandidate);
                    if (trustedKey && "validated-string-table".equals(keyCandidate.source)) {
                        best = candidate;
                        keyTie = false;
                        break;
                    }
                    int comparison = best == null ? 1 : candidate.compareTo(best);
                    if (comparison > 0) {
                        best = candidate;
                        keyTie = false;
                    } else if (equallyStrong(candidate, best) && best != null
                            && candidate.key.value != best.key.value
                            && candidate.decrypted > 0) {
                        keyTie = true;
                    }
                }
            }
            if (best == null || best.table == null || best.decrypted == 0
                    || (!trustedKey && (keyTie || !best.isStrong(sites.size())))) {
                String reason = best == null || best.table == null
                        ? "NO_VALID_LONG_TABLE" : keyTie
                        ? "AMBIGUOUS_CLASS_KEY" : inlinedOuterKeyMode
                        ? "UNVALIDATED_INLINED_OUTER_KEY" : "UNVALIDATED_CLASS_KEY";
                tableRows.add(tsv(owner.name,
                        best == null || inlinedOuterKeyMode ? "" : hex(best.key.value),
                        best == null ? "" : best.key.source, value(outerMask),
                        inlinedOuterKeyMode ? hex(inlinedOuterKey)
                                : best == null ? "" : hex(best.key.value ^ outerMask),
                        spec.tableField,
                        layout.expectedEntries, best == null || best.table == null ? ""
                                : best.table.entries.size(),
                        best == null || best.table == null ? ""
                                : best.table.literalInstructions.size(),
                        best == null ? 0 : best.resolved,
                        best == null ? 0 : best.decrypted, reason));
                if (best != null) {
                    appendSiteRows(siteRows, owner, best.results);
                } else {
                    for (IndySite site : sites) siteRows.add(siteFailure(owner, site, reason));
                }
                summary.tableFailures++;
                summary.unresolvedSites += sites.size() - (best == null ? 0 : best.decrypted);
                continue;
            }

            summary.tableClasses++;
            summary.resolvedArguments += best.resolved;
            summary.decryptedSites += best.decrypted;
            summary.unresolvedSites += sites.size() - best.decrypted;
            tableRows.add(tsv(owner.name, inlinedOuterKeyMode ? "" : hex(best.key.value),
                    best.key.source, value(outerMask),
                    inlinedOuterKeyMode ? hex(inlinedOuterKey)
                            : hex(best.key.value ^ outerMask), spec.tableField,
                    layout.expectedEntries, best.table.entries.size(),
                    best.table.literalInstructions.size(), best.resolved, best.decrypted, "OK"));
            appendSiteRows(siteRows, owner, best.results);

            if (rewrittenOutput != null) {
                RewriteResult rewrite = rewriteClass(owner, best.results);
                summary.rewritePlannedSites += rewrite.plannedSites;
                summary.rewriteAppliedSites += rewrite.appliedSites;
                summary.rewriteSkippedSites += rewrite.skippedSites;
                if (rewrite.rolledBack) summary.rewriteRollbackClasses++;
                if (rewrite.bytes != null) {
                    replacements.put(owner.name, rewrite.bytes);
                    summary.rewriteClasses++;
                    summary.rewriteMethods += rewrite.changedMethods;
                }
                for (RewriteRecord record : rewrite.records) {
                    rewriteRows.add(tsv(owner.name, record.method, record.instruction,
                            value(record.value), record.action, record.reason));
                }
            }
        }

        siteRows.subList(1, siteRows.size()).sort(Comparator.naturalOrder());
        tableRows.subList(1, tableRows.size()).sort(Comparator.naturalOrder());
        rewriteRows.subList(1, rewriteRows.size()).sort(Comparator.naturalOrder());
        Files.write(reportDirectory.resolve("sites.tsv"), siteRows, StandardCharsets.UTF_8);
        Files.write(reportDirectory.resolve("tables.tsv"), tableRows, StandardCharsets.UTF_8);
        if (rewrittenOutput != null) {
            Files.write(reportDirectory.resolve("rewrite.tsv"), rewriteRows, StandardCharsets.UTF_8);
            ArchiveWriteResult written = writeRewrittenArchive(input, rewrittenOutput, replacements);
            summary.archiveEntries = written.entries;
            summary.archiveResources = written.resources;
            summary.signaturesRemoved = written.signaturesRemoved;
            ArchiveVerification verification = verifyArchive(rewrittenOutput);
            summary.outputClasses = verification.classes;
            summary.outputVerificationErrors = verification.errors;
            summary.remainingIntegerSites = verification.integerSites;
        } else {
            summary.remainingIntegerSites = summary.totalIntegerSites;
        }

        List<String> audit = new ArrayList<>();
        audit.add("input=" + input.toAbsolutePath());
        audit.add("input_sha256=" + sha256(input));
        audit.add("parsed_classes=" + summary.parsedClasses);
        audit.add("validated_class_keys=" + summary.validatedClassKeys);
        audit.add("integer_classes=" + summary.integerClasses);
        audit.add("total_integer_sites=" + summary.totalIntegerSites);
        audit.add("table_classes=" + summary.tableClasses);
        audit.add("table_failures=" + summary.tableFailures);
        audit.add("resolved_arguments=" + summary.resolvedArguments);
        audit.add("decrypted_sites=" + summary.decryptedSites);
        audit.add("unresolved_sites=" + summary.unresolvedSites);
        audit.add("rewrite_requested=" + (rewrittenOutput != null));
        audit.add("rewrite_output=" + (rewrittenOutput == null ? ""
                : rewrittenOutput.toAbsolutePath()));
        audit.add("rewrite_classes=" + summary.rewriteClasses);
        audit.add("rewrite_methods=" + summary.rewriteMethods);
        audit.add("rewrite_planned_sites=" + summary.rewritePlannedSites);
        audit.add("rewrite_applied_sites=" + summary.rewriteAppliedSites);
        audit.add("rewrite_skipped_sites=" + summary.rewriteSkippedSites);
        audit.add("rewrite_rollback_classes=" + summary.rewriteRollbackClasses);
        audit.add("remaining_integer_sites=" + summary.remainingIntegerSites);
        audit.add("output_classes=" + summary.outputClasses);
        audit.add("output_verification_errors=" + summary.outputVerificationErrors);
        audit.add("archive_entries=" + summary.archiveEntries);
        audit.add("archive_resources=" + summary.archiveResources);
        audit.add("signatures_removed=" + summary.signaturesRemoved);
        audit.add("input_modified=false");
        audit.add("input_classes_loaded=false");
        boolean integrityPass = summary.rewriteRollbackClasses == 0
                && (rewrittenOutput == null || summary.outputVerificationErrors == 0
                && summary.rewriteAppliedSites == summary.rewritePlannedSites);
        boolean completeCoverage = summary.tableFailures == 0 && summary.unresolvedSites == 0
                && (rewrittenOutput == null || summary.remainingIntegerSites == 0);
        String coverageGate = completeCoverage ? "PASS"
                : summary.decryptedSites != 0 ? "PARTIAL" : "FAIL";
        String gate = integrityPass ? ("PASS".equals(coverageGate)
                ? "PASS" : "PASS_" + coverageGate) : "FAIL_INTEGRITY";
        audit.add("integrity_gate=" + (integrityPass ? "PASS" : "FAIL"));
        audit.add("coverage_gate=" + coverageGate);
        audit.add("coverage_reason=unresolved_sites=" + summary.unresolvedSites
                + ";table_failures=" + summary.tableFailures
                + ";remaining_integer_sites=" + summary.remainingIntegerSites);
        audit.add("gate=" + gate);
        Files.write(reportDirectory.resolve("audit.txt"), audit, StandardCharsets.UTF_8);
        Files.write(reportDirectory.resolve("integrity-gate.txt"),
                ((integrityPass ? "PASS" : "FAIL") + "\n").getBytes(StandardCharsets.UTF_8));
        Files.write(reportDirectory.resolve("coverage-gate.txt"),
                (coverageGate + "\n").getBytes(StandardCharsets.UTF_8));
        Files.write(reportDirectory.resolve("gate.txt"),
                (gate + "\n").getBytes(StandardCharsets.UTF_8));
        System.out.println("integer_sites=" + summary.totalIntegerSites + " decrypted="
                + summary.decryptedSites + " tables=" + summary.tableClasses + "/"
                + summary.integerClasses + " report=" + reportDirectory);
        return summary;
    }

    private static CandidateResult recoverCandidate(ClassNode owner, List<IndySite> sites,
                                                      KeyField keyShape, long outerMask,
                                                      LongTableLayout layout, IntegerSpec spec,
                                                      KeyCandidate keyCandidate) {
        KeyField keyField = new KeyField(keyShape.owner, keyShape.name, keyCandidate.value);
        return recoverCandidateWithOuterKey(owner, sites, keyField,
                keyCandidate.value ^ outerMask, layout, spec, keyCandidate);
    }

    private static CandidateResult recoverCandidateWithOuterKey(
            ClassNode owner, List<IndySite> sites, KeyField keyField, long outerKey,
            LongTableLayout layout, IntegerSpec spec, KeyCandidate keyCandidate) {
        CandidateResult result = new CandidateResult(keyCandidate);
        List<LongTableCandidate> tables = longTableCandidates(method(owner, "<clinit>", "()V"),
                outerKey, layout);
        if (tables.size() != 1) return result;
        result.table = tables.get(0);
        Map<MethodNode, Frame<SourceValue>[]> sourceFrames = new IdentityHashMap<>();
        Map<MethodNode, Boolean> sourceFailures = new IdentityHashMap<>();
        for (IndySite site : sites) {
            ArgumentExpressions arguments = resolveArguments(owner.name, site, keyField,
                    sourceFrames, sourceFailures);
            if (arguments == null) {
                result.results.add(SiteResult.failure(site, "UNRESOLVED_ARGUMENTS"));
                continue;
            }
            result.resolved++;
            int tableIndex = arguments.intArgument.value
                    ^ (int) (arguments.longArgument.value & spec.indexMask) ^ spec.indexXor;
            if (tableIndex < 0 || tableIndex >= result.table.entries.size()) {
                result.results.add(SiteResult.indexFailure(site, arguments, tableIndex));
                continue;
            }
            try {
                int value = decryptInteger(result.table.entries.get(tableIndex),
                        arguments.longArgument.value);
                result.decrypted++;
                if (isLikelyStructuralInteger(value)) result.structuralValues++;
                result.results.add(SiteResult.success(site, arguments, tableIndex, value));
            } catch (Exception failure) {
                result.results.add(SiteResult.decryptFailure(site, arguments, tableIndex));
            }
        }
        return result;
    }

    static int decryptInteger(long encrypted, long keyValue) throws Exception {
        byte[] plaintext = desNoPadding(ByteBuffer.allocate(8).putLong(encrypted).array(), keyValue,
                Cipher.DECRYPT_MODE);
        return ByteBuffer.wrap(plaintext).getInt(4);
    }

    /**
     * Proves a class key against every class-local {@code invokedynamic (IJ)I} site without
     * defining, initializing, or executing the input class.
     *
     * <p>The proof is deliberately all-or-nothing. The integer bootstrap, decryptor spec,
     * class-key field, outer key mask, and packed {@code long[]} table must each be unique;
     * every call-site argument must have a unique statically evaluable source; every derived
     * index must be in range; and both DES layers must complete for every site.</p>
     */
    public static IntegerProof proveClassKey(ClassNode owner, long classKey) {
        if (owner == null) throw new IllegalArgumentException("owner must not be null");
        ProofAccumulator proof = new ProofAccumulator(owner.name, classKey);
        List<IndySite> sites = integerDescriptorSites(owner);
        sites.sort(new Comparator<IndySite>() {
            @Override
            public int compare(IndySite left, IndySite right) {
                String leftSite = left.method.name + left.method.desc + "\t" + left.instruction;
                String rightSite = right.method.name + right.method.desc + "\t" + right.instruction;
                return leftSite.compareTo(rightSite);
            }
        });
        proof.sites = sites.size();
        if (sites.isEmpty()) return proof.fail("NO_INTEGER_SITES", "integer-sites=0");

        Set<Handle> bootstraps = new LinkedHashSet<>();
        int standardSites = 0;
        for (IndySite site : sites) {
            if (isStandardIntegerIndy(owner, site.node)) standardSites++;
            if (site.node.bsm != null) bootstraps.add(site.node.bsm);
        }
        proof.bootstrapCount = bootstraps.size();
        if (standardSites != sites.size()) {
            return proof.fail("NONSTANDARD_INTEGER_SITE",
                    "standard-sites=" + standardSites + "/" + sites.size());
        }
        if (bootstraps.size() != 1) {
            return proof.fail("INTEGER_BOOTSTRAP_NOT_UNIQUE",
                    "bootstrap-handles=" + bootstraps.size());
        }
        Handle bootstrap = bootstraps.iterator().next();
        proof.bootstrapMethodCount = bootstrapMethodCount(owner, bootstrap);
        if (proof.bootstrapMethodCount != 1) {
            return proof.fail("INTEGER_BOOTSTRAP_METHOD_NOT_UNIQUE",
                    "bootstrap-methods=" + proof.bootstrapMethodCount);
        }

        List<IntegerSpec> specs = integerSpecs(owner);
        proof.specCount = specs.size();
        if (specs.size() != 1) {
            return proof.fail("INTEGER_SPEC_NOT_UNIQUE", "integer-specs=" + specs.size());
        }
        IntegerSpec spec = specs.get(0);

        List<MethodNode> clinits = methods(owner, "<clinit>", "()V");
        proof.clinitCount = clinits.size();
        if (clinits.size() != 1) {
            return proof.fail("CLINIT_NOT_UNIQUE", "clinits=" + clinits.size());
        }
        MethodNode clinit = clinits.get(0);

        List<KeyField> keyFields = keyFields(owner, clinit, classKey);
        proof.keyFieldCount = keyFields.size();
        if (keyFields.size() != 1) {
            return proof.fail("KEY_FIELD_NOT_UNIQUE", "key-fields=" + keyFields.size());
        }
        KeyField keyField = keyFields.get(0);

        List<Long> masks = outerMasks(clinit, keyField);
        proof.outerMaskCount = masks.size();
        if (masks.size() != 1) {
            return proof.fail("OUTER_MASK_NOT_UNIQUE", "outer-masks=" + masks.size());
        }

        List<LongTableLayout> layouts = longTableLayouts(owner, clinit, spec.tableField);
        proof.tableLayoutCount = layouts.size();
        if (layouts.size() != 1) {
            return proof.fail("LONG_TABLE_LAYOUT_NOT_UNIQUE",
                    "table-layouts=" + layouts.size());
        }
        List<LongTableCandidate> tables = longTableCandidates(clinit,
                classKey ^ masks.get(0), layouts.get(0));
        proof.tableCount = tables.size();
        if (tables.size() != 1) {
            return proof.fail("LONG_TABLE_NOT_UNIQUE", "long-tables=" + tables.size());
        }
        LongTableCandidate table = tables.get(0);
        proof.tableEntries = table.entries.size();

        int unresolvedArguments = 0;
        int outOfRange = 0;
        int desFailures = 0;
        Map<MethodNode, Frame<SourceValue>[]> sourceFrames = new IdentityHashMap<>();
        Map<MethodNode, Boolean> sourceFailures = new IdentityHashMap<>();
        for (IndySite site : sites) {
            ArgumentExpressions arguments = resolveArguments(owner.name, site, keyField,
                    sourceFrames, sourceFailures);
            if (arguments == null) {
                unresolvedArguments++;
                continue;
            }
            proof.resolvedArguments++;
            int tableIndex = arguments.intArgument.value
                    ^ (int) (arguments.longArgument.value & spec.indexMask) ^ spec.indexXor;
            if (tableIndex < 0 || tableIndex >= table.entries.size()) {
                outOfRange++;
                continue;
            }
            proof.indexedSites++;
            try {
                proof.values.add(decryptInteger(table.entries.get(tableIndex),
                        arguments.longArgument.value));
                proof.decryptedSites++;
            } catch (Exception failure) {
                desFailures++;
            }
        }
        if (unresolvedArguments != 0) {
            return proof.fail("UNRESOLVED_ARGUMENTS",
                    "unresolved-arguments=" + unresolvedArguments + "/" + sites.size());
        }
        if (outOfRange != 0) {
            return proof.fail("INDEX_OUT_OF_RANGE",
                    "out-of-range=" + outOfRange + "/" + sites.size());
        }
        if (desFailures != 0) {
            return proof.fail("INNER_DES_FAILED",
                    "inner-des-failures=" + desFailures + "/" + sites.size());
        }
        return proof.pass();
    }

    private static int bootstrapMethodCount(ClassNode owner, Handle bootstrap) {
        int result = 0;
        for (MethodNode method : owner.methods) {
            if (bootstrap.getName().equals(method.name)
                    && bootstrap.getDesc().equals(method.desc)
                    && (method.access & Opcodes.ACC_STATIC) != 0) result++;
        }
        return result;
    }

    private static boolean isLikelyStructuralInteger(int value) {
        return value >= -0x100000 && value <= 0x100000;
    }

    private static boolean equallyStrong(CandidateResult left, CandidateResult right) {
        return right != null && left.decrypted == right.decrypted
                && left.resolved == right.resolved
                && left.structuralValues == right.structuralValues;
    }

    private static List<KeyCandidate> classKeyCandidates(String owner,
                                                          Map<String, Long> validated,
                                                          Map<String, Long> isolated,
                                                          Map<String, Long> sequential) {
        List<KeyCandidate> result = new ArrayList<>();
        addKeyCandidate(result, validated.get(owner), "validated-string-table");
        addKeyCandidate(result, isolated.get(owner), "isolated-long-key");
        addKeyCandidate(result, sequential.get(owner), "sequential-long-key");
        return result;
    }

    private static void addKeyCandidate(List<KeyCandidate> candidates, Long value, String source) {
        if (value == null) return;
        for (KeyCandidate candidate : candidates) if (candidate.value == value) return;
        candidates.add(new KeyCandidate(value, source));
    }

    private static void appendSiteRows(List<String> rows, ClassNode owner,
                                       List<SiteResult> results) {
        for (SiteResult result : results) {
            rows.add(tsv(owner.name, result.site.method.name + result.site.method.desc,
                    result.site.instruction, value(result.callInt), value(result.callLong),
                    value(result.tableIndex), value(result.value), result.status));
        }
    }

    private static String siteFailure(ClassNode owner, IndySite site, String status) {
        return tsv(owner.name, site.method.name + site.method.desc, site.instruction,
                "", "", "", "", status);
    }

    private static IntegerSpec integerSpec(ClassNode owner) {
        List<IntegerSpec> specs = integerSpecs(owner);
        return specs.size() == 1 ? specs.get(0) : null;
    }

    private static List<IntegerSpec> integerSpecs(ClassNode owner) {
        List<IntegerSpec> result = new ArrayList<>();
        for (MethodNode method : owner.methods) {
            if ((method.access & Opcodes.ACC_STATIC) == 0 || !INTEGER_DESC.equals(method.desc)) {
                continue;
            }
            Long mask = null;
            Integer xor = null;
            String tableField = null;
            boolean cipher = false;
            boolean extractsLowInt = false;
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
                    if (field.getOpcode() == Opcodes.GETSTATIC && owner.name.equals(field.owner)
                            && "[J".equals(field.desc)) {
                        AbstractInsnNode cursor = nextCode(insn);
                        boolean indexedLoad = false;
                        for (int scanned = 0; cursor != null && scanned < 5;
                             scanned++, cursor = nextCode(cursor)) {
                            if (cursor.getOpcode() == Opcodes.LALOAD) {
                                indexedLoad = true;
                                break;
                            }
                        }
                        if (!indexedLoad) continue;
                        tableField = field.name;
                    }
                } else if (insn instanceof MethodInsnNode) {
                    MethodInsnNode call = (MethodInsnNode) insn;
                    if ("javax/crypto/Cipher".equals(call.owner) && "doFinal".equals(call.name)) {
                        cipher = true;
                    }
                }
                if (insn.getOpcode() == Opcodes.BALOAD) {
                    Integer index = intConstant(previousCode(insn));
                    if (index != null && index == 7) extractsLowInt = true;
                }
            }
            if (mask != null && xor != null && tableField != null && cipher && extractsLowInt) {
                result.add(new IntegerSpec(method, mask, xor, tableField));
            }
        }
        return result;
    }

    static LongTableLayout longTableLayout(ClassNode owner, MethodNode clinit, String tableField) {
        List<LongTableLayout> layouts = longTableLayouts(owner, clinit, tableField);
        return layouts.size() == 1 ? layouts.get(0) : null;
    }

    private static List<LongTableLayout> longTableLayouts(ClassNode owner, MethodNode clinit,
                                                           String tableField) {
        List<LongTableLayout> result = new ArrayList<>();
        for (AbstractInsnNode insn = clinit.instructions.getFirst(); insn != null;
             insn = insn.getNext()) {
            if (!(insn instanceof FieldInsnNode)) continue;
            FieldInsnNode field = (FieldInsnNode) insn;
            if (field.getOpcode() != Opcodes.PUTSTATIC || !owner.name.equals(field.owner)
                    || !tableField.equals(field.name) || !"[J".equals(field.desc)) continue;
            AbstractInsnNode value = previousCode(field);
            LongTableLayout candidate = null;
            if (value != null && value.getOpcode() == Opcodes.NEWARRAY
                    && value instanceof IntInsnNode
                    && ((IntInsnNode) value).operand == Opcodes.T_LONG) {
                Integer size = intConstant(previousCode(value));
                if (size != null && size > 0) {
                        candidate = new LongTableLayout(value.getNext(), field, size);
                }
            }
            if (candidate == null && value instanceof VarInsnNode
                    && value.getOpcode() == Opcodes.ALOAD) {
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
                    if (array != null && array.getOpcode() == Opcodes.NEWARRAY
                            && array instanceof IntInsnNode
                            && ((IntInsnNode) array).operand == Opcodes.T_LONG) {
                        Integer size = intConstant(previousCode(array));
                        if (size != null && size > 0) {
                            candidate = new LongTableLayout(definition.getNext(), field, size);
                        }
                    }
                }
            }
            if (candidate == null) return Collections.emptyList();
            result.add(candidate);
        }
        return result;
    }

    static List<LongTableCandidate> longTableCandidates(MethodNode clinit, long outerKey,
                                                         LongTableLayout layout) {
        List<LongTableCandidate> result = new ArrayList<>();
        if (clinit == null || layout == null) return result;
        LongTableCandidate candidate = new LongTableCandidate();
        boolean active = false;
        int instruction = 0;
        try {
            for (AbstractInsnNode insn = clinit.instructions.getFirst(); insn != null;
                 insn = insn.getNext(), instruction++) {
                if (insn == layout.scanStart) {
                    active = true;
                }
                if (insn == layout.tableStore) break;
                if (!active || !(insn instanceof LdcInsnNode)
                        || !(((LdcInsnNode) insn).cst instanceof String)) continue;
                String packed = (String) ((LdcInsnNode) insn).cst;
                if (packed.length() < 8 || (packed.length() & 7) != 0 || !isLatin1(packed)) {
                    continue;
                }
                candidate.literalInstructions.add(instruction);
                for (int offset = 0; offset < packed.length(); offset += 8) {
                    byte[] encrypted = new byte[8];
                    for (int i = 0; i < 8; i++) encrypted[i] = (byte) packed.charAt(offset + i);
                    byte[] plaintext = desNoPadding(encrypted, outerKey, Cipher.DECRYPT_MODE);
                    candidate.entries.add(ByteBuffer.wrap(plaintext).getLong());
                }
            }
        } catch (Exception failure) {
            return result;
        }
        if (candidate.entries.size() == layout.expectedEntries) result.add(candidate);
        return result;
    }

    private static byte[] desNoPadding(byte[] input, long keyValue, int mode) throws Exception {
        Cipher cipher = Cipher.getInstance("DES/CBC/NoPadding");
        SecretKeyFactory factory = SecretKeyFactory.getInstance("DES");
        SecretKey key = factory.generateSecret(
                new DESKeySpec(ByteBuffer.allocate(8).putLong(keyValue).array()));
        cipher.init(mode, (Key) key, new IvParameterSpec(new byte[8]));
        return cipher.doFinal(input);
    }

    private static List<IndySite> integerIndySites(ClassNode owner) {
        List<IndySite> result = new ArrayList<>();
        for (IndySite site : integerDescriptorSites(owner)) {
            if (isStandardIntegerIndy(owner, site.node)) result.add(site);
        }
        return result;
    }

    private static List<IndySite> integerDescriptorSites(ClassNode owner) {
        List<IndySite> result = new ArrayList<>();
        for (MethodNode method : owner.methods) {
            int instruction = 0;
            for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
                 insn = insn.getNext(), instruction++) {
                if (!(insn instanceof InvokeDynamicInsnNode)) continue;
                InvokeDynamicInsnNode indy = (InvokeDynamicInsnNode) insn;
                if (INTEGER_DESC.equals(indy.desc)) {
                    result.add(new IndySite(method, indy, instruction));
                }
            }
        }
        return result;
    }

    private static boolean isStandardIntegerIndy(ClassNode owner, InvokeDynamicInsnNode indy) {
        Handle bootstrap = indy.bsm;
        return INTEGER_DESC.equals(indy.desc) && bootstrap != null
                && bootstrap.getTag() == Opcodes.H_INVOKESTATIC
                && owner.name.equals(bootstrap.getOwner())
                && BOOTSTRAP_DESC.equals(bootstrap.getDesc());
    }

    private static ArgumentExpressions resolveArguments(
            String owner, IndySite site, KeyField keyField,
            Map<MethodNode, Frame<SourceValue>[]> sourceFrames,
            Map<MethodNode, Boolean> sourceFailures) {
        if (!Boolean.TRUE.equals(sourceFailures.get(site.method))) {
            Frame<SourceValue>[] frames = sourceFrames.get(site.method);
            if (frames == null) {
                try {
                    frames = new Analyzer<>(new SourceInterpreter()).analyze(owner, site.method);
                    sourceFrames.put(site.method, frames);
                } catch (Exception failure) {
                    sourceFailures.put(site.method, true);
                }
            }
            if (frames != null) {
                int index = site.method.instructions.indexOf(site.node);
                if (index >= 0 && index < frames.length) {
                    AbstractInsnNode[] producers = uniqueArgumentProducers(frames[index]);
                    if (producers != null) {
                        IntExpression intArgument = evalInt(producers[0], site.method, keyField);
                        LongExpression longArgument = evalLong(producers[1], site.method, keyField);
                        if (intArgument != null && longArgument != null) {
                            return new ArgumentExpressions(intArgument, longArgument);
                        }
                    }
                }
            }
        }
        LongExpression longArgument = evalLong(previousCode(site.node), site.method, keyField);
        IntExpression intArgument = longArgument == null ? null
                : evalInt(previousCode(longArgument.start), site.method, keyField);
        return intArgument == null || longArgument == null ? null
                : new ArgumentExpressions(intArgument, longArgument);
    }

    static AbstractInsnNode[] uniqueArgumentProducers(String owner, MethodNode method,
                                                       InvokeDynamicInsnNode indy)
            throws Exception {
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
        return new AbstractInsnNode[]{intSource.insns.iterator().next(),
                longSource.insns.iterator().next()};
    }

    private static KeyField keyField(ClassNode owner, MethodNode clinit, long value) {
        List<KeyField> fields = keyFields(owner, clinit, value);
        return fields.size() == 1 ? fields.get(0) : null;
    }

    private static List<KeyField> keyFields(ClassNode owner, MethodNode clinit, long value) {
        List<KeyField> result = new ArrayList<>();
        for (AbstractInsnNode insn = clinit.instructions.getFirst(); insn != null;
             insn = insn.getNext()) {
            if (!(insn instanceof FieldInsnNode)) continue;
            FieldInsnNode field = (FieldInsnNode) insn;
            if (field.getOpcode() != Opcodes.PUTSTATIC || !owner.name.equals(field.owner)
                    || !"J".equals(field.desc)) continue;
            AbstractInsnNode previous = previousCode(field);
            if (previous instanceof MethodInsnNode) {
                MethodInsnNode call = (MethodInsnNode) previous;
                if (call.getOpcode() == Opcodes.INVOKEINTERFACE && "(J)J".equals(call.desc)) {
                    result.add(new KeyField(owner.name, field.name, value));
                }
            }
        }
        return result;
    }

    private static Long outerMask(MethodNode clinit, KeyField keyField) {
        List<Long> masks = outerMasks(clinit, keyField);
        return masks.size() == 1 ? masks.get(0) : null;
    }

    private static List<Long> outerMasks(MethodNode clinit, KeyField keyField) {
        Set<Long> result = new LinkedHashSet<>();
        for (AbstractInsnNode insn = clinit.instructions.getFirst(); insn != null;
             insn = insn.getNext()) {
            if (insn.getOpcode() != Opcodes.LXOR) continue;
            AbstractInsnNode right = previousCode(insn);
            AbstractInsnNode left = previousCode(right);
            Long constant = longConstant(right);
            if (constant != null && isKeyField(left, keyField)) result.add(constant);
            constant = longConstant(left);
            if (constant != null && isKeyField(right, keyField)) result.add(constant);
        }
        return new ArrayList<>(result);
    }

    /** Finds the unique DES table key after the long-key pass has inlined it. */
    private static Long inlinedOuterKey(MethodNode clinit) {
        int constructors = 0;
        Map<Long, Integer> prefixConstants = new LinkedHashMap<>();
        Map<Long, Integer> selectedConstants = null;
        for (AbstractInsnNode insn = clinit.instructions.getFirst(); insn != null;
             insn = insn.getNext()) {
            Long constant = longConstant(insn);
            if (constant != null) {
                prefixConstants.put(constant,
                        prefixConstants.containsKey(constant)
                                ? prefixConstants.get(constant) + 1 : 1);
            }
            if (!(insn instanceof MethodInsnNode)) continue;
            MethodInsnNode call = (MethodInsnNode) insn;
            if (call.getOpcode() == Opcodes.INVOKESPECIAL
                    && "javax/crypto/spec/DESKeySpec".equals(call.owner)
                    && "<init>".equals(call.name) && "([B)V".equals(call.desc)) {
                constructors++;
                selectedConstants = new LinkedHashMap<>(prefixConstants);
            }
        }
        if (constructors != 1 || selectedConstants == null
                || selectedConstants.size() != 1) return null;
        Map.Entry<Long, Integer> selected = selectedConstants.entrySet().iterator().next();
        return selected.getValue() >= 2 ? selected.getKey() : null;
    }

    private static boolean isKeyField(AbstractInsnNode insn, KeyField keyField) {
        if (keyField == null || !(insn instanceof FieldInsnNode)) return false;
        FieldInsnNode field = (FieldInsnNode) insn;
        return field.getOpcode() == Opcodes.GETSTATIC && keyField.owner.equals(field.owner)
                && keyField.name.equals(field.name) && "J".equals(field.desc);
    }

    private static LongExpression evalLong(AbstractInsnNode end, MethodNode method,
                                           KeyField keyField) {
        if (end == null) return null;
        Long constant = longConstant(end);
        if (constant != null) return new LongExpression(constant, end);
        if (isKeyField(end, keyField)) return new LongExpression(keyField.value, end);
        if (end instanceof VarInsnNode && end.getOpcode() == Opcodes.LLOAD) {
            AbstractInsnNode store = findStore(end, ((VarInsnNode) end).var, Opcodes.LSTORE);
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
            long value = opcode == Opcodes.LXOR ? left.value ^ right.value
                    : opcode == Opcodes.LAND ? left.value & right.value
                    : opcode == Opcodes.LOR ? left.value | right.value
                    : opcode == Opcodes.LADD ? left.value + right.value
                    : left.value - right.value;
            return new LongExpression(value, left.start);
        }
        if (opcode == Opcodes.LNEG) {
            LongExpression value = evalLong(previousCode(end), method, keyField);
            return value == null ? null : new LongExpression(-value.value, value.start);
        }
        return null;
    }

    private static IntExpression evalInt(AbstractInsnNode end, MethodNode method,
                                         KeyField keyField) {
        if (end == null) return null;
        Integer constant = intConstant(end);
        if (constant != null) return new IntExpression(constant, end);
        if (end instanceof VarInsnNode && end.getOpcode() == Opcodes.ILOAD) {
            AbstractInsnNode store = findStore(end, ((VarInsnNode) end).var, Opcodes.ISTORE);
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
            int value = opcode == Opcodes.IXOR ? left.value ^ right.value
                    : opcode == Opcodes.IAND ? left.value & right.value
                    : opcode == Opcodes.IOR ? left.value | right.value
                    : opcode == Opcodes.IADD ? left.value + right.value
                    : left.value - right.value;
            return new IntExpression(value, left.start);
        }
        if (opcode == Opcodes.L2I) {
            LongExpression value = evalLong(previousCode(end), method, keyField);
            return value == null ? null : new IntExpression((int) value.value, value.start);
        }
        return null;
    }

    private static AbstractInsnNode findStore(AbstractInsnNode load, int local, int opcode) {
        for (AbstractInsnNode cursor = load.getPrevious(); cursor != null;
             cursor = cursor.getPrevious()) {
            if (cursor instanceof VarInsnNode && cursor.getOpcode() == opcode
                    && ((VarInsnNode) cursor).var == local) return cursor;
        }
        return null;
    }

    private static RewriteResult rewriteClass(ClassNode owner, List<SiteResult> results) {
        RewriteResult rewrite = new RewriteResult();
            Map<MethodNode, Boolean> changedMethods = new IdentityHashMap<>();
        for (SiteResult result : results) {
            String method = result.site.method.name + result.site.method.desc;
            if (!"OK".equals(result.status) || result.value == null) {
                rewrite.skippedSites++;
                rewrite.records.add(new RewriteRecord(method, result.site.instruction,
                        result.value, "skip", "recovery_status=" + result.status));
                continue;
            }
            rewrite.plannedSites++;
            if (!isStandardIntegerIndy(owner, result.site.node)
                    || !rewriteSiteToLdc(result.site.method, result.site.node, result.value)) {
                rewrite.skippedSites++;
                rewrite.records.add(new RewriteRecord(method, result.site.instruction,
                        result.value, "skip", "bootstrap_or_site_mismatch"));
                continue;
            }
            changedMethods.put(result.site.method, true);
            rewrite.records.add(new RewriteRecord(method, result.site.instruction,
                    result.value, "rewrite", "proven_table+arguments+inner_des"));
        }
        if (changedMethods.isEmpty()) return rewrite;
        try {
            ClassWriter writer = new ClassWriter(0);
            owner.accept(writer);
            byte[] candidate = writer.toByteArray();
            verifyClass(candidate);
            rewrite.bytes = candidate;
            rewrite.changedMethods = changedMethods.size();
            for (RewriteRecord record : rewrite.records) {
                if ("rewrite".equals(record.action)) rewrite.appliedSites++;
            }
        } catch (Throwable failure) {
            rewrite.rolledBack = true;
            String reason = "class_verification=" + shortReason(failure);
            for (RewriteRecord record : rewrite.records) {
                if (!"rewrite".equals(record.action)) continue;
                record.action = "rollback";
                record.reason = reason;
                rewrite.skippedSites++;
            }
        }
        return rewrite;
    }

    static boolean rewriteSiteToLdc(MethodNode method, InvokeDynamicInsnNode indy, int value) {
        if (method.instructions.indexOf(indy) < 0 || !INTEGER_DESC.equals(indy.desc)) return false;
        method.instructions.insertBefore(indy, new InsnNode(Opcodes.POP2));
        method.instructions.insertBefore(indy, new InsnNode(Opcodes.POP));
        method.instructions.set(indy, pushInteger(value));
        return true;
    }

    private static AbstractInsnNode pushInteger(int value) {
        if (value >= -1 && value <= 5) return new InsnNode(Opcodes.ICONST_0 + value);
        if (value >= Byte.MIN_VALUE && value <= Byte.MAX_VALUE) {
            return new IntInsnNode(Opcodes.BIPUSH, value);
        }
        if (value >= Short.MIN_VALUE && value <= Short.MAX_VALUE) {
            return new IntInsnNode(Opcodes.SIPUSH, value);
        }
        return new LdcInsnNode(value);
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

    private static ArchiveWriteResult writeRewrittenArchive(Path input, Path output,
                                                              Map<String, byte[]> replacements)
            throws IOException {
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
                    ClassNode owner = new ClassNode(Opcodes.ASM9);
                    new ClassReader(bytes).accept(owner, 0);
                    verifyClass(bytes);
                    result.integerSites += integerIndySites(owner).size();
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

    private static String sha256(Path input) throws IOException {
        final MessageDigest digest;
        try {
            digest = MessageDigest.getInstance("SHA-256");
        } catch (NoSuchAlgorithmException failure) {
            throw new IOException("SHA-256 unavailable", failure);
        }
        digest.update(Files.readAllBytes(input));
        StringBuilder result = new StringBuilder(64);
        for (byte value : digest.digest()) {
            result.append(String.format(Locale.ROOT, "%02X", value & 0xff));
        }
        return result.toString();
    }

    private static boolean isSignatureEntry(String name) {
        String upper = name.replace('\\', '/').toUpperCase(Locale.ROOT);
        if (!upper.startsWith("META-INF/")) return false;
        String leaf = upper.substring("META-INF/".length());
        return leaf.startsWith("SIG-") || leaf.endsWith(".SF") || leaf.endsWith(".RSA")
                || leaf.endsWith(".DSA") || leaf.endsWith(".EC");
    }

    private static boolean isLatin1(String value) {
        for (int i = 0; i < value.length(); i++) if (value.charAt(i) > 0xff) return false;
        return true;
    }

    private static MethodNode method(ClassNode owner, String name, String descriptor) {
        if (owner == null) return null;
        for (MethodNode method : owner.methods) {
            if (name.equals(method.name) && descriptor.equals(method.desc)) return method;
        }
        return null;
    }

    private static List<MethodNode> methods(ClassNode owner, String name, String descriptor) {
        List<MethodNode> result = new ArrayList<>();
        if (owner == null) return result;
        for (MethodNode method : owner.methods) {
            if (name.equals(method.name) && descriptor.equals(method.desc)) result.add(method);
        }
        return result;
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

    private static String value(Object value) {
        return value == null ? "" : String.valueOf(value);
    }

    private static String hex(long value) {
        return String.format(Locale.ROOT, "%016X", value);
    }

    private static String tsv(Object... values) {
        StringBuilder row = new StringBuilder();
        for (int i = 0; i < values.length; i++) {
            if (i != 0) row.append('\t');
            if (values[i] != null) row.append(values[i]);
        }
        return row.toString();
    }

    private static String shortReason(Throwable failure) {
        String text = failure.getClass().getSimpleName() + ":" + String.valueOf(failure.getMessage());
        text = text.replace('\t', ' ').replace('\r', ' ').replace('\n', ' ');
        return text.substring(0, Math.min(160, text.length()));
    }

    /** Immutable result of the offline integer-table class-key proof. */
    public static final class IntegerProof {
        public final String owner;
        public final long classKey;
        public final int bootstrapCount;
        public final int bootstrapMethodCount;
        public final int specCount;
        public final int clinitCount;
        public final int keyFieldCount;
        public final int outerMaskCount;
        public final int tableLayoutCount;
        public final int tableCount;
        public final int tableEntries;
        public final int sites;
        public final int resolvedArguments;
        public final int indexedSites;
        public final int decryptedSites;
        public final List<Integer> values;
        public final String status;
        public final String reason;

        private IntegerProof(ProofAccumulator proof, String status, String reason) {
            this.owner = proof.owner;
            this.classKey = proof.classKey;
            this.bootstrapCount = proof.bootstrapCount;
            this.bootstrapMethodCount = proof.bootstrapMethodCount;
            this.specCount = proof.specCount;
            this.clinitCount = proof.clinitCount;
            this.keyFieldCount = proof.keyFieldCount;
            this.outerMaskCount = proof.outerMaskCount;
            this.tableLayoutCount = proof.tableLayoutCount;
            this.tableCount = proof.tableCount;
            this.tableEntries = proof.tableEntries;
            this.sites = proof.sites;
            this.resolvedArguments = proof.resolvedArguments;
            this.indexedSites = proof.indexedSites;
            this.decryptedSites = proof.decryptedSites;
            this.values = Collections.unmodifiableList(new ArrayList<>(proof.values));
            this.status = status;
            this.reason = reason;
        }

        public boolean passes() {
            return "PASS".equals(status);
        }
    }

    private static final class ProofAccumulator {
        final String owner;
        final long classKey;
        final List<Integer> values = new ArrayList<>();
        int bootstrapCount;
        int bootstrapMethodCount;
        int specCount;
        int clinitCount;
        int keyFieldCount;
        int outerMaskCount;
        int tableLayoutCount;
        int tableCount;
        int tableEntries;
        int sites;
        int resolvedArguments;
        int indexedSites;
        int decryptedSites;

        ProofAccumulator(String owner, long classKey) {
            this.owner = owner;
            this.classKey = classKey;
        }

        IntegerProof fail(String status, String reason) {
            return new IntegerProof(this, status, reason);
        }

        IntegerProof pass() {
            return new IntegerProof(this, "PASS", "all-integer-sites-proven");
        }
    }

    static final class RecoverySummary {
        int parsedClasses;
        int validatedClassKeys;
        int integerClasses;
        int totalIntegerSites;
        int tableClasses;
        int tableFailures;
        int resolvedArguments;
        int decryptedSites;
        int unresolvedSites;
        int rewriteClasses;
        int rewriteMethods;
        int rewritePlannedSites;
        int rewriteAppliedSites;
        int rewriteSkippedSites;
        int rewriteRollbackClasses;
        int remainingIntegerSites;
        int outputClasses;
        int outputVerificationErrors;
        int archiveEntries;
        int archiveResources;
        int signaturesRemoved;
    }

    static final class LongTableLayout {
        final AbstractInsnNode scanStart;
        final AbstractInsnNode tableStore;
        final int expectedEntries;

        LongTableLayout(AbstractInsnNode scanStart, AbstractInsnNode tableStore,
                        int expectedEntries) {
            this.scanStart = scanStart;
            this.tableStore = tableStore;
            this.expectedEntries = expectedEntries;
        }
    }

    static final class LongTableCandidate {
        final List<Integer> literalInstructions = new ArrayList<>();
        final List<Long> entries = new ArrayList<>();
    }

    private static final class IntegerSpec {
        final MethodNode method;
        final long indexMask;
        final int indexXor;
        final String tableField;

        IntegerSpec(MethodNode method, long indexMask, int indexXor, String tableField) {
            this.method = method;
            this.indexMask = indexMask;
            this.indexXor = indexXor;
            this.tableField = tableField;
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

    private static final class KeyCandidate {
        final long value;
        final String source;

        KeyCandidate(long value, String source) {
            this.value = value;
            this.source = source;
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

    private static final class SiteResult {
        final IndySite site;
        final Integer callInt;
        final Long callLong;
        final Integer tableIndex;
        final Integer value;
        final String status;

        SiteResult(IndySite site, Integer callInt, Long callLong, Integer tableIndex,
                   Integer value, String status) {
            this.site = site;
            this.callInt = callInt;
            this.callLong = callLong;
            this.tableIndex = tableIndex;
            this.value = value;
            this.status = status;
        }

        static SiteResult failure(IndySite site, String status) {
            return new SiteResult(site, null, null, null, null, status);
        }

        static SiteResult indexFailure(IndySite site, ArgumentExpressions arguments, int index) {
            return new SiteResult(site, arguments.intArgument.value, arguments.longArgument.value,
                    index, null, "INDEX_OUT_OF_RANGE");
        }

        static SiteResult decryptFailure(IndySite site, ArgumentExpressions arguments, int index) {
            return new SiteResult(site, arguments.intArgument.value, arguments.longArgument.value,
                    index, null, "INNER_DES_FAILED");
        }

        static SiteResult success(IndySite site, ArgumentExpressions arguments, int index,
                                  int value) {
            return new SiteResult(site, arguments.intArgument.value, arguments.longArgument.value,
                    index, value, "OK");
        }
    }

    private static final class CandidateResult implements Comparable<CandidateResult> {
        final KeyCandidate key;
        final List<SiteResult> results = new ArrayList<>();
        LongTableCandidate table;
        int resolved;
        int decrypted;
        int structuralValues;

        CandidateResult(KeyCandidate key) {
            this.key = key;
        }

        boolean isStrong(int sites) {
            return table != null && resolved == sites && decrypted == sites
                    && (sites > 1 || structuralValues == sites);
        }

        @Override
        public int compareTo(CandidateResult other) {
            int result = Integer.compare(decrypted, other.decrypted);
            if (result != 0) return result;
            result = Integer.compare(resolved, other.resolved);
            if (result != 0) return result;
            result = Integer.compare(structuralValues, other.structuralValues);
            if (result != 0) return result;
            return -Long.compareUnsigned(key.value, other.key.value);
        }
    }

    private static final class RewriteResult {
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
        final Integer value;
        String action;
        String reason;

        RewriteRecord(String method, int instruction, Integer value, String action,
                      String reason) {
            this.method = method;
            this.instruction = instruction;
            this.value = value;
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
        int integerSites;
    }
}
