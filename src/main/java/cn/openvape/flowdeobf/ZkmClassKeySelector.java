package cn.openvape.flowdeobf;

import org.objectweb.asm.Handle;
import org.objectweb.asm.Opcodes;
import org.objectweb.asm.Type;
import org.objectweb.asm.tree.AbstractInsnNode;
import org.objectweb.asm.tree.ClassNode;
import org.objectweb.asm.tree.FieldInsnNode;
import org.objectweb.asm.tree.FieldNode;
import org.objectweb.asm.tree.InvokeDynamicInsnNode;
import org.objectweb.asm.tree.LdcInsnNode;
import org.objectweb.asm.tree.MethodInsnNode;
import org.objectweb.asm.tree.MethodNode;
import org.objectweb.asm.tree.VarInsnNode;
import org.objectweb.asm.tree.analysis.Analyzer;
import org.objectweb.asm.tree.analysis.Frame;
import org.objectweb.asm.tree.analysis.SourceInterpreter;
import org.objectweb.asm.tree.analysis.SourceValue;

import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.security.MessageDigest;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Set;

/**
 * Selects class-key candidates using the original archive's member-indy evidence.
 * Input classes are parsed as data and are never defined or initialized.
 */
public final class ZkmClassKeySelector {
    private static final String BSM_DESC = "(Ljava/lang/invoke/MethodHandles$Lookup;"
            + "Ljava/lang/String;Ljava/lang/invoke/MethodType;)"
            + "Ljava/lang/invoke/CallSite;";
    private static final String LONG_STATE =
            ObfRuntimeNames.STATE_INTERFACE;

    private ZkmClassKeySelector() {
    }

    public static void main(String[] args) throws Exception {
        if (args.length != 2 && args.length != 3) {
            System.err.println("usage: ZkmClassKeySelector <original-input.jar> <report-dir>"
                    + " [--residual-integer-oracle]");
            System.exit(2);
        }
        boolean residual = args.length == 3
                && "--residual-integer-oracle".equals(args[2]);
        if (args.length == 3 && !residual) {
            throw new IllegalArgumentException("unknown option: " + args[2]);
        }
        audit(Paths.get(args[0]), Paths.get(args[1]), residual);
    }

    static Selection audit(Path input, Path reportDirectory) throws Exception {
        return audit(input, reportDirectory, false);
    }

    static Selection audit(Path input, Path reportDirectory,
                           boolean residualIntegerOracle) throws Exception {
        Files.createDirectories(reportDirectory);
        Map<String, ClassNode> classes = ZkmLongKeyEvaluator.readClasses(input);
        ReportRows report = new ReportRows();
        Selection result = select(classes, report, residualIntegerOracle);
        List<String> candidateRows = report.candidates;
        List<String> enumCandidateRows = report.enumCandidates;
        List<String> integerCandidateRows = report.integerCandidates;
        List<String> selectionRows = report.selections;
        List<String> noMemberRows = report.noMember;

        candidateRows.subList(1, candidateRows.size()).sort(Comparator.naturalOrder());
        enumCandidateRows.subList(1, enumCandidateRows.size()).sort(Comparator.naturalOrder());
        integerCandidateRows.subList(1, integerCandidateRows.size())
                .sort(Comparator.naturalOrder());
        selectionRows.subList(1, selectionRows.size()).sort(Comparator.naturalOrder());
        noMemberRows.subList(1, noMemberRows.size()).sort(Comparator.naturalOrder());
        Files.write(reportDirectory.resolve("candidates.tsv"), candidateRows,
                StandardCharsets.UTF_8);
        Files.write(reportDirectory.resolve("enum-candidates.tsv"), enumCandidateRows,
                StandardCharsets.UTF_8);
        Files.write(reportDirectory.resolve("integer-candidates.tsv"), integerCandidateRows,
                StandardCharsets.UTF_8);
        Files.write(reportDirectory.resolve("selections.tsv"), selectionRows,
                StandardCharsets.UTF_8);
        Files.write(reportDirectory.resolve("unresolved-no-member.tsv"), noMemberRows,
                StandardCharsets.UTF_8);
        List<String> audit = Arrays.asList(
                "input=" + input.toAbsolutePath(),
                "input_sha256=" + sha256(input),
                "residual_integer_oracle_requested=" + residualIntegerOracle,
                "parsed_classes=" + result.parsedClasses,
                "key_sites=" + result.keySites,
                "validated_keys=" + result.validatedKeys,
                "unresolved_keys=" + result.unresolvedKeys,
                "member_classes=" + result.memberClasses,
                "member_sites=" + result.memberSites,
                "validated_member_pass=" + result.validatedMemberPass,
                "validated_member_fail=" + result.validatedMemberFail,
                "unresolved_member_classes=" + result.unresolvedMemberClasses,
                "member_unique_selected=" + result.memberSelected,
                "member_ambiguous=" + result.memberAmbiguous,
                "member_no_candidate=" + result.memberRejected,
                "enum_oracle_classes=" + result.enumOracleClasses,
                "enum_unique_selected=" + result.enumSelected,
                "enum_ambiguous=" + result.enumAmbiguous,
                "enum_no_candidate=" + result.enumRejected,
                "integer_oracle_remaining_stage=" + result.integerOracleRemainingStage,
                "integer_oracle_classes=" + result.integerOracleClasses,
                "integer_candidate_values_checked=" + result.integerCandidateValues,
                "integer_unique_selected=" + result.integerSelected,
                "integer_ambiguous=" + result.integerAmbiguous,
                "integer_no_candidate=" + result.integerRejected,
                "integer_sites_proven=" + result.integerSitesProven,
                "integer_sites_decrypted=" + result.integerSitesDecrypted,
                "unresolved_no_member_evidence=" + result.noMemberEvidence,
                "no_member_models_agree=" + result.noMemberModelsAgree,
                "no_member_model_conflicts=" + result.noMemberModelConflicts,
                "candidate_values_checked=" + result.candidateValues,
                "selected_keys=" + result.selected.size(),
                "input_classes_loaded=false");
        Files.write(reportDirectory.resolve("audit.txt"), audit, StandardCharsets.UTF_8);
        String gate = result.validatedMemberFail == 0
                ? result.selected.size() == result.keySites ? "PASS\n" : "PASS_PARTIAL\n"
                : "FAIL\n";
        Files.write(reportDirectory.resolve("gate.txt"), gate.getBytes(StandardCharsets.UTF_8));
        System.out.println("keys=" + result.keySites + " validated=" + result.validatedKeys
                + " member_sites=" + result.memberSites + " member_selected="
                + result.memberSelected + " integer_selected=" + result.integerSelected
                + " selected=" + result.selected.size()
                + " report=" + reportDirectory);
        return result;
    }

    /** Runs the evidence selector without writing an archive or report. */
    static Selection select(Map<String, ClassNode> classes) {
        return select(classes, new ReportRows(), false);
    }

    /**
     * Returns every independently reconstructed state-model value for each
     * class-key owner.  Consumers must still supply their own uniqueness
     * oracle; the presence of a value here is not itself a key proof.
     */
    static Map<String, Set<Long>> candidateClassKeys(
            Map<String, ClassNode> classes) {
        Map<String, Long> validated =
                ZkmStringDecryptor.solveValidatedClassKeys(classes);
        Map<String, CandidateSet> candidates = new LinkedHashMap<>();
        addCandidates(candidates, validated, "validated-string-table");
        addCandidates(candidates, ZkmLongKeyEvaluator.evaluateClassKeys(classes),
                "isolated-model");
        addCandidates(candidates,
                ZkmLongKeyEvaluator.evaluateClassKeysSequential(classes),
                "archive-sequential-model");
        List<String> archiveOrder =
                ZkmLongKeyEvaluator.newStatefulKeySequence(classes).owners();
        List<String> hierarchy = hierarchyOrder(classes, archiveOrder);
        addCandidates(candidates, evaluateOrder(classes, hierarchy),
                "hierarchy-sequential-model");
        Set<String> unresolved = new LinkedHashSet<>(candidates.keySet());
        unresolved.removeAll(validated.keySet());
        collectValidatedFrontier(classes, validated, archiveOrder, unresolved,
                candidates, "validated-archive-frontier");
        collectValidatedFrontier(classes, validated, hierarchy, unresolved,
                candidates, "validated-hierarchy-frontier");

        Map<String, Set<Long>> result = new LinkedHashMap<>();
        for (Map.Entry<String, CandidateSet> entry : candidates.entrySet()) {
            result.put(entry.getKey(), Collections.unmodifiableSet(
                    new LinkedHashSet<>(entry.getValue().values.keySet())));
        }
        return Collections.unmodifiableMap(result);
    }

    /**
     * Runs the explicit final-stage integer oracle on an archive whose independently proven
     * string/member/enum key owners have already been removed.
     */
    public static Selection selectResidual(Map<String, ClassNode> classes) {
        return select(classes, new ReportRows(), true);
    }

    private static Selection select(Map<String, ClassNode> classes, ReportRows report,
                                    boolean residualIntegerOracle) {
        Map<String, Long> validated = ZkmStringDecryptor.solveValidatedClassKeys(classes);
        Map<String, CandidateSet> candidates = new LinkedHashMap<>();
        addCandidates(candidates, validated, "validated-string-table");
        addCandidates(candidates, ZkmLongKeyEvaluator.evaluateClassKeys(classes),
                "isolated-model");
        addCandidates(candidates, ZkmLongKeyEvaluator.evaluateClassKeysSequential(classes),
                "archive-sequential-model");

        List<String> hierarchy = hierarchyOrder(classes,
                ZkmLongKeyEvaluator.newStatefulKeySequence(classes).owners());
        addCandidates(candidates, evaluateOrder(classes, hierarchy),
                "hierarchy-sequential-model");

        Map<String, ClassEvidence> evidence = memberEvidence(classes);
        Set<String> unresolvedOwners = new LinkedHashSet<>();
        for (String owner : candidates.keySet()) {
            if (!validated.containsKey(owner)) unresolvedOwners.add(owner);
        }
        collectValidatedFrontier(classes, validated,
                ZkmLongKeyEvaluator.newStatefulKeySequence(classes).owners(),
                unresolvedOwners, candidates, "validated-archive-frontier");
        collectValidatedFrontier(classes, validated, hierarchy,
                unresolvedOwners, candidates, "validated-hierarchy-frontier");

        Map<String, EnumEvidence> enumEvidence = enumEvidence(classes, validated);

        Selection result = new Selection();
        result.parsedClasses = classes.size();
        result.keySites = candidates.size();
        result.validatedKeys = validated.size();
        result.unresolvedKeys = candidates.size() - validated.size();
        result.memberClasses = evidence.size();
        for (ClassEvidence value : evidence.values()) result.memberSites += value.sites.size();
        result.selected.putAll(validated);

        List<String> owners = new ArrayList<>(candidates.keySet());
        Collections.sort(owners);
        for (String owner : owners) {
            ClassEvidence classEvidence = evidence.get(owner);
            EnumEvidence ownerEnum = enumEvidence.get(owner);
            CandidateSet ownerCandidates = candidates.get(owner);
            Long trusted = validated.get(owner);
            if (classEvidence == null) {
                if (trusted != null) {
                    decide(result, owner, trusted, "string-table",
                            "TRUSTED_NO_MEMBER_SITES", "validated-string-table");
                    report.selections.add(tsv(owner, hex(trusted), "string-table",
                            "TRUSTED_NO_MEMBER_SITES", "validated-string-table",
                            1, ownerCandidates.values.size()));
                } else if (ownerEnum != null) {
                    result.enumOracleClasses++;
                    List<Long> passing = new ArrayList<>();
                    for (Map.Entry<Long, Set<String>> candidate
                            : ownerCandidates.values.entrySet()) {
                        EnumCheck check = ownerEnum.check(candidate.getKey());
                        report.enumCandidates.add(tsv(owner, hex(candidate.getKey()),
                                join(candidate.getValue()), hex(ownerEnum.mask),
                                hex(candidate.getKey() ^ ownerEnum.mask),
                                ownerEnum.names.size(), check.tables, check.plaintexts,
                                check.passes() ? "PASS" : "FAIL", check.reason));
                        if (check.passes()) passing.add(candidate.getKey());
                    }
                    if (passing.size() == 1) {
                        long selected = passing.get(0);
                        String sources = join(ownerCandidates.values.get(selected));
                        result.selected.put(owner, selected);
                        result.enumSelected++;
                        decide(result, owner, selected, sources, "ENUM_NAMES_UNIQUE",
                                "constructor-name-index-set=ACC_ENUM-fields");
                        report.selections.add(tsv(owner, hex(selected), sources,
                                "ENUM_NAMES_UNIQUE",
                                "constructor-name-index-set=ACC_ENUM-fields", 1,
                                ownerCandidates.values.size()));
                        continue;
                    }
                    if (passing.isEmpty()) result.enumRejected++;
                    else result.enumAmbiguous++;
                    // A failed enum oracle remains unresolved and is classified below.
                    recordNoMember(result, report, owner, ownerCandidates,
                            passing.isEmpty() ? "ENUM_NO_CANDIDATE"
                                    : "ENUM_AMBIGUOUS=" + passing.size());
                } else {
                    recordNoMember(result, report, owner, ownerCandidates, "");
                }
                continue;
            }

            List<Long> passing = new ArrayList<>();
            for (Map.Entry<Long, Set<String>> candidate : ownerCandidates.values.entrySet()) {
                CandidateCheck check = classEvidence.check(candidate.getKey());
                result.candidateValues++;
                if (check.passes()) passing.add(candidate.getKey());
                report.candidates.add(tsv(owner, trusted != null, hex(candidate.getKey()),
                        join(candidate.getValue()), check.sites, check.arguments,
                        check.decoded, check.compatible, check.passes() ? "PASS" : "FAIL",
                        check.reason));
            }

            if (trusted != null) {
                CandidateCheck trustedCheck = classEvidence.check(trusted);
                if (trustedCheck.passes()) {
                    result.validatedMemberPass++;
                    decide(result, owner, trusted, "string-table+member-indy",
                            "TRUSTED_VALIDATED", "all-member-sites-compatible");
                    report.selections.add(tsv(owner, hex(trusted),
                            "string-table+member-indy", "TRUSTED_VALIDATED",
                            "all-member-sites-compatible",
                            passing.size(), ownerCandidates.values.size()));
                } else {
                    result.validatedMemberFail++;
                    decide(result, owner, trusted, "string-table",
                            "TRUSTED_MEMBER_CHECK_FAILED", trustedCheck.reason);
                    report.selections.add(tsv(owner, hex(trusted), "string-table",
                            "TRUSTED_MEMBER_CHECK_FAILED", trustedCheck.reason,
                            passing.size(), ownerCandidates.values.size()));
                }
                continue;
            }

            result.unresolvedMemberClasses++;
            if (passing.size() == 1) {
                long selected = passing.get(0);
                String sources = join(ownerCandidates.values.get(selected));
                result.selected.put(owner, selected);
                result.memberSelected++;
                decide(result, owner, selected, sources, "MEMBER_UNIQUE",
                        "all-member-sites-compatible; rejected_candidates="
                                + (ownerCandidates.values.size() - 1));
                report.selections.add(tsv(owner, hex(selected), sources,
                        "MEMBER_UNIQUE", "all-member-sites-compatible; rejected-candidates="
                                + (ownerCandidates.values.size() - 1),
                        1, ownerCandidates.values.size()));
            } else if (passing.isEmpty()) {
                result.memberRejected++;
                decide(result, owner, null, "", "MEMBER_NO_CANDIDATE",
                        "all-candidates-rejected");
                report.selections.add(tsv(owner, "", "", "MEMBER_NO_CANDIDATE",
                        "all-candidates-rejected", 0, ownerCandidates.values.size()));
            } else {
                result.memberAmbiguous++;
                decide(result, owner, null, "", "MEMBER_AMBIGUOUS",
                        "passing-candidates=" + passing.size());
                report.selections.add(tsv(owner, "", "", "MEMBER_AMBIGUOUS",
                        "passing-candidates=" + passing.size(), passing.size(),
                        ownerCandidates.values.size()));
            }
        }
        result.integerOracleRemainingStage = residualIntegerOracle;
        if (residualIntegerOracle && !result.selected.isEmpty()) {
            throw new IllegalStateException("residual integer oracle requires a remaining-key "
                    + "archive; prior-oracle-selected=" + result.selected.size());
        }
        if (residualIntegerOracle) {
            applyIntegerOracle(classes, candidates, result, report, owners);
        }
        return result;
    }

    private static void decide(Selection selection, String owner, Long key,
                               String source, String status, String reason) {
        selection.decisions.put(owner, new Decision(key, source, status, reason));
    }

    private static void recordNoMember(Selection result, ReportRows report, String owner,
                                       CandidateSet candidates, String oracleReason) {
        result.noMemberEvidence++;
        Long isolated = candidates.valueForSource("isolated-model");
        Long archive = candidates.valueForSource("archive-sequential-model");
        Long hierarchy = candidates.valueForSource("hierarchy-sequential-model");
        int distinct = distinct(isolated, archive, hierarchy);
        String classification = distinct == 1
                ? "NO_MEMBER_INDY_CONSUMER_MODELS_AGREE"
                : "NO_MEMBER_INDY_CONSUMER_MODEL_CONFLICT";
        if (!oracleReason.isEmpty()) classification = oracleReason + ";" + classification;
        if (distinct == 1) result.noMemberModelsAgree++;
        else result.noMemberModelConflicts++;
        decide(result, owner, null, "", "UNRESOLVED_NO_MEMBER_SITES", classification);
        report.noMember.add(tsv(owner, hex(isolated), hex(archive), hex(hierarchy),
                distinct, classification));
        report.selections.add(tsv(owner, "", "", "UNRESOLVED_NO_MEMBER_SITES",
                classification, 0, candidates.values.size()));
    }

    private static void applyIntegerOracle(Map<String, ClassNode> classes,
                                           Map<String, CandidateSet> candidates,
                                           Selection result, ReportRows report,
                                           List<String> owners) {
        for (String owner : owners) {
            if (result.selected.containsKey(owner)) continue;
            ClassNode ownerClass = classes.get(owner);
            CandidateSet ownerCandidates = candidates.get(owner);
            if (ownerClass == null || ownerCandidates == null) continue;

            List<IntegerCandidateCheck> checks = new ArrayList<>();
            boolean hasIntegerSites = false;
            for (Map.Entry<Long, Set<String>> candidate : ownerCandidates.values.entrySet()) {
                ZkmIntegerDecryptor.IntegerProof proof =
                        ZkmIntegerDecryptor.proveClassKey(ownerClass, candidate.getKey());
                if (proof.sites != 0) hasIntegerSites = true;
                checks.add(new IntegerCandidateCheck(candidate.getKey(), candidate.getValue(),
                        proof));
            }
            if (!hasIntegerSites) continue;

            result.integerOracleClasses++;
            result.integerCandidateValues += checks.size();
            List<IntegerCandidateCheck> passing = new ArrayList<>();
            for (IntegerCandidateCheck check : checks) {
                ZkmIntegerDecryptor.IntegerProof proof = check.proof;
                if (proof.passes()) passing.add(check);
                report.integerCandidates.add(tsv(owner, hex(check.key), join(check.sources),
                        proof.bootstrapCount, proof.bootstrapMethodCount, proof.specCount,
                        proof.clinitCount, proof.keyFieldCount, proof.outerMaskCount,
                        proof.tableLayoutCount, proof.tableCount, proof.tableEntries,
                        proof.sites, proof.resolvedArguments, proof.indexedSites,
                        proof.decryptedSites, joinIntegers(proof.values),
                        proof.passes() ? "PASS" : "FAIL", proof.status, proof.reason));
            }

            Decision previous = result.decisions.get(owner);
            removeOwnerRows(report.selections, owner);
            if (passing.size() == 1) {
                IntegerCandidateCheck selected = passing.get(0);
                String sources = join(selected.sources);
                result.selected.put(owner, selected.key);
                result.integerSelected++;
                result.integerSitesProven += selected.proof.sites;
                result.integerSitesDecrypted += selected.proof.decryptedSites;
                String reason = "all-integer-sites-proven; values="
                        + joinIntegers(selected.proof.values);
                decide(result, owner, selected.key, "integer-table+" + sources,
                        "INTEGER_TABLE_UNIQUE", reason);
                report.selections.add(tsv(owner, hex(selected.key),
                        "integer-table+" + sources, "INTEGER_TABLE_UNIQUE", reason,
                        1, ownerCandidates.values.size()));
                if (previous != null
                        && "UNRESOLVED_NO_MEMBER_SITES".equals(previous.status)) {
                    removeOwnerRows(report.noMember, owner);
                    result.noMemberEvidence--;
                    Long isolated = ownerCandidates.valueForSource("isolated-model");
                    Long archive = ownerCandidates.valueForSource("archive-sequential-model");
                    Long hierarchy = ownerCandidates.valueForSource("hierarchy-sequential-model");
                    if (distinct(isolated, archive, hierarchy) == 1) {
                        result.noMemberModelsAgree--;
                    } else {
                        result.noMemberModelConflicts--;
                    }
                }
            } else if (passing.isEmpty()) {
                result.integerRejected++;
                String reason = "all-candidates-rejected; failure-codes="
                        + integerFailureCodes(checks);
                decide(result, owner, null, "", "INTEGER_NO_CANDIDATE", reason);
                report.selections.add(tsv(owner, "", "", "INTEGER_NO_CANDIDATE", reason,
                        0, ownerCandidates.values.size()));
            } else {
                result.integerAmbiguous++;
                String reason = "passing-candidates=" + passing.size();
                decide(result, owner, null, "", "INTEGER_AMBIGUOUS", reason);
                report.selections.add(tsv(owner, "", "", "INTEGER_AMBIGUOUS", reason,
                        passing.size(), ownerCandidates.values.size()));
            }
        }
    }

    private static String integerFailureCodes(List<IntegerCandidateCheck> checks) {
        Set<String> result = new LinkedHashSet<>();
        for (IntegerCandidateCheck check : checks) {
            if (!check.proof.passes()) result.add(check.proof.status);
        }
        return join(result);
    }

    private static String joinIntegers(List<Integer> values) {
        StringBuilder result = new StringBuilder();
        for (Integer value : values) {
            if (result.length() != 0) result.append(',');
            result.append(value);
        }
        return result.toString();
    }

    private static void removeOwnerRows(List<String> rows, String owner) {
        String prefix = owner + '\t';
        for (int index = rows.size() - 1; index >= 1; index--) {
            if (rows.get(index).startsWith(prefix)) rows.remove(index);
        }
    }

    private static Map<String, ClassEvidence> memberEvidence(Map<String, ClassNode> classes) {
        Map<String, ClassEvidence> result = new LinkedHashMap<>();
        for (ClassNode owner : classes.values()) {
            List<MemberSite> sites = new ArrayList<>();
            for (MethodNode method : owner.methods) {
                List<InvokeDynamicInsnNode> methodSites = new ArrayList<>();
                for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
                     insn = insn.getNext()) {
                    if (insn instanceof InvokeDynamicInsnNode
                            && isMemberSite(owner, (InvokeDynamicInsnNode) insn)) {
                        methodSites.add((InvokeDynamicInsnNode) insn);
                    }
                }
                if (methodSites.isEmpty()) continue;
                try {
                    MethodExpressions expressions = MethodExpressions.build(owner, method);
                    for (InvokeDynamicInsnNode indy : methodSites) {
                        sites.add(expressions.site(indy));
                    }
                } catch (Throwable failure) {
                    for (InvokeDynamicInsnNode indy : methodSites) {
                        sites.add(MemberSite.failure(indy, "analysis=" + shortReason(failure)));
                    }
                }
            }
            if (sites.isEmpty()) continue;
            try {
                result.put(owner.name, new ClassEvidence(owner,
                        ZkmMemberIndyDeobfuscator.ResolverModel.build(owner), sites));
            } catch (Throwable failure) {
                result.put(owner.name, new ClassEvidence(owner, null, sites,
                        "resolver=" + shortReason(failure)));
            }
        }
        return result;
    }

    private static Map<String, EnumEvidence> enumEvidence(
            Map<String, ClassNode> classes, Map<String, Long> validated) {
        Map<String, EnumEvidence> result = new LinkedHashMap<>();
        for (ClassNode owner : classes.values()) {
            if (validated.containsKey(owner.name) || (owner.access & Opcodes.ACC_ENUM) == 0) {
                continue;
            }
            Set<String> names = new LinkedHashSet<>();
            for (FieldNode field : owner.fields) {
                if ((field.access & Opcodes.ACC_STATIC) != 0
                        && (field.access & Opcodes.ACC_ENUM) != 0
                        && ("L" + owner.name + ";").equals(field.desc)) {
                    names.add(field.name);
                }
            }
            MethodNode clinit = method(owner, "<clinit>", "()V");
            Long mask = clinit == null ? null : outerMask(owner, clinit);
            List<Integer> nameIndexes = clinit == null ? Collections.<Integer>emptyList()
                    : enumNameIndexes(owner, clinit);
            if (!names.isEmpty() && clinit != null && mask != null
                    && nameIndexes.size() == names.size()
                    && new LinkedHashSet<Integer>(nameIndexes).size() == nameIndexes.size()) {
                result.put(owner.name, new EnumEvidence(clinit, names, nameIndexes, mask));
            }
        }
        return result;
    }

    private static Long outerMask(ClassNode owner, MethodNode clinit) {
        Set<String> keyFields = MethodExpressions.keyFields(owner);
        List<MethodInsnNode> transforms = new ArrayList<>();
        for (AbstractInsnNode insn = clinit.instructions.getFirst(); insn != null;
             insn = insn.getNext()) {
            if (isClassKeyTransform(insn)) transforms.add((MethodInsnNode) insn);
        }
        Set<Long> masks = new LinkedHashSet<>();
        for (AbstractInsnNode xor = clinit.instructions.getFirst(); xor != null;
             xor = xor.getNext()) {
            if (xor.getOpcode() != Opcodes.LXOR
                    || !(nextCode(xor) instanceof VarInsnNode)
                    || nextCode(xor).getOpcode() != Opcodes.LSTORE) continue;
            AbstractInsnNode right = previousCode(xor);
            Long mask = constant(right);
            if (mask == null) continue;
            AbstractInsnNode left = previousCode(right);
            boolean classKey = isClassKeyTransform(left);
            if (left instanceof FieldInsnNode && left.getOpcode() == Opcodes.GETSTATIC) {
                FieldInsnNode field = (FieldInsnNode) left;
                classKey = keyFields.contains(field.owner + "." + field.name);
            }
            if (!classKey && transforms.size() == 1
                    && clinit.instructions.indexOf(transforms.get(0))
                    < clinit.instructions.indexOf(xor)) {
                // The three stack-carried shapes keep the sole transform result live
                // until this mask/store pair.
                classKey = true;
            }
            if (classKey) masks.add(mask);
        }
        return masks.size() == 1 ? masks.iterator().next() : null;
    }

    private static List<Integer> enumNameIndexes(ClassNode owner, MethodNode clinit) {
        List<Integer> result = new ArrayList<>();
        for (AbstractInsnNode start = clinit.instructions.getFirst(); start != null;
             start = start.getNext()) {
            if (start.getOpcode() != Opcodes.NEW
                    || !(start instanceof org.objectweb.asm.tree.TypeInsnNode)
                    || !owner.name.equals(((org.objectweb.asm.tree.TypeInsnNode) start).desc)) {
                continue;
            }
            Integer nameIndex = null;
            boolean constructor = false;
            for (AbstractInsnNode cursor = nextCode(start); cursor != null;
                 cursor = nextCode(cursor)) {
                if (cursor.getOpcode() == Opcodes.NEW) break;
                if (nameIndex == null && cursor.getOpcode() == Opcodes.AALOAD) {
                    AbstractInsnNode indexNode = previousCode(cursor);
                    AbstractInsnNode arrayNode = previousCode(indexNode);
                    Integer index = intConstant(indexNode);
                    if (index != null && arrayNode instanceof VarInsnNode
                            && arrayNode.getOpcode() == Opcodes.ALOAD) {
                        nameIndex = index;
                    }
                }
                if (cursor instanceof MethodInsnNode
                        && cursor.getOpcode() == Opcodes.INVOKESPECIAL) {
                    MethodInsnNode call = (MethodInsnNode) cursor;
                    if (owner.name.equals(call.owner) && "<init>".equals(call.name)) {
                        constructor = true;
                    }
                    break;
                }
            }
            if (constructor && nameIndex != null) result.add(nameIndex);
        }
        return result;
    }

    private static boolean isClassKeyTransform(AbstractInsnNode insn) {
        if (!(insn instanceof MethodInsnNode)) return false;
        MethodInsnNode call = (MethodInsnNode) insn;
        return call.getOpcode() == Opcodes.INVOKEINTERFACE
                && LONG_STATE.equals(call.owner) && "a".equals(call.name)
                && "(J)J".equals(call.desc);
    }

    private static MethodNode method(ClassNode owner, String name, String descriptor) {
        for (MethodNode method : owner.methods) {
            if (name.equals(method.name) && descriptor.equals(method.desc)) return method;
        }
        return null;
    }

    private static boolean isMemberSite(ClassNode owner, InvokeDynamicInsnNode indy) {
        Handle bsm = indy.bsm;
        Type[] arguments = Type.getArgumentTypes(indy.desc);
        return arguments.length >= 2
                && Type.LONG_TYPE.equals(arguments[arguments.length - 2])
                && Type.LONG_TYPE.equals(arguments[arguments.length - 1])
                && bsm != null && bsm.getTag() == Opcodes.H_INVOKESTATIC
                && owner.name.equals(bsm.getOwner()) && BSM_DESC.equals(bsm.getDesc())
                && (indy.bsmArgs == null || indy.bsmArgs.length == 0);
    }

    private static void addCandidates(Map<String, CandidateSet> candidates,
                                      Map<String, Long> values, String source) {
        for (Map.Entry<String, Long> entry : values.entrySet()) {
            candidates.computeIfAbsent(entry.getKey(), ignored -> new CandidateSet())
                    .add(entry.getValue(), source);
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

    private static void collectValidatedFrontier(
            Map<String, ClassNode> classes, Map<String, Long> validated, List<String> order,
            Set<String> targets, Map<String, CandidateSet> candidates, String source) {
        ZkmLongKeyEvaluator.StatefulKeySequence sequence =
                ZkmLongKeyEvaluator.newStatefulKeySequence(classes);
        Set<String> remaining = new LinkedHashSet<>(validated.keySet());
        captureFrontier(sequence, targets, candidates, source);
        boolean progress;
        int passes = 0;
        do {
            progress = false;
            passes++;
            for (String owner : order) {
                Long expected = remaining.contains(owner) ? validated.get(owner) : null;
                if (expected == null || !sequence.hasSite(owner)
                        || sequence.peek(owner) != expected.longValue()) continue;
                sequence.commit(owner);
                remaining.remove(owner);
                captureFrontier(sequence, targets, candidates, source);
                progress = true;
            }
        } while (progress && !remaining.isEmpty() && passes <= 64);
    }

    private static void captureFrontier(ZkmLongKeyEvaluator.StatefulKeySequence sequence,
                                        Set<String> targets,
                                        Map<String, CandidateSet> candidates, String source) {
        for (String owner : targets) {
            if (!sequence.hasSite(owner)) continue;
            candidates.computeIfAbsent(owner, ignored -> new CandidateSet())
                    .add(sequence.peek(owner), source);
        }
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

    private static void visitHierarchy(String owner, Map<String, ClassNode> classes,
                                       Set<String> keys, Set<String> visited,
                                       Set<String> active, List<String> result) {
        if (visited.contains(owner)) return;
        if (!active.add(owner)) throw new IllegalStateException("hierarchy-cycle=" + owner);
        ClassNode node = classes.get(owner);
        if (node != null && (node.access & Opcodes.ACC_INTERFACE) == 0
                && node.superName != null && classes.containsKey(node.superName)) {
            visitHierarchy(node.superName, classes, keys, visited, active, result);
        }
        active.remove(owner);
        visited.add(owner);
        if (keys.contains(owner)) result.add(owner);
    }

    private static String expectedHandleDescriptor(
            ZkmMemberIndyDeobfuscator.MemberTarget target) {
        Type owner = Type.getObjectType(target.owner);
        if ("GETFIELD".equals(target.kind)) {
            return Type.getMethodDescriptor(Type.getType(target.desc), owner);
        }
        if ("PUTFIELD".equals(target.kind)) {
            return Type.getMethodDescriptor(Type.VOID_TYPE, owner, Type.getType(target.desc));
        }
        if ("GETSTATIC".equals(target.kind)) {
            return Type.getMethodDescriptor(Type.getType(target.desc));
        }
        if ("PUTSTATIC".equals(target.kind)) {
            return Type.getMethodDescriptor(Type.VOID_TYPE, Type.getType(target.desc));
        }
        Type method = Type.getMethodType(target.desc);
        if ("INVOKESTATIC".equals(target.kind)) return target.desc;
        if ("<init>".equals(target.name)) {
            return Type.getMethodDescriptor(owner, method.getArgumentTypes());
        }
        Type[] old = method.getArgumentTypes();
        Type[] arguments = new Type[old.length + 1];
        arguments[0] = owner;
        System.arraycopy(old, 0, arguments, 1, old.length);
        return Type.getMethodDescriptor(method.getReturnType(), arguments);
    }

    static boolean explicitCastCompatible(String actualDescriptor,
                                          String targetDescriptor) {
        return ZkmMemberIndyDeobfuscator.ConversionModel
                .between(actualDescriptor, targetDescriptor).compatible;
    }

    private static String stripTrailingKeys(String descriptor) {
        Type method = Type.getMethodType(descriptor);
        Type[] arguments = method.getArgumentTypes();
        return Type.getMethodDescriptor(method.getReturnType(),
                Arrays.copyOf(arguments, arguments.length - 2));
    }

    private static boolean validMemberName(String name) {
        if (name == null || name.isEmpty()) return false;
        if ("<init>".equals(name) || "<clinit>".equals(name)) return true;
        for (int index = 0; index < name.length(); index++) {
            char value = name.charAt(index);
            if (value == '.' || value == ';' || value == '[' || value == '/') return false;
        }
        return true;
    }

    private static Long constant(AbstractInsnNode insn) {
        if (insn == null) return null;
        if (insn.getOpcode() == Opcodes.LCONST_0) return 0L;
        if (insn.getOpcode() == Opcodes.LCONST_1) return 1L;
        return insn instanceof LdcInsnNode && ((LdcInsnNode) insn).cst instanceof Long
                ? (Long) ((LdcInsnNode) insn).cst : null;
    }

    private static Integer intConstant(AbstractInsnNode insn) {
        if (insn == null) return null;
        int opcode = insn.getOpcode();
        if (opcode >= Opcodes.ICONST_M1 && opcode <= Opcodes.ICONST_5) {
            return opcode - Opcodes.ICONST_0;
        }
        if (insn instanceof org.objectweb.asm.tree.IntInsnNode
                && (opcode == Opcodes.BIPUSH || opcode == Opcodes.SIPUSH)) {
            return ((org.objectweb.asm.tree.IntInsnNode) insn).operand;
        }
        return insn instanceof LdcInsnNode && ((LdcInsnNode) insn).cst instanceof Integer
                ? (Integer) ((LdcInsnNode) insn).cst : null;
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

    private static String hex(long value) {
        return String.format(Locale.ROOT, "%016X", value);
    }

    private static String sha256(Path input) throws Exception {
        byte[] digest = MessageDigest.getInstance("SHA-256")
                .digest(Files.readAllBytes(input));
        StringBuilder result = new StringBuilder(digest.length * 2);
        for (byte value : digest) result.append(String.format(Locale.ROOT, "%02X", value & 0xff));
        return result.toString();
    }

    private static String hex(Long value) {
        return value == null ? "" : hex(value.longValue());
    }

    private static int distinct(Long... values) {
        Set<Long> distinct = new HashSet<>();
        for (Long value : values) if (value != null) distinct.add(value);
        return distinct.size();
    }

    private static String join(Set<String> values) {
        StringBuilder result = new StringBuilder();
        for (String value : values) {
            if (result.length() != 0) result.append(',');
            result.append(value);
        }
        return result.toString();
    }

    private static String tsv(Object... values) {
        StringBuilder result = new StringBuilder();
        for (int index = 0; index < values.length; index++) {
            if (index != 0) result.append('\t');
            if (values[index] != null) result.append(String.valueOf(values[index])
                    .replace('\t', ' ').replace('\r', ' ').replace('\n', ' '));
        }
        return result.toString();
    }

    private static String shortReason(Throwable failure) {
        String value = failure.getClass().getSimpleName() + ":" + failure.getMessage();
        return value.length() <= 160 ? value : value.substring(0, 160);
    }

    public static final class Selection {
        final Map<String, Long> selected = new LinkedHashMap<>();
        final Map<String, Decision> decisions = new LinkedHashMap<>();
        int parsedClasses;
        int keySites;
        int validatedKeys;
        int unresolvedKeys;
        int memberClasses;
        int memberSites;
        int validatedMemberPass;
        int validatedMemberFail;
        int unresolvedMemberClasses;
        int memberSelected;
        int memberAmbiguous;
        int memberRejected;
        int enumOracleClasses;
        int enumSelected;
        int enumAmbiguous;
        int enumRejected;
        boolean integerOracleRemainingStage;
        int integerOracleClasses;
        int integerCandidateValues;
        int integerSelected;
        int integerAmbiguous;
        int integerRejected;
        int integerSitesProven;
        int integerSitesDecrypted;
        int noMemberEvidence;
        int noMemberModelsAgree;
        int noMemberModelConflicts;
        int candidateValues;

        public Map<String, Long> selectedKeys() {
            return Collections.unmodifiableMap(selected);
        }

        public Map<String, Decision> decisions() {
            return Collections.unmodifiableMap(decisions);
        }
    }

    static final class Decision {
        final Long key;
        final String source;
        final String status;
        final String reason;

        Decision(Long key, String source, String status, String reason) {
            this.key = key;
            this.source = source;
            this.status = status;
            this.reason = reason;
        }
    }

    private static final class ReportRows {
        final List<String> candidates = new ArrayList<>();
        final List<String> enumCandidates = new ArrayList<>();
        final List<String> integerCandidates = new ArrayList<>();
        final List<String> selections = new ArrayList<>();
        final List<String> noMember = new ArrayList<>();

        ReportRows() {
            candidates.add("class\tvalidated\tcandidate_key_hex\tsources\tsites"
                    + "\targument_sites\tdecoded_sites\tcompatible_sites\tstatus\treason");
            enumCandidates.add("class\tcandidate_key_hex\tsources\touter_mask_hex"
                    + "\touter_key_hex\tenum_fields\tdecoded_tables\tplaintexts"
                    + "\tstatus\treason");
            integerCandidates.add("class\tcandidate_key_hex\tsources\tbootstrap_handles"
                    + "\tbootstrap_methods\tinteger_specs\tclinits\tkey_fields"
                    + "\touter_masks\ttable_layouts\tlong_tables\ttable_entries"
                    + "\tsites\tresolved_arguments\tin_range_indices\tdecrypted_sites"
                    + "\tvalues\tresult\tfailure_code\treason");
            selections.add("class\tselected_key_hex\tsource\tstatus\treason"
                    + "\tpassing_candidates\ttotal_candidates");
            noMember.add("class\tisolated_key_hex\tarchive_sequential_key_hex"
                    + "\thierarchy_sequential_key_hex\tdistinct_candidates\tclassification");
        }
    }

    private static final class IntegerCandidateCheck {
        final long key;
        final Set<String> sources;
        final ZkmIntegerDecryptor.IntegerProof proof;

        IntegerCandidateCheck(long key, Set<String> sources,
                              ZkmIntegerDecryptor.IntegerProof proof) {
            this.key = key;
            this.sources = sources;
            this.proof = proof;
        }
    }

    private static final class EnumEvidence {
        final MethodNode clinit;
        final Set<String> names;
        final List<Integer> nameIndexes;
        final long mask;

        EnumEvidence(MethodNode clinit, Set<String> names, List<Integer> nameIndexes,
                     long mask) {
            this.clinit = clinit;
            this.names = names;
            this.nameIndexes = nameIndexes;
            this.mask = mask;
        }

        EnumCheck check(long classKey) {
            List<ZkmStringDecryptor.TableCandidate> candidates =
                    ZkmStringDecryptor.genericOuterCandidates(clinit, classKey ^ mask);
            List<String> combinedEntries = new ArrayList<>();
            StringBuilder plaintexts = new StringBuilder();
            for (ZkmStringDecryptor.TableCandidate candidate : candidates) {
                if (plaintexts.length() != 0) plaintexts.append('|');
                for (int index = 0; index < candidate.entries.size(); index++) {
                    if (index != 0) plaintexts.append(',');
                    plaintexts.append(candidate.entries.get(index));
                }
                combinedEntries.addAll(candidate.entries);
            }
            List<String> constructorNames = new ArrayList<>();
            boolean indexesValid = true;
            for (Integer index : nameIndexes) {
                if (index < 0 || index >= combinedEntries.size()) {
                    indexesValid = false;
                    break;
                }
                constructorNames.add(combinedEntries.get(index));
            }
            Set<String> selected = new LinkedHashSet<>(constructorNames);
            boolean constructorExact = indexesValid
                    && selected.size() == constructorNames.size()
                    && constructorNames.size() == names.size() && selected.equals(names);
            int matches = constructorExact ? 1 : 0;
            String reason = constructorExact ? "exact-enum-constructor-name-set"
                    : candidates.isEmpty() ? "outer-des-failed"
                    : !indexesValid ? "enum-name-index-out-of-range"
                    : "enum-constructor-name-set-mismatch";
            return new EnumCheck(candidates.size(), plaintexts.toString(), matches, reason);
        }
    }

    private static final class EnumCheck {
        final int tables;
        final String plaintexts;
        final int matches;
        final String reason;

        EnumCheck(int tables, String plaintexts, int matches, String reason) {
            this.tables = tables;
            this.plaintexts = plaintexts;
            this.matches = matches;
            this.reason = reason;
        }

        boolean passes() {
            return matches == 1;
        }
    }

    private static final class CandidateSet {
        final Map<Long, Set<String>> values = new LinkedHashMap<>();

        void add(long value, String source) {
            values.computeIfAbsent(value, ignored -> new LinkedHashSet<>()).add(source);
        }

        Long valueForSource(String source) {
            Long result = null;
            for (Map.Entry<Long, Set<String>> entry : values.entrySet()) {
                if (!entry.getValue().contains(source)) continue;
                if (result != null && result.longValue() != entry.getKey().longValue()) {
                    throw new IllegalStateException("multiple-values-for-source=" + source);
                }
                result = entry.getKey();
            }
            return result;
        }
    }

    private static final class ClassEvidence {
        final ClassNode owner;
        final ZkmMemberIndyDeobfuscator.ResolverModel model;
        final List<MemberSite> sites;
        final String failure;

        ClassEvidence(ClassNode owner, ZkmMemberIndyDeobfuscator.ResolverModel model,
                      List<MemberSite> sites) {
            this(owner, model, sites, null);
        }

        ClassEvidence(ClassNode owner, ZkmMemberIndyDeobfuscator.ResolverModel model,
                      List<MemberSite> sites, String failure) {
            this.owner = owner;
            this.model = model;
            this.sites = sites;
            this.failure = failure;
        }

        CandidateCheck check(long classKey) {
            CandidateCheck result = new CandidateCheck(sites.size());
            if (model == null) {
                result.reason = failure;
                return result;
            }
            for (MemberSite site : sites) {
                if (site.failure != null || site.first == null || site.second == null) {
                    if (result.reason == null) result.reason = site.failure;
                    continue;
                }
                long first;
                long second;
                try {
                    first = site.first.evaluate(classKey);
                    second = site.second.evaluate(classKey);
                    result.arguments++;
                } catch (Throwable failure) {
                    if (result.reason == null) result.reason = "arguments=" + shortReason(failure);
                    continue;
                }
                try {
                    ZkmMemberIndyDeobfuscator.ResolverModel fresh =
                            new ZkmMemberIndyDeobfuscator.ResolverModel(model.owner,
                                    model.symbols, model.decoded.clone(), model.offsets,
                                    model.selectors);
                    ZkmMemberIndyDeobfuscator.MemberTarget target =
                            fresh.resolve(site.indy.name, first, second);
                    if (!validMemberName(target.name)) {
                        throw new IllegalStateException("invalid-member-name");
                    }
                    result.decoded++;
                    String expected = expectedHandleDescriptor(target);
                    if (explicitCastCompatible(stripTrailingKeys(site.indy.desc), expected)) {
                        result.compatible++;
                    } else if (result.reason == null) {
                        result.reason = "descriptor=" + stripTrailingKeys(site.indy.desc)
                                + "!=" + expected;
                    }
                } catch (Throwable failure) {
                    if (result.reason == null) result.reason = "decode=" + shortReason(failure);
                }
            }
            if (result.reason == null && !result.passes()) result.reason = "partial-class-evidence";
            return result;
        }
    }

    private static final class CandidateCheck {
        final int sites;
        int arguments;
        int decoded;
        int compatible;
        String reason;

        CandidateCheck(int sites) {
            this.sites = sites;
        }

        boolean passes() {
            return sites != 0 && arguments == sites && decoded == sites && compatible == sites;
        }
    }

    private static final class MemberSite {
        final InvokeDynamicInsnNode indy;
        final Expression first;
        final Expression second;
        final String failure;

        MemberSite(InvokeDynamicInsnNode indy, Expression first, Expression second) {
            this(indy, first, second, null);
        }

        MemberSite(InvokeDynamicInsnNode indy, Expression first, Expression second,
                   String failure) {
            this.indy = indy;
            this.first = first;
            this.second = second;
            this.failure = failure;
        }

        static MemberSite failure(InvokeDynamicInsnNode indy, String reason) {
            return new MemberSite(indy, null, null, reason);
        }
    }

    private static final class MethodExpressions {
        final MethodNode method;
        final Frame<SourceValue>[] frames;
        final Map<AbstractInsnNode, Integer> indexes = new IdentityHashMap<>();
        final Set<String> keyFields;

        private MethodExpressions(ClassNode owner, MethodNode method,
                                  Frame<SourceValue>[] frames) {
            this.method = method;
            this.frames = frames;
            this.keyFields = keyFields(owner);
            int index = 0;
            for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
                 insn = insn.getNext(), index++) indexes.put(insn, index);
        }

        static MethodExpressions build(ClassNode owner, MethodNode method) throws Exception {
            Frame<SourceValue>[] frames = new Analyzer<SourceValue>(new SourceInterpreter())
                    .analyze(owner.name, method);
            return new MethodExpressions(owner, method, frames);
        }

        MemberSite site(InvokeDynamicInsnNode indy) {
            Integer index = indexes.get(indy);
            Frame<SourceValue> frame = index == null ? null : frames[index];
            if (frame == null || frame.getStackSize() < 2) {
                return MemberSite.failure(indy, "missing-site-frame");
            }
            AbstractInsnNode first = soleSource(frame.getStack(frame.getStackSize() - 2));
            AbstractInsnNode second = soleSource(frame.getStack(frame.getStackSize() - 1));
            if (first == null || second == null) {
                return MemberSite.failure(indy, "non-unique-tail-producers");
            }
            try {
                return new MemberSite(indy, expression(first, new HashSet<AbstractInsnNode>()),
                        expression(second, new HashSet<AbstractInsnNode>()));
            } catch (Throwable failure) {
                return MemberSite.failure(indy, "expression=" + shortReason(failure));
            }
        }

        private Expression expression(AbstractInsnNode end, Set<AbstractInsnNode> active) {
            if (end == null || !active.add(end)) {
                throw new IllegalStateException("expression-cycle");
            }
            try {
                Long value = constant(end);
                if (value != null) return Expression.constant(value, end);
                if (end instanceof FieldInsnNode && end.getOpcode() == Opcodes.GETSTATIC) {
                    FieldInsnNode field = (FieldInsnNode) end;
                    if ("J".equals(field.desc) && keyFields.contains(field.owner + "." + field.name)) {
                        return Expression.classKey(end);
                    }
                }
                if (end instanceof MethodInsnNode) {
                    MethodInsnNode call = (MethodInsnNode) end;
                    if (call.getOpcode() == Opcodes.INVOKEINTERFACE
                            && LONG_STATE.equals(call.owner) && "a".equals(call.name)
                            && "(J)J".equals(call.desc)) {
                        return Expression.classKey(end);
                    }
                }
                if (end instanceof VarInsnNode && end.getOpcode() == Opcodes.LLOAD) {
                    Integer index = indexes.get(end);
                    int local = ((VarInsnNode) end).var;
                    Frame<SourceValue> frame = index == null ? null : frames[index];
                    AbstractInsnNode store = frame == null || frame.getLocals() <= local ? null
                            : soleSource(frame.getLocal(local));
                    if (!(store instanceof VarInsnNode) || store.getOpcode() != Opcodes.LSTORE) {
                        throw new IllegalStateException("long-local-source");
                    }
                    return expression(previousCode(store), active).at(end);
                }
                int opcode = end.getOpcode();
                if (opcode == Opcodes.LXOR || opcode == Opcodes.LADD || opcode == Opcodes.LSUB
                        || opcode == Opcodes.LAND || opcode == Opcodes.LOR) {
                    Expression right = expression(previousCode(end), active);
                    Expression left = expression(previousCode(right.start), active);
                    return Expression.binary(opcode, left, right, end, left.start);
                }
                if (opcode == Opcodes.LNEG) {
                    Expression valueExpression = expression(previousCode(end), active);
                    return Expression.negate(valueExpression, end, valueExpression.start);
                }
                throw new IllegalStateException("unsupported-opcode=" + opcode);
            } finally {
                active.remove(end);
            }
        }

        private static AbstractInsnNode soleSource(SourceValue value) {
            return value == null || value.insns == null || value.insns.size() != 1
                    ? null : value.insns.iterator().next();
        }

        private static Set<String> keyFields(ClassNode owner) {
            Set<String> result = new HashSet<>();
            MethodNode clinit = null;
            for (MethodNode method : owner.methods) {
                if ("<clinit>".equals(method.name) && "()V".equals(method.desc)) clinit = method;
            }
            if (clinit == null) return result;
            for (AbstractInsnNode insn = clinit.instructions.getFirst(); insn != null;
                 insn = insn.getNext()) {
                if (!(insn instanceof FieldInsnNode) || insn.getOpcode() != Opcodes.PUTSTATIC) continue;
                FieldInsnNode field = (FieldInsnNode) insn;
                AbstractInsnNode value = previousCode(insn);
                if (owner.name.equals(field.owner) && "J".equals(field.desc)
                        && value instanceof MethodInsnNode
                        && value.getOpcode() == Opcodes.INVOKEINTERFACE
                        && LONG_STATE.equals(((MethodInsnNode) value).owner)
                        && "(J)J".equals(((MethodInsnNode) value).desc)) {
                    result.add(field.owner + "." + field.name);
                }
            }
            return result;
        }
    }

    private static final class Expression {
        final int opcode;
        final long constant;
        final Expression left;
        final Expression right;
        final AbstractInsnNode start;

        private Expression(int opcode, long constant, Expression left, Expression right,
                           AbstractInsnNode start) {
            this.opcode = opcode;
            this.constant = constant;
            this.left = left;
            this.right = right;
            this.start = start;
        }

        static Expression constant(long value, AbstractInsnNode start) {
            return new Expression(0, value, null, null, start);
        }

        static Expression classKey(AbstractInsnNode start) {
            return new Expression(-1, 0L, null, null, start);
        }

        static Expression binary(int opcode, Expression left, Expression right,
                                 AbstractInsnNode end, AbstractInsnNode start) {
            return new Expression(opcode, 0L, left, right, start);
        }

        static Expression negate(Expression value, AbstractInsnNode end,
                                 AbstractInsnNode start) {
            return new Expression(Opcodes.LNEG, 0L, value, null, start);
        }

        Expression at(AbstractInsnNode newStart) {
            return new Expression(opcode, constant, left, right, newStart);
        }

        long evaluate(long classKey) {
            if (opcode == 0) return constant;
            if (opcode == -1) return classKey;
            if (opcode == Opcodes.LNEG) return -left.evaluate(classKey);
            long leftValue = left.evaluate(classKey);
            long rightValue = right.evaluate(classKey);
            if (opcode == Opcodes.LXOR) return leftValue ^ rightValue;
            if (opcode == Opcodes.LADD) return leftValue + rightValue;
            if (opcode == Opcodes.LSUB) return leftValue - rightValue;
            if (opcode == Opcodes.LAND) return leftValue & rightValue;
            if (opcode == Opcodes.LOR) return leftValue | rightValue;
            throw new IllegalStateException("expression-opcode=" + opcode);
        }
    }
}
