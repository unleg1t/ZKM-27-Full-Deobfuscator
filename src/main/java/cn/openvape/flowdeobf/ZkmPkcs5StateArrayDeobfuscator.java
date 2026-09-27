package cn.openvape.flowdeobf;

import org.objectweb.asm.Opcodes;
import org.objectweb.asm.tree.ClassNode;
import org.objectweb.asm.tree.MethodNode;

import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.StandardOpenOption;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Restores local PKCS5 string tables whose DES key is derived from the ZKM
 * long-key state model.
 *
 * <p>The pass evaluates the long-key graph with ASM only, binds each selected
 * class key to the exact transform/XOR/local chain in {@code <clinit>}, and
 * delegates table, CFG, exception-boundary, consumer, and byte-decoder proofs
 * to {@link ZkmDirectStringArrayDeobfuscator}. Input classes are never defined,
 * loaded, or initialized.</p>
 */
public final class ZkmPkcs5StateArrayDeobfuscator {
    private static final String STATE =
            ObfRuntimeNames.STATE;
    private static final String GRAPH =
            ObfRuntimeNames.GRAPH_BOOTSTRAP;

    private ZkmPkcs5StateArrayDeobfuscator() {
    }

    public static void main(String[] args) throws Exception {
        if (args.length < 2 || args.length > 3) {
            System.err.println("usage: ZkmPkcs5StateArrayDeobfuscator "
                    + "<input.jar> <report-dir> [output.jar]");
            System.exit(2);
        }
        ZkmDirectStringArrayDeobfuscator.Summary summary = rewrite(
                Paths.get(args[0]), Paths.get(args[1]),
                args.length == 3 ? Paths.get(args[2]) : null);
        System.out.println("classes=" + summary.parsedClasses
                + " candidates=" + summary.pkcs5ClinitClasses
                + " proven=" + summary.provenCandidates
                + " strings=" + summary.provenStrings
                + " changed=" + summary.changedClasses
                + " rollbacks=" + summary.classRollbacks
                + " residual_pkcs5_clinit="
                + summary.outputPkcs5ClinitClasses
                + " output_committed=" + summary.outputCommitted);
    }

    static ZkmDirectStringArrayDeobfuscator.Summary rewrite(
            Path input, Path reportDirectory, Path output) throws Exception {
        Map<String, ClassNode> classes = ZkmLongKeyEvaluator.readClasses(input);
        Provenance provenance = classes.containsKey(STATE)
                && classes.containsKey(GRAPH)
                ? resolveProvenance(classes) : new Provenance();
        ZkmDirectStringArrayDeobfuscator.Summary summary =
                ZkmDirectStringArrayDeobfuscator.deobfuscateStateDerived(
                        input, reportDirectory, output, provenance.proofs);
        writeProvenance(reportDirectory, provenance);
        List<String> audit = new ArrayList<>();
        audit.add("long_key_sites=" + provenance.decisions.size());
        audit.add("validated_string_keys=" + provenance.validatedKeys);
        audit.add("jvm_initialization_chain_keys=" + provenance.chainKeys);
        audit.add("selected_key_proofs=" + provenance.proofs.size());
        audit.add("class_key_model_failures=0");
        audit.add("key_binding=state-transform/XOR/local-chain");
        audit.add("input_classes_loaded=false");
        audit.add("input_classes_initialized=false");
        Files.write(reportDirectory.resolve("audit.txt"), audit,
                StandardCharsets.UTF_8, StandardOpenOption.APPEND);
        return summary;
    }

    static ZkmDirectStringArrayDeobfuscator.Summary rewriteWithProofs(
            Path input, Path reportDirectory, Path output,
            Map<String, ZkmDirectStringArrayDeobfuscator.StateKeyProof> proofs)
            throws Exception {
        return ZkmDirectStringArrayDeobfuscator.deobfuscateStateDerived(
                input, reportDirectory, output, proofs);
    }

    static Map<String, ZkmDirectStringArrayDeobfuscator.StateKeyProof>
    resolveClassKeyProofs(Map<String, ClassNode> classes) {
        return new LinkedHashMap<>(resolveProvenance(classes).proofs);
    }

    private static Provenance resolveProvenance(
            Map<String, ClassNode> classes) {
        Map<String, Long> isolated =
                ZkmLongKeyEvaluator.evaluateClassKeys(classes);
        Map<String, Long> sequential =
                ZkmLongKeyEvaluator.evaluateClassKeysSequential(classes);
        Map<String, Long> validated;
        try {
            validated = ZkmStringDecryptor.solveValidatedClassKeys(classes);
        } catch (Throwable ignored) {
            validated = Collections.emptyMap();
        }

        ZkmLongKeyEvaluator.StatefulKeySequence sites =
                ZkmLongKeyEvaluator.newStatefulKeySequence(classes);
        Provenance result = new Provenance();
        result.validatedKeys = validated.size();
        for (String owner : sites.owners()) {
            ChainEvaluation chain = evaluateJvmInitializationChain(
                    classes, owner, sites);
            result.chainKeys++;
            Long trusted = validated.get(owner);
            long selected = trusted == null ? chain.classKey : trusted;
            String source;
            if (trusted != null) {
                source = trusted.longValue() == chain.classKey
                        ? "validated-string-table+jvm-init-chain"
                        : "validated-string-table";
            } else {
                Long isolatedKey = isolated.get(owner);
                source = isolatedKey != null
                        && isolatedKey.longValue() == chain.classKey
                        ? "isolated+jvm-init-chain-agree"
                        : "jvm-init-chain-static-model";
            }
            String chainText = String.join(">", chain.committedOwners);
            result.proofs.put(owner,
                    new ZkmDirectStringArrayDeobfuscator.StateKeyProof(
                            owner, selected, source, chainText));
            result.decisions.add(new KeyDecision(owner, selected, trusted,
                    isolated.get(owner), sequential.get(owner), chain.classKey,
                    source, chainText));
        }
        return result;
    }

    private static ChainEvaluation evaluateJvmInitializationChain(
            Map<String, ClassNode> classes, String owner,
            ZkmLongKeyEvaluator.StatefulKeySequence base) {
        ZkmLongKeyEvaluator.StatefulKeySequence sequence = base.copy();
        List<String> initializationOrder = new ArrayList<>();
        collectInitializationOrder(owner, classes, new HashSet<String>(),
                new HashSet<String>(), initializationOrder);
        ChainEvaluation result = new ChainEvaluation();
        boolean selected = false;
        for (String current : initializationOrder) {
            if (!sequence.hasSite(current)) continue;
            long key = sequence.commit(current);
            result.committedOwners.add(current);
            if (owner.equals(current)) {
                result.classKey = key;
                selected = true;
            }
        }
        if (!selected) {
            throw new IllegalStateException("no long-key site for " + owner);
        }
        return result;
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
                && owner.superName != null
                && classes.containsKey(owner.superName)) {
            collectInitializationOrder(owner.superName, classes, visited,
                    active, result);
        }
        if (owner != null) {
            for (String iface : owner.interfaces) {
                if (declaresOrInheritsDefaultMethod(iface, classes,
                        new LinkedHashSet<String>())) {
                    collectInitializationOrder(iface, classes, visited,
                            active, result);
                }
            }
        }
        active.remove(name);
        visited.add(name);
        result.add(name);
    }

    private static boolean declaresOrInheritsDefaultMethod(
            String name, Map<String, ClassNode> classes,
            Set<String> visited) {
        if (!visited.add(name)) return false;
        ClassNode owner = classes.get(name);
        if (owner == null
                || (owner.access & Opcodes.ACC_INTERFACE) == 0) return false;
        for (MethodNode method : owner.methods) {
            if ("<clinit>".equals(method.name)
                    || "<init>".equals(method.name)) continue;
            if ((method.access & (Opcodes.ACC_ABSTRACT | Opcodes.ACC_STATIC))
                    == 0) return true;
        }
        for (String parent : owner.interfaces) {
            if (declaresOrInheritsDefaultMethod(parent, classes, visited)) {
                return true;
            }
        }
        return false;
    }

    private static void writeProvenance(
            Path reportDirectory, Provenance provenance) throws Exception {
        List<String> rows = new ArrayList<>();
        rows.add("class\tselected_key_hex\tvalidated_key_hex"
                + "\tisolated_key_hex\tarchive_sequential_key_hex"
                + "\tjvm_init_chain_key_hex\tsource\tcommitted_key_owners");
        for (KeyDecision decision : provenance.decisions) {
            rows.add(decision.row());
        }
        Files.write(reportDirectory.resolve("key-provenance.tsv"), rows,
                StandardCharsets.UTF_8);
    }

    private static String hex(Long value) {
        return value == null ? "" : String.format("%016X", value);
    }

    private static String tsv(Object... values) {
        List<String> cells = new ArrayList<>();
        for (Object value : values) {
            cells.add(String.valueOf(value).replace('\t', ' ')
                    .replace('\r', ' ').replace('\n', ' '));
        }
        return String.join("\t", cells);
    }

    private static final class Provenance {
        final Map<String, ZkmDirectStringArrayDeobfuscator.StateKeyProof>
                proofs = new LinkedHashMap<>();
        final List<KeyDecision> decisions = new ArrayList<>();
        int validatedKeys;
        int chainKeys;
    }

    private static final class ChainEvaluation {
        long classKey;
        final List<String> committedOwners = new ArrayList<>();
    }

    private static final class KeyDecision {
        final String owner;
        final long selected;
        final Long validated;
        final Long isolated;
        final Long sequential;
        final long chain;
        final String source;
        final String committedOwners;

        KeyDecision(String owner, long selected, Long validated,
                    Long isolated, Long sequential, long chain,
                    String source, String committedOwners) {
            this.owner = owner;
            this.selected = selected;
            this.validated = validated;
            this.isolated = isolated;
            this.sequential = sequential;
            this.chain = chain;
            this.source = source;
            this.committedOwners = committedOwners;
        }

        String row() {
            return tsv(owner, hex(selected), hex(validated), hex(isolated),
                    hex(sequential), hex(chain), source, committedOwners);
        }
    }
}
