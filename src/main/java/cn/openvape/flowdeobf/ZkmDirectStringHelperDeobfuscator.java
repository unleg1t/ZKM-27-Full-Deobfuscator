package cn.openvape.flowdeobf;

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
import org.objectweb.asm.tree.InsnList;
import org.objectweb.asm.tree.InsnNode;
import org.objectweb.asm.tree.IntInsnNode;
import org.objectweb.asm.tree.InvokeDynamicInsnNode;
import org.objectweb.asm.tree.JumpInsnNode;
import org.objectweb.asm.tree.LabelNode;
import org.objectweb.asm.tree.LdcInsnNode;
import org.objectweb.asm.tree.MethodInsnNode;
import org.objectweb.asm.tree.MethodNode;
import org.objectweb.asm.tree.TypeInsnNode;
import org.objectweb.asm.tree.TryCatchBlockNode;
import org.objectweb.asm.tree.VarInsnNode;
import org.objectweb.asm.tree.analysis.Analyzer;
import org.objectweb.asm.tree.analysis.BasicVerifier;
import org.objectweb.asm.tree.analysis.Frame;
import org.objectweb.asm.tree.analysis.SourceInterpreter;
import org.objectweb.asm.tree.analysis.SourceValue;
import org.objectweb.asm.util.CheckClassAdapter;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.AtomicMoveNotSupportedException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.StandardCopyOption;
import java.security.MessageDigest;
import java.util.ArrayDeque;
import java.util.ArrayList;
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
import java.util.zip.CRC32;
import java.util.zip.ZipEntry;
import java.util.zip.ZipInputStream;
import java.util.zip.ZipOutputStream;

/**
 * Restores the field-backed ZKM two-layer PKCS5 string family.
 *
 * <p>The accepted family has one closed outer packed {@code String[]} table
 * initializer and one private static {@code (IJ)String} delayed decoder. The
 * outer table proof is shared with {@link ZkmDirectStringArrayDeobfuscator};
 * this pass additionally proves the inner index formula, every live helper
 * reference, and both constant arguments at every live call. Obsolete ZKM
 * bootstrap adapters may be removed only as a private, signature-matched
 * method subgraph with no inbound edge from outside that subgraph.</p>
 *
 * <p>No input class is defined or initialized. All DES evaluation is applied
 * only to constants whose bytecode provenance has been proven.</p>
 */
public final class ZkmDirectStringHelperDeobfuscator {
    private static final String PKCS5 = "DES/CBC/PKCS5Padding";
    private static final String HELPER_DESC = "(IJ)Ljava/lang/String;";
    private static final String BYTE_DECODER_DESC = "([B)Ljava/lang/String;";
    private static final String ADAPTER_DESC = "(Ljava/lang/invoke/MethodHandles$Lookup;"
            + "Ljava/lang/invoke/MutableCallSite;Ljava/lang/String;[Ljava/lang/Object;)"
            + "Ljava/lang/Object;";
    private static final String BOOTSTRAP_DESC = "(Ljava/lang/invoke/MethodHandles$Lookup;"
            + "Ljava/lang/String;Ljava/lang/invoke/MethodType;)Ljava/lang/invoke/CallSite;";

    private ZkmDirectStringHelperDeobfuscator() {
    }

    public static void main(String[] args) throws Exception {
        if (args.length != 2 && args.length != 3) {
            System.err.println("usage: ZkmDirectStringHelperDeobfuscator"
                    + " <input.jar> <report-dir> [output.jar]");
            System.exit(2);
        }
        Summary summary = rewrite(Paths.get(args[0]), Paths.get(args[1]),
                args.length == 3 ? Paths.get(args[2]) : null);
        System.out.println("field_tables=" + summary.fieldTableCandidates
                + " proven=" + summary.provenClasses
                + " sites=" + summary.provenSites
                + " changed=" + summary.changedClasses
                + " pkcs5_removed=" + summary.pkcs5CallsRemoved
                + " rollbacks=" + summary.classRollbacks
                + " gate=" + (summary.gatePass ? "PASS" : "FAIL"));
    }

    static Summary rewrite(Path input, Path reportDirectory, Path output)
            throws Exception {
        return rewrite(input, reportDirectory, output,
                Collections.<String, StateHelperProof>emptyMap());
    }

    static Summary rewriteWithStateProofs(
            Path input, Path reportDirectory, Path output,
            Map<String, StateHelperProof> proofs) throws Exception {
        return rewrite(input, reportDirectory, output, proofs);
    }

    private static Summary rewrite(
            Path input, Path reportDirectory, Path output,
            Map<String, StateHelperProof> proofs) throws Exception {
        validatePaths(input, output);
        Files.createDirectories(reportDirectory);
        List<EntryBytes> entries = readEntries(input);
        Map<String, byte[]> originalBytes = classBytes(entries);
        Map<String, ClassNode> classes = readClasses(originalBytes);
        List<ReferenceEdge> edges = referenceEdges(classes);
        Summary summary = new Summary();
        summary.parsedClasses = classes.size();
        summary.inputPkcs5Calls = countPkcs5(classes);
        summary.outputRequested = output != null;
        List<Candidate> candidates = new ArrayList<>();
        Map<String, byte[]> replacements = new LinkedHashMap<>();
        List<String> verifier = new ArrayList<>();
        verifier.add("scope\tclass\tstatus\treason");
        ZkmClassRewriteTransaction.Emitter emitter =
                ZkmDirectStringArrayDeobfuscator.archiveEmitter(classes);

        for (Map.Entry<String, byte[]> entry : originalBytes.entrySet()) {
            ClassNode owner = classes.get(entry.getKey());
            Candidate candidate = inspect(owner, classes, edges, summary,
                    proofs.get(owner.name));
            if (candidate == null) continue;
            candidates.add(candidate);
            if (!candidate.proven()) continue;
            summary.provenClasses++;
            summary.provenSites += candidate.liveSites.size();
            summary.provenStrings += candidate.plaintexts.size();
            summary.deadBootstrapMethods += candidate.deadSupport.size();
            if (output == null) {
                candidate.action = "PROVEN_DRY_RUN";
                continue;
            }
            ZkmClassRewriteTransaction.Result transaction =
                    ZkmClassRewriteTransaction.attempt(entry.getValue(),
                            mutable -> apply(mutable, candidate),
                            emitted -> assertRewritten(emitted, candidate), emitter);
            if (transaction.isCommitted()) {
                replacements.put(owner.name, transaction.bytes());
                candidate.action = "REWRITE";
                summary.changedClasses++;
                summary.rewrittenSites += candidate.liveSites.size();
                summary.helpersRemoved++;
                summary.outerTablesRewritten++;
                summary.byteDecodersRemoved += candidate.removeByteDecoder ? 1 : 0;
                verifier.add(tsv("class-transaction", owner.name, "PASS", ""));
            } else {
                candidate.action = "ROLLBACK";
                candidate.reason = append(candidate.reason,
                        transaction.stage() + ":" + transaction.reason());
                summary.classRollbacks++;
                verifier.add(tsv("class-transaction", owner.name, "ROLLBACK",
                        transaction.stage() + ":" + transaction.reason()));
            }
        }

        if (output != null) {
            writeVerifiedArchive(entries, replacements, output, summary, verifier);
        } else {
            summary.outputPkcs5Calls = summary.inputPkcs5Calls;
        }
        summary.pkcs5CallsRemoved = output == null ? summary.provenClasses * 2
                : summary.inputPkcs5Calls - summary.outputPkcs5Calls;
        summary.integrityPass = summary.classRollbacks == 0
                && summary.outputVerificationErrors == 0
                && (!summary.outputRequested || summary.outputCommitted);
        summary.gatePass = summary.integrityPass && summary.provenClasses > 0;
        writeReports(input, reportDirectory, output, summary, candidates, verifier);
        return summary;
    }

    private static Candidate inspect(ClassNode owner,
                                     Map<String, ClassNode> classes,
                                     List<ReferenceEdge> edges,
                                     Summary summary,
                                     StateHelperProof stateProof) {
        List<HelperSpec> helpers = new ArrayList<>();
        for (MethodNode method : owner.methods) {
            if (!HELPER_DESC.equals(method.desc) || !containsPkcs5(method)) continue;
            HelperSpec spec = inspectHelper(owner, method);
            if (spec != null) helpers.add(spec);
        }
        if (helpers.isEmpty()) return null;
        summary.fieldTableCandidates++;
        Candidate candidate = new Candidate(owner.name);
        if (helpers.size() != 1) {
            return candidate.reject("helper-count=" + helpers.size());
        }
        candidate.helper = helpers.get(0);
        if (countPkcs5(owner) != 2) {
            return candidate.reject("owner-pkcs5-count=" + countPkcs5(owner));
        }
        if (stateProof != null && !owner.name.equals(stateProof.owner)) {
            return candidate.reject("state-proof-owner=" + stateProof.owner);
        }
        if (stateProof != null && !stateProof.outerEntries.isEmpty()) {
            if (!candidate.helper.tableField.equals(stateProof.tableField)) {
                return candidate.reject("state-table-field="
                        + stateProof.tableField + "/"
                        + candidate.helper.tableField);
            }
            candidate.table = new OuterTableProof(stateProof.tableField,
                    stateProof.outerEntries.size(), stateProof.outerKey,
                    stateProof.outerEntries, null, null);
        } else {
            candidate.table = inspectOuterTable(owner,
                    candidate.helper.tableField,
                    stateProof == null ? null : stateProof.outerKey);
        }
        if (candidate.table == null) {
            return candidate.reject("outer-table-not-proven");
        }

        List<DirectSite> allSites = directSites(owner, candidate.helper);
        if (allSites.isEmpty()) return candidate.reject("helper-has-no-direct-sites");
        Set<MethodRef> unresolvedRoots = new LinkedHashSet<>();
        Map<MethodNode, Frame<SourceValue>[]> frames = new IdentityHashMap<>();
        for (DirectSite site : allSites) {
            Arguments arguments = resolveArguments(owner, site, frames,
                    stateProof == null
                            ? Collections.<String, Long>emptyMap()
                            : stateProof.staticLongs);
            if (arguments == null) {
                unresolvedRoots.add(new MethodRef(owner.name,
                        site.method.name, site.method.desc));
                continue;
            }
            site.callInt = arguments.intValue;
            site.callLong = arguments.longValue;
        }

        Set<MethodRef> support = proveDeadSupport(owner, candidate.helper,
                unresolvedRoots, edges);
        if (support == null) {
            return candidate.reject("unresolved-live-helper-sites="
                    + unresolvedRoots.size());
        }
        candidate.deadSupport.addAll(support);
        for (DirectSite site : allSites) {
            MethodRef source = new MethodRef(owner.name,
                    site.method.name, site.method.desc);
            if (support.contains(source)) continue;
            if (site.callInt == null || site.callLong == null) {
                return candidate.reject("unresolved-site=" + site.id());
            }
            candidate.liveSites.add(site);
        }
        MethodRef helperRef = new MethodRef(owner.name,
                candidate.helper.method.name, HELPER_DESC);
        Set<MethodInsnNode> liveNodes = Collections.newSetFromMap(
                new IdentityHashMap<MethodInsnNode, Boolean>());
        for (DirectSite site : candidate.liveSites) liveNodes.add(site.node);
        for (ReferenceEdge edge : edges) {
            if (!helperRef.equals(edge.target)) continue;
            if (support.contains(edge.source)) continue;
            if (!edge.direct || !liveNodes.contains(edge.call)) {
                return candidate.reject("non-direct-live-helper-reference="
                        + edge.source);
            }
        }

        for (DirectSite site : candidate.liveSites) {
            int index = site.callInt
                    ^ (int) (site.callLong & candidate.helper.indexMask)
                    ^ candidate.helper.indexXor;
            site.tableIndex = index;
            if (index < 0 || index >= candidate.table.encryptedEntries.size()) {
                return candidate.reject("table-index=" + index + "/"
                        + candidate.table.encryptedEntries.size() + "@" + site.id());
            }
            try {
                site.plaintext = ZkmDesConstantEvaluator.decryptZkmString(
                        ZkmDesConstantEvaluator.KeyMaterial.proven(site.callLong,
                                "DIRECT_HELPER_ARGUMENT", site.id()),
                        candidate.table.encryptedEntries.get(index));
            } catch (Throwable failure) {
                return candidate.reject("inner-decrypt=" + shortReason(failure)
                        + "@" + site.id());
            }
            candidate.plaintexts.add(site.plaintext);
        }
        candidate.removeByteDecoder = byteDecoderReferencesAfterRewrite(owner,
                candidate) == 0;
        candidate.action = "PROVEN";
        return candidate;
    }

    private static HelperSpec inspectHelper(ClassNode owner, MethodNode method) {
        if ((method.access & (Opcodes.ACC_PRIVATE | Opcodes.ACC_STATIC))
                != (Opcodes.ACC_PRIVATE | Opcodes.ACC_STATIC)) return null;
        String tableField = ciphertextTableField(owner, method);
        if (tableField == null) return null;
        int factories = 0, doFinal = 0, init = 0, tableReads = 0;
        int keyFactories = 0, desKeySpecs = 0, generatedKeys = 0;
        int ivSpecs = 0, latin1Reads = 0, decoderCalls = 0;
        int byteArrays = 0, byteStores = 0, lushr = 0, lshl = 0, imul = 0;
        int keyParameterLoads = 0;
        Set<Long> masks = new LinkedHashSet<>();
        Set<Integer> xors = new LinkedHashSet<>();
        for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
             insn = insn.getNext()) {
            if (isCipherFactory(insn, PKCS5)) factories++;
            if (isCall(insn, Opcodes.INVOKEVIRTUAL, "javax/crypto/Cipher",
                    "doFinal", "([B)[B")) doFinal++;
            if (isCall(insn, Opcodes.INVOKEVIRTUAL, "javax/crypto/Cipher",
                    "init", "(ILjava/security/Key;"
                            + "Ljava/security/spec/AlgorithmParameterSpec;)V")) init++;
            if (isCall(insn, Opcodes.INVOKESTATIC,
                    "javax/crypto/SecretKeyFactory", "getInstance",
                    "(Ljava/lang/String;)Ljavax/crypto/SecretKeyFactory;")) {
                keyFactories++;
            }
            if (isCall(insn, Opcodes.INVOKESPECIAL,
                    "javax/crypto/spec/DESKeySpec", "<init>", "([B)V")) {
                desKeySpecs++;
            }
            if (isCall(insn, Opcodes.INVOKEVIRTUAL,
                    "javax/crypto/SecretKeyFactory", "generateSecret",
                    "(Ljava/security/spec/KeySpec;)Ljavax/crypto/SecretKey;")) {
                generatedKeys++;
            }
            if (isCall(insn, Opcodes.INVOKESPECIAL,
                    "javax/crypto/spec/IvParameterSpec", "<init>", "([B)V")) {
                ivSpecs++;
            }
            if (isCall(insn, Opcodes.INVOKEVIRTUAL, "java/lang/String",
                    "getBytes", "(Ljava/lang/String;)[B")) latin1Reads++;
            if (insn instanceof MethodInsnNode) {
                MethodInsnNode call = (MethodInsnNode) insn;
                if (call.getOpcode() == Opcodes.INVOKESTATIC
                        && owner.name.equals(call.owner)
                        && BYTE_DECODER_DESC.equals(call.desc)) decoderCalls++;
            }
            if (insn instanceof IntInsnNode && insn.getOpcode() == Opcodes.NEWARRAY
                    && ((IntInsnNode) insn).operand == Opcodes.T_BYTE) byteArrays++;
            if (insn.getOpcode() == Opcodes.BASTORE) byteStores++;
            if (insn.getOpcode() == Opcodes.LUSHR) lushr++;
            if (insn.getOpcode() == Opcodes.LSHL) lshl++;
            if (insn.getOpcode() == Opcodes.IMUL) imul++;
            if (insn instanceof VarInsnNode && insn.getOpcode() == Opcodes.LLOAD
                    && ((VarInsnNode) insn).var == 1) keyParameterLoads++;
            if (insn instanceof FieldInsnNode) {
                FieldInsnNode field = (FieldInsnNode) insn;
                if (field.getOpcode() == Opcodes.GETSTATIC
                        && owner.name.equals(field.owner)
                        && tableField.equals(field.name)
                        && "[Ljava/lang/String;".equals(field.desc)) tableReads++;
            }
            if (insn.getOpcode() == Opcodes.LAND) {
                Long value = longConstant(previousCode(insn));
                if (value != null) masks.add(value);
            } else if (insn.getOpcode() == Opcodes.IXOR) {
                Integer value = intConstant(previousCode(insn));
                if (value != null) xors.add(value);
            }
        }
        if (factories != 1 || doFinal != 1 || init != 1 || tableReads != 1
                || keyFactories != 1 || desKeySpecs != 1 || generatedKeys != 1
                || ivSpecs != 1 || latin1Reads != 1 || decoderCalls != 1
                || byteArrays != 2 || byteStores != 2 || lushr != 2
                || lshl != 1 || imul != 1 || keyParameterLoads < 3
                || masks.size() != 1 || xors.size() != 1) return null;
        String decoder = byteDecoderName(owner, method);
        if (!ZkmDirectStringArrayDeobfuscator.isExactByteDecoder(owner, decoder)) {
            return null;
        }
        return new HelperSpec(method, masks.iterator().next(),
                xors.iterator().next(), tableField, decoder);
    }

    private static String ciphertextTableField(ClassNode owner,
                                               MethodNode method) {
        Set<String> result = new LinkedHashSet<>();
        for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
             insn = insn.getNext()) {
            if (!(insn instanceof FieldInsnNode) || insn.getOpcode() != Opcodes.GETSTATIC) {
                continue;
            }
            FieldInsnNode field = (FieldInsnNode) insn;
            if (!owner.name.equals(field.owner)
                    || !"[Ljava/lang/String;".equals(field.desc)) continue;
            AbstractInsnNode cursor = insn;
            for (int scanned = 0; cursor != null && scanned < 10; scanned++) {
                cursor = nextCode(cursor);
                if (isCall(cursor, Opcodes.INVOKEVIRTUAL, "java/lang/String",
                        "getBytes", "(Ljava/lang/String;)[B")) {
                    result.add(field.name);
                    break;
                }
                if (cursor instanceof FieldInsnNode) break;
            }
        }
        return result.size() == 1 ? result.iterator().next() : null;
    }

    private static String byteDecoderName(ClassNode owner, MethodNode method) {
        Set<String> result = new LinkedHashSet<>();
        for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
             insn = insn.getNext()) {
            if (!(insn instanceof MethodInsnNode)) continue;
            MethodInsnNode call = (MethodInsnNode) insn;
            if (call.getOpcode() == Opcodes.INVOKESTATIC
                    && owner.name.equals(call.owner)
                    && BYTE_DECODER_DESC.equals(call.desc)) result.add(call.name);
        }
        return result.size() == 1 ? result.iterator().next() : null;
    }

    private static OuterTableProof inspectOuterTable(ClassNode owner,
                                                     String tableField) {
        return inspectOuterTable(owner, tableField, null);
    }

    private static OuterTableProof inspectOuterTable(ClassNode owner,
                                                     String tableField,
                                                     Long provenOuterKey) {
        MethodNode clinit = method(owner, "<clinit>", "()V");
        if (clinit == null) return null;
        ZkmStringDecryptor.TableLayout layout =
                ZkmStringDecryptor.tableLayout(owner, clinit, tableField);
        if (layout == null) return null;
        AbstractInsnNode factory = null;
        for (AbstractInsnNode insn = clinit.instructions.getFirst(); insn != null;
             insn = insn.getNext()) {
            if (!isCipherFactory(insn, PKCS5)) continue;
            if (factory != null) return null;
            factory = insn;
        }
        if (factory == null) return null;
        AbstractInsnNode start = previousCode(factory);
        int startIndex = clinit.instructions.indexOf(start);
        int allocationIndex = clinit.instructions.indexOf(layout.allocationStore);
        if (startIndex < 0 || allocationIndex <= startIndex) return null;
        long key;
        if (provenOuterKey == null) {
            Set<Long> keys = new LinkedHashSet<>();
            int keyLoads = 0;
            for (AbstractInsnNode insn = start; insn != null
                    && clinit.instructions.indexOf(insn) <= allocationIndex;
                 insn = insn.getNext()) {
                if (insn instanceof LdcInsnNode
                        && ((LdcInsnNode) insn).cst instanceof Long) {
                    keys.add((Long) ((LdcInsnNode) insn).cst);
                    keyLoads++;
                }
            }
            if (keys.size() != 1 || keyLoads < 2) return null;
            key = keys.iterator().next();
        } else {
            key = provenOuterKey.longValue();
        }
        List<ZkmStringDecryptor.TableCandidate> candidates =
                ZkmStringDecryptor.outerCandidates(clinit, key, layout);
        if (candidates.size() != 1) return null;
        ZkmStringDecryptor.TableCandidate table = candidates.get(0);
        if (table.entries.size() != layout.expectedEntries) return null;
        return new OuterTableProof(tableField, layout.expectedEntries, key,
                table.entries, start, layout.tableStore);
    }

    private static List<DirectSite> directSites(ClassNode owner,
                                                HelperSpec helper) {
        List<DirectSite> result = new ArrayList<>();
        for (MethodNode method : owner.methods) {
            if (method == helper.method) continue;
            int instruction = 0;
            int ordinal = 0;
            for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
                 insn = insn.getNext(), instruction++) {
                if (!(insn instanceof MethodInsnNode)) continue;
                MethodInsnNode call = (MethodInsnNode) insn;
                if (call.getOpcode() == Opcodes.INVOKESTATIC
                        && owner.name.equals(call.owner)
                        && helper.method.name.equals(call.name)
                        && HELPER_DESC.equals(call.desc)) {
                    result.add(new DirectSite(method, call, instruction, ordinal++));
                }
            }
        }
        return result;
    }

    private static Arguments resolveArguments(ClassNode owner, DirectSite site,
                                              Map<MethodNode,
                                                      Frame<SourceValue>[]> cache,
                                              Map<String, Long> staticLongs) {
        try {
            Frame<SourceValue>[] frames = cache.get(site.method);
            if (frames == null) {
                frames = new Analyzer<>(new SourceInterpreter()).analyze(
                        owner.name, site.method);
                cache.put(site.method, frames);
            }
            int index = site.method.instructions.indexOf(site.node);
            if (index < 0 || index >= frames.length) return null;
            Frame<SourceValue> frame = frames[index];
            if (frame == null || frame.getStackSize() < 2) return null;
            SourceValue intSource = frame.getStack(frame.getStackSize() - 2);
            SourceValue longSource = frame.getStack(frame.getStackSize() - 1);
            if (intSource == null || longSource == null
                    || intSource.getSize() != 1 || longSource.getSize() != 2
                    || intSource.insns.size() != 1
                    || longSource.insns.size() != 1) return null;
            Integer intValue = evalInt(intSource.insns.iterator().next(),
                    site.method, owner, new HashSet<AbstractInsnNode>(),
                    staticLongs);
            Long longValue = evalLong(longSource.insns.iterator().next(),
                    site.method, owner, new HashSet<AbstractInsnNode>(),
                    staticLongs);
            return intValue == null || longValue == null ? null
                    : new Arguments(intValue, longValue);
        } catch (Throwable failure) {
            return null;
        }
    }

    private static Integer evalInt(AbstractInsnNode end, MethodNode method,
                                   ClassNode owner,
                                   Set<AbstractInsnNode> active,
                                   Map<String, Long> staticLongs) {
        if (end == null || !active.add(end)) return null;
        try {
            Integer constant = intConstant(end);
            if (constant != null) return constant;
            if (end instanceof FieldInsnNode && end.getOpcode() == Opcodes.GETSTATIC) {
                Number value = constantField(owner, (FieldInsnNode) end, "I",
                        staticLongs);
                return value == null ? null : value.intValue();
            }
            if (end instanceof VarInsnNode && end.getOpcode() == Opcodes.ILOAD) {
                AbstractInsnNode store = uniqueStoreBefore(method, end,
                        ((VarInsnNode) end).var, Opcodes.ISTORE);
                return store == null ? null : evalInt(previousCode(store), method,
                        owner, active, staticLongs);
            }
            int opcode = end.getOpcode();
            if (opcode == Opcodes.IXOR || opcode == Opcodes.IAND
                    || opcode == Opcodes.IOR || opcode == Opcodes.IADD
                    || opcode == Opcodes.ISUB || opcode == Opcodes.IMUL) {
                AbstractInsnNode rightEnd = previousCode(end);
                Integer right = evalInt(rightEnd, method, owner, active,
                        staticLongs);
                AbstractInsnNode leftEnd = expressionStartInt(rightEnd, method,
                        owner);
                Integer left = leftEnd == null ? null : evalInt(
                        previousCode(leftEnd), method, owner, active,
                        staticLongs);
                if (left == null || right == null) return null;
                if (opcode == Opcodes.IXOR) return left ^ right;
                if (opcode == Opcodes.IAND) return left & right;
                if (opcode == Opcodes.IOR) return left | right;
                if (opcode == Opcodes.IADD) return left + right;
                if (opcode == Opcodes.ISUB) return left - right;
                return left * right;
            }
            if (opcode == Opcodes.INEG) {
                Integer value = evalInt(previousCode(end), method, owner, active,
                        staticLongs);
                return value == null ? null : -value;
            }
            if (opcode == Opcodes.L2I) {
                Long value = evalLong(previousCode(end), method, owner,
                        new HashSet<AbstractInsnNode>(), staticLongs);
                return value == null ? null : value.intValue();
            }
            return null;
        } finally {
            active.remove(end);
        }
    }

    private static Long evalLong(AbstractInsnNode end, MethodNode method,
                                 ClassNode owner,
                                 Set<AbstractInsnNode> active,
                                 Map<String, Long> staticLongs) {
        if (end == null || !active.add(end)) return null;
        try {
            Long constant = longConstant(end);
            if (constant != null) return constant;
            if (end instanceof FieldInsnNode && end.getOpcode() == Opcodes.GETSTATIC) {
                Number value = constantField(owner, (FieldInsnNode) end, "J",
                        staticLongs);
                return value == null ? null : value.longValue();
            }
            if (end instanceof VarInsnNode && end.getOpcode() == Opcodes.LLOAD) {
                AbstractInsnNode store = uniqueStoreBefore(method, end,
                        ((VarInsnNode) end).var, Opcodes.LSTORE);
                return store == null ? null : evalLong(previousCode(store), method,
                        owner, active, staticLongs);
            }
            int opcode = end.getOpcode();
            if (opcode == Opcodes.LXOR || opcode == Opcodes.LAND
                    || opcode == Opcodes.LOR || opcode == Opcodes.LADD
                    || opcode == Opcodes.LSUB || opcode == Opcodes.LMUL) {
                AbstractInsnNode rightEnd = previousCode(end);
                Long right = evalLong(rightEnd, method, owner, active,
                        staticLongs);
                AbstractInsnNode leftEnd = expressionStartLong(rightEnd, method,
                        owner);
                Long left = leftEnd == null ? null : evalLong(
                        previousCode(leftEnd), method, owner, active,
                        staticLongs);
                if (left == null || right == null) return null;
                if (opcode == Opcodes.LXOR) return left ^ right;
                if (opcode == Opcodes.LAND) return left & right;
                if (opcode == Opcodes.LOR) return left | right;
                if (opcode == Opcodes.LADD) return left + right;
                if (opcode == Opcodes.LSUB) return left - right;
                return left * right;
            }
            if (opcode == Opcodes.LNEG) {
                Long value = evalLong(previousCode(end), method, owner, active,
                        staticLongs);
                return value == null ? null : -value;
            }
            if (opcode == Opcodes.I2L) {
                Integer value = evalInt(previousCode(end), method, owner,
                        new HashSet<AbstractInsnNode>(), staticLongs);
                return value == null ? null : value.longValue();
            }
            return null;
        } finally {
            active.remove(end);
        }
    }

    /* Returns the first instruction in a proven adjacent integer expression. */
    private static AbstractInsnNode expressionStartInt(AbstractInsnNode end,
                                                       MethodNode method,
                                                       ClassNode owner) {
        if (end == null) return null;
        if (intConstant(end) != null || end instanceof FieldInsnNode) return end;
        if (end instanceof VarInsnNode && end.getOpcode() == Opcodes.ILOAD) return end;
        int opcode = end.getOpcode();
        if (opcode == Opcodes.INEG || opcode == Opcodes.L2I) {
            AbstractInsnNode child = previousCode(end);
            return opcode == Opcodes.INEG ? expressionStartInt(child, method, owner)
                    : expressionStartLong(child, method, owner);
        }
        if (opcode == Opcodes.IXOR || opcode == Opcodes.IAND
                || opcode == Opcodes.IOR || opcode == Opcodes.IADD
                || opcode == Opcodes.ISUB || opcode == Opcodes.IMUL) {
            AbstractInsnNode right = previousCode(end);
            AbstractInsnNode rightStart = expressionStartInt(right, method, owner);
            return rightStart == null ? null
                    : expressionStartInt(previousCode(rightStart), method, owner);
        }
        return null;
    }

    private static AbstractInsnNode expressionStartLong(AbstractInsnNode end,
                                                        MethodNode method,
                                                        ClassNode owner) {
        if (end == null) return null;
        if (longConstant(end) != null || end instanceof FieldInsnNode) return end;
        if (end instanceof VarInsnNode && end.getOpcode() == Opcodes.LLOAD) return end;
        int opcode = end.getOpcode();
        if (opcode == Opcodes.LNEG || opcode == Opcodes.I2L) {
            AbstractInsnNode child = previousCode(end);
            return opcode == Opcodes.LNEG ? expressionStartLong(child, method, owner)
                    : expressionStartInt(child, method, owner);
        }
        if (opcode == Opcodes.LXOR || opcode == Opcodes.LAND
                || opcode == Opcodes.LOR || opcode == Opcodes.LADD
                || opcode == Opcodes.LSUB || opcode == Opcodes.LMUL) {
            AbstractInsnNode right = previousCode(end);
            AbstractInsnNode rightStart = expressionStartLong(right, method, owner);
            return rightStart == null ? null
                    : expressionStartLong(previousCode(rightStart), method, owner);
        }
        return null;
    }

    private static AbstractInsnNode uniqueStoreBefore(MethodNode method,
                                                      AbstractInsnNode load,
                                                      int local, int opcode) {
        AbstractInsnNode found = null;
        for (AbstractInsnNode cursor = method.instructions.getFirst();
             cursor != null && cursor != load; cursor = cursor.getNext()) {
            if (cursor instanceof VarInsnNode && cursor.getOpcode() == opcode
                    && ((VarInsnNode) cursor).var == local) {
                if (found != null) return null;
                found = cursor;
            }
        }
        return found;
    }

    private static Number constantField(ClassNode owner, FieldInsnNode read,
                                        String descriptor,
                                        Map<String, Long> staticLongs) {
        if (!owner.name.equals(read.owner) || !descriptor.equals(read.desc)) return null;
        if ("J".equals(descriptor) && staticLongs.containsKey(read.name)) {
            return staticLongs.get(read.name);
        }
        for (FieldNode field : owner.fields) {
            if (field.name.equals(read.name) && descriptor.equals(field.desc)
                    && (field.access & (Opcodes.ACC_STATIC | Opcodes.ACC_FINAL))
                    == (Opcodes.ACC_STATIC | Opcodes.ACC_FINAL)
                    && field.value instanceof Number) return (Number) field.value;
        }
        return null;
    }

    private static Set<MethodRef> proveDeadSupport(ClassNode owner,
                                                   HelperSpec helper,
                                                   Set<MethodRef> roots,
                                                   List<ReferenceEdge> edges) {
        if (roots.isEmpty()) return Collections.emptySet();
        Set<MethodRef> support = new LinkedHashSet<>();
        ArrayDeque<MethodRef> queue = new ArrayDeque<>();
        for (MethodRef root : roots) {
            MethodNode method = method(owner, root.name, root.desc);
            if (!isBootstrapSupport(method)) return null;
            support.add(root);
            queue.add(root);
        }
        while (!queue.isEmpty()) {
            MethodRef target = queue.removeFirst();
            for (ReferenceEdge edge : edges) {
                if (!target.equals(edge.target) || support.contains(edge.source)) continue;
                if (!owner.name.equals(edge.source.owner)) return null;
                MethodNode predecessor = method(owner, edge.source.name,
                        edge.source.desc);
                if (!isBootstrapSupport(predecessor)
                        || predecessor == helper.method) return null;
                support.add(edge.source);
                queue.add(edge.source);
            }
        }
        for (ReferenceEdge edge : edges) {
            if (support.contains(edge.target) && !support.contains(edge.source)) {
                return null;
            }
        }
        return support;
    }

    private static boolean isBootstrapSupport(MethodNode method) {
        if (method == null || (method.access & (Opcodes.ACC_PRIVATE
                | Opcodes.ACC_STATIC)) != (Opcodes.ACC_PRIVATE
                | Opcodes.ACC_STATIC)) return false;
        if (!ADAPTER_DESC.equals(method.desc) && !BOOTSTRAP_DESC.equals(method.desc)) {
            return false;
        }
        boolean marker = false;
        for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
             insn = insn.getNext()) {
            if (insn instanceof MethodInsnNode) {
                String callOwner = ((MethodInsnNode) insn).owner;
                if (callOwner.startsWith("java/lang/invoke/MethodHandle")
                        || callOwner.startsWith("java/lang/invoke/MutableCallSite")) {
                    marker = true;
                }
            }
        }
        return marker;
    }

    private static int byteDecoderReferencesAfterRewrite(ClassNode owner,
                                                         Candidate candidate) {
        if (candidate.helper.byteDecoderName == null) return 1;
        int result = 0;
        MethodRef decoder = new MethodRef(owner.name,
                candidate.helper.byteDecoderName, BYTE_DECODER_DESC);
        for (ReferenceEdge edge : referenceEdges(
                Collections.singletonMap(owner.name, owner))) {
            if (!decoder.equals(edge.target)) continue;
            if (edge.source.equals(new MethodRef(owner.name,
                    candidate.helper.method.name, candidate.helper.method.desc))) {
                continue;
            }
            if (candidate.deadSupport.contains(edge.source)) continue;
            MethodNode clinit = method(owner, "<clinit>", "()V");
            if (clinit != null && edge.source.equals(new MethodRef(owner.name,
                    clinit.name, clinit.desc))) continue;
            result++;
        }
        return result;
    }

    private static void apply(ClassNode owner, Candidate candidate) throws Exception {
        int rewritten = 0;
        for (MethodNode method : owner.methods) {
            if (candidate.deadSupport.contains(new MethodRef(owner.name,
                    method.name, method.desc))) continue;
            int ordinal = 0;
            for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null; ) {
                AbstractInsnNode next = insn.getNext();
                if (insn instanceof MethodInsnNode) {
                    MethodInsnNode call = (MethodInsnNode) insn;
                    if (call.getOpcode() == Opcodes.INVOKESTATIC
                            && owner.name.equals(call.owner)
                            && candidate.helper.method.name.equals(call.name)
                            && HELPER_DESC.equals(call.desc)) {
                        DirectSite site = candidate.site(method.name, method.desc,
                                ordinal++);
                        if (site == null) {
                            throw new IllegalStateException("live-site-moved:"
                                    + method.name + method.desc + "#" + (ordinal - 1));
                        }
                        InsnList replacement = new InsnList();
                        replacement.add(new InsnNode(Opcodes.POP2));
                        replacement.add(new InsnNode(Opcodes.POP));
                        replacement.add(new LdcInsnNode(site.plaintext));
                        method.instructions.insertBefore(call, replacement);
                        method.instructions.remove(call);
                        rewritten++;
                    }
                }
                insn = next;
            }
        }
        if (rewritten != candidate.liveSites.size()) {
            throw new IllegalStateException("rewritten-sites=" + rewritten + "/"
                    + candidate.liveSites.size());
        }
        owner.methods.removeIf(method -> candidate.deadSupport.contains(
                new MethodRef(owner.name, method.name, method.desc)));
        MethodNode helper = method(owner, candidate.helper.method.name, HELPER_DESC);
        if (helper == null || hasMethodReference(owner, helper.name, helper.desc)) {
            throw new IllegalStateException("helper-still-referenced");
        }
        owner.methods.remove(helper);
        bypassOuterTable(owner, candidate.helper.tableField);
        if (candidate.removeByteDecoder) {
            MethodNode decoder = method(owner, candidate.helper.byteDecoderName,
                    BYTE_DECODER_DESC);
            if (decoder == null || hasMethodReference(owner, decoder.name,
                    decoder.desc)) {
                throw new IllegalStateException("byte-decoder-still-referenced");
            }
            owner.methods.remove(decoder);
        }
    }

    private static void bypassOuterTable(ClassNode owner, String tableField)
            throws Exception {
        MethodNode clinit = method(owner, "<clinit>", "()V");
        if (clinit == null) throw new IllegalStateException("missing <clinit>");
        AbstractInsnNode start = null;
        MethodInsnNode factory = null;
        FieldInsnNode tableStore = null;
        for (AbstractInsnNode insn = clinit.instructions.getFirst(); insn != null;
             insn = insn.getNext()) {
            if (isCipherFactory(insn, PKCS5)) {
                if (factory != null) throw new IllegalStateException(
                        "multiple outer PKCS5 factories");
                factory = (MethodInsnNode) insn;
                start = previousCode(insn);
            }
            if (insn instanceof FieldInsnNode && insn.getOpcode() == Opcodes.PUTSTATIC) {
                FieldInsnNode field = (FieldInsnNode) insn;
                if (owner.name.equals(field.owner) && tableField.equals(field.name)
                        && "[Ljava/lang/String;".equals(field.desc)) {
                    if (tableStore != null) throw new IllegalStateException(
                            "multiple table stores");
                    tableStore = field;
                }
            }
        }
        if (start == null || factory == null || tableStore == null) {
            throw new IllegalStateException("outer table boundary missing");
        }
        AbstractInsnNode continuation = nextCode(tableStore);
        if (continuation == null) throw new IllegalStateException(
                "outer table continuation missing");

        Frame<?>[] before = new Analyzer<>(new BasicVerifier()).analyze(
                owner.name, clinit);
        Frame<?> startFrame = before[clinit.instructions.indexOf(start)];
        Frame<?> continuationFrame = before[clinit.instructions.indexOf(continuation)];
        if (startFrame == null || continuationFrame == null
                || startFrame.getStackSize() != 0
                || continuationFrame.getStackSize() != 0) {
            throw new IllegalStateException("outer boundary stack");
        }

        LabelNode target = new LabelNode();
        clinit.instructions.insertBefore(continuation, target);
        JumpInsnNode bypass = new JumpInsnNode(Opcodes.GOTO, target);
        clinit.instructions.insertBefore(start, bypass);
        clinit.instructions.remove(start);

        Frame<?>[] frames = new Analyzer<>(new BasicVerifier()).analyze(
                owner.name, clinit);
        int factoryIndex = clinit.instructions.indexOf(factory);
        if (factoryIndex < 0 || frames[factoryIndex] != null) {
            throw new IllegalStateException("outer factory remained reachable");
        }
        Set<AbstractInsnNode> unreachable = Collections.newSetFromMap(
                new IdentityHashMap<AbstractInsnNode, Boolean>());
        int index = 0;
        for (AbstractInsnNode insn = clinit.instructions.getFirst(); insn != null;
             insn = insn.getNext(), index++) {
            if (insn.getOpcode() >= 0 && frames[index] == null) unreachable.add(insn);
        }
        clinit.tryCatchBlocks.removeIf(block -> !reachableExceptionRange(
                clinit, block, frames));
        for (AbstractInsnNode insn : unreachable) clinit.instructions.remove(insn);
        for (AbstractInsnNode insn = clinit.instructions.getFirst(); insn != null; ) {
            AbstractInsnNode next = insn.getNext();
            if (insn instanceof FrameNode) clinit.instructions.remove(insn);
            insn = next;
        }
        if (clinit.localVariables != null) clinit.localVariables.clear();
        clinit.visibleLocalVariableAnnotations = null;
        clinit.invisibleLocalVariableAnnotations = null;
        new Analyzer<>(new BasicVerifier()).analyze(owner.name, clinit);
        if (containsPkcs5(clinit)) throw new IllegalStateException(
                "outer PKCS5 survived pruning");
    }

    private static boolean reachableExceptionRange(MethodNode method,
                                                   TryCatchBlockNode block,
                                                   Frame<?>[] frames) {
        int handler = method.instructions.indexOf(block.handler);
        int start = method.instructions.indexOf(block.start);
        int end = method.instructions.indexOf(block.end);
        if (handler < 0 || start < 0 || end < 0 || start >= end
                || frames[handler] == null) return false;
        for (int i = start; i < end; i++) {
            AbstractInsnNode insn = method.instructions.get(i);
            if (insn.getOpcode() >= 0 && frames[i] != null) return true;
        }
        return false;
    }

    private static void assertRewritten(ClassNode owner, Candidate candidate) {
        if (countPkcs5(owner) != 0) {
            throw new IllegalStateException("PKCS5 survived=" + countPkcs5(owner));
        }
        if (method(owner, candidate.helper.method.name, HELPER_DESC) != null) {
            throw new IllegalStateException("delayed helper survived");
        }
        for (MethodRef dead : candidate.deadSupport) {
            if (method(owner, dead.name, dead.desc) != null) {
                throw new IllegalStateException("dead bootstrap survived=" + dead);
            }
        }
        if (candidate.removeByteDecoder && method(owner,
                candidate.helper.byteDecoderName, BYTE_DECODER_DESC) != null) {
            throw new IllegalStateException("byte decoder survived");
        }
        Set<String> constants = new HashSet<>();
        for (MethodNode method : owner.methods) {
            for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
                 insn = insn.getNext()) {
                if (insn instanceof LdcInsnNode
                        && ((LdcInsnNode) insn).cst instanceof String) {
                    constants.add((String) ((LdcInsnNode) insn).cst);
                }
            }
        }
        if (!constants.containsAll(candidate.plaintexts)) {
            throw new IllegalStateException("plaintext constants incomplete");
        }
    }

    private static boolean hasMethodReference(ClassNode owner, String name,
                                              String desc) {
        MethodRef target = new MethodRef(owner.name, name, desc);
        for (ReferenceEdge edge : referenceEdges(
                Collections.singletonMap(owner.name, owner))) {
            if (target.equals(edge.target)) return true;
        }
        return false;
    }

    private static List<ReferenceEdge> referenceEdges(
            Map<String, ClassNode> classes) {
        List<ReferenceEdge> result = new ArrayList<>();
        for (ClassNode owner : classes.values()) {
            for (MethodNode method : owner.methods) {
                MethodRef source = new MethodRef(owner.name, method.name,
                        method.desc);
                for (AbstractInsnNode insn = method.instructions.getFirst();
                     insn != null; insn = insn.getNext()) {
                    if (insn instanceof MethodInsnNode) {
                        MethodInsnNode call = (MethodInsnNode) insn;
                        result.add(new ReferenceEdge(source, new MethodRef(
                                call.owner, call.name, call.desc), true, call));
                    } else if (insn instanceof InvokeDynamicInsnNode) {
                        InvokeDynamicInsnNode indy = (InvokeDynamicInsnNode) insn;
                        addHandleEdge(result, source, indy.bsm);
                        for (Object argument : indy.bsmArgs) {
                            addConstantEdges(result, source, argument);
                        }
                    } else if (insn instanceof LdcInsnNode) {
                        addConstantEdges(result, source,
                                ((LdcInsnNode) insn).cst);
                    }
                }
            }
        }
        return result;
    }

    private static void addConstantEdges(List<ReferenceEdge> result,
                                         MethodRef source, Object value) {
        if (value instanceof Handle) addHandleEdge(result, source, (Handle) value);
        else if (value instanceof ConstantDynamic) {
            ConstantDynamic dynamic = (ConstantDynamic) value;
            addHandleEdge(result, source, dynamic.getBootstrapMethod());
            for (int i = 0; i < dynamic.getBootstrapMethodArgumentCount(); i++) {
                addConstantEdges(result, source,
                        dynamic.getBootstrapMethodArgument(i));
            }
        }
    }

    private static void addHandleEdge(List<ReferenceEdge> result,
                                      MethodRef source, Handle handle) {
        if (handle == null) return;
        int tag = handle.getTag();
        if (tag >= Opcodes.H_INVOKEVIRTUAL && tag <= Opcodes.H_INVOKEINTERFACE) {
            result.add(new ReferenceEdge(source, new MethodRef(handle.getOwner(),
                    handle.getName(), handle.getDesc()), false, null));
        }
    }

    private static int countPkcs5(Map<String, ClassNode> classes) {
        int result = 0;
        for (ClassNode owner : classes.values()) result += countPkcs5(owner);
        return result;
    }

    private static int countPkcs5(ClassNode owner) {
        int result = 0;
        for (MethodNode method : owner.methods) {
            for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
                 insn = insn.getNext()) {
                if (isCipherFactory(insn, PKCS5)) result++;
            }
        }
        return result;
    }

    private static boolean containsPkcs5(MethodNode method) {
        for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
             insn = insn.getNext()) if (isCipherFactory(insn, PKCS5)) return true;
        return false;
    }

    private static boolean isCipherFactory(AbstractInsnNode insn,
                                           String algorithm) {
        if (!isCall(insn, Opcodes.INVOKESTATIC, "javax/crypto/Cipher",
                "getInstance", "(Ljava/lang/String;)Ljavax/crypto/Cipher;")) {
            return false;
        }
        AbstractInsnNode previous = previousCode(insn);
        return previous instanceof LdcInsnNode
                && algorithm.equals(((LdcInsnNode) previous).cst);
    }

    private static boolean isCall(AbstractInsnNode insn, int opcode,
                                  String owner, String name, String desc) {
        if (!(insn instanceof MethodInsnNode)) return false;
        MethodInsnNode call = (MethodInsnNode) insn;
        return call.getOpcode() == opcode && owner.equals(call.owner)
                && name.equals(call.name) && desc.equals(call.desc);
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

    private static Integer intConstant(AbstractInsnNode insn) {
        if (insn == null) return null;
        int opcode = insn.getOpcode();
        if (opcode >= Opcodes.ICONST_M1 && opcode <= Opcodes.ICONST_5) {
            return opcode - Opcodes.ICONST_0;
        }
        if (insn instanceof IntInsnNode && (opcode == Opcodes.BIPUSH
                || opcode == Opcodes.SIPUSH)) return ((IntInsnNode) insn).operand;
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

    private static MethodNode method(ClassNode owner, String name, String desc) {
        for (MethodNode method : owner.methods) {
            if (name.equals(method.name) && desc.equals(method.desc)) return method;
        }
        return null;
    }

    private static void writeVerifiedArchive(List<EntryBytes> entries,
                                             Map<String, byte[]> replacements,
                                             Path output, Summary summary,
                                             List<String> verifier)
            throws Exception {
        Path parent = output.toAbsolutePath().getParent();
        if (parent == null) parent = Paths.get(".").toAbsolutePath();
        Files.createDirectories(parent);
        Path temporary = Files.createTempFile(parent,
                output.getFileName().toString() + ".", ".tmp");
        summary.temporaryOutput = temporary.toAbsolutePath().toString();
        try {
            writeArchive(entries, replacements, temporary, summary);
            ArchiveVerification verification = verifyArchive(temporary, verifier);
            summary.outputClasses = verification.classes;
            summary.outputVerificationErrors += verification.errors;
            summary.outputPkcs5Calls = verification.pkcs5Calls;
            int expected = summary.inputPkcs5Calls - replacements.size() * 2;
            if (verification.classes != summary.parsedClasses) {
                summary.outputVerificationErrors++;
                verifier.add(tsv("archive", "<archive>", "FAIL",
                        "class-count=" + verification.classes + "/"
                                + summary.parsedClasses));
            }
            if (verification.pkcs5Calls != expected) {
                summary.outputVerificationErrors++;
                verifier.add(tsv("archive", "<archive>", "FAIL",
                        "pkcs5-count=" + verification.pkcs5Calls + "/" + expected));
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
                                     Map<String, byte[]> replacements,
                                     Path output, Summary summary) throws IOException {
        Set<String> applied = new LinkedHashSet<>();
        try (ZipOutputStream out = new ZipOutputStream(Files.newOutputStream(output))) {
            for (EntryBytes entry : entries) {
                if (isSignatureEntry(entry.name) && !replacements.isEmpty()) {
                    summary.signaturesRemoved++;
                    continue;
                }
                byte[] bytes = entry.bytes;
                if (entry.name.endsWith(".class")) {
                    String name = new ClassReader(bytes).getClassName();
                    byte[] replacement = replacements.get(name);
                    if (replacement != null) {
                        bytes = replacement;
                        applied.add(name);
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
                } else written.setMethod(ZipEntry.DEFLATED);
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

    private static ArchiveVerification verifyArchive(Path archive,
                                                      List<String> verifier)
            throws IOException {
        ArchiveVerification result = new ArchiveVerification();
        try (ZipInputStream in = new ZipInputStream(Files.newInputStream(archive))) {
            ZipEntry entry;
            while ((entry = in.getNextEntry()) != null) {
                byte[] bytes = readAll(in);
                if (!entry.getName().endsWith(".class")) continue;
                result.classes++;
                String name = entry.getName();
                try {
                    verifyClass(bytes);
                    ClassNode owner = readClass(bytes);
                    name = owner.name;
                    result.pkcs5Calls += countPkcs5(owner);
                    verifier.add(tsv("archive", name, "PASS", ""));
                } catch (Throwable failure) {
                    result.errors++;
                    verifier.add(tsv("archive", name, "FAIL",
                            shortReason(failure)));
                }
            }
        }
        return result;
    }

    private static void verifyClass(byte[] bytes) throws Exception {
        ClassReader reader = new ClassReader(bytes);
        reader.accept(new CheckClassAdapter(new ClassWriter(0), false), 0);
        ClassNode owner = readClass(bytes);
        for (MethodNode method : owner.methods) {
            if (method.instructions != null && method.instructions.size() != 0) {
                new Analyzer<>(new BasicVerifier()).analyze(owner.name, method);
            }
        }
    }

    private static void writeReports(Path input, Path report, Path output,
                                     Summary summary,
                                     List<Candidate> candidates,
                                     List<String> verifier) throws Exception {
        candidates.sort(Comparator.comparing(candidate -> candidate.owner));
        List<String> rows = new ArrayList<>();
        rows.add("class\ttable_field\tcapacity\touter_key_hex\thelper\tindex_mask_hex"
                + "\tindex_xor\tlive_sites\tdead_support_methods\tplaintexts"
                + "\tremove_byte_decoder\taction\treason");
        List<String> sites = new ArrayList<>();
        sites.add("class\tmethod\tinstruction\tcall_int\tcall_long_hex"
                + "\ttable_index\tplaintext\taction");
        List<String> removed = new ArrayList<>();
        removed.add("class\tmethod\tkind\taction");
        for (Candidate candidate : candidates) {
            rows.add(candidate.row());
            for (DirectSite site : candidate.liveSites) {
                sites.add(tsv(candidate.owner, site.method.name + site.method.desc,
                        site.instruction, site.callInt, hex(site.callLong),
                        site.tableIndex, escape(site.plaintext),
                        candidate.proven() || "REWRITE".equals(candidate.action)
                                || "PROVEN_DRY_RUN".equals(candidate.action)
                                ? "DIRECTIZE" : "KEEP"));
            }
            for (MethodRef support : candidate.deadSupport) {
                removed.add(tsv(candidate.owner, support.name + support.desc,
                        "dead-bootstrap-support",
                        candidate.proven() || "REWRITE".equals(candidate.action)
                                || "PROVEN_DRY_RUN".equals(candidate.action)
                                ? "REMOVE" : "KEEP"));
            }
            if (candidate.helper != null) {
                removed.add(tsv(candidate.owner,
                        candidate.helper.method.name + HELPER_DESC,
                        "pkcs5-delayed-helper",
                        candidate.proven() || "REWRITE".equals(candidate.action)
                                || "PROVEN_DRY_RUN".equals(candidate.action)
                                ? "REMOVE" : "KEEP"));
            }
        }
        Files.write(report.resolve("candidates.tsv"), rows, StandardCharsets.UTF_8);
        Files.write(report.resolve("sites.tsv"), sites, StandardCharsets.UTF_8);
        Files.write(report.resolve("removed-methods.tsv"), removed,
                StandardCharsets.UTF_8);
        Files.write(report.resolve("verifier.tsv"), verifier,
                StandardCharsets.UTF_8);
        List<String> audit = new ArrayList<>();
        audit.add("input=" + input.toAbsolutePath());
        audit.add("input_sha256=" + sha256(input));
        audit.add("parsed_classes=" + summary.parsedClasses);
        audit.add("field_table_candidates=" + summary.fieldTableCandidates);
        audit.add("proven_classes=" + summary.provenClasses);
        audit.add("proven_live_sites=" + summary.provenSites);
        audit.add("proven_plaintexts=" + summary.provenStrings);
        audit.add("dead_bootstrap_methods=" + summary.deadBootstrapMethods);
        audit.add("changed_classes=" + summary.changedClasses);
        audit.add("rewritten_sites=" + summary.rewrittenSites);
        audit.add("outer_tables_rewritten=" + summary.outerTablesRewritten);
        audit.add("helpers_removed=" + summary.helpersRemoved);
        audit.add("byte_decoders_removed=" + summary.byteDecodersRemoved);
        audit.add("class_rollbacks=" + summary.classRollbacks);
        audit.add("input_pkcs5_calls=" + summary.inputPkcs5Calls);
        audit.add("output_pkcs5_calls=" + summary.outputPkcs5Calls);
        audit.add("pkcs5_calls_removed=" + summary.pkcs5CallsRemoved);
        audit.add("output_requested=" + summary.outputRequested);
        audit.add("output=" + (output == null ? "" : output.toAbsolutePath()));
        audit.add("temporary_output=" + value(summary.temporaryOutput));
        audit.add("output_entries=" + summary.outputEntries);
        audit.add("output_classes=" + summary.outputClasses);
        audit.add("output_verification_errors=" + summary.outputVerificationErrors);
        audit.add("signatures_removed=" + summary.signaturesRemoved);
        audit.add("output_committed=" + summary.outputCommitted);
        audit.add("proof=closed outer table CFG + unique delayed helper formula"
                + " + unique constant producers + closed dead bootstrap subgraph");
        audit.add("input_classes_loaded=false");
        audit.add("input_classes_initialized=false");
        audit.add("gate=" + (summary.gatePass ? "PASS" : "FAIL"));
        Files.write(report.resolve("audit.txt"), audit, StandardCharsets.UTF_8);
        Files.write(report.resolve("gate.txt"), Collections.singletonList(
                summary.gatePass ? "PASS" : "FAIL"), StandardCharsets.UTF_8);
    }

    private static String escape(String value) {
        if (value == null) return "";
        StringBuilder result = new StringBuilder();
        for (int i = 0; i < value.length(); i++) {
            char c = value.charAt(i);
            if (c == '\\') result.append("\\\\");
            else if (c == '\t') result.append("\\t");
            else if (c == '\r') result.append("\\r");
            else if (c == '\n') result.append("\\n");
            else if (c < 0x20 || c == 0x7f) {
                result.append(String.format(Locale.ROOT, "\\u%04X", (int) c));
            } else result.append(c);
        }
        return result.toString();
    }

    private static String sha256(Path path) throws Exception {
        MessageDigest digest = MessageDigest.getInstance("SHA-256");
        try (InputStream input = Files.newInputStream(path)) {
            byte[] buffer = new byte[8192];
            int read;
            while ((read = input.read(buffer)) != -1) digest.update(buffer, 0, read);
        }
        StringBuilder result = new StringBuilder();
        for (byte value : digest.digest()) {
            result.append(String.format(Locale.ROOT, "%02X", value & 0xff));
        }
        return result.toString();
    }

    private static void validatePaths(Path input, Path output) {
        if (output != null && input.toAbsolutePath().normalize().equals(
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

    private static String append(String current, String added) {
        return current == null || current.isEmpty() ? added : current + ";" + added;
    }

    private static String shortReason(Throwable failure) {
        String text = failure.getClass().getSimpleName() + ":"
                + String.valueOf(failure.getMessage());
        text = text.replace('\t', ' ').replace('\r', ' ').replace('\n', ' ');
        return text.substring(0, Math.min(200, text.length()));
    }

    private static String hex(Long value) {
        return value == null ? "" : String.format(Locale.ROOT, "%016X", value);
    }

    private static String value(Object value) {
        return value == null ? "" : String.valueOf(value);
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

    static final class Summary {
        int parsedClasses;
        int fieldTableCandidates;
        int provenClasses;
        int provenSites;
        int provenStrings;
        int deadBootstrapMethods;
        int changedClasses;
        int rewrittenSites;
        int outerTablesRewritten;
        int helpersRemoved;
        int byteDecodersRemoved;
        int classRollbacks;
        int inputPkcs5Calls;
        int outputPkcs5Calls;
        int pkcs5CallsRemoved;
        boolean outputRequested;
        String temporaryOutput;
        int outputEntries;
        int outputClasses;
        int outputVerificationErrors;
        int signaturesRemoved;
        boolean outputCommitted;
        boolean integrityPass;
        boolean gatePass;
    }

    static final class StateHelperProof {
        final String owner;
        final long outerKey;
        final Map<String, Long> staticLongs;
        final String tableField;
        final List<String> outerEntries;
        final String source;

        StateHelperProof(String owner, long outerKey,
                         Map<String, Long> staticLongs, String source) {
            this(owner, outerKey, staticLongs, "",
                    Collections.<String>emptyList(), source);
        }

        StateHelperProof(String owner, long outerKey,
                         Map<String, Long> staticLongs, String tableField,
                         List<String> outerEntries, String source) {
            this.owner = owner;
            this.outerKey = outerKey;
            this.staticLongs = Collections.unmodifiableMap(
                    new LinkedHashMap<>(staticLongs));
            this.tableField = tableField;
            this.outerEntries = Collections.unmodifiableList(
                    new ArrayList<>(outerEntries));
            this.source = source;
        }
    }

    private static final class Candidate {
        final String owner;
        OuterTableProof table;
        HelperSpec helper;
        final List<DirectSite> liveSites = new ArrayList<>();
        final Set<MethodRef> deadSupport = new LinkedHashSet<>();
        final Set<String> plaintexts = new LinkedHashSet<>();
        boolean removeByteDecoder;
        String action = "REJECT";
        String reason = "";

        Candidate(String owner) {
            this.owner = owner;
        }

        Candidate reject(String reason) {
            this.action = "REJECT";
            this.reason = reason;
            return this;
        }

        boolean proven() {
            return "PROVEN".equals(action);
        }

        DirectSite site(String methodName, String methodDesc, int ordinal) {
            for (DirectSite site : liveSites) {
                if (site.method.name.equals(methodName)
                        && site.method.desc.equals(methodDesc)
                        && site.ordinal == ordinal) return site;
            }
            return null;
        }

        String row() {
            return tsv(owner, table == null ? "" : value(table.tableField),
                    table == null ? "" : table.capacity,
                    table == null ? "" : hex(table.outerKey), helper == null ? ""
                            : helper.method.name + HELPER_DESC,
                    helper == null ? "" : hex(helper.indexMask),
                    helper == null ? "" : helper.indexXor,
                    liveSites.size(), deadSupport.size(), plaintexts.size(),
                    removeByteDecoder, action, reason);
        }
    }

    private static final class HelperSpec {
        final MethodNode method;
        final long indexMask;
        final int indexXor;
        final String tableField;
        final String byteDecoderName;

        HelperSpec(MethodNode method, long indexMask, int indexXor,
                   String tableField, String byteDecoderName) {
            this.method = method;
            this.indexMask = indexMask;
            this.indexXor = indexXor;
            this.tableField = tableField;
            this.byteDecoderName = byteDecoderName;
        }
    }

    private static final class OuterTableProof {
        final String tableField;
        final int capacity;
        final long outerKey;
        final List<String> encryptedEntries;
        final AbstractInsnNode start;
        final AbstractInsnNode tableStore;

        OuterTableProof(String tableField, int capacity, long outerKey,
                        List<String> encryptedEntries, AbstractInsnNode start,
                        AbstractInsnNode tableStore) {
            this.tableField = tableField;
            this.capacity = capacity;
            this.outerKey = outerKey;
            this.encryptedEntries = Collections.unmodifiableList(
                    new ArrayList<>(encryptedEntries));
            this.start = start;
            this.tableStore = tableStore;
        }
    }

    private static final class DirectSite {
        final MethodNode method;
        final MethodInsnNode node;
        final int instruction;
        final int ordinal;
        Integer callInt;
        Long callLong;
        int tableIndex;
        String plaintext;

        DirectSite(MethodNode method, MethodInsnNode node, int instruction,
                   int ordinal) {
            this.method = method;
            this.node = node;
            this.instruction = instruction;
            this.ordinal = ordinal;
        }

        String id() {
            return method.name + method.desc + "@" + instruction;
        }
    }

    private static final class Arguments {
        final int intValue;
        final long longValue;

        Arguments(int intValue, long longValue) {
            this.intValue = intValue;
            this.longValue = longValue;
        }
    }

    private static final class MethodRef {
        final String owner;
        final String name;
        final String desc;

        MethodRef(String owner, String name, String desc) {
            this.owner = owner;
            this.name = name;
            this.desc = desc;
        }

        @Override
        public boolean equals(Object value) {
            if (!(value instanceof MethodRef)) return false;
            MethodRef other = (MethodRef) value;
            return owner.equals(other.owner) && name.equals(other.name)
                    && desc.equals(other.desc);
        }

        @Override
        public int hashCode() {
            int result = owner.hashCode();
            result = 31 * result + name.hashCode();
            return 31 * result + desc.hashCode();
        }

        @Override
        public String toString() {
            return owner + "." + name + desc;
        }
    }

    private static final class ReferenceEdge {
        final MethodRef source;
        final MethodRef target;
        final boolean direct;
        final MethodInsnNode call;

        ReferenceEdge(MethodRef source, MethodRef target, boolean direct,
                      MethodInsnNode call) {
            this.source = source;
            this.target = target;
            this.direct = direct;
            this.call = call;
        }
    }

    private static final class EntryBytes {
        final String name;
        final byte[] bytes;
        final long time;
        final String comment;
        final byte[] extra;
        final int method;

        EntryBytes(ZipEntry entry, byte[] bytes) {
            this.name = entry.getName();
            this.bytes = bytes;
            this.time = entry.getTime();
            this.comment = entry.getComment();
            this.extra = entry.getExtra();
            this.method = entry.getMethod();
        }
    }

    private static final class ArchiveVerification {
        int classes;
        int errors;
        int pkcs5Calls;
    }
}
