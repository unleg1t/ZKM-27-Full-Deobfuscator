package unlegit.zkm;

import org.objectweb.asm.ClassReader;
import org.objectweb.asm.ClassWriter;
import org.objectweb.asm.Opcodes;
import org.objectweb.asm.Type;
import org.objectweb.asm.tree.AbstractInsnNode;
import org.objectweb.asm.tree.ClassNode;
import org.objectweb.asm.tree.FieldInsnNode;
import org.objectweb.asm.tree.FieldNode;
import org.objectweb.asm.tree.InsnList;
import org.objectweb.asm.tree.IntInsnNode;
import org.objectweb.asm.tree.InvokeDynamicInsnNode;
import org.objectweb.asm.tree.JumpInsnNode;
import org.objectweb.asm.tree.LabelNode;
import org.objectweb.asm.tree.LdcInsnNode;
import org.objectweb.asm.tree.LookupSwitchInsnNode;
import org.objectweb.asm.tree.MethodInsnNode;
import org.objectweb.asm.tree.MethodNode;
import org.objectweb.asm.tree.TableSwitchInsnNode;
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
import java.io.IOException;
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
import java.util.IdentityHashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.zip.CRC32;
import java.util.zip.ZipEntry;
import java.util.zip.ZipInputStream;
import java.util.zip.ZipOutputStream;

/**
 * Folds a closed literal-key DES/CBC/NoPadding scalar island inside a mixed
 * static initializer.
 *
 * <p>The ZKM layout places the result block before the byte-array decrypt
 * body.  This stage proves both removed ranges are closed, replaces the first
 * range with a plaintext long and a jump to the original result block, and
 * retains that result block and the business continuation verbatim.  State-
 * derived keys, exception ranges, tables, and helper decryptors are rejected.
 * Input classes are parsed only; they are never defined or initialized.</p>
 */
public final class ZkmNoPaddingLiteralFragmentDeobfuscator {
    private static final String ALGORITHM = "DES/CBC/NoPadding";
    private static final String STATE = ObfRuntimeNames.STATE;
    private static final String STATE_IFACE = ObfRuntimeNames.STATE_INTERFACE;

    private ZkmNoPaddingLiteralFragmentDeobfuscator() {
    }

    public static void main(String[] args) throws Exception {
        if (args.length < 2 || args.length > 3) {
            System.err.println("usage: ZkmNoPaddingLiteralFragmentDeobfuscator "
                    + "<input.jar> <report-dir> [output.jar]");
            System.exit(2);
        }
        Summary summary = rewrite(Paths.get(args[0]), Paths.get(args[1]),
                args.length == 3 ? Paths.get(args[2]) : null);
        System.out.println("classes=" + summary.parsedClasses + " candidates="
                + summary.candidates + " proven=" + summary.proven + " rewritten="
                + summary.changedClasses + " rejected=" + summary.rejected
                + " rollbacks=" + summary.rollbacks + " residual_nopadding="
                + summary.outputResidualNoPadding + " output_committed="
                + summary.outputCommitted);
    }

    static Summary rewrite(Path input, Path reportDirectory, Path output) throws Exception {
        return rewrite(input, reportDirectory, output, Collections.emptyMap(), false);
    }

    static Summary rewriteStateDerived(Path input, Path reportDirectory, Path output,
                                       Map<String, KeyProof> keyProofs) throws Exception {
        return rewrite(input, reportDirectory, output, keyProofs, true);
    }

    private static Summary rewrite(Path input, Path reportDirectory, Path output,
                                   Map<String, KeyProof> keyProofs,
                                   boolean stateDerived) throws Exception {
        if (output != null && input.toAbsolutePath().normalize()
                .equals(output.toAbsolutePath().normalize())) {
            throw new IllegalArgumentException("output must not replace input");
        }
        Files.createDirectories(reportDirectory);
        List<EntryBytes> entries = readEntries(input);
        Map<String, byte[]> originals = classBytes(entries);
        Map<String, ClassNode> hierarchy = classNodes(originals);
        Summary summary = new Summary();
        summary.parsedClasses = originals.size();
        List<Candidate> candidates = new ArrayList<>();
        Map<String, byte[]> replacements = new LinkedHashMap<>();
        List<String> verifier = new ArrayList<>();
        verifier.add("scope\tclass\tstatus\tdetail");

        List<String> names = new ArrayList<>(originals.keySet());
        Collections.sort(names);
        for (String name : names) {
            ClassNode owner = readClass(originals.get(name));
            KeyProof keyProof = keyProofs.get(name);
            Candidate candidate = inspect(owner, keyProof, stateDerived);
            if (candidate == null) continue;
            candidates.add(candidate);
            summary.candidates++;
            if (!candidate.proven) {
                summary.rejected++;
                continue;
            }
            summary.proven++;
            if (output == null) {
                candidate.action = "PROVEN_DRY_RUN";
                continue;
            }
            ZkmClassRewriteTransaction.Result transaction =
                    ZkmClassRewriteTransaction.attempt(originals.get(name), rewritten -> {
                        Candidate fresh = inspect(rewritten, keyProof, stateDerived);
                        if (fresh == null || !fresh.proven
                                || fresh.key != candidate.key
                                || fresh.ciphertext != candidate.ciphertext
                                || fresh.plaintext != candidate.plaintext
                                || !fresh.fieldName.equals(candidate.fieldName)
                                || !fresh.fieldDesc.equals(candidate.fieldDesc)) {
                            throw new IllegalStateException("proof changed before mutation");
                        }
                        apply(rewritten, fresh);
                    }, emitted -> assertRewritten(emitted, candidate),
                    rewritten -> writeClass(rewritten, hierarchy));
            if (transaction.isCommitted()) {
                replacements.put(name, transaction.bytes());
                candidate.action = "REWRITE";
                summary.changedClasses++;
                verifier.add(tsv("class", name, "PASS", "field="
                        + candidate.fieldName + candidate.fieldDesc));
            } else {
                candidate.action = "ROLLBACK";
                candidate.reason += ";rollback=" + transaction.stage() + ":"
                        + transaction.reason();
                summary.rollbacks++;
                verifier.add(tsv("class", name, "FAIL", transaction.stage() + ":"
                        + transaction.reason()));
            }
        }

        if (output != null) writeArchive(entries, replacements, output, summary, verifier);
        writeReports(input, output, reportDirectory, summary, candidates, verifier,
                stateDerived);
        return summary;
    }

    private static Candidate inspect(ClassNode owner) {
        return inspect(owner, null, false);
    }

    private static Candidate inspect(ClassNode owner, KeyProof keyProof,
                                     boolean stateDerived) {
        MethodNode clinit = method(owner, "<clinit>", "()V");
        if (clinit == null) return null;
        Code code = new Code(clinit);
        List<Integer> factories = new ArrayList<>();
        for (int index = 0; index < code.nodes.size(); index++) {
            if (isNoPaddingFactory(code, index)) factories.add(index);
        }
        if (factories.isEmpty()) return null;

        Candidate candidate = new Candidate(owner.name);
        candidate.instructions = code.nodes.size();
        candidate.noPaddingCalls = factories.size();
        if (factories.size() != 1) return candidate.reject("nopadding-factories="
                + factories.size());
        if (clinit.tryCatchBlocks != null && !clinit.tryCatchBlocks.isEmpty()) {
            return candidate.reject("exception-ranges=" + clinit.tryCatchBlocks.size());
        }
        boolean hasState = hasStateCall(clinit);
        if (!stateDerived && hasState) return candidate.reject("state-derived-key");
        if (stateDerived && !hasState) return null;
        if (stateDerived && keyProof == null) {
            return candidate.reject("state-class-key-unproven");
        }

        int factory = factories.get(0);
        int start = factory - 1;
        int init = uniqueCall(code, factory + 1, code.nodes.size(),
                "javax/crypto/Cipher", "init");
        if (init < 0) return candidate.reject("cipher-init-not-unique");
        int doFinal = uniqueCall(code, init + 1, code.nodes.size(),
                "javax/crypto/Cipher", "doFinal");
        if (doFinal < 0) return candidate.reject("do-final-not-unique");

        Set<Long> keyConstants = longConstants(code, factory + 1, init);
        Set<Long> ciphertextConstants = longConstants(code, init + 1, doFinal);
        if (!stateDerived && keyConstants.size() != 1) {
            return candidate.reject("literal-key-count=" + keyConstants.size());
        }
        if (stateDerived) {
            String keyFailure = deriveStateKey(owner, clinit, code, start, init,
                    keyProof, candidate);
            if (keyFailure != null) return candidate.reject(keyFailure);
        }
        if (ciphertextConstants.size() != 1) {
            return candidate.reject("ciphertext-count=" + ciphertextConstants.size());
        }

        List<Integer> resultJumps = new ArrayList<>();
        for (int index = doFinal + 1; index < code.nodes.size(); index++) {
            AbstractInsnNode insn = code.nodes.get(index);
            if (!(insn instanceof JumpInsnNode) || insn.getOpcode() != Opcodes.GOTO) continue;
            int target = code.target(((JumpInsnNode) insn).label);
            if (target > init && target < doFinal) resultJumps.add(index);
            if (!resultJumps.isEmpty()) break;
        }
        if (resultJumps.size() != 1) return candidate.reject("result-backedges="
                + resultJumps.size());
        int resultJump = resultJumps.get(0);
        JumpInsnNode backedge = (JumpInsnNode) code.nodes.get(resultJump);
        int result = code.target(backedge.label);

        int resultExit = -1;
        int continuation = -1;
        for (int index = result; index < doFinal; index++) {
            AbstractInsnNode insn = code.nodes.get(index);
            if (!(insn instanceof JumpInsnNode) || insn.getOpcode() != Opcodes.GOTO) continue;
            int target = code.target(((JumpInsnNode) insn).label);
            if (target > resultJump) {
                resultExit = index;
                continuation = target;
                break;
            }
        }
        if (resultExit < 0 || continuation <= resultJump) {
            return candidate.reject("business-continuation-not-found");
        }
        if (!(start < result && result <= resultExit && resultExit < doFinal
                && doFinal < resultJump && resultJump < continuation)) {
            return candidate.reject("cfg-order=" + start + "," + result + ","
                    + resultExit + "," + doFinal + "," + resultJump + ","
                    + continuation);
        }

        String removedFailure = validateRemovedIsland(code, start, result, resultExit,
                continuation);
        if (removedFailure != null) return candidate.reject(removedFailure);
        String inboundFailure = validateNoExternalInbound(code, start, result,
                resultExit, continuation);
        if (inboundFailure != null) return candidate.reject(inboundFailure);

        FieldInsnNode target = findResultWrite(owner, code, result);
        if (target == null) return candidate.reject("result-field-write-not-proven");
        FieldNode targetField = field(owner, target.name, target.desc);
        if (targetField == null || (targetField.access & Opcodes.ACC_STATIC) == 0) {
            return candidate.reject("result-field-not-static=" + target.name + target.desc);
        }

        try {
            Frame<BasicValue>[] frames = new Analyzer<BasicValue>(new BasicVerifier())
                    .analyze(owner.name, clinit);
            Frame<BasicValue> startFrame = frames[code.rawIndex(code.nodes.get(start))];
            Frame<BasicValue> resultFrame = frames[code.rawIndex(code.nodes.get(result))];
            Frame<BasicValue> continuationFrame =
                    frames[code.rawIndex(code.nodes.get(continuation))];
            if (startFrame == null || startFrame.getStackSize() != 0) {
                return candidate.reject("start-stack-not-empty");
            }
            if (resultFrame == null || resultFrame.getStackSize() != 1
                    || resultFrame.getStack(resultFrame.getStackSize() - 1) != BasicValue.LONG_VALUE) {
                return candidate.reject("result-stack-not-long");
            }
            if (continuationFrame == null || continuationFrame.getStackSize() != 0) {
                return candidate.reject("continuation-stack-not-empty");
            }
        } catch (Throwable failure) {
            return candidate.reject("original-basic-verifier=" + shortReason(failure));
        }

        candidate.startCodeIndex = start;
        candidate.resultCodeIndex = result;
        candidate.resultExitCodeIndex = resultExit;
        candidate.continuationCodeIndex = continuation;
        candidate.resultLabel = backedge.label;
        candidate.continuationLabel = ((JumpInsnNode) code.nodes.get(resultExit)).label;
        candidate.fieldName = target.name;
        candidate.fieldDesc = target.desc;
        if (!stateDerived) candidate.key = keyConstants.iterator().next();
        candidate.ciphertext = ciphertextConstants.iterator().next();
        try {
            ZkmDesConstantEvaluator.KeyMaterial material =
                    ZkmDesConstantEvaluator.KeyMaterial.proven(candidate.key,
                            stateDerived ? "ZKM_LONG_KEY_PROVENANCE" : "LDC_LONG",
                            stateDerived
                                    ? "closed state-derived NoPadding scalar island;"
                                    + candidate.keySource
                                    : "closed literal-key NoPadding scalar island");
            candidate.plaintext = ZkmDesConstantEvaluator.decryptLong(material,
                    candidate.ciphertext);
        } catch (Throwable failure) {
            return candidate.reject("decrypt=" + shortReason(failure));
        }
        candidate.proven = true;
        candidate.reason = stateDerived
                ? "closed-state-derived-scalar-island;long-key-bootstrap-preserved;"
                + "result-block-and-business-continuation-preserved;key="
                + candidate.keySource
                : "closed-literal-scalar-island;result-block-and-business-continuation-preserved";
        return candidate;
    }

    private static String deriveStateKey(ClassNode owner, MethodNode clinit, Code code,
                                         int start, int init, KeyProof proof,
                                         Candidate candidate) {
        if (!owner.name.equals(proof.owner)) return "key-proof-owner=" + proof.owner;
        Set<Integer> keyLocals = new LinkedHashSet<>();
        for (int index = start + 1; index < init; index++) {
            AbstractInsnNode insn = code.nodes.get(index);
            if (insn instanceof VarInsnNode && insn.getOpcode() == Opcodes.LLOAD) {
                keyLocals.add(((VarInsnNode) insn).var);
            }
        }
        if (keyLocals.size() != 1) return "state-key-long-loads=" + keyLocals;
        int local = keyLocals.iterator().next();
        int definition = -1;
        int definitions = 0;
        for (int index = 0; index < start; index++) {
            AbstractInsnNode insn = code.nodes.get(index);
            if (insn instanceof VarInsnNode && insn.getOpcode() == Opcodes.LSTORE
                    && ((VarInsnNode) insn).var == local) {
                definition = index;
                definitions++;
            }
        }
        if (definitions != 1 || definition < 1) {
            return "state-key-local-definitions=" + definitions;
        }
        AbstractInsnNode xor = code.nodes.get(definition - 1);
        if (xor.getOpcode() != Opcodes.LXOR) return "state-key-local-producer";

        AbstractInsnNode maskNode;
        AbstractInsnNode keyNode;
        try {
            Frame<SourceValue>[] frames = new Analyzer<SourceValue>(
                    new SourceInterpreter()).analyze(owner.name, clinit);
            Frame<SourceValue> frame = frames[code.rawIndex(xor)];
            if (frame == null || frame.getStackSize() < 2) {
                return "state-key-xor-frame";
            }
            maskNode = uniqueSource(frame.getStack(frame.getStackSize() - 1));
            keyNode = uniqueSource(frame.getStack(frame.getStackSize() - 2));
        } catch (Throwable failure) {
            return "state-key-source-analysis=" + shortReason(failure);
        }
        if (!(maskNode instanceof LdcInsnNode)
                || !(((LdcInsnNode) maskNode).cst instanceof Long)) {
            return "state-key-xor-mask-source";
        }

        MethodInsnNode transform;
        if (keyNode instanceof MethodInsnNode
                && isStateTransform((MethodInsnNode) keyNode)) {
            transform = (MethodInsnNode) keyNode;
        } else if (keyNode instanceof FieldInsnNode
                && keyNode.getOpcode() == Opcodes.GETSTATIC) {
            FieldInsnNode read = (FieldInsnNode) keyNode;
            if (!owner.name.equals(read.owner) || !"J".equals(read.desc)) {
                return "state-key-field=" + read.owner + "." + read.name + read.desc;
            }
            FieldNode keyField = field(owner, read.name, read.desc);
            if (keyField == null
                    || (keyField.access & (Opcodes.ACC_STATIC | Opcodes.ACC_FINAL))
                    != (Opcodes.ACC_STATIC | Opcodes.ACC_FINAL)) {
                return "state-key-field-not-static-final=" + read.name;
            }
            FieldInsnNode write = null;
            int writeIndex = -1;
            for (int index = 0; index < definition; index++) {
                AbstractInsnNode insn = code.nodes.get(index);
                if (!(insn instanceof FieldInsnNode)
                        || insn.getOpcode() != Opcodes.PUTSTATIC) continue;
                FieldInsnNode field = (FieldInsnNode) insn;
                if (!read.owner.equals(field.owner) || !read.name.equals(field.name)
                        || !read.desc.equals(field.desc)) continue;
                if (write != null) return "state-key-field-writes-multiple";
                write = field;
                writeIndex = index;
            }
            if (write == null || writeIndex < 1) return "state-key-field-write";
            AbstractInsnNode producer = code.nodes.get(writeIndex - 1);
            if (!(producer instanceof MethodInsnNode)
                    || !isStateTransform((MethodInsnNode) producer)) {
                return "state-key-field-transform";
            }
            transform = (MethodInsnNode) producer;
            candidate.keyFieldName = read.name;
        } else {
            return "state-key-value-source=" + (keyNode == null ? "null"
                    : keyNode.getClass().getSimpleName() + ":" + keyNode.getOpcode());
        }

        int bootstraps = 0;
        int transforms = 0;
        for (int index = 0; index < start; index++) {
            AbstractInsnNode insn = code.nodes.get(index);
            if (!(insn instanceof MethodInsnNode)) continue;
            MethodInsnNode call = (MethodInsnNode) insn;
            if (call.getOpcode() == Opcodes.INVOKESTATIC && STATE.equals(call.owner)
                    && "a".equals(call.name)
                    && ObfRuntimeNames.BOOTSTRAP_DESC
                    .equals(call.desc)) bootstraps++;
            if (call.getOpcode() == Opcodes.INVOKEINTERFACE
                    && STATE_IFACE.equals(call.owner) && "a".equals(call.name)
                    && "(J)J".equals(call.desc)) transforms++;
        }
        if (bootstraps != 1 || transforms != 1) {
            return "state-key-call-count=" + bootstraps + "/" + transforms;
        }

        candidate.stateDerived = true;
        candidate.classKey = proof.classKey;
        candidate.outerMask = (Long) ((LdcInsnNode) maskNode).cst;
        candidate.key = candidate.classKey ^ candidate.outerMask;
        candidate.keySource = proof.source;
        candidate.keyChain = proof.chain;
        candidate.stateCallCount = countStateCalls(clinit);
        candidate.ownerFieldWriteCount = countOwnerFieldWrites(owner, clinit);
        return null;
    }

    private static AbstractInsnNode uniqueSource(SourceValue value) {
        if (value == null || value.insns == null || value.insns.size() != 1) return null;
        return value.insns.iterator().next();
    }

    private static boolean isStateTransform(MethodInsnNode call) {
        return call.getOpcode() == Opcodes.INVOKEINTERFACE
                && STATE_IFACE.equals(call.owner) && "a".equals(call.name)
                && "(J)J".equals(call.desc);
    }

    private static String validateRemovedIsland(Code code, int start, int result,
                                                int resultExit, int continuation) {
        Set<Integer> removed = removedIndices(start, result, resultExit, continuation);
        Map<String, Integer> calls = new LinkedHashMap<>();
        int byteArrays = 0;
        for (int index : removed) {
            AbstractInsnNode insn = code.nodes.get(index);
            int opcode = insn.getOpcode();
            if (insn instanceof InvokeDynamicInsnNode) return "removed-indy";
            if (insn instanceof FieldInsnNode) return "removed-field-access";
            if (insn instanceof MethodInsnNode) {
                MethodInsnNode call = (MethodInsnNode) insn;
                String id = call.owner + "." + call.name + call.desc;
                if (!allowedCryptoCall(call)) return "removed-call=" + id;
                calls.put(id, calls.getOrDefault(id, 0) + 1);
            }
            if (insn instanceof TypeInsnNode) {
                TypeInsnNode type = (TypeInsnNode) insn;
                if (opcode != Opcodes.NEW || !("javax/crypto/spec/DESKeySpec".equals(type.desc)
                        || "javax/crypto/spec/IvParameterSpec".equals(type.desc))) {
                    return "removed-type-op=" + opcode + ":" + type.desc;
                }
            }
            if (insn instanceof IntInsnNode && opcode == Opcodes.NEWARRAY) {
                if (((IntInsnNode) insn).operand != Opcodes.T_BYTE) {
                    return "removed-non-byte-array";
                }
                byteArrays++;
            }
            if (opcode == Opcodes.ATHROW || opcode == Opcodes.MONITORENTER
                    || opcode == Opcodes.MONITOREXIT || opcode == Opcodes.RETURN) {
                return "removed-side-effect-opcode=" + opcode;
            }
        }
        if (countCall(calls, "javax/crypto/Cipher.getInstance") != 1
                || countCall(calls, "javax/crypto/Cipher.init") != 1
                || countCall(calls, "javax/crypto/Cipher.doFinal") != 1
                || countCall(calls, "javax/crypto/SecretKeyFactory.getInstance") != 1
                || countCall(calls, "javax/crypto/SecretKeyFactory.generateSecret") != 1
                || countCall(calls, "javax/crypto/spec/DESKeySpec.<init>") != 1
                || countCall(calls, "javax/crypto/spec/IvParameterSpec.<init>") != 1) {
            return "removed-crypto-call-multiplicity=" + calls;
        }
        return byteArrays >= 3 ? null : "removed-byte-arrays=" + byteArrays;
    }

    private static String validateNoExternalInbound(Code code, int start, int result,
                                                     int resultExit, int continuation) {
        Set<Integer> removed = removedIndices(start, result, resultExit, continuation);
        for (int source = 0; source < code.nodes.size(); source++) {
            for (int target : code.targets(code.nodes.get(source))) {
                if (removed.contains(target) && !removed.contains(source)) {
                    return "external-inbound=" + source + "->" + target;
                }
            }
        }
        return null;
    }

    private static Set<Integer> removedIndices(int start, int result,
                                               int resultExit, int continuation) {
        Set<Integer> removed = new LinkedHashSet<>();
        for (int index = start; index < result; index++) removed.add(index);
        for (int index = resultExit + 1; index < continuation; index++) removed.add(index);
        return removed;
    }

    private static FieldInsnNode findResultWrite(ClassNode owner, Code code, int result) {
        Set<Integer> seen = new LinkedHashSet<>();
        int index = result;
        for (int steps = 0; steps < 48 && index >= 0 && index < code.nodes.size(); steps++) {
            if (!seen.add(index)) return null;
            AbstractInsnNode insn = code.nodes.get(index);
            int opcode = insn.getOpcode();
            if (insn instanceof FieldInsnNode) {
                FieldInsnNode field = (FieldInsnNode) insn;
                if (opcode == Opcodes.PUTSTATIC && owner.name.equals(field.owner)) return field;
                return null;
            }
            if (insn instanceof MethodInsnNode) {
                MethodInsnNode call = (MethodInsnNode) insn;
                boolean boxing = call.getOpcode() == Opcodes.INVOKESTATIC
                        && (("java/lang/Integer".equals(call.owner)
                        && "valueOf".equals(call.name) && "(I)Ljava/lang/Integer;".equals(call.desc))
                        || ("java/lang/Long".equals(call.owner)
                        && "valueOf".equals(call.name) && "(J)Ljava/lang/Long;".equals(call.desc)));
                if (!boxing) return null;
            }
            if (insn instanceof InvokeDynamicInsnNode || insn instanceof TypeInsnNode
                    || insn instanceof TableSwitchInsnNode || insn instanceof LookupSwitchInsnNode
                    || opcode == Opcodes.ATHROW || opcode == Opcodes.RETURN) return null;
            if (insn instanceof JumpInsnNode) {
                if (opcode != Opcodes.GOTO) return null;
                index = code.target(((JumpInsnNode) insn).label);
            } else {
                index++;
            }
        }
        return null;
    }

    private static void apply(ClassNode owner, Candidate candidate) {
        MethodNode clinit = method(owner, "<clinit>", "()V");
        Code code = new Code(clinit);
        AbstractInsnNode start = code.nodes.get(candidate.startCodeIndex);
        LabelNode result = candidate.resultLabel;
        AbstractInsnNode resultExit = code.nodes.get(candidate.resultExitCodeIndex);
        LabelNode continuation = candidate.continuationLabel;

        InsnList replacement = new InsnList();
        replacement.add(new LdcInsnNode(candidate.plaintext));
        replacement.add(new JumpInsnNode(Opcodes.GOTO, result));
        clinit.instructions.insertBefore(start, replacement);
        removeUntil(clinit.instructions, start, result);
        removeUntil(clinit.instructions, resultExit.getNext(), continuation);
        candidate.applied = true;
    }

    private static void removeUntil(InsnList instructions, AbstractInsnNode start,
                                    AbstractInsnNode exclusiveEnd) {
        AbstractInsnNode cursor = start;
        while (cursor != null && cursor != exclusiveEnd) {
            AbstractInsnNode next = cursor.getNext();
            instructions.remove(cursor);
            cursor = next;
        }
        if (cursor != exclusiveEnd) throw new IllegalStateException("rewrite-boundary-lost");
    }

    private static void assertRewritten(ClassNode owner, Candidate original) {
        MethodNode clinit = method(owner, "<clinit>", "()V");
        if (clinit == null) throw new IllegalStateException("clinit removed");
        for (int index = 0; index < new Code(clinit).nodes.size(); index++) {
            if (isNoPaddingFactory(new Code(clinit), index)) {
                throw new IllegalStateException("NoPadding factory remains");
            }
        }
        boolean fieldWrite = false;
        boolean plaintext = false;
        for (AbstractInsnNode insn = clinit.instructions.getFirst(); insn != null;
             insn = insn.getNext()) {
            if (insn instanceof LdcInsnNode
                    && Long.valueOf(original.plaintext).equals(((LdcInsnNode) insn).cst)) {
                plaintext = true;
            }
            if (insn instanceof FieldInsnNode && insn.getOpcode() == Opcodes.PUTSTATIC) {
                FieldInsnNode field = (FieldInsnNode) insn;
                if (owner.name.equals(field.owner) && original.fieldName.equals(field.name)
                        && original.fieldDesc.equals(field.desc)) fieldWrite = true;
            }
        }
        if (!plaintext || !fieldWrite) throw new IllegalStateException("folded result missing");
        if (original.stateDerived) {
            int stateCalls = countStateCalls(clinit);
            int ownerWrites = countOwnerFieldWrites(owner, clinit);
            if (stateCalls != original.stateCallCount) {
                throw new IllegalStateException("state-calls=" + stateCalls + "/"
                        + original.stateCallCount);
            }
            if (ownerWrites != original.ownerFieldWriteCount) {
                throw new IllegalStateException("owner-field-writes=" + ownerWrites + "/"
                        + original.ownerFieldWriteCount);
            }
            if (!original.keyFieldName.isEmpty()
                    && fieldWriteCount(owner, clinit, original.keyFieldName, "J") != 1) {
                throw new IllegalStateException("long-key-field-write-not-preserved");
            }
        }
    }

    private static boolean isNoPaddingFactory(Code code, int index) {
        if (index <= 0 || index >= code.nodes.size()) return false;
        AbstractInsnNode insn = code.nodes.get(index);
        if (!(insn instanceof MethodInsnNode)) return false;
        MethodInsnNode call = (MethodInsnNode) insn;
        if (call.getOpcode() != Opcodes.INVOKESTATIC
                || !"javax/crypto/Cipher".equals(call.owner)
                || !"getInstance".equals(call.name)
                || !"(Ljava/lang/String;)Ljavax/crypto/Cipher;".equals(call.desc)) return false;
        AbstractInsnNode previous = code.nodes.get(index - 1);
        return previous instanceof LdcInsnNode
                && ALGORITHM.equals(((LdcInsnNode) previous).cst);
    }

    private static boolean hasStateCall(MethodNode method) {
        return countStateCalls(method) != 0;
    }

    private static int countStateCalls(MethodNode method) {
        int result = 0;
        for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
             insn = insn.getNext()) {
            if (!(insn instanceof MethodInsnNode)) continue;
            MethodInsnNode call = (MethodInsnNode) insn;
            if (STATE.equals(call.owner) || STATE_IFACE.equals(call.owner)) result++;
        }
        return result;
    }

    private static int countOwnerFieldWrites(ClassNode owner, MethodNode method) {
        int result = 0;
        for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
             insn = insn.getNext()) {
            if (insn instanceof FieldInsnNode && insn.getOpcode() == Opcodes.PUTSTATIC
                    && owner.name.equals(((FieldInsnNode) insn).owner)) result++;
        }
        return result;
    }

    private static int fieldWriteCount(ClassNode owner, MethodNode method,
                                       String name, String desc) {
        int result = 0;
        for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
             insn = insn.getNext()) {
            if (!(insn instanceof FieldInsnNode) || insn.getOpcode() != Opcodes.PUTSTATIC) {
                continue;
            }
            FieldInsnNode field = (FieldInsnNode) insn;
            if (owner.name.equals(field.owner) && name.equals(field.name)
                    && desc.equals(field.desc)) result++;
        }
        return result;
    }

    private static int uniqueCall(Code code, int from, int to,
                                  String owner, String name) {
        int result = -1;
        for (int index = from; index < to; index++) {
            AbstractInsnNode insn = code.nodes.get(index);
            if (!(insn instanceof MethodInsnNode)) continue;
            MethodInsnNode call = (MethodInsnNode) insn;
            if (!owner.equals(call.owner) || !name.equals(call.name)) continue;
            if (result >= 0) return -1;
            result = index;
        }
        return result;
    }

    private static Set<Long> longConstants(Code code, int from, int to) {
        Set<Long> result = new LinkedHashSet<>();
        for (int index = from; index < to; index++) {
            AbstractInsnNode insn = code.nodes.get(index);
            if (!(insn instanceof LdcInsnNode)
                    || !(((LdcInsnNode) insn).cst instanceof Long)) continue;
            long value = (Long) ((LdcInsnNode) insn).cst;
            if (value != 255L) result.add(value);
        }
        return result;
    }

    private static boolean allowedCryptoCall(MethodInsnNode call) {
        if ("javax/crypto/Cipher".equals(call.owner)) {
            return "getInstance".equals(call.name) || "init".equals(call.name)
                    || "doFinal".equals(call.name);
        }
        if ("javax/crypto/SecretKeyFactory".equals(call.owner)) {
            return "getInstance".equals(call.name) || "generateSecret".equals(call.name);
        }
        return ("javax/crypto/spec/DESKeySpec".equals(call.owner)
                || "javax/crypto/spec/IvParameterSpec".equals(call.owner))
                && "<init>".equals(call.name);
    }

    private static int countCall(Map<String, Integer> calls, String prefix) {
        int result = 0;
        for (Map.Entry<String, Integer> entry : calls.entrySet()) {
            if (entry.getKey().startsWith(prefix)) result += entry.getValue();
        }
        return result;
    }

    private static MethodNode method(ClassNode owner, String name, String desc) {
        for (MethodNode method : owner.methods) {
            if (name.equals(method.name) && desc.equals(method.desc)) return method;
        }
        return null;
    }

    private static FieldNode field(ClassNode owner, String name, String desc) {
        for (FieldNode field : owner.fields) {
            if (name.equals(field.name) && desc.equals(field.desc)) return field;
        }
        return null;
    }

    private static ClassNode readClass(byte[] bytes) {
        ClassNode owner = new ClassNode(Opcodes.ASM9);
        new ClassReader(bytes).accept(owner, 0);
        return owner;
    }

    private static Map<String, ClassNode> classNodes(Map<String, byte[]> bytes) {
        Map<String, ClassNode> result = new LinkedHashMap<>();
        for (Map.Entry<String, byte[]> entry : bytes.entrySet()) {
            result.put(entry.getKey(), readClass(entry.getValue()));
        }
        return result;
    }

    private static byte[] writeClass(ClassNode owner, Map<String, ClassNode> hierarchy) {
        int flags = containsLegacySubroutine(owner)
                ? ClassWriter.COMPUTE_MAXS
                : ClassWriter.COMPUTE_FRAMES | ClassWriter.COMPUTE_MAXS;
        ClassWriter writer = flags == ClassWriter.COMPUTE_MAXS
                ? new ClassWriter(flags)
                : new HierarchyClassWriter(flags, hierarchy);
        owner.accept(writer);
        return writer.toByteArray();
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
        ClassNode owner = readClass(bytes);
        for (MethodNode method : owner.methods) {
            if (method.instructions != null && method.instructions.size() != 0) {
                new Analyzer<BasicValue>(new BasicVerifier()).analyze(owner.name, method);
            }
        }
    }

    private static List<EntryBytes> readEntries(Path input) throws IOException {
        List<EntryBytes> result = new ArrayList<>();
        try (ZipInputStream zip = new ZipInputStream(Files.newInputStream(input))) {
            ZipEntry entry;
            while ((entry = zip.getNextEntry()) != null) {
                result.add(new EntryBytes(entry, readAll(zip)));
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

    private static void writeArchive(List<EntryBytes> entries,
                                     Map<String, byte[]> replacements, Path output,
                                     Summary summary, List<String> verifier) throws IOException {
        Path parent = output.toAbsolutePath().getParent();
        if (parent == null) parent = Paths.get(".").toAbsolutePath();
        Files.createDirectories(parent);
        Path temporary = Files.createTempFile(parent,
                output.getFileName().toString() + ".", ".tmp");
        try {
            Set<String> applied = new LinkedHashSet<>();
            try (ZipOutputStream zip = new ZipOutputStream(Files.newOutputStream(temporary))) {
                for (EntryBytes entry : entries) {
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
                    } else {
                        written.setMethod(ZipEntry.DEFLATED);
                    }
                    zip.putNextEntry(written);
                    zip.write(bytes);
                    zip.closeEntry();
                }
            }
            if (!applied.equals(replacements.keySet())) {
                throw new IOException("replacement-coverage=" + applied.size() + "/"
                        + replacements.size());
            }
            verifyArchive(temporary, summary, verifier);
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

    private static void verifyArchive(Path archive, Summary summary,
                                      List<String> verifier) throws IOException {
        try (ZipInputStream zip = new ZipInputStream(Files.newInputStream(archive))) {
            ZipEntry entry;
            while ((entry = zip.getNextEntry()) != null) {
                byte[] bytes = readAll(zip);
                if (!entry.getName().endsWith(".class")) continue;
                summary.outputClasses++;
                String owner = entry.getName();
                try {
                    verifyClass(bytes);
                    ClassNode node = readClass(bytes);
                    owner = node.name;
                    summary.outputResidualNoPadding += countNoPadding(node);
                } catch (Throwable failure) {
                    summary.outputVerificationErrors++;
                    verifier.add(tsv("archive", owner, "FAIL", shortReason(failure)));
                }
            }
        }
        verifier.add(tsv("archive", "*", summary.outputVerificationErrors == 0
                ? "PASS" : "FAIL", "classes=" + summary.outputClasses
                + ";errors=" + summary.outputVerificationErrors));
    }

    private static int countNoPadding(ClassNode owner) {
        int result = 0;
        for (MethodNode method : owner.methods) {
            Code code = new Code(method);
            for (int index = 0; index < code.nodes.size(); index++) {
                if (isNoPaddingFactory(code, index)) result++;
            }
        }
        return result;
    }

    private static void writeReports(Path input, Path output, Path reportDirectory,
                                     Summary summary, List<Candidate> candidates,
                                     List<String> verifier,
                                     boolean stateDerived) throws IOException {
        candidates.sort(Comparator.comparing(candidate -> candidate.owner));
        List<String> rows = new ArrayList<>();
        rows.add("class\tinsns\tnopadding\tfield\tfield_desc\tstate_derived"
                + "\tclass_key_hex\touter_mask_hex\tkey_hex\tkey_source\tkey_chain"
                + "\tciphertext_hex\tplaintext_hex\tstart\tresult\tcontinuation"
                + "\tproven\taction\treason");
        for (Candidate candidate : candidates) rows.add(candidate.row());
        Files.write(reportDirectory.resolve("candidates.tsv"), rows, StandardCharsets.UTF_8);
        Files.write(reportDirectory.resolve("verifier.tsv"), verifier,
                StandardCharsets.UTF_8);

        List<String> audit = new ArrayList<>();
        audit.add("input=" + input.toAbsolutePath().normalize());
        audit.add("input_sha256=" + sha256(Files.readAllBytes(input)));
        audit.add("output=" + (output == null ? "" : output.toAbsolutePath().normalize()));
        audit.add("parsed_classes=" + summary.parsedClasses);
        audit.add("candidates=" + summary.candidates);
        audit.add("proven=" + summary.proven);
        audit.add("rejected=" + summary.rejected);
        audit.add("changed_classes=" + summary.changedClasses);
        audit.add("rollbacks=" + summary.rollbacks);
        audit.add("output_classes=" + summary.outputClasses);
        audit.add("output_residual_nopadding=" + summary.outputResidualNoPadding);
        audit.add("output_verification_errors=" + summary.outputVerificationErrors);
        audit.add("output_committed=" + summary.outputCommitted);
        audit.add("input_classes_loaded=false");
        audit.add("input_classes_initialized=false");
        audit.add("policy=" + (stateDerived
                ? "state-derived key with statically evaluated JVM superclass provenance; "
                + "long-key bootstrap, result block, and business continuation retained; "
                + "exception/table/helper shapes rejected"
                : "literal-key closed CFG island only; original result block and business "
                + "continuation retained; state/exception/table/helper shapes rejected"));
        audit.add("gate=" + (summary.rollbacks == 0 && summary.outputVerificationErrors == 0
                ? "PASS" : "FAIL"));
        Files.write(reportDirectory.resolve("audit.txt"), audit, StandardCharsets.UTF_8);
        Files.write(reportDirectory.resolve("gate.txt"),
                ((summary.rollbacks == 0 && summary.outputVerificationErrors == 0
                        ? "PASS" : "FAIL") + "\n").getBytes(StandardCharsets.UTF_8));
    }

    private static byte[] readAll(ZipInputStream zip) throws IOException {
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        byte[] buffer = new byte[8192];
        int read;
        while ((read = zip.read(buffer)) >= 0) if (read != 0) out.write(buffer, 0, read);
        return out.toByteArray();
    }

    private static String sha256(byte[] bytes) throws IOException {
        try {
            MessageDigest digest = MessageDigest.getInstance("SHA-256");
            StringBuilder result = new StringBuilder();
            for (byte value : digest.digest(bytes)) result.append(String.format("%02X", value));
            return result.toString();
        } catch (Exception failure) {
            throw new IOException(failure);
        }
    }

    private static String shortReason(Throwable failure) {
        String message = failure.getMessage();
        return failure.getClass().getSimpleName()
                + (message == null || message.isEmpty() ? "" : ":" + message);
    }

    private static String tsv(Object... values) {
        List<String> result = new ArrayList<>();
        for (Object value : values) result.add(String.valueOf(value).replace('\t', ' ')
                .replace('\n', ' ').replace('\r', ' '));
        return String.join("\t", result);
    }

    static final class Summary {
        int parsedClasses;
        int candidates;
        int proven;
        int rejected;
        int changedClasses;
        int rollbacks;
        int outputClasses;
        int outputResidualNoPadding;
        int outputVerificationErrors;
        boolean outputCommitted;
    }

    private static final class Candidate {
        final String owner;
        int instructions;
        int noPaddingCalls;
        int startCodeIndex = -1;
        int resultCodeIndex = -1;
        int resultExitCodeIndex = -1;
        int continuationCodeIndex = -1;
        LabelNode resultLabel;
        LabelNode continuationLabel;
        String fieldName = "";
        String fieldDesc = "";
        String keyFieldName = "";
        boolean stateDerived;
        long classKey;
        long outerMask;
        String keySource = "";
        String keyChain = "";
        int stateCallCount;
        int ownerFieldWriteCount;
        long key;
        long ciphertext;
        long plaintext;
        boolean proven;
        boolean applied;
        String action = "REJECT";
        String reason = "";

        Candidate(String owner) {
            this.owner = owner;
        }

        Candidate reject(String failure) {
            this.reason = failure;
            return this;
        }

        String row() {
            return tsv(owner, instructions, noPaddingCalls, fieldName, fieldDesc,
                    stateDerived, stateDerived ? hex(classKey) : "",
                    stateDerived ? hex(outerMask) : "", hex(key), keySource, keyChain,
                    hex(ciphertext), hex(plaintext), startCodeIndex,
                    resultCodeIndex, continuationCodeIndex, proven, action, reason);
        }
    }

    static final class KeyProof {
        final String owner;
        final long classKey;
        final String source;
        final String chain;

        KeyProof(String owner, long classKey, String source, String chain) {
            this.owner = owner;
            this.classKey = classKey;
            this.source = source;
            this.chain = chain;
        }
    }

    private static String hex(long value) {
        return String.format("%016X", value);
    }

    private static final class Code {
        final MethodNode method;
        final List<AbstractInsnNode> nodes = new ArrayList<>();
        final IdentityHashMap<AbstractInsnNode, Integer> codeIndices = new IdentityHashMap<>();
        final IdentityHashMap<AbstractInsnNode, Integer> rawIndices = new IdentityHashMap<>();

        Code(MethodNode method) {
            this.method = method;
            int raw = 0;
            for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
                 insn = insn.getNext(), raw++) {
                rawIndices.put(insn, raw);
                if (insn.getOpcode() >= 0) {
                    codeIndices.put(insn, nodes.size());
                    nodes.add(insn);
                }
            }
        }

        int rawIndex(AbstractInsnNode insn) {
            Integer result = rawIndices.get(insn);
            if (result == null) throw new IllegalArgumentException("raw instruction missing");
            return result;
        }

        int target(LabelNode label) {
            AbstractInsnNode cursor = label;
            while (cursor != null && cursor.getOpcode() < 0) cursor = cursor.getNext();
            Integer result = cursor == null ? null : codeIndices.get(cursor);
            if (result == null) throw new IllegalArgumentException("label target missing");
            return result;
        }

        List<Integer> targets(AbstractInsnNode insn) {
            List<Integer> result = new ArrayList<>();
            if (insn instanceof JumpInsnNode) {
                result.add(target(((JumpInsnNode) insn).label));
            } else if (insn instanceof TableSwitchInsnNode) {
                TableSwitchInsnNode table = (TableSwitchInsnNode) insn;
                result.add(target(table.dflt));
                for (LabelNode label : table.labels) result.add(target(label));
            } else if (insn instanceof LookupSwitchInsnNode) {
                LookupSwitchInsnNode lookup = (LookupSwitchInsnNode) insn;
                result.add(target(lookup.dflt));
                for (LabelNode label : lookup.labels) result.add(target(label));
            }
            return result;
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
            Set<String> rightTypes = supertypes(right);
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
            return "java/lang/Object".equals(target) || supertypes(source).contains(target);
        }

        private Set<String> supertypes(String type) {
            return new LinkedHashSet<>(orderedSupertypes(type));
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
}
