package cn.openvape.flowdeobf;

import org.objectweb.asm.ClassReader;
import org.objectweb.asm.ClassWriter;
import org.objectweb.asm.Opcodes;
import org.objectweb.asm.tree.AbstractInsnNode;
import org.objectweb.asm.tree.ClassNode;
import org.objectweb.asm.tree.FieldInsnNode;
import org.objectweb.asm.tree.FieldNode;
import org.objectweb.asm.tree.IincInsnNode;
import org.objectweb.asm.tree.InsnList;
import org.objectweb.asm.tree.InsnNode;
import org.objectweb.asm.tree.IntInsnNode;
import org.objectweb.asm.tree.InvokeDynamicInsnNode;
import org.objectweb.asm.tree.JumpInsnNode;
import org.objectweb.asm.tree.LabelNode;
import org.objectweb.asm.tree.LdcInsnNode;
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
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.AtomicMoveNotSupportedException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.StandardCopyOption;
import java.security.MessageDigest;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
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
 * Folds canonical NoPadding scalar and packed-long fragments wrapped by
 * {@code catch (Exception) -> ExceptionInInitializerError}.
 *
 * <p>The pass proves a single complete exception range, a canonical handler
 * with no normal predecessor, full protected-range coverage of every removed
 * instruction, and a closed normal CFG.  It replaces only the crypto/result
 * producer and an optional fake key-byte tail; business initialization and the
 * original handler remain bytecode-for-bytecode equivalent at the executable
 * instruction level.  Input classes are parsed as ASM data and are never
 * defined, loaded, initialized, or reflected on.</p>
 */
public final class ZkmNoPaddingExceptionFragmentDeobfuscator {
    private static final String ALGORITHM = "DES/CBC/NoPadding";
    private static final String KEY_ALGORITHM = "DES";
    private static final String LATIN1 = "ISO-8859-1";
    private static final String STATE = ObfRuntimeNames.STATE;
    private static final String STATE_IFACE =
            ObfRuntimeNames.STATE_INTERFACE;

    private ZkmNoPaddingExceptionFragmentDeobfuscator() {
    }

    public static void main(String[] args) throws Exception {
        if (args.length != 2 && args.length != 3) {
            System.err.println("usage: ZkmNoPaddingExceptionFragmentDeobfuscator"
                    + " <input.jar> <report-dir> [output.jar]");
            System.exit(2);
        }
        Summary summary = rewrite(Paths.get(args[0]), Paths.get(args[1]),
                args.length == 3 ? Paths.get(args[2]) : null);
        System.out.println("classes=" + summary.parsedClasses
                + " candidates=" + summary.candidates + " proven=" + summary.proven
                + " changed=" + summary.changedClasses + " literal="
                + summary.literalClasses + " state=" + summary.stateClasses
                + " scalar=" + summary.scalarClasses + " arrays="
                + summary.arrayClasses + " rollbacks=" + summary.rollbacks
                + " des=" + summary.inputDesCalls + "->" + summary.outputDesCalls
                + " committed=" + summary.outputCommitted);
    }

    static Summary rewrite(Path input, Path reportDirectory, Path output) throws Exception {
        if (output != null && input.toAbsolutePath().normalize()
                .equals(output.toAbsolutePath().normalize())) {
            throw new IllegalArgumentException("output must not replace input");
        }
        Files.createDirectories(reportDirectory);
        List<EntryBytes> entries = readEntries(input);
        Map<String, byte[]> originals = classBytes(entries);
        Map<String, ZkmNoPaddingLiteralFragmentDeobfuscator.KeyProof> keyProofs =
                ZkmNoPaddingStateFragmentDeobfuscator.keyProofs(input);
        Summary summary = new Summary();
        summary.parsedClasses = originals.size();
        summary.inputDesCalls = countDesFactories(originals);
        summary.inputNoPaddingCalls = countNoPaddingFactories(originals);
        List<Candidate> candidates = new ArrayList<>();
        Map<String, byte[]> replacements = new LinkedHashMap<>();
        List<String> verifier = new ArrayList<>();
        verifier.add("scope\tclass\tstatus\tdetail");

        List<String> names = new ArrayList<>(originals.keySet());
        Collections.sort(names);
        for (String name : names) {
            ClassNode owner = readClass(originals.get(name));
            Candidate candidate = inspect(owner, keyProofs.get(name));
            if (candidate == null) continue;
            candidates.add(candidate);
            summary.candidates++;
            if (!candidate.proven) {
                summary.rejected++;
                continue;
            }
            summary.proven++;
            if (candidate.stateDerived) summary.stateClasses++;
            else summary.literalClasses++;
            if (candidate.kind == Kind.SCALAR) summary.scalarClasses++;
            else {
                summary.arrayClasses++;
                summary.tableEntries += candidate.values.size();
            }
            if (output == null) {
                candidate.action = "PROVEN_DRY_RUN";
                continue;
            }

            ZkmClassRewriteTransaction.Result transaction =
                    ZkmClassRewriteTransaction.attempt(originals.get(name), rewritten -> {
                        Candidate fresh = inspect(rewritten, keyProofs.get(name));
                        if (fresh == null || !fresh.proven || fresh.kind != candidate.kind
                                || fresh.key != candidate.key
                                || fresh.ciphertext != candidate.ciphertext
                                || !fresh.fieldName.equals(candidate.fieldName)
                                || !fresh.fieldDesc.equals(candidate.fieldDesc)
                                || !fresh.values.equals(candidate.values)) {
                            throw new IllegalStateException("proof changed before mutation");
                        }
                        apply(rewritten, fresh);
                    }, emitted -> assertRewritten(emitted, candidate));
            if (transaction.isCommitted()) {
                replacements.put(name, transaction.bytes());
                candidate.action = "REWRITE";
                summary.changedClasses++;
                verifier.add(tsv("class", name, "PASS", "kind=" + candidate.kind
                        + ";field=" + candidate.fieldName + candidate.fieldDesc));
            } else {
                candidate.action = "ROLLBACK";
                candidate.reason += ";rollback=" + transaction.stage() + ":"
                        + transaction.reason();
                summary.rollbacks++;
                verifier.add(tsv("class", name, "FAIL", transaction.stage() + ":"
                        + transaction.reason()));
            }
        }

        if (output != null) {
            writeArchive(entries, replacements, output, summary, verifier);
        } else {
            summary.outputDesCalls = summary.inputDesCalls;
            summary.outputNoPaddingCalls = summary.inputNoPaddingCalls;
        }
        writeReports(input, output, reportDirectory, summary, candidates, verifier);
        return summary;
    }

    private static Candidate inspect(
            ClassNode owner,
            ZkmNoPaddingLiteralFragmentDeobfuscator.KeyProof keyProof) {
        MethodNode clinit = method(owner, "<clinit>", "()V");
        if (clinit == null) return null;
        Code code = new Code(clinit);
        List<MethodInsnNode> factories = new ArrayList<>();
        for (AbstractInsnNode insn : code.executable) {
            if (isNoPaddingFactory(insn)) factories.add((MethodInsnNode) insn);
        }
        if (factories.isEmpty()) return null;
        if (clinit.tryCatchBlocks == null || clinit.tryCatchBlocks.isEmpty()) return null;

        Candidate candidate = new Candidate(owner.name);
        candidate.instructions = code.executable.size();
        candidate.noPaddingCalls = factories.size();
        if (factories.size() != 1) {
            return candidate.reject("nopadding-factories=" + factories.size());
        }
        if (clinit.tryCatchBlocks.size() != 1) {
            return candidate.reject("exception-ranges=" + clinit.tryCatchBlocks.size());
        }
        MethodInsnNode factory = factories.get(0);
        AbstractInsnNode algorithm = previousCode(factory);
        if (!(algorithm instanceof LdcInsnNode)
                || !ALGORITHM.equals(((LdcInsnNode) algorithm).cst)) {
            return candidate.reject("algorithm-source");
        }
        TryCatchBlockNode wrapper = clinit.tryCatchBlocks.get(0);
        String handlerFailure = proveHandler(code, wrapper);
        if (handlerFailure != null) return candidate.reject(handlerFailure);
        candidate.tryStartRaw = code.raw(wrapper.start);
        candidate.tryEndRaw = code.raw(wrapper.end);
        candidate.handlerRaw = code.raw(wrapper.handler);

        int algorithmRaw = code.raw(algorithm);
        int tryStart = code.raw(wrapper.start);
        int tryEnd = code.raw(wrapper.end);
        if (!(tryStart <= algorithmRaw && algorithmRaw < tryEnd)) {
            return candidate.reject("algorithm-outside-wrapper=" + tryStart + "/"
                    + algorithmRaw + "/" + tryEnd);
        }

        MethodInsnNode init = uniqueCall(code, algorithmRaw, tryEnd,
                "javax/crypto/Cipher", "init");
        MethodInsnNode doFinal = uniqueCall(code, algorithmRaw, tryEnd,
                "javax/crypto/Cipher", "doFinal");
        if (init == null || doFinal == null || code.raw(init) >= code.raw(doFinal)) {
            return candidate.reject("cipher-init-final-order");
        }
        FieldInsnNode target = firstOwnerWrite(owner, code, code.raw(doFinal), tryEnd);
        if (target == null || !("J".equals(target.desc) || "[J".equals(target.desc))) {
            return candidate.reject("result-write-not-scalar-or-long-array");
        }
        FieldNode targetField = field(owner, target.name, target.desc);
        if (targetField == null
                || (targetField.access & (Opcodes.ACC_STATIC | Opcodes.ACC_FINAL))
                != (Opcodes.ACC_STATIC | Opcodes.ACC_FINAL)) {
            return candidate.reject("result-field-not-static-final=" + target.name
                    + target.desc);
        }
        candidate.kind = "J".equals(target.desc) ? Kind.SCALAR : Kind.LONG_ARRAY;
        candidate.fieldName = target.name;
        candidate.fieldDesc = target.desc;
        candidate.algorithm = algorithm;
        candidate.targetWrite = target;
        candidate.wrapper = wrapper;

        Set<Long> literalKeys = longConstants(code, algorithmRaw, code.raw(init));
        if (literalKeys.size() == 1) {
            candidate.key = literalKeys.iterator().next();
            candidate.keySource = "LDC_LONG";
        } else if (literalKeys.isEmpty() && hasStateCall(clinit)) {
            String failure = deriveStateKey(owner, clinit, code, algorithmRaw,
                    code.raw(init), keyProof, candidate);
            if (failure != null) return candidate.reject(failure);
        } else {
            return candidate.reject("literal-key-count=" + literalKeys.size());
        }

        ZkmDesConstantEvaluator.KeyMaterial material =
                ZkmDesConstantEvaluator.KeyMaterial.proven(candidate.key,
                        candidate.stateDerived ? "ZKM_LONG_KEY_PROVENANCE" : "LDC_LONG",
                        "canonical exception-wrapped NoPadding " + candidate.kind);
        try {
            if (candidate.kind == Kind.SCALAR) {
                Set<Long> ciphertexts = longConstants(code, code.raw(init) + 1,
                        code.raw(doFinal));
                if (ciphertexts.size() != 1) {
                    return candidate.reject("ciphertext-count=" + ciphertexts.size());
                }
                candidate.ciphertext = ciphertexts.iterator().next();
                candidate.values.add(ZkmDesConstantEvaluator.decryptLong(
                        material, candidate.ciphertext));
            } else {
                String packed = uniquePackedLiteral(code, code.raw(init),
                        code.raw(target));
                if (packed == null) return candidate.reject("packed-literal-not-unique");
                candidate.packedLength = packed.length();
                candidate.values.addAll(
                        ZkmDesConstantEvaluator.decryptPackedLongs(material, packed));
                Integer capacity = uniqueLongArrayCapacity(code, code.raw(init),
                        code.raw(target));
                if (capacity == null || capacity.intValue() != candidate.values.size()) {
                    return candidate.reject("long-array-capacity=" + capacity + "/"
                            + candidate.values.size());
                }
            }
        } catch (Throwable failure) {
            return candidate.reject("decrypt=" + shortReason(failure));
        }

        JumpInsnNode resultExit = gotoTargeting(code, code.raw(target) + 1,
                tryEnd, wrapper.end);
        candidate.resultExit = resultExit;
        if (resultExit != null) {
            AbstractInsnNode tailStart = resultExit.getNext();
            if (tailStart == null) return candidate.reject("tail-start-missing");
            candidate.tailStart = tailStart;
        }
        candidate.removed = removedNodes(code, algorithm, target,
                candidate.tailStart, wrapper.end);
        if (candidate.removed.isEmpty()) return candidate.reject("empty-removal");

        String rangeFailure = proveRemovedRange(owner, code, candidate, init, doFinal);
        if (rangeFailure != null) return candidate.reject(rangeFailure);
        String cfgFailure = proveNormalClosure(code, candidate.removed, algorithm);
        if (cfgFailure != null) return candidate.reject(cfgFailure);
        for (AbstractInsnNode removed : candidate.removed) {
            int raw = code.raw(removed);
            if (removed.getOpcode() >= 0 && !(tryStart <= raw && raw < tryEnd)) {
                return candidate.reject("removed-outside-try=" + raw);
            }
        }

        candidate.stateCallCount = countStateCalls(clinit);
        candidate.ownerWrites = ownerWriteCounts(owner, clinit);
        candidate.expectedExecutable = expectedExecutable(code, candidate);
        candidate.proven = true;
        candidate.reason = "canonical-exception-wrapper;complete-protected-removal;"
                + "handler-preserved;normal-cfg-closed;business-executable-preserved;key="
                + candidate.keySource;
        return candidate;
    }

    private static String proveHandler(Code code, TryCatchBlockNode wrapper) {
        if (!"java/lang/Exception".equals(wrapper.type)) {
            return "handler-type=" + wrapper.type;
        }
        int start = code.raw(wrapper.start);
        int end = code.raw(wrapper.end);
        int handler = code.raw(wrapper.handler);
        if (!(start < end && end < handler)) {
            return "handler-order=" + start + "/" + end + "/" + handler;
        }
        AbstractInsnNode previous = previousCode(wrapper.handler);
        if (!(previous instanceof JumpInsnNode)
                || previous.getOpcode() != Opcodes.GOTO) {
            return "handler-normal-predecessor-not-goto";
        }
        int done = code.raw(((JumpInsnNode) previous).label);
        if (done <= handler) return "handler-skip-target=" + done;
        for (AbstractInsnNode insn : code.executable) {
            if (!(insn instanceof JumpInsnNode
                    || insn instanceof TableSwitchInsnNode
                    || insn instanceof LookupSwitchInsnNode)) continue;
            for (LabelNode target : labels(insn)) {
                if (target == wrapper.handler) return "normal-edge-to-handler";
            }
        }

        List<AbstractInsnNode> body = new ArrayList<>();
        AbstractInsnNode cursor = firstCode(wrapper.handler);
        while (cursor != null && code.raw(cursor) < done) {
            if (cursor.getOpcode() >= 0) body.add(cursor);
            cursor = cursor.getNext();
        }
        if (body.size() != 6) return "handler-insns=" + body.size();
        if (!(body.get(0) instanceof VarInsnNode)
                || body.get(0).getOpcode() != Opcodes.ASTORE) return "handler-astore";
        int local = ((VarInsnNode) body.get(0)).var;
        if (!(body.get(1) instanceof TypeInsnNode)
                || body.get(1).getOpcode() != Opcodes.NEW
                || !"java/lang/ExceptionInInitializerError"
                .equals(((TypeInsnNode) body.get(1)).desc)
                || body.get(2).getOpcode() != Opcodes.DUP
                || !(body.get(3) instanceof VarInsnNode)
                || body.get(3).getOpcode() != Opcodes.ALOAD
                || ((VarInsnNode) body.get(3)).var != local
                || !(body.get(4) instanceof MethodInsnNode)
                || !isCall(body.get(4), Opcodes.INVOKESPECIAL,
                "java/lang/ExceptionInInitializerError", "<init>",
                "(Ljava/lang/Throwable;)V")
                || body.get(5).getOpcode() != Opcodes.ATHROW) {
            return "handler-noncanonical";
        }
        return null;
    }

    private static String deriveStateKey(
            ClassNode owner, MethodNode clinit, Code code, int start, int init,
            ZkmNoPaddingLiteralFragmentDeobfuscator.KeyProof proof,
            Candidate candidate) {
        if (proof == null) return "state-class-key-unproven";
        if (!owner.name.equals(proof.owner)) return "key-proof-owner=" + proof.owner;
        Set<Integer> locals = new LinkedHashSet<>();
        for (AbstractInsnNode insn : code.between(start, init)) {
            if (insn instanceof VarInsnNode && insn.getOpcode() == Opcodes.LLOAD) {
                locals.add(((VarInsnNode) insn).var);
            }
        }
        if (locals.size() != 1) return "state-key-long-loads=" + locals;
        int local = locals.iterator().next();
        VarInsnNode definition = null;
        for (AbstractInsnNode insn : code.between(0, start)) {
            if (insn instanceof VarInsnNode && insn.getOpcode() == Opcodes.LSTORE
                    && ((VarInsnNode) insn).var == local) {
                if (definition != null) return "state-key-local-definitions-multiple";
                definition = (VarInsnNode) insn;
            }
        }
        if (definition == null) return "state-key-local-definition";
        AbstractInsnNode xor = previousCode(definition);
        if (xor == null || xor.getOpcode() != Opcodes.LXOR) {
            return "state-key-local-producer";
        }
        AbstractInsnNode left;
        AbstractInsnNode right;
        try {
            Frame<SourceValue>[] frames = new Analyzer<SourceValue>(new SourceInterpreter())
                    .analyze(owner.name, clinit);
            Frame<SourceValue> frame = frames[code.raw(xor)];
            if (frame == null || frame.getStackSize() < 2) return "state-key-xor-frame";
            left = uniqueSource(frame.getStack(frame.getStackSize() - 2));
            right = uniqueSource(frame.getStack(frame.getStackSize() - 1));
        } catch (Throwable failure) {
            return "state-key-source-analysis=" + shortReason(failure);
        }
        LdcInsnNode mask = left instanceof LdcInsnNode
                && ((LdcInsnNode) left).cst instanceof Long ? (LdcInsnNode) left
                : right instanceof LdcInsnNode && ((LdcInsnNode) right).cst instanceof Long
                ? (LdcInsnNode) right : null;
        AbstractInsnNode stateValue = mask == left ? right : left;
        if (mask == null) return "state-key-mask-source";
        if (stateValue instanceof FieldInsnNode
                && stateValue.getOpcode() == Opcodes.GETSTATIC) {
            FieldInsnNode read = (FieldInsnNode) stateValue;
            if (!owner.name.equals(read.owner) || !"J".equals(read.desc)) {
                return "state-key-field=" + read.owner + "." + read.name + read.desc;
            }
            FieldNode field = field(owner, read.name, read.desc);
            if (field == null || (field.access & (Opcodes.ACC_STATIC | Opcodes.ACC_FINAL))
                    != (Opcodes.ACC_STATIC | Opcodes.ACC_FINAL)) {
                return "state-key-field-not-static-final";
            }
            int writes = 0;
            for (AbstractInsnNode insn : code.between(0, code.raw(definition))) {
                if (!(insn instanceof FieldInsnNode)
                        || insn.getOpcode() != Opcodes.PUTSTATIC) continue;
                FieldInsnNode write = (FieldInsnNode) insn;
                if (read.owner.equals(write.owner) && read.name.equals(write.name)
                        && read.desc.equals(write.desc)
                        && isStateTransform(previousCode(write))) writes++;
            }
            if (writes != 1) return "state-key-field-writes=" + writes;
        } else if (!isStateTransform(stateValue)) {
            return "state-key-value-source=" + (stateValue == null ? "null"
                    : stateValue.getClass().getSimpleName() + ":" + stateValue.getOpcode());
        }
        int bootstraps = 0;
        int transforms = 0;
        for (AbstractInsnNode insn : code.between(0, start)) {
            if (!(insn instanceof MethodInsnNode)) continue;
            MethodInsnNode call = (MethodInsnNode) insn;
            if (STATE.equals(call.owner)) bootstraps++;
            if (isStateTransform(call)) transforms++;
        }
        if (bootstraps != 1 || transforms != 1) {
            return "state-key-call-count=" + bootstraps + "/" + transforms;
        }
        candidate.stateDerived = true;
        candidate.classKey = proof.classKey;
        candidate.outerMask = (Long) mask.cst;
        candidate.key = proof.classKey ^ candidate.outerMask;
        candidate.keySource = proof.source;
        candidate.keyChain = proof.chain;
        return null;
    }

    private static String proveRemovedRange(ClassNode owner, Code code,
                                            Candidate candidate,
                                            MethodInsnNode init,
                                            MethodInsnNode doFinal) {
        Map<String, Integer> calls = new LinkedHashMap<>();
        int byteArrays = 0;
        int longArrays = 0;
        int longStores = 0;
        for (AbstractInsnNode insn : candidate.removed) {
            int opcode = insn.getOpcode();
            if (opcode < 0) continue;
            if (insn instanceof InvokeDynamicInsnNode) return "removed-indy";
            if (insn instanceof FieldInsnNode) {
                FieldInsnNode field = (FieldInsnNode) insn;
                if (insn != candidate.targetWrite || opcode != Opcodes.PUTSTATIC
                        || !owner.name.equals(field.owner)) {
                    return "removed-field=" + field.owner + "." + field.name + field.desc;
                }
            }
            if (insn instanceof MethodInsnNode) {
                MethodInsnNode call = (MethodInsnNode) insn;
                if (!allowedCall(call, candidate.kind)) {
                    return "removed-call=" + call.owner + "." + call.name + call.desc;
                }
                String id = call.owner + "." + call.name + call.desc;
                calls.put(id, calls.getOrDefault(id, 0) + 1);
            }
            if (insn instanceof TypeInsnNode) {
                TypeInsnNode type = (TypeInsnNode) insn;
                if (opcode != Opcodes.NEW
                        || !("javax/crypto/spec/DESKeySpec".equals(type.desc)
                        || "javax/crypto/spec/IvParameterSpec".equals(type.desc))) {
                    return "removed-type=" + opcode + ":" + type.desc;
                }
            }
            if (insn instanceof IntInsnNode && opcode == Opcodes.NEWARRAY) {
                int operand = ((IntInsnNode) insn).operand;
                if (operand == Opcodes.T_BYTE) byteArrays++;
                else if (operand == Opcodes.T_LONG) longArrays++;
                else return "removed-newarray=" + operand;
            }
            if (opcode == Opcodes.LASTORE) longStores++;
            if (opcode == Opcodes.ATHROW || opcode == Opcodes.RETURN
                    || opcode == Opcodes.MONITORENTER || opcode == Opcodes.MONITOREXIT) {
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
            return "crypto-call-multiplicity=" + calls;
        }
        if (byteArrays < 3) return "byte-arrays=" + byteArrays;
        if (candidate.kind == Kind.LONG_ARRAY) {
            if (countCall(calls, "java/lang/String.length") != 1
                    || countCall(calls, "java/lang/String.substring") != 1
                    || countCall(calls, "java/lang/String.getBytes") != 1
                    || longArrays != 1 || longStores != 1) {
                return "long-array-shape=calls:" + calls + ",arrays:" + longArrays
                        + ",stores:" + longStores;
            }
        } else if (longArrays != 0 || longStores != 0) {
            return "scalar-has-long-array";
        }
        if (!candidate.removed.contains(init) || !candidate.removed.contains(doFinal)) {
            return "crypto-call-outside-removal";
        }
        String dataflow = proveCanonicalDataflow(code, candidate, init, doFinal);
        if (dataflow != null) return dataflow;
        return null;
    }

    private static String proveCanonicalDataflow(Code code, Candidate candidate,
                                                 MethodInsnNode init,
                                                 MethodInsnNode doFinal) {
        int initRaw = code.raw(init);
        int finalRaw = code.raw(doFinal);
        int targetRaw = code.raw(candidate.targetWrite);

        LdcInsnNode ciphertextNode = null;
        VarInsnNode ciphertextStore = null;
        for (AbstractInsnNode insn : code.between(initRaw + 1, finalRaw)) {
            if (!(insn instanceof LdcInsnNode)
                    || !(((LdcInsnNode) insn).cst instanceof Long)
                    || Long.valueOf(255L).equals(((LdcInsnNode) insn).cst)) continue;
            AbstractInsnNode next = nextCode(insn);
            if (!(next instanceof VarInsnNode) || next.getOpcode() != Opcodes.LSTORE) {
                continue;
            }
            if (ciphertextNode != null) return "ciphertext-local-multiple";
            ciphertextNode = (LdcInsnNode) insn;
            ciphertextStore = (VarInsnNode) next;
        }
        if (candidate.kind == Kind.SCALAR) {
            if (ciphertextNode == null || ciphertextStore == null
                    || ((Long) ciphertextNode.cst).longValue() != candidate.ciphertext) {
                return "ciphertext-local-binding";
            }
            int loads = countVar(code, code.raw(ciphertextStore) + 1, finalRaw,
                    Opcodes.LLOAD, ciphertextStore.var);
            if (loads != 8) return "ciphertext-byte-loads=" + loads;
        }

        AbstractInsnNode resultStoreNode = nextCode(doFinal);
        if (!(resultStoreNode instanceof VarInsnNode)
                || resultStoreNode.getOpcode() != Opcodes.ASTORE) {
            return "do-final-result-store";
        }
        int resultLocal = ((VarInsnNode) resultStoreNode).var;
        int resultLoads = countVar(code, code.raw(resultStoreNode) + 1, targetRaw,
                Opcodes.ALOAD, resultLocal);
        int baload = countOpcode(code, code.raw(resultStoreNode) + 1, targetRaw,
                Opcodes.BALOAD);
        int i2l = countOpcode(code, code.raw(resultStoreNode) + 1, targetRaw,
                Opcodes.I2L);
        int land = countOpcode(code, code.raw(resultStoreNode) + 1, targetRaw,
                Opcodes.LAND);
        int lor = countOpcode(code, code.raw(resultStoreNode) + 1, targetRaw,
                Opcodes.LOR);
        int lshl = countOpcode(code, code.raw(resultStoreNode) + 1, targetRaw,
                Opcodes.LSHL);
        if (resultLoads != 8 || baload != 8 || i2l != 8 || land != 8
                || lor != 7 || lshl != 7) {
            return "result-long-reconstruction=" + resultLoads + "/" + baload + "/"
                    + i2l + "/" + land + "/" + lor + "/" + lshl;
        }
        Set<Integer> shifts = new LinkedHashSet<>();
        for (AbstractInsnNode insn : code.between(code.raw(resultStoreNode) + 1,
                targetRaw)) {
            if (insn.getOpcode() == Opcodes.LSHL) {
                Integer shift = intConstant(previousCode(insn));
                if (shift != null) shifts.add(shift);
            }
        }
        if (!shifts.equals(new LinkedHashSet<Integer>(
                java.util.Arrays.asList(56, 48, 40, 32, 24, 16, 8)))) {
            return "result-shifts=" + shifts;
        }
        if (candidate.kind == Kind.SCALAR) {
            if (previousCode(candidate.targetWrite) == null
                    || previousCode(candidate.targetWrite).getOpcode() != Opcodes.LOR) {
                return "scalar-result-write-source";
            }
        } else {
            AbstractInsnNode previous = previousCode(candidate.targetWrite);
            if (!(previous instanceof VarInsnNode)
                    || previous.getOpcode() != Opcodes.ALOAD) {
                return "array-result-write-source";
            }
            int arrayLocal = ((VarInsnNode) previous).var;
            int longArrayStores = countOpcode(code, initRaw, targetRaw, Opcodes.LASTORE);
            if (longArrayStores != 1
                    || countVar(code, initRaw, targetRaw, Opcodes.ALOAD, arrayLocal) < 2) {
                return "array-result-local-binding=" + arrayLocal + "/" + longArrayStores;
            }
        }
        return null;
    }

    private static int countVar(Code code, int from, int to, int opcode, int local) {
        int result = 0;
        for (AbstractInsnNode insn : code.between(from, to)) {
            if (insn instanceof VarInsnNode && insn.getOpcode() == opcode
                    && ((VarInsnNode) insn).var == local) result++;
        }
        return result;
    }

    private static int countOpcode(Code code, int from, int to, int opcode) {
        int result = 0;
        for (AbstractInsnNode insn : code.between(from, to)) {
            if (insn.getOpcode() == opcode) result++;
        }
        return result;
    }

    private static String proveNormalClosure(Code code, Set<AbstractInsnNode> removed,
                                             AbstractInsnNode entry) {
        for (AbstractInsnNode source : code.executable) {
            for (LabelNode label : labels(source)) {
                AbstractInsnNode target = firstCode(label);
                boolean sourceRemoved = removed.contains(source);
                boolean targetRemoved = removed.contains(target);
                if (sourceRemoved != targetRemoved) {
                    return sourceRemoved
                            ? "removed-normal-exit=" + code.raw(source) + "->"
                            + code.raw(target)
                            : "external-normal-inbound=" + code.raw(source) + "->"
                            + code.raw(target);
                }
            }
        }
        AbstractInsnNode previous = null;
        for (AbstractInsnNode current : code.executable) {
            if (removed.contains(current) && (previous == null || !removed.contains(previous))
                    && current != entry && canFallThrough(previous)) {
                return "external-fallthrough=" + (previous == null ? -1 : code.raw(previous))
                        + "->" + code.raw(current);
            }
            previous = current;
        }
        return null;
    }

    private static void apply(ClassNode owner, Candidate candidate) {
        MethodNode clinit = method(owner, "<clinit>", "()V");
        InsnList replacement = new InsnList();
        if (candidate.kind == Kind.SCALAR) {
            replacement.add(new LdcInsnNode(candidate.values.get(0)));
        } else {
            pushInt(replacement, candidate.values.size());
            replacement.add(new IntInsnNode(Opcodes.NEWARRAY, Opcodes.T_LONG));
            for (int index = 0; index < candidate.values.size(); index++) {
                replacement.add(new InsnNode(Opcodes.DUP));
                pushInt(replacement, index);
                replacement.add(new LdcInsnNode(candidate.values.get(index)));
                replacement.add(new InsnNode(Opcodes.LASTORE));
            }
        }
        replacement.add(new FieldInsnNode(Opcodes.PUTSTATIC, owner.name,
                candidate.fieldName, candidate.fieldDesc));
        clinit.instructions.insertBefore(candidate.algorithm, replacement);
        removeInclusive(clinit.instructions, candidate.algorithm, candidate.targetWrite);
        if (candidate.tailStart != null) {
            removeUntil(clinit.instructions, candidate.tailStart, candidate.wrapper.end);
        }
    }

    private static void assertRewritten(ClassNode owner, Candidate original) {
        MethodNode clinit = method(owner, "<clinit>", "()V");
        if (clinit == null) throw new IllegalStateException("clinit removed");
        if (countNoPadding(clinit) != 0) {
            throw new IllegalStateException("NoPadding factory remains");
        }
        Code code = new Code(clinit);
        List<String> actual = executableSignatures(code.executable);
        if (!actual.equals(original.expectedExecutable)) {
            throw new IllegalStateException("preserved-executable-mismatch="
                    + firstDifference(original.expectedExecutable, actual));
        }
        if (!ownerWriteCounts(owner, clinit).equals(original.ownerWrites)) {
            throw new IllegalStateException("owner-field-writes-not-preserved");
        }
        if (countStateCalls(clinit) != original.stateCallCount) {
            throw new IllegalStateException("state-calls-not-preserved");
        }
        if (clinit.tryCatchBlocks == null || clinit.tryCatchBlocks.size() != 1
                || proveHandler(code, clinit.tryCatchBlocks.get(0)) != null) {
            throw new IllegalStateException("exception-wrapper-not-preserved");
        }
    }

    private static List<String> expectedExecutable(Code code, Candidate candidate) {
        List<String> result = new ArrayList<>();
        for (AbstractInsnNode insn : code.executable) {
            if (insn == candidate.algorithm) {
                if (candidate.kind == Kind.SCALAR) {
                    result.add("LDC:Long:" + candidate.values.get(0));
                } else {
                    result.add(intPushSignature(candidate.values.size()));
                    result.add("INT:" + Opcodes.NEWARRAY + ":" + Opcodes.T_LONG);
                    for (int index = 0; index < candidate.values.size(); index++) {
                        result.add("OP:" + Opcodes.DUP);
                        result.add(intPushSignature(index));
                        result.add("LDC:Long:" + candidate.values.get(index));
                        result.add("OP:" + Opcodes.LASTORE);
                    }
                }
                result.add(fieldSignature(Opcodes.PUTSTATIC, candidate.owner,
                        candidate.fieldName, candidate.fieldDesc));
            }
            if (!candidate.removed.contains(insn)) result.add(signature(insn));
        }
        return result;
    }

    private static Set<AbstractInsnNode> removedNodes(Code code,
                                                       AbstractInsnNode start,
                                                       AbstractInsnNode target,
                                                       AbstractInsnNode tailStart,
                                                       LabelNode tryEnd) {
        Set<AbstractInsnNode> result = Collections.newSetFromMap(
                new IdentityHashMap<AbstractInsnNode, Boolean>());
        AbstractInsnNode cursor = start;
        while (cursor != null) {
            result.add(cursor);
            if (cursor == target) break;
            cursor = cursor.getNext();
        }
        if (cursor != target) return Collections.emptySet();
        if (tailStart != null) {
            cursor = tailStart;
            while (cursor != null && cursor != tryEnd) {
                result.add(cursor);
                cursor = cursor.getNext();
            }
            if (cursor != tryEnd) return Collections.emptySet();
        }
        return result;
    }

    private static FieldInsnNode firstOwnerWrite(ClassNode owner, Code code,
                                                  int from, int to) {
        for (AbstractInsnNode insn : code.between(from + 1, to)) {
            if (!(insn instanceof FieldInsnNode) || insn.getOpcode() != Opcodes.PUTSTATIC) {
                continue;
            }
            FieldInsnNode field = (FieldInsnNode) insn;
            if (owner.name.equals(field.owner)) return field;
        }
        return null;
    }

    private static JumpInsnNode gotoTargeting(Code code, int from, int to,
                                               LabelNode target) {
        JumpInsnNode result = null;
        for (AbstractInsnNode insn : code.between(from, to)) {
            if (!(insn instanceof JumpInsnNode) || insn.getOpcode() != Opcodes.GOTO
                    || ((JumpInsnNode) insn).label != target) continue;
            if (result != null) return null;
            result = (JumpInsnNode) insn;
        }
        return result;
    }

    private static MethodInsnNode uniqueCall(Code code, int from, int to,
                                              String owner, String name) {
        MethodInsnNode result = null;
        for (AbstractInsnNode insn : code.between(from, to)) {
            if (!(insn instanceof MethodInsnNode)) continue;
            MethodInsnNode call = (MethodInsnNode) insn;
            if (!owner.equals(call.owner) || !name.equals(call.name)) continue;
            if (result != null) return null;
            result = call;
        }
        return result;
    }

    private static Set<Long> longConstants(Code code, int from, int to) {
        Set<Long> result = new LinkedHashSet<>();
        for (AbstractInsnNode insn : code.between(from, to)) {
            if (insn instanceof LdcInsnNode && ((LdcInsnNode) insn).cst instanceof Long) {
                long value = (Long) ((LdcInsnNode) insn).cst;
                if (value != 255L) result.add(value);
            }
        }
        return result;
    }

    private static String uniquePackedLiteral(Code code, int from, int to) {
        Set<String> result = new LinkedHashSet<>();
        for (AbstractInsnNode insn : code.between(from, to)) {
            if (!(insn instanceof LdcInsnNode)
                    || !(((LdcInsnNode) insn).cst instanceof String)) continue;
            String value = (String) ((LdcInsnNode) insn).cst;
            if (value.isEmpty() || (value.length() & 7) != 0 || !latin1(value)
                    || ALGORITHM.equals(value) || KEY_ALGORITHM.equals(value)
                    || LATIN1.equals(value)) continue;
            result.add(value);
        }
        return result.size() == 1 ? result.iterator().next() : null;
    }

    private static Integer uniqueLongArrayCapacity(Code code, int from, int to) {
        Integer result = null;
        for (AbstractInsnNode insn : code.between(from, to)) {
            if (!(insn instanceof IntInsnNode) || insn.getOpcode() != Opcodes.NEWARRAY
                    || ((IntInsnNode) insn).operand != Opcodes.T_LONG) continue;
            Integer value = intConstant(previousCode(insn));
            if (value == null || result != null) return null;
            result = value;
        }
        return result;
    }

    private static boolean allowedCall(MethodInsnNode call, Kind kind) {
        if ("javax/crypto/Cipher".equals(call.owner)) {
            return "getInstance".equals(call.name) || "init".equals(call.name)
                    || "doFinal".equals(call.name);
        }
        if ("javax/crypto/SecretKeyFactory".equals(call.owner)) {
            return "getInstance".equals(call.name) || "generateSecret".equals(call.name);
        }
        if (("javax/crypto/spec/DESKeySpec".equals(call.owner)
                || "javax/crypto/spec/IvParameterSpec".equals(call.owner))
                && "<init>".equals(call.name)) return true;
        return kind == Kind.LONG_ARRAY && "java/lang/String".equals(call.owner)
                && ("length".equals(call.name) || "substring".equals(call.name)
                || "getBytes".equals(call.name));
    }

    private static int countCall(Map<String, Integer> calls, String prefix) {
        int result = 0;
        for (Map.Entry<String, Integer> entry : calls.entrySet()) {
            if (entry.getKey().startsWith(prefix)) result += entry.getValue();
        }
        return result;
    }

    private static boolean isNoPaddingFactory(AbstractInsnNode insn) {
        if (!(insn instanceof MethodInsnNode)) return false;
        MethodInsnNode call = (MethodInsnNode) insn;
        if (call.getOpcode() != Opcodes.INVOKESTATIC
                || !"javax/crypto/Cipher".equals(call.owner)
                || !"getInstance".equals(call.name)
                || !"(Ljava/lang/String;)Ljavax/crypto/Cipher;".equals(call.desc)) {
            return false;
        }
        AbstractInsnNode previous = previousCode(call);
        return previous instanceof LdcInsnNode
                && ALGORITHM.equals(((LdcInsnNode) previous).cst);
    }

    private static boolean isStateTransform(AbstractInsnNode insn) {
        if (!(insn instanceof MethodInsnNode)) return false;
        MethodInsnNode call = (MethodInsnNode) insn;
        return call.getOpcode() == Opcodes.INVOKEINTERFACE
                && STATE_IFACE.equals(call.owner) && "a".equals(call.name)
                && "(J)J".equals(call.desc);
    }

    private static boolean hasStateCall(MethodNode method) {
        return countStateCalls(method) != 0;
    }

    private static int countStateCalls(MethodNode method) {
        int result = 0;
        for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
             insn = insn.getNext()) {
            if (insn instanceof MethodInsnNode) {
                MethodInsnNode call = (MethodInsnNode) insn;
                if (STATE.equals(call.owner) || STATE_IFACE.equals(call.owner)) result++;
            }
        }
        return result;
    }

    private static Map<String, Integer> ownerWriteCounts(ClassNode owner,
                                                          MethodNode method) {
        Map<String, Integer> result = new LinkedHashMap<>();
        for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
             insn = insn.getNext()) {
            if (!(insn instanceof FieldInsnNode) || insn.getOpcode() != Opcodes.PUTSTATIC) {
                continue;
            }
            FieldInsnNode field = (FieldInsnNode) insn;
            if (!owner.name.equals(field.owner)) continue;
            String key = field.name + field.desc;
            result.put(key, result.getOrDefault(key, 0) + 1);
        }
        return result;
    }

    private static List<LabelNode> labels(AbstractInsnNode insn) {
        List<LabelNode> result = new ArrayList<>();
        if (insn instanceof JumpInsnNode) {
            result.add(((JumpInsnNode) insn).label);
        } else if (insn instanceof TableSwitchInsnNode) {
            TableSwitchInsnNode table = (TableSwitchInsnNode) insn;
            result.add(table.dflt);
            result.addAll(table.labels);
        } else if (insn instanceof LookupSwitchInsnNode) {
            LookupSwitchInsnNode lookup = (LookupSwitchInsnNode) insn;
            result.add(lookup.dflt);
            result.addAll(lookup.labels);
        }
        return result;
    }

    private static boolean canFallThrough(AbstractInsnNode insn) {
        if (insn == null) return true;
        int opcode = insn.getOpcode();
        return opcode != Opcodes.GOTO && opcode != Opcodes.ATHROW
                && opcode != Opcodes.RETURN && opcode != Opcodes.IRETURN
                && opcode != Opcodes.LRETURN && opcode != Opcodes.FRETURN
                && opcode != Opcodes.DRETURN && opcode != Opcodes.ARETURN
                && !(insn instanceof TableSwitchInsnNode)
                && !(insn instanceof LookupSwitchInsnNode);
    }

    private static AbstractInsnNode uniqueSource(SourceValue value) {
        return value != null && value.insns != null && value.insns.size() == 1
                ? value.insns.iterator().next() : null;
    }

    private static AbstractInsnNode previousCode(AbstractInsnNode insn) {
        AbstractInsnNode previous = insn == null ? null : insn.getPrevious();
        while (previous != null && previous.getOpcode() < 0) previous = previous.getPrevious();
        return previous;
    }

    private static AbstractInsnNode nextCode(AbstractInsnNode insn) {
        AbstractInsnNode next = insn == null ? null : insn.getNext();
        while (next != null && next.getOpcode() < 0) next = next.getNext();
        return next;
    }

    private static AbstractInsnNode firstCode(AbstractInsnNode insn) {
        AbstractInsnNode current = insn;
        while (current != null && current.getOpcode() < 0) current = current.getNext();
        return current;
    }

    private static void removeInclusive(InsnList instructions, AbstractInsnNode start,
                                        AbstractInsnNode end) {
        AbstractInsnNode cursor = start;
        while (cursor != null) {
            AbstractInsnNode next = cursor.getNext();
            instructions.remove(cursor);
            if (cursor == end) return;
            cursor = next;
        }
        throw new IllegalStateException("inclusive boundary lost");
    }

    private static void removeUntil(InsnList instructions, AbstractInsnNode start,
                                    AbstractInsnNode exclusiveEnd) {
        AbstractInsnNode cursor = start;
        while (cursor != null && cursor != exclusiveEnd) {
            AbstractInsnNode next = cursor.getNext();
            instructions.remove(cursor);
            cursor = next;
        }
        if (cursor != exclusiveEnd) throw new IllegalStateException("exclusive boundary lost");
    }

    private static void pushInt(InsnList instructions, int value) {
        if (value >= -1 && value <= 5) {
            instructions.add(new InsnNode(Opcodes.ICONST_0 + value));
        } else if (value >= Byte.MIN_VALUE && value <= Byte.MAX_VALUE) {
            instructions.add(new IntInsnNode(Opcodes.BIPUSH, value));
        } else if (value >= Short.MIN_VALUE && value <= Short.MAX_VALUE) {
            instructions.add(new IntInsnNode(Opcodes.SIPUSH, value));
        } else {
            instructions.add(new LdcInsnNode(value));
        }
    }

    private static Integer intConstant(AbstractInsnNode insn) {
        if (insn == null) return null;
        int opcode = insn.getOpcode();
        if (opcode >= Opcodes.ICONST_M1 && opcode <= Opcodes.ICONST_5) {
            return opcode - Opcodes.ICONST_0;
        }
        if (insn instanceof IntInsnNode) return ((IntInsnNode) insn).operand;
        if (insn instanceof LdcInsnNode && ((LdcInsnNode) insn).cst instanceof Integer) {
            return (Integer) ((LdcInsnNode) insn).cst;
        }
        return null;
    }

    private static boolean latin1(String value) {
        for (int index = 0; index < value.length(); index++) {
            if (value.charAt(index) > 0xff) return false;
        }
        return true;
    }

    private static boolean isCall(AbstractInsnNode insn, int opcode, String owner,
                                  String name, String desc) {
        if (!(insn instanceof MethodInsnNode)) return false;
        MethodInsnNode call = (MethodInsnNode) insn;
        return call.getOpcode() == opcode && owner.equals(call.owner)
                && name.equals(call.name) && desc.equals(call.desc);
    }

    private static int countNoPadding(MethodNode method) {
        int result = 0;
        for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
             insn = insn.getNext()) if (isNoPaddingFactory(insn)) result++;
        return result;
    }

    private static List<String> executableSignatures(List<AbstractInsnNode> instructions) {
        List<String> result = new ArrayList<>();
        for (AbstractInsnNode insn : instructions) result.add(signature(insn));
        return result;
    }

    private static String signature(AbstractInsnNode insn) {
        if (insn instanceof LdcInsnNode) {
            Object value = ((LdcInsnNode) insn).cst;
            return "LDC:" + value.getClass().getSimpleName() + ":" + value;
        }
        if (insn instanceof IntInsnNode) {
            return "INT:" + insn.getOpcode() + ":" + ((IntInsnNode) insn).operand;
        }
        if (insn instanceof VarInsnNode) {
            return "VAR:" + insn.getOpcode() + ":" + ((VarInsnNode) insn).var;
        }
        if (insn instanceof IincInsnNode) {
            IincInsnNode value = (IincInsnNode) insn;
            return "IINC:" + value.var + ":" + value.incr;
        }
        if (insn instanceof TypeInsnNode) {
            return "TYPE:" + insn.getOpcode() + ":" + ((TypeInsnNode) insn).desc;
        }
        if (insn instanceof FieldInsnNode) {
            FieldInsnNode field = (FieldInsnNode) insn;
            return fieldSignature(insn.getOpcode(), field.owner, field.name, field.desc);
        }
        if (insn instanceof MethodInsnNode) {
            MethodInsnNode call = (MethodInsnNode) insn;
            return "CALL:" + insn.getOpcode() + ":" + call.owner + "." + call.name
                    + call.desc + ":" + call.itf;
        }
        if (insn instanceof InvokeDynamicInsnNode) {
            InvokeDynamicInsnNode indy = (InvokeDynamicInsnNode) insn;
            return "INDY:" + indy.name + indy.desc + ":" + indy.bsm;
        }
        if (insn instanceof JumpInsnNode) return "JUMP:" + insn.getOpcode();
        if (insn instanceof TableSwitchInsnNode) {
            TableSwitchInsnNode table = (TableSwitchInsnNode) insn;
            return "TABLE:" + table.min + ":" + table.max + ":" + table.labels.size();
        }
        if (insn instanceof LookupSwitchInsnNode) {
            return "LOOKUP:" + ((LookupSwitchInsnNode) insn).keys;
        }
        if (insn instanceof MultiANewArrayInsnNode) {
            MultiANewArrayInsnNode array = (MultiANewArrayInsnNode) insn;
            return "MULTI:" + array.desc + ":" + array.dims;
        }
        return "OP:" + insn.getOpcode();
    }

    private static String fieldSignature(int opcode, String owner, String name,
                                         String desc) {
        return "FIELD:" + opcode + ":" + owner + "." + name + desc;
    }

    private static String intPushSignature(int value) {
        if (value >= -1 && value <= 5) return "OP:" + (Opcodes.ICONST_0 + value);
        if (value >= Byte.MIN_VALUE && value <= Byte.MAX_VALUE) {
            return "INT:" + Opcodes.BIPUSH + ":" + value;
        }
        if (value >= Short.MIN_VALUE && value <= Short.MAX_VALUE) {
            return "INT:" + Opcodes.SIPUSH + ":" + value;
        }
        return "LDC:Integer:" + value;
    }

    private static String firstDifference(List<String> expected, List<String> actual) {
        int size = Math.min(expected.size(), actual.size());
        for (int index = 0; index < size; index++) {
            if (!expected.get(index).equals(actual.get(index))) {
                return index + ":" + expected.get(index) + "!=" + actual.get(index);
            }
        }
        return "size:" + expected.size() + "!=" + actual.size();
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
            if (entry.name.endsWith(".class")) {
                result.put(new ClassReader(entry.bytes).getClassName(), entry.bytes);
            }
        }
        return result;
    }

    private static void writeArchive(List<EntryBytes> entries,
                                     Map<String, byte[]> replacements, Path output,
                                     Summary summary, List<String> verifier)
            throws IOException {
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
                        String owner = new ClassReader(bytes).getClassName();
                        if (replacements.containsKey(owner)) {
                            bytes = replacements.get(owner);
                            applied.add(owner);
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
        Map<String, byte[]> classes = new LinkedHashMap<>();
        try (ZipInputStream zip = new ZipInputStream(Files.newInputStream(archive))) {
            ZipEntry entry;
            while ((entry = zip.getNextEntry()) != null) {
                byte[] bytes = readAll(zip);
                if (!entry.getName().endsWith(".class")) continue;
                summary.outputClasses++;
                try {
                    verifyClass(bytes);
                    classes.put(new ClassReader(bytes).getClassName(), bytes);
                } catch (Throwable failure) {
                    summary.outputVerificationErrors++;
                    verifier.add(tsv("archive", entry.getName(), "FAIL",
                            shortReason(failure)));
                }
            }
        }
        summary.outputDesCalls = countDesFactories(classes);
        summary.outputNoPaddingCalls = countNoPaddingFactories(classes);
        verifier.add(tsv("archive", "*",
                summary.outputVerificationErrors == 0 ? "PASS" : "FAIL",
                "classes=" + summary.outputClasses + ";errors="
                        + summary.outputVerificationErrors + ";des="
                        + summary.outputDesCalls + ";nopadding="
                        + summary.outputNoPaddingCalls));
    }

    private static int countDesFactories(Map<String, byte[]> classes) {
        int result = 0;
        for (byte[] bytes : classes.values()) {
            ClassNode owner = readClass(bytes);
            for (MethodNode method : owner.methods) {
                for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
                     insn = insn.getNext()) {
                    if (!(insn instanceof MethodInsnNode)) continue;
                    MethodInsnNode call = (MethodInsnNode) insn;
                    AbstractInsnNode previous = previousCode(call);
                    if (call.getOpcode() == Opcodes.INVOKESTATIC
                            && "javax/crypto/Cipher".equals(call.owner)
                            && "getInstance".equals(call.name)
                            && previous instanceof LdcInsnNode
                            && ((LdcInsnNode) previous).cst instanceof String
                            && ((String) ((LdcInsnNode) previous).cst).startsWith("DES/")) {
                        result++;
                    }
                }
            }
        }
        return result;
    }

    private static int countNoPaddingFactories(Map<String, byte[]> classes) {
        int result = 0;
        for (byte[] bytes : classes.values()) {
            ClassNode owner = readClass(bytes);
            for (MethodNode method : owner.methods) result += countNoPadding(method);
        }
        return result;
    }

    private static void writeReports(Path input, Path output, Path report,
                                     Summary summary, List<Candidate> candidates,
                                     List<String> verifier) throws Exception {
        candidates.sort(Comparator.comparing(candidate -> candidate.owner));
        List<String> rows = new ArrayList<>();
        rows.add("class\tkind\tstate_derived\tfield\tfield_desc\tkey_hex"
                + "\tclass_key_hex\tmask_hex\tkey_source\tkey_chain"
                + "\tciphertext_hex\tpacked_length\tvalues\ttry_start\ttry_end"
                + "\thandler\tremoved_nodes\tproven\taction\treason");
        for (Candidate candidate : candidates) rows.add(candidate.row());
        Files.write(report.resolve("candidates.tsv"), rows, StandardCharsets.UTF_8);
        Files.write(report.resolve("verifier.tsv"), verifier, StandardCharsets.UTF_8);

        List<String> audit = new ArrayList<>();
        audit.add("input=" + input.toAbsolutePath().normalize());
        audit.add("input_sha256=" + sha256(Files.readAllBytes(input)));
        audit.add("output=" + (output == null ? "" : output.toAbsolutePath().normalize()));
        audit.add("parsed_classes=" + summary.parsedClasses);
        audit.add("candidates=" + summary.candidates);
        audit.add("proven=" + summary.proven);
        audit.add("rejected=" + summary.rejected);
        audit.add("changed_classes=" + summary.changedClasses);
        audit.add("literal_classes=" + summary.literalClasses);
        audit.add("state_classes=" + summary.stateClasses);
        audit.add("scalar_classes=" + summary.scalarClasses);
        audit.add("array_classes=" + summary.arrayClasses);
        audit.add("table_entries=" + summary.tableEntries);
        audit.add("rollbacks=" + summary.rollbacks);
        audit.add("input_des_calls=" + summary.inputDesCalls);
        audit.add("output_des_calls=" + summary.outputDesCalls);
        audit.add("des_calls_removed="
                + (summary.inputDesCalls - summary.outputDesCalls));
        audit.add("input_nopadding_calls=" + summary.inputNoPaddingCalls);
        audit.add("output_nopadding_calls=" + summary.outputNoPaddingCalls);
        audit.add("output_classes=" + summary.outputClasses);
        audit.add("output_verification_errors=" + summary.outputVerificationErrors);
        audit.add("output_committed=" + summary.outputCommitted);
        audit.add("proof=single complete Exception range + canonical preserved "
                + "ExceptionInInitializerError handler + closed normal CFG + exact "
                + "crypto call/effect template + proven literal/state key");
        audit.add("input_classes_loaded=false");
        audit.add("input_classes_initialized=false");
        boolean pass = summary.rollbacks == 0 && summary.outputVerificationErrors == 0
                && (output == null || summary.outputCommitted);
        audit.add("gate=" + (pass ? "PASS" : "FAIL"));
        Files.write(report.resolve("audit.txt"), audit, StandardCharsets.UTF_8);
        Files.write(report.resolve("gate.txt"), Collections.singletonList(
                pass ? "PASS" : "FAIL"), StandardCharsets.UTF_8);
    }

    private static String sha256(byte[] bytes) throws Exception {
        MessageDigest digest = MessageDigest.getInstance("SHA-256");
        StringBuilder result = new StringBuilder();
        for (byte value : digest.digest(bytes)) {
            result.append(String.format(Locale.ROOT, "%02X", value & 0xff));
        }
        return result.toString();
    }

    private static byte[] readAll(ZipInputStream zip) throws IOException {
        ByteArrayOutputStream output = new ByteArrayOutputStream();
        byte[] buffer = new byte[8192];
        int count;
        while ((count = zip.read(buffer)) >= 0) {
            if (count != 0) output.write(buffer, 0, count);
        }
        return output.toByteArray();
    }

    private static String shortReason(Throwable failure) {
        String value = failure.getClass().getSimpleName() + ":"
                + String.valueOf(failure.getMessage());
        value = value.replace('\t', ' ').replace('\r', ' ').replace('\n', ' ');
        return value.substring(0, Math.min(240, value.length()));
    }

    private static String tsv(Object... values) {
        List<String> result = new ArrayList<>();
        for (Object value : values) {
            result.add(String.valueOf(value).replace('\t', ' ')
                    .replace('\r', ' ').replace('\n', ' '));
        }
        return String.join("\t", result);
    }

    private static String hex(long value) {
        return String.format(Locale.ROOT, "%016X", value);
    }

    static final class Summary {
        int parsedClasses;
        int candidates;
        int proven;
        int rejected;
        int changedClasses;
        int literalClasses;
        int stateClasses;
        int scalarClasses;
        int arrayClasses;
        int tableEntries;
        int rollbacks;
        int inputDesCalls;
        int outputDesCalls;
        int inputNoPaddingCalls;
        int outputNoPaddingCalls;
        int outputClasses;
        int outputVerificationErrors;
        boolean outputCommitted;
    }

    private enum Kind { SCALAR, LONG_ARRAY }

    private static final class Candidate {
        final String owner;
        Kind kind;
        boolean stateDerived;
        long classKey;
        long outerMask;
        long key;
        long ciphertext;
        String keySource = "";
        String keyChain = "";
        String fieldName = "";
        String fieldDesc = "";
        int packedLength;
        int instructions;
        int noPaddingCalls;
        int stateCallCount;
        int tryStartRaw = -1;
        int tryEndRaw = -1;
        int handlerRaw = -1;
        AbstractInsnNode algorithm;
        FieldInsnNode targetWrite;
        JumpInsnNode resultExit;
        AbstractInsnNode tailStart;
        TryCatchBlockNode wrapper;
        Set<AbstractInsnNode> removed = Collections.emptySet();
        Map<String, Integer> ownerWrites = Collections.emptyMap();
        List<Long> values = new ArrayList<>();
        List<String> expectedExecutable = Collections.emptyList();
        boolean proven;
        String action = "REJECT";
        String reason = "";

        Candidate(String owner) {
            this.owner = owner;
        }

        Candidate reject(String failure) {
            reason = failure;
            return this;
        }

        String row() {
            return tsv(owner, kind, stateDerived, fieldName, fieldDesc, hex(key),
                    stateDerived ? hex(classKey) : "",
                    stateDerived ? hex(outerMask) : "", keySource, keyChain,
                    kind == Kind.SCALAR ? hex(ciphertext) : "", packedLength,
                    values.size(), tryStartRaw, tryEndRaw, handlerRaw,
                    removed.size(), proven, action, reason);
        }
    }

    private static final class Code {
        final MethodNode method;
        final List<AbstractInsnNode> all = new ArrayList<>();
        final List<AbstractInsnNode> executable = new ArrayList<>();
        final IdentityHashMap<AbstractInsnNode, Integer> raw = new IdentityHashMap<>();

        Code(MethodNode method) {
            this.method = method;
            int index = 0;
            for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
                 insn = insn.getNext(), index++) {
                all.add(insn);
                raw.put(insn, index);
                if (insn.getOpcode() >= 0) executable.add(insn);
            }
        }

        int raw(AbstractInsnNode insn) {
            Integer value = raw.get(insn);
            if (value == null) throw new IllegalArgumentException("instruction not in method");
            return value;
        }

        List<AbstractInsnNode> between(int from, int to) {
            if (from < 0) from = 0;
            if (to > all.size()) to = all.size();
            return all.subList(from, to);
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
}
