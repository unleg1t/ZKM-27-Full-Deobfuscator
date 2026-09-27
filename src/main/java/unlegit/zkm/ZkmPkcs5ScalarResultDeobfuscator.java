package unlegit.zkm;

import org.objectweb.asm.ClassReader;
import org.objectweb.asm.ClassWriter;
import org.objectweb.asm.Opcodes;
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
import org.objectweb.asm.tree.LookupSwitchInsnNode;
import org.objectweb.asm.tree.MethodInsnNode;
import org.objectweb.asm.tree.MethodNode;
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
 * Restores a scalar PKCS5 string result while preserving the result sink and
 * every business instruction after it.
 *
 * <p>The accepted region begins at the unique PKCS5 algorithm literal and
 * reaches exactly one {@code ASTORE} or static-final String {@code PUTSTATIC}
 * whose stack value is sourced by the unique {@code String.intern()} call.
 * Its normal-flow subgraph must have one entry and that result sink as its
 * only exit. The complete JCE call set, byte-key construction, exact ZKM byte
 * decoder, ciphertext, literal or statically proven state key, and empty/start
 * stack are all checked before mutation. The rewrite inserts a plaintext LDC
 * and jumps to the original sink, then removes only analyzer-unreachable code.
 * Input classes are parsed as ASM data and are never loaded or initialized.</p>
 */
public final class ZkmPkcs5ScalarResultDeobfuscator {
    private static final String PKCS5 = "DES/CBC/PKCS5Padding";
    private static final String KEY_ALGORITHM = "DES";
    private static final String LATIN1 = "ISO-8859-1";
    private static final String BYTE_DECODER_DESC = "([B)Ljava/lang/String;";
    private static final String STATE =
            ObfRuntimeNames.STATE;
    private static final String STATE_IFACE =
            ObfRuntimeNames.STATE_INTERFACE;

    private ZkmPkcs5ScalarResultDeobfuscator() {
    }

    public static void main(String[] args) throws Exception {
        if (args.length < 2 || args.length > 4) {
            System.err.println("usage: ZkmPkcs5ScalarResultDeobfuscator "
                    + "<input.jar> <report-dir> [output.jar] [authority.jar]");
            System.exit(2);
        }
        Summary summary = rewrite(Paths.get(args[0]), Paths.get(args[1]),
                args.length >= 3 ? Paths.get(args[2]) : null,
                args.length == 4 ? Paths.get(args[3]) : null);
        System.out.println("classes=" + summary.parsedClasses
                + " candidates=" + summary.candidates
                + " proven=" + summary.proven
                + " changed=" + summary.changedClasses
                + " pkcs5_removed=" + summary.pkcs5Removed
                + " rollbacks=" + summary.rollbacks
                + " residual_pkcs5=" + summary.outputPkcs5
                + " output_committed=" + summary.outputCommitted);
    }

    static Summary rewrite(Path input, Path reportDirectory, Path output)
            throws Exception {
        return rewrite(input, reportDirectory, output, null);
    }

    static Summary rewrite(Path input, Path reportDirectory, Path output,
                           Path authority) throws Exception {
        if (output != null && input.toAbsolutePath().normalize()
                .equals(output.toAbsolutePath().normalize())) {
            throw new IllegalArgumentException("output must not replace input");
        }
        Files.createDirectories(reportDirectory);
        List<EntryBytes> entries = readEntries(input);
        Map<String, byte[]> originals = classBytes(entries);
        Map<String, ClassNode> classes = classNodes(originals);
        Map<String, ZkmDirectStringArrayDeobfuscator.StateKeyProof> classKeys =
                ZkmPkcs5StateArrayDeobfuscator.resolveClassKeyProofs(classes);
        Map<String, Set<Long>> classKeyCandidates = new LinkedHashMap<>();
        mergeClassKeyCandidates(classKeyCandidates,
                ZkmClassKeySelector.candidateClassKeys(classes));
        if (authority != null) {
            Map<String, ClassNode> authorityClasses = classNodes(
                    classBytes(readEntries(authority)));
            mergeClassKeyCandidates(classKeyCandidates,
                    ZkmClassKeySelector.candidateClassKeys(authorityClasses));
        }
        Summary summary = new Summary();
        summary.authority = authority == null ? ""
                : authority.toAbsolutePath().normalize().toString();
        summary.authoritySha256 = authority == null ? "" : sha256(authority);
        summary.parsedClasses = classes.size();
        summary.inputPkcs5 = countPkcs5(classes);
        summary.outputRequested = output != null;
        List<Candidate> candidates = new ArrayList<>();
        Map<String, byte[]> replacements = new LinkedHashMap<>();
        List<String> verifier = new ArrayList<>();
        verifier.add("scope\tclass\tstatus\tdetail");
        ZkmClassRewriteTransaction.Emitter emitter =
                ZkmDirectStringArrayDeobfuscator.archiveEmitter(classes);

        List<String> names = new ArrayList<>(classes.keySet());
        Collections.sort(names);
        for (String name : names) {
            Candidate candidate = inspect(classes.get(name), classKeys.get(name),
                    classKeyCandidates.get(name));
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
            final ZkmDirectStringArrayDeobfuscator.StateKeyProof keyProof =
                    classKeys.get(name);
            final Set<Long> keyCandidates = classKeyCandidates.get(name);
            ZkmClassRewriteTransaction.Result transaction =
                    ZkmClassRewriteTransaction.attempt(originals.get(name),
                            mutable -> {
                                Candidate fresh = inspect(mutable, keyProof,
                                        keyCandidates);
                                if (fresh == null || !fresh.proven
                                        || fresh.key != candidate.key
                                        || !fresh.plaintext.equals(candidate.plaintext)
                                        || fresh.startIndex != candidate.startIndex
                                        || fresh.sinkIndex != candidate.sinkIndex) {
                                    throw new IllegalStateException(
                                            "proof changed before mutation");
                                }
                                apply(mutable, fresh);
                            }, emitted -> assertRewritten(emitted, candidate),
                            emitter);
            if (transaction.isCommitted()) {
                replacements.put(name, transaction.bytes());
                candidate.action = "REWRITE";
                summary.changedClasses++;
                verifier.add(tsv("class", name, "PASS", "sink="
                        + candidate.sinkKind + ";plaintext="
                        + printable(candidate.plaintext)));
            } else {
                candidate.action = "ROLLBACK";
                candidate.reason = append(candidate.reason,
                        transaction.stage() + ":" + transaction.reason());
                summary.rollbacks++;
                verifier.add(tsv("class", name, "ROLLBACK",
                        transaction.stage() + ":" + transaction.reason()));
            }
        }

        if (output != null) {
            writeArchive(entries, replacements, output, summary, verifier);
        } else {
            summary.outputPkcs5 = summary.inputPkcs5;
        }
        summary.pkcs5Removed = summary.inputPkcs5 - summary.outputPkcs5;
        writeReports(input, output, reportDirectory, summary, candidates,
                verifier, classKeys.size());
        return summary;
    }

    private static Candidate inspect(
            ClassNode owner,
            ZkmDirectStringArrayDeobfuscator.StateKeyProof classProof,
            Set<Long> classKeyCandidates) {
        MethodNode clinit = method(owner, "<clinit>", "()V");
        if (clinit == null) return null;
        Code code = new Code(clinit);
        List<Integer> factories = new ArrayList<>();
        for (int index = 0; index < code.nodes.size(); index++) {
            if (isPkcs5Factory(code.nodes.get(index))) factories.add(index);
        }
        if (factories.isEmpty()) return null;
        Candidate candidate = new Candidate(owner.name);
        candidate.instructions = code.nodes.size();
        candidate.pkcs5Calls = factories.size();
        if (factories.size() != 1) {
            return candidate.reject("pkcs5-factories=" + factories.size());
        }
        int factory = factories.get(0);
        int start = factory - 1;
        if (start < 0 || !(code.nodes.get(start) instanceof LdcInsnNode)
                || !PKCS5.equals(((LdcInsnNode) code.nodes.get(start)).cst)) {
            return candidate.reject("algorithm-entry");
        }

        List<MethodInsnNode> interns = new ArrayList<>();
        MethodInsnNode decoder = null;
        for (int index = factory + 1; index < code.nodes.size(); index++) {
            AbstractInsnNode insn = code.nodes.get(index);
            if (isCall(insn, Opcodes.INVOKEVIRTUAL, "java/lang/String",
                    "intern", "()Ljava/lang/String;")) {
                interns.add((MethodInsnNode) insn);
            }
            if (insn instanceof MethodInsnNode) {
                MethodInsnNode call = (MethodInsnNode) insn;
                if (call.getOpcode() == Opcodes.INVOKESTATIC
                        && owner.name.equals(call.owner)
                        && BYTE_DECODER_DESC.equals(call.desc)) {
                    if (decoder != null && (!decoder.name.equals(call.name))) {
                        return candidate.reject("multiple-byte-decoders");
                    }
                    decoder = call;
                }
            }
        }
        if (interns.size() != 1) {
            return candidate.reject("intern-calls=" + interns.size());
        }
        if (decoder == null || !ZkmDirectStringArrayDeobfuscator
                .isExactByteDecoder(owner, decoder.name)) {
            return candidate.reject("byte-decoder-not-proven");
        }

        int sink = findResultSink(owner, clinit, code, interns.get(0), candidate);
        if (sink < 0) return candidate.reject("scalar-result-sink");
        Set<Integer> region;
        try {
            region = closedRegion(code, start, sink);
        } catch (Throwable failure) {
            return candidate.reject("cfg=" + shortReason(failure));
        }
        String inbound = validateInbound(code, region, start);
        if (inbound != null) return candidate.reject(inbound);
        String shape = validateCryptoShape(owner, code, region, decoder);
        if (shape != null) return candidate.reject(shape);

        int keySpec = uniqueCallIndex(code, region,
                "javax/crypto/spec/DESKeySpec", "<init>", "([B)V");
        if (keySpec < 0) return candidate.reject("des-key-spec");
        KeyDecision key = deriveKey(owner, clinit, code, start, keySpec,
                classProof, region);
        if (!key.proven) return candidate.reject(key.reason);

        Set<String> ciphertexts = new LinkedHashSet<>();
        for (int index : region) {
            AbstractInsnNode insn = code.nodes.get(index);
            if (!(insn instanceof LdcInsnNode)
                    || !(((LdcInsnNode) insn).cst instanceof String)) continue;
            String value = (String) ((LdcInsnNode) insn).cst;
            if (PKCS5.equals(value) || KEY_ALGORITHM.equals(value)
                    || LATIN1.equals(value)) continue;
            try {
                ZkmDesConstantEvaluator.latin1Bytes(value);
                if (!value.isEmpty() && (value.length() & 7) == 0) {
                    ciphertexts.add(value);
                }
            } catch (IllegalArgumentException ignored) {
                // Non-Latin business strings are rejected by the region call/
                // side-effect proof if they are executable before the sink.
            }
        }
        if (ciphertexts.size() != 1) {
            return candidate.reject("ciphertexts=" + ciphertexts.size());
        }
        String ciphertext = ciphertexts.iterator().next();
        List<KeyDecision> attempts = new ArrayList<>();
        if (key.source.startsWith("STATE_KEY:")) {
            Set<Long> models = new LinkedHashSet<>();
            models.add(key.classKey);
            if (classKeyCandidates != null) models.addAll(classKeyCandidates);
            for (long classKey : models) {
                attempts.add(KeyDecision.state(classKey, key.mask,
                        classKey ^ key.mask, "pkcs5-model-candidate"));
            }
        } else {
            attempts.add(key);
        }
        List<KeyDecision> passingKeys = new ArrayList<>();
        List<String> passingPlaintexts = new ArrayList<>();
        String lastFailure = "";
        for (KeyDecision attempt : attempts) {
            try {
                String value = ZkmDesConstantEvaluator.decryptZkmString(
                        ZkmDesConstantEvaluator.KeyMaterial.proven(attempt.key,
                                attempt.source,
                                owner.name + ".<clinit> scalar-result"),
                        ciphertext);
                if (value.indexOf('\u0000') >= 0) {
                    lastFailure = "plaintext-contains-nul";
                    continue;
                }
                passingKeys.add(attempt);
                passingPlaintexts.add(value);
            } catch (Throwable failure) {
                lastFailure = shortReason(failure);
            }
        }
        if (passingKeys.size() != 1) {
            return candidate.reject("pkcs5-key-oracle=" + passingKeys.size()
                    + "/" + attempts.size() + ";class-key-candidates="
                    + classKeyHex(attempts) + ";last=" + lastFailure);
        }
        key = passingKeys.get(0);
        String plaintext = passingPlaintexts.get(0);

        try {
            Frame<BasicValue>[] frames = new Analyzer<BasicValue>(
                    new BasicVerifier()).analyze(owner.name, clinit);
            Frame<BasicValue> startFrame = frames[clinit.instructions.indexOf(
                    code.nodes.get(start))];
            Frame<BasicValue> sinkFrame = frames[clinit.instructions.indexOf(
                    code.nodes.get(sink))];
            if (startFrame == null || startFrame.getStackSize() != 0) {
                return candidate.reject("start-stack");
            }
            if (sinkFrame == null || sinkFrame.getStackSize() < 1
                    || !BasicValue.REFERENCE_VALUE.equals(
                    sinkFrame.getStack(sinkFrame.getStackSize() - 1))) {
                return candidate.reject("sink-stack");
            }
        } catch (Throwable failure) {
            return candidate.reject("basic-verifier=" + shortReason(failure));
        }

        candidate.startIndex = start;
        candidate.sinkIndex = sink;
        candidate.regionSize = region.size();
        candidate.stateDerived = key.source.startsWith("STATE_KEY:");
        candidate.key = key.key;
        candidate.keyKind = key.source;
        candidate.classKey = key.classKey;
        candidate.mask = key.mask;
        candidate.ciphertextLength = ciphertext.length();
        candidate.plaintext = plaintext;
        candidate.decoderName = decoder.name;
        candidate.proven = true;
        candidate.reason = "closed-scalar-result-island;original-sink-and-business-tail-preserved";
        return candidate;
    }

    private static int findResultSink(ClassNode owner, MethodNode method,
                                      Code code, MethodInsnNode intern,
                                      Candidate candidate) {
        Frame<SourceValue>[] frames;
        try {
            frames = new Analyzer<SourceValue>(new SourceInterpreter())
                    .analyze(owner.name, method);
        } catch (Throwable failure) {
            return -1;
        }
        int found = -1;
        for (int index = 0; index < code.nodes.size(); index++) {
            AbstractInsnNode insn = code.nodes.get(index);
            boolean local = insn instanceof VarInsnNode
                    && insn.getOpcode() == Opcodes.ASTORE;
            boolean field = insn instanceof FieldInsnNode
                    && insn.getOpcode() == Opcodes.PUTSTATIC
                    && owner.name.equals(((FieldInsnNode) insn).owner)
                    && "Ljava/lang/String;".equals(
                    ((FieldInsnNode) insn).desc);
            if (!local && !field) continue;
            int raw = method.instructions.indexOf(insn);
            Frame<SourceValue> frame = raw < 0 ? null : frames[raw];
            if (frame == null || frame.getStackSize() < 1) continue;
            SourceValue value = frame.getStack(frame.getStackSize() - 1);
            if (value == null || value.insns == null
                    || !value.insns.contains(intern)) continue;
            if (found >= 0) return -1;
            found = index;
            if (local) {
                int slot = ((VarInsnNode) insn).var;
                boolean consumed = false;
                for (int next = index + 1; next < code.nodes.size(); next++) {
                    AbstractInsnNode use = code.nodes.get(next);
                    if (use instanceof VarInsnNode
                            && ((VarInsnNode) use).var == slot) {
                        if (use.getOpcode() == Opcodes.ALOAD) consumed = true;
                        if (use.getOpcode() == Opcodes.ASTORE) break;
                    }
                }
                if (!consumed) return -1;
                candidate.sinkKind = "ASTORE:" + slot;
            } else {
                FieldInsnNode target = (FieldInsnNode) insn;
                FieldNode declaration = field(owner, target.name, target.desc);
                if (declaration == null
                        || (declaration.access & Opcodes.ACC_STATIC) == 0) {
                    return -1;
                }
                int writes = 0;
                for (AbstractInsnNode write = method.instructions.getFirst();
                     write != null; write = write.getNext()) {
                    if (!(write instanceof FieldInsnNode)
                            || write.getOpcode() != Opcodes.PUTSTATIC) continue;
                    FieldInsnNode writeField = (FieldInsnNode) write;
                    if (owner.name.equals(writeField.owner)
                            && target.name.equals(writeField.name)
                            && target.desc.equals(writeField.desc)) writes++;
                }
                if (writes != 1) return -1;
                candidate.sinkKind = "PUTSTATIC:" + target.name;
            }
        }
        if (found >= 0) return found;
        return findResultSinkByTokenFlow(owner, method, code, intern, candidate);
    }

    /**
     * Follows the plaintext reference through the small stack-shuffle tail
     * emitted by ZKM.  SourceInterpreter cannot retain a unique producer when
     * the normal path jumps backwards into an exception-handler-shaped
     * ASTORE/PUTSTATIC block.  This fallback deliberately understands only
     * SWAP/POP/GOTO (plus reference CHECKCAST); any computation, branch, or
     * duplicated token is rejected.
     */
    private static int findResultSinkByTokenFlow(
            ClassNode owner, MethodNode method, Code code,
            MethodInsnNode intern, Candidate candidate) {
        int internIndex = code.index(intern);
        if (internIndex < 0) return -1;
        ArrayDeque<TokenState> queue = new ArrayDeque<>();
        for (int successor : code.successors.get(internIndex)) {
            queue.add(new TokenState(successor, 0));
        }
        Set<Long> visited = new HashSet<>();
        int sink = -1;
        while (!queue.isEmpty()) {
            TokenState state = queue.removeFirst();
            if (state.index < 0 || state.index >= code.nodes.size()
                    || state.depth < 0 || state.depth > 1) {
                return -1;
            }
            long identity = ((long) state.index << 32)
                    ^ (state.depth & 0xffffffffL);
            if (!visited.add(identity)) continue;
            AbstractInsnNode insn = code.nodes.get(state.index);
            int opcode = insn.getOpcode();

            boolean localSink = opcode == Opcodes.ASTORE
                    && insn instanceof VarInsnNode && state.depth == 0;
            boolean fieldSink = opcode == Opcodes.PUTSTATIC
                    && insn instanceof FieldInsnNode && state.depth == 0
                    && owner.name.equals(((FieldInsnNode) insn).owner)
                    && "Ljava/lang/String;".equals(
                    ((FieldInsnNode) insn).desc);
            if (localSink || fieldSink) {
                if (sink >= 0 && sink != state.index) return -1;
                sink = state.index;
                continue;
            }

            int nextDepth = state.depth;
            if (opcode == Opcodes.SWAP) {
                nextDepth = 1 - state.depth;
            } else if (opcode == Opcodes.POP) {
                if (state.depth == 0) return -1;
                nextDepth--;
            } else if (opcode == Opcodes.NOP || opcode == Opcodes.GOTO
                    || opcode == Opcodes.CHECKCAST) {
                // No change to the tracked reference.
            } else {
                return -1;
            }
            List<Integer> successors = code.successors.get(state.index);
            if (successors.isEmpty()) return -1;
            for (int successor : successors) {
                queue.add(new TokenState(successor, nextDepth));
            }
        }
        if (sink < 0) return -1;
        AbstractInsnNode target = code.nodes.get(sink);
        if (target instanceof VarInsnNode) {
            candidate.sinkKind = "ASTORE:" + ((VarInsnNode) target).var;
            return sink;
        }
        FieldInsnNode fieldTarget = (FieldInsnNode) target;
        FieldNode declaration = field(owner, fieldTarget.name, fieldTarget.desc);
        if (declaration == null
                || (declaration.access & Opcodes.ACC_STATIC) == 0) {
            return -1;
        }
        int writes = 0;
        for (AbstractInsnNode write = method.instructions.getFirst();
             write != null; write = write.getNext()) {
            if (!(write instanceof FieldInsnNode)
                    || write.getOpcode() != Opcodes.PUTSTATIC) continue;
            FieldInsnNode writeField = (FieldInsnNode) write;
            if (owner.name.equals(writeField.owner)
                    && fieldTarget.name.equals(writeField.name)
                    && fieldTarget.desc.equals(writeField.desc)) writes++;
        }
        if (writes != 1) return -1;
        candidate.sinkKind = "PUTSTATIC:" + fieldTarget.name;
        return sink;
    }

    private static Set<Integer> closedRegion(Code code, int start, int sink) {
        Set<Integer> result = new LinkedHashSet<>();
        ArrayDeque<Integer> queue = new ArrayDeque<>();
        queue.add(start);
        while (!queue.isEmpty()) {
            int current = queue.removeFirst();
            if (current == sink || !result.add(current)) continue;
            List<Integer> successors = code.successors.get(current);
            if (successors.isEmpty()) {
                throw new IllegalArgumentException("exit-before-sink=" + current);
            }
            for (int target : successors) {
                if (target == sink) continue;
                if (target < 0 || target >= code.nodes.size()) {
                    throw new IllegalArgumentException("invalid-target=" + target);
                }
                queue.add(target);
            }
        }
        if (result.isEmpty()) throw new IllegalArgumentException("empty-region");
        boolean reachesSink = false;
        for (int index : result) {
            if (code.successors.get(index).contains(sink)) reachesSink = true;
        }
        if (!reachesSink) throw new IllegalArgumentException("sink-unreachable");
        return result;
    }

    private static String validateInbound(Code code, Set<Integer> region,
                                          int start) {
        for (int source = 0; source < code.nodes.size(); source++) {
            for (int target : code.successors.get(source)) {
                if (region.contains(target) && !region.contains(source)
                        && target != start) {
                    return "external-inbound=" + source + "->" + target;
                }
            }
        }
        return null;
    }

    private static String validateCryptoShape(
            ClassNode owner, Code code, Set<Integer> region,
            MethodInsnNode decoder) {
        Map<String, Integer> calls = new LinkedHashMap<>();
        int byteArrays = 0;
        int byteStores = 0;
        int shiftsRight = 0;
        int shiftsLeft = 0;
        int multiplies = 0;
        for (int index : region) {
            AbstractInsnNode insn = code.nodes.get(index);
            int opcode = insn.getOpcode();
            if (insn instanceof InvokeDynamicInsnNode
                    || insn instanceof TableSwitchInsnNode
                    || insn instanceof LookupSwitchInsnNode) {
                return "dynamic-or-switch-in-region";
            }
            if (insn instanceof FieldInsnNode) {
                return "field-side-effect-in-region=" + index;
            }
            if (insn instanceof MethodInsnNode) {
                MethodInsnNode call = (MethodInsnNode) insn;
                String id = call.getOpcode() + ":" + call.owner + "."
                        + call.name + call.desc;
                calls.put(id, calls.containsKey(id) ? calls.get(id) + 1 : 1);
            }
            if (insn instanceof TypeInsnNode) {
                TypeInsnNode type = (TypeInsnNode) insn;
                if (opcode != Opcodes.NEW
                        || !("javax/crypto/spec/DESKeySpec".equals(type.desc)
                        || "javax/crypto/spec/IvParameterSpec".equals(type.desc))) {
                    return "type-side-effect=" + type.desc;
                }
            }
            if (insn instanceof IntInsnNode && opcode == Opcodes.NEWARRAY) {
                if (((IntInsnNode) insn).operand != Opcodes.T_BYTE) {
                    return "non-byte-array";
                }
                byteArrays++;
            }
            if (opcode == Opcodes.BASTORE) byteStores++;
            if (opcode == Opcodes.LUSHR) shiftsRight++;
            if (opcode == Opcodes.LSHL) shiftsLeft++;
            if (opcode == Opcodes.IMUL) multiplies++;
            if (opcode == Opcodes.RETURN || opcode == Opcodes.ATHROW
                    || opcode == Opcodes.MONITORENTER
                    || opcode == Opcodes.MONITOREXIT) {
                return "terminal-side-effect=" + opcode;
            }
        }
        Map<String, Integer> expected = new LinkedHashMap<>();
        put(expected, call(Opcodes.INVOKESTATIC, "javax/crypto/Cipher",
                "getInstance", "(Ljava/lang/String;)Ljavax/crypto/Cipher;"));
        put(expected, call(Opcodes.INVOKESTATIC,
                "javax/crypto/SecretKeyFactory", "getInstance",
                "(Ljava/lang/String;)Ljavax/crypto/SecretKeyFactory;"));
        put(expected, call(Opcodes.INVOKESPECIAL,
                "javax/crypto/spec/DESKeySpec", "<init>", "([B)V"));
        put(expected, call(Opcodes.INVOKEVIRTUAL,
                "javax/crypto/SecretKeyFactory", "generateSecret",
                "(Ljava/security/spec/KeySpec;)Ljavax/crypto/SecretKey;"));
        put(expected, call(Opcodes.INVOKESPECIAL,
                "javax/crypto/spec/IvParameterSpec", "<init>", "([B)V"));
        put(expected, call(Opcodes.INVOKEVIRTUAL, "javax/crypto/Cipher",
                "init", "(ILjava/security/Key;"
                        + "Ljava/security/spec/AlgorithmParameterSpec;)V"));
        put(expected, call(Opcodes.INVOKEVIRTUAL, "java/lang/String",
                "getBytes", "(Ljava/lang/String;)[B"));
        put(expected, call(Opcodes.INVOKEVIRTUAL, "javax/crypto/Cipher",
                "doFinal", "([B)[B"));
        put(expected, call(Opcodes.INVOKESTATIC, owner.name, decoder.name,
                BYTE_DECODER_DESC));
        put(expected, call(Opcodes.INVOKEVIRTUAL, "java/lang/String",
                "intern", "()Ljava/lang/String;"));
        if (!calls.equals(expected)) {
            return "jce-call-set=" + calls.size() + "/" + expected.size();
        }
        if (byteArrays != 2 || byteStores < 2 || shiftsRight < 2
                || shiftsLeft < 1 || multiplies < 1) {
            return "key-byte-shape=" + byteArrays + "," + byteStores
                    + "," + shiftsRight + "," + shiftsLeft + ","
                    + multiplies;
        }
        return null;
    }

    private static KeyDecision deriveKey(
            ClassNode owner, MethodNode clinit, Code code, int start,
            int keySpec, ZkmDirectStringArrayDeobfuscator.StateKeyProof proof,
            Set<Integer> region) {
        Set<Integer> longLocals = new LinkedHashSet<>();
        for (int index : region) {
            if (index >= keySpec) continue;
            AbstractInsnNode insn = code.nodes.get(index);
            if (insn instanceof VarInsnNode
                    && insn.getOpcode() == Opcodes.LLOAD) {
                longLocals.add(((VarInsnNode) insn).var);
            }
        }
        if (longLocals.isEmpty()) {
            Set<Long> constants = new LinkedHashSet<>();
            int loads = 0;
            for (int index : region) {
                if (index >= keySpec) continue;
                AbstractInsnNode insn = code.nodes.get(index);
                if (insn instanceof LdcInsnNode
                        && ((LdcInsnNode) insn).cst instanceof Long) {
                    constants.add((Long) ((LdcInsnNode) insn).cst);
                    loads++;
                }
            }
            if (constants.size() != 1 || loads < 1) {
                return KeyDecision.reject("literal-key-shape="
                        + constants.size() + "/" + loads);
            }
            return KeyDecision.literal(constants.iterator().next());
        }
        if (longLocals.size() != 1 || proof == null) {
            return KeyDecision.reject("state-key-locals=" + longLocals
                    + ";proof=" + (proof != null));
        }
        int local = longLocals.iterator().next();
        int definition = -1;
        int definitions = 0;
        for (int index = 0; index < start; index++) {
            AbstractInsnNode insn = code.nodes.get(index);
            if (insn instanceof VarInsnNode
                    && insn.getOpcode() == Opcodes.LSTORE
                    && ((VarInsnNode) insn).var == local) {
                definition = index;
                definitions++;
            }
        }
        if (definitions != 1 || definition < 1
                || code.nodes.get(definition - 1).getOpcode() != Opcodes.LXOR) {
            return KeyDecision.reject("state-key-definition=" + definitions);
        }
        AbstractInsnNode xor = code.nodes.get(definition - 1);
        AbstractInsnNode left;
        AbstractInsnNode right;
        try {
            Frame<SourceValue>[] frames = new Analyzer<SourceValue>(
                    new SourceInterpreter()).analyze(owner.name, clinit);
            Frame<SourceValue> frame = frames[clinit.instructions.indexOf(xor)];
            if (frame == null || frame.getStackSize() < 2) {
                return KeyDecision.reject("state-key-xor-frame");
            }
            left = unique(frame.getStack(frame.getStackSize() - 2));
            right = unique(frame.getStack(frame.getStackSize() - 1));
        } catch (Throwable failure) {
            return KeyDecision.reject("state-key-source="
                    + shortReason(failure));
        }
        LdcInsnNode maskNode = longLdc(left) ? (LdcInsnNode) left
                : longLdc(right) ? (LdcInsnNode) right : null;
        AbstractInsnNode keyNode = maskNode == left ? right : left;
        if (maskNode == null) {
            return KeyDecision.reject("state-key-mask");
        }
        MethodInsnNode transform;
        if (keyNode instanceof MethodInsnNode
                && isStateTransform((MethodInsnNode) keyNode)) {
            transform = (MethodInsnNode) keyNode;
        } else if (keyNode instanceof FieldInsnNode
                && keyNode.getOpcode() == Opcodes.GETSTATIC) {
            FieldInsnNode read = (FieldInsnNode) keyNode;
            if (!owner.name.equals(read.owner) || !"J".equals(read.desc)) {
                return KeyDecision.reject("state-key-field");
            }
            FieldNode declaration = field(owner, read.name, read.desc);
            if (declaration == null
                    || (declaration.access
                    & (Opcodes.ACC_STATIC | Opcodes.ACC_FINAL))
                    != (Opcodes.ACC_STATIC | Opcodes.ACC_FINAL)) {
                return KeyDecision.reject("state-key-field-declaration");
            }
            transform = null;
            for (int index = 1; index < definition; index++) {
                AbstractInsnNode insn = code.nodes.get(index);
                if (!(insn instanceof FieldInsnNode)
                        || insn.getOpcode() != Opcodes.PUTSTATIC) continue;
                FieldInsnNode write = (FieldInsnNode) insn;
                if (!read.owner.equals(write.owner)
                        || !read.name.equals(write.name)
                        || !read.desc.equals(write.desc)) continue;
                AbstractInsnNode producer = code.nodes.get(index - 1);
                if (!(producer instanceof MethodInsnNode)
                        || !isStateTransform((MethodInsnNode) producer)
                        || transform != null) {
                    return KeyDecision.reject("state-key-field-write");
                }
                transform = (MethodInsnNode) producer;
            }
            if (transform == null) {
                return KeyDecision.reject("state-key-transform-field");
            }
        } else {
            return KeyDecision.reject("state-key-source-node");
        }
        int bootstraps = 0;
        int transforms = 0;
        for (int index = 0; index < start; index++) {
            AbstractInsnNode insn = code.nodes.get(index);
            if (!(insn instanceof MethodInsnNode)) continue;
            MethodInsnNode call = (MethodInsnNode) insn;
            if (isStateBootstrap(call)) bootstraps++;
            if (isStateTransform(call)) transforms++;
        }
        if (bootstraps != 1 || transforms != 1) {
            return KeyDecision.reject("state-call-count=" + bootstraps
                    + "/" + transforms);
        }
        long mask = (Long) maskNode.cst;
        return KeyDecision.state(proof.classKey, mask,
                proof.classKey ^ mask, proof.source);
    }

    private static void apply(ClassNode owner, Candidate candidate)
            throws Exception {
        MethodNode clinit = method(owner, "<clinit>", "()V");
        if (clinit == null) throw new IllegalStateException("missing clinit");
        AbstractInsnNode start = codeNode(clinit, candidate.startIndex);
        AbstractInsnNode sink = codeNode(clinit, candidate.sinkIndex);
        if (start == null || sink == null) {
            throw new IllegalStateException("region moved");
        }
        LabelNode target = new LabelNode();
        clinit.instructions.insertBefore(sink, target);
        InsnList replacement = new InsnList();
        replacement.add(new LdcInsnNode(candidate.plaintext));
        replacement.add(new JumpInsnNode(Opcodes.GOTO, target));
        clinit.instructions.insertBefore(start, replacement);
        clinit.instructions.remove(start);

        Frame<BasicValue>[] frames = new Analyzer<BasicValue>(
                new BasicVerifier()).analyze(owner.name, clinit);
        List<AbstractInsnNode> unreachable = new ArrayList<>();
        int raw = 0;
        for (AbstractInsnNode insn = clinit.instructions.getFirst(); insn != null;
             insn = insn.getNext(), raw++) {
            if (insn.getOpcode() >= 0 && frames[raw] == null) {
                unreachable.add(insn);
            }
        }
        clinit.tryCatchBlocks.removeIf(block -> !reachableExceptionRange(
                clinit, block, frames));
        for (AbstractInsnNode insn : unreachable) {
            clinit.instructions.remove(insn);
        }
        for (AbstractInsnNode insn = clinit.instructions.getFirst(); insn != null; ) {
            AbstractInsnNode next = insn.getNext();
            if (insn instanceof FrameNode) clinit.instructions.remove(insn);
            insn = next;
        }
        if (clinit.localVariables != null) clinit.localVariables.clear();
        clinit.visibleLocalVariableAnnotations = null;
        clinit.invisibleLocalVariableAnnotations = null;
        new Analyzer<BasicValue>(new BasicVerifier()).analyze(owner.name, clinit);
        if (containsPkcs5(clinit)) {
            throw new IllegalStateException("PKCS5 survived pruning");
        }
    }

    private static boolean reachableExceptionRange(
            MethodNode method, TryCatchBlockNode block,
            Frame<BasicValue>[] frames) {
        int handler = method.instructions.indexOf(block.handler);
        int start = method.instructions.indexOf(block.start);
        int end = method.instructions.indexOf(block.end);
        if (handler < 0 || start < 0 || end < 0 || start >= end
                || handler >= frames.length || frames[handler] == null) {
            return false;
        }
        for (int index = start; index < end && index < frames.length; index++) {
            AbstractInsnNode insn = method.instructions.get(index);
            if (insn.getOpcode() >= 0 && frames[index] != null) return true;
        }
        return false;
    }

    private static void assertRewritten(ClassNode owner, Candidate candidate) {
        MethodNode clinit = method(owner, "<clinit>", "()V");
        if (clinit == null || containsPkcs5(clinit)) {
            throw new IllegalStateException("PKCS5 postcondition");
        }
        boolean plaintext = false;
        for (AbstractInsnNode insn = clinit.instructions.getFirst(); insn != null;
             insn = insn.getNext()) {
            if (insn instanceof LdcInsnNode
                    && candidate.plaintext.equals(((LdcInsnNode) insn).cst)) {
                plaintext = true;
            }
        }
        if (!plaintext) throw new IllegalStateException("plaintext missing");
    }

    private static void writeArchive(List<EntryBytes> entries,
                                     Map<String, byte[]> replacements,
                                     Path output, Summary summary,
                                     List<String> verifier) throws Exception {
        Path parent = output.toAbsolutePath().normalize().getParent();
        if (parent != null) Files.createDirectories(parent);
        Path temporary = Files.createTempFile(parent, output.getFileName().toString(),
                ".tmp");
        summary.temporaryOutput = temporary.toAbsolutePath().toString();
        int signatures = 0;
        try {
            try (ZipOutputStream zip = new ZipOutputStream(Files.newOutputStream(temporary))) {
                for (EntryBytes entry : entries) {
                    if (isSignature(entry.name)) {
                        signatures++;
                        continue;
                    }
                    ZipEntry written = new ZipEntry(entry.name);
                    if (entry.time >= 0) written.setTime(entry.time);
                    if (entry.comment != null) written.setComment(entry.comment);
                    if (entry.extra != null) written.setExtra(entry.extra);
                    zip.putNextEntry(written);
                    byte[] bytes = entry.name.endsWith(".class")
                            ? replacements.getOrDefault(entry.className(), entry.bytes)
                            : entry.bytes;
                    if (bytes.length != 0) zip.write(bytes);
                    zip.closeEntry();
                }
            }
            ArchiveVerification verification = verifyArchive(temporary, verifier);
            summary.outputEntries = entries.size() - signatures;
            summary.outputClasses = verification.classes;
            summary.outputPkcs5 = verification.pkcs5;
            summary.outputVerificationErrors = verification.errors;
            summary.signaturesRemoved = signatures;
            if (verification.errors != 0) {
                throw new IllegalStateException("archive verification errors="
                        + verification.errors);
            }
            try {
                Files.move(temporary, output, StandardCopyOption.ATOMIC_MOVE,
                        StandardCopyOption.REPLACE_EXISTING);
            } catch (AtomicMoveNotSupportedException ignored) {
                Files.move(temporary, output, StandardCopyOption.REPLACE_EXISTING);
            }
            summary.outputCommitted = true;
        } catch (Throwable failure) {
            summary.outputVerificationErrors++;
            verifier.add(tsv("archive", "*", "FAIL", shortReason(failure)));
            Files.deleteIfExists(temporary);
        }
    }

    private static ArchiveVerification verifyArchive(Path archive,
                                                      List<String> verifier)
            throws Exception {
        ArchiveVerification result = new ArchiveVerification();
        try (ZipInputStream input = new ZipInputStream(Files.newInputStream(archive))) {
            ZipEntry entry;
            while ((entry = input.getNextEntry()) != null) {
                if (entry.isDirectory() || !entry.getName().endsWith(".class")) continue;
                byte[] bytes = readAll(input);
                try {
                    verifyClass(bytes);
                    ClassNode owner = readClass(bytes);
                    MethodNode clinit = method(owner, "<clinit>", "()V");
                    if (clinit != null && containsPkcs5(clinit)) result.pkcs5++;
                    result.classes++;
                    verifier.add(tsv("archive", owner.name, "PASS", ""));
                } catch (Throwable failure) {
                    result.errors++;
                    verifier.add(tsv("archive", entry.getName(), "FAIL",
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
                new Analyzer<BasicValue>(new BasicVerifier()).analyze(owner.name,
                        method);
            }
        }
    }

    private static void writeReports(Path input, Path output, Path directory,
                                     Summary summary, List<Candidate> candidates,
                                     List<String> verifier, int classKeys)
            throws Exception {
        List<String> rows = new ArrayList<>();
        rows.add("class\tinsns\tpkcs5\tregion\tsink\tstate_derived"
                + "\tclass_key_hex\tmask_hex\tkey_hex\tkey_source"
                + "\tciphertext_length\tplaintext\tproven\taction\treason");
        for (Candidate candidate : candidates) rows.add(candidate.row());
        Files.write(directory.resolve("candidates.tsv"), rows,
                StandardCharsets.UTF_8);
        Files.write(directory.resolve("verifier.tsv"), verifier,
                StandardCharsets.UTF_8);
        List<String> audit = new ArrayList<>();
        audit.add("input=" + input.toAbsolutePath());
        audit.add("input_sha256=" + sha256(input));
        audit.add("pre_removal_authority=" + summary.authority);
        audit.add("pre_removal_authority_sha256=" + summary.authoritySha256);
        audit.add("parsed_classes=" + summary.parsedClasses);
        audit.add("input_pkcs5_calls=" + summary.inputPkcs5);
        audit.add("candidates=" + summary.candidates);
        audit.add("proven=" + summary.proven);
        audit.add("rejected=" + summary.rejected);
        audit.add("changed_classes=" + summary.changedClasses);
        audit.add("rollbacks=" + summary.rollbacks);
        audit.add("output_requested=" + summary.outputRequested);
        audit.add("output=" + (output == null ? "" : output.toAbsolutePath()));
        audit.add("temporary_output=" + value(summary.temporaryOutput));
        audit.add("output_entries=" + summary.outputEntries);
        audit.add("output_classes=" + summary.outputClasses);
        audit.add("output_pkcs5_calls=" + summary.outputPkcs5);
        audit.add("pkcs5_calls_removed=" + summary.pkcs5Removed);
        audit.add("output_verification_errors=" + summary.outputVerificationErrors);
        audit.add("signatures_removed=" + summary.signaturesRemoved);
        audit.add("output_committed=" + summary.outputCommitted);
        audit.add("state_class_key_proofs=" + classKeys);
        audit.add("policy=closed scalar result CFG island; literal or state-bound key;"
                + " original result sink and business tail retained");
        audit.add("input_classes_loaded=false");
        audit.add("input_classes_initialized=false");
        audit.add("gate=" + gate(summary));
        Files.write(directory.resolve("audit.txt"), audit,
                StandardCharsets.UTF_8);
        Files.write(directory.resolve("gate.txt"),
                Collections.singletonList(gate(summary)), StandardCharsets.UTF_8);
    }

    private static String gate(Summary summary) {
        if (summary.rollbacks != 0 || summary.outputVerificationErrors != 0
                || summary.outputRequested && !summary.outputCommitted) return "FAIL";
        return summary.proven == 0 ? "FAIL" : "PASS";
    }

    private static Map<String, ClassNode> classNodes(Map<String, byte[]> bytes) {
        Map<String, ClassNode> result = new LinkedHashMap<>();
        for (byte[] value : bytes.values()) {
            ClassNode node = readClass(value);
            result.put(node.name, node);
        }
        return result;
    }

    private static void mergeClassKeyCandidates(
            Map<String, Set<Long>> target, Map<String, Set<Long>> source) {
        for (Map.Entry<String, Set<Long>> entry : source.entrySet()) {
            target.computeIfAbsent(entry.getKey(), ignored ->
                    new LinkedHashSet<Long>()).addAll(entry.getValue());
        }
    }

    private static Map<String, byte[]> classBytes(List<EntryBytes> entries) {
        Map<String, byte[]> result = new LinkedHashMap<>();
        for (EntryBytes entry : entries) {
            if (entry.name.endsWith(".class")) result.put(entry.className(), entry.bytes);
        }
        return result;
    }

    private static List<EntryBytes> readEntries(Path input) throws IOException {
        List<EntryBytes> result = new ArrayList<>();
        try (ZipInputStream zip = new ZipInputStream(Files.newInputStream(input))) {
            ZipEntry entry;
            while ((entry = zip.getNextEntry()) != null) {
                result.add(new EntryBytes(entry, entry.isDirectory()
                        ? new byte[0] : readAll(zip)));
            }
        }
        return result;
    }

    private static int countPkcs5(Map<String, ClassNode> classes) {
        int result = 0;
        for (ClassNode owner : classes.values()) {
            for (MethodNode method : owner.methods) {
                for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
                     insn = insn.getNext()) {
                    if (isPkcs5Factory(insn)) result++;
                }
            }
        }
        return result;
    }

    private static boolean containsPkcs5(MethodNode method) {
        for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
             insn = insn.getNext()) {
            if (isPkcs5Factory(insn)) return true;
        }
        return false;
    }

    private static int uniqueCallIndex(Code code, Set<Integer> region,
                                       String owner, String name, String desc) {
        int result = -1;
        for (int index : region) {
            if (!isCall(code.nodes.get(index), -1, owner, name, desc)) continue;
            if (result >= 0) return -1;
            result = index;
        }
        return result;
    }

    private static boolean isPkcs5Factory(AbstractInsnNode insn) {
        return isCall(insn, Opcodes.INVOKESTATIC, "javax/crypto/Cipher",
                "getInstance", "(Ljava/lang/String;)Ljavax/crypto/Cipher;")
                && previousCode(insn) instanceof LdcInsnNode
                && PKCS5.equals(((LdcInsnNode) previousCode(insn)).cst);
    }

    private static boolean isCall(AbstractInsnNode insn, int opcode,
                                  String owner, String name, String desc) {
        if (!(insn instanceof MethodInsnNode)) return false;
        MethodInsnNode call = (MethodInsnNode) insn;
        return (opcode < 0 || opcode == call.getOpcode())
                && owner.equals(call.owner) && name.equals(call.name)
                && desc.equals(call.desc);
    }

    private static String call(int opcode, String owner, String name,
                               String desc) {
        return opcode + ":" + owner + "." + name + desc;
    }

    private static void put(Map<String, Integer> target, String key) {
        target.put(key, 1);
    }

    private static boolean isStateBootstrap(MethodInsnNode call) {
        return call.getOpcode() == Opcodes.INVOKESTATIC
                && STATE.equals(call.owner) && "a".equals(call.name)
                && ObfRuntimeNames.BOOTSTRAP_DESC
                .equals(call.desc);
    }

    private static boolean isStateTransform(MethodInsnNode call) {
        return call.getOpcode() == Opcodes.INVOKEINTERFACE
                && STATE_IFACE.equals(call.owner) && "a".equals(call.name)
                && "(J)J".equals(call.desc);
    }

    private static boolean longLdc(AbstractInsnNode node) {
        return node instanceof LdcInsnNode
                && ((LdcInsnNode) node).cst instanceof Long;
    }

    private static AbstractInsnNode unique(SourceValue value) {
        if (value == null || value.insns == null || value.insns.size() != 1) {
            return null;
        }
        return value.insns.iterator().next();
    }

    private static AbstractInsnNode codeNode(MethodNode method, int codeIndex) {
        int current = 0;
        for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
             insn = insn.getNext()) {
            if (insn.getOpcode() < 0) continue;
            if (current++ == codeIndex) return insn;
        }
        return null;
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

    private static AbstractInsnNode previousCode(AbstractInsnNode node) {
        AbstractInsnNode cursor = node == null ? null : node.getPrevious();
        while (cursor != null && cursor.getOpcode() < 0) cursor = cursor.getPrevious();
        return cursor;
    }

    private static byte[] readAll(InputStream input) throws IOException {
        ByteArrayOutputStream output = new ByteArrayOutputStream();
        byte[] buffer = new byte[8192];
        int count;
        while ((count = input.read(buffer)) >= 0) output.write(buffer, 0, count);
        return output.toByteArray();
    }

    private static ClassNode readClass(byte[] bytes) {
        ClassNode result = new ClassNode(Opcodes.ASM9);
        new ClassReader(bytes).accept(result, 0);
        return result;
    }

    private static boolean isSignature(String name) {
        String upper = name.toUpperCase(Locale.ROOT);
        if (!upper.startsWith("META-INF/")) return false;
        String leaf = upper.substring("META-INF/".length());
        return leaf.endsWith(".SF") || leaf.endsWith(".RSA")
                || leaf.endsWith(".DSA") || leaf.endsWith(".EC");
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

    private static String append(String original, String addition) {
        return original == null || original.isEmpty() ? addition
                : original + ";" + addition;
    }

    private static String printable(String value) {
        return value.replace('\t', ' ').replace('\r', ' ').replace('\n', ' ');
    }

    private static String value(Object value) {
        return value == null ? "" : String.valueOf(value);
    }

    private static String shortReason(Throwable failure) {
        String result = failure.getClass().getSimpleName() + ":"
                + String.valueOf(failure.getMessage());
        result = result.replace('\t', ' ').replace('\r', ' ').replace('\n', ' ');
        return result.substring(0, Math.min(240, result.length()));
    }

    private static String tsv(Object... cells) {
        List<String> values = new ArrayList<>();
        for (Object cell : cells) values.add(String.valueOf(cell).replace('\t', ' ')
                .replace('\r', ' ').replace('\n', ' '));
        return String.join("\t", values);
    }

    static final class Summary {
        String authority;
        String authoritySha256;
        int parsedClasses;
        int inputPkcs5;
        int candidates;
        int proven;
        int rejected;
        int changedClasses;
        int rollbacks;
        int outputPkcs5;
        int pkcs5Removed;
        boolean outputRequested;
        String temporaryOutput;
        int outputEntries;
        int outputClasses;
        int outputVerificationErrors;
        int signaturesRemoved;
        boolean outputCommitted;
    }

    private static final class TokenState {
        final int index;
        final int depth;

        TokenState(int index, int depth) {
            this.index = index;
            this.depth = depth;
        }
    }

    private static final class Candidate {
        final String owner;
        int instructions;
        int pkcs5Calls;
        int startIndex;
        int sinkIndex;
        int regionSize;
        String sinkKind = "";
        boolean stateDerived;
        long classKey;
        long mask;
        long key;
        String keyKind = "";
        int ciphertextLength;
        String plaintext = "";
        String decoderName = "";
        boolean proven;
        String action = "REJECT";
        String reason = "";

        Candidate(String owner) {
            this.owner = owner;
        }

        Candidate reject(String reason) {
            this.reason = reason;
            return this;
        }

        String row() {
            return tsv(owner, instructions, pkcs5Calls, regionSize, sinkKind,
                    stateDerived, stateDerived ? hex(classKey) : "",
                    stateDerived ? hex(mask) : "", proven ? hex(key) : "",
                    keyKind, ciphertextLength, printable(plaintext), proven,
                    action, reason);
        }
    }

    private static final class KeyDecision {
        final boolean proven;
        final long classKey;
        final long mask;
        final long key;
        final String source;
        final String reason;

        private KeyDecision(boolean proven, long classKey, long mask, long key,
                            String source, String reason) {
            this.proven = proven;
            this.classKey = classKey;
            this.mask = mask;
            this.key = key;
            this.source = source;
            this.reason = reason;
        }

        static KeyDecision literal(long key) {
            return new KeyDecision(true, 0L, 0L, key, "LDC_LONG", "");
        }

        static KeyDecision state(long classKey, long mask, long key,
                                 String source) {
            return new KeyDecision(true, classKey, mask, key,
                    "STATE_KEY:" + source, "");
        }

        static KeyDecision reject(String reason) {
            return new KeyDecision(false, 0L, 0L, 0L, "", reason);
        }
    }

    private static String hex(long value) {
        return String.format(Locale.ROOT, "%016X", value);
    }

    private static String classKeyHex(List<KeyDecision> decisions) {
        List<String> values = new ArrayList<>();
        for (KeyDecision decision : decisions) {
            values.add(hex(decision.classKey));
        }
        return String.join(",", values);
    }

    private static final class ArchiveVerification {
        int classes;
        int errors;
        int pkcs5;
    }

    private static final class EntryBytes {
        final String name;
        final byte[] bytes;
        final long time;
        final String comment;
        final byte[] extra;

        EntryBytes(ZipEntry entry, byte[] bytes) {
            this.name = entry.getName();
            this.bytes = bytes;
            this.time = entry.getTime();
            this.comment = entry.getComment();
            this.extra = entry.getExtra();
        }

        String className() {
            return name.substring(0, name.length() - ".class".length());
        }
    }

    private static final class Code {
        final List<AbstractInsnNode> nodes = new ArrayList<>();
        final IdentityHashMap<AbstractInsnNode, Integer> indices =
                new IdentityHashMap<>();
        final IdentityHashMap<LabelNode, Integer> labels =
                new IdentityHashMap<>();
        final List<List<Integer>> successors = new ArrayList<>();

        Code(MethodNode method) {
            for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
                 insn = insn.getNext()) {
                if (insn.getOpcode() >= 0) {
                    indices.put(insn, nodes.size());
                    nodes.add(insn);
                }
            }
            for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
                 insn = insn.getNext()) {
                if (!(insn instanceof LabelNode)) continue;
                AbstractInsnNode target = nextCode(insn);
                labels.put((LabelNode) insn,
                        target == null ? nodes.size() : index(target));
            }
            for (int index = 0; index < nodes.size(); index++) {
                successors.add(successors(index));
            }
        }

        int index(AbstractInsnNode node) {
            Integer result = indices.get(node);
            return result == null ? -1 : result;
        }

        private List<Integer> successors(int index) {
            AbstractInsnNode insn = nodes.get(index);
            List<Integer> result = new ArrayList<>();
            int opcode = insn.getOpcode();
            if (insn instanceof JumpInsnNode) {
                add(result, target(((JumpInsnNode) insn).label));
                if (opcode != Opcodes.GOTO && opcode != Opcodes.JSR
                        && index + 1 < nodes.size()) add(result, index + 1);
            } else if (insn instanceof TableSwitchInsnNode) {
                TableSwitchInsnNode table = (TableSwitchInsnNode) insn;
                add(result, target(table.dflt));
                for (LabelNode label : table.labels) add(result, target(label));
            } else if (insn instanceof LookupSwitchInsnNode) {
                LookupSwitchInsnNode table = (LookupSwitchInsnNode) insn;
                add(result, target(table.dflt));
                for (LabelNode label : table.labels) add(result, target(label));
            } else if (opcode != Opcodes.RETURN && opcode != Opcodes.IRETURN
                    && opcode != Opcodes.LRETURN && opcode != Opcodes.FRETURN
                    && opcode != Opcodes.DRETURN && opcode != Opcodes.ARETURN
                    && opcode != Opcodes.ATHROW && opcode != Opcodes.RET
                    && index + 1 < nodes.size()) {
                add(result, index + 1);
            }
            return result;
        }

        private int target(LabelNode label) {
            Integer result = labels.get(label);
            return result == null ? -1 : result;
        }

        private static void add(List<Integer> target, int value) {
            if (value >= 0 && !target.contains(value)) target.add(value);
        }
    }

    private static AbstractInsnNode nextCode(AbstractInsnNode node) {
        AbstractInsnNode cursor = node == null ? null : node.getNext();
        while (cursor != null && cursor.getOpcode() < 0) cursor = cursor.getNext();
        return cursor;
    }
}
