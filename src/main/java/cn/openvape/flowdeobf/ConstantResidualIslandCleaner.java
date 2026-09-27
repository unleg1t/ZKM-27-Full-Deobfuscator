package cn.openvape.flowdeobf;

import org.objectweb.asm.ClassReader;
import org.objectweb.asm.ClassWriter;
import org.objectweb.asm.Opcodes;
import org.objectweb.asm.tree.AbstractInsnNode;
import org.objectweb.asm.tree.ClassNode;
import org.objectweb.asm.tree.IntInsnNode;
import org.objectweb.asm.tree.JumpInsnNode;
import org.objectweb.asm.tree.LabelNode;
import org.objectweb.asm.tree.LdcInsnNode;
import org.objectweb.asm.tree.LookupSwitchInsnNode;
import org.objectweb.asm.tree.MethodNode;
import org.objectweb.asm.tree.TableSwitchInsnNode;
import org.objectweb.asm.tree.TryCatchBlockNode;
import org.objectweb.asm.tree.VarInsnNode;
import org.objectweb.asm.tree.analysis.Analyzer;
import org.objectweb.asm.tree.analysis.BasicValue;
import org.objectweb.asm.tree.analysis.BasicVerifier;
import org.objectweb.asm.tree.analysis.Frame;
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
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.zip.CRC32;
import java.util.zip.ZipEntry;
import java.util.zip.ZipInputStream;
import java.util.zip.ZipOutputStream;

/**
 * Removes one proven ZKM constant-only residual stack island:
 *
 * <pre>
 * int-constant, long-operand, long-operand, lxor, pop2, pop
 * </pre>
 *
 * <p>Each long operand is either a constant or a local load, and at least one
 * operand must be a constant. This covers the ZKM residual form that combines
 * a method key local with a site literal while keeping the matcher narrower
 * than general dead-code elimination.</p>
 *
 * <p>The matcher is intentionally narrow. Each island must be raw-contiguous,
 * have no internal control-flow entry, touch no exception range, and preserve
 * the complete verifier frame. A rewritten class is published only through a
 * verified class transaction. No sample class is loaded or initialized.</p>
 */
public final class ConstantResidualIslandCleaner {
    private static final int MAX_FIXED_POINT_PASSES = 32;

    private ConstantResidualIslandCleaner() {
    }

    public static void main(String[] args) throws Exception {
        if (args.length != 2 && args.length != 3) {
            System.err.println("usage: ConstantResidualIslandCleaner <input.jar>"
                    + " <report-dir> [output.jar]");
            System.exit(2);
        }
        rewrite(Paths.get(args[0]), Paths.get(args[1]),
                args.length == 3 ? Paths.get(args[2]) : null);
    }

    static Summary rewrite(Path input, Path reportDirectory, Path output)
            throws Exception {
        validatePaths(input, output);
        Files.createDirectories(reportDirectory);
        List<Entry> entries = readEntries(input);
        Map<String, byte[]> replacements = new LinkedHashMap<String, byte[]>();
        List<Island> audit = new ArrayList<Island>();
        List<ClassFailure> classFailures = new ArrayList<ClassFailure>();
        Summary summary = new Summary();

        for (Entry entry : entries) {
            if (!entry.name.endsWith(".class")) continue;
            summary.classEntries++;
            ClassResult result = rewriteClass(entry.bytes);
            if ("PARSE".equals(result.stage)) summary.parseFailures++;
            else summary.parsedClasses++;
            if (result.candidates != 0) {
                audit.addAll(result.internalIslands);
                summary.candidates += result.candidates;
                summary.proven += result.proven;
                summary.rejected += result.rejected;
                summary.fixedPointPasses += result.passes;
            }

            if (!result.committed) {
                summary.rollbacks++;
                classFailures.add(new ClassFailure(entry.name,
                        result.stage, result.reason));
                continue;
            }
            if (result.removed == 0) continue;

            summary.committedIslands += result.removed;
            summary.changedClasses++;
            for (Island island : result.internalIslands) {
                if (island.proven) {
                    island.action = output == null ? "PROVEN_DRY_RUN" : "REWRITE";
                }
            }
            if (output != null) replacements.put(entry.name, result.bytes());
        }

        if (output != null && summary.rollbacks != 0) {
            writeReports(input, output, reportDirectory, summary, audit,
                    classFailures);
            throw new IOException("refusing partial constant-island archive: class rollbacks="
                    + summary.rollbacks + ", parse failures=" + summary.parseFailures);
        }
        if (output != null) {
            writeVerifiedArchive(entries, replacements, output, summary);
        }
        writeReports(input, output, reportDirectory, summary, audit, classFailures);
        System.out.println("class_entries=" + summary.classEntries
                + " parsed_classes=" + summary.parsedClasses
                + " parse_failures=" + summary.parseFailures
                + " candidates=" + summary.candidates
                + " proven=" + summary.proven
                + " rejected=" + summary.rejected
                + " committed_islands=" + summary.committedIslands
                + " changed_classes=" + summary.changedClasses
                + " rollbacks=" + summary.rollbacks
                + " output_committed=" + summary.outputCommitted);
        return summary;
    }

    /**
     * Atomically rewrites every proven method island in one class. On any
     * mutation, emission, verifier, or fixed-point failure, {@link
     * ClassResult#bytes()} is an exact copy of the input class.
     */
    public static ClassResult rewriteClass(byte[] original) {
        if (original == null || original.length == 0) {
            throw new IllegalArgumentException("original class bytes are required");
        }
        try {
            if (!containsShape(original)) return ClassResult.unchanged(original);
        } catch (Throwable failure) {
            return ClassResult.failure(original, "PARSE", shortReason(failure));
        }

        RewriteWork work = new RewriteWork();
        ZkmClassRewriteTransaction.Result transaction =
                ZkmClassRewriteTransaction.attempt(
                        original,
                        owner -> rewriteToFixedPoint(owner, work),
                        ConstantResidualIslandCleaner::verifyFixedPoint,
                        owner -> {
                            ClassWriter writer = new ClassWriter(0);
                            owner.accept(writer);
                            return writer.toByteArray();
                        });
        if (!transaction.isCommitted() && work.removed != 0) {
            for (Island island : work.islands) {
                if (!island.proven) continue;
                island.action = "ROLLBACK";
                island.reason = appendReason(island.reason,
                        transaction.stage() + ":" + transaction.reason());
            }
        }
        return new ClassResult(transaction.bytes(), transaction.isCommitted(),
                transaction.stage().name(), transaction.reason(), work);
    }

    private static boolean containsShape(byte[] bytes) {
        ClassNode owner = readClass(bytes);
        for (MethodNode method : owner.methods) {
            if (!findShapes(method).isEmpty()) return true;
        }
        return false;
    }

    private static void rewriteToFixedPoint(ClassNode owner, RewriteWork work)
            throws Exception {
        Set<AbstractInsnNode> reported = Collections.newSetFromMap(
                new IdentityHashMap<AbstractInsnNode, Boolean>());
        for (int pass = 1; pass <= MAX_FIXED_POINT_PASSES; pass++) {
            int removedThisPass = 0;
            for (MethodNode method : owner.methods) {
                List<Island> islands = inspectMethod(owner, method, pass);
                for (Island island : islands) {
                    if (reported.add(island.nodes[0])) {
                        work.islands.add(island);
                        if (island.proven) work.proven++;
                        else work.rejected++;
                    }
                    if (!island.proven) continue;
                    remove(method, island);
                    removedThisPass++;
                }
            }
            work.passes = pass;
            work.removed += removedThisPass;
            if (removedThisPass == 0) return;
        }
        throw new IllegalStateException("constant-island fixed point did not converge");
    }

    private static void verifyFixedPoint(ClassNode owner) throws Exception {
        for (MethodNode method : owner.methods) {
            for (Island island : inspectMethod(owner, method, 0)) {
                if (island.proven) {
                    throw new IllegalStateException("proven residual island remains in "
                            + owner.name + '.' + method.name + method.desc);
                }
            }
        }
    }

    private static List<Island> inspectMethod(ClassNode owner, MethodNode method,
                                              int pass) {
        List<AbstractInsnNode[]> shapes = findShapes(method);
        if (shapes.isEmpty()) return Collections.emptyList();

        Map<AbstractInsnNode, Integer> indexes = rawIndexes(method);
        Frame<BasicValue>[] frames = null;
        String frameFailure = null;
        try {
            frames = new Analyzer<BasicValue>(new BasicVerifier())
                    .analyze(owner.name, method);
        } catch (Throwable failure) {
            frameFailure = shortReason(failure);
        }

        boolean legacySubroutine = hasLegacySubroutine(method);
        List<AbstractInsnNode> targets = controlFlowTargets(method);
        List<Island> result = new ArrayList<Island>();
        for (AbstractInsnNode[] nodes : shapes) {
            Island island = new Island(owner.name, method.name, method.desc,
                    pass, indexes.get(nodes[0]), nodes);
            if (!rawContiguous(nodes)) island.reject("NONCONTIGUOUS_METADATA");
            if (legacySubroutine) island.reject("JSR_RET_METHOD");
            validateControlFlow(island, targets);
            validateExceptionRanges(island, method, indexes);
            if (frameFailure != null) {
                island.reject("FRAME_ANALYSIS=" + frameFailure);
            } else {
                validateFrames(island, method, indexes, frames);
            }
            island.proven = island.reasons.isEmpty();
            island.action = island.proven ? "PROVEN" : "REJECT";
            island.reason = island.proven ? "PROVEN" : join(island.reasons);
            result.add(island);
        }
        return result;
    }

    private static List<AbstractInsnNode[]> findShapes(MethodNode method) {
        List<AbstractInsnNode[]> result = new ArrayList<AbstractInsnNode[]>();
        if (method.instructions == null || method.instructions.size() == 0) {
            return result;
        }
        for (AbstractInsnNode first = method.instructions.getFirst(); first != null;
             first = first.getNext()) {
            if (!isIntConstant(first)) continue;
            AbstractInsnNode second = nextCode(first);
            AbstractInsnNode third = nextCode(second);
            AbstractInsnNode fourth = nextCode(third);
            AbstractInsnNode fifth = nextCode(fourth);
            AbstractInsnNode sixth = nextCode(fifth);
            if (!isLongOperand(second) || !isLongOperand(third)
                    || !isLongLdc(second) && !isLongLdc(third)
                    || opcode(fourth) != Opcodes.LXOR
                    || opcode(fifth) != Opcodes.POP2
                    || opcode(sixth) != Opcodes.POP) continue;
            result.add(new AbstractInsnNode[]{first, second, third, fourth, fifth, sixth});
        }
        return result;
    }

    private static void validateControlFlow(Island island,
                                            List<AbstractInsnNode> targets) {
        for (AbstractInsnNode target : targets) {
            int position = position(island.nodes, target);
            if (position > 0) island.reject("EXTERNAL_ENTRY_AT=" + position);
        }
    }

    private static void validateExceptionRanges(Island island, MethodNode method,
                                                Map<AbstractInsnNode, Integer> indexes) {
        if (method.tryCatchBlocks == null) return;
        Integer islandStart = indexes.get(island.nodes[0]);
        Integer islandEnd = indexes.get(island.nodes[island.nodes.length - 1]);
        if (islandStart == null || islandEnd == null) {
            island.reject("MISSING_RAW_INDEX");
            return;
        }
        for (TryCatchBlockNode block : method.tryCatchBlocks) {
            Integer start = indexes.get(block.start);
            Integer end = indexes.get(block.end);
            AbstractInsnNode handler = nextCode(block.handler);
            if (start == null || end == null || handler == null) {
                island.reject("INVALID_EXCEPTION_RANGE");
                continue;
            }
            if (start <= islandEnd && end > islandStart) {
                island.reject("EXCEPTION_RANGE_OVERLAP");
            }
            if (position(island.nodes, handler) >= 0) {
                island.reject("EXCEPTION_HANDLER_ENTRY");
            }
        }
    }

    private static void validateFrames(Island island, MethodNode method,
                                       Map<AbstractInsnNode, Integer> indexes,
                                       Frame<BasicValue>[] frames) {
        AbstractInsnNode continuation = nextCode(island.nodes[5]);
        if (continuation == null) {
            island.reject("NO_CONTINUATION");
            return;
        }
        Frame<BasicValue>[] sequence = new Frame[7];
        for (int index = 0; index < 6; index++) {
            Integer raw = indexes.get(island.nodes[index]);
            sequence[index] = frameAt(frames, raw);
        }
        sequence[6] = frameAt(frames, indexes.get(continuation));
        for (Frame<BasicValue> frame : sequence) {
            if (frame == null) {
                island.reject("UNREACHABLE_FRAME");
                return;
            }
        }

        Frame<BasicValue> entry = sequence[0];
        if (!sameFrame(entry, sequence[6])) {
            island.reject("BOUNDARY_FRAME_MISMATCH");
        }
        if (!sameLocals(entry, sequence[1]) || !sameLocals(entry, sequence[2])
                || !sameLocals(entry, sequence[3]) || !sameLocals(entry, sequence[4])
                || !sameLocals(entry, sequence[5])) {
            island.reject("LOCAL_FRAME_CHANGED");
        }

        int stack = entry.getStackSize();
        requireStack(island, sequence[1], stack + 1,
                new BasicValue[]{BasicValue.INT_VALUE});
        requireStack(island, sequence[2], stack + 2,
                new BasicValue[]{BasicValue.INT_VALUE, BasicValue.LONG_VALUE});
        requireStack(island, sequence[3], stack + 3,
                new BasicValue[]{BasicValue.INT_VALUE, BasicValue.LONG_VALUE,
                        BasicValue.LONG_VALUE});
        requireStack(island, sequence[4], stack + 2,
                new BasicValue[]{BasicValue.INT_VALUE, BasicValue.LONG_VALUE});
        requireStack(island, sequence[5], stack + 1,
                new BasicValue[]{BasicValue.INT_VALUE});
    }

    private static void requireStack(Island island, Frame<BasicValue> frame,
                                     int size, BasicValue[] suffix) {
        if (frame.getStackSize() != size) {
            island.reject("STACK_SIZE=" + frame.getStackSize() + '/' + size);
            return;
        }
        int start = size - suffix.length;
        for (int index = 0; index < suffix.length; index++) {
            if (!Objects.equals(suffix[index], frame.getStack(start + index))) {
                island.reject("STACK_TYPE_AT=" + (start + index));
            }
        }
    }

    private static boolean sameFrame(Frame<BasicValue> left,
                                     Frame<BasicValue> right) {
        return sameLocals(left, right) && sameStack(left, right);
    }

    private static boolean sameLocals(Frame<BasicValue> left,
                                      Frame<BasicValue> right) {
        if (left.getLocals() != right.getLocals()) return false;
        for (int index = 0; index < left.getLocals(); index++) {
            if (!Objects.equals(left.getLocal(index), right.getLocal(index))) return false;
        }
        return true;
    }

    private static boolean sameStack(Frame<BasicValue> left,
                                     Frame<BasicValue> right) {
        if (left.getStackSize() != right.getStackSize()) return false;
        for (int index = 0; index < left.getStackSize(); index++) {
            if (!Objects.equals(left.getStack(index), right.getStack(index))) return false;
        }
        return true;
    }

    private static Frame<BasicValue> frameAt(Frame<BasicValue>[] frames,
                                             Integer index) {
        return index == null || index < 0 || index >= frames.length
                ? null : frames[index];
    }

    private static List<AbstractInsnNode> controlFlowTargets(MethodNode method) {
        List<AbstractInsnNode> result = new ArrayList<AbstractInsnNode>();
        for (AbstractInsnNode node = method.instructions.getFirst(); node != null;
             node = node.getNext()) {
            if (node instanceof JumpInsnNode) {
                addTarget(result, ((JumpInsnNode) node).label);
            } else if (node instanceof TableSwitchInsnNode) {
                TableSwitchInsnNode table = (TableSwitchInsnNode) node;
                addTarget(result, table.dflt);
                for (LabelNode label : table.labels) addTarget(result, label);
            } else if (node instanceof LookupSwitchInsnNode) {
                LookupSwitchInsnNode lookup = (LookupSwitchInsnNode) node;
                addTarget(result, lookup.dflt);
                for (LabelNode label : lookup.labels) addTarget(result, label);
            }
        }
        return result;
    }

    private static void addTarget(List<AbstractInsnNode> targets, LabelNode label) {
        AbstractInsnNode target = nextCode(label);
        if (target != null) targets.add(target);
    }

    private static boolean hasLegacySubroutine(MethodNode method) {
        for (AbstractInsnNode node = method.instructions.getFirst(); node != null;
             node = node.getNext()) {
            if (node.getOpcode() == Opcodes.JSR || node.getOpcode() == Opcodes.RET) {
                return true;
            }
        }
        return false;
    }

    private static Map<AbstractInsnNode, Integer> rawIndexes(MethodNode method) {
        Map<AbstractInsnNode, Integer> result =
                new IdentityHashMap<AbstractInsnNode, Integer>();
        int index = 0;
        for (AbstractInsnNode node = method.instructions.getFirst(); node != null;
             node = node.getNext()) result.put(node, index++);
        return result;
    }

    private static boolean rawContiguous(AbstractInsnNode[] nodes) {
        for (int index = 0; index + 1 < nodes.length; index++) {
            if (nodes[index].getNext() != nodes[index + 1]) return false;
        }
        return true;
    }

    private static int position(AbstractInsnNode[] nodes, AbstractInsnNode target) {
        for (int index = 0; index < nodes.length; index++) {
            if (nodes[index] == target) return index;
        }
        return -1;
    }

    private static void remove(MethodNode method, Island island) {
        for (AbstractInsnNode node : island.nodes) method.instructions.remove(node);
    }

    private static boolean isIntConstant(AbstractInsnNode node) {
        if (node == null) return false;
        int opcode = node.getOpcode();
        if (opcode >= Opcodes.ICONST_M1 && opcode <= Opcodes.ICONST_5) return true;
        if (node instanceof IntInsnNode) {
            return opcode == Opcodes.BIPUSH || opcode == Opcodes.SIPUSH;
        }
        return node instanceof LdcInsnNode
                && ((LdcInsnNode) node).cst instanceof Integer;
    }

    private static boolean isLongLdc(AbstractInsnNode node) {
        return node instanceof LdcInsnNode
                && ((LdcInsnNode) node).cst instanceof Long;
    }

    private static boolean isLongOperand(AbstractInsnNode node) {
        return isLongLdc(node) || opcode(node) == Opcodes.LLOAD;
    }

    private static int opcode(AbstractInsnNode node) {
        return node == null ? -1 : node.getOpcode();
    }

    private static AbstractInsnNode nextCode(AbstractInsnNode node) {
        AbstractInsnNode cursor = node == null ? null : node.getNext();
        while (cursor != null && cursor.getOpcode() < 0) cursor = cursor.getNext();
        return cursor;
    }

    private static void validatePaths(Path input, Path output) throws IOException {
        if (!Files.isRegularFile(input)) {
            throw new IOException("input archive does not exist: " + input);
        }
        if (output == null) return;
        if (input.toAbsolutePath().normalize().equals(
                output.toAbsolutePath().normalize())) {
            throw new IllegalArgumentException("output must not replace input");
        }
        Path parent = output.toAbsolutePath().normalize().getParent();
        if (parent != null) Files.createDirectories(parent);
    }

    private static List<Entry> readEntries(Path input) throws IOException {
        List<Entry> result = new ArrayList<Entry>();
        try (ZipInputStream zip = new ZipInputStream(Files.newInputStream(input))) {
            ZipEntry entry;
            while ((entry = zip.getNextEntry()) != null) {
                result.add(new Entry(entry, readAll(zip)));
            }
        }
        return result;
    }

    private static void writeVerifiedArchive(List<Entry> entries,
                                             Map<String, byte[]> replacements,
                                             Path output, Summary summary)
            throws IOException {
        Path absolute = output.toAbsolutePath().normalize();
        Path parent = absolute.getParent();
        if (parent == null) parent = Paths.get(".").toAbsolutePath().normalize();
        Path temporary = Files.createTempFile(parent, absolute.getFileName().toString(),
                ".constant-islands.tmp");
        Set<String> applied = new LinkedHashSet<String>();
        try {
            try (ZipOutputStream zip = new ZipOutputStream(Files.newOutputStream(temporary))) {
                for (Entry entry : entries) {
                    if (!replacements.isEmpty() && isSignatureEntry(entry.name)) {
                        summary.removedSignatureEntries++;
                        continue;
                    }
                    byte[] bytes = replacements.get(entry.name);
                    if (bytes == null) bytes = entry.bytes;
                    else applied.add(entry.name);
                    ZipEntry written = copyEntry(entry, bytes);
                    zip.putNextEntry(written);
                    if (!entry.directory) zip.write(bytes);
                    zip.closeEntry();
                }
            }
            if (!applied.equals(replacements.keySet())) {
                throw new IOException("replacement coverage " + applied.size() + '/'
                        + replacements.size());
            }
            verifyOutputArchive(temporary,
                    entries.size() - summary.removedSignatureEntries,
                    summary.classEntries, replacements);
            try {
                Files.move(temporary, absolute, StandardCopyOption.ATOMIC_MOVE,
                        StandardCopyOption.REPLACE_EXISTING);
            } catch (AtomicMoveNotSupportedException unsupported) {
                Files.move(temporary, absolute, StandardCopyOption.REPLACE_EXISTING);
            }
            summary.outputCommitted = true;
        } finally {
            Files.deleteIfExists(temporary);
        }
    }

    private static boolean isSignatureEntry(String name) {
        String upper = name.replace('\\', '/').toUpperCase(java.util.Locale.ROOT);
        if (!upper.startsWith("META-INF/")) return false;
        String leaf = upper.substring("META-INF/".length());
        if (leaf.indexOf('/') >= 0) return false;
        return leaf.endsWith(".SF") || leaf.endsWith(".RSA")
                || leaf.endsWith(".DSA") || leaf.endsWith(".EC")
                || leaf.startsWith("SIG-");
    }

    private static ZipEntry copyEntry(Entry entry, byte[] bytes) {
        ZipEntry result = new ZipEntry(entry.name);
        if (entry.time >= 0) result.setTime(entry.time);
        if (entry.comment != null) result.setComment(entry.comment);
        if (entry.extra != null) result.setExtra(entry.extra);
        if (entry.directory) return result;
        if (entry.method == ZipEntry.STORED) {
            CRC32 crc = new CRC32();
            crc.update(bytes);
            result.setMethod(ZipEntry.STORED);
            result.setSize(bytes.length);
            result.setCompressedSize(bytes.length);
            result.setCrc(crc.getValue());
        } else {
            result.setMethod(ZipEntry.DEFLATED);
        }
        return result;
    }

    private static void verifyOutputArchive(Path output, int expectedEntries,
                                            int expectedClasses,
                                            Map<String, byte[]> replacements)
            throws IOException {
        int entries = 0;
        int classes = 0;
        Set<String> names = new LinkedHashSet<String>();
        Set<String> verified = new LinkedHashSet<String>();
        try (ZipInputStream zip = new ZipInputStream(Files.newInputStream(output))) {
            ZipEntry entry;
            while ((entry = zip.getNextEntry()) != null) {
                entries++;
                if (!names.add(entry.getName())) {
                    throw new IOException("duplicate archive entry: " + entry.getName());
                }
                byte[] bytes = readAll(zip);
                if (!entry.isDirectory() && entry.getName().endsWith(".class")) {
                    verifyClassBytes(entry.getName(), bytes);
                    classes++;
                }
                byte[] expected = replacements.get(entry.getName());
                if (expected != null) {
                    if (!java.util.Arrays.equals(expected, bytes)) {
                        throw new IOException("rewritten entry mismatch: " + entry.getName());
                    }
                    verified.add(entry.getName());
                }
            }
        }
        if (entries != expectedEntries) {
            throw new IOException("archive entry count " + entries + '/' + expectedEntries);
        }
        if (classes != expectedClasses) {
            throw new IOException("archive class count " + classes + '/' + expectedClasses);
        }
        if (!verified.equals(replacements.keySet())) {
            throw new IOException("verified replacement coverage " + verified.size() + '/'
                    + replacements.size());
        }
    }

    private static void verifyClassBytes(String entryName, byte[] bytes)
            throws IOException {
        try {
            ClassReader reader = new ClassReader(bytes);
            reader.accept(new CheckClassAdapter(new ClassWriter(0), false), 0);
            ClassNode owner = readClass(bytes);
            for (MethodNode method : owner.methods) {
                if (method.instructions != null && method.instructions.size() != 0) {
                    new Analyzer<BasicValue>(new BasicVerifier())
                            .analyze(owner.name, method);
                }
            }
        } catch (Throwable failure) {
            throw new IOException("archive verifier rejected " + entryName + ": "
                    + shortReason(failure), failure);
        }
    }

    private static void writeReports(Path input, Path output, Path reportDirectory,
                                     Summary summary, List<Island> islands,
                                     List<ClassFailure> classFailures)
            throws IOException {
        List<String> rows = new ArrayList<String>();
        rows.add("class\tmethod\tdesc\tpass\traw_start\tint_value\tlong_left"
                + "\tlong_right\taction\tproven\treason");
        for (Island island : islands) rows.add(island.row());
        Files.write(reportDirectory.resolve("islands.tsv"), rows,
                StandardCharsets.UTF_8);

        List<String> failures = new ArrayList<String>();
        failures.add("entry\tstage\treason");
        for (ClassFailure failure : classFailures) failures.add(failure.row());
        Files.write(reportDirectory.resolve("class-failures.tsv"), failures,
                StandardCharsets.UTF_8);

        List<String> audit = new ArrayList<String>();
        audit.add("input=" + input.toAbsolutePath().normalize());
        audit.add("input_sha256=" + sha256(Files.readAllBytes(input)));
        audit.add("output=" + (output == null ? ""
                : output.toAbsolutePath().normalize()));
        audit.add("class_entries=" + summary.classEntries);
        audit.add("parsed_classes=" + summary.parsedClasses);
        audit.add("parse_failures=" + summary.parseFailures);
        audit.add("candidates=" + summary.candidates);
        audit.add("proven=" + summary.proven);
        audit.add("rejected=" + summary.rejected);
        audit.add("committed_islands=" + summary.committedIslands);
        audit.add("changed_classes=" + summary.changedClasses);
        audit.add("rollbacks=" + summary.rollbacks);
        audit.add("fixed_point_passes=" + summary.fixedPointPasses);
        audit.add("removed_signature_entries=" + summary.removedSignatureEntries);
        audit.add("output_committed=" + summary.outputCommitted);
        audit.add("policy=exact int,(LDC-long|LLOAD),(LDC-long|LLOAD),"
                + "LXOR,POP2,POP with at least one LDC-long;"
                + " raw-contiguous; no internal CFG entry; no exception overlap;"
                + " complete verifier frame equality; class transaction; fixed point");
        Files.write(reportDirectory.resolve("audit.txt"), audit,
                StandardCharsets.UTF_8);
    }

    private static ClassNode readClass(byte[] bytes) {
        ClassNode result = new ClassNode(Opcodes.ASM9);
        new ClassReader(bytes).accept(result, 0);
        return result;
    }

    private static byte[] readAll(ZipInputStream input) throws IOException {
        ByteArrayOutputStream output = new ByteArrayOutputStream();
        byte[] buffer = new byte[8192];
        int count;
        while ((count = input.read(buffer)) >= 0) {
            if (count != 0) output.write(buffer, 0, count);
        }
        return output.toByteArray();
    }

    private static String sha256(byte[] bytes) throws IOException {
        try {
            MessageDigest digest = MessageDigest.getInstance("SHA-256");
            StringBuilder result = new StringBuilder();
            for (byte value : digest.digest(bytes)) {
                result.append(String.format("%02X", value));
            }
            return result.toString();
        } catch (Exception failure) {
            throw new IOException(failure);
        }
    }

    private static String intValue(AbstractInsnNode node) {
        int opcode = node.getOpcode();
        if (opcode >= Opcodes.ICONST_M1 && opcode <= Opcodes.ICONST_5) {
            return Integer.toString(opcode - Opcodes.ICONST_0);
        }
        if (node instanceof IntInsnNode) {
            return Integer.toString(((IntInsnNode) node).operand);
        }
        return String.valueOf(((LdcInsnNode) node).cst);
    }

    private static String longValue(AbstractInsnNode node) {
        if (node instanceof LdcInsnNode) {
            return String.valueOf(((LdcInsnNode) node).cst);
        }
        return "local:" + ((VarInsnNode) node).var;
    }

    private static String appendReason(String current, String addition) {
        return current == null || current.isEmpty() || "PROVEN".equals(current)
                ? addition : current + ';' + addition;
    }

    private static String join(List<String> values) {
        StringBuilder result = new StringBuilder();
        for (String value : values) {
            if (result.length() != 0) result.append(';');
            result.append(value);
        }
        return result.toString();
    }

    private static String shortReason(Throwable failure) {
        String message = failure.getMessage();
        return failure.getClass().getSimpleName()
                + (message == null || message.isEmpty() ? "" : ":" + message);
    }

    static final class Summary {
        int classEntries;
        int parsedClasses;
        int parseFailures;
        int candidates;
        int proven;
        int rejected;
        int committedIslands;
        int changedClasses;
        int rollbacks;
        int fixedPointPasses;
        int removedSignatureEntries;
        boolean outputCommitted;
    }

    /** Result consumed by the archive CLI and by the fixed-point coordinator. */
    public static final class ClassResult {
        private final byte[] bytes;
        private final boolean committed;
        private final String stage;
        private final String reason;
        private final int candidates;
        private final int proven;
        private final int rejected;
        private final int removed;
        private final int passes;
        private final List<Island> internalIslands;

        private ClassResult(byte[] bytes, boolean committed, String stage,
                            String reason, RewriteWork work) {
            this.bytes = bytes.clone();
            this.committed = committed;
            this.stage = stage;
            this.reason = reason;
            this.candidates = work.islands.size();
            this.proven = work.proven;
            this.rejected = work.rejected;
            this.removed = work.removed;
            this.passes = work.passes;
            this.internalIslands = Collections.unmodifiableList(
                    new ArrayList<Island>(work.islands));
        }

        private static ClassResult unchanged(byte[] bytes) {
            return new ClassResult(bytes, true, "UNCHANGED", "NO_CANDIDATE",
                    new RewriteWork());
        }

        private static ClassResult failure(byte[] bytes, String stage, String reason) {
            return new ClassResult(bytes, false, stage, reason, new RewriteWork());
        }

        public byte[] bytes() {
            return bytes.clone();
        }

        public boolean isCommitted() {
            return committed;
        }

        public String stage() {
            return stage;
        }

        public String reason() {
            return reason;
        }

        public int candidates() {
            return candidates;
        }

        public int proven() {
            return proven;
        }

        public int rejected() {
            return rejected;
        }

        public int removed() {
            return removed;
        }

        /** Includes the final zero-change convergence pass. */
        public int passes() {
            return passes;
        }

        public List<IslandLocation> islands() {
            List<IslandLocation> result = new ArrayList<IslandLocation>();
            for (Island island : internalIslands) {
                result.add(new IslandLocation(island));
            }
            return Collections.unmodifiableList(result);
        }
    }

    /** Stable method and raw-instruction location for audit report merging. */
    public static final class IslandLocation {
        private final String owner;
        private final String method;
        private final String descriptor;
        private final int pass;
        private final int rawStart;
        private final boolean proven;
        private final String action;
        private final String reason;

        private IslandLocation(Island island) {
            this.owner = island.owner;
            this.method = island.method;
            this.descriptor = island.desc;
            this.pass = island.pass;
            this.rawStart = island.rawStart;
            this.proven = island.proven;
            this.action = island.action;
            this.reason = island.reason;
        }

        public String owner() { return owner; }
        public String method() { return method; }
        public String descriptor() { return descriptor; }
        public int pass() { return pass; }
        public int rawStart() { return rawStart; }
        public boolean isProven() { return proven; }
        public String action() { return action; }
        public String reason() { return reason; }
    }

    private static final class RewriteWork {
        final List<Island> islands = new ArrayList<Island>();
        int proven;
        int rejected;
        int removed;
        int passes;
    }

    private static final class Island {
        final String owner;
        final String method;
        final String desc;
        final int pass;
        final int rawStart;
        final AbstractInsnNode[] nodes;
        final List<String> reasons = new ArrayList<String>();
        boolean proven;
        String action;
        String reason;

        Island(String owner, String method, String desc, int pass, int rawStart,
               AbstractInsnNode[] nodes) {
            this.owner = owner;
            this.method = method;
            this.desc = desc;
            this.pass = pass;
            this.rawStart = rawStart;
            this.nodes = nodes;
        }

        void reject(String value) {
            if (!reasons.contains(value)) reasons.add(value);
        }

        String row() {
            return String.join("\t", owner, method, desc,
                    Integer.toString(pass), Integer.toString(rawStart),
                    intValue(nodes[0]), longValue(nodes[1]), longValue(nodes[2]),
                    action, Boolean.toString(proven), reason);
        }
    }

    private static final class Entry {
        final String name;
        final byte[] bytes;
        final int method;
        final long time;
        final String comment;
        final byte[] extra;
        final boolean directory;

        Entry(ZipEntry entry, byte[] bytes) {
            this.name = entry.getName();
            this.bytes = bytes;
            this.method = entry.getMethod();
            this.time = entry.getTime();
            this.comment = entry.getComment();
            this.extra = entry.getExtra();
            this.directory = entry.isDirectory();
        }
    }

    private static final class ClassFailure {
        final String entry;
        final String stage;
        final String reason;

        ClassFailure(String entry, String stage, String reason) {
            this.entry = entry;
            this.stage = stage;
            this.reason = reason;
        }

        String row() {
            return tsv(entry) + '\t' + tsv(stage) + '\t' + tsv(reason);
        }
    }

    private static String tsv(String value) {
        if (value == null) return "";
        return value.replace('\t', ' ').replace('\r', ' ').replace('\n', ' ');
    }
}
