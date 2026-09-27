package unlegit.zkm;

import org.objectweb.asm.ClassReader;
import org.objectweb.asm.ClassWriter;
import org.objectweb.asm.ConstantDynamic;
import org.objectweb.asm.Handle;
import org.objectweb.asm.Opcodes;
import org.objectweb.asm.Type;
import org.objectweb.asm.tree.AbstractInsnNode;
import org.objectweb.asm.tree.AnnotationNode;
import org.objectweb.asm.tree.ClassNode;
import org.objectweb.asm.tree.FieldInsnNode;
import org.objectweb.asm.tree.FieldNode;
import org.objectweb.asm.tree.InvokeDynamicInsnNode;
import org.objectweb.asm.tree.LdcInsnNode;
import org.objectweb.asm.tree.LocalVariableNode;
import org.objectweb.asm.tree.MethodInsnNode;
import org.objectweb.asm.tree.MethodNode;
import org.objectweb.asm.tree.MultiANewArrayInsnNode;
import org.objectweb.asm.tree.TryCatchBlockNode;
import org.objectweb.asm.tree.TypeInsnNode;
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
import java.nio.channels.FileChannel;
import java.nio.charset.StandardCharsets;
import java.nio.file.AtomicMoveNotSupportedException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.StandardCopyOption;
import java.nio.file.StandardOpenOption;
import java.security.MessageDigest;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Comparator;
import java.util.Enumeration;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Set;
import java.util.zip.ZipEntry;
import java.util.zip.ZipFile;

/**
 * Last, fail-closed publication boundary for a fully deobfuscated archive.
 *
 * <p>The candidate is treated as staging data.  The destination is not opened
 * until every integrity and residue gate passes, all reports have been written,
 * and an exact candidate copy has been forced to disk.  Publication requires a
 * same-filesystem atomic move; lack of atomic-move support is an error rather
 * than permission to perform a non-atomic replacement.</p>
 *
 * <p>All inspection is ASM-only.  Input classes are never defined, loaded,
 * initialized, reflected on, or executed.</p>
 */
public final class ZkmAtomicPublicationGate {
    private static final String CIPHER = "javax/crypto/Cipher";
    private static final String STRING_INDY_DESC = "(IJ)Ljava/lang/String;";
    private static final String INTEGER_INDY_DESC = "(IJ)I";
    private static final String MEMBER_BSM_DESC =
            "(Ljava/lang/invoke/MethodHandles$Lookup;"
                    + "Ljava/lang/invoke/MutableCallSite;Ljava/lang/String;"
                    + "Ljava/lang/invoke/MethodType;JJ)"
                    + "Ljava/lang/invoke/MethodHandle;";
    private static final String STANDARD_BSM_DESC =
            "(Ljava/lang/invoke/MethodHandles$Lookup;Ljava/lang/String;"
                    + "Ljava/lang/invoke/MethodType;)Ljava/lang/invoke/CallSite;";
    private static final Set<String> FORBIDDEN_RUNTIME = Collections.unmodifiableSet(
            new LinkedHashSet<String>(Arrays.asList(
                    ObfRuntimeNames.STATE_INTERFACE,
                    ObfRuntimeNames.STATE,
                    ObfRuntimeNames.GRAPH_BOOTSTRAP,
                    ObfRuntimeNames.STRING_PAIR_CONSTANTS)));
    private static final Set<String> SUPPORT_DESCRIPTORS = Collections.unmodifiableSet(
            new HashSet<String>(Arrays.asList(
                    STRING_INDY_DESC,
                    INTEGER_INDY_DESC,
                    "(JJ)I",
                    "(JJ)Ljava/lang/reflect/Field;",
                    "(JJ)Ljava/lang/reflect/Method;",
                    STANDARD_BSM_DESC,
                    MEMBER_BSM_DESC,
                    "(Ljava/lang/invoke/MethodHandles$Lookup;"
                            + "Ljava/lang/invoke/MutableCallSite;Ljava/lang/String;"
                            + "Ljava/lang/invoke/MethodType;[Ljava/lang/Object;)"
                            + "Ljava/lang/Object;",
                    "(Ljava/lang/invoke/MethodHandles$Lookup;"
                            + "Ljava/lang/invoke/MutableCallSite;Ljava/lang/String;"
                            + "[Ljava/lang/Object;)Ljava/lang/Object;",
                    "(Ljava/lang/invoke/MethodHandles$Lookup;"
                            + "Ljava/lang/invoke/MutableCallSite;Ljava/lang/String;"
                            + "[Ljava/lang/Object;)I")));

    private ZkmAtomicPublicationGate() {
    }

    public static void main(String[] args) throws Exception {
        if (args.length != 3) {
            System.err.println("usage: ZkmAtomicPublicationGate <candidate.jar>"
                    + " <report-dir> <final.jar>");
            System.exit(2);
        }
        Summary summary = publish(Paths.get(args[0]), Paths.get(args[1]),
                Paths.get(args[2]));
        System.out.println("integrity=" + pass(summary.integrityPass)
                + " des=" + summary.desResidues()
                + " runtime=" + summary.runtimeDefinitions
                + " indy=" + summary.zkmIndySites
                + " references=" + summary.unresolvedReferences()
                + " bootstrap_families=" + summary.bootstrapSupportFamilies
                + " published=" + summary.published);
        if (!summary.published) System.exit(1);
    }

    /**
     * Publishes {@code candidate} only when the complete fail-closed gate passes.
     * A returned non-published summary is an ordinary coverage failure.  An I/O
     * exception is propagated, but the destination has not been touched unless
     * the final atomic move completed successfully.
     */
    public static Summary publish(Path candidate, Path reportDirectory, Path destination)
            throws Exception {
        return publish(candidate, reportDirectory, destination,
                new AtomicMover() {
                    @Override
                    public void move(Path source, Path target) throws IOException {
                        try {
                            Files.move(source, target, StandardCopyOption.ATOMIC_MOVE,
                                    StandardCopyOption.REPLACE_EXISTING);
                        } catch (AtomicMoveNotSupportedException unsupported) {
                            throw new IOException("atomic publication is not supported for "
                                    + target, unsupported);
                        }
                    }
                });
    }

    /** Evaluates the complete fail-closed gate without publishing an archive. */
    static Summary audit(Path candidate, Path reportDirectory) throws Exception {
        if (candidate == null || reportDirectory == null) {
            throw new IllegalArgumentException("candidate and reportDirectory are required");
        }
        Path source = candidate.toAbsolutePath().normalize();
        Path report = reportDirectory.toAbsolutePath().normalize();
        if (!Files.isRegularFile(source)) {
            throw new IOException("candidate is not a regular file: " + source);
        }
        if (source.equals(report)) {
            throw new IllegalArgumentException("report directory aliases candidate");
        }
        Files.createDirectories(report);
        return evaluate(source, report, null);
    }

    static Summary publish(Path candidate, Path reportDirectory, Path destination,
                           AtomicMover mover) throws Exception {
        if (candidate == null || reportDirectory == null || destination == null
                || mover == null) {
            throw new IllegalArgumentException(
                    "candidate, reportDirectory, destination and mover are required");
        }
        Path source = candidate.toAbsolutePath().normalize();
        Path report = reportDirectory.toAbsolutePath().normalize();
        Path target = destination.toAbsolutePath().normalize();
        validatePaths(source, report, target);
        Files.createDirectories(report);
        Summary summary = evaluate(source, report, target);
        if (!summary.eligible) return summary;

        Path parent = target.getParent();
        if (parent == null) throw new IOException("destination has no parent: " + target);
        Files.createDirectories(parent);
        Path temporary = Files.createTempFile(parent,
                "." + target.getFileName().toString() + ".", ".tmp");
        boolean moved = false;
        try {
            Files.copy(source, temporary, StandardCopyOption.REPLACE_EXISTING);
            try (FileChannel channel = FileChannel.open(temporary, StandardOpenOption.WRITE)) {
                channel.force(true);
            }
            if (Files.size(source) != Files.size(temporary)
                    || !summary.candidateSha256.equals(sha256(temporary))) {
                throw new IOException("staged publication copy differs from candidate");
            }
            Files.write(report.resolve("publication.txt"), Arrays.asList(
                    "status=READY", "destination=" + target,
                    "sha256=" + summary.candidateSha256), StandardCharsets.UTF_8);
            mover.move(temporary, target);
            if (Files.exists(temporary) || !Files.isRegularFile(target)
                    || Files.size(source) != Files.size(target)
                    || !summary.candidateSha256.equals(sha256(target))) {
                throw new IOException("atomic mover did not commit the exact candidate");
            }
            moved = true;
            summary.published = true;
            writePublicationBestEffort(report, Arrays.asList(
                    "status=COMMITTED", "destination=" + target,
                    "sha256=" + summary.candidateSha256));
            return summary;
        } catch (IOException failure) {
            writePublicationBestEffort(report, Arrays.asList(
                    "status=FAILED", "destination=" + target,
                    "reason=" + shortReason(failure)));
            throw failure;
        } finally {
            if (!moved) {
                try {
                    Files.deleteIfExists(temporary);
                } catch (IOException ignored) {
                    // Preserve the publication failure; a temp file cannot replace target.
                }
            }
        }
    }

    private static void writePublicationBestEffort(Path report, List<String> lines) {
        try {
            Files.write(report.resolve("publication.txt"), lines, StandardCharsets.UTF_8);
        } catch (IOException ignored) {
            // Eligibility reports were durably written before publication.
        }
    }

    private static Summary evaluate(Path source, Path report, Path target)
            throws Exception {
        ScanResult scan = scan(source);
        Summary summary = scan.summary;
        summary.candidate = source.toString();
        summary.destination = target == null ? "" : target.toString();

        if (summary.baseIntegrityPass()) {
            try {
                ZkmBootstrapSupportCleaner.Summary bootstrap =
                        ZkmBootstrapSupportCleaner.clean(source,
                                report.resolve("bootstrap-support"), null);
                summary.bootstrapAuditAttempted = true;
                summary.bootstrapSupportFamilies = bootstrap.candidateFamilies;
                summary.bootstrapLiveReferences = bootstrap.liveBootstrapReferences;
                summary.bootstrapReferenceBlockedFamilies =
                        bootstrap.referenceBlockedFamilies;
                summary.bootstrapAuditErrors = bootstrap.classRollbacks
                        + bootstrap.outputVerificationErrors;
            } catch (Exception failure) {
                summary.bootstrapAuditAttempted = true;
                summary.bootstrapAuditErrors++;
                scan.sites.add(new Site("<archive>", "<bootstrap-audit>", -1,
                        "BOOTSTRAP_AUDIT_ERROR", shortReason(failure)));
            }
        }
        summary.finish();
        writeReports(report, summary, scan.sites);
        return summary;
    }

    private static void validatePaths(Path candidate, Path report, Path destination)
            throws IOException {
        if (!Files.isRegularFile(candidate)) {
            throw new IOException("candidate is not a regular file: " + candidate);
        }
        if (candidate.equals(destination)
                || Files.exists(destination) && Files.isSameFile(candidate, destination)) {
            throw new IllegalArgumentException(
                    "candidate and destination must be different files");
        }
        if (candidate.equals(report)) {
            throw new IllegalArgumentException("report directory aliases candidate");
        }
    }

    private static ScanResult scan(Path archive) throws Exception {
        Summary summary = new Summary();
        summary.candidateSha256 = sha256(archive);
        List<Site> sites = new ArrayList<>();
        List<ParsedClass> classes = new ArrayList<>();
        Set<String> entryNames = new HashSet<>();
        Set<String> classNames = new HashSet<>();

        try (ZipFile zip = new ZipFile(archive.toFile())) {
            Enumeration<? extends ZipEntry> entries = zip.entries();
            while (entries.hasMoreElements()) {
                ZipEntry entry = entries.nextElement();
                summary.archiveEntries++;
                if (!entryNames.add(entry.getName())) {
                    summary.duplicateEntries++;
                    sites.add(new Site("<archive>", entry.getName(), -1,
                            "DUPLICATE_ENTRY", entry.getName()));
                }
                if (entry.isDirectory() || !entry.getName().endsWith(".class")) continue;
                summary.classEntries++;
                byte[] bytes;
                try (InputStream input = zip.getInputStream(entry)) {
                    bytes = readAll(input);
                }
                try {
                    ClassNode owner = new ClassNode(Opcodes.ASM9);
                    new ClassReader(bytes).accept(owner, 0);
                    summary.parsedClasses++;
                    if (!classNames.add(owner.name)) {
                        summary.duplicateClasses++;
                        sites.add(new Site(owner.name, "<class>", -1,
                                "DUPLICATE_CLASS", entry.getName()));
                    }
                    if (!entryMatchesClass(entry.getName(), owner.name)) {
                        summary.entryNameMismatches++;
                        sites.add(new Site(owner.name, "<class>", -1,
                                "ENTRY_NAME_MISMATCH", entry.getName()));
                    }
                    try {
                        verifyClass(bytes, owner);
                    } catch (Throwable failure) {
                        summary.verificationErrors++;
                        sites.add(new Site(owner.name, "<class>", -1,
                                "CLASS_VERIFICATION_ERROR", shortReason(failure)));
                    }
                    classes.add(new ParsedClass(entry.getName(), owner));
                } catch (Throwable failure) {
                    summary.malformedClasses++;
                    sites.add(new Site("<unknown>", entry.getName(), -1,
                            "MALFORMED_CLASS", shortReason(failure)));
                }
            }
        }
        if (summary.archiveEntries == 0 || summary.classEntries == 0) {
            summary.archiveErrors++;
            sites.add(new Site("<archive>", "<entries>", -1,
                    "EMPTY_ARCHIVE", "entries=" + summary.archiveEntries
                            + ",classes=" + summary.classEntries));
        }

        Map<FieldRef, String> constantStrings = constantStringFields(classes);
        Set<MethodRef> supportMethods = supportMethods(classes);
        for (ParsedClass parsed : classes) {
            inspectClass(parsed.node, constantStrings, supportMethods, summary, sites);
        }
        return new ScanResult(summary, sites);
    }

    private static void inspectClass(ClassNode owner, Map<FieldRef, String> constants,
                                     Set<MethodRef> supportMethods, Summary summary,
                                     List<Site> sites) {
        if (isForbiddenRuntimeClass(owner.name)) {
            summary.runtimeDefinitions++;
            sites.add(new Site(owner.name, "<class>", -1,
                    "FORBIDDEN_RUNTIME_DEFINITION", owner.name));
        }
        checkReference(owner, "<class>", -1, RuntimeReferenceKind.METADATA,
                summary, sites,
                owner.superName, owner.signature, owner.outerClass, owner.outerMethodDesc,
                owner.nestHostClass, owner.interfaces, owner.nestMembers,
                owner.permittedSubclasses);
        inspectAnnotations(owner, "<class>", -1, summary, sites,
                owner.visibleAnnotations, owner.invisibleAnnotations,
                owner.visibleTypeAnnotations, owner.invisibleTypeAnnotations);

        for (FieldNode field : owner.fields) {
            String location = field.name + field.desc;
            checkReference(owner, location, -1, RuntimeReferenceKind.DESCRIPTOR,
                    summary, sites, field.desc, field.signature);
            checkReference(owner, location, -1, RuntimeReferenceKind.LITERAL,
                    summary, sites, field.value);
            checkDesConstant(owner, location, -1, field.value, summary, sites);
            inspectAnnotations(owner, location, -1, summary, sites,
                    field.visibleAnnotations, field.invisibleAnnotations,
                    field.visibleTypeAnnotations, field.invisibleTypeAnnotations);
        }

        for (MethodNode method : owner.methods) {
            String location = method.name + method.desc;
            checkReference(owner, location, -1, RuntimeReferenceKind.DESCRIPTOR,
                    summary, sites,
                    method.desc, method.signature, method.exceptions);
            inspectAnnotations(owner, location, -1, summary, sites,
                    method.visibleAnnotations, method.invisibleAnnotations,
                    method.visibleTypeAnnotations, method.invisibleTypeAnnotations);
            if (method.visibleParameterAnnotations != null) {
                for (List<AnnotationNode> annotations : method.visibleParameterAnnotations) {
                    inspectAnnotations(owner, location, -1, summary, sites, annotations);
                }
            }
            if (method.invisibleParameterAnnotations != null) {
                for (List<AnnotationNode> annotations : method.invisibleParameterAnnotations) {
                    inspectAnnotations(owner, location, -1, summary, sites, annotations);
                }
            }
            for (TryCatchBlockNode block : method.tryCatchBlocks) {
                checkReference(owner, location, -1, RuntimeReferenceKind.OWNER,
                        summary, sites, block.type);
                inspectAnnotations(owner, location, -1, summary, sites,
                        block.visibleTypeAnnotations, block.invisibleTypeAnnotations);
            }
            if (method.localVariables != null) {
                for (LocalVariableNode local : method.localVariables) {
                    checkReference(owner, location, -1, RuntimeReferenceKind.DESCRIPTOR,
                            summary, sites,
                            local.desc, local.signature);
                }
            }

            Frame<SourceValue>[] sourceFrames = null;
            try {
                sourceFrames = new Analyzer<SourceValue>(new SourceInterpreter())
                        .analyze(owner.name, method);
            } catch (Throwable ignored) {
                // An unresolved factory below is fail-closed when provenance is unavailable.
            }
            int index = 0;
            for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
                 insn = insn.getNext(), index++) {
                if (insn instanceof MethodInsnNode) {
                    MethodInsnNode call = (MethodInsnNode) insn;
                    checkReference(owner, location, index, RuntimeReferenceKind.OWNER,
                            summary, sites, call.owner);
                    checkReference(owner, location, index, RuntimeReferenceKind.DESCRIPTOR,
                            summary, sites, call.desc);
                    MethodRef target = new MethodRef(call.owner, call.name, call.desc);
                    if (supportMethods.contains(target)) {
                        summary.zkmSupportReferences++;
                        sites.add(new Site(owner.name, location, index,
                                "ZKM_SUPPORT_REFERENCE", target.toString()));
                    }
                    if (isCipherFactory(call)) {
                        AlgorithmKind algorithm = algorithmKind(method, index, call,
                                sourceFrames, constants);
                        if (algorithm == AlgorithmKind.DES) {
                            summary.desCipherFactories++;
                            sites.add(new Site(owner.name, location, index,
                                    "DES_CIPHER_FACTORY", call.owner + "." + call.name
                                            + call.desc));
                        } else if (algorithm == AlgorithmKind.UNKNOWN) {
                            summary.unresolvedCipherFactories++;
                            sites.add(new Site(owner.name, location, index,
                                    "UNRESOLVED_CIPHER_FACTORY",
                                    "algorithm provenance is not a proven non-DES literal"));
                        }
                    }
                } else if (insn instanceof FieldInsnNode) {
                    FieldInsnNode field = (FieldInsnNode) insn;
                    checkReference(owner, location, index, RuntimeReferenceKind.OWNER,
                            summary, sites, field.owner);
                    checkReference(owner, location, index, RuntimeReferenceKind.DESCRIPTOR,
                            summary, sites, field.desc);
                } else if (insn instanceof TypeInsnNode) {
                    checkReference(owner, location, index, RuntimeReferenceKind.OWNER,
                            summary, sites,
                            ((TypeInsnNode) insn).desc);
                } else if (insn instanceof MultiANewArrayInsnNode) {
                    checkReference(owner, location, index, RuntimeReferenceKind.DESCRIPTOR,
                            summary, sites,
                            ((MultiANewArrayInsnNode) insn).desc);
                } else if (insn instanceof LdcInsnNode) {
                    Object value = ((LdcInsnNode) insn).cst;
                    checkReference(owner, location, index,
                            containsHandle(value) ? RuntimeReferenceKind.HANDLE
                                    : RuntimeReferenceKind.LITERAL,
                            summary, sites, value);
                    checkDesConstant(owner, location, index, value, summary, sites);
                    if (referencesSupport(value, supportMethods)) {
                        summary.zkmSupportReferences++;
                        sites.add(new Site(owner.name, location, index,
                                "ZKM_SUPPORT_REFERENCE", String.valueOf(value)));
                    }
                } else if (insn instanceof InvokeDynamicInsnNode) {
                    InvokeDynamicInsnNode indy = (InvokeDynamicInsnNode) insn;
                    checkReference(owner, location, index, RuntimeReferenceKind.INDY,
                            summary, sites,
                            indy.desc, indy.bsm, indy.bsmArgs);
                    checkDesConstant(owner, location, index, indy.bsmArgs, summary, sites);
                    if (isZkmIndy(indy)) {
                        summary.zkmIndySites++;
                        sites.add(new Site(owner.name, location, index,
                                "ZKM_INDY", indy.name + indy.desc + ",bsm=" + indy.bsm));
                    }
                    if (referencesSupport(indy.bsm, supportMethods)
                            || referencesSupport(indy.bsmArgs, supportMethods)) {
                        summary.zkmSupportReferences++;
                        sites.add(new Site(owner.name, location, index,
                                "ZKM_SUPPORT_REFERENCE", "indy=" + indy.name + indy.desc));
                    }
                }
            }
        }
    }

    @SafeVarargs
    private static void inspectAnnotations(ClassNode owner, String location, int index,
                                           Summary summary, List<Site> sites,
                                           List<? extends AnnotationNode>... groups) {
        if (groups == null) return;
        for (List<? extends AnnotationNode> group : groups) {
            if (group == null) continue;
            for (AnnotationNode annotation : group) {
                checkReference(owner, location, index, RuntimeReferenceKind.DESCRIPTOR,
                        summary, sites,
                        annotation.desc, annotation.values);
                checkDesConstant(owner, location, index, annotation.values, summary, sites);
            }
        }
    }

    private static void checkReference(ClassNode owner, String location, int index,
                                       RuntimeReferenceKind kind, Summary summary,
                                       List<Site> sites,
                                       Object... values) {
        // References wholly inside a forbidden runtime definition disappear with that
        // definition.  The closure gate needs the external consumers that would dangle.
        if (isForbiddenRuntimeClass(owner.name)) return;
        String forbidden = forbiddenReference(values);
        if (forbidden == null) return;
        summary.runtimeReferences++;
        summary.countRuntimeReference(kind);
        sites.add(new Site(owner.name, location, index,
                "FORBIDDEN_RUNTIME_" + kind.name() + "_REFERENCE", forbidden));
    }

    private static String forbiddenReference(Object value) {
        if (value == null) return null;
        if (value instanceof Object[]) {
            for (Object element : (Object[]) value) {
                String result = forbiddenReference(element);
                if (result != null) return result;
            }
            return null;
        }
        if (value instanceof Iterable<?>) {
            for (Object element : (Iterable<?>) value) {
                String result = forbiddenReference(element);
                if (result != null) return result;
            }
            return null;
        }
        if (value instanceof Type) return forbiddenReference(((Type) value).getDescriptor());
        if (value instanceof Handle) {
            Handle handle = (Handle) value;
            return forbiddenReference(new Object[]{handle.getOwner(), handle.getDesc()});
        }
        if (value instanceof ConstantDynamic) {
            ConstantDynamic dynamic = (ConstantDynamic) value;
            Object[] nested = new Object[dynamic.getBootstrapMethodArgumentCount() + 2];
            nested[0] = dynamic.getDescriptor();
            nested[1] = dynamic.getBootstrapMethod();
            for (int i = 0; i < dynamic.getBootstrapMethodArgumentCount(); i++) {
                nested[i + 2] = dynamic.getBootstrapMethodArgument(i);
            }
            return forbiddenReference(nested);
        }
        String text = String.valueOf(value);
        for (String name : FORBIDDEN_RUNTIME) {
            String dotted = name.replace('/', '.');
            if (text.contains(name) || text.contains(dotted)) return name;
        }
        return null;
    }

    private static boolean isForbiddenRuntimeClass(String owner) {
        return owner != null && FORBIDDEN_RUNTIME.contains(owner);
    }

    private static boolean containsHandle(Object value) {
        if (value == null) return false;
        if (value instanceof Handle) return true;
        if (value instanceof Object[]) {
            for (Object element : (Object[]) value) if (containsHandle(element)) return true;
            return false;
        }
        if (value instanceof Iterable<?>) {
            for (Object element : (Iterable<?>) value) if (containsHandle(element)) return true;
            return false;
        }
        if (value instanceof ConstantDynamic) {
            ConstantDynamic dynamic = (ConstantDynamic) value;
            if (containsHandle(dynamic.getBootstrapMethod())) return true;
            for (int i = 0; i < dynamic.getBootstrapMethodArgumentCount(); i++) {
                if (containsHandle(dynamic.getBootstrapMethodArgument(i))) return true;
            }
        }
        return false;
    }

    private static void checkDesConstant(ClassNode owner, String location, int index,
                                         Object value, Summary summary, List<Site> sites) {
        String transformation = desTransformation(value);
        if (transformation == null) return;
        summary.desTransformationLiterals++;
        sites.add(new Site(owner.name, location, index,
                "DES_TRANSFORMATION_LITERAL", transformation));
    }

    private static String desTransformation(Object value) {
        if (value == null) return null;
        if (value instanceof Object[]) {
            for (Object element : (Object[]) value) {
                String result = desTransformation(element);
                if (result != null) return result;
            }
            return null;
        }
        if (value instanceof Iterable<?>) {
            for (Object element : (Iterable<?>) value) {
                String result = desTransformation(element);
                if (result != null) return result;
            }
            return null;
        }
        if (value instanceof ConstantDynamic) {
            ConstantDynamic dynamic = (ConstantDynamic) value;
            for (int i = 0; i < dynamic.getBootstrapMethodArgumentCount(); i++) {
                String result = desTransformation(dynamic.getBootstrapMethodArgument(i));
                if (result != null) return result;
            }
            return null;
        }
        if (!(value instanceof String)) return null;
        String text = ((String) value).trim();
        String upper = text.toUpperCase(Locale.ROOT);
        return upper.equals("DES") || upper.startsWith("DES/") ? text : null;
    }

    private static AlgorithmKind algorithmKind(MethodNode method, int instruction,
                                               MethodInsnNode call,
                                               Frame<SourceValue>[] frames,
                                               Map<FieldRef, String> constants) {
        if (frames == null || instruction < 0 || instruction >= frames.length
                || frames[instruction] == null) {
            return precedingAlgorithm(call, constants);
        }
        Frame<SourceValue> frame = frames[instruction];
        Type[] arguments = Type.getArgumentTypes(call.desc);
        int stack = frame.getStackSize() - arguments.length;
        if (stack < 0 || stack >= frame.getStackSize()) return AlgorithmKind.UNKNOWN;
        SourceValue source = frame.getStack(stack);
        if (source == null || source.insns == null || source.insns.isEmpty()) {
            return AlgorithmKind.UNKNOWN;
        }
        boolean known = false;
        boolean unknown = false;
        for (AbstractInsnNode producer : source.insns) {
            String value = null;
            if (producer instanceof LdcInsnNode
                    && ((LdcInsnNode) producer).cst instanceof String) {
                value = (String) ((LdcInsnNode) producer).cst;
            } else if (producer instanceof FieldInsnNode
                    && producer.getOpcode() == Opcodes.GETSTATIC) {
                FieldInsnNode field = (FieldInsnNode) producer;
                value = constants.get(new FieldRef(field.owner, field.name, field.desc));
            }
            if (value == null) {
                unknown = true;
            } else {
                known = true;
                if (desTransformation(value) != null) return AlgorithmKind.DES;
            }
        }
        return known && !unknown ? AlgorithmKind.PROVEN_NON_DES : AlgorithmKind.UNKNOWN;
    }

    private static AlgorithmKind precedingAlgorithm(MethodInsnNode call,
                                                     Map<FieldRef, String> constants) {
        AbstractInsnNode previous = previousCode(call);
        if (previous instanceof LdcInsnNode
                && ((LdcInsnNode) previous).cst instanceof String) {
            return desTransformation(((LdcInsnNode) previous).cst) == null
                    ? AlgorithmKind.PROVEN_NON_DES : AlgorithmKind.DES;
        }
        if (previous instanceof FieldInsnNode && previous.getOpcode() == Opcodes.GETSTATIC) {
            FieldInsnNode field = (FieldInsnNode) previous;
            String value = constants.get(new FieldRef(field.owner, field.name, field.desc));
            if (value != null) {
                return desTransformation(value) == null
                        ? AlgorithmKind.PROVEN_NON_DES : AlgorithmKind.DES;
            }
        }
        return AlgorithmKind.UNKNOWN;
    }

    private static boolean isCipherFactory(MethodInsnNode call) {
        if (call.getOpcode() != Opcodes.INVOKESTATIC || !CIPHER.equals(call.owner)
                || !"getInstance".equals(call.name)) return false;
        Type[] arguments = Type.getArgumentTypes(call.desc);
        return arguments.length >= 1
                && Type.getType(String.class).equals(arguments[0])
                && Type.getObjectType(CIPHER).equals(Type.getReturnType(call.desc));
    }

    private static boolean isZkmIndy(InvokeDynamicInsnNode indy) {
        if (STRING_INDY_DESC.equals(indy.desc) || INTEGER_INDY_DESC.equals(indy.desc)) {
            return true;
        }
        Type[] arguments = Type.getArgumentTypes(indy.desc);
        return arguments.length >= 2
                && Type.LONG_TYPE.equals(arguments[arguments.length - 1])
                && Type.LONG_TYPE.equals(arguments[arguments.length - 2])
                && indy.bsm != null && indy.bsm.getTag() == Opcodes.H_INVOKESTATIC
                && MEMBER_BSM_DESC.equals(indy.bsm.getDesc());
    }

    private static Set<MethodRef> supportMethods(List<ParsedClass> classes) {
        Set<MethodRef> result = new LinkedHashSet<>();
        for (ParsedClass parsed : classes) {
            ClassNode owner = parsed.node;
            boolean supportOwner = false;
            for (MethodNode method : owner.methods) {
                if (!isPrivateStatic(method.access)) continue;
                if (STANDARD_BSM_DESC.equals(method.desc)
                        || MEMBER_BSM_DESC.equals(method.desc)) supportOwner = true;
                if (containsCipherFactory(method)) supportOwner = true;
            }
            if (!supportOwner) continue;
            for (MethodNode method : owner.methods) {
                if (isPrivateStatic(method.access)
                        && SUPPORT_DESCRIPTORS.contains(method.desc)) {
                    result.add(new MethodRef(owner.name, method.name, method.desc));
                }
            }
        }
        return result;
    }

    private static boolean isPrivateStatic(int access) {
        return (access & (Opcodes.ACC_PRIVATE | Opcodes.ACC_STATIC))
                == (Opcodes.ACC_PRIVATE | Opcodes.ACC_STATIC);
    }

    private static boolean containsCipherFactory(MethodNode method) {
        for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
             insn = insn.getNext()) {
            if (insn instanceof MethodInsnNode && isCipherFactory((MethodInsnNode) insn)) {
                return true;
            }
        }
        return false;
    }

    private static boolean referencesSupport(Object value, Set<MethodRef> supportMethods) {
        if (value == null) return false;
        if (value instanceof Object[]) {
            for (Object element : (Object[]) value) {
                if (referencesSupport(element, supportMethods)) return true;
            }
            return false;
        }
        if (value instanceof Iterable<?>) {
            for (Object element : (Iterable<?>) value) {
                if (referencesSupport(element, supportMethods)) return true;
            }
            return false;
        }
        if (value instanceof Handle) {
            Handle handle = (Handle) value;
            return supportMethods.contains(new MethodRef(handle.getOwner(), handle.getName(),
                    handle.getDesc()));
        }
        if (value instanceof ConstantDynamic) {
            ConstantDynamic dynamic = (ConstantDynamic) value;
            if (referencesSupport(dynamic.getBootstrapMethod(), supportMethods)) return true;
            for (int i = 0; i < dynamic.getBootstrapMethodArgumentCount(); i++) {
                if (referencesSupport(dynamic.getBootstrapMethodArgument(i), supportMethods)) {
                    return true;
                }
            }
        }
        return false;
    }

    private static Map<FieldRef, String> constantStringFields(List<ParsedClass> classes) {
        Map<FieldRef, String> result = new HashMap<>();
        for (ParsedClass parsed : classes) {
            for (FieldNode field : parsed.node.fields) {
                if (field.value instanceof String && "Ljava/lang/String;".equals(field.desc)) {
                    result.put(new FieldRef(parsed.node.name, field.name, field.desc),
                            (String) field.value);
                }
            }
        }
        return result;
    }

    private static boolean entryMatchesClass(String entry, String owner) {
        String prefix = "META-INF/versions/";
        if (entry.startsWith(prefix)) {
            int slash = entry.indexOf('/', prefix.length());
            if (slash >= 0) entry = entry.substring(slash + 1);
        }
        return (owner + ".class").equals(entry);
    }

    private static void verifyClass(byte[] bytes, ClassNode owner) throws Exception {
        new ClassReader(bytes).accept(
                new CheckClassAdapter(new ClassWriter(0), false), 0);
        for (MethodNode method : owner.methods) {
            if (method.instructions != null && method.instructions.size() != 0) {
                new Analyzer<BasicValue>(new BasicVerifier()).analyze(owner.name, method);
            }
        }
    }

    private static void writeReports(Path report, Summary summary, List<Site> sites)
            throws IOException {
        List<Site> ordered = new ArrayList<>(sites);
        Collections.sort(ordered, new Comparator<Site>() {
            @Override public int compare(Site left, Site right) {
                return left.key().compareTo(right.key());
            }
        });
        List<String> rows = new ArrayList<>();
        rows.add("class\tmethod\tinstruction\ttype\tdetail");
        for (Site site : ordered) rows.add(site.row());
        Files.write(report.resolve("sites.tsv"), rows, StandardCharsets.UTF_8);

        List<String> audit = new ArrayList<>();
        audit.add("candidate=" + summary.candidate);
        audit.add("candidate_sha256=" + summary.candidateSha256);
        audit.add("destination=" + summary.destination);
        audit.add("archive_entries=" + summary.archiveEntries);
        audit.add("class_entries=" + summary.classEntries);
        audit.add("parsed_classes=" + summary.parsedClasses);
        audit.add("malformed_classes=" + summary.malformedClasses);
        audit.add("class_verification_errors=" + summary.verificationErrors);
        audit.add("archive_errors=" + summary.archiveErrors);
        audit.add("duplicate_entries=" + summary.duplicateEntries);
        audit.add("duplicate_classes=" + summary.duplicateClasses);
        audit.add("entry_name_mismatches=" + summary.entryNameMismatches);
        audit.add("des_transformation_literals=" + summary.desTransformationLiterals);
        audit.add("des_cipher_factories=" + summary.desCipherFactories);
        audit.add("unresolved_cipher_factories=" + summary.unresolvedCipherFactories);
        audit.add("forbidden_runtime_definitions=" + summary.runtimeDefinitions);
        audit.add("forbidden_runtime_references=" + summary.runtimeReferences);
        audit.add("runtime_owner_references=" + summary.runtimeOwnerReferences);
        audit.add("runtime_descriptor_references=" + summary.runtimeDescriptorReferences);
        audit.add("runtime_handle_references=" + summary.runtimeHandleReferences);
        audit.add("runtime_indy_references=" + summary.runtimeIndyReferences);
        audit.add("runtime_metadata_references=" + summary.runtimeMetadataReferences);
        audit.add("runtime_literal_references=" + summary.runtimeLiteralReferences);
        audit.add("zkm_indy_sites=" + summary.zkmIndySites);
        audit.add("zkm_support_references=" + summary.zkmSupportReferences);
        audit.add("bootstrap_audit_attempted=" + summary.bootstrapAuditAttempted);
        audit.add("bootstrap_support_families=" + summary.bootstrapSupportFamilies);
        audit.add("bootstrap_live_references=" + summary.bootstrapLiveReferences);
        audit.add("bootstrap_reference_blocked_families="
                + summary.bootstrapReferenceBlockedFamilies);
        audit.add("bootstrap_audit_errors=" + summary.bootstrapAuditErrors);
        audit.add("input_classes_loaded=false");
        audit.add("input_classes_initialized=false");
        audit.add("atomic_move_required=true");
        audit.add("publication_eligible=" + summary.eligible);
        audit.add("gate=" + pass(summary.eligible));
        Files.write(report.resolve("audit.txt"), audit, StandardCharsets.UTF_8);

        List<String> gates = new ArrayList<>();
        gates.add("gate\tstatus\tresidue");
        gates.add("integrity\t" + pass(summary.integrityPass) + "\t"
                + summary.integrityResidues());
        gates.add("des\t" + pass(summary.desResidues() == 0) + "\t"
                + summary.desResidues());
        gates.add("runtime\t" + pass(summary.runtimeDefinitions == 0) + "\t"
                + summary.runtimeDefinitions);
        gates.add("indy\t" + pass(summary.zkmIndySites == 0) + "\t"
                + summary.zkmIndySites);
        gates.add("references\t" + pass(summary.unresolvedReferences() == 0) + "\t"
                + summary.unresolvedReferences());
        gates.add("bootstrap_support\t"
                + pass(summary.bootstrapSupportFamilies == 0) + "\t"
                + summary.bootstrapSupportFamilies);
        gates.add("overall\t" + pass(summary.eligible) + "\t"
                + (summary.eligible ? 0 : 1));
        Files.write(report.resolve("gates.tsv"), gates, StandardCharsets.UTF_8);
        Files.write(report.resolve("gate.txt"),
                Collections.singletonList(pass(summary.eligible)), StandardCharsets.UTF_8);
    }

    private static String pass(boolean value) {
        return value ? "PASS" : "FAIL";
    }

    private static AbstractInsnNode previousCode(AbstractInsnNode insn) {
        AbstractInsnNode previous = insn.getPrevious();
        while (previous != null && previous.getOpcode() < 0) previous = previous.getPrevious();
        return previous;
    }

    private static String sha256(Path path) throws Exception {
        MessageDigest digest = MessageDigest.getInstance("SHA-256");
        try (InputStream input = Files.newInputStream(path)) {
            byte[] buffer = new byte[8192];
            int count;
            while ((count = input.read(buffer)) >= 0) {
                if (count != 0) digest.update(buffer, 0, count);
            }
        }
        StringBuilder result = new StringBuilder();
        for (byte value : digest.digest()) {
            result.append(String.format(Locale.ROOT, "%02X", value & 0xff));
        }
        return result.toString();
    }

    private static byte[] readAll(InputStream input) throws IOException {
        ByteArrayOutputStream output = new ByteArrayOutputStream();
        byte[] buffer = new byte[8192];
        int count;
        while ((count = input.read(buffer)) >= 0) {
            if (count != 0) output.write(buffer, 0, count);
        }
        return output.toByteArray();
    }

    private static String shortReason(Throwable failure) {
        String reason = failure.getClass().getSimpleName() + ":"
                + String.valueOf(failure.getMessage());
        reason = reason.replace('\t', ' ').replace('\r', ' ').replace('\n', ' ');
        return reason.substring(0, Math.min(reason.length(), 240));
    }

    interface AtomicMover {
        void move(Path source, Path target) throws IOException;
    }

    static final class Summary {
        String candidate;
        String candidateSha256;
        String destination;
        int archiveEntries;
        int classEntries;
        int parsedClasses;
        int malformedClasses;
        int verificationErrors;
        int archiveErrors;
        int duplicateEntries;
        int duplicateClasses;
        int entryNameMismatches;
        int desTransformationLiterals;
        int desCipherFactories;
        int unresolvedCipherFactories;
        int runtimeDefinitions;
        int runtimeReferences;
        int runtimeOwnerReferences;
        int runtimeDescriptorReferences;
        int runtimeHandleReferences;
        int runtimeIndyReferences;
        int runtimeMetadataReferences;
        int runtimeLiteralReferences;
        int zkmIndySites;
        int zkmSupportReferences;
        boolean bootstrapAuditAttempted;
        int bootstrapSupportFamilies;
        int bootstrapLiveReferences;
        int bootstrapReferenceBlockedFamilies;
        int bootstrapAuditErrors;
        boolean integrityPass;
        boolean eligible;
        boolean published;

        private boolean baseIntegrityPass() {
            return archiveErrors == 0 && duplicateEntries == 0 && duplicateClasses == 0
                    && entryNameMismatches == 0 && malformedClasses == 0
                    && verificationErrors == 0 && classEntries == parsedClasses;
        }

        private void finish() {
            integrityPass = baseIntegrityPass() && bootstrapAuditAttempted
                    && bootstrapAuditErrors == 0;
            eligible = integrityPass && desResidues() == 0 && runtimeDefinitions == 0
                    && zkmIndySites == 0 && unresolvedReferences() == 0
                    && bootstrapSupportFamilies == 0;
        }

        int integrityResidues() {
            return archiveErrors + duplicateEntries + duplicateClasses + entryNameMismatches
                    + malformedClasses + verificationErrors
                    + Math.abs(classEntries - parsedClasses) + bootstrapAuditErrors;
        }

        int desResidues() {
            return desTransformationLiterals + desCipherFactories
                    + unresolvedCipherFactories;
        }

        int unresolvedReferences() {
            return runtimeReferences + zkmSupportReferences + bootstrapLiveReferences
                    + bootstrapReferenceBlockedFamilies;
        }

        private void countRuntimeReference(RuntimeReferenceKind kind) {
            switch (kind) {
                case OWNER: runtimeOwnerReferences++; break;
                case DESCRIPTOR: runtimeDescriptorReferences++; break;
                case HANDLE: runtimeHandleReferences++; break;
                case INDY: runtimeIndyReferences++; break;
                case METADATA: runtimeMetadataReferences++; break;
                case LITERAL: runtimeLiteralReferences++; break;
                default: throw new AssertionError(kind);
            }
        }
    }

    private enum AlgorithmKind { DES, PROVEN_NON_DES, UNKNOWN }

    private enum RuntimeReferenceKind {
        OWNER, DESCRIPTOR, HANDLE, INDY, METADATA, LITERAL
    }

    private static final class ScanResult {
        final Summary summary;
        final List<Site> sites;

        ScanResult(Summary summary, List<Site> sites) {
            this.summary = summary;
            this.sites = sites;
        }
    }

    private static final class ParsedClass {
        final String entry;
        final ClassNode node;

        ParsedClass(String entry, ClassNode node) {
            this.entry = entry;
            this.node = node;
        }
    }

    private static final class Site {
        final String owner;
        final String method;
        final int instruction;
        final String type;
        final String detail;

        Site(String owner, String method, int instruction, String type, String detail) {
            this.owner = owner;
            this.method = method;
            this.instruction = instruction;
            this.type = type;
            this.detail = detail;
        }

        String key() {
            return owner + "\t" + method + "\t" + String.format(Locale.ROOT, "%09d",
                    instruction) + "\t" + type + "\t" + detail;
        }

        String row() {
            return sanitize(owner) + "\t" + sanitize(method) + "\t" + instruction + "\t"
                    + sanitize(type) + "\t" + sanitize(detail);
        }

        private static String sanitize(String value) {
            return value.replace('\t', ' ').replace('\r', ' ').replace('\n', ' ');
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

        @Override public boolean equals(Object other) {
            if (!(other instanceof MethodRef)) return false;
            MethodRef value = (MethodRef) other;
            return owner.equals(value.owner) && name.equals(value.name)
                    && desc.equals(value.desc);
        }

        @Override public int hashCode() {
            return (owner.hashCode() * 31 + name.hashCode()) * 31 + desc.hashCode();
        }

        @Override public String toString() {
            return owner + "." + name + desc;
        }
    }

    private static final class FieldRef {
        final String owner;
        final String name;
        final String desc;

        FieldRef(String owner, String name, String desc) {
            this.owner = owner;
            this.name = name;
            this.desc = desc;
        }

        @Override public boolean equals(Object other) {
            if (!(other instanceof FieldRef)) return false;
            FieldRef value = (FieldRef) other;
            return owner.equals(value.owner) && name.equals(value.name)
                    && desc.equals(value.desc);
        }

        @Override public int hashCode() {
            return (owner.hashCode() * 31 + name.hashCode()) * 31 + desc.hashCode();
        }
    }
}
