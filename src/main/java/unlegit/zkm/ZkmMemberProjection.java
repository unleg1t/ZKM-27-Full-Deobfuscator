package unlegit.zkm;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Objects;
import java.util.Set;

import org.objectweb.asm.Type;
import org.objectweb.asm.tree.ClassNode;
import org.objectweb.asm.tree.MethodNode;

/**
 * Projects decoded ZKM member symbols through the current 4.21 class and method
 * mappings. Projection is collision-aware: canonical, case-insensitive names are
 * only evidence for a candidate set and are never selected without a unique
 * mapped member or a unique member in the current archive.
 */
public final class ZkmMemberProjection {
    public static final String IDENTITY_EXTERNAL = "IDENTITY_EXTERNAL";
    public static final String IDENTITY_RAW = "IDENTITY_RAW";
    public static final String PROJECTED_METHOD_UNION = "PROJECTED_METHOD_UNION";
    public static final String PROJECTED_CURRENT_MEMBER = "PROJECTED_CURRENT_MEMBER";
    public static final String AMBIGUOUS_METHOD_UNION = "AMBIGUOUS_METHOD_UNION";
    public static final String AMBIGUOUS_CURRENT_MEMBER = "AMBIGUOUS_CURRENT_MEMBER";
    public static final String FAILED_NO_CLASS_CANDIDATE = "FAILED_NO_CLASS_CANDIDATE";
    public static final String FAILED_NO_MEMBER = "FAILED_NO_MEMBER";
    public static final String FAILED_UNSUPPORTED_FIELD = "FAILED_UNSUPPORTED_FIELD";

    private ZkmMemberProjection() {
    }

    /** Loads mapping metadata without loading or initializing any input class. */
    public static Mapping load(Path classMap, Path methodMap) throws IOException {
        Objects.requireNonNull(classMap, "classMap");
        Objects.requireNonNull(methodMap, "methodMap");
        return new Mapping(loadClassMappings(classMap), loadMethodMappings(methodMap));
    }

    /** Uses decoded archive symbols directly without semantic mapping. */
    public static Mapping identity() {
        return new Mapping(Collections.<ClassMapping>emptyList(),
                Collections.<MethodMapping>emptyList(), true);
    }

    /** Immutable mapping metadata plus an audit of projection calls. */
    public static final class Mapping {
        private final List<ClassMapping> classMappings;
        private final Map<String, List<ClassMapping>> exactClasses;
        private final Map<String, List<ClassMapping>> canonicalClasses;
        private final Map<MethodKey, List<MethodMapping>> methods;
        private final MutableAudit audit = new MutableAudit();
        private final boolean identity;

        private Mapping(List<ClassMapping> classMappings,
                        List<MethodMapping> methodMappings) {
            this(classMappings, methodMappings, false);
        }

        private Mapping(List<ClassMapping> classMappings,
                        List<MethodMapping> methodMappings, boolean identity) {
            this.classMappings = Collections.unmodifiableList(
                    new ArrayList<>(classMappings));
            this.exactClasses = indexExactClasses(classMappings);
            this.canonicalClasses = indexCanonicalClasses(classMappings);
            this.methods = indexMethods(methodMappings);
            this.identity = identity;
        }

        /**
         * Projects one decoded member target. An unresolved result has empty
         * projected owner/name/descriptor fields and must not be directized.
         */
        public ProjectedTarget project(ZkmMemberIndyDeobfuscator.MemberTarget target,
                                       Map<String, ClassNode> classes) {
            Objects.requireNonNull(target, "target");
            Objects.requireNonNull(classes, "classes");
            ProjectedTarget projected = resolve(target, classes);
            audit.record(target, projected);
            return projected;
        }

        /** Returns an immutable snapshot; later projections do not mutate it. */
        public Audit audit() {
            return audit.snapshot();
        }

        public int classMappingCount() {
            return classMappings.size();
        }

        private ProjectedTarget resolve(ZkmMemberIndyDeobfuscator.MemberTarget raw,
                                        Map<String, ClassNode> classes) {
            if (identity) {
                return resolved(raw, 1, raw.owner, raw.name, raw.desc,
                        IDENTITY_RAW, "decoded-archive-symbol");
            }
            if (!raw.owner.startsWith("a/")) {
                return resolved(raw, 1, raw.owner, raw.name, raw.desc,
                        IDENTITY_EXTERNAL, "non-obfuscated-owner");
            }
            List<ClassMapping> candidates = candidates(raw.owner);
            if (raw.isField()) {
                return unresolved(raw, candidates, Collections.<Projection>emptySet(),
                        FAILED_UNSUPPORTED_FIELD);
            }

            Set<Projection> mapped = new LinkedHashSet<>();
            String rawCanonicalDescriptor = canonicalDescriptor(raw.desc);
            for (ClassMapping candidate : candidates) {
                MethodKey key = new MethodKey(candidate.source, raw.name,
                        rawCanonicalDescriptor);
                List<MethodMapping> matches = methods.get(key);
                if (matches == null) continue;
                for (MethodMapping method : matches) {
                    String descriptor = projectMappedDescriptor(method.descriptor);
                    if (descriptor == null) continue;
                    mapped.add(new Projection(candidate.target, method.targetName,
                            descriptor, "method-union"));
                }
            }
            if (mapped.size() == 1) {
                Projection projection = mapped.iterator().next();
                return resolved(raw, candidates.size(), projection.owner,
                        projection.name, projection.descriptor,
                        PROJECTED_METHOD_UNION, projection.evidence);
            }
            if (mapped.size() > 1) {
                return unresolved(raw, candidates, mapped, AMBIGUOUS_METHOD_UNION);
            }

            Set<Projection> archive = new LinkedHashSet<>();
            String projectedRawDescriptor = projectRawDescriptor(raw.desc);
            for (ClassMapping candidate : candidates) {
                ClassNode owner = classes.get(candidate.target);
                if (owner == null) continue;
                for (MethodNode method : owner.methods) {
                    boolean descriptorMatch = projectedRawDescriptor == null
                            ? shapeCompatible(raw.desc, method.desc)
                            : projectedRawDescriptor.equals(method.desc);
                    if (!raw.name.equals(method.name) || !descriptorMatch) continue;
                    archive.add(new Projection(owner.name, method.name, method.desc,
                            "unique-current-member-shape"));
                }
            }
            if (archive.size() == 1) {
                Projection projection = archive.iterator().next();
                return resolved(raw, candidates.size(), projection.owner,
                        projection.name, projection.descriptor,
                        PROJECTED_CURRENT_MEMBER, projection.evidence);
            }
            if (archive.size() > 1) {
                return unresolved(raw, candidates, archive, AMBIGUOUS_CURRENT_MEMBER);
            }
            return unresolved(raw, candidates, Collections.<Projection>emptySet(),
                    candidates.isEmpty() ? FAILED_NO_CLASS_CANDIDATE : FAILED_NO_MEMBER);
        }

        private String projectMappedDescriptor(String descriptor) {
            Type method = Type.getMethodType(descriptor);
            Type[] arguments = method.getArgumentTypes();
            Type[] projected = new Type[arguments.length];
            for (int i = 0; i < arguments.length; i++) {
                projected[i] = projectMappedType(arguments[i]);
                if (projected[i] == null) return null;
            }
            Type returned = projectMappedType(method.getReturnType());
            return returned == null ? null
                    : Type.getMethodDescriptor(returned, projected);
        }

        private Type projectMappedType(Type type) {
            if (type.getSort() == Type.ARRAY) {
                Type element = projectMappedType(type.getElementType());
                return element == null ? null : arrayType(type.getDimensions(), element);
            }
            if (type.getSort() != Type.OBJECT) return type;
            List<ClassMapping> exact = exactClasses.get(type.getInternalName());
            if (exact == null || exact.isEmpty()) return type;
            Set<String> targets = targets(exact);
            return targets.size() == 1
                    ? Type.getObjectType(targets.iterator().next()) : null;
        }

        private String projectRawDescriptor(String descriptor) {
            Type method = Type.getMethodType(descriptor);
            Type[] arguments = method.getArgumentTypes();
            Type[] projected = new Type[arguments.length];
            for (int i = 0; i < arguments.length; i++) {
                projected[i] = projectRawType(arguments[i]);
                if (projected[i] == null) return null;
            }
            Type returned = projectRawType(method.getReturnType());
            return returned == null ? null
                    : Type.getMethodDescriptor(returned, projected);
        }

        private Type projectRawType(Type type) {
            if (type.getSort() == Type.ARRAY) {
                Type element = projectRawType(type.getElementType());
                return element == null ? null : arrayType(type.getDimensions(), element);
            }
            if (type.getSort() != Type.OBJECT
                    || !type.getInternalName().startsWith("a/")) return type;
            Set<String> targets = targets(candidates(type.getInternalName()));
            return targets.size() == 1
                    ? Type.getObjectType(targets.iterator().next()) : null;
        }

        private List<ClassMapping> candidates(String rawOwner) {
            List<ClassMapping> exact = new ArrayList<>();
            List<ClassMapping> direct = exactClasses.get(rawOwner);
            if (direct != null) exact.addAll(direct);
            String suffixPrefix = rawOwner + "_";
            for (ClassMapping mapping : classMappings) {
                if (mapping.source.startsWith(suffixPrefix)
                        && numeric(mapping.source.substring(suffixPrefix.length()))) {
                    exact.add(mapping);
                }
            }
            if (!exact.isEmpty()) return deduplicate(exact);
            List<ClassMapping> canonical = canonicalClasses.get(
                    canonicalInternal(rawOwner));
            return canonical == null ? Collections.<ClassMapping>emptyList()
                    : canonical;
        }
    }

    /** Result of one projection attempt. */
    public static final class ProjectedTarget {
        public final int index;
        public final String rawKind;
        public final String rawOwner;
        public final String rawName;
        public final String rawDesc;
        public final String kind;
        public final String owner;
        public final String name;
        public final String desc;
        public final String status;
        public final String evidence;
        public final int candidateClasses;
        private final boolean resolved;

        private ProjectedTarget(ZkmMemberIndyDeobfuscator.MemberTarget raw,
                                int candidateClasses, String owner, String name,
                                String descriptor, String status, String evidence,
                                boolean resolved) {
            this.index = raw.index;
            this.rawKind = raw.kind;
            this.rawOwner = raw.owner;
            this.rawName = raw.name;
            this.rawDesc = raw.desc;
            this.kind = raw.kind;
            this.owner = owner;
            this.name = name;
            this.desc = descriptor;
            this.status = status;
            this.evidence = evidence;
            this.candidateClasses = candidateClasses;
            this.resolved = resolved;
        }

        public boolean isResolved() {
            return resolved;
        }

        public boolean isAmbiguous() {
            return status.startsWith("AMBIGUOUS_");
        }

        public boolean isIdentity() {
            return IDENTITY_EXTERNAL.equals(status);
        }
    }

    /** Immutable aggregate audit for calls made through one Mapping instance. */
    public static final class Audit {
        public final int sites;
        public final int resolvedSites;
        public final int unresolvedSites;
        public final int ambiguousSites;
        public final int uniqueRawMembers;
        public final int resolvedMembers;
        public final Map<String, Integer> statuses;

        private Audit(int sites, int resolvedSites, int ambiguousSites,
                      int uniqueRawMembers, int resolvedMembers,
                      Map<String, Integer> statuses) {
            this.sites = sites;
            this.resolvedSites = resolvedSites;
            this.unresolvedSites = sites - resolvedSites;
            this.ambiguousSites = ambiguousSites;
            this.uniqueRawMembers = uniqueRawMembers;
            this.resolvedMembers = resolvedMembers;
            this.statuses = Collections.unmodifiableMap(
                    new LinkedHashMap<>(statuses));
        }

        public List<String> lines() {
            List<String> result = new ArrayList<>();
            result.add("projection_sites=" + sites);
            result.add("projection_resolved_sites=" + resolvedSites);
            result.add("projection_unresolved_sites=" + unresolvedSites);
            result.add("projection_ambiguous_sites=" + ambiguousSites);
            result.add("projection_unique_raw_members=" + uniqueRawMembers);
            result.add("projection_resolved_members=" + resolvedMembers);
            for (Map.Entry<String, Integer> status : statuses.entrySet()) {
                result.add("projection_status." + status.getKey() + "="
                        + status.getValue());
            }
            result.add("projection_gate="
                    + (unresolvedSites == 0 ? "PASS" : "PARTIAL"));
            return Collections.unmodifiableList(result);
        }

        public void write(Path path) throws IOException {
            Files.write(path, lines(), StandardCharsets.UTF_8);
        }
    }

    private static ProjectedTarget resolved(
            ZkmMemberIndyDeobfuscator.MemberTarget raw, int candidateClasses,
            String owner, String name, String descriptor, String status,
            String evidence) {
        return new ProjectedTarget(raw, candidateClasses, owner, name, descriptor,
                status, evidence, true);
    }

    private static ProjectedTarget unresolved(
            ZkmMemberIndyDeobfuscator.MemberTarget raw,
            List<ClassMapping> candidates, Set<Projection> projections,
            String status) {
        StringBuilder evidence = new StringBuilder();
        for (ClassMapping candidate : candidates) {
            if (evidence.length() != 0) evidence.append(',');
            evidence.append(candidate.source).append("->").append(candidate.target);
        }
        List<Projection> sorted = new ArrayList<>(projections);
        sorted.sort(Comparator.comparing((Projection value) -> value.owner)
                .thenComparing(value -> value.name)
                .thenComparing(value -> value.descriptor));
        for (Projection projection : sorted) {
            evidence.append(';').append(projection.owner).append('.')
                    .append(projection.name).append(projection.descriptor);
        }
        return new ProjectedTarget(raw, candidates.size(), "", "", "", status,
                evidence.toString(), false);
    }

    private static Map<String, List<ClassMapping>> indexExactClasses(
            List<ClassMapping> mappings) {
        Map<String, List<ClassMapping>> result = new LinkedHashMap<>();
        for (ClassMapping mapping : mappings) {
            result.computeIfAbsent(mapping.source, ignored -> new ArrayList<>())
                    .add(mapping);
        }
        return immutableLists(result);
    }

    private static Map<String, List<ClassMapping>> indexCanonicalClasses(
            List<ClassMapping> mappings) {
        Map<String, List<ClassMapping>> result = new LinkedHashMap<>();
        for (ClassMapping mapping : mappings) {
            result.computeIfAbsent(canonicalInternal(mapping.source),
                    ignored -> new ArrayList<>()).add(mapping);
        }
        return immutableLists(result);
    }

    private static Map<MethodKey, List<MethodMapping>> indexMethods(
            List<MethodMapping> mappings) {
        Map<MethodKey, List<MethodMapping>> result = new LinkedHashMap<>();
        for (MethodMapping mapping : mappings) {
            MethodKey key = new MethodKey(mapping.owner, mapping.name,
                    canonicalDescriptor(mapping.descriptor));
            result.computeIfAbsent(key, ignored -> new ArrayList<>()).add(mapping);
        }
        Map<MethodKey, List<MethodMapping>> immutable = new LinkedHashMap<>();
        for (Map.Entry<MethodKey, List<MethodMapping>> entry : result.entrySet()) {
            immutable.put(entry.getKey(), Collections.unmodifiableList(
                    new ArrayList<>(entry.getValue())));
        }
        return Collections.unmodifiableMap(immutable);
    }

    private static <K> Map<K, List<ClassMapping>> immutableLists(
            Map<K, List<ClassMapping>> values) {
        Map<K, List<ClassMapping>> result = new LinkedHashMap<>();
        for (Map.Entry<K, List<ClassMapping>> entry : values.entrySet()) {
            result.put(entry.getKey(), Collections.unmodifiableList(
                    deduplicate(entry.getValue())));
        }
        return Collections.unmodifiableMap(result);
    }

    private static List<ClassMapping> deduplicate(List<ClassMapping> mappings) {
        return new ArrayList<>(new LinkedHashSet<>(mappings));
    }

    private static Set<String> targets(List<ClassMapping> mappings) {
        Set<String> result = new LinkedHashSet<>();
        for (ClassMapping mapping : mappings) result.add(mapping.target);
        return result;
    }

    private static List<ClassMapping> loadClassMappings(Path path) throws IOException {
        Table table = Table.read(path);
        table.require("source_internal_name", "target_internal_name");
        List<ClassMapping> result = new ArrayList<>();
        for (Map<String, String> row : table.rows) {
            String source = required(row, "source_internal_name", path);
            String target = required(row, "target_internal_name", path);
            result.add(new ClassMapping(source, target));
        }
        return result;
    }

    private static List<MethodMapping> loadMethodMappings(Path path) throws IOException {
        Table table = Table.read(path);
        table.require("source_owner", "source_name", "source_descriptor", "target_name");
        List<MethodMapping> result = new ArrayList<>();
        for (Map<String, String> row : table.rows) {
            String owner = required(row, "source_owner", path);
            String name = required(row, "source_name", path);
            String descriptor = required(row, "source_descriptor", path);
            String targetName = required(row, "target_name", path);
            try {
                Type.getMethodType(descriptor);
            } catch (IllegalArgumentException failure) {
                throw new IOException("invalid method descriptor in " + path + ": "
                        + descriptor, failure);
            }
            result.add(new MethodMapping(owner, name, descriptor, targetName));
        }
        return result;
    }

    private static String required(Map<String, String> row, String column, Path path)
            throws IOException {
        String value = row.get(column);
        if (value == null || value.isEmpty()) {
            throw new IOException("empty " + column + " in " + path);
        }
        return value;
    }

    private static Type arrayType(int dimensions, Type element) {
        StringBuilder descriptor = new StringBuilder();
        for (int i = 0; i < dimensions; i++) descriptor.append('[');
        return Type.getType(descriptor.append(element.getDescriptor()).toString());
    }

    private static boolean numeric(String value) {
        if (value.isEmpty()) return false;
        for (int i = 0; i < value.length(); i++) {
            if (value.charAt(i) < '0' || value.charAt(i) > '9') return false;
        }
        return true;
    }

    private static boolean shapeCompatible(String raw, String current) {
        Type left = Type.getMethodType(raw);
        Type right = Type.getMethodType(current);
        Type[] leftArguments = left.getArgumentTypes();
        Type[] rightArguments = right.getArgumentTypes();
        if (leftArguments.length != rightArguments.length) return false;
        for (int i = 0; i < leftArguments.length; i++) {
            if (!sameShape(leftArguments[i], rightArguments[i])) return false;
        }
        return sameShape(left.getReturnType(), right.getReturnType());
    }

    private static boolean sameShape(Type left, Type right) {
        if (left.getSort() == Type.ARRAY || right.getSort() == Type.ARRAY) {
            return left.getSort() == Type.ARRAY && right.getSort() == Type.ARRAY
                    && left.getDimensions() == right.getDimensions()
                    && sameShape(left.getElementType(), right.getElementType());
        }
        boolean leftReference = left.getSort() == Type.OBJECT;
        boolean rightReference = right.getSort() == Type.OBJECT;
        return leftReference || rightReference
                ? leftReference && rightReference : left.getSort() == right.getSort();
    }

    private static String canonicalDescriptor(String descriptor) {
        Type method = Type.getMethodType(descriptor);
        StringBuilder result = new StringBuilder("(");
        for (Type argument : method.getArgumentTypes()) {
            result.append(canonicalType(argument));
        }
        return result.append(')').append(canonicalType(method.getReturnType())).toString();
    }

    private static String canonicalType(Type type) {
        if (type.getSort() == Type.ARRAY) {
            StringBuilder result = new StringBuilder();
            for (int i = 0; i < type.getDimensions(); i++) result.append('[');
            return result.append(canonicalType(type.getElementType())).toString();
        }
        if (type.getSort() != Type.OBJECT) return type.getDescriptor();
        return "L" + canonicalInternal(type.getInternalName()) + ";";
    }

    private static String canonicalInternal(String name) {
        return name.replaceFirst("_[0-9]+$", "").toLowerCase(Locale.ROOT);
    }

    private static final class MutableAudit {
        private int sites;
        private int resolvedSites;
        private int ambiguousSites;
        private final Set<MemberKey> rawMembers = new LinkedHashSet<>();
        private final Set<MemberKey> resolvedMembers = new LinkedHashSet<>();
        private final Map<String, Integer> statuses = new LinkedHashMap<>();

        synchronized void record(ZkmMemberIndyDeobfuscator.MemberTarget raw,
                                 ProjectedTarget projected) {
            sites++;
            MemberKey key = new MemberKey(raw.kind, raw.owner, raw.name, raw.desc);
            rawMembers.add(key);
            if (projected.isResolved()) {
                resolvedSites++;
                resolvedMembers.add(key);
            }
            if (projected.isAmbiguous()) ambiguousSites++;
            statuses.put(projected.status,
                    statuses.getOrDefault(projected.status, 0) + 1);
        }

        synchronized Audit snapshot() {
            return new Audit(sites, resolvedSites, ambiguousSites, rawMembers.size(),
                    resolvedMembers.size(), statuses);
        }
    }

    private static final class Table {
        final Path path;
        final Set<String> header;
        final List<Map<String, String>> rows;

        private Table(Path path, Set<String> header,
                      List<Map<String, String>> rows) {
            this.path = path;
            this.header = header;
            this.rows = rows;
        }

        static Table read(Path path) throws IOException {
            List<String> lines = Files.readAllLines(path, StandardCharsets.UTF_8);
            if (lines.isEmpty()) throw new IOException("empty table: " + path);
            String[] columns = lines.get(0).split("\\t", -1);
            Set<String> header = new LinkedHashSet<>(Arrays.asList(columns));
            List<Map<String, String>> rows = new ArrayList<>();
            for (int line = 1; line < lines.size(); line++) {
                if (lines.get(line).isEmpty()) continue;
                String[] cells = lines.get(line).split("\\t", -1);
                Map<String, String> row = new HashMap<>();
                for (int column = 0; column < columns.length; column++) {
                    row.put(columns[column], column < cells.length ? cells[column] : "");
                }
                rows.add(row);
            }
            return new Table(path, header, rows);
        }

        void require(String... columns) throws IOException {
            for (String column : columns) {
                if (!header.contains(column)) {
                    throw new IOException("missing " + column + " in " + path);
                }
            }
        }
    }

    private static final class ClassMapping {
        final String source;
        final String target;

        ClassMapping(String source, String target) {
            this.source = source;
            this.target = target;
        }

        @Override
        public boolean equals(Object other) {
            if (!(other instanceof ClassMapping)) return false;
            ClassMapping mapping = (ClassMapping) other;
            return source.equals(mapping.source) && target.equals(mapping.target);
        }

        @Override
        public int hashCode() {
            return Arrays.hashCode(new Object[]{source, target});
        }
    }

    private static final class MethodMapping {
        final String owner;
        final String name;
        final String descriptor;
        final String targetName;

        MethodMapping(String owner, String name, String descriptor, String targetName) {
            this.owner = owner;
            this.name = name;
            this.descriptor = descriptor;
            this.targetName = targetName;
        }
    }

    private static final class MethodKey {
        final String owner;
        final String name;
        final String descriptor;

        MethodKey(String owner, String name, String descriptor) {
            this.owner = owner;
            this.name = name;
            this.descriptor = descriptor;
        }

        @Override
        public boolean equals(Object other) {
            if (!(other instanceof MethodKey)) return false;
            MethodKey key = (MethodKey) other;
            return owner.equals(key.owner) && name.equals(key.name)
                    && descriptor.equals(key.descriptor);
        }

        @Override
        public int hashCode() {
            return Arrays.hashCode(new Object[]{owner, name, descriptor});
        }
    }

    private static final class MemberKey {
        final String kind;
        final String owner;
        final String name;
        final String descriptor;

        MemberKey(String kind, String owner, String name, String descriptor) {
            this.kind = kind;
            this.owner = owner;
            this.name = name;
            this.descriptor = descriptor;
        }

        @Override
        public boolean equals(Object other) {
            if (!(other instanceof MemberKey)) return false;
            MemberKey key = (MemberKey) other;
            return kind.equals(key.kind) && owner.equals(key.owner)
                    && name.equals(key.name) && descriptor.equals(key.descriptor);
        }

        @Override
        public int hashCode() {
            return Arrays.hashCode(new Object[]{kind, owner, name, descriptor});
        }
    }

    private static final class Projection {
        final String owner;
        final String name;
        final String descriptor;
        final String evidence;

        Projection(String owner, String name, String descriptor, String evidence) {
            this.owner = owner;
            this.name = name;
            this.descriptor = descriptor;
            this.evidence = evidence;
        }

        @Override
        public boolean equals(Object other) {
            if (!(other instanceof Projection)) return false;
            Projection projection = (Projection) other;
            return owner.equals(projection.owner) && name.equals(projection.name)
                    && descriptor.equals(projection.descriptor);
        }

        @Override
        public int hashCode() {
            return Arrays.hashCode(new Object[]{owner, name, descriptor});
        }
    }
}
