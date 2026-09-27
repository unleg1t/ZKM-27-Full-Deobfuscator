package unlegit.zkm;

import org.objectweb.asm.ClassReader;
import org.objectweb.asm.ClassWriter;
import org.objectweb.asm.commons.ClassRemapper;
import org.objectweb.asm.commons.Remapper;
import org.objectweb.asm.commons.SimpleRemapper;
import org.objectweb.asm.tree.ClassNode;

import java.io.BufferedReader;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * Applies a ZKM {@code changeLogFileOut} mapping in reverse so obfuscated
 * names become the original source names. Manufactured members are left
 * untouched. Input classes are never loaded.
 */
public final class ZkmChangeLogRenamer {
    private ZkmChangeLogRenamer() {
    }

    public static void main(String[] args) throws Exception {
        if (args.length != 3 && args.length != 4) {
            System.err.println("usage: ZkmChangeLogRenamer <input.jar> <changelog.txt>"
                    + " <report-dir> [output.jar]");
            System.exit(2);
        }
        rewrite(Paths.get(args[0]), Paths.get(args[1]), Paths.get(args[2]),
                args.length == 4 ? Paths.get(args[3]) : null);
    }

    static Summary rewrite(Path input, Path changelog, Path reportDirectory,
                           Path output) throws Exception {
        Files.createDirectories(reportDirectory);
        ZkmArchiveIo.validatePaths(input, output);
        Mapping mapping = Mapping.parse(changelog);
        List<ZkmArchiveIo.EntryBytes> entries = ZkmArchiveIo.readEntries(input);
        Map<String, byte[]> original = ZkmArchiveIo.classBytes(entries);
        Summary summary = new Summary();
        summary.parsedClasses = original.size();
        summary.mappedClasses = mapping.classMap.size();
        List<String> rows = new ArrayList<String>();
        rows.add("from\tto\tkind");
        for (Map.Entry<String, String> entry : mapping.classMap.entrySet()) {
            rows.add(ZkmArchiveIo.tsv(entry.getKey(), entry.getValue(), "class"));
        }
        Map<String, byte[]> replacements = new LinkedHashMap<String, byte[]>();
        Remapper remapper = mapping.remapper();
        for (Map.Entry<String, byte[]> entry : original.entrySet()) {
            ClassReader reader = new ClassReader(entry.getValue());
            ClassWriter writer = new ClassWriter(0);
            reader.accept(new ClassRemapper(writer, remapper), 0);
            byte[] rewritten = writer.toByteArray();
            ClassNode node = ZkmArchiveIo.readClass(rewritten);
            replacements.put(node.name, rewritten);
            if (!node.name.equals(entry.getKey())) summary.changedClasses++;
        }
        List<ZkmArchiveIo.EntryBytes> remappedEntries =
                new ArrayList<ZkmArchiveIo.EntryBytes>();
        for (ZkmArchiveIo.EntryBytes entry : entries) {
            if (!entry.name.endsWith(".class")) {
                remappedEntries.add(entry);
                continue;
            }
            String oldName = new ClassReader(entry.bytes).getClassName();
            String newName = remapper.map(oldName);
            if (newName == null) newName = oldName;
            remappedEntries.add(new ZkmArchiveIo.EntryBytes(
                    newName + ".class", replacements.get(newName),
                    entry.time, entry.comment, entry.extra, entry.method));
        }
        ZkmArchiveIo.writeText(reportDirectory.resolve("rewrite.tsv"), rows);
        if (output != null) {
            ZkmArchiveIo.writeArchive(remappedEntries,
                    new LinkedHashMap<String, byte[]>(), output);
            summary.outputCommitted = true;
        }
        ZkmArchiveIo.writeText(reportDirectory.resolve("audit.txt"), Arrays.asList(
                "parsed_classes=" + summary.parsedClasses,
                "mapped_classes=" + summary.mappedClasses,
                "changed_classes=" + summary.changedClasses,
                "output_committed=" + summary.outputCommitted,
                "input_classes_loaded=false",
                "input_classes_initialized=false"));
        return summary;
    }

    static final class Mapping {
        final Map<String, String> classMap = new LinkedHashMap<String, String>();
        final Map<String, String> fieldMap = new HashMap<String, String>();
        final Map<String, String> methodMap = new HashMap<String, String>();

        Remapper remapper() {
            final Map<String, String> names = new HashMap<String, String>();
            names.putAll(classMap);
            names.putAll(fieldMap);
            names.putAll(methodMap);
            return new Remapper() {
                @Override
                public String map(String internalName) {
                    String mapped = names.get(internalName);
                    return mapped == null ? internalName : mapped;
                }

                @Override
                public String mapFieldName(String owner, String name, String descriptor) {
                    String mapped = names.get(owner + "." + name);
                    if (mapped == null) mapped = names.get(map(owner) + "." + name);
                    return mapped == null ? name : mapped;
                }

                @Override
                public String mapMethodName(String owner, String name, String descriptor) {
                    String prefix = owner + "." + name + argPrefix(descriptor);
                    String mapped = names.get(prefix);
                    if (mapped == null) {
                        mapped = names.get(map(owner) + "." + name + argPrefix(descriptor));
                    }
                    return mapped == null ? name : mapped;
                }
            };
        }

        static Mapping parse(Path changelog) throws Exception {
            Mapping mapping = new Mapping();
            String currentObfClass = null;
            String currentOrigClass = null;
            String section = "";
            try (BufferedReader reader = Files.newBufferedReader(changelog,
                    StandardCharsets.UTF_8)) {
                String line;
                while ((line = reader.readLine()) != null) {
                    String trimmed = line.trim();
                    if (trimmed.isEmpty() || trimmed.startsWith("//")) continue;
                    if (trimmed.startsWith("Package:")) {
                        String[] parts = splitArrow(trimmed.substring("Package:".length()));
                        if (parts != null) {
                            mapping.classMap.put(dotsToSlashes(parts[1]),
                                    dotsToSlashes(parts[0]));
                        }
                        continue;
                    }
                    if (trimmed.startsWith("Class:")) {
                        String payload = trimmed.substring("Class:".length()).trim();
                        payload = stripModifiers(payload);
                        String[] parts = splitArrow(payload);
                        if (parts != null) {
                            currentOrigClass = dotsToSlashes(parts[0]);
                            currentObfClass = dotsToSlashes(parts[1]);
                            mapping.classMap.put(currentObfClass, currentOrigClass);
                        }
                        continue;
                    }
                    if (trimmed.startsWith("FieldsOf:")) {
                        section = "fields";
                        continue;
                    }
                    if (trimmed.startsWith("MethodsOf:")) {
                        section = "methods";
                        continue;
                    }
                    if (trimmed.startsWith("Source:")
                            || trimmed.startsWith("TraceBackClass:")
                            || trimmed.startsWith("ForwardClass:")
                            || trimmed.startsWith("MemberClass:")) {
                        continue;
                    }
                    if (currentObfClass == null || currentOrigClass == null) continue;
                    if ("fields".equals(section) && trimmed.contains("=>")) {
                        String[] parts = splitArrow(stripModifiers(trimmed));
                        if (parts == null) continue;
                        String orig = lastToken(parts[0]);
                        String obf = lastToken(parts[1]);
                        if (orig != null && obf != null && !obf.contains("Manufactured")) {
                            mapping.fieldMap.put(currentObfClass + "." + obf, orig);
                        }
                    } else if ("methods".equals(section) && trimmed.contains("=>")) {
                        String[] parts = splitArrow(stripModifiers(trimmed));
                        if (parts == null) continue;
                        Member orig = parseMember(parts[0]);
                        Member obf = parseMember(parts[1]);
                        if (orig != null && obf != null
                                && !"<init>".equals(orig.name)
                                && !"<clinit>".equals(orig.name)) {
                            mapping.methodMap.put(
                                    currentObfClass + "." + obf.name + toDescriptor(obf.args),
                                    orig.name);
                        }
                    }
                }
            }
            return mapping;
        }

        private static String[] splitArrow(String line) {
            int idx = line.indexOf("=>");
            if (idx < 0) return null;
            return new String[] {
                    line.substring(0, idx).trim(),
                    line.substring(idx + 2).trim()
            };
        }

        private static String stripModifiers(String value) {
            return value.replace("public ", "")
                    .replace("private ", "")
                    .replace("protected ", "")
                    .replace("static ", "")
                    .replace("final ", "")
                    .replace("native ", "")
                    .replace("abstract ", "")
                    .replace("synchronized ", "")
                    .replace("volatile ", "")
                    .replace("transient ", "")
                    .replace("SignatureNotChanged:", "")
                    .replace("Manufactured:", "")
                    .trim();
        }

        private static String lastToken(String value) {
            String cleaned = value.replace("*", "").trim();
            int space = cleaned.lastIndexOf(' ');
            String token = space < 0 ? cleaned : cleaned.substring(space + 1);
            int paren = token.indexOf('(');
            if (paren >= 0) token = token.substring(0, paren);
            return token;
        }

        private static Member parseMember(String value) {
            String cleaned = value.replace("*", "").trim();
            int paren = cleaned.indexOf('(');
            if (paren < 0) return null;
            String namePart = cleaned.substring(0, paren).trim();
            String name = lastToken(namePart);
            int close = cleaned.indexOf(')', paren);
            String args = close < 0 ? "" : cleaned.substring(paren + 1, close);
            Member member = new Member();
            member.name = name;
            member.args = args;
            return member;
        }

        private static String argPrefix(String descriptor) {
            if (descriptor == null) return "()";
            int close = descriptor.indexOf(')');
            return close < 0 ? descriptor : descriptor.substring(0, close + 1);
        }

        private static String toDescriptor(String javaArgs) {
            if (javaArgs == null || javaArgs.trim().isEmpty()) return "()";
            StringBuilder desc = new StringBuilder("(");
            String[] parts = javaArgs.split(",");
            for (String part : parts) {
                String type = part.trim();
                if (type.isEmpty()) continue;
                desc.append(javaTypeToDesc(type));
            }
            desc.append(")");
            return desc.toString();
        }

        private static String javaTypeToDesc(String type) {
            int arrays = 0;
            while (type.endsWith("[]")) {
                arrays++;
                type = type.substring(0, type.length() - 2);
            }
            String base;
            if ("boolean".equals(type)) base = "Z";
            else if ("byte".equals(type)) base = "B";
            else if ("char".equals(type)) base = "C";
            else if ("short".equals(type)) base = "S";
            else if ("int".equals(type)) base = "I";
            else if ("long".equals(type)) base = "J";
            else if ("float".equals(type)) base = "F";
            else if ("double".equals(type)) base = "D";
            else if ("void".equals(type)) base = "V";
            else base = "L" + type.replace('.', '/') + ";";
            StringBuilder out = new StringBuilder();
            for (int i = 0; i < arrays; i++) out.append('[');
            out.append(base);
            return out.toString();
        }

        private static String dotsToSlashes(String name) {
            int space = name.lastIndexOf(' ');
            if (space >= 0) name = name.substring(space + 1);
            return name.replace('.', '/');
        }

        private static final class Member {
            String name;
            String args;
        }
    }

    static final class Summary {
        int parsedClasses;
        int mappedClasses;
        int changedClasses;
        boolean outputCommitted;
    }
}
