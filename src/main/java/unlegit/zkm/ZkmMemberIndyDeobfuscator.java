package unlegit.zkm;

import org.objectweb.asm.Handle;
import org.objectweb.asm.Opcodes;
import org.objectweb.asm.Type;
import org.objectweb.asm.tree.AbstractInsnNode;
import org.objectweb.asm.tree.ClassNode;
import org.objectweb.asm.tree.FieldInsnNode;
import org.objectweb.asm.tree.InsnNode;
import org.objectweb.asm.tree.IntInsnNode;
import org.objectweb.asm.tree.InvokeDynamicInsnNode;
import org.objectweb.asm.tree.JumpInsnNode;
import org.objectweb.asm.tree.LabelNode;
import org.objectweb.asm.tree.LdcInsnNode;
import org.objectweb.asm.tree.MethodInsnNode;
import org.objectweb.asm.tree.MethodNode;
import org.objectweb.asm.tree.TableSwitchInsnNode;
import org.objectweb.asm.tree.VarInsnNode;

import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Set;

/** Static decoder for ZKM member invokedynamic sites with trailing JJ keys. */
public final class ZkmMemberIndyDeobfuscator {
    private static final String BSM_DESC = "(Ljava/lang/invoke/MethodHandles$Lookup;"
            + "Ljava/lang/String;Ljava/lang/invoke/MethodType;)"
            + "Ljava/lang/invoke/CallSite;";

    private ZkmMemberIndyDeobfuscator() {
    }

    public static void main(String[] args) throws Exception {
        if (args.length != 2) {
            System.err.println("usage: ZkmMemberIndyDeobfuscator <input.jar> <report-dir>");
            System.exit(2);
        }
        audit(Paths.get(args[0]), Paths.get(args[1]));
    }

    static Summary audit(Path input, Path reportDirectory) throws Exception {
        Files.createDirectories(reportDirectory);
        Map<String, ClassNode> classes = ZkmLongKeyEvaluator.readClasses(input);
        List<String> rows = new ArrayList<>();
        rows.add("class\tmethod\tinstruction\tindy_name\tindy_desc\tfirst_key"
                + "\tsecond_key\tindex\tkind\ttarget_owner\ttarget_name"
                + "\ttarget_desc\tstripped_desc\ttarget_handle_desc"
                + "\tdescriptor_compatible\targument_conversions"
                + "\treturn_conversion\tstatus\treason");
        Summary summary = new Summary();
        summary.parsedClasses = classes.size();
        Map<String, ResolverModel> models = new HashMap<>();
        for (ClassNode owner : classes.values()) {
            int ownerSites = countSites(owner);
            if (ownerSites == 0) continue;
            summary.siteClasses++;
            ResolverModel model;
            try {
                model = ResolverModel.build(owner);
                models.put(owner.name, model);
                summary.models++;
            } catch (Throwable failure) {
                model = null;
                summary.modelFailures++;
            }
            for (MethodNode method : owner.methods) {
                int instruction = 0;
                for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
                     insn = insn.getNext(), instruction++) {
                    if (!(insn instanceof InvokeDynamicInsnNode)
                            || !isMemberSite(owner, (InvokeDynamicInsnNode) insn)) continue;
                    summary.sites++;
                    InvokeDynamicInsnNode indy = (InvokeDynamicInsnNode) insn;
                    AbstractInsnNode secondNode = previousCode(indy);
                    AbstractInsnNode firstNode = previousCode(secondNode);
                    Long first = longConstant(firstNode);
                    Long second = longConstant(secondNode);
                    if (first == null || second == null) {
                        summary.argumentFailures++;
                        rows.add(row(owner.name, method.name + method.desc, instruction,
                                printable(indy.name), indy.desc, "", "", "", "", "",
                                "", "", "", "", false, "", "", "FAIL",
                                "non-adjacent-constant-keys"));
                        continue;
                    }
                    if (model == null) {
                        rows.add(row(owner.name, method.name + method.desc, instruction,
                                printable(indy.name), indy.desc, first, second, "", "", "",
                                "", "", "", "", false, "", "", "FAIL",
                                "resolver-model"));
                        continue;
                    }
                    try {
                        MemberTarget target = model.resolve(indy.name, first, second);
                        String stripped = stripTrailingKeys(indy.desc);
                        String handleDescriptor = target.handleDescriptor();
                        ConversionModel conversions = ConversionModel.between(
                                stripped, handleDescriptor);
                        if (conversions.compatible) {
                            summary.resolved++;
                            summary.descriptorCompatible++;
                        } else {
                            summary.descriptorMismatches++;
                        }
                        rows.add(row(owner.name, method.name + method.desc, instruction,
                                printable(indy.name), indy.desc, first, second, target.index,
                                target.kind, target.owner, target.name, target.desc,
                                stripped, handleDescriptor, conversions.compatible,
                                conversions.argumentSummary(), conversions.returnConversion,
                                conversions.compatible ? "OK" : "FAIL",
                                conversions.compatible ? "" : conversions.reason));
                    } catch (Throwable failure) {
                        summary.decodeFailures++;
                        rows.add(row(owner.name, method.name + method.desc, instruction,
                                printable(indy.name), indy.desc, first, second, "", "", "",
                                "", "", "", "", false, "", "", "FAIL",
                                shortReason(failure)));
                    }
                }
            }
        }
        Files.write(reportDirectory.resolve("sites.tsv"), rows, StandardCharsets.UTF_8);
        List<String> audit = Arrays.asList(
                "input=" + input.toAbsolutePath(),
                "parsed_classes=" + summary.parsedClasses,
                "site_classes=" + summary.siteClasses,
                "sites=" + summary.sites,
                "models=" + summary.models,
                "model_failures=" + summary.modelFailures,
                "resolved=" + summary.resolved,
                "descriptor_compatible=" + summary.descriptorCompatible,
                "descriptor_mismatches=" + summary.descriptorMismatches,
                "argument_failures=" + summary.argumentFailures,
                "decode_failures=" + summary.decodeFailures,
                "input_classes_loaded=false",
                "gate=" + (summary.resolved == summary.sites ? "PASS" : "FAIL"));
        Files.write(reportDirectory.resolve("audit.txt"), audit, StandardCharsets.UTF_8);
        System.out.println("sites=" + summary.sites + " classes=" + summary.siteClasses
                + " models=" + summary.models + " resolved=" + summary.resolved
                + " failed=" + (summary.modelFailures + summary.argumentFailures
                + summary.decodeFailures));
        return summary;
    }

    private static int countSites(ClassNode owner) {
        int count = 0;
        for (MethodNode method : owner.methods) {
            for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
                 insn = insn.getNext()) {
                if (insn instanceof InvokeDynamicInsnNode
                        && isMemberSite(owner, (InvokeDynamicInsnNode) insn)) count++;
            }
        }
        return count;
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

    static final class Summary {
        int parsedClasses;
        int siteClasses;
        int sites;
        int models;
        int modelFailures;
        int resolved;
        int argumentFailures;
        int decodeFailures;
        int descriptorCompatible;
        int descriptorMismatches;
    }

    static final class ResolverModel {
        final String owner;
        final Object[] symbols;
        final String[] decoded;
        final int[] offsets;
        final SelectorModel selectors;

        ResolverModel(String owner, Object[] symbols, String[] decoded, int[] offsets,
                      SelectorModel selectors) {
            this.owner = owner;
            this.symbols = symbols;
            this.decoded = decoded;
            this.offsets = offsets;
            this.selectors = selectors;
        }

        static ResolverModel build(ClassNode owner) {
            MethodNode indexMethod = null;
            TableSwitchInsnNode table = null;
            FieldRef objectField = null;
            FieldRef stringField = null;
            for (MethodNode method : owner.methods) {
                if (!"(JJ)I".equals(method.desc)
                        || (method.access & Opcodes.ACC_STATIC) == 0) continue;
                TableSwitchInsnNode candidateTable = null;
                FieldRef candidateObject = null;
                FieldRef candidateString = null;
                for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
                     insn = insn.getNext()) {
                    if (insn instanceof TableSwitchInsnNode) {
                        TableSwitchInsnNode candidate = (TableSwitchInsnNode) insn;
                        if (candidate.min == 0 && candidate.max == 62
                                && candidate.labels.size() == 63) candidateTable = candidate;
                    }
                    if (insn instanceof FieldInsnNode && insn.getOpcode() == Opcodes.GETSTATIC) {
                        FieldInsnNode field = (FieldInsnNode) insn;
                        if (owner.name.equals(field.owner)
                                && "[Ljava/lang/Object;".equals(field.desc)) {
                            candidateObject = new FieldRef(field.owner, field.name, field.desc);
                        }
                        if (owner.name.equals(field.owner)
                                && "[Ljava/lang/String;".equals(field.desc)) {
                            candidateString = new FieldRef(field.owner, field.name, field.desc);
                        }
                    }
                }
                if (candidateTable == null || candidateObject == null
                        || candidateString == null) continue;
                if (indexMethod != null) throw new IllegalStateException("multiple-index-methods");
                indexMethod = method;
                table = candidateTable;
                objectField = candidateObject;
                stringField = candidateString;
            }
            if (indexMethod == null) throw new IllegalStateException("index-method");
            int[] offsets = offsets(table);
            TableValues values = tableValues(owner, objectField, stringField);
            return new ResolverModel(owner.name, values.symbols, values.decoded, offsets,
                    SelectorModel.extract(owner));
        }

        MemberTarget resolve(String selector, long first, long second) {
            if (selector == null || selector.isEmpty()) {
                throw new IllegalArgumentException("empty-selector");
            }
            int index = index(first, second);
            String symbol = decode(index, mixed(first, second));
            try {
            String kind = selectors.kind(selector.charAt(0));
            if (SelectorModel.isFieldKind(kind)) {
                String[] parts = symbol.split("\b", -1);
                if (parts.length != 3) throw new IllegalStateException("field-symbol-parts="
                        + parts.length);
                TypeRef ownerType = classToken(parts[0]);
                TypeRef fieldType = classToken(parts[2]);
                return new MemberTarget(index, kind, ownerType.internalName(), parts[1],
                        fieldType.descriptor);
                }
                List<String> parts = new ArrayList<>(Arrays.asList(symbol.split("\b", -1)));
                if (!parts.isEmpty() && parts.get(parts.size() - 1).isEmpty()) {
                    parts.remove(parts.size() - 1);
                }
                if (parts.size() < 3) throw new IllegalStateException("method-symbol-parts="
                        + parts.size());
                TypeRef ownerType = classToken(parts.get(0));
                String name = parts.get(1);
                TypeRef returnType = classToken(parts.get(parts.size() - 1));
                StringBuilder descriptor = new StringBuilder("(");
                for (int i = 2; i < parts.size() - 1; i++) {
                    descriptor.append(classToken(parts.get(i)).descriptor);
                }
                descriptor.append(')').append(returnType.descriptor);
            return new MemberTarget(index, kind, ownerType.internalName(), name,
                    descriptor.toString());
            } catch (Throwable failure) {
                throw new IllegalStateException("member-symbol=" + printable(symbol)
                        + "; " + shortReason(failure));
            }
        }

        private int index(long first, long second) {
            long value = mixed(first, second);
            int index = (int) (value >>> 46);
            if (index < 0 || index >= symbols.length) {
                throw new IllegalStateException("symbol-index=" + index + "/" + symbols.length);
            }
            return index;
        }

        private static long mixed(long first, long second) {
            return first ^ (second << 48 | second);
        }

        private String decode(int index, long value) {
            if (decoded[index] != null) return decoded[index];
            Object raw = symbols[index];
            if (!(raw instanceof String)) {
                throw new IllegalStateException("non-string-symbol=" + index);
            }
            int base = offsets[(int) (value >>> 42 & 63L)];
            int[] keys = new int[6];
            for (int i = 0; i < keys.length; i++) {
                int key = (int) (value >>> (7 * (5 - i)) & 127L) - base;
                keys[i] = key < 0 ? key + 128 : key;
            }
            char[] chars = ((String) raw).toCharArray();
            for (int i = 0; i < chars.length; i++) {
                int key = keys[i % keys.length];
                if (key == 0) break;
                chars[i] = (char) (chars[i] ^ key);
            }
            return decoded[index] = new String(chars);
        }

        private TypeRef classToken(String token) {
            long value;
            try {
                value = Long.parseLong(token, 36);
            } catch (NumberFormatException failure) {
                throw new IllegalStateException("class-token=" + printable(token));
            }
            long mixed = mixed(value, 0L);
            int index = (int) (mixed >>> 46);
            if (index < 0 || index >= symbols.length) {
                throw new IllegalStateException("class-token=" + printable(token)
                        + ",index=" + index + "/" + symbols.length);
            }
            Object raw = symbols[index];
            if (raw instanceof TypeRef) return (TypeRef) raw;
            String name = decode(index, mixed(value, 0L));
            return TypeRef.reference(name);
        }
    }

    static final class MemberTarget {
        final int index;
        final String kind;
        final String owner;
        final String name;
        final String desc;

        MemberTarget(int index, String kind, String owner, String name, String desc) {
            this.index = index;
            this.kind = kind;
            this.owner = owner;
            this.name = name;
            this.desc = desc;
        }

        boolean isField() {
            return SelectorModel.isFieldKind(kind);
        }

        String handleDescriptor() {
            Type ownerType = Type.getObjectType(owner);
            if (!isField()) {
                Type method = Type.getMethodType(desc);
                if ("INVOKESTATIC".equals(kind)) return desc;
                Type[] declared = method.getArgumentTypes();
                Type[] arguments = new Type[declared.length + 1];
                arguments[0] = ownerType;
                System.arraycopy(declared, 0, arguments, 1, declared.length);
                return Type.getMethodDescriptor(method.getReturnType(), arguments);
            }
            Type fieldType = Type.getType(desc);
            if ("GETSTATIC".equals(kind)) {
                return Type.getMethodDescriptor(fieldType);
            }
            if ("PUTSTATIC".equals(kind)) {
                return Type.getMethodDescriptor(Type.VOID_TYPE, fieldType);
            }
            if ("GETFIELD".equals(kind)) {
                return Type.getMethodDescriptor(fieldType, ownerType);
            }
            return Type.getMethodDescriptor(Type.VOID_TYPE, ownerType, fieldType);
        }
    }

    /** Selector characters are randomized per class, so recover them from the resolver. */
    static final class SelectorModel {
        private static final String LOOKUP = "java/lang/invoke/MethodHandles$Lookup";
        private final Map<Character, String> explicitKinds;
        private final Set<Character> fieldSelectors;

        SelectorModel(Map<Character, String> explicitKinds,
                      Set<Character> fieldSelectors) {
            this.explicitKinds = explicitKinds;
            this.fieldSelectors = fieldSelectors;
        }

        static SelectorModel extract(ClassNode owner) {
            MethodNode resolver = null;
            for (MethodNode method : owner.methods) {
                int lookupFactories = 0;
                for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
                     insn = insn.getNext()) {
                    if (insn instanceof MethodInsnNode
                            && LOOKUP.equals(((MethodInsnNode) insn).owner)
                            && lookupKind(((MethodInsnNode) insn).name) != null) {
                        lookupFactories++;
                    }
                }
                if (lookupFactories < 7) continue;
                if (resolver != null) {
                    throw new IllegalStateException("multiple-member-resolvers");
                }
                resolver = method;
            }
            if (resolver == null) throw new IllegalStateException("member-resolver");

            int selectorVar = selectorVariable(resolver);
            Set<Character> fieldSelectors = fieldSelectors(resolver, selectorVar);
            Map<Character, String> kinds = new LinkedHashMap<>();
            for (AbstractInsnNode insn = resolver.instructions.getFirst(); insn != null;
                 insn = insn.getNext()) {
                if (!(insn instanceof MethodInsnNode)) continue;
                MethodInsnNode call = (MethodInsnNode) insn;
                if (!LOOKUP.equals(call.owner)) continue;
                String kind = lookupKind(call.name);
                if (kind == null || "PUTSTATIC".equals(kind)
                        || "INVOKESPECIAL".equals(kind)) continue;
                Character selector = nearestSelectorComparison(call, selectorVar);
                if (selector == null) {
                    throw new IllegalStateException("selector-for-" + call.name);
                }
                String previous = kinds.put(selector, kind);
                if (previous != null && !previous.equals(kind)) {
                    throw new IllegalStateException("selector-kind-conflict=" + (int) selector);
                }
            }
            Set<Character> unmappedFields = new LinkedHashSet<>(fieldSelectors);
            unmappedFields.removeAll(kinds.keySet());
            if (unmappedFields.size() != 1) {
                throw new IllegalStateException("unmapped-field-selectors=" + unmappedFields.size());
            }
            kinds.put(unmappedFields.iterator().next(), "PUTSTATIC");
            requireKind(kinds, "GETFIELD");
            requireKind(kinds, "PUTFIELD");
            requireKind(kinds, "GETSTATIC");
            requireKind(kinds, "PUTSTATIC");
            requireKind(kinds, "INVOKEVIRTUAL");
            requireKind(kinds, "INVOKESTATIC");
            return new SelectorModel(kinds, fieldSelectors);
        }

        String kind(char selector) {
            String explicit = explicitKinds.get(selector);
            if (explicit != null) return explicit;
            if (fieldSelectors.contains(selector)) {
                throw new IllegalStateException("unmapped-field-selector=" + (int) selector);
            }
            return "INVOKESPECIAL";
        }

        static boolean isFieldKind(String kind) {
            return "GETFIELD".equals(kind) || "PUTFIELD".equals(kind)
                    || "GETSTATIC".equals(kind) || "PUTSTATIC".equals(kind);
        }

        private static int selectorVariable(MethodNode resolver) {
            for (AbstractInsnNode insn = resolver.instructions.getFirst(); insn != null;
                 insn = insn.getNext()) {
                if (!(insn instanceof MethodInsnNode)) continue;
                MethodInsnNode call = (MethodInsnNode) insn;
                if (!"java/lang/String".equals(call.owner) || !"charAt".equals(call.name)
                        || !"(I)C".equals(call.desc)) continue;
                AbstractInsnNode store = nextCode(call);
                if (store instanceof VarInsnNode && store.getOpcode() == Opcodes.ISTORE) {
                    return ((VarInsnNode) store).var;
                }
            }
            throw new IllegalStateException("selector-variable");
        }

        private static Set<Character> fieldSelectors(MethodNode resolver, int selectorVar) {
            Set<Character> result = new LinkedHashSet<>();
            for (AbstractInsnNode insn = resolver.instructions.getFirst(); insn != null;
                 insn = insn.getNext()) {
                if (insn instanceof MethodInsnNode
                        && "(JJ)Ljava/lang/reflect/Field;".equals(
                        ((MethodInsnNode) insn).desc)) {
                    break;
                }
                if (!(insn instanceof JumpInsnNode)) continue;
                int opcode = insn.getOpcode();
                if (opcode != Opcodes.IF_ICMPEQ && opcode != Opcodes.IF_ICMPNE) continue;
                Character value = selectorComparison((JumpInsnNode) insn, selectorVar);
                if (value != null) result.add(value);
            }
            if (result.size() != 4) {
                throw new IllegalStateException("field-selectors=" + result.size());
            }
            return result;
        }

        private static Character nearestSelectorComparison(AbstractInsnNode call,
                                                            int selectorVar) {
            int examined = 0;
            for (AbstractInsnNode insn = previousCode(call); insn != null && examined < 24;
                 insn = previousCode(insn), examined++) {
                if (!(insn instanceof JumpInsnNode)) continue;
                int opcode = insn.getOpcode();
                if (opcode != Opcodes.IF_ICMPEQ && opcode != Opcodes.IF_ICMPNE) continue;
                Character value = selectorComparison((JumpInsnNode) insn, selectorVar);
                if (value != null) return value;
            }
            return null;
        }

        private static Character selectorComparison(JumpInsnNode branch, int selectorVar) {
            AbstractInsnNode right = previousCode(branch);
            AbstractInsnNode left = previousCode(right);
            Integer rightConstant = intConstant(right);
            Integer leftConstant = intConstant(left);
            if (isSelectorLoad(left, selectorVar) && rightConstant != null) {
                return character(rightConstant);
            }
            if (leftConstant != null && isSelectorLoad(right, selectorVar)) {
                return character(leftConstant);
            }
            return null;
        }

        private static boolean isSelectorLoad(AbstractInsnNode insn, int variable) {
            return insn instanceof VarInsnNode && insn.getOpcode() == Opcodes.ILOAD
                    && ((VarInsnNode) insn).var == variable;
        }

        private static Character character(int value) {
            if (value < Character.MIN_VALUE || value > Character.MAX_VALUE) {
                throw new IllegalStateException("selector-out-of-range=" + value);
            }
            return (char) value;
        }

        private static String lookupKind(String name) {
            if ("findGetter".equals(name)) return "GETFIELD";
            if ("findSetter".equals(name)) return "PUTFIELD";
            if ("findStaticGetter".equals(name)) return "GETSTATIC";
            if ("findStaticSetter".equals(name)) return "PUTSTATIC";
            if ("findVirtual".equals(name)) return "INVOKEVIRTUAL";
            if ("findStatic".equals(name)) return "INVOKESTATIC";
            if ("findSpecial".equals(name)) return "INVOKESPECIAL";
            return null;
        }

        private static void requireKind(Map<Character, String> kinds, String kind) {
            if (!kinds.containsValue(kind)) {
                throw new IllegalStateException("missing-selector-kind=" + kind);
            }
        }
    }

    static final class ConversionModel {
        final boolean compatible;
        final List<String> argumentConversions;
        final String returnConversion;
        final String reason;

        ConversionModel(boolean compatible, List<String> argumentConversions,
                        String returnConversion, String reason) {
            this.compatible = compatible;
            this.argumentConversions = argumentConversions;
            this.returnConversion = returnConversion;
            this.reason = reason;
        }

        static ConversionModel between(String callSiteDescriptor,
                                       String targetHandleDescriptor) {
            try {
                Type callSite = Type.getMethodType(callSiteDescriptor);
                Type target = Type.getMethodType(targetHandleDescriptor);
                Type[] sources = callSite.getArgumentTypes();
                Type[] destinations = target.getArgumentTypes();
                if (sources.length != destinations.length) {
                    return new ConversionModel(false, Collections.<String>emptyList(), "",
                            "argument-count=" + sources.length + "/" + destinations.length);
                }
                List<String> arguments = new ArrayList<>();
                for (int i = 0; i < sources.length; i++) {
                    arguments.add(conversion(sources[i], destinations[i], false));
                }
                String returned = conversion(target.getReturnType(),
                        callSite.getReturnType(), true);
                return new ConversionModel(true, arguments, returned, "");
            } catch (RuntimeException failure) {
                return new ConversionModel(false, Collections.<String>emptyList(), "",
                        "descriptor=" + shortReason(failure));
            }
        }

        String argumentSummary() {
            if (argumentConversions.isEmpty()) return "<none>";
            StringBuilder out = new StringBuilder();
            for (int i = 0; i < argumentConversions.size(); i++) {
                if (i != 0) out.append(',');
                out.append(i).append(':').append(argumentConversions.get(i));
            }
            return out.toString();
        }

        private static String conversion(Type source, Type destination,
                                         boolean returned) {
            if (source.equals(destination)) return "exact:" + source.getDescriptor();
            if (returned && destination.getSort() == Type.VOID) {
                return "discard:" + source.getDescriptor() + "->V";
            }
            if (returned && source.getSort() == Type.VOID) {
                return "default-return:V->" + destination.getDescriptor();
            }
            boolean sourceReference = reference(source);
            boolean destinationReference = reference(destination);
            if (sourceReference && destinationReference) {
                return "reference-cast:" + source.getDescriptor() + "->"
                        + destination.getDescriptor();
            }
            if (sourceReference) {
                return "unbox:" + source.getDescriptor() + "->"
                        + destination.getDescriptor();
            }
            if (destinationReference) {
                return "box:" + source.getDescriptor() + "->"
                        + destination.getDescriptor();
            }
            return "primitive-cast:" + source.getDescriptor() + "->"
                    + destination.getDescriptor();
        }

        private static boolean reference(Type type) {
            return type.getSort() == Type.OBJECT || type.getSort() == Type.ARRAY;
        }
    }

    private static String stripTrailingKeys(String descriptor) {
        Type method = Type.getMethodType(descriptor);
        Type[] arguments = method.getArgumentTypes();
        if (arguments.length < 2
                || !Type.LONG_TYPE.equals(arguments[arguments.length - 2])
                || !Type.LONG_TYPE.equals(arguments[arguments.length - 1])) {
            throw new IllegalArgumentException("descriptor-without-trailing-JJ=" + descriptor);
        }
        return Type.getMethodDescriptor(method.getReturnType(),
                Arrays.copyOf(arguments, arguments.length - 2));
    }

    private static TableValues tableValues(ClassNode owner, FieldRef objectField,
                                           FieldRef stringField) {
        TableValues best = null;
        for (MethodNode method : owner.methods) {
            if (!"()V".equals(method.desc) || (method.access & Opcodes.ACC_STATIC) == 0) {
                continue;
            }
            TableValues values = interpretTableMethod(method, objectField, stringField);
            if (values == null) continue;
            if (best != null) throw new IllegalStateException("multiple-table-populators");
            best = values;
        }
        if (best == null) throw new IllegalStateException("table-populator");
        return best;
    }

    private static TableValues interpretTableMethod(MethodNode method,
                                                    FieldRef objectField,
                                                    FieldRef stringField) {
        Deque<Object> stack = new ArrayDeque<>();
        Map<Integer, Object> locals = new HashMap<>();
        Map<Integer, Object> raw = new LinkedHashMap<>();
        Map<Integer, String> decoded = new LinkedHashMap<>();
        int stores = 0;
        for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null;
             insn = insn.getNext()) {
            int opcode = insn.getOpcode();
            if (opcode < 0) continue;
            Integer integer = intConstant(insn);
            if (integer != null) {
                stack.push(integer);
            } else if (insn instanceof LdcInsnNode) {
                Object constant = ((LdcInsnNode) insn).cst;
                if (constant instanceof String) stack.push(constant);
                else if (constant instanceof Type) {
                    stack.push(TypeRef.fromDescriptor(((Type) constant).getDescriptor()));
                } else stack.push(Unknown.VALUE);
            } else if (insn instanceof FieldInsnNode && opcode == Opcodes.GETSTATIC) {
                FieldInsnNode field = (FieldInsnNode) insn;
                if (objectField.matches(field)) stack.push(new ArrayRef(false));
                else if (stringField.matches(field)) stack.push(new ArrayRef(true));
                else if ("TYPE".equals(field.name)
                        && "Ljava/lang/Class;".equals(field.desc)) {
                    stack.push(TypeRef.primitive(field.owner));
                } else stack.push(Unknown.VALUE);
            } else if (opcode == Opcodes.DUP) {
                if (stack.isEmpty()) return null;
                stack.push(stack.peek());
            } else if (insn instanceof VarInsnNode && opcode == Opcodes.ASTORE) {
                if (stack.isEmpty()) return null;
                locals.put(((VarInsnNode) insn).var, stack.pop());
            } else if (insn instanceof VarInsnNode && opcode == Opcodes.ALOAD) {
                stack.push(locals.containsKey(((VarInsnNode) insn).var)
                        ? locals.get(((VarInsnNode) insn).var) : Unknown.VALUE);
            } else if (opcode == Opcodes.CHECKCAST) {
                // The modeled value is unchanged.
            } else if (opcode == Opcodes.AASTORE) {
                if (stack.size() < 3) return null;
                Object value = stack.pop();
                Object index = stack.pop();
                Object array = stack.pop();
                if (!(array instanceof ArrayRef) || !(index instanceof Integer)) continue;
                if (((ArrayRef) array).strings) {
                    if (value instanceof String) decoded.put((Integer) index, (String) value);
                } else if (value instanceof String || value instanceof TypeRef) {
                    raw.put((Integer) index, value);
                    stores++;
                }
            } else if (opcode == Opcodes.RETURN) {
                break;
            } else {
                return null;
            }
        }
        if (stores == 0 || raw.isEmpty()) return null;
        int size = Collections.max(raw.keySet()) + 1;
        Object[] symbols = new Object[size];
        String[] names = new String[size];
        for (Map.Entry<Integer, Object> entry : raw.entrySet()) {
            if (entry.getKey() < 0 || entry.getKey() >= size) return null;
            symbols[entry.getKey()] = entry.getValue();
            if (entry.getValue() instanceof TypeRef) {
                names[entry.getKey()] = ((TypeRef) entry.getValue()).className;
            }
        }
        for (Map.Entry<Integer, String> entry : decoded.entrySet()) {
            if (entry.getKey() >= 0 && entry.getKey() < size) names[entry.getKey()] = entry.getValue();
        }
        for (Object symbol : symbols) if (symbol == null) return null;
        return new TableValues(symbols, names);
    }

    private static int[] offsets(TableSwitchInsnNode table) {
        int[] result = new int[64];
        for (int i = 0; i < 63; i++) {
            Integer value = intConstant(nextCode(table.labels.get(i)));
            if (value == null) throw new IllegalStateException("switch-offset=" + i);
            result[i] = value;
        }
        Integer fallback = intConstant(nextCode(table.dflt));
        if (fallback == null) throw new IllegalStateException("switch-default");
        result[63] = fallback;
        boolean[] seen = new boolean[64];
        for (int value : result) {
            if (value < 0 || value >= 64 || seen[value]) {
                throw new IllegalStateException("switch-offset-permutation");
            }
            seen[value] = true;
        }
        return result;
    }

    private static final class TableValues {
        final Object[] symbols;
        final String[] decoded;

        TableValues(Object[] symbols, String[] decoded) {
            this.symbols = symbols;
            this.decoded = decoded;
        }
    }

    private static final class ArrayRef {
        final boolean strings;

        ArrayRef(boolean strings) {
            this.strings = strings;
        }
    }

    private enum Unknown { VALUE }

    private static final class FieldRef {
        final String owner;
        final String name;
        final String desc;

        FieldRef(String owner, String name, String desc) {
            this.owner = owner;
            this.name = name;
            this.desc = desc;
        }

        boolean matches(FieldInsnNode field) {
            return owner.equals(field.owner) && name.equals(field.name)
                    && desc.equals(field.desc);
        }
    }

    private static final class TypeRef {
        final String descriptor;
        final String className;

        TypeRef(String descriptor, String className) {
            this.descriptor = descriptor;
            this.className = className;
        }

        static TypeRef primitive(String wrapper) {
            if ("java/lang/Void".equals(wrapper)) return new TypeRef("V", wrapper);
            if ("java/lang/Boolean".equals(wrapper)) return new TypeRef("Z", wrapper);
            if ("java/lang/Byte".equals(wrapper)) return new TypeRef("B", wrapper);
            if ("java/lang/Character".equals(wrapper)) return new TypeRef("C", wrapper);
            if ("java/lang/Short".equals(wrapper)) return new TypeRef("S", wrapper);
            if ("java/lang/Integer".equals(wrapper)) return new TypeRef("I", wrapper);
            if ("java/lang/Long".equals(wrapper)) return new TypeRef("J", wrapper);
            if ("java/lang/Float".equals(wrapper)) return new TypeRef("F", wrapper);
            if ("java/lang/Double".equals(wrapper)) return new TypeRef("D", wrapper);
            throw new IllegalArgumentException("primitive-wrapper=" + wrapper);
        }

        static TypeRef fromDescriptor(String descriptor) {
            Type type = Type.getType(descriptor);
            if (type.getSort() == Type.VOID || type.getSort() >= Type.BOOLEAN
                    && type.getSort() <= Type.DOUBLE) {
                return new TypeRef(descriptor, type.getClassName().replace('.', '/'));
            }
            return new TypeRef(descriptor, type.getClassName().replace('.', '/'));
        }

        static TypeRef reference(String name) {
            String normalized = name.replace('.', '/');
            if (normalized.startsWith("[")) {
                return new TypeRef(normalized.replace('.', '/'), normalized);
            }
            return new TypeRef("L" + normalized + ";", normalized);
        }

        String internalName() {
            Type type = Type.getType(descriptor);
            if (type.getSort() != Type.OBJECT) {
                throw new IllegalStateException("member-owner=" + descriptor);
            }
            return type.getInternalName();
        }
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
        if (insn instanceof IntInsnNode
                && (opcode == Opcodes.BIPUSH || opcode == Opcodes.SIPUSH)) {
            return ((IntInsnNode) insn).operand;
        }
        return insn instanceof LdcInsnNode && ((LdcInsnNode) insn).cst instanceof Integer
                ? (Integer) ((LdcInsnNode) insn).cst : null;
    }

    private static Long longConstant(AbstractInsnNode insn) {
        if (insn == null) return null;
        if (insn.getOpcode() == Opcodes.LCONST_0) return 0L;
        if (insn.getOpcode() == Opcodes.LCONST_1) return 1L;
        return insn instanceof LdcInsnNode && ((LdcInsnNode) insn).cst instanceof Long
                ? (Long) ((LdcInsnNode) insn).cst : null;
    }

    private static String row(Object... cells) {
        StringBuilder result = new StringBuilder();
        for (int i = 0; i < cells.length; i++) {
            if (i != 0) result.append('\t');
            if (cells[i] != null) result.append(printable(String.valueOf(cells[i])));
        }
        return result.toString();
    }

    private static String printable(String value) {
        if (value == null) return "";
        StringBuilder result = new StringBuilder();
        for (int i = 0; i < value.length(); i++) {
            char c = value.charAt(i);
            if (c == '\t' || c == '\r' || c == '\n' || c < 32 || c > 126) {
                result.append(String.format(Locale.ROOT, "\\u%04X", (int) c));
            } else {
                result.append(c);
            }
        }
        return result.toString();
    }

    private static String shortReason(Throwable failure) {
        String message = failure.getMessage();
        if (message == null || message.isEmpty()) message = failure.getClass().getSimpleName();
        return message.length() <= 180 ? message : message.substring(0, 180);
    }
}
