package cn.openvape.flowdeobf;

import org.objectweb.asm.ClassReader;
import org.objectweb.asm.ClassWriter;
import org.objectweb.asm.Opcodes;
import org.objectweb.asm.tree.ClassNode;
import org.objectweb.asm.tree.MethodNode;
import org.objectweb.asm.tree.analysis.Analyzer;
import org.objectweb.asm.tree.analysis.BasicValue;
import org.objectweb.asm.tree.analysis.BasicVerifier;
import org.objectweb.asm.util.CheckClassAdapter;

/**
 * Isolated class rewrite transaction. The original bytes are never modified;
 * mutated bytes are exposed only after serialization, ASM structural checks,
 * BasicVerifier and a caller-supplied semantic postcondition all pass.
 */
public final class ZkmClassRewriteTransaction {
    private ZkmClassRewriteTransaction() {
    }

    public interface Mutation {
        void apply(ClassNode owner) throws Exception;
    }

    public interface Postcondition {
        void verify(ClassNode emittedOwner) throws Exception;
    }

    /** Allows an archive-aware ClassWriter while retaining the same gates. */
    public interface Emitter {
        byte[] emit(ClassNode owner) throws Exception;
    }

    public enum Stage {
        COMMITTED,
        PARSE,
        MUTATION,
        EMIT,
        VERIFY,
        POSTCONDITION
    }

    public static Result attempt(byte[] original, Mutation mutation,
                                 Postcondition postcondition) {
        return attempt(original, mutation, postcondition, new ComputeMaxsEmitter());
    }

    public static Result attempt(byte[] original, Mutation mutation,
                                 Postcondition postcondition, Emitter emitter) {
        if (original == null || original.length == 0) {
            throw new IllegalArgumentException("original class bytes are required");
        }
        if (mutation == null || postcondition == null || emitter == null) {
            throw new IllegalArgumentException("mutation, postcondition and emitter are required");
        }
        byte[] preserved = original.clone();
        ClassNode owner;
        try {
            owner = read(preserved);
        } catch (Throwable failure) {
            return Result.rollback(preserved, "", Stage.PARSE, failure);
        }
        String ownerName = owner.name;
        try {
            mutation.apply(owner);
        } catch (Throwable failure) {
            return Result.rollback(preserved, ownerName, Stage.MUTATION, failure);
        }
        byte[] emitted;
        try {
            emitted = emitter.emit(owner);
        } catch (Throwable failure) {
            return Result.rollback(preserved, ownerName, Stage.EMIT, failure);
        }
        try {
            verify(emitted);
        } catch (Throwable failure) {
            return Result.rollback(preserved, ownerName, Stage.VERIFY, failure);
        }
        try {
            postcondition.verify(read(emitted));
        } catch (Throwable failure) {
            return Result.rollback(preserved, ownerName, Stage.POSTCONDITION, failure);
        }
        return Result.commit(emitted, ownerName);
    }

    public static final class Result {
        private final boolean committed;
        private final byte[] bytes;
        private final String owner;
        private final Stage stage;
        private final String reason;

        private Result(boolean committed, byte[] bytes, String owner,
                       Stage stage, String reason) {
            this.committed = committed;
            this.bytes = bytes.clone();
            this.owner = owner;
            this.stage = stage;
            this.reason = reason;
        }

        private static Result commit(byte[] bytes, String owner) {
            return new Result(true, bytes, owner, Stage.COMMITTED, "COMMITTED");
        }

        private static Result rollback(byte[] original, String owner, Stage stage,
                                       Throwable failure) {
            String message = failure.getMessage();
            String reason = failure.getClass().getSimpleName()
                    + (message == null || message.isEmpty() ? "" : ": " + message);
            return new Result(false, original, owner, stage, reason);
        }

        public boolean isCommitted() {
            return committed;
        }

        /** Committed bytes, or an exact copy of the original bytes on rollback. */
        public byte[] bytes() {
            return bytes.clone();
        }

        public String owner() {
            return owner;
        }

        public Stage stage() {
            return stage;
        }

        public String reason() {
            return reason;
        }
    }

    private static final class ComputeMaxsEmitter implements Emitter {
        @Override
        public byte[] emit(ClassNode owner) {
            ClassWriter writer = new ClassWriter(ClassWriter.COMPUTE_MAXS);
            owner.accept(writer);
            return writer.toByteArray();
        }
    }

    private static ClassNode read(byte[] bytes) {
        ClassNode owner = new ClassNode(Opcodes.ASM9);
        new ClassReader(bytes).accept(owner, 0);
        return owner;
    }

    private static void verify(byte[] bytes) throws Exception {
        ClassReader reader = new ClassReader(bytes);
        reader.accept(new CheckClassAdapter(new ClassWriter(0), false), 0);
        ClassNode owner = read(bytes);
        for (MethodNode method : owner.methods) {
            if (method.instructions != null && method.instructions.size() != 0) {
                new Analyzer<BasicValue>(new BasicVerifier()).analyze(owner.name, method);
            }
        }
    }
}
