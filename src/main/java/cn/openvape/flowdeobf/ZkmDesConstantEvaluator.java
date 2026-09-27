package cn.openvape.flowdeobf;

import javax.crypto.Cipher;
import javax.crypto.SecretKey;
import javax.crypto.SecretKeyFactory;
import javax.crypto.spec.DESKeySpec;
import javax.crypto.spec.IvParameterSpec;
import java.nio.ByteBuffer;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

/**
 * Pure, provenance-aware evaluator for the DES constants used by ZKM.
 *
 * <p>This class has no ASM dependency and never defines or initializes an input
 * class. Template recognizers are responsible for proving where a key and a
 * ciphertext came from; this evaluator is responsible only for reproducing the
 * accepted DES semantics. A hypothesis is deliberately rejected so that a
 * guessed class key cannot silently become a rewrite.</p>
 */
public final class ZkmDesConstantEvaluator {
    private static final byte[] ZERO_IV = new byte[8];

    private ZkmDesConstantEvaluator() {
    }

    /** The two transformations observed in the sample. */
    public enum Transformation {
        CBC_PKCS5("DES/CBC/PKCS5Padding"),
        CBC_NO_PADDING("DES/CBC/NoPadding");

        private final String jceName;

        Transformation(String jceName) {
            this.jceName = jceName;
        }

        public String jceName() {
            return jceName;
        }
    }

    /** Whether the recognizer proved the key or merely proposed it. */
    public enum Confidence {
        PROVEN,
        HYPOTHESIS
    }

    /**
     * Immutable evidence attached to a key value.
     *
     * <p>Derived evidence retains its parents, which makes a report able to
     * distinguish a literal key from {@code classKey ^ mask} without coupling
     * the evaluator to a particular bytecode template.</p>
     */
    public static final class KeyProvenance {
        private final Confidence confidence;
        private final String kind;
        private final String source;
        private final List<KeyProvenance> parents;

        private KeyProvenance(Confidence confidence, String kind, String source,
                              List<KeyProvenance> parents) {
            if (confidence == null) throw new IllegalArgumentException("confidence");
            if (kind == null || kind.isEmpty()) throw new IllegalArgumentException("kind");
            if (source == null || source.isEmpty()) throw new IllegalArgumentException("source");
            this.confidence = confidence;
            this.kind = kind;
            this.source = source;
            this.parents = Collections.unmodifiableList(
                    new ArrayList<KeyProvenance>(parents));
        }

        public static KeyProvenance proven(String kind, String source) {
            return new KeyProvenance(Confidence.PROVEN, kind, source,
                    Collections.<KeyProvenance>emptyList());
        }

        public static KeyProvenance hypothesis(String kind, String source) {
            return new KeyProvenance(Confidence.HYPOTHESIS, kind, source,
                    Collections.<KeyProvenance>emptyList());
        }

        public static KeyProvenance derived(String kind, String source,
                                            KeyProvenance... parents) {
            if (parents == null || parents.length == 0) {
                throw new IllegalArgumentException("derived provenance needs a parent");
            }
            Confidence confidence = Confidence.PROVEN;
            for (KeyProvenance parent : parents) {
                if (parent == null) throw new IllegalArgumentException("null parent");
                if (parent.confidence != Confidence.PROVEN) {
                    confidence = Confidence.HYPOTHESIS;
                }
            }
            return new KeyProvenance(confidence, kind, source,
                    Arrays.asList(parents.clone()));
        }

        public Confidence confidence() {
            return confidence;
        }

        public String kind() {
            return kind;
        }

        public String source() {
            return source;
        }

        public List<KeyProvenance> parents() {
            return parents;
        }

        public String describe() {
            StringBuilder result = new StringBuilder();
            describe(result);
            return result.toString();
        }

        private void describe(StringBuilder output) {
            output.append(kind).append('(').append(source).append(')');
            if (!parents.isEmpty()) {
                output.append(" <- [");
                for (int index = 0; index < parents.size(); index++) {
                    if (index != 0) output.append(", ");
                    parents.get(index).describe(output);
                }
                output.append(']');
            }
        }
    }

    /** A concrete DES key and the proof that supplied it. */
    public static final class KeyMaterial {
        private final long value;
        private final KeyProvenance provenance;

        private KeyMaterial(long value, KeyProvenance provenance) {
            if (provenance == null) throw new IllegalArgumentException("provenance");
            this.value = value;
            this.provenance = provenance;
        }

        public static KeyMaterial proven(long value, String kind, String source) {
            return new KeyMaterial(value, KeyProvenance.proven(kind, source));
        }

        public static KeyMaterial hypothesis(long value, String kind, String source) {
            return new KeyMaterial(value, KeyProvenance.hypothesis(kind, source));
        }

        public KeyMaterial xor(long mask, String source) {
            String renderedMask = String.format("0x%016X", mask);
            return new KeyMaterial(value ^ mask, KeyProvenance.derived(
                    "XOR", source + " ^ " + renderedMask, provenance));
        }

        public long value() {
            return value;
        }

        public KeyProvenance provenance() {
            return provenance;
        }

        public boolean isProven() {
            return provenance.confidence() == Confidence.PROVEN;
        }
    }

    /** Immutable result retained by a recognizer until its rewrite commits. */
    public static final class Evaluation {
        private final Transformation transformation;
        private final KeyMaterial key;
        private final byte[] ciphertext;
        private final byte[] plaintext;

        private Evaluation(Transformation transformation, KeyMaterial key,
                           byte[] ciphertext, byte[] plaintext) {
            this.transformation = transformation;
            this.key = key;
            this.ciphertext = ciphertext.clone();
            this.plaintext = plaintext.clone();
        }

        public Transformation transformation() {
            return transformation;
        }

        public KeyMaterial key() {
            return key;
        }

        public byte[] ciphertext() {
            return ciphertext.clone();
        }

        public byte[] plaintext() {
            return plaintext.clone();
        }
    }

    public static Evaluation decrypt(Transformation transformation,
                                     KeyMaterial key, byte[] ciphertext)
            throws EvaluationException {
        if (transformation == null) throw new IllegalArgumentException("transformation");
        if (key == null) throw new IllegalArgumentException("key");
        if (!key.isProven()) {
            throw new EvaluationException("unproven-key: " + key.provenance().describe());
        }
        if (ciphertext == null || ciphertext.length == 0
                || (ciphertext.length & 7) != 0) {
            throw new EvaluationException("ciphertext is not a non-empty DES block sequence");
        }
        try {
            Cipher cipher = Cipher.getInstance(transformation.jceName());
            SecretKeyFactory factory = SecretKeyFactory.getInstance("DES");
            SecretKey secret = factory.generateSecret(
                    new DESKeySpec(longToBytes(key.value())));
            cipher.init(Cipher.DECRYPT_MODE, secret, new IvParameterSpec(ZERO_IV));
            return new Evaluation(transformation, key, ciphertext,
                    cipher.doFinal(ciphertext));
        } catch (Exception failure) {
            throw new EvaluationException("DES evaluation failed: "
                    + failure.getClass().getSimpleName() + ": "
                    + String.valueOf(failure.getMessage()), failure);
        }
    }

    public static long decryptLong(KeyMaterial key, long ciphertext)
            throws EvaluationException {
        byte[] plaintext = decrypt(Transformation.CBC_NO_PADDING, key,
                longToBytes(ciphertext)).plaintext();
        return bytesToLong(plaintext);
    }

    /** The integer decryptor returns bytes 4..7 of the decrypted DES block. */
    public static int decryptLowInt(KeyMaterial key, long ciphertext)
            throws EvaluationException {
        byte[] plaintext = decrypt(Transformation.CBC_NO_PADDING, key,
                longToBytes(ciphertext)).plaintext();
        return ByteBuffer.wrap(plaintext).getInt(4);
    }

    public static String decryptZkmString(KeyMaterial key, String ciphertext)
            throws EvaluationException {
        byte[] encrypted;
        try {
            encrypted = latin1Bytes(ciphertext);
        } catch (IllegalArgumentException failure) {
            throw new EvaluationException(failure.getMessage(), failure);
        }
        return decodeZkmBmp(decrypt(Transformation.CBC_PKCS5, key,
                encrypted).plaintext());
    }

    /** Decrypts a packed sequence of fixed eight-byte NoPadding blocks. */
    public static List<Long> decryptPackedLongs(KeyMaterial key, String packed)
            throws EvaluationException {
        byte[] input;
        try {
            input = latin1Bytes(packed);
        } catch (IllegalArgumentException failure) {
            throw new EvaluationException(failure.getMessage(), failure);
        }
        if (input.length == 0 || (input.length & 7) != 0) {
            throw new EvaluationException("packed long table is not DES-block aligned");
        }
        List<Long> result = new ArrayList<Long>(input.length / 8);
        for (int offset = 0; offset < input.length; offset += 8) {
            byte[] block = Arrays.copyOfRange(input, offset, offset + 8);
            result.add(bytesToLong(decrypt(Transformation.CBC_NO_PADDING,
                    key, block).plaintext()));
        }
        return Collections.unmodifiableList(result);
    }

    /**
     * Decrypts the ZKM packed string format: one encrypted chunk followed by a
     * character containing the length of the next encrypted chunk.
     */
    public static List<String> decryptPackedStrings(KeyMaterial key, String packed,
                                                    int initialLength)
            throws EvaluationException {
        if (packed == null || packed.isEmpty()) {
            throw new EvaluationException("empty packed string table");
        }
        List<String> result = new ArrayList<String>();
        int cursor = 0;
        int length = initialLength;
        while (cursor < packed.length()) {
            if (length <= 0 || (length & 7) != 0
                    || cursor + length > packed.length()) {
                throw new EvaluationException("invalid packed boundary " + cursor
                        + "+" + length + "/" + packed.length());
            }
            result.add(decryptZkmString(key,
                    packed.substring(cursor, cursor + length)));
            cursor += length;
            if (cursor == packed.length()) break;
            length = packed.charAt(cursor++);
        }
        if (cursor != packed.length() || result.isEmpty()) {
            throw new EvaluationException("incomplete packed string table");
        }
        return Collections.unmodifiableList(result);
    }

    public static byte[] longToBytes(long value) {
        return ByteBuffer.allocate(8).putLong(value).array();
    }

    public static long bytesToLong(byte[] bytes) {
        if (bytes == null || bytes.length != 8) {
            throw new IllegalArgumentException("a DES long must contain exactly eight bytes");
        }
        return ByteBuffer.wrap(bytes).getLong();
    }

    public static byte[] latin1Bytes(String value) {
        if (value == null) throw new IllegalArgumentException("null Latin-1 value");
        byte[] result = new byte[value.length()];
        for (int index = 0; index < value.length(); index++) {
            char character = value.charAt(index);
            if (character > 0xff) {
                throw new IllegalArgumentException("non-Latin-1 character at " + index);
            }
            result[index] = (byte) character;
        }
        return result;
    }

    public static String bytesToLatin1(byte[] value) {
        if (value == null) throw new IllegalArgumentException("null byte value");
        char[] result = new char[value.length];
        for (int index = 0; index < value.length; index++) {
            result[index] = (char) (value[index] & 0xff);
        }
        return new String(result);
    }

    /** Exact BMP decoder implemented by the accepted ZKM helper shape. */
    public static String decodeZkmBmp(byte[] bytes) {
        if (bytes == null) throw new IllegalArgumentException("bytes");
        char[] chars = new char[bytes.length];
        int output = 0;
        for (int index = 0; index < bytes.length; index++) {
            int value = bytes[index] & 0xff;
            if (value < 192) {
                chars[output++] = (char) value;
            } else if (value < 224) {
                char decoded = (char) ((value & 0x1f) << 6);
                value = bytes[++index];
                chars[output++] = (char) (decoded | (value & 0x3f));
            } else if (index < bytes.length - 2) {
                char decoded = (char) ((value & 0x0f) << 12);
                value = bytes[++index];
                decoded = (char) (decoded | ((value & 0x3f) << 6));
                value = bytes[++index];
                chars[output++] = (char) (decoded | (value & 0x3f));
            }
        }
        return new String(chars, 0, output);
    }

    public static final class EvaluationException extends Exception {
        EvaluationException(String message) {
            super(message);
        }

        EvaluationException(String message, Throwable cause) {
            super(message, cause);
        }
    }
}
