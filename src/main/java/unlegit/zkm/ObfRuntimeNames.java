package unlegit.zkm;

/**
 * Single source of truth for the target obfuscation runtime's internal names.
 *
 * <p>The defaults reproduce the internal names observed in the original analyzed
 * sample, so the deobfuscation passes behave identically when nothing is
 * overridden. To retarget the tool at another archive whose ZKM-style runtime
 * uses different class names, override the corresponding system property at JVM
 * launch, e.g. {@code -Dopenvape.runtime.state=com/example/State}. All names are
 * JVM internal form (slashes, no {@code .class}).
 */
public final class ObfRuntimeNames {

    private ObfRuntimeNames() {
    }

    /** Package prefix (internal form, trailing slash) shared by every runtime name. */
    public static final String PKG =
            System.getProperty("openvape.runtime.pkg", "gg/vape/runtime/obfuscation/");

    /** Concrete long-key state class. */
    public static final String STATE =
            PKG + System.getProperty("openvape.runtime.state", "ZkmLongKeyState");

    /** Long-key state interface implemented by {@link #STATE}. */
    public static final String STATE_INTERFACE =
            PKG + System.getProperty("openvape.runtime.stateInterface", "LongKeyState");

    /** Graph bootstrap class that seeds the long-key state model. */
    public static final String GRAPH_BOOTSTRAP =
            PKG + System.getProperty("openvape.runtime.graph", "ZkmLongKeyGraphBootstrap");

    /** Decrypted string-pair constants holder. */
    public static final String STRING_PAIR_CONSTANTS =
            PKG + System.getProperty("openvape.runtime.stringPair", "DecryptedStringPairConstants");

    /** {@link #STATE} as an archive entry name. */
    public static final String STATE_CLASS = STATE + ".class";

    /** {@link #GRAPH_BOOTSTRAP} as an archive entry name. */
    public static final String GRAPH_BOOTSTRAP_CLASS = GRAPH_BOOTSTRAP + ".class";

    /** Bootstrap factory descriptor {@code (JJLjava/lang/Object;)L<stateInterface>;}. */
    public static final String BOOTSTRAP_DESC =
            "(JJLjava/lang/Object;)L" + STATE_INTERFACE + ";";
}
