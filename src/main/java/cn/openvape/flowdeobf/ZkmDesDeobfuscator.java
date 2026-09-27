package cn.openvape.flowdeobf;

/** Single public entry point for the archive-wide DES recovery pipeline. */
public final class ZkmDesDeobfuscator {
    private ZkmDesDeobfuscator() {
    }

    public static void main(String[] args) throws Exception {
        ZkmDesPipelineDeobfuscator.main(args);
    }
}
