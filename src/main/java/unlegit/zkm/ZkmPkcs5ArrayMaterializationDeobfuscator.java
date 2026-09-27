package unlegit.zkm;

import java.nio.file.Path;
import java.nio.file.Paths;

/**
 * Entry point for CFG-closed PKCS5 String-array materialization whose
 * plaintext array escapes into an arbitrary preserved business continuation.
 */
public final class ZkmPkcs5ArrayMaterializationDeobfuscator {
    private ZkmPkcs5ArrayMaterializationDeobfuscator() {
    }

    public static void main(String[] args) throws Exception {
        if (args.length < 2 || args.length > 4) {
            System.err.println("usage: ZkmPkcs5ArrayMaterializationDeobfuscator "
                    + "<input.jar> <report-dir> [output.jar] [authority.jar]");
            System.exit(2);
        }
        Path output = args.length >= 3 ? Paths.get(args[2]) : null;
        Path authority = args.length == 4 ? Paths.get(args[3]) : null;
        ZkmDirectStringArrayDeobfuscator.Summary summary =
                ZkmDirectStringArrayDeobfuscator
                        .deobfuscateFlexibleMaterialization(
                                Paths.get(args[0]), Paths.get(args[1]),
                                output, authority);
        System.out.println("classes=" + summary.parsedClasses
                + " candidates=" + summary.pkcs5ClinitClasses
                + " proven=" + summary.provenCandidates
                + " strings=" + summary.provenStrings
                + " changed=" + summary.changedClasses
                + " rollbacks=" + summary.classRollbacks
                + " residual_pkcs5="
                + summary.outputPkcs5ClinitClasses
                + " output_committed=" + summary.outputCommitted);
    }
}
