# ZKM 27 Full Deobfuscator

Static, fail-closed undo for Zelix KlassMaster 27 archives.

Input classes are never defined, loaded, initialized, or reflected on. Every
class is parsed as an ASM `ClassNode`. A mutation is published only after
`CheckClassAdapter`, `BasicVerifier`, and the stage postcondition pass.

Developed with [crush-plus](https://github.com/unleg1t/crush-plus).

Made with love from the authors of the original ZKM deobfuscation work, the
flowdeobf toolkit, **unlegit**, and Crush.

## What it undoes

| Stage | ZKM transform |
|---|---|
| XOR string tables / rolling-XOR lookup | `encryptStringLiterals=normal` and `(II)` helpers |
| XOR int / long packed tables | `encryptIntegerConstants` / `encryptLongConstants` (XOR) |
| DES string / integer / long indy | enhanced / aggressive DES templates |
| Member invokedynamic | `obfuscateReferences` (identity / mapped) |
| Long-key fold | class-long-key bootstrap |
| Opaque predicates | once-written sentinel fields |
| Exception identity / dummy handlers | `exceptionObfuscation` |
| Parameter descriptors | `obfuscateParameters` (report / recover) |
| Control-flow cleanup | residual guards, shared tails, islands |
| Changelog rename | reverse `changeLogFileOut` |

Not inverted: `trim`, names without a changelog, and shapes the existing
proofs refuse (guessed opaque predicates, general switch flattening).

A lone ZKM jar is enough for crypto / flow / exceptions. Original identifiers
need the changelog ZKM wrote at obfuscation time.

## Requirements

- JDK 8 or newer to **run** the JAR
- JDK 21 (or any JDK that can target 8) to **build**

## Build

```bash
./gradlew shadowJar
```

Output: `build/libs/zkm27-full-deobfuscator-1.0.0.jar`

## Run (GUI)

Double-click the JAR, or:

```bash
java -jar build/libs/zkm27-full-deobfuscator-1.0.0.jar
```

Pick the obfuscated input, the output path, and optionally a ZKM changelog.
The report directory defaults next to the output.

## Run (CLI)

```bash
java -jar build/libs/zkm27-full-deobfuscator-1.0.0.jar \
  input.jar report-dir [output.jar] \
  [--changelog ChangeLog.txt] \
  [--runtime-authority pre-removal.jar] \
  [--runtime-semantic-overrides evidence.tsv]
```

No arguments opens the Swing GUI. With arguments, the same pipeline runs
headless.

## Credits

- **unlegit** — this packaging, GUI, full-pipeline wiring, XOR / opaque /
  exception / changelog stages
- **Crush**, via [crush-plus](https://github.com/unleg1t/crush-plus) — pair
  programming on the pipeline and the desktop app
- **OpenVapeCN / NoHackClient** — `zkm-flowdeobf` DES, indy, long-key, and
  control-flow proofs this project is built on
- Everyone who recovered, renamed, and documented Zelix KlassMaster 27 so
  these undoes could be written against real transformers instead of guesses

Zelix KlassMaster is a product of Zelix Pty Ltd. This project is not
affiliated with, approved by, or associated with Zelix.

## License

MIT. See [LICENSE](LICENSE).
