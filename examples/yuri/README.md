# Yuri examples

These are the ZKM 27 test archives used while building the full deobfuscator.

| File | What it is |
|---|---|
| `yuri-original.jar` | Unobfuscated Yuri 1.8.9 client fat JAR (`Start` + `ddlc` + Minecraft/OptiFine) |
| `yuri-zkm27-obfuscated.jar` | Same archive after ZKM 27 (`obfuscateFlow=aggressive`, `exceptionObfuscation=heavy`, `encryptStringLiterals=enhanced`, integer/long encryption, rename). Only `ddlc` + `Start` were rewritten; `net` / assets stayed vanilla |
| `yuri-zkm27-changelog.txt` | ZKM `changeLogFileOut` from that run. Needed to restore original names |
| `yuri-deobfuscated.jar` | Output of this tool on the obfuscated JAR plus the changelog |

Replay:

```bash
java -jar build/libs/zkm27-full-deobfuscator-1.0.0.jar \
  examples/yuri/yuri-zkm27-obfuscated.jar \
  examples/yuri/report \
  examples/yuri/yuri-replay-deobf.jar \
  --changelog examples/yuri/yuri-zkm27-changelog.txt
```

Or open the GUI, pick the obfuscated JAR, the changelog, and an output path.

Yuri is a third-party Minecraft 1.8.9 client. These jars are fixtures, not a
redistribution of Zelix KlassMaster.
