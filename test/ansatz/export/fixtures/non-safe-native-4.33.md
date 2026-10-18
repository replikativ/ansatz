# Native unsafe/partial SCC replay fixture

`NativeNonSafeSCC.lean` constructs two mutual definition blocks through Lean's
actual checked `Environment.addDeclCore`. One uses unsafe safety, the other
partial safety. It checks that a safe theorem using either block is rejected.
The single `P : Prop` axiom is an explicit assumption. The fixture is about the
native kernel declaration API; it does not claim that these are the companions
produced by elaborating surface `partial def` syntax.

Capture is intentionally narrow: the exported dependency closure should contain
exactly that axiom and four definitions. `DefinitionVal.all` remains unchanged;
production replay derives recursion from actual body references.

Pinned producer: Lean **4.33.1**, commit
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`. The staged exporter is built by
`scripts/generate-bundle.py`; retain its `generation.json` exporter identities in
the companion capture manifest. No Mathlib import is involved.

Run from the Ansatz root, explicitly setting `lean_prefix` to the pinned
toolchain directory and `exporter` to the staged exporter binary:

```sh
scratch=target/non-safe-native-4.33
mkdir -p "$scratch"
export LEAN_SYSROOT="$lean_prefix"
export LEAN_PATH="$PWD/$scratch:$lean_prefix/lib/lean"
"$lean_prefix/bin/lean" -o "$scratch/NativeNonSafeSCC.olean" \
  test/ansatz/export/fixtures/NativeNonSafeSCC.lean
"$exporter" --export-unsafe NativeNonSafeSCC -- \
  NativeNonSafeSCC.unsafeLeft NativeNonSafeSCC.partialLeft \
  > "$scratch/non-safe-native-4.33.ndjson"
```

Compile first; failed native positive or negative assertions must prevent capture.
Verify the exact producer header and five-declaration inventory before copying the
NDJSON to this fixture directory. Record SHA256 for source, raw export, exporter
binary, and exporter source inventory; never refresh a capture to conceal a replay
failure. Native/JVM validation is deliberately scheduled separately from source
preparation when a resident frontend experiment occupies the memory budget.

The committed capture passed native compilation and both rejection assertions.
It contains **five declarations**, **1,110 bytes**, SHA256
`f418258c793b7a57da7484e6b68c83d519a3e0607b5cd1faa743677f16aab3a0`.
Exact producer/source identities and the capture memory guard are recorded in
`non-safe-native-4.33.provenance.json`. Production JVM replay has a separate
regression test in `ansatz.export.non-safe-replay-test`; native capture success
alone does not establish that this regression has run.
