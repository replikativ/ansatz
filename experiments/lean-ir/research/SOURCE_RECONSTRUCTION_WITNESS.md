# Exporting the frontend visibility witness

`SourceReconstructionWitness.isExporting` reads the actual
`Lean.Environment.isExporting` field through pinned Lean compilation. It fills a
missing accessor in the existing producer catalogue; it does not authorize
imported source execution, establish a checked association, or issue an import
receipt. No hosted JVM admission has been performed for this artifact.

The [source](../lean/SourceReconstructionWitness.lean) imports only
`Lean.Environment`, which directly owns the type and field. The
[exact exported IR](../fixtures/source-reconstruction-witness.jsonl) contains a
manifest and two ordinary local declarations, with no initializer actions:

| Entry | Parameter | Result | Dependencies |
| --- | --- | --- | --- |
| `SourceReconstructionWitness.isExporting` | borrowed `object` Environment | `uint8` Bool | none |
| `SourceReconstructionWitness.isExporting._boxed` | owned `object` Environment | `tagged` boxed Bool | the unboxed entry |

These are measured IR types and borrow flags. In particular the boxed adapter
consumes its input; callers retaining an Environment must retain their owner
before using that adapter. The source does not guess a runtime field offset.
Future admission must authenticate this exact closure and the pinned ABI, even
though its emitted body is small.

The [native export record](../measurements/source-reconstruction-witness-native-export.json)
retains source, exporter, generated build inputs, installed toolchain/olean
hashes, explicit environment, actual child mappings, guard receipts and earlier
failed attempts. Lean is statically linked into the existing exporter; there
were no dynamic Lean libraries in its ELF dependencies or observed child
mappings. Hashes of matching installed static archives are context, not proof of
reproducible historical linkage. The legacy manifest reports Lean version and
runtime ABI but no commit, so explicit toolchain/source/binary pins remain part
of host provenance.

## Repeating the native export

From `experiments/lean-ir`, supply an existing exporter through the explicit
`ANSATZ_IR_EXPORTER` path. For this exact receipt its SHA-256 must be
`0b0344058631b8c3dc18a8a1a600f8100611eaf49c3b4ee5ad18a121651e736e`.
The existing `scripts/build-exporter.sh` documents how a new exporter is built
with the pinned compiler. A rebuild has its own binary hash and requires a new
provenance record; do not relabel it as the captured binary.

Resolve and verify the selected toolchain explicitly, then use only that prefix
for `.olean` lookup. Default `lean` selection is insufficient: an older default
can read incompatible Init headers even when the exporter itself is pinned.

```sh
leanir_toolchain=leanprover/lean4:v4.33.1
leanir_prefix="$(lean +"$leanir_toolchain" --print-prefix)"
test "$("$leanir_prefix/bin/lean" --githash)" = 819816b2e0a3bf405af45ae5c7af2491d8f5bee6
"$leanir_prefix/bin/lean" --version
sha256sum "$ANSATZ_IR_EXPORTER"
readelf -d "$ANSATZ_IR_EXPORTER"
```

Use a process-group resource guard around the following command: the successful
receipt used a 768 MiB RSS limit, 120 seconds, and a 1 GiB system-available-memory
floor. Create a fresh output directory and preserve failure artifacts. Set a
minimal child environment rather than inheriting toolchain or loader overrides:

```sh
test ! -e target/reconstruction-witness-repeat
mkdir -p target/reconstruction-witness-repeat
env -i PATH="$leanir_prefix/bin:/usr/bin:/bin" \
  LEAN_SYSROOT="$leanir_prefix" LEAN_PATH="$leanir_prefix/lib/lean" \
  LD_LIBRARY_PATH="$leanir_prefix/lib/lean" LEAN_NUM_THREADS=1 LANG=C.UTF-8 \
  "$ANSATZ_IR_EXPORTER" --source lean/SourceReconstructionWitness.lean \
  --closure --local SourceReconstructionWitness \
  > target/reconstruction-witness-repeat/SourceReconstructionWitness.source.jsonl \
  2> target/reconstruction-witness-repeat/stderr
```

Check the actual manifest's version, target, source module and empty action list;
require exactly the two declarations and dependency closure above, including
`sourceLocal=true`, exact borrow flags and result types. Compare output bytes
with the checked-in fixture and record its digest; this receipt's IR SHA-256 is
`9d067007df4fa3a7a0d019009a76244cd0988a001f2a407f54660d510a2c078f`.
Record guard outcome, stderr and actual exporter/library provenance before
considering an artifact for a hosted profile.

Two prior attempts used the broader `import Lean` and stopped at their 512 MiB
and 768 MiB RSS guards. They are retained as failed diagnostics. Narrowing the
source dependency succeeded under the same 768 MiB limit in 3.01 seconds for the
whole guarded preflight/export, with 326,545,408 bytes peak group RSS. The exporter
subprocess itself took about 0.775 seconds. These are export receipts, not a
comparison with Clojure or a hosted runtime benchmark.
