# Java Lean runtime: IO coverage and implementation plan

Status: source-audited plan, not implemented Java runtime coverage. The reference
is Lean 4.33.1 commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`.
The sibling checkout has older local changes, so the audit read pinned Git blobs
rather than assuming its working files match the producer. No new frontend
image was loaded. The [compatibility corpus](LEAN_COMPATIBILITY_CORPUS.md)
supplies the first application gates.

## Compiled IO contract

Pinned [`Init/System/ST.lean`](https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/src/Init/System/ST.lean)
defines `ST` and `EST`; `Init/System/IO.lean` defines `BaseIO`, `EIO` and `IO`.
In captured executable IR:

| Type | Runtime representation |
| --- | --- |
| `BaseIO α` | Erased world argument and direct result `α` |
| `EIO ε α` / `IO α` | Erased world argument and constructor result |
| EIO success | Tag 0 with one owned payload |
| EIO failure | Tag 1 with one owned error payload |

The native helpers in `src/include/lean/lean.h` agree with these result layouts.
The guest world is an erased ABI slot, not a snapshot or a JVM machine object.
Preserve erased parameters from the captured declaration even where the C
function omits them: `lean_get_stdout` has one captured `void` argument, while
its C implementation has none. Validate original captured signatures, not a
single signature guessed from the C prototype. RBMap contains two signatures
for `lean_usize_of_nat`, one with an additional erased proof argument.

Separate three outcomes:

- Declared guest error: EIO tag 1, handled by Lean `tryCatch`.
- Host implementation failure: trap/exception with the original cause and
  inspectable failed execution state.
- Panic: Lean's separate panic/default-result policy; do not silently convert
  every panic into an EIO error.

`Init/System/IOError.lean` has 19 error constructors with differing fields,
including UInt32 OS codes and optional filenames. Filesystem adapters need an
explicit error mapping tested against native Lean. A Java exception message in
an arbitrary constructor is not faithful; platform-specific text equality is a
separate, narrower claim.

## Streams, values and resources

`IO.FS.Stream` is a guest record with six closure fields in this order:
`flush`, `read`, `write`, `getLine`, `putStr`, `isTty`.
`getStdout` returns this record, not a raw Java stream. `IO.println` obtains the
current record and invokes its closure. Guest stream replacement and capture
therefore depend on ordinary projection/application/ownership behavior.

The native runtime in
[`runtime/io.cpp`](https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/src/runtime/io.cpp)
uses persistent default stream roots and thread-local current streams. It wraps
native handles using the exported `lean_stream_of_handle` function from
`Init/System/IO.lean`. A first JVM stream provider should produce valid six-field
records backed by admitted host closures. Unimplemented stream operations must
fail explicitly when invoked. Getter retains, setter transfer and task-local
stream ownership need their own checks.

The full RBMap main reaches 26 extern declarations representing 25 C symbols.
Beyond the five supported Nat externs, its runtime gaps are:

- Nat division, multiplication and power.
- Array construction, size and borrowed indexing.
- UInt32 comparison/conversion; USize conversion/rendering; platform bit width.
- String list construction, append/push, UTF-8 byte size, character decoding
  and position advance.
- Standard output retrieval and a panic path.

This requires U32 and USize lanes before most IO is usable. Preserve unsigned
arithmetic, exact scalar byte offsets/widths, boxing, and captured ownership.
Char uses a Unicode scalar in UInt32; Java UTF-16 `char` is insufficient. String
positions are UTF-8 byte offsets. ByteArray is binary data. General runtime
coverage will also require U16/U64, Int, floats and more primitives; those are
not prerequisites to claim merely the first RBMap subset.

Guest refs are needed for stateful programs and buffer-backed streams. Their
alias identity and get/set/take/swap ownership must survive engine integration.
A fork copies logical state according to the chosen storage contract, not the
underlying external resource. Logical RC, JVM memory ownership and authority to
close a resource remain distinct.

Real handles need exactly-once close authority and defined behavior through
closure capture, failures and abandonment. Two forks holding the same physical
file also share its cursor unless a provider virtualizes it. Recommended profiles:

| Provider/state | Fork behavior |
| --- | --- |
| Pure guest state | Forkable under the engine's heap contract |
| Snapshot-local virtual streams, entropy and environment | Forkable when all provider state participates |
| Real files/processes/streams | Explicitly shared or nonforkable scoped capabilities |
| Recorded transcript | Separate opt-in replay provider; restoration does not imply replay |

Single-use host completion prevents accidental duplicate completion; it does
not prevent deliberately executing an effect again from an older retained world.
Do not promise automatic effect rollback or retry.

## Existing Ansatz implementation to reuse

All paths below are under `experiments/lean-ir/src/prototype`.

| Existing component | Reusable contract and limit |
| --- | --- |
| `runtime_io.cljc` | Validated six-field streams, seeded defaults, logical thread slots and transfers; does not provide complete host writes/filesystem handles |
| `runtime_string.cljc` | Native-oracle-backed UTF-8 positions, supplementary characters, extraction/comparison; caches are derived views |
| `runtime_prim.cljc`, `scalar.cljc`, `native_scalar.cljc`, `runtime_signatures.edn` | Scalar/ByteArray ABI and snapshot-local refs; some panic/default paths explicitly unsupported |
| `typed_eio.clj`, `typed_extern.clj` | Validated emitted success/error wrappers, codecs, exact ownership and bounded effect permissions |
| `raw_interop.clj` | Pause/host-boundary completion/abandonment and staged ownership |
| `runtime_task.cljc` | Cooperative task/promise/cancellation roots; does not claim native thread scheduling |
| `runtime_sync.cljc` | Limited snapshot-local mutex representation, not full native synchronization |
| `module_runtime.clj`, `resident_init_prefix.clj`, `initialization.clj` | Explicit initialization/checkpoint machinery; selected globals alone do not reconstruct module registration order |

The Java engine should implement or adapt these contracts behind the existing
facade. It should not create a second public IO, loader or host-call API. Existing
contracts are reuse material, not evidence of new-engine coverage.

## Frontend dependencies beyond ordinary IO

`Lean/CompactedRegion.lean` and `Lean/Environment.lean` load compacted object
graphs with dependency-region identity, relocation, roots and lifetimes. Reading
`.olean` bytes into a ByteArray is insufficient. The pinned module system also
uses `.olean.server`, `.olean.private`, `.ir.sig` and `.ir` parts.

Frontend hosting needs artifact lookup/version/trust checks, imported graph
transport, environment extension state, ordered module/builtin initialization,
syntax/attribute registration, initialized globals, dynamic `evalConst`, kernel
admission, Name/Expr/Level primitives, heartbeats/cancellation and diagnostics.
Native `lean_eval_const` and `lean_run_mod_init_core` in
`src/library/ir_interpreter.cpp` are substantive bridges, not trivial externs.

Reuse `module_store.clj` and `import_capabilities.clj` for verified transported
artifact graphs and leases; `resident_init_prefix.clj` for region/evalConst
integration; `imported_kernel.clj`, `kernel_host.clj` and `kernel_bridge.clj` for
checked admission and representation. `hosted_file.clj` is the existing surface.
Some existing paths retain native capabilities and restricted kernel support.
Record each dependency and its replacement; do not call the new frontend purely
JVM-hosted until the selected profile no longer needs an external Lean process
or native Lean service.

Task timing is also observable: Lean documents eager effectful BaseIO tasks
that can survive loss of the user reference. Running all tasks inline or only
on demand is not generally equivalent. A cooperative profile must be explicit
and validated against the chosen frontend path. Full server concurrency is a
separate milestone. Process spawning, native plugins/dynamic libraries, sockets,
OpenSSL, signals and OS synchronization remain outside the first profile unless
an exercised path requires them.

## Implementation and validation sequence

The [first extern slice](JAVA_EXTERN_RUNTIME.md) implements the captured ABI
registry for eight executable Nat operations and recognizes both USize conversion
signatures without enabling USize execution. Nat multiplication, division and
power reduce the original RBMap main's unsupported extern count from 21 to 18.
The remaining sequence below is still an implementation plan.

The subsequent [U32/USize slice](JAVA_SCALAR_RUNTIME.md) implements those lanes,
boxing, packed fields and seven original scalar extern declarations. RBMap
main's remaining unsupported extern count is now 11. Its string/array/IO closure
still requires implementation; scalar coverage alone does not execute main.

1. Extern registry keyed by symbol and allowed captured signatures, with borrow
   bits, erased slots and return convention. Test RBMap's repeated-symbol case.
2. Add the U32/USize lanes and data/Nat/string primitives reached by RBMap main.
   Compare scalar boundaries and UTF-8 cases against pinned Lean.
3. Connect explicit Java continuations to the existing host boundary contract.
   Validate owned results, host failure and pause/resume without effect replay.
4. Run unchanged RBMap main using a valid captured-output stream. Check stdout,
   EIO result, stream replacement, cleanup and pauses around output in both
   execution drivers. Keep the computational performance control.
5. Expand to refs, binary/text file IO, mapped guest errors, catch/finally and
   explicit initialization order. Select a modest original IO/import example.
6. Integrate verified artifact transport and existing kernel/loader authority.
7. Host one frontend invocation with imports, syntax registration, elaboration,
   checked admission, diagnostics and a new callable declaration.
8. Maintain a native-dependency retirement ledger and validate self-rebuilding
   compiler artifacts after in-process source loading works.

Still unmeasured: full frontend runtime reachability, complete kernel primitive
coverage, registration completeness, exact panic policy, adequacy of cooperative
tasks, and cross-version artifact transport. This audit does not establish those
properties or change production execution defaults.
