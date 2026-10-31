# Unchanged multi-file tutorial target

The selected campaign target is the [first Lake greeting project from Functional Programming in Lean](https://github.com/leanprover/fp-lean/tree/0abeea545d560a324e2561f7210fbd6ed154fa02/examples/first-lake/expected), pinned at `0abeea545d560a324e2561f7210fbd6ed154fa02`. It has three small source files, a genuine import/re-export chain and no external package dependencies. This directory contains portable metadata and a bounded native compile/cache service, without vendoring the tutorial code. Native-frontend → JavaIR execution has passed; hosted frontend/default Init acceptance remains separate.

[corpus.json](corpus.json) records exact URLs, byte counts and SHA-256 values for all three source files, its Lake configuration and the relevant provenance files. The source bytes were fetched from the pinned GitHub commit without execution or editing. The upstream examples toolchain is 4.33.0; the campaign uses the independently pinned Lean 4.33.1 commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`. An external toolchain override must be recorded rather than modifying the project.

| Candidate | Pin and dependencies | Assessment |
| --- | --- | --- |
| [FP Lean first Lake project](https://github.com/leanprover/fp-lean/tree/0abeea545d560a324e2561f7210fbd6ed154fa02/examples/first-lake/expected) | Three modules; toolchain 4.33.0 inherited from `examples/lean-toolchain`; no package dependencies | Selected educational target. Small import chain and a deterministic greeting. |
| [Official Lean Lake hello example](https://github.com/leanprover/lean4/tree/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/tests/lake/examples/hello) | Exact campaign compiler commit; two modules; no package dependencies; Apache-2.0 | Useful earlier fallback. Upstream's test script builds and runs both empty and nonempty argument cases. |
| [lean4-samples CSVParser](https://github.com/leanprover-community/lean4-samples/tree/c3690b7a51667cfe74a64a49b0057dbc42d8716a/CSVParser) | Toolchain 4.1.0; `Lean.Data.Parsec`; Apache-2.0 | Not the first target. Upstream [explicitly deprecated the repository](https://github.com/leanprover-community/lean4-samples/blob/c3690b7a51667cfe74a64a49b0057dbc42d8716a/README.md); this example also needs partial recursion, parser APIs and `#eval`. |

The selected source dependency order is `Greeting.Basic` → `Greeting` → `Main`. `Greeting.Basic` defines the closed String `hello`; `Greeting` imports that module; `Main` imports `Greeting` and defines `main : IO Unit`. Both the official Lean reference and JavaIR execution produced the UTF-8 text `Hello, world!` followed by one newline: fourteen bytes, SHA-256 `d9014c4624844aa5bac314773d6b689ad467fa4e1d1a50a1b8a99d5a95f72ff5`.

For the native reference, use a clean checkout at the recorded commit, select the project directory, and run:

```sh
cd examples/first-lake/expected
lake +leanprover/lean4:v4.33.1 build
./.lake/build/bin/greeting
```

Record the actual toolchain binary/source cohort, source hashes before and after, build exit, stdout and stderr. Building the book is unnecessary and would introduce its unrelated Verso/tooling dependencies. The selected folder's `lakefile.toml` declares only the Greeting library and Main executable.

## License evidence and attribution

The pinned FP Lean repository has no root `LICENSE` and no separate license file for these example sources. Its [README](https://github.com/leanprover/fp-lean/blob/0abeea545d560a324e2561f7210fbd6ed154fa02/README.md) identifies the original book as CC BY 4.0 and the later modifications as copyright 2023–2025 Lean FRO, LLC. [LICENSE-ASSETS](https://github.com/leanprover/fp-lean/blob/0abeea545d560a324e2561f7210fbd6ed154fa02/LICENSE-ASSETS) contains the CC BY 4.0 license text. This metadata does not infer a separate Apache or other software license for the standalone examples.

Retain those exact provenance files and identify David Thrane Christiansen, Microsoft Corporation's original edition, Lean FRO's updates and the pinned source URL when presenting the tutorial. No upstream example code is vendored here. The official Lean fallback has an independently clear [Apache-2.0 license](https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/LICENSE).

## What exists and what remains

The unchanged project was checked/compiled by official Lean 4.33.1, with all three local initialization plans observed empty. Its main static IR closure contains six declarations, no missing static dependency and one dynamic stdout-method application. The compiler folded/inlined the greeting and interpolation into a closed String; these results do not prove a runtime call across a source-module boundary. The native reference used official `lean --run`; no C-linked tutorial executable was built by that reference step.

The JavaIR run independently authenticated the artifact manifest and unchanged IR stream, invoked the actual raw `[void] → object` entry with its world carrier, and returned actual IO-ok Unit. Captured stdout equals the native file byte for byte. The owned result was released and ordinary synchronous close completed (`closed=true`, `disposed=false`, the inactive tiny-engine close profile). The 512 MiB receipt is pinned in `corpus.json`. This run explicitly trusts the native frontend/checker/compiler: it did not run the hosted frontend, recheck the project in the Java kernel, import guest Init ModuleData or establish full imported-module initialization parity.

The separate explicit-Prelude campaign has actually exported/imported/re-exported checked source modules A → B → C, including C importing both A and B. Hosted calls returned `42` and `43` from input `40`, agreeing with the recorded native references, under a 512 MiB heap cap. Portable receipt locators and hashes are in `corpus.json`. The latest V3 receipt also records normal disposal/closure after releasing 38 extra owner occurrences and the 534 runtime-root occurrences. The earlier V1/V2 receipts remain historical execution receipts with cleanup pending.

That campaign does not establish this tutorial's default-import profile. Each unchanged tutorial source implicitly imports real `Init`. Relabeling Prelude as Init, prepending `prelude`, rewriting imports, dropping constants or omitting extension data would change the claim.

The remaining coherent gates for the hosted source route are:

- Genuine default Init ModuleData/kernel association and original import/finalization, including initialized-module policy and all source extension data.
- Closed String value/initializer roles across generated IR, source export and linking. Treating a closed value as an ordinary function would change identity and initialization semantics.
- The original `s!` macro from `Init/Data/ToString/Macro.lean`, String conversion/interpolation operations and the original `IO.println` → `IO.print` → stdout stream path from `Init/System/IO.lean`.
- A typed `IO Unit` invocation boundary with actual owned IO-result handling, service continuation, stdout capture and cleanup. The current public General FileRun invocation API checks `Nat → Nat`; it does not authorize this new ABI by itself.
- Unchanged native/hosted output comparison and normal retirement of every issued module, Run, Base, provider, store and runtime owner.

## Native compile/cache service

`service.py` is the Linux/x86-64 prototype for an internally invoked compiler service. It accepts exactly this selected source/TOML profile and leaves the caller's project unchanged:

```sh
python3 service.py --project "$PROJECT_DIR" --cache "$CACHE_DIR" \
  --sysroot "$LEAN4331_ROOT" --exporter "$PINNED_EXPORTER" --native-reference
```

Inputs and cache paths are explicit. The service copies the four hash-checked input files into a private build tree, compiles `Greeting.Basic`, `Greeting`, then `Main`, exports each local stream/actual initialization plan and the main closure, and checks static dependency completeness. The cache key binds source bytes, service/profile bytes, compiler options, the exporter and actual installed toolchain descriptor. Cache publication writes its manifest last and renames the completed private directory atomically. Hits revalidate the whole file set and every artifact digest as well as current input/toolchain identity. Unknown sources, malformed or modified cache entries and changed toolchain descriptors reject; they are not silently treated as hits.

Each native process is shell-free, single-threaded and monitored against 900 MiB RSS, a 2 GiB MemAvailable floor, 90 CPU seconds, 120 wall seconds and bounded output. Failures preserve only their private unpublished compiler evidence, never a successful cache manifest. The source project is not written. Structured progress goes to stderr; stdout is one final JSON response containing the cache status, manifest locator and its digest.

The installed official sysroot and caller-owned cache are trusted inputs. Executable hashes, reported version/commit and the bounded Init library stat inventory detect ordinary dependency changes; they do not cryptographically attest every library byte or defend against a hostile host restoring metadata. The interface configures the native toolchain explicitly, like another installed compiler dependency. This profile still requires the independently pinned prebuilt exporter. A source-run exporter probe exceeded its 900 MiB cap before output and is not an accepted fallback.

`--native-reference` explicitly executes the selected program through official Lean and records its actual stdout; without that flag the manifest's native reference is absent, not a fabricated fresh comparison. The cold service/cache-hit smoke passed with the flag, produced the same accepted IR SHA, and retained the exact native fourteen-byte output. Five native stages took 6.60 seconds in total, with sampled peak RSS 672,284 KiB. The subsequent hit returned the same manifest digest without compiler-stage execution. These are research measurements, not general performance guarantees.

Run the seven metadata/cache/process checks with `python3 service_checks.py`. They execute no Lean or Java. Actual frontend compilation and runtime tests remain separately coordinated.

## Smallest correct default Init route

Use the existing genuine matched Init V3 pair, not an invented smaller module. Its audit covers 631 modules, 3,155 parts, 65,994 distinct ConstantInfos and complete source payloads. The graph has 11,233,359 records; all 11,233,358 source objects are persistent RC0, with only the produced roots-array shell counted RC1. The transport receipt reports 23,400,068 reference occurrences and 2,137,887 immediate occurrences, with 369.65 MiB of native allocation. This explains why eager Java Node/array/JSON construction is not a 512 MiB route. Native allocation is not a Java heap estimate.

First implement a separate authenticated persistent arena reader: compact indexed binary records produced by a streaming conversion of the audited transport; immutable scalar/field reads; source-index identity; weak canonical live wrappers; explicit shared leases; stable source pointer words; and rejection of mutable or unsupported source kinds. An eight-byte offset table alone is 85.70 MiB, and eight-byte storage for the reported field occurrences is 194.84 MiB. Put those tables in the mapped file rather than on the Java heap. These are storage arithmetic, not measured working-set promises. A narrower four-byte-offset format is possible only with a validated total file-size bound.

Then introduce an actual runtime value-access boundary. The current final `Interpreter.Node` exposes concrete arrays; this checkpoint has 556 `.fields`, 116 `.scalars` and 118 `.rc` references in Interpreter.java. Empty arrays or hidden eager hydration would not implement a mapped value. Port readonly constructor/array/scalar paths, RC0 no-ops, immediate-shell copy-on-write, certified pointer observations and fork/lease behavior coherently, including the Clojure source/layout witnesses. Use a bounded genuine graph projection and both execution drivers before admitting the full graph. Fresh frames/Refs/owned arrays remain ordinary branch-local Nodes.

Keep the paired kernel side lazy too. The pair contains 6,418,857 Expr records; do not build an Expr array or materialize all proofs at startup. Prepare a full format2 store offline, validate its exact audited domain/counts/roots, and add an explicit lazy Base admission route over raw immutable shell/body correspondence. Resolve actual full CIs on demand without substituting a defs-only view or weakening payload identity checks.

Finally resolve the one observed initialization requirement, Init.Data.Random's `IO.stdGenRef`, through a reviewed source-faithful route. The old captured 534-global seed already having that global is not an initializer-status witness. Preserve the genuine negative native-symbol path and implement original interpreted initialization with explicit virtual entropy/global replacement semantics, or create a new seed with actual source-coupled per-module native initialization event receipts. Never return successful initialization just to skip fallback.

The detailed boundaries are in [the mapped graph design](../../../paired-init/MAPPED_GRAPH.md), [kernel-store design](../../../paired-init/KERNEL_STORE.md) and [initialization design](../../../paired-init/INITIALIZATION.md). None of these future representation/import capabilities is claimed implemented by this target selection.
