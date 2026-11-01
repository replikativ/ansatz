# Typed source exporter diagnostic channel

The structural NDJSON channel is stdout. During the genuine `Elab.runFrontend` call, `IO.withStdout (← IO.getStderr)` routes normal frontend diagnostics to stderr. After that scoped call, the original stdout is restored for the manifest and declaration rows. Warnings are neither disabled nor changed into errors; options, asynchronous elaboration, module identity and `.olean` arguments are unchanged.

This follows Lean commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`:

- `src/Lean/Elab/Frontend.lean:335–340` runs and reports the snapshot tree before accepting a final environment.
- `src/Lean/Language/Basic.lean:409–451` reports normal diagnostics with `IO.print`/`IO.println` on the calling thread's current stdout.
- `src/Init/System/IO.lean:1249–1254` restores the previous stream in `finally`.

The existing `none` result check still throws before any structural manifest is emitted. Native metaprograms remain trusted application code; this scoped channel change is not an OS-level sandbox or interception of arbitrary direct native writes.

## Root-operated acceptance spec

Compile/link a new producer cohort before changing accepted binary/source pins. No compilation or native execution was performed by this patch's author. Keep the old producer fixtures and accepted artifacts as compatibility evidence.

For each case, use a separate bounded native process and fresh output path with the ordinary `--source … --olean … --local --typed-module …` arguments:

1. **Clean source:** `def diagnosticClean (x : Nat) : Nat := x`. Require exit zero, one structural manifest, and declaration rows only. Compare parsed structural observations with the previous producer for the same source.
2. **Unchanged warning:** `def diagnosticWarning (unused : Nat) : Nat := 7`. Keep the unused binder and default warning policy. Require exit zero, the actual unused-variable warning on stderr, and every nonempty stdout line independently parsing as a structural manifest/declaration record. Do not strip a leading line or tolerate non-JSON stdout. The compiler must still produce the genuine `.olean` and native IR.
3. **Information:** add `#check Nat` to valid source. Require its actual information message on stderr and no information text in stdout. This also checks that successful reporting does not leave stdout redirected when structural emission begins.
4. **Frontend error:** `def diagnosticError : Nat := "wrong"`. Require nonzero exit, the actual frontend diagnostic on stderr, and no accepted manifest or declaration stream. Do not accept a cache entry or BuildReceipt from this result; a failed compiler may leave incidental files which remain untrusted.
5. **Restoration invariant:** independently exercise `IO.withStdout` around a throwing IO action in the root's native model if needed. The pinned implementation must restore its previous stream in `finally`; no exporter catch/retry or warning suppression is added.

Finally run the actual public source cold→cache-hit→artifact-export→artifact-load path with the warning-bearing source. Source/binary cohort identities and cache keys must reflect this producer revision. A native compilation failure remains a failure, without command retry or fallback to a different frontend.
