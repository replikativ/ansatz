# Value initializers and ordinary hosted files

This is a source-derived contract and implementation proposal, not new runtime
support. Inspection used Lean 4.33.1 commit
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, installed Lean sources, and
`git show <commit>:src/library/ir_interpreter.cpp`. The sibling checkout's working
C++ sources are older. No native oracle or additional heavy process ran for this
review.

## Three separate execution paths

1. Source commands elaborate declarations and modify the current Environment.
   `initialize value : T ← action` expands into a private `initFn : IO T` and an
   opaque `value` carrying `[init initFn]`; the IOUnit form emits a private
   `[init]` function. Elaboration records future import work. It does not run
   regular initialization merely because its declaration was compiled.
2. Native module lookup (`lean_run_mod_init_core`) resolves the exact mangled
   module initializer symbol and invokes it with builtin=false. It returns
   IO.ok false when unavailable. The existing capability can report availability
   only from explicit trusted producer plans and completed world-local guards;
   it must not invent a successful native initializer or a completion receipt.
3. When native initialization is unavailable, the actual guest
   `runInitAttrForMod` handles regular imported initializers. It checks and
   inserts the module in `interpretedModInits` before effects, combines ordinary
   and IR attribute entries with deduplication, applies phase filtering, then
   evaluates IOUnit actions or calls `lean_run_init` for named values.

Sources: [initialize elaborator](https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/src/Lean/Elab/Declaration.lean#L342),
[InitAttr](https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/src/Lean/Compiler/InitAttr.lean#L159),
[native module lookup](https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/src/library/ir_interpreter.cpp#L1192).

The guest fallback guard is entered, not transactionally committed. A failed
initializer leaves it entered. Reusing that partial world is not a clean retry;
restore an earlier immutable snapshot if guest effects must be discarded, and
never claim to roll back external effects. Direct `lean_run_init` has no once
guard: calling it twice executes the initializer twice and replaces the global
on each success. The guard must not be moved into that primitive.

## Exact `lean_run_init` boundary

Lean declares borrowed Environment, Options, declaration Name and initializer
Name, followed by an erased IO world. Its raw IR signature is four borrowed
`object` parameters and one owned `void`, returning an owned `object` IO result.
The native implementation creates an interpreter and calls the boxed initializer
with one effective world argument. It chooses the actual boxed implementation
where needed. On IO success it marks the boxed payload persistent, drops the IO
wrapper, and writes the value into either a native global slot or
`g_init_globals`; it returns fresh IO.ok Unit. An IO error is returned unchanged.
Native interpreter exceptions become IO errors.

Sources: [declaration](https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/src/Lean/Compiler/InitAttr.lean#L41),
[boxed calls](https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/src/library/ir_interpreter.cpp#L1067),
[value initialization](https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/src/library/ir_interpreter.cpp#L1127),
[C entry](https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/src/library/ir_interpreter.cpp#L1209).

Native `load` checks the initialized-value table before evaluating a constant.
A successful boxed scalar global is unboxed according to its actual IR result
type. If no initialized/native value exists, it explicitly rejects a regular
`[init]` declaration in the same module. It must not execute the initializer
lazily to make that source-time access succeed.
[Source](https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/src/library/ir_interpreter.cpp#L881).

A supported host adapter should use the scoped raw `:invoke` and the existing
strict interpreter-witness/code-admission path. It must authenticate actual
environment-selected declaration and initializer IR/ABI and their attribute
pair, then execute the owned boxed closure with the erased world. This supports
the checked initialization subset; it is not a promise to implement arbitrary
unsafe writes to unrelated globals that the native unsafe primitive permits.
All four borrowed input owners stay borrowed. IO errors retain their original
owned result. On success, persist the payload before releasing its wrapper and
publish the exact object value or typed scalar view in the world's globals.
Unsupported code/provenance remains an explicit trap, not fabricated IO success.

`machine/publish-io-global` cannot be called blindly: it delivers guest control
and traps on IO errors. `:begin-init` also skips ready values, which would change
direct `run_init` behavior. The new adapter must thread the caller's unchanged
control state through the raw boundary and return an IO result normally.

Initializer permission and “currently importing” also differ. The guest
`enableInitializersExecution` flag gates import finalization; actual
`withImporting` sets a guest IO.Ref and clears both flags on exit. It need not set
the host world's `:initializing?`. Requiring that host Boolean alone would reject
the existing genuine source finalizer. If a narrower adapter restricts invocation
to import time, query the actual trusted guest initialization state.
[ImportingFlag](https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/src/Lean/ImportingFlag.lean#L18).

## Ordinary macros do not require a new value initializer

`macro` and `macro_rules` produce definitions tagged with the regular macro
attribute. Its after-compilation handler evaluates the new Macro closure through
`evalConstCheck` and adds it to the current scoped Environment extension. During
import, `ofOLeanEntry` reconstructs the callback through actual imported
`evalConstCheck`. Builtin attribute registration is different: `declareBuiltin`
emits a future builtin IOUnit registration action. Running every exported local
initializer again would duplicate source-time registration rather than help the
ordinary macro path.

Sources: [macro rules](https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/src/Lean/Elab/MacroRules.lean#L51),
[import reconstruction](https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/src/Lean/KeyedDeclsAttribute.lean#L117),
[local attribute execution](https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/src/Lean/KeyedDeclsAttribute.lean#L163),
[builtin registration](https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/src/Lean/Compiler/InitAttr.lean#L149).

The [actual local macro acceptance](../measurements/native-local-macro-runtime.json)
now passes against a retained descendant of genuinely reconstructed, freshly
checked Init+A. It embeds the existing `OrdinaryMacro.lean` fixture in
[`OrdinaryMacroLocal.lean`](../fixtures/hosted/OrdinaryMacroLocal.lean), adding the
matching import header and a monomorphic Nat wrapper. Compilation produced zero
diagnostics and three admitted units. The wrapper introduces one compiler value
action, so the deferred call correctly stopped before guest invocation. A separate
explicit `resident/initialize` operation on the already loaded unit followed by
`resident/call` returned **42**; neither compilation nor a failed guest call was
replayed. This value action initializes the closed wrapper, not macro registration.

Imported macro/attribute reconstruction and edited-module fork isolation remain
future gates. Local macro success does not resolve imported evalConst authority
during extension reconstruction before final checking. Value initialization for
imported named globals, custom attributes and newly registered extensions also
remains separate. The complete retained campaign process later exited 0 without
a guard stop; semantic Context/Source cleanup was not performed or verified.

## Guard coordination required before broader source imports

`eval-const/run-initializers` currently records a separate admitted-unit digest
guard and completion evidence. It does not update the actual guest
`interpretedModInits` reference. Explicit `:run` followed by genuine import
fallback can therefore duplicate IOUnit effects. Either use guest fallback as
the sole source-import initialization path, or explicitly coordinate the real
guest guard and validated completion evidence. Do not infer completion from a
source export or a ready value alone. The current source registry's restriction
to modules without initializer actions avoids this unresolved integration.

Essential tests before enabling that extension:

- Local compile does not execute regular effects or make named globals readable.
- Direct run_init twice repeats effects; the actual module fallback does not.
- IO failure preserves the owned error, publishes no value, and leaves the
  guest module guard entered; clean-snapshot retries stay separate.
- Successful object, UInt64 and Float values preserve ownership and exact typed
  representations; independent forks retain their previous global state.
- Macro registration works once in the command Environment and reconstructs
  through actual import extension callbacks; final bundle installation does not
  replay source-time registration.

## Preparing the ordinary-file context

The public `hosted-file/run-file` API is already sufficient once its prepared
context is real. Ordinary import preparation should remain a separate explicit
operation rather than adding hidden filesystem discovery to that runner.

A proposed `prepare-imported-file` operation would take an initialized runtime
world/session/catalogue, source text and file name, a trusted import resolver,
and an owned guest Options factory/input. It would:

1. Run `frontend/inspect-file-header` in that world. Preserve its actual ordered
   requests and module-system Boolean; stop on header diagnostics before import
   effects. An ordinary classic file requests Init twice: ordinary and meta,
   both importAll=false and isExported=true. Do not reduce these to one request.
2. Resolve only an exact compatible verified import closure. The current Init
   transport is private/classic and must not serve a module-system header whose
   visibility requires a separately exported module-aware closure. Preserve
   parts, IR phases, effective imports and initialization-symbol authority.
3. Execute actual `module-import/import-loaded`, including extension callbacks,
   real initializer guards, and strict final kernel association. Retain the
   immutable DAG source lifetime for every resulting world/fork. No failure
   yields a prepared runnable context or authorizes effects replay.
4. Return the updated session and bindings from import, its world, the explicit
   original pinned catalogue, owned imported Environment, and owned Options
   created in that compatible world. Keep the successful import certificate and
   requested-header evidence as preparation metadata. Never reuse an Options Ref
   from another fork just because its integer ID matches.
5. Pass this prepared context into `hosted-file/run-file` with the same source
   and file name and explicit `:initialization :defer`. The existing guest file
   helper rechecks exact header imports/module mode before compiling commands.
   Retain the final Environment and session for later evalConst and continuation.

The prototype's `target/run-module-import.clj` already performs most of steps
2–3, returning its updated session/bindings/source, but it is an experiment driver,
not a combined public preparation API. The returned catalogue must be supplied
explicitly by its caller. Header parsing and Options production remain explicit
caller work. `HostedFileProbe.preparePrelude` deliberately creates an unrelated
empty Environment and seeds three compiler markers; it must not replace an
ordinary imported Environment. A generic guest Options factory, or an already
owned Options value from the same world, is the cleaner preparation boundary.

The first ordinary acceptance inputs are `OrdinaryAnswer.lean` and
`OrdinaryMacro.lean`, each compiled from an independent prepared fork of the
same successful imported Init baseline. Check actual diagnostics, retained
Environment, strict admitted declarations, actual emitted IR and a final call.
Do not rerun the full native import/extension reconstruction between these
experiments if a compatible prepared immutable baseline is already available.
The default runner should keep source export/publication separate: the existing
source registry still rejects modules with dependencies or initializer actions,
so publishing an ordinary Init-importing module is a later transitive-import
slice, even after its compile/call succeeds.
