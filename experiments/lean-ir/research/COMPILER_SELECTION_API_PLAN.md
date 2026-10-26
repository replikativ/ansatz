# Compiler selection after file loading

Status: advanced immutable Clojure setter implemented; four focused tests and
44 composed regressions passed in the shared resident REPL.
The FileHandle/root selector below remains a proposal. Callers still prepare
explicit facts for already installed code. The current provider-first profile is
not turnkey optimized file loading.

## First increment: immutable advanced Clojure setter

`resident/with-compiler-options [context selection]` is a thin adapter over
the existing raw constructor, following `resident/fork` and `with-externs`:

1. Lock the supplied Context, check it is open, and validate protected functions
   and host bindings through the existing context checks.
2. Reopen the same immutable executable map and binding registry with
   `raw/open-functions`, using `raw/session-options` plus the replacement
   `:compiler-options`. Existing validation copies bounded pure data, rejects stale
   facts and prepares the selected JVM plan. `{}` deliberately clears selection.
3. Return a new separately closeable Context retaining the same World roots,
   configuration, protected registries and shared code cache. Follow existing
   persistent fork ownership; do not introduce a retain/cleanup policy.

Construction performs no guest execution, checking, publication, source read or
initializer replay. Failure occurs before issuing a child and leaves the input
Context usable. A selection is not a receipt, an environment association or
permission to call an uninitialized/unadmitted file.

The thin Clojure facade delegates through its existing `operate`/`child` pattern,
preserving the borrowed provider scope and lease through every descendant and
failure object. Java remains unchanged. Passing opaque Clojure compiler
fact maps should not be presented as a convenient Java API; a later meaningful
profile/FileHandle/names interface can receive a thin Java adapter.

The focused tests cover default→selected→cleared children with retained old contexts,
actual execution-route evidence, shared cache identity, malformed/stale selection
before child issuance, closed contexts, protected authority and borrowed provider
scope. Reuse existing resident/facade failure packets and ownership tests.

## Second increment: bounded FileHandle/root convenience

Accept an explicit active FileHandle, structured source names and supported
compiler profile/budgets. Validate the handle's unit identity and readiness
through the existing resident path before deriving any selection.

Read exact admitted source rows from the active World's
`:eval-const-authorizations :declarations`. For imported helpers, only consult an
already independently trusted catalogue/authorization path; a same-named row is
not authority. Never substitute a different source version from a global lookup.

For each demanded original source declaration, create its M1 companion through
`import-ir/lower-typed-declaration`. Follow actual installed direct callees under
explicit function/work limits, mint supported numeric extern descriptors with
`runtime-abi/describe-scalar`, and validate every fact against installed code via
the existing compiler-options contract. Discard transient raw producer rows,
catalogue/source owners and metadata; retain bounded immutable selected facts.
Do not scan/type the whole catalogue or Init, and do not authorize missing code.

Select eligible original unboxed workers, not automatically their public boxed
wrapper. UInt64 public calls often resolve `name._boxed`; making that wrapper a
region root causes unbox/box preparation fallback. Leave the wrapper ordinary
and enter its selected worker under the existing caller-frame contract. Nat's
original entry may already have an object ABI. Eligibility must follow explicit
IR/extern semantics; `object` alone is not a Nat/dependent-type descriptor.

The later Nat small-value path has a Long carrier guard. Java BigInteger/Clojure
BigInt inputs remain valid ordinary values, but small mathematical magnitude
alone does not promise that fast path. Do not silently normalize codec carrier
classes to obtain optimization. Preserve exact UInt64 and floating-point boundary
contracts as well.

Report unsupported roots/profile cases explicitly and preserve existing generic
execution. New code still needs ordinary kernel admission, source receipts and
initializer readiness. This convenience supplies optimization facts only.

The [setter validation record](../measurements/resident-compiler-options.json)
pins the exact new-function injection and test source. Frontend transport and
facade lease tests are models; selected boxed execution uses actual emitted IR.
No genuine source/class cohort or hosted file-loading gate is accepted here.
