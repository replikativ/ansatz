# Experimental optional Lean facade

`ansatz.lean` adapts the resident frontend without adding prototype requirements to
core Ansatz. This is a **provider-first prototype**, not a zero-configuration Lean
SDK. The caller supplies a genuinely checked prepared Environment and independent
trusted registries; `resident-preparation/open-checked` still validates their live
association. A Boolean, serialized receipt or certificate cannot replace it.

The initial supported runtime baseline is **JDK 17 or later**. Archived provider
paths use `java.util.HexFormat`; that provider dependency is outside the narrower
facade source closure. Its public Java DTOs compile with `--release 11`; that
bytecode target does not establish JDK 11 runtime compatibility. A lower runtime
baseline remains unverified. Core's Java
11 target and AOT behavior are unchanged. The facade and prototype namespaces
remain source-loaded. No Graal/Truffle, native Lean, SCI, malli or datahike is added.

## Borrowed provider scope

The provider is a trusted function of the supplied options. It returns:

```clojure
{:candidate {:world world :session session :environment owned-environment}
 :configuration {:catalogue independent-catalogue
                 :trusted-functions independently-captured-functions
                 :trusted-bindings independently-captured-bindings
                 ;; Existing resident helper/frontend configuration and admitted
                 ;; application-extern-symbols belong here when needed.
                 }
 :source-lease caller-owned-open-lease-or-provider-scope}
```

The lease must be nonnil. Its contents do not grant checking authority. The
provider/caller retains ownership and keeps it open through **all descendants,
active operations, retained file handles and diagnostic failure evidence**.
`Context.close` releases only its resident Environment/Options roots. It never
closes Source, ResourceLease, provider or application capabilities, even when the
last context closes or open fails. Strong references keep provider scope reachable;
they cannot prevent a caller from explicitly closing borrowed backing too early.
There is no ownership transfer, reference-counted lease release or Cleaner.

Each successful `open`, `fork`, `initialize` and `with-externs` creates a separately
closeable context. `load-file`, `load-string` and `call` return their matching child
context. Always use that returned context for subsequent work and close every
context you retain. Closing a parent leaves a child usable while the borrowed
provider scope remains open. Forks isolate guest state and share executable caches;
host effects remain external. Per-context operations serialize with its close.
The provider is responsible for safe acquisition if it is called concurrently.

## Clojure API

```clojure
(require '[ansatz.lean :as lean])

;; prepared-provider must supply the real pinned runtime/helper/source setup.
(with-open [root (lean/open {:provider prepared-provider :options {}})
            edit (lean/fork root)]
  (let [loaded (lean/load-string edit "prelude\ndef answer (x : Nat) : Nat := x\n"
                                {:module "Example" :roots ["answer"]
                                 :file-name "Example.lean" :initialization :defer})]
    (with-open [compiled (:context loaded)]
      (when (:success? loaded)
        (with-open [ready (lean/initialize compiled (:file loaded))]
          (let [called (lean/call ready (:file loaded) "answer" [42N]
                                  {:arguments [:nat] :result :nat})]
            (with-open [after-call (:context called)]
              (:value called))))))))
```

`load-file` accepts a Path or path string and the same explicit request options.
It captures UTF-8 once and passes text to resident, which never reopens that path.
Malformed UTF-8 and unpaired UTF-16 surrogates reject. The envelope is
`{:context :file :success? :diagnostics :source}`; source includes immutable text,
SHA-256 of its UTF-8 bytes, byte count, module Name, display filename and origin.
A path is an origin, not source identity. No module name is inferred from a path.
Diagnostic records are forwarded unchanged; no unverified byte/character span
convention is invented. A compile diagnostic failure returns the actual partial
child context, `:success? false` and no executable file. Close that child as usual.

`(lean/name "A.42")` creates two **string** segments. `(lean/name ["A.B" 42])`
preserves a literal dot and a numeric segment. Existing kernel Names pass through;
`[]` is anonymous. Numeric convenience segments follow the existing guest encoder's
nonnegative signed-long domain. Name identity is never inferred from printing.

Outbound `call` forwards existing generic codec descriptors unchanged, including
explicit erased/null arguments. Facade acceptance with genuine frontend execution
initially targets Nat/String; codec availability alone is not acceptance of every
Lean source type. There is no facade `call-io`, generic object binding, callback
closure handle, asynchronous callback, source importer/DAG or proof-state API.

`lean/extern` accepts `:symbol` plus the existing exact typed-extern specification:

```clojure
(lean/extern
 {:symbol "application_answer"
  :signature {:params [{:ty "tobject" :borrow false}] :return-type "tobject"}
  :arguments [{:codec :nat :ownership :owned}]
  :result :nat :fn inc})
```

Pass the returned symbol/binding map to `lean/with-externs`. This never widens the
provider's application allowlist or replaces reserved/runtime bindings. Inbound
values are exactly the existing synchronous Nat/String subset, with explicit ABI
borrow bits. Host functions receive ordinary immutable decoded values by positional
application. No raw world, Ref, IO or arbitrary host object is passed to a callback.

## Failures

Invalid facade input uses `:lean/code :invalid-request`; a closed handle uses
`:closed-context`. Exceptions from resident operations use `:operation-failed`
unless a facade preflight code already exists. This prototype does not infer
fuel/cancellation/ABI categories from exception messages. The outer ExceptionInfo
records operation and an opaque, bounded-printing `:lean/failure` object. The
original Throwable remains its cause, with exact lower checkpoint/session/owner
packets untouched. `lean/failure-cause` permits advanced diagnostic inspection.
Keep the provider lease open while retaining or inspecting that evidence.

No failure invents a resumable context or guesses disposal, retries host effects,
rolls back IO, or silently drains guest owners. Existing terminal/phase markers
stay in the original evidence. There is no failure `close` pretending to discharge
unknown owner stages. Releasing diagnostic owners requires the existing explicit
owner-aware low-level procedure. This is a documented limitation of this slice.

## Java API

`ansatz.lean.LeanRuntime` contains the thin public nested DTOs/interfaces:
`PreparedProvider`, `PreparedInput`, `OpenOptions`, `LeanContext`, `SourceRequest`,
`LoadResult`, `LeanFile`, `CapturedSource`, `CallSignature`, `CallResult`,
`ExternArgument`, `ExternSpec`, `HostFunction` and `LeanException`.

`LeanRuntime.open(provider, options)` and `LeanContext` methods delegate to the
same Clojure operations. A provider may be configured by Clojure and passed to
Java; this does not promise a Java bootstrap producer. `PreparedInput` accepts
opaque candidate/configuration maps and borrowed source scope, never a checked
flag. `LeanContext` implements AutoCloseable; use try-with-resources on every
returned result context. Nat results and callback arguments become exact
`BigInteger`, including beyond `long`. Unicode/NUL Strings stay Java Strings.

`CallSignature` accepts codec names such as `"nat"`, or nested Lists such as
`Arrays.asList("option", "nat")`. Existing Clojure keyword/vector descriptors
also pass through. ByteArray inputs accept ordinary Java Lists of exact UInt8
integers; negative signed bytes are rejected by the existing codec without
truncation. Java Option values use null or a single `"some"` Map entry.
Lists are defensively copied without `List.copyOf`, so explicit Unit/erased null
values are preserved. SAM callbacks receive an unmodifiable argument list.
`LeanException` retains the original Clojure cause and opaque failure object;
public DTOs never expose a raw guest checkpoint as an ordinary value.

## Build and verification gates

Run from `modules/lean`, after building a pinned core jar. This checkout's core
build derives the version from its revision count; pass the actual built version.
The development dependency points at that built jar; `:dev` instead selects core
and prototype source explicitly. The generated optional POM pins a supplied core
Maven version rather than publishing machine-local paths.

```sh
clj -T:build jar :core-jar '"../../target/ansatz.jar"' :core-version '"0.2.<actual-revision>"'
clj -M:dev:test
python3 consumer/check.py --core-classpath '<pinned-core-and-Maven-dependency-jar-classpath>' --core-version '0.2.<actual-revision>'
```

`runtime-closure.edn` lists every staged prototype source and the required
`prototype/runtime_signatures.edn` resource. Build verifies the explicit closure
against its source requires, copies only those files and this module's own source,
and compiles only its own Java DTO. Runtime helper classes `ansatz.runtime.HeapOverlay`
and `GlobalsOverlay` come from the pinned core jar; no duplicate core classes or
unrelated experimental `TypedLongMemo` are packaged. No sibling repositories,
artifact inventories or bootstrap assets are copied. Build never AOT-compiles the
facade/prototype runtime. Bootstrap/helpers/checkpoints are **not distributed** by
this jar; provider setup remains a separate obligation.

`consumer/check.py` stages fresh Clojure/Java consumers in an isolated directory.
The runtime classpath is jars only (plus freshly compiled Java consumer classes):
no repository `src`, experiment paths or target artifact inventories. It audits
jar entries, exact staged source bytes and the selected core Maven POM version,
checks core-alone loading with optional
API absent, loads optional Clojure and Java entrypoints, and tests rejection of an
unchecked provider. These are packaging/load checks, not frontend acceptance.

`consumer/PreparedAcceptance.java` is the public Java fixture used by the genuine
provider campaign: exact BigInteger beyond long, Unicode/NUL String, two Java SAM
invocations and try-with-resources. Its explicit Nat ABI is `tobject` with
`borrow=false`. Its ordinary source header imports Init, matching the supplied
checked provider environment; adding `prelude` changes that header contract.
The provider must independently admit `ansatz_facade_host_nat`. The smoke gate
does not automatically run this guest compilation.

The [genuine provider receipt](measurements/genuine-provider-acceptance.json)
records a completed public Clojure and Java campaign on a pinned Lean 4.33.1
mutable profile, after freshly checking all 65,994 Init declarations with 15
explicit assumptions. Clojure acceptance includes a type diagnostic followed by a
good pristine branch, Nat beyond long, Unicode/NUL, two typed extern calls,
unrelated-file refusal, idempotent root close with a surviving descendant, and a
controlled host throw without retry. Java acceptance covers the public provider,
exact BigInteger/String values, two SAM calls and normal context closing.
The borrowed native Source remained open through all retained failure evidence.

Observed once in that process: Clojure source loading took 39.872 s, explicit
initialization plus three calls took 85 ms, and the Java fixture took 37.348 s.
These are one-shot observations with explicit host GC, not throughput or backend
comparisons. The receipt pins the actual controllers, consumer, fixture and
runtime bytes. Later merged runtime changes receive separate model/packaging
checks; those checks do not imply a new genuine frontend run.

Earlier fixture mistakes were retained as evidence: strict Nat ABI checking
rejected `object` against actual `tobject`, and the Java `prelude` header differed
from the supplied Init environment. Only examples/fixtures were corrected.
The owned JVM subsequently exited with status 0; this OS disposal does not claim
explicit Source close or cleanup of retained guest failure owners.

Provider bootstrap distribution, general import graphs, imported-macro
reconstruction, broader callbacks/IO and other backends remain separate acceptance
gates. Model tests substitute resident calls and make no new frontend claim.
