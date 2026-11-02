# Unchanged upstream persistent-map regression

`phashmap_alter.lean` and `expected.stdout` are unchanged official Lean files at
commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6` (4.33.1), Apache-2.0.
Exact upstream paths and SHA-256 hashes are in [provenance.json](provenance.json).
Copyright belongs to the Lean project contributors; no upstream endorsement is
implied. This is a substantive upstream library regression, not a multi-source
tutorial application.

The driver tests insertion, update, deletion, same-slot/deep collisions, map
draining and 200-key alter/insert equivalence. It imports only
`Lean.Data.PersistentHashMap`, whose own direct imports are all Init modules.
The expected native result is IO Unit with stdout `OK\n` and empty stderr.
The integration candidate passes an independent official-native reference,
public source loading, cache reuse and prepared-artifact loading. Repeated JVM
calls produce the same result. This is candidate validation, not a published
release claim; use the release checks for the deployed JAR's evidence.

```clojure
(def options
  {:compiler {:sysroot sysroot :producer-bundle bundle :cache cache}
   :root-module "phashmap_alter"
   :installed-imports ["Lean.Data.PersistentHashMap"]
   :entries ["main"]})
(def project (lean/load-project runtime "examples/persistent-map" options))
(lean/call project "main")
;; => {:value nil :stdout "OK\n" :stderr ""}
(lean/close! project)
```

The explicit list is generic and exact: every non-Init installed dependency
must be declared, with no prefix permission or package fetching. Source
headers, startup obligations, public codec checks, extern ABI admission and
runtime budgets remain independent. The selected closure additionally uses
`lean_string_any` and `lean_string_isprefixof`, ported from the pinned Lean
definitions with exact ABI checks. String predicates run through ordinary guest
closure application, including resumable execution. Existing helpers and their
immutable bundle identities are unchanged.

Load [installed_acceptance.clj](../../test/installed_acceptance.clj) in a fresh
namespace of a retained packaged-SDK REPL. Its functions separate source/cache/
artifact checks from an explicit independent official-native reference run.
Loading the helper itself starts no process or Project. Static contract tests
are in [installed_import_checks.clj](../../test/installed_import_checks.clj).
