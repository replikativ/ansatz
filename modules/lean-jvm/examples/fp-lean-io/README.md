# Unchanged interactive FP Lean programs

These complete source files are copied unchanged from
[Functional Programming in Lean](https://github.com/leanprover/fp-lean/tree/0abeea545d560a324e2561f7210fbd6ed154fa02/examples),
pinned at `0abeea545d560a324e2561f7210fbd6ed154fa02`. Exact paths and SHA-256 hashes
are in [provenance.json](provenance.json).

| Module / entry | Explicit Lean arguments | Exercise |
| --- | --- | --- |
| `HelloName` / `main` | none | Read a name and print a greeting |
| `EarlyReturn` / `main`, `Nested.main` | `List String` | Read a name, handle empty input and unexpected arguments, capture stderr |
| `ForMIO` / `main` | `List String` | Recursive stream traversal and filtering lines that contain alphabetic characters |

Each module defines its own global main. Load one selected root per Project;
unreferenced files do not become imports. No upstream source rewrite or book
tooling is needed for these standalone programs. The Campaign 2 supplied-stream
API is described in [STDIO.md](../../STDIO.md); it is separate from the released
0.2.583 array-sort example.

```clojure
(require '[ansatz.lean.jvm :as lean])

(def runtime (lean/open))
(def project
  (lean/load-project runtime "examples/fp-lean-io"
    {:compiler {:sysroot (System/getenv "LEAN_SYSROOT")
                :producer-bundle (System/getenv "PRODUCER_BUNDLE")
                :cache (System/getenv "COMPILER_CACHE")}
     :root-module "EarlyReturn"
     :entries ["main" "Nested.main"]}))

(select-keys (lean/call-with-options project "main" {:stdin "Ada\n"} [])
             [:value :stdout :stderr])
;; => {:value 0
;;     :stdout "How would you like to be addressed?\nHello, Ada!\n"
;;     :stderr ""}

(lean/close! project)
(lean/close! runtime)
```

This establishes selected standalone-program coverage, not complete fp-lean or
Lake compatibility. Book chapters importing ExampleSupport/SubVerso retain the
separate external-import limitation. No filesystem handles or process-global
stdin are provided by these options.

## Attribution

The source is by David Thrane Christiansen and the Functional Programming in Lean
contributors. The pinned upstream README identifies the original Microsoft
Corporation 2023 book as Creative Commons Attribution 4.0 International, with
subsequent modifications copyright 2023–2025 Lean FRO, LLC. See the
[upstream README](https://github.com/leanprover/fp-lean/blob/0abeea545d560a324e2561f7210fbd6ed154fa02/README.md)
and [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/).
The copied files have no modifications. No upstream endorsement is implied.
