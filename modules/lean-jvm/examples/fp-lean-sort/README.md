# Proof-backed insertion sort

This project imports the complete, unchanged
[`InstrumentedInsertionSort.lean`](https://github.com/leanprover/fp-lean/blob/0abeea545d560a324e2561f7210fbd6ed154fa02/examples/Examples/ProgramsProofs/InstrumentedInsertionSort.lean)
from *Functional Programming in Lean*, with a separate [host adapter](Tutorial.lean).
The upstream source SHA-256 is
`7102c8947e7fc0bfc8aaf3df1077a9d0937b9b3ce02f8a8a13525613e5ed7b10`.

The module includes polymorphic sorting, typeclass comparison, a proved array-size
lemma and a termination proof. The native Lean frontend elaborates the whole source;
the JVM executes the selected entry and its dependency/initialization closure.
Execution does not import these proofs into the core Ansatz kernel.

The adapter fixes the element type to Nat or String and returns IO so the sharing
diagnostic has an explicit captured stderr channel. `sortAndOriginal` returns both
the sorted array and the original. The upstream stdin-consuming CLI is a separate
compatibility target; this example does not claim that every function in the module
can be selected or run.

After resolving the candidate SDK and ordinary runtime JARs, run the Java source
launcher with an explicit supported Lean 4.33.1 installation and producer bundle:

```sh
java --class-path "$CLASSPATH" RunSort.java \
  fp-lean-sort "$LEAN_SYSROOT" "$PRODUCER_BUNDLE" "$COMPILER_CACHE"
```

From a Clojure REPL with `ansatz.lean.jvm` required as `lean`:

```clojure
(def runtime (lean/open))
(def project
  (lean/load-project runtime "examples/fp-lean-sort"
    {:compiler {:sysroot (System/getenv "LEAN_SYSROOT")
                :producer-bundle (System/getenv "PRODUCER_BUNDLE")
                :cache (System/getenv "COMPILER_CACHE")}
     :root-module "Tutorial"
     :entries ["Tutorial.sortNats" "Tutorial.sortStrings"
               "Tutorial.sortAndOriginal"]}))
(def sort-and-original (lean/function project "Tutorial.sortAndOriginal"))
(:value (sort-and-original [3 2 1]))
;; => [[1 2 3] [3 2 1]]
(lean/close! project)
(lean/close! runtime)
```

Diagnostic emission depends on actual guest ownership. Its line count is not a
portable measure of allocations or native/JVM performance. This runtime supports
the diagnostic on managed objects/immediate scalars whose provenance is established
before admission; sharing observations of untracked String/BigInteger heap leaves
remain unsupported. Array String observes the managed array, not its String elements.

For prepared artifacts, use the ordinary `prepare-project` / `load-artifact` API and
retain the independently trusted manifest hash. The execution host then needs the
SDK and its ordinary dependencies, without native Lean tools.

## Attribution and source license

The copied upstream module is by David Thrane Christiansen and the Functional
Programming in Lean contributors. The pinned upstream README identifies the original
Microsoft Corporation 2023 book as licensed under Creative Commons Attribution 4.0
International, with subsequent modifications copyright 2023–2025 Lean FRO, LLC.
See the [pinned upstream README](https://github.com/leanprover/fp-lean/blob/0abeea545d560a324e2561f7210fbd6ed154fa02/README.md)
and [CC BY 4.0 license](https://creativecommons.org/licenses/by/4.0/).
The copied file has no modifications; the separate adapter is original Ansatz code.
No upstream endorsement is implied.
