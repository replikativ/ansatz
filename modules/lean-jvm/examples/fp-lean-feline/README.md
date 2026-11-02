# Unchanged two-file Feline tutorial

[Main.lean](Main.lean) imports [FelineLib.lean](FelineLib.lean), which owns the real
`main : List String → IO UInt32`. Both files and the original lakefile are copied
unchanged from *Functional Programming in Lean*, commit
[`0abeea545d560a324e2561f7210fbd6ed154fa02`](https://github.com/leanprover/fp-lean/tree/0abeea545d560a324e2561f7210fbd6ed154fa02/examples/feline/2).
[provenance.json](provenance.json) records exact hashes. Attribution and upstream
licensing notices remain with the [book repository](https://github.com/leanprover/fp-lean/tree/0abeea545d560a324e2561f7210fbd6ed154fa02).
No upstream endorsement is implied.

The book is by David Thrane Christiansen. Its original version was released by
Microsoft Corporation in 2023 under [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/);
the pinned repository credits subsequent changes to Lean FRO, LLC, 2023–2025.
The copied files are unchanged; this README and the JVM harness are Ansatz additions.

Feline concatenates files and `-` stdin entries in argument order, copies raw
bytes in 20 KiB chunks, reports missing paths and continues with exit status 1.
With no arguments it copies stdin. It constructs real `Stream.ofHandle` closures;
no imports, algorithms or IO methods have been replaced with JVM-only adapters.
The original lakefile has no external package dependency. Preparation here uses
the SDK's pinned Lean 4.33.1 frontend; it does not run Lake or require SubVerso.

The integration candidate passes source loading, cache reuse and prepared-artifact
loading for eight regular-file/stdin cases, with repeated retained handles.
Independent native comparison and policy/failure checks are separate acceptance
steps. This is candidate validation, not a published-release claim or full book
compatibility. The [filesystem contract](../../FILESYSTEM.md) describes the
explicit service configuration, resource limits and unsupported domains.

[filesystem_acceptance.clj](../../test/filesystem_acceptance.clj) provides explicit
functions for source/cache/artifact checks, native references and failure branches;
loading it starts no process. [FelineSmoke](../../consumer/FelineSmoke.java) loads
the prepared artifact from an application JAR with public Java/Clojure APIs.
Execution does not import proofs into the core Ansatz kernel or self-host the
Lean frontend.
