# Constructing casesOn definitions

`ansatz.kernel.cases-on/make-declaration` constructs an abbreviation definition
from an existing inductive and its recursor in an `ansatz.kernel.Env`:

```clojure
(require '[ansatz.kernel.cases-on :as cases])
(import '[ansatz.kernel Name TypeChecker])

(def declaration
  (cases/make-declaration existing-env (Name/fromString "MyType")))
(def extended-env
  (TypeChecker/checkConstant existing-env declaration))
```

Construction and admission are separate. Construction returns a complete
`ConstantInfo`; it does not add declarations. Existing lookup memo caches may be
populated. The caller supplies an environment whose declaration data stays stable
throughout the call and decides whether to admit the result.

The algorithm follows Lean commit
[`819816b2`](https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/src/library/constructions/cases_on.cpp).
It preserves recursor universe order and binder annotations, places indices and
the major premise before constructor branches, and handles mutual motives using
`PUnit` in the same way as that implementation. It derives safe/unsafe status
from the constants used by the generated type and value.

Optional `:max-work` and `:max-locals` limits default to 10,000,000 and 100,000.
Consumed Name, Level and Expr paths and generated binder depths are capped at
256. Validation and memoized expression transformations share the work budget;
Name text also consumes that budget. These are host resource limits, not Lean
heartbeat accounting. Unknown options, open expressions, unsupported collection
carriers and exceeded limits throw `ExceptionInfo`. Reflective or concurrent
mutation of kernel objects is outside the input contract.

Tests include families generated and checked by the source kernel, plus complete
structural comparisons against nine captured native definitions: enum,
structure, polymorphic Box, indexed family, both mutual members, nested family,
Prop elimination and unsafe family. The native fixture test removes all nine
answers before construction and checks each result with `TypeChecker` relative
to the remaining native input carriers. Those carriers are assembled without
whole-prefix admission; the test does not certify that prefix. Fixture provenance
and reproduction instructions live in
[`test/ansatz/kernel/fixtures/cases_on`](../test/ansatz/kernel/fixtures/cases_on/README.md).

This API supplies pure declaration construction. It does not install the guest
`lean_mk_cases_on` binding or establish hosted Lean frontend support. Those need
an authenticated guest environment association, faithful declaration encoding,
ownership tests and preparation before executable profiles are sealed.
