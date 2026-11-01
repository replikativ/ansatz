# Host-only managed argument plans

`ansatz.lean.jvm.argument/plan` accepts `[descriptor codec-witnesses arguments]`, where `arguments` is an exact `Object[]`. It returns persistent data:

```clojure
{:constructors [{:tag 1 :fields [7 0]}
                {:tag 0 :fields [{:ref 0} "example"]}]
 :roots [{:ref 1}]}
```

Every reference selects an earlier recipe. Every recipe occurs exactly once in a parent or root; repeated host subtrees are copied. The plan contains no guest Nodes, DataCtor/DataRef instances, owner credits, or admission token. Metadata validation by the authenticated entry publisher remains required. Layout parsing reuses the result decoder's witness helpers; the field-order model uses deliberately changed structural metadata without claiming native authority.

The supported input grammar is the five primitive leaves plus Prod, Option and List. Prod and List use bounded indexed snapshots of `java.util.List`; Prod requires exactly two elements. Option uses `java.util.Optional`; Unit uses `LeanUnit.INSTANCE`, keeping Some Unit distinct from None. Arbitrary Iterable and Clojure ISeq inputs are refused without realizing them; Clojure wrapper conversion is separate. Custom List method execution is host application code, not sandboxed or preempted by this planner.

Budgets match the managed constructor API: 100,000 field/root occurrences, 4,194,304 aggregate integer bits (Long occurrences charge 64), 1,048,576 aggregate UTF-16 units, and existing primitive per-leaf limits. The host walk separately limits occurrences and depth to 100,000 and 128. The validated descriptor's nesting limit of 32 is stricter for the currently supported first-order types. Lists are traversed and constructed iteratively along their spines. An ancestry identity set refuses cycles while allowing copied DAG sharing.

Load the canonical codec/signature/value namespaces, then `src/ansatz/lean/jvm/argument.clj` and `test/ansatz_lean_jvm_argument_checks.clj`. Run `(ansatz-lean-jvm-argument-checks/check!)` from the module directory, or supply an explicit path to `value-codec-witnesses.json`. The 11 test families are host-only models. Reader validation succeeded for 7 implementation forms and 23 model forms; no worker JVM/native execution was performed.

The Project owner must materialize actual runtime-cohort recipe objects, construct and journal the guest roots, then start and drive under one serialized lease. Successful start adopts those credits; clearing aliases performs no DEC. A start failure with uncertain adoption preserves the journal for reviewed whole-branch abandonment. This namespace does not modify that protocol.
