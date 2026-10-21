# Checking a completed or restored import result

`check-restored-import.clj` is a definitions-only experiment helper. It consumes an explicit
completed guest finalizer IO result through the existing strict checker and kernel association
path. It performs no archive restore, bootstrap, assembly, guest finalization, source compilation,
or source/lease acquisition or closure. It is not a public Ansatz bootstrap API.

This fills the post-restore checking boundary needed by the full-Init campaign. Its tests do not establish full-Init capture or restoration. A later
[Oct20 producer run](../measurements/full-init-finalized-capture-oct20.json) completed
full-Init finalization and durable capture. Fresh restoration subsequently reached
precheck without replay. The original strict projection attempt was stopped for
resource pressure. The subsequent [compact full-profile run](../measurements/full-init-strict-resident-acceptance.json)
passes fresh strict checking and the ordinary resident source/macro/diagnostic/interop
sequence. Small genuine KernelImportProbe checkpoint/source acceptance is separate
earlier evidence.

## Explicit operation

Run from `experiments/lean-ir`. Loading the script defines functions only:

```clojure
(binding [*ns* *ns*] (load-file "scripts/check-restored-import.clj"))
```

After an independently authenticated restore and a separate resource-budget decision:

```clojure
(def strict-control
  (prototype.restored-import-check/prepare
    restored
    {:trusted-functions (:trusted-functions restored)
     :trusted-bindings (:trusted-bindings restored)
     :kernel-helpers approved-kernel-helpers
     :kernel-policy approved-kernel-policy
     :fuel 20000000
     :observe! prn}))

(def checked (prototype.restored-import-check/check! strict-control))
(prototype.restored-import-check/summary strict-control)
```

Here `restored` is the **actual** returned checkpoint packet, including `:world`, `:session` and
owned `:io-result`. Its trusted registries must be those independently reconstructed by the
approved binding factory. Deriving them from the candidate world's function map would abandon
that independent authority boundary. This helper does not authenticate archive bytes, loaded
code, factory policy or the claim that the result came from Lean's real finalizer.

The selected helpers are the effective merge with `module-import/helpers`. The checker validates
`:constants`, `:root`, `:constant-map` and `:quot-init?` and their transitive executable identities,
including defaults omitted from the explicit overrides. Binding keysets and every binding object
must match the independent registry exactly. Entry execution must be idle with matching
world/session function-map identity, the exact live IO result, and no kernel association. Saved
certificates and phase flags grant no checking authority.

Fuel applies separately to every raw helper invocation. It does not bound Java checking, host
work, total guest instructions, wall time or memory; keep the external process/resource guard.
Finalizer attestation/header overrides are deliberately outside this helper's admitted options.
The normal strict quotient-state rule remains in force.

## Separate compact checking consumer

`prototype.compact-import-check` offers the same explicit `prepare`, `check!`,
`summary` and `checkpoint` lifecycle with a separately named host consumer. It
uses `prototype.compact-kernel-projection` and a primitive typed long-ID memo to
avoid retaining vector/reference keys for every projected node. Non-reference
keys retain the original equality semantics. This is an experiment, not a default
runtime change or a new checkpoint format.

Compile its new helper from `experiments/lean-ir`:

```sh
javac -d target/compact-projection-classes java/prototype/TypedLongMemo.java
```

Add `target/compact-projection-classes` to the experiment classpath and explicitly
require `prototype.compact-import-check`. A full restore launcher must separately
pin its source, helper class and selected class resource, in addition to authenticating
the unchanged original factory inventory. Restoring build50f and checking through
this consumer are distinct identities; no checkpoint is relabeled or initializer
replayed.

The consumer reuses the pinned projection specification and grouping/quotient
helpers through read-only private Var adapters. It preserves duplicate/dependency,
axiom/safety, mutual/inductive, fresh-Env checking and exact association rules. It
rejects injected projection certificates. The admission/control code is an explicit
experimental copy so the original factory inputs remain unchanged; consolidating
these adapters behind public shared APIs is later work. No live Var replacement is
used. `summary` additionally reports scalar projection, dependency, admission and
association stages. Partial projection state is not resumable.

The [compact validation receipt](../measurements/compact-import-consumer-validation.json)
records 802 tests / 88,618 assertions passing on the final formatted sources,
including complete small-fixture parity. The separately recorded genuine full-profile
sequence subsequently passes all 65,994 declarations and resident acceptance;
independent native-map/extension-state parity remains unverified.

## Result and failure ownership

A successful `:ok` result owns `:environment` and carries the actual certificate and latest raw
session. The existing `finish-finalization` checks the complete final guest constant map and
associates its exact protected roots. An `:io-error` result retains the same owned IO error and
runs no helper/checker call. No eager second native whole-map certificate is built; native versus
guest full-map parity remains a separate, potentially memory-intensive validation gate.

Each controller has one claimable operation. Its phases are:

```text
ready → checking → checked
                → guest-io-error
                → failed
```

Concurrent/reentrant calls cannot enter checking again. Failed calls cannot retry effects.
The exact returned result is retained before status assertions or observer calls. An observer
failure therefore leaves a successful checked packet available for deliberate ownership cleanup,
while the controller itself becomes terminal. The observer receives only a scalar summary.

`checkpoint` borrows the entry, current raw progress, returned result and failure evidence. Do not
print or serialize this whole map. Exceptions retain the same controller-owned entry/result/
progress under reserved keys, while child `:checkpoint` and `:checkpoint-session` remain intact.
A callback can change backends before failing; its newer session must not be replaced by the last
successful sibling session. Original owned IO and post-consumption Environment snapshots remain
separate diagnostic alternatives; never pair an old root with a different newer world.

There is intentionally no source or ResourceLease close method on this controller. Keep the
caller's lease open while checked results, resident contexts, diagnostic worlds, controllers,
exceptions, futures or other borrowers reference the source. Release/discard those borrowers
before closing the lease. Retaining the controller retains its diagnostic worlds. A fresh
controller over an old snapshot is not authorization to replay external effects after failure.

For subsequent source acceptance use the real checked Environment with
`resident-preparation/open-checked` and the independently prepared frontend/Name encoder
closures. That is a separate adoption step; this helper does not link those closures, acquire
Options, add compiler markers, alter import headers or claim ordinary-source compatibility.

## Validation scope and reproduction

The focused tests use a **model Environment layout and small guest helper IR**, executed by the
real reference, mutable and JVM runtimes. The constants are genuine transported native
KernelImportProbe ConstantInfos; the current Java checker strictly verifies all 17 declarations
and all eight variants, the sole ordinary axiom A, unsafe policy and canonical quotient state.
These are not captured Lean helper bodies or a new genuine finalizer/checkpoint run.

Tests cover changed transitive/default helpers, binding substitution, malformed/active entries,
IO error ownership, actual strict policy rejection, a real callback/backend switch followed by
failure, observer failure with conflicting diagnostic keys, and concurrent/reentrant claims.

```sh
clojure -J-Xmx512m -M -e \
  "(require 'prototype.restored-import-check-test) \
   (let [r (clojure.test/run-tests 'prototype.restored-import-check-test)] \
     (shutdown-agents) (System/exit (+ (:fail r) (:error r))))"
```

The new test is invoked explicitly. Existing `prototype.test-runner` and the prior factory's
242 inventoried runtime inputs are unchanged. The new script/test must be pinned separately by
a future full restore launcher; their addition does not silently change an approved old build,
restore profile or checkpoint pin. Existing ignored `full-run-v4` control files are not rewritten.

The [validation receipt](../measurements/restored-import-check-validation.json) records 9 focused
tests / 107 assertions and 791 runtime tests / 66,396 assertions passing, independent review,
and preservation of the 242 original on-disk preparation inputs. The full runtime run preceded
whitespace-only formatting; the final formatted sources pass the focused tests. The isolated parent library suite subsequently passed 822 tests / 3,591 assertions
on 2026-10-20. Optional Mathlib integration was excluded. Earlier shared-store and
resource refusals remain recorded. The subsequent full-profile strict and resident acceptance is recorded above;
independent native-map/extension-state parity and source-module import/edit remain open.
