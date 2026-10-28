# Five-step Klara / Lean REPL results

The bounded five-step experiment is complete. Production interop and the
resident frontend are unchanged. No JVM restart, guest Init image or full
frontend campaign was run. Runtime measurements and tests used the existing
384 MiB Java 25 REPL. Native Lean separately elaborated the small source fixture
and checked the mathematical model.

## 1. Common observation contract

The [branch contract](KLARA_BRANCH_CONTRACT.md) separates definition basis,
guest store/control, branch-local host cells, pending intents and trusted
settlement authority. Klara's actual definition-world implementation was
loaded into the REPL: parent version 2 coexists with a pinned fiber, a Klara
child and both executed Lean alternatives still carrying version 1.

This is composition of roots, not shared definition resolution or interpreter
equivalence. Family settlement remains a single choice among alternatives;
it does not grant independently spendable external rights to every child.

## 2. Cost attribution and private execution

[The probe](klara_branch_probe.clj) prepares independent mutable inputs before
accounting. Each sampled input executes once, preventing repeated freezes of a
warmed machine from masquerading as fresh boundary materialization. Allocation
is current-thread JVM ThreadMXBean allocation, not retained memory. All samples
and scope information are in the [measurement record](../measurements/klara-branch-five-step.edn).

For one complete tiny compiled execution, phase medians were approximately:

| Phase | Allocation |
| --- | ---: |
| Initial thaw | 9.7 KB |
| Resume to output request | 5.3 KB |
| First freeze | 7.8 KB |
| Second thaw | 11.4 KB |
| Resume to completion | 1.1 KB |
| Final freeze | 6.9 KB |

About 85% was restoration/materialization. This justified an experimental
`scoped-runner`: it retains a private Machine while servicing only the closed
descriptor table, and freezes at the next exposed suspension, pause or
completion. No arbitrary handler observes the mutable machine. A fork at that
exposed boundary still receives an ordinary immutable packet. Unknown effects
fail closed; they never trigger an effectful fallback or replay.

Matched compiled fork/two-resume/adopt trials:

| Fixture | Materialize every request | Scoped execution | Allocation reduction |
| --- | ---: | ---: | ---: |
| Handwritten guest reference/closure | 93.2 KB | 57.5 KB | 38% |
| Frontend-generated Lean reference/closure | 170.3 KB | 116.0 KB | 32% |
| Host-cell descriptors, handles as arguments | 150.6 KB | 52.0 KB | 66% |

An earlier host-cell encoding embedded opaque cell records as code constants.
The conservative register-layout proof cache correctly declined to reuse
proofs for those custom collections. Passing cell identities as runtime
arguments leaves code independent of branch instances and restores reuse.
Combined with scoping, compiled allocation fell from roughly 426.4 KB in that
earlier encoding to 52.0 KB. This is a representation lesson, not a change that
relaxes code validation or treats mutable payloads as immutable proofs.

The persistent reference path still allocates less on the tiny host-cell
workload (31.8 KB). These short programs cross many boundaries and contain no
substantial numerical loop; the results do not establish general throughput or
retained-heap performance. Timings are exploratory, with sequential sample
ordering and JVM tiering. No production World handler contract changed.

## 3. Branch-aware host cells

[host_cells_lab.clj](../src/prototype/host_cells_lab.clj) provides scalar cells
whose identities resolve through a persistent branch-local store. Closures can
retain an identity while observing different contents in different branches.
Guest requests use explicit read/write/output descriptors; arbitrary host
functions are not callbacks on this path. Atoms and other mutable payloads are
rejected. Ordinary raw JVM interop retains its existing behavior.

Each allocation carries a fresh identity token in addition to its local index.
After a fork, siblings can reuse an index without accidentally making their
new cells aliases. Cross-sibling access rejects; inherited cells retain their
identity. This was found in independent review and regression-tested.

These identity tokens are in-memory data, not serializable store addresses,
security capabilities or external-resource authority. There is no merge,
general recursive value schema or durable memory format in this adapter.

## 4. Generated Lean and ownership-ledger composition

[The Lean source](../fixtures/klara-branch-ref-closure.lean) creates an `IO.Ref`,
captures it in a closure, and passes both as borrowed arguments to the explicit
choice hook. The native frontend produces the [selected IR closure](../fixtures/klara-branch-ref-closure.jsonl):
10 declarations, without loading a guest Init image. Only the two explicit lab
externs are adapted. Generated callers, closures and RC instructions remain
unchanged. Producer hashes, ABI checks and reproducible commands are in the
[provenance record](klara-branch-generated-provenance.edn).

`admit-choice` validates that specific choice request before representing it as
an input suspension. It cannot admit pending output or arbitrary host effects.
Branches then update the shared reference identity independently, invoke their
captured closures, and queue 10 or 20. Generated instructions free the reference
and closure before output. The sole returned successful IO result is explicitly
released; each completed guest heap becomes empty. The original paused parent
keeps its own live owners and remains unchanged.

The fixture composes with the existing coherent owner ledger for that one
returned owner. Cleanup binds one operation key, escrows its actual returned
World before post-validation, and never repeats a completed or failed drop.
Invalid results and extra/resource owners are rejected before release. A
combined test selects one branch, retires both alternative result owners via
separate cleanup ledgers, and preserves the original parent.

Family adoption and owner cleanup are separate ledgers, without atomicity
between them or crash recovery. This is not resident Context/Source ownership
integration. Provisioning a new ledger for the same owner would be a new trusted
authority grant; hostile host code is outside this experiment's guarantees.

## 5. Small formal reference and differential checks

[BranchModel.lean](klara-branch-model/BranchModel.lean) defines a pure store,
aliases, fork isolation and synthetic family selection/settlement. Native Lean
4.33.1 checked 13 theorems; an axiom audit reports no axioms for any of them.
The [verification record](klara-branch-model/verification.txt) and
[model scope](klara-branch-model/README.md) distinguish these statements from
runtime enforcement.

The [JVM differential tests](../test/prototype/klara_branch_model_test.clj)
compare all 27 generated store cases against persistent, mutable and compiled
execution, both materialized and scoped: six paths per case. They also compare
the successful and incomplete settlement observations, including attempts,
receipts, blocked second choice and blocked replay. Captured host-cell aliases
and an untouched second cell are observed on the runtime side.

This proves the elementary pure model's stated invariants and supplies finite
runtime agreement. It does not prove interpreter refinement, RC/storage
ownership, concurrency, fresh-ID enforcement, arbitrary IO or the full Klara
memory model. Proofs were checked by native Lean, not imported into Ansatz's
kernel in this experiment. Trusted authority minting and current-state registry
discipline remain explicit assumptions.

## Validation and next decisions

58 focused tests / 2,594 assertions passed, covering the experiment and existing
mutable, field-copying, persistent-snapshot and lazy-runtime suites. The model
verification passed separately. Independent review covered scoped execution,
authority races, generated lifetime cleanup, identity allocation and proof
scope. Local documentation links and whitespace checks passed. Full repository
tests, fresh-JVM packaging and a full hosted frontend image were not run.

The evidence supports preserving the separate engines and sharing the semantic
contract. A next implementation decision is where to expose a production
scoped effect ABI, including pause/capture policy, typed runtime handles and
failure checkpoints. It should retain existing World handlers for callers that
need them. General authority splitting, native resources, RNG/budget policies,
durable cells and runtime refinement proofs remain separate work.
