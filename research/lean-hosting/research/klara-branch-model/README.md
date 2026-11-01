# Small pure branch/store reference

`BranchModel.lean` imports only `Init`. Its named theorems use neither admitted
proofs nor axioms, including Lean's standard logical axioms (the verification
script checks each theorem with `#print axioms`). It is a small specification
fragment, not a proof of either interpreter, a concurrency model, an ownership
proof, a capability API, or a full Klara model.

The store is a total map from natural-number cell identifiers to natural-number
values. Two aliases are equal identifiers. `write` returns a new map; `fork`
returns two views of the old map. The theorems establish reads after writes,
unchanged distinct cells, alias observations, and retention of the sibling's
old value. They say nothing about allocation, reclamation, object identity,
reference counting, arbitrary JVM objects, or performance.

The authority state has open, claimed, complete and incomplete phases. `choose`
selects one branch; `settle` folds an explicit list of synthetic callback
outcomes and closes the family. The first false result counts as an attempt,
does not count as a receipt, and stops traversal. Complete and incomplete
families reject both a second choice and settlement replay. Receipts never
exceed attempts. Real IO and callback execution are outside the model.

Family minting and fresh identifier allocation are trusted external operations.
The host must retain the latest family state in a registry outside guest
snapshots and serialize registry transitions. A caller that copies an old
*family* state can reuse it in this pure model. The theorems constrain state
transition sequences using the current state; they do not prevent hostile host
code from restoring old authority, provisioning another family, forging an ID,
or executing a callback outside this protocol. Runtime authority registry
concurrency, asynchronous interruption and crash recovery require separate
reasoning.

For a differential check, relate model cell IDs to the host adapter's opaque
identifiers by a fixed injection, relate lookup values at those identifiers,
and relate phase/branch/attempt/receipt observations. The samples initialize
cell 0 and another untouched cell 1 to `base`, fork, then write cell 0 in each
child. The direct and alias observations both use ID 0. A real closure capture
and host mint must be exercised on the adapter side. Successful finite sample
comparison does not establish the relation for all executions.

Run using an already installed native Lean executable:

```sh
LEAN_BIN=/path/to/native/bin/lean python3 research/klara-branch-model/verify.py
/path/to/native/bin/lean --run research/klara-branch-model/BranchModel.lean
```

These commands are relative to `experiments/lean-ir`. Verification records the
actual compiler version and writes `sample-results.jsonl`. No Lake build,
download, JVM restart, frontend export or large Init image is required. The
source checkout at `../lean4` had no built native binary when checked; the
recorded run instead used the already installed native Lean 4.33.1 toolchain
used by other experiment commands. No source checkout was changed.

The output is JSONL, 27 store rows and one authority row. Store inputs enumerate
`base ∈ [0,1,2]`, `left ∈ [0,10,20]`, `right ∈ [0,10,20]`. The seven observations
are `[parentDirect,leftDirect,leftAlias,rightDirect,rightAlias,leftOther,rightOther]`.
The authority row checks a second choice while claimed, successful settlement
of two outcomes, and incomplete settlement of `[true,false,true]`; incomplete
settlement records two attempts and one receipt, then rejects replay/choice.
