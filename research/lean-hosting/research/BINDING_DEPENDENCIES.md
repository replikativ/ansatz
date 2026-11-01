# Fixed guest dependencies of trusted bindings

A raw host handler is opaque to the guest executable dependency walker. Kernel
publication, error, cancellation and generated-family helpers can therefore be
absent from the closure of the association/frontend roots that resident adoption
already protects. `kernel-host/make-binding` now records `:guest-helper-roots`
for the fixed helper roles read by that handler and its adapters. The constructor
copies the bounded helper map into a persistent map before both declaration and
closure construction, so a caller's Java map cannot later redirect the handler.
It records `:kernel-policy` from the same effective boolean flags and checking
fuel captured by the handler. Unknown helper-map entries are not dependencies;
all provided known roles are protected conservatively, even when a policy flag
currently disables a branch. Checking fuel must be a positive bounded integer.

Resident adoption first matches every actual binding object against the
independently retained `configuration.trusted-bindings`. It then reads declared
roots from those authenticated binding objects, validates their finite structured
Names, and checks their complete actual executable closure against the independent
`configuration.trusted-functions`. The resulting functions are retained in
Context protection. Changing both World and session function maps does not grant
replacement authority; fork, source operations and extern extension still check
these protected objects. A new adoption repeats independent validation before
association helpers execute. Copying or editing a candidate binding map, including
its root/policy fields, fails the original binding-identity check.

`with-externs` admits new binding objects only through the existing independent
application-symbol allowlist. These are explicit trusted host capabilities. Their
fixed helper declarations must resolve against the EXISTING independently trusted
executable registry; actual candidate code cannot authorize itself. Existing and
new binding declarations share one aggregate budget and their full closure is
merged into protection. Binding objects, ABI checks, owner transfer, cache and
Context lifecycle contracts remain unchanged. Re-adopting an extended snapshot
requires independently retained configuration including the newly admitted
binding objects; the old configuration is not silently rewritten.

The declaration format is an immutable vector of structured Name vectors, with
at most 1,024 root occurrences, 256 nodes and 16,384 string characters per Name,
16,384 nodes and 262,144 string characters in total. Duplicates consume budget.
Numeric components use canonical nonnegative decimal strings. Bounds and tags are
validated before executable lookup hashes a Name. A present malformed field,
including nil or an unbounded sequence, is rejected; absence preserves legacy
callback behavior. This does not introspect arbitrary custom callbacks, infer
dynamic dependencies, prove that an absent field means no guest calls, or turn
trusted host code into a sandbox. Arbitrary trusted hosts can construct opaque
bindings; constructor policy metadata is meaningful only alongside that original
binding object's independently retained identity.

This is preparation for an optional ordinary source-inductive profile, not its
activation. A future profile must still authenticate actual helper IR, complete
closure, ABI and initialization provenance; preserve original policy by checking
the old binding's effective policy; seal a coherent fresh graph/evaluator profile;
and open a new checked Context and prefix. The new host namespace changes the
consumer source inventory and requires a fresh reviewed identity. No old live
capture can acquire this behavior by metadata association or Var replacement.

Focused regression tests passed for all provided kernel roles, constructor
policy/helper snapshot behavior under Java-map mutation, bounded malformed Name
metadata (including the exact 16,384/+1 aggregate node boundary), old/new helper
and dependency replacement, candidate binding forgery, legacy callbacks,
fork/extern extension/re-adoption, and explicit application helper admission
against independent code. The eight kernel/resident/native-reset/Project model
namespaces ran 70 tests with 896 assertions, zero failures/errors, in 11.53 seconds
with a 384 MiB heap and 530,243,584 bytes peak group RSS (including the guard).
All 698 source/class/fixture/JAR pins matched afterward and the guarded process
group was disposed. The included suites exercise reference, mutable and JVM
backends; this is not a full Init/native frontend or ordinary-inductive result.
The portable record is
[declared-binding-helper-protection.json](../measurements/declared-binding-helper-protection.json).

This feature adds a host namespace and changes kernel/resident source identities.
A captured hosted frontend must select a fresh reviewed consumer inventory and
profile; it cannot retain the old 257-row identity while loading this new code.
Keeping the previous selected members and adding `prototype.binding-dependencies`
gives a 258-row consumer inventory. That inventory needs its own reviewed profile
and digest; no fresh full-runtime capture is established by the focused tests.
Current source-only file/CodeSource attestation and later packaged profiles stay
separate contracts. Actual helper IR/ABI/closure and ordinary source-inductive
acceptance remain uncompleted gates described above.
