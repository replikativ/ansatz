# Ordinary source inductive preparation

`prototype.source-inductive-preparation/prepare-ordinary` is an explicit host-only
code preparation step. Invoke it before sealing a graph/evaluator profile, opening
a resident Context or preparing a prefix. It does not execute Lean, admit an
Environment, acquire a guest owner, run an initializer or enable nested families.

The input candidate retains its actual original support. The independently
retained configuration supplies catalogue, trusted functions/bindings and kernel
helpers; never obtain this authority by copying the candidate. The effective
kernel policy comes from the independently authenticated original binding's
`:kernel-policy`, constructed alongside that same handler. The optional fourth
policy argument must normalize identically. Inherited flags and checker fuel are
preserved. A support/configuration policy alone cannot widen the opaque handler.

Two explicit artifact packets, `:publication` and `:encoding`, supply source/IR
bytes, independently trusted SHA256s, finite byte/declaration bounds, and the FULL
expected root ABI inspected from actual pinned exporter output. No ABI or digest
is inferred as authority from the loaded artifact. Initializer-free classic local
manifests are required; imported metadata is retained and any required initialized
global must already be ready. All overlap rows reconcile, and all actual existing
and missing static dependencies are walked; unresolved executable frontiers fail.

The resulting immutable branch preserves every old executable object and all
non-code World storage. One newly constructed kernel binding is shared by the
candidate, independent support session and configuration. Its declared fixed guest
helper roots enter the existing resident protection contract. Candidate and support
trusted registries and catalogues are updated together. Old packets stay valid;
no existing Context/prefix is edited. Already sealed graph/install/prefix inputs
are rejected because adjacent map updates cannot alter closures captured earlier.

Composition order is therefore: authenticate/restore/check the original base;
prepare ordinary helper code; build a NEW graph profile/eval-binding/install-options
using the returned catalogue/registry/helpers/bindings; construct independent actual
and trusted sessions with those exact graph binding objects; open a NEW checked
Context; prepare a NEW prefix; finally use public Project operations. This module
is the pre-seal kernel building block, not a replacement for graph profile sealing.
It never retrofits a live graph profile or reuses a prefix from older bindings.

`KernelSourceInductivePublication.lean` is source for the proposed borrowed family
publisher; expected-root ABI remains an explicit caller gate. Model preparation
tests authenticate/link/check ownership metadata without executing those modeled
functions. They are not genuine Lean publication or whole-Project acceptance.
Actual native helper output, real generation/reprojection/publication tests and a
fresh authenticated consumer capture remain separate required integration gates.
Native sysroot/toolchain failures must not be disguised by guessed borrow flags,
filtered initializer inventories or a weakened Context admission check.

Failures preserve the original candidate/configuration/policy and original cause
in private exception data. These are borrowed diagnostic packets, never serialize
them or treat them as retry authority. No guest effect has run in this stage.


Validation: focused preparation/kernel-host/resident helper-protection regressions
passed 31 tests and 406 assertions. Actual pinned Lean4.33.1 local exports contain
48 publication declarations and 58 encoding declarations, with no local initializer
actions; their complete manifests and source/output hashes are retained under
`fixtures/source-inductive/`. The encoding output's 44 names shared with the existing
transitive fixture have identical complete rows. The other imported dependencies
must still come from the independently authenticated catalogue. This is host
preparation and artifact/ABI evidence; a fresh full restored-catalogue composition
and genuine Project source-inductive acceptance remain outstanding.
