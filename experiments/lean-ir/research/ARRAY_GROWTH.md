# Array growth storage proposal

This is a deferred optimization proposal. It has not been implemented or tested.
The current runtime continues through semantic Init and ordinary-file gates;
this observation does not justify another immediate execution pause.

## Bounded evidence

[The bounded sample](../measurements/hosted-array-push-sample.json) records 64 normal guest array pushes
ending at guest step 538,097,685. All sampled input arrays had RC1. Their input
field counts totaled 6508, averaging approximately 102, with a maximum of 276.
No large array was observed in this window. A separate 64-call dispatch sample
contained 13 each of Array.push, USize.add, Array.append.foldlM and USize.decEq,
plus 12 Array.ugetBorrowed calls. Dispatch frequency alone does not establish
that field copying dominates total compilation time.

## Candidate

`runtime_prim/exclusive-array` obtains vector fields through `node!`.
Push/pop computes a vector and `replace-fields` borrows the CURRENT node again
before replacing its fields. `mutable/replace-node!` currently converts every
replacement's fields to a private `Object[]`. Thus repeated unique pushes and
pops can repeatedly convert and copy complete storage.

A narrow candidate is to preserve immutable vector fields only for array-kind
replacement. Nonvector replacement still copies storage. Refs, tasks and new
allocations keep their existing behavior. Repeated push/pop could then use
persistent-vector structural updates; a later unique element store would acquire
its private array through the existing `writable-fields!` path. Alternating
structural updates and element stores may still copy complete storage.

The FIRST push on existing `Object[]` storage can currently convert old fields
TWICE: once through `exclusive-array`/`node!`, and again when `replace-fields`
re-reads `:node` for current RC/metadata before overwriting its fields. Preserving
replacement vectors would remove repeated steady-state conversions, but would
not by itself remove this initial duplication.

## Ownership and snapshot constraints

Keep the current-node re-read after releasing the popped or overwritten element;
related RC effects must not be overwritten by stale node metadata. Copying host
storage performs no guest retain/release. A pushed value transfers its existing
owner into the array; pop releases exactly the removed owner. Shared and RC0
arrays must still retain contents into an exclusive copy and consume the old
array owner. Imported NativeSource arrays remain immutable. Preserve tag,
current RC and other valid node metadata.

Freeze can share immutable vectors and must continue cloning owned arrays.
Original snapshots and independent forks must remain unchanged. Borrowed reads
must not leak mutable storage. Array-specific storage preservation must not
change persistent ref/task mutation semantics or guest allocation/fuel counters.

## Native profile limits

Upstream `src/runtime/object.cpp` (`lean_array_push` and `lean_copy_expand_array`)
uses spare capacity when possible and can allocate a new native pointer even
for a unique array when capacity is exhausted. Native copy/expansion transfers
exclusive element owners, or retains elements when copying a nonexclusive array.
`src/include/lean/lean.h` implements pop by ensuring exclusivity, reducing size
and releasing the removed element.

The prototype already abstracts spare capacity and preserves its guest Ref on
unique growth. Array capacity is not queried by the currently supported array
runtime. Some represented nodes have `:native-capacity` metadata, which existing
structural updates may leave stale. This proposal preserves the existing logical
array/RC profile; it makes no exact native capacity, allocation-pointer identity
or growth-policy claim.

## Focused validation after semantic gates

Use a deliberately large unique array and repeated pushes/pops to count full
field conversions (`vec` on `Object[]` and `object-array` on large fields).
Compare against the reference world: fields, RC, releases/events and guest
allocation/fuel counters. The candidate should bound conversions by transitions
between representations rather than by every structural update; do not use
wall-clock ratios as a correctness assertion.

Cover two forks and original snapshots; freeze followed by continued parent
writes; push→element-store→push transitions; shared/persistent/imported inputs;
and popping a resource with exactly one release. Retain native ownership probes
where useful, without asserting unmodeled capacity or pointer behavior.
