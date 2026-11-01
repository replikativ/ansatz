# Array runtime profile

The Java engine implements the original object-array externs used by the first
header-parser path, against Lean 4.33.1 commit
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`. This is a bounded single-thread
runtime profile, not the complete Lean array or scalar-array API.

Exact original declarations and all fourteen genuine boxed wrappers are in
[test/fixtures/java-array-runtime](../test/fixtures/java-array-runtime/README.md).
They preserve full erased/proof parameters, raw result lanes and borrow flags.
Covered operations are empty-with-capacity (both names), push, pop, primitive
usize, owned and borrowed Nat/USize getters, Nat/USize setters, proof-backed
swap, toList and replicate. Checked panic/default getters, checked swap, arbitrary
capacity, byte/scalar arrays, and native concurrency are separate work.

`Node.fields` remains final storage; `Node.arraySize()` reads its live prefix
from private array metadata, without adding a counter to ordinary constructors. Capacity
can exceed size. Spare slots are null, own no values and never participate in
get/size results. Destruction visits only the live prefix, matching native O(size).
Prepared graphs continue describing only live elements; import
sets capacity=size. Fork copies live size, capacity and aliasing into independent
storage. Ordinary constructor operations reject arrays rather than treating
spare capacity as constructor fields.

A positive RC1 array mutates in place when capacity permits. Unique growth uses
Lean's geometric `(capacity + 1) * 2` rule, transfers element credits into a new
shell and invalidates the old shell without decrementing its transferred children.
Shared and RC0 arrays copy each live occurrence, retain each copied child edge,
then consume the old container once. Persistent RC0 never grants exclusivity.
Maximum capacity is explicitly one million elements; capacity/index checks occur
before array mutation. These bounds reject operations outside this research
profile rather than emulating native out-of-memory or unsafe memory access.

Push transfers its incoming value. Pop clears and releases the last live slot.
Set replaces and releases the old value; supplying an aliased value requires its
separate owned credit. Swap exchanges owners without inc/dec. Replicate consumes
its value once, retaining n-1 additional occurrences or releasing it for n=0.
ToList retains each live element into ordered List cells and consumes the array.

Owned getters retain the returned element. Borrowed getters do not. Their
original boxed wrappers decrement the owned array argument without upgrading the
result's ownership; these unsafe compiler operations require the caller's lifetime
discipline. Direct external entry/PAP into borrowed array primitives requires an
owning guest wrapper, as in the earlier interpreter contract. This does not make
an unsafe borrowed wrapper result independently owned.

Eight focused tests / 79 assertions pass with each driver configuration. They
cover exact source ABIs, geometric growth, unique reuse, shared/persistent alias
counts, pop/spare clearing, setters, swap, list order, replicate zero/many, owned
and borrowed getters, USize boxing, fork isolation and bounded failures. The
combined isolated jar gate passes 422 executions / 14,022 assertions across
49 suites, including both array test invocations, at 384 MiB. A guest failure still has the existing
explicit-driver ownership-cleanup limitation; it is not an import transaction.

The demand-loaded original header program now loads five original bodies and
executes sixteen IR instructions before the next missing runtime primitive,
`String.Pos.Raw.atEnd`. It uses the selected 47,240-node prepared companion and
the compact code catalogue in a retained 384 MiB JVM. This establishes progress
through array creation, not full header parsing, source elaboration or self-hosting.
