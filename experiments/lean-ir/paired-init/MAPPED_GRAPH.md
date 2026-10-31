# Persistent mapped ModuleData: bounded prototype plan

This is a design, not an implemented runtime capability. The V3 native census
observes 11,233,359 graph objects: 11,233,358 persistent (`rc=0`), one fresh
single-threaded roots Array (`nodeId=0`, `rc=1`), and no MT objects. The source
allocation total is 387,607,953 bytes. Every underlying ModuleData object is
therefore persistent in this exact cohort. Arrays below the root are persistent;
references, closures, tasks and foreign handles are rejected transport kinds.

Keep the ordinary roots Array as a small counted branch-local shell. Store all
other source objects in a separately authenticated immutable arena. Stream the
existing DAG into an indexed binary format containing node offsets, kind/tag,
object-field offsets, scalar bytes and typed immediate domains; use exact
transport node IDs as arena identity. Bind the arena/index to the original
transport SHA and typed-scalar/audit receipts. A checksum merely detects changed
bytes; it does not replace the source-typed domain proof. Positive Nat, signed
Int and MPZ values must remain distinguished. No native addresses are needed.

Use one arena-scoped canonical weak view cache keyed by source index. A live
wrapper keeps the arena lease alive, and cache lookup must return that same
wrapper while any strong alias survives. A dead wrapper may be recreated only
when no guest or host strong alias can observe the old wrapper. Separate arenas
with identical contents do not acquire pointer identity. Reserve a distinct
stable pointer-word interval for the arena (or a collision-checked arena/index
mapping); wrapper GC must not change the guest pointer word. The cache itself
must not strongly retain all wrappers, the SourceBinding, Programs or engines.
All fresh guest frames, references and owned arrays remain ordinary branch data.

This needs a real value-representation boundary, not a new `Node` with misleading
empty arrays. Current Interpreter.Node is final and has public final Object[]
fields and byte[] scalars; hundreds of runtime paths directly read them, some
mutate them, and Clojure source/layout witnesses reflect those fields. Introduce
explicit read accessors (kind/tag/arity/objectField/scalarByte/scalarWord/live
extent) plus a separate mutable-owned representation before accepting a mapped
view as an interpreter object. Update source witness decoders at the same boundary.
Never silently turn `.fields` into an eager recursive materialization operation.

Current obligations checked in Interpreter.java:

* `node`, `constructorNode`, typed ABI and native helpers currently require the
  concrete Node class. They must recognize the authenticated persistent view
  representation with the same constructor/array/scalar distinctions and bounds.
* INC/DEC on persistent values are no-ops. `exclusive` is `rc==1 && !logicalMT`,
  so mapped persistent values are never mutable/exclusive. Destructive REUSE,
  object/scalar writes and array operations must take their existing copy path;
  copy the immediate shell/bytes and acquire its outgoing owned occurrences.
  Persistent children remain shared. Do not deep-copy the entire source DAG.
* `pointerWord` currently mutates PointerMetadata on a Node and binds it to one
  runtimeIdentity. A mapped persistent view must use arena identity separately;
  stamping shared source bytes or adding branch owner metadata to a globally
  shared wrapper would break fork/source isolation. Certified caller/site guards
  remain mandatory. Existing pointer equality relies on Java identity in places;
  canonical live views must preserve it, or those sites need an explicit identity
  accessor before support is admitted.
* ForkCopy currently eagerly clones every reachable Node, fields array, scalar
  array and metadata. Share an arena reference only for source-proven immutable
  views, using the same fork memo as every mutable root. Clone the counted roots
  shell and branch-local mutable values. Existing eager-copy behavior for
  ordinary persistent Nodes remains unchanged until separately justified.
* Host request operands/results, global lookup, logical-region bridge, Java
  constant checking and runtime graph ownership need explicit arena leases.
  Closing a parent must not invalidate a child or outstanding borrowed helper.
  The last live arena lease may close mappings; failed branch journals must keep
  their actual surviving leases. There is no finalizer-dependent correctness.
* Graph import currently stages recipes/ID maps and allocates Node+arrays eagerly,
  with explicit profile limits. A mapped arena needs a separate reviewed import
  profile; raising the current node limit does not implement it. Full checksum,
  record/index/domain validation precedes publishing its first root.

Smallest prototype target: a separate research arena reader, not a full Init boot.
Create a synthetic pinned graph with persistent shared constructors, arrays,
strings, MPZ, Nat and Int slots plus a counted roots shell; then create a bounded
projection from the genuine V3 Prelude-containing part. Prove source-index
sharing, wrapper weak-cache identity across live aliases, stable pointer words
after wrapper GC, close/lease failures, scalar padding/typed-domain correctness,
and rejection of unsupported/mutable source kinds. Measure mapped/index heap and
view allocation counts. No guest execution is needed for this first target.

The next runtime slice can port constructor/array reads, RC0 INC/DEC, ordinary
copy-on-write, pointer guards and fork to this representation, tested on the same
bounded source projection in both drivers. Only after physical APIs, ownership,
layout witnesses and full existing regression gates pass should a new cohort
attempt real full Init finalization. Kernel-store laziness and initialization
status are independent gates; mapped transport alone grants neither.
