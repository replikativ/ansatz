# Automatic nominal datatype interop: implementation contract

Status: implemented experimental v3 boundary, with native, public API and
packaged-consumer acceptance. This contract does not establish a published
version or admit a type independently of the source/artifact issuers.
The existing [value conventions](VALUE_EXAMPLES.md), [compatibility policy](COMPATIBILITY.md),
and [release gates](RELEASE_CHECKLIST.md) remain authoritative for current SDKs.
The subsequent host-binding candidate is specified separately in
[FFI.md](FFI.md); later-work references below describe this datatype
milestone's scope.

## Implementation checkpoint

The logical graph, native discovery/layout observations, normalized storage
plans, detached Java values, immutable Clojure views and certified storage reuse
are implemented. The registered v3 cohort binds its exact source closure,
executable and build receipt. Native checked entry data is admitted only through
the actual source issuer or independently hash-validated artifact path.

In a retained 384 MiB REPL, native and JVM oracle results match for a recursive
AST, a mixed record, a scalar-only record and builtin containers. The public
Java/Clojure path also passes the independent three-file expression application:
host construction, custom IO results, aggregate refusal recovery and concurrent
reuse in independent Projects. Its application-JAR consumer needs no Lean or
source checkout. These checks are not a performance measurement.

Source-phase reconciliation compares actual raw/callable IR and all selected
local closure observations against original source rows. New compilation
baselines bind used defining products before compilation and preserve their
custody through helper calls, cache reuse and artifact reopening. A defining
product edit rejects old values even when their apparent layout matches.
Callback FFI, public forks and permissive semantic reload identity remain later.

## Outcome and scope

Selected Lean entries automatically expose their supported, entry-reachable
datatypes to Java and Clojure from native declaration and compiler evidence.
Application authors do not write bindings, schemas, serializers, or wrapper
functions solely to describe each supported datatype.

The target is immutable detached Java `LeanData` values and Clojure
`IPersistentMap` views backed by certified frozen storage that the interpreter
can read directly. First export requires bounded O(graph) validation/freezing;
it must not deep-copy the data payload. Compatible subsequent imports reuse
that storage. Explicit materialization supplies ordinary host collection/byte
snapshots when requested. This shared representation is part of the initial
design, not an optimization postponed until after a copy-based API ships.

Datatype interop precedes callback/extern FFI. Writable IO may progress in
parallel and grants no authority for datatype layouts or shared storage.
The optional SDK remains independent of the Ansatz core kernel/DSL. Native
frontend evidence does not import declarations or proofs into that kernel.

The first public nominal profile covers proof-free, non-indexed closed enums,
empty/trivial/mixed/scalar-only records, ordinary first-order recursive
inductives, and finite monomorphic instantiations of ordinary generic types.
Existing Option/List/Array/Prod/Sum/Except and ByteArray may contain nominal
values, and nominal fields may contain those builtins. Pure and existing IO
entry results are covered. All constructors must pass admission, including
constructors not encountered by a particular call.

Initially unsupported: indexed/dependent families or fields, proof-bearing
host values (including Fin/Subtype), open polymorphic invocation, functions,
opaque/resource/Ref/Task/thunk/Promise/closure fields, cyclic runtime values,
nonuniform recursive instantiations, mutual recursion, arbitrary special runtime
tags, and automatic cross-cohort storage conversion. Mutual recursion needs a
separate SCC discovery/verification acceptance increment. Proof-rich Lean
internals remain possible behind a supported selected host signature.

## Public values and host conventions

Proposed public names describe required semantics; phase 1 fixes exact methods:

- `LeanName`: lossless anonymous/string/numeric components. Dotted text is a
  display, not identity; a string containing a dot differs from two components.
- `LeanTypeId`: authenticated defining-module product identity, structured
  declaration Name, closed type/universe arguments and logical-schema identity.
- `LeanData`: final immutable nominal type, structured constructor Name, and
  ordered logical fields. Actual structure projections may supply named sugar;
  arbitrary constructor binder text does not establish unique field names.
- `LeanBytes`: immutable live-byte access; `toByteArray()` explicitly copies.

Values and descriptors have no Project, engine, Program, Header, source binding,
generation, lease, callback, resource, or Throwable reference. They survive
Project/runtime close and later call failure, and can enter a fresh compatible
Project. Their own application value-class loader is ordinary JVM retention;
they must not retain a per-Project loader or engine. No public raw Node,
backing array, mutable buffer alias, or certificate factory is exposed.

Clojure's canonical nominal view has exactly these keys:

```clojure
{:lean/type detached-type-id
 :lean/constructor structured-constructor-name
 :lean/fields immutable-indexed-fields}
```

Type and Name use immutable Java identity values with explicit lossless EDN
conversion. Fixed keys avoid interning application names as keywords. The map
view implements `IPersistentMap` semantics: lookup, destructuring, seq,
collection equality/hash, and nonmutating assoc/dissoc. It need not eagerly build
PersistentArrayMap/PersistentHashMap objects. Edits create host values; they
never modify storage. No executable reader tags or metadata-dependent identity.

Builtin containers *inside the new nominal value/view path* also use immutable
typed views, preserving sharing instead of recursively copying beneath a nominal
wrapper. Option Unit remains distinguishable from None. Legacy standalone
builtin signatures keep their existing Java/Clojure carriers and byte snapshots;
old artifacts do not silently acquire new results.

Ordinary literal host maps/lists/arrays have no existing Lean storage and require
bounded validation/construction; mutable bytes are snapshotted. Candidate
factories do not confer evidence authority. Exact keys, constructor membership,
field count/type, identity and ranges are checked against the callee's admitted
schema before execution. An unchanged certified view takes the shared fast path;
edited/materialized collections take the ordinary validated construction path.
An explicit bounded materialize operation produces conventional persistent
maps/vectors and requested mutable byte copies.

Graph sharing is preserved internally without promising public reference
identity. Cache views by storage identity **and logical type/representation
plan**, scoped to the returned graph rather than a global strong registry.
`LeanData.equals` compares only LeanData using nominal identity, constructor
and ordered fields under Java value semantics; Float/Double use ordinary boxed
equals/hashCode. Clojure views use ordinary map/sequence equiv and hasheq,
including comparison with equivalent conventional collections. There is no
LeanData-to-map equality promise. Equality/hash are stack-safe. Transport and
scalar access preserve raw Float/Float32 bits independently of equality;
test signed zero and multiple NaN payloads separately. Diagnostic printing is
bounded and does not invoke arbitrary input methods.

## Native schema and layout authority

Introduce one new versioned evidence cohort (proposed entry schema v3); preserve
v1/v2 producer hashes, admission rules, limits, carriers and error behavior.
`NativeGeneralEntryEvidence.lean` extends actual native telescope/safety/DefEq
checks with a bounded definition graph. A provisional node keyed by canonical
closed native type breaks regular recursive discovery. Closed aliases normalize
according to native evidence; distinct inductive declarations stay nominally
distinct. Reject unsupported closure rather than guessing erased IR types.

Each nominal definition binds its authenticated origin, closed application,
constructor identities, logical ordered field telescope and instantiated lowering
to actual persisted `LCNF.getCtorLayout`, trivial-structure and impure-type
evidence. A logical field must not depend on an earlier field value. Type
parameters are not value fields; proof erasure is not permission to admit proofs.

Keep logical-schema and target/lowering fingerprints separate. Canonically
serialize the finite graph with deterministic IDs to hash recursive definitions.
Type identity must not depend on selected entry lists or Project identity.
Defining-module products/import provenance prevent same-Name substitutions;
different layouts with the same logical identity still require explicit
compatibility. First admission conservatively requires the admitted matching
origin/schema/cohort and compatible actual storage classes.
This conservative product identity may invalidate values after an unrelated
function edit in the same defining module. Permissive semantic reload
compatibility requires a separately reviewed authenticated origin policy;
dropping the product digest is not that policy.

The consumer verifies exact reachable closure, references, constructor families,
field correspondence, disjoint/bounded scalar slots, legal tags and all extent
arithmetic. Public host schemas do not authorize reads/writes. Do not extend a
fixture-specific family table and call that arbitrary-application discovery.

Representation plans explicitly cover enum result lanes; empty and erased
one-field wrappers; generic boxing versus concrete scalar fields; object,
usize and grouped-width scalar positions; target width/endianness; and known
value-unit erasure. Ordinary allocated tags remain in the reviewed 0–243
domain. Native compiler behavior is pinned to the admitted Lean cohort;
`ToImpureType.lean`/`ToImpure.lean` are authority for lowering, not host guesses.

The phase 1 model below fixes 256 nominal instances, 1,024 constructors,
64 fields/constructor, 4,096 schema edges and a 1 MiB encoded graph ceiling.
Existing runtime leaf/aggregate
limits remain unless a reviewed change states otherwise. Add explicit limits
for graph nodes/edges, logical depth, payload validation and materialization.
Check overflow before allocation. DAG-aware saturated statistics must bound
logical occurrences without exponential unfolding; do not blanket-raise all
limits to admit new types.

## Phase 1 exact logical wire/model

`ansatz.lean.jvm.type-graph` implements the following internal model only.
The v3 source and artifact paths integrate this model with checked native entry
and layout evidence. This pure model alone grants no entry authority.
All keys below are required string keys; unknown keys are rejected at every
level. No JSON null, open variables, term parameters, proof or dependency
expression grammar exists in this version.

```json
{
  "schema": "lean-jvm-type-graph/3",
  "roots": [{"kind": "nominal", "id": 0}],
  "definitions": [{
    "id": 0,
    "origin": {
      "module": ["str", ["anonymous"], "Example"],
      "productSha256": "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
    },
    "name": ["str", ["str", ["anonymous"], "Example"], "Tree"],
    "universes": [],
    "arguments": [],
    "constructors": [{
      "name": ["str", ["str", ["str", ["anonymous"], "Example"], "Tree"], "leaf"],
      "fields": [{"name": ["anonymous"], "type": {"kind": "nat"}}]
    }, {
      "name": ["str", ["str", ["str", ["anonymous"], "Example"], "Tree"], "children"],
      "fields": [{"name": ["anonymous"], "type": {"kind": "list", "element": {"kind": "nominal", "id": 0}}}]
    }]
  }]
}
```

Type descriptors have exactly the existing v2 builtin shapes (`nat`, `int`,
`bool`, `string`, `unit`, `char`, `bytes`; machine-int bits/signed; word signed;
float bits; product first/second; option/list/array element; sum left/right;
except error/value), plus `{"kind":"nominal","id":N}`. Nominal IDs select
closed definitions, not open constructors or type variables. Definition
arguments are closed type descriptors; universes are normalized closed natural
levels, not arbitrary Lean Level syntax. The native classifier independently
checks that normalization and the supported type-only parameter grammar.

Roots are an ordered, nonempty, duplicate-free list of at most 1,024 types.
They form an evidence catalog; v3 entries bind their argument/result root
indices to the native checked function signatures. Root order affects the whole-graph digest. Definition IDs are distinct
integers 0–255; table order and original IDs do not affect canonical digests.
There are at most 256 definitions, 1,024 constructors globally, 64 ordered logical
fields per constructor, 64 closed arguments and 32 universes per definition.
Universe values are integers 0–255. Logical constructor counts do not inherit
the allocated Node tag ceiling: a 245-constructor enum is valid model data.
Physical allocated-tag checks belong to the later representation verifier.

Names are `["anonymous"]`, `["str",parent,text]` or
`["num",parent,canonicalUnsignedDecimalString]`, with UInt64 numeric leaves.
Origin/module/type/constructor Names must be nonanonymous; field binder Names
may be anonymous or duplicated. Name depth is less than 64, each leaf is at
most 1,024 UTF-16 units, and aggregate name text is at most 65,536 units.
Unpaired surrogates, noncanonical numerals and numeric overflow are rejected.
Origin hashes are lowercase 64-digit SHA-256 hex; model syntax does not
authenticate that provenance.

All references resolve and all definitions are reachable. Duplicate closed
applications are rejected even if local IDs differ. Constructor Names are
unique within a closed definition; order defines the logical constructor index.
Inline type depth is less than 32, at most 8,192 descriptor visits and 4,096
edges (builtin child edges plus nominal references) are allowed, and canonical
UTF-8 JSON is at most 1 MiB. Constructor/field/argument vectors preserve order.
Arithmetic is bounded before allocation.

Only constructor-field self references, including through builtin containers,
form supported recursion. Removing these self edges must leave an acyclic
nominal dependency graph; arguments may not refer back to their definition.
Reaching a different instance of the same declaration is allowed only when
already present in the closed argument dependency closure (ordinary nested
`Box (Box Nat)`); changing recursive applications otherwise fails. These are
model checks, not a substitute for the native telescope classifier's semantic
nonuniform-recursion rejection. Graph traversal, dependency ordering and
application hashing use worklists rather than composed nominal/inline recursion.

Canonicalization visits roots in order, assigning IDs on first nominal visit;
it visits definition arguments before constructors and their ordered fields.
It emits definitions in that order with all IDs rewritten. Map keys sort
lexicographically; JSON is compact data.json UTF-8 without optional Unicode or
slash escaping and without a trailing newline. The schema string separates
this domain. `logical-digest` is SHA-256 of the whole canonical document.
`type-digest` instead canonicalizes only one declared closed nominal/root and
its reachable closure with a singleton root: it is independent of unrelated
selected entries, roots, discovery IDs and table order. The latter is the
logical-schema component of type identity. Neither digest authenticates itself.

Physical evidence is validated separately by the native observation normalizer.
The earlier shape-only reference model remains an independent structural check,
not the executable v3 storage program. Its exact shape is:

```clojure
{"schema" "lean-jvm-layout-references/3"
 "logicalDigest" whole-canonical-logical-sha256
 "representationDigest" independently-authenticated-physical-document-sha256
 "definitions"
 [{"definition" canonical-definition-id
   "applicationPath" ["applications" application-index]
   "constructors"
   [{"constructor" logical-constructor-index
     "layoutPath" ["families" family-index "constructors" native-constructor-index]
     "fields"
     [{"field" logical-field-index
       "layoutPath" ["families" family-index "constructors" native-constructor-index
                     "fields" native-field-index]}]}]}]}
```

References cover every canonical definition/constructor/logical field exactly;
constructor and field rows are ordered by logical index. Application/family
indices are 0–255, native constructor index is within that logical family's
constructor count, and native field index is 0–63. Field paths share their
constructor prefix and are distinct within it. No path language, offsets,
storage bytes, reflection members or allocation instructions are accepted.
`validate-layout-references!` validates only this shape and the logical digest
link. It intentionally does not authenticate the representation digest or
assert that a path exists or corresponds to the claimed logical field. Actual
persisted declaration layouts and instantiated/trivial type representation
must be independently validated in the native-evidence phase before these
references authorize any reads, writes or allocation.

The isolated [NativeTypeGraph module](../../tools/lean-producer/src/NativeTypeGraph.lean)
now defines `discover (roots : Array Expr) (products : Name → Option String) :
MetaM Discovery`, returning `logical : Json` and separate `layouts : Json`.
It is imported by the v3 producer, separately from the unchanged v2 producer.
Only the registered source/binary/closure/receipt cohort and source/artifact
issuers grant entry authority; source implementation alone does not. Its [probe](../../tools/lean-producer/test/NativeTypeGraphProbe.lean)
uses explicit dummy product claims only to test lookup custody; those hashes
are never authenticated product evidence.

Discovery checks actual closed native types, normalizes aliases under default
Meta transparency, reconstructs canonical closed applications with native DefEq,
and registers provisional Expr keys before walking constructor fields through a
bounded work queue. Constructor parameters are instantiated from actual closed
arguments; every remaining logical domain must be closed and independent of
previous field binders, including before reduction. Actual constructor result
type/family/index/field count are checked. The native parameter classifier admits
type-valued parameters only. Closed universe arguments use actual
`Level.normalize.toNat`, with input work/depth and output numeral bounds.
Native expression normalization/checking has separate bounded input scans;
repeated inference work is charged conservatively and may exhaust before the
emitted graph's structural maximum.

Native `InductiveVal.all` records the user mutual block; `numNested` separately
counts compiler-generated nested auxiliaries (`numTypeFormers = all.length +
numNested` in the pinned source). Requiring `all == [name]` rejects user mutual
families while admitting AST recursion under List/Array. Native elaboration's
fixed-parameter checks and the graph's regularity/finite-closure checks remain
independent safeguards against changing recursive applications. Unknown compiler
runtime builtins are excluded using the pinned LCNF runtime-type registry in
addition to explicit special/resource head checks.

Origin module Names come from native `Environment.getModuleIdxFor?` and the
imported module table, or native `mainModule` for local declarations. The supplied
lookup must contain a canonical product digest for every encountered nominal
defining module; absence fails. This does not establish product authenticity or
permit using a source path/module Name alone as identity.

The separate observation document has schema
`lean-jvm-native-layout-observations/3`, scope `observed-not-admitted`, an
`applications` array of discovery-definition IDs and actual closed application
IR types, and a `families` array of persisted generic declaration layouts:
typeName/IR type/trivial-structure information plus each original constructor's
CtorInfo and CtorFieldInfo. Declaration `getCtorLayout` is not recomputed as a
specialization of each closed generic instance. Closed application observation
uses actual toLCNFType → toMonoType → toImpureType, including trivial erasure.
These are observations, not the authenticated physical document or checked
layout-reference plan described above. Future evidence integration must bind
digests, rewrite discovery IDs to canonical IDs, establish exact logical/native
field correspondence and independently verify the representation profile.

## Frozen storage and custody

Current `Interpreter.Node` is static, but exposes mutable tag/RC and mutable
arrays. Positive-RC destruction clears fields. Existing `markPersistent`
preflight accepts Ref/closures and stops at rc0; it is **not** a typed immutable
certificate. Sharing/MT alone still leaves positive-RC writes. Array/ByteArray
logical extents are mutable metadata. Pointer stamping introduces owner metadata.

Use the existing persistent/nonexclusive behavior as the storage foundation,
with a restricted transitive pure-data certificate. Encapsulate Node payloads
and supply narrow trusted internal readers; the enclosing Interpreter may still
access its nested class's private fields. Avoid a second heap, public borrowed
leases, permanent positive host RC credits, cleaners, or a full interpreter
rewrite as prerequisites.

The export protocol is mandatory:

1. Keep the actual result root owned in the existing Project slot/lease. With an
   explicit stack, validate the complete typed graph, live extents, scalar/UTF
   invariants, metadata and layout. Distinguish DAG aliases from active-path
   cycles. Visit preexisting rc0 subgraphs unless a compatible transitive frozen
   certificate already proves them. Admit only pure ordinary data, approved
   boxes/arrays/bytes and immutable leaves. Validate physical custody as well as
   visible fields: array object slots outside the live prefix must be null,
   otherwise an invisible closure/resource could remain retained. Inspect the
   full storage even under preexisting rc0. Scalar spare capacity/padding is
   nonsemantic, while live extents and reserved field domains are explicit.
2. Preallocate detached descriptors, wrappers, frozen extent state, bookkeeping
   and commit list. Complete cancellation, budget and failure-prone validation
   before any storage transition. Audit every data/tag/metadata/dead/extent write,
   including intrinsic, fork/import and release shortcuts. No concurrent guest
   execution may observe the transition.
3. Commit monotonically to persistent/nonexclusive certified storage and immutable
   logical extents. The commit cannot allocate, throw, cancel, or call user/guest
   code. Prevent all later payload/metadata mutation, including pointer stamping;
   pointer-sensitive operations remain excluded or require a separately reviewed
   policy. `pointerWord` must guard frozen values before allocating/stamping a
   pointer token. ForkCopy must share certified Nodes or clear/reissue certificates;
   it must not copy a root-bound certificate onto new Nodes. Certify all reachable
   nodes, not merely the root.
4. Publish with explicit release/acquire certificate publication (for example,
   a volatile publication read/write). Preallocated wrappers' final fields do
   not publish Node writes performed after wrapper construction. Shared caches/views
   cannot lazily mutate backing Nodes. Concurrent independent Projects may read
   certified values without RC/metadata writes; engines retain their normal
   confinement policy. Subsequent Lean updates copy rather than reuse storage.
5. Finish the existing exactly-once result-release journal and clear slots/Header.
   A frozen pure root's release is a no-op. For IO success, freeze the payload
   and release its ordinary envelope; do not freeze IO resources/errors into
   public data. Precommit failure follows normal owned-root cleanup; no failure
   exposes a partial public value. Preserve current cancellation/error precedence,
   exact unexpected host Error identity, and terminal/abandonment policy.

JVM GC reclaims persistent storage once all host/engine references disappear;
rc0 does not require a native immortal arena. Freezing changes allocation reuse
and `isShared` observations; logical supported observations remain equivalent.
Do not extend this guarantee to arbitrary unsafe pointer/profiling behavior.

Compatible certified imports reuse their immediate/leaf/Node payload after
root identity/layout/class and ABI checks. INC/DEC are no-ops for frozen nodes.
Add an explicit trusted certified-root/child path; never relax DataRef's ordinary
fresh exactly-one-owner rule to accept arbitrary Nodes. Mixed fresh parents and
certified children retain normal ownership only for fresh nodes. Trivial wrappers
and primitive lanes may need shallow view/boxing adaptation, never a deep copy.

First export costs O(unique nodes + edges + payload validation), with O(nodes)
temporary bookkeeping. Reusing a certificate avoids rescanning the graph;
precomputed immutable statistics enforce compatible limits. Access allocates
views/boxes as needed; hash, equality and materialization still traverse.
Large spare capacity may remain retained with shared storage; measure/document
that and offer explicit compact/materialize copying when useful. Cross-layout
conversion is initially refused, not silently copied.

## Implementation phases and admission gate

1. **Contract/model:** settle exact schema version, canonical identity/graph,
   limits, diagnostics, public accessors and collection semantics. Pin old-cohort
   negatives. No public nominal admission.
2. **Evidence:** implement producer discovery, generic verifier, authenticated
   helper source/binary cohort and immutable publication/bundle receipts. Carry
   graph/origin/layout identities through source requests, compilation receipts,
   cache keys, retained startup evidence and artifact validation/export.
3. **Storage and record slice:** private typed freeze/certificate and mutation
   audit, encapsulation, Java/Clojure views, certified input reuse and ordinary
   scalar-only/mixed construction. Demonstrate enums and empty/trivial/scalar
   records end to end without payload copying. This is an early performance gate.
4. **Recursive closure:** ordinary recursive types, finite closed generic
   instances and all supported builtin/nominal nesting; DAG/cycle budgets,
   immutable bytes, IO payload custody and explicit materialization.
5. **Acceptance/publication:** independent applications, native oracle,
   cold-source/cache/edit/reload/artifact and isolated Java/Clojure consumers.
   Admit the new cohort publicly only after all gates pass. Then resume FFI.

Required acceptance evidence:

- Native construction → JVM field observation and host construction → independently
  compiled Lean observation for every lane/constructor, erased/singleton/empty
  forms, generic boxes, recursion and nested containers. Symmetric codec round
  trips alone are insufficient. Check scalar extremes, Unicode, raw float bits,
  USize width, empty bytes and Option Unit.
- A separately authored multi-module application AST/transformation plus a record
  and enum workload, including imported type origins. Distinct same-layout types,
  same Name/different origin, changed arguments/constructors and stale/cohort
  mismatches fail. Unsupported dependent/proof/resource forms fail at discovery.
- Independent tampering of helper pins, logical graphs/fields/origins, layout/ABI,
  scalar overlap/overflow/tags, artifact hashes and graph digest is rejected.
  Unknown schemas and malformed/extra map keys fail before execution.
- Mutable host input cannot affect constructed values/calls. Shared diamonds do
  not expand or copy; cycles and bounded deep chains fail cleanly. Values survive
  release/close/failure, remain unchanged after Lean updates, and work in a fresh
  compatible Project. Two Projects can concurrently reuse them. Retention/source
  audits plus bounded weak-reference probes exclude engine/Program/Header leaks.
- Inject planning/freeze/materialization/cancellation/output failures; prove
  precommit atomicity, safe publication, exactly-once cleanup and healthy reuse
  after host refusal. Map lookup/destructuring/seq/equality/hash/assoc/dissoc and
  explicit materialization match their documented semantics.
- Measure first export, repeated reuse, selective access, updates and full
  materialization for trees, DAGs and bytes: visited nodes/edges, payload copies,
  wrapper allocations, retained capacity and RC traffic. First export must avoid
  payload duplication; repeated compatible crossings must avoid graph rescans.
- Cold native source, cache hit, edit/reload and native-free artifact reopen carry
  identical authenticated schema identities. Isolated application-JAR Java and
  Clojure consumers need no source tree, compiler namespace, Lean or runtime javac.
  Preserve existing general/scalar/monad/persistent-map/stdio/filesystem consumers
  and unchanged attributed fp-lean sort/Feline tutorial targets.

Research only: a private trusted-hook 1,000-node List Nat probe reused the same
Nodes in a peer after original Project close, preserved the original through an
update, and survived runtime close. It supports feasibility of persistent JVM
storage. The current public decoder still copies; that fixture does not prove
general typed certificates, native nominal discovery, public API safety,
concurrent publication, or production performance. It is not a release receipt.

### Used-origin product model (private foundation)

`ansatz.lean.jvm.used-products` validates the pathless
`lean-jvm-used-module-products/1` manifest. Each of at most 256 defining modules
has its primary `.olean` SHA-256 plus the exact ordered present/absent records for
`.olean`, `.olean.server`, `.olean.private`, `.ir.sig`, and `.ir`. The primary
record is mandatory and must match the nominal product identity. Existing
installed-product byte ceilings apply; canonical manifest encoding is bounded at
4 MiB and independent of module enumeration order.

The complete native advisory origin inventory must equal the captured module
set. Origins require a local compiled module, an explicitly authorized installed
module, or implicit Init; inventory discovery does not authorize new imports.
Local/installed overlap and attempts to shadow Init are rejected. Every logical
definition must match its defining module's primary product, and unused product
records are rejected when binding the graph. An empty manifest supports a graph
containing only builtin types.

These pure checks establish internal correspondence, not byte custody. Source
loading must still capture and recheck actual products before and after native
evidence collection, bind the module-cache compilation baseline, and retain the
issued provenance for artifact reopening. A caller-created manifest or advisory
inventory cannot issue a public datatype descriptor or admit a v3 entry.

### Observation normalization and product custody

`representation/normalize-observation!` validates native logical/lowering links
before emitting a canonical typed-storage program. It bounds work, UTF-16,
integers and encoded bytes. Root subsets select complete closures. Version 2
observations and v3 entries carry closed builtin/special-runtime witnesses for
full ASTs and mixed records; IO additionally requires the actual selected-entry,
envelope and erased-world bindings. Missing witnesses fail rather than being
inferred from an object's apparent shape.

`compiler.products/capture!` derives product paths from a verified cache manifest
under an issued compiler. It checks compiler identity, exact native package-root
resolution, every present role and optional absence, and the immutable parsed
baseline. Caller paths or descriptive maps cannot replace the issued token.

Legacy captures report `:requires-v3-rebuild true`: old caches cannot acquire
compilation-time evidence retrospectively. The `/3` profile snapshots selected
used Init products and all declared installed products before compilation, binds
those records into cache inputs, and rechecks them through final receipt issuance.
A newly required origin needs a new compilation baseline. This supplements the
existing trusted immutable installed-toolchain policy; it is not cryptographic
attestation of every transitive implementation dependency. Pure normalization
and caller-created maps still issue no public authority.
