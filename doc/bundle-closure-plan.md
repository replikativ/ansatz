# Pure bounded bundle closure requests

`ansatz.bundle-closure-plan/next-round` plans GLOBAL metadata dependencies against
each kernel role separately. It reuses `bundle-metadata/plan-role` and its explicit
planner-only `ansatz-global-companions/2` option. It does not run a producer, parse
raw evidence, authenticate provenance, check declarations or publish a recipe.
The existing `scripts/generate-bundle.py` and shipped bundle paths are unchanged.

Call `(next-round captured nil {} limits)` to obtain all three initial requests.
Subsequent calls use the returned `:state` and exactly the requested roles as
observations. Reuse the identical `captured` and `limits` objects. A terminal
`:closure-planned` state rejects further observations. The private immutable
state is trusted in-process material, not an interchange or authority receipt.
Private construction and identity checks are cooperative API conventions, not a
security boundary: a caller fabricating state gains no authority.

Captured input has these exact fields:

```clojure
{:capture-id "<64 lowercase hex characters>"
 :native-names [{:text "native opaque text" :name [["str" "component"] ["num" "7"]]}]
 :original-roots {:init ["native opaque text"] :lex [...] :sizeof [...]}
 :companions {:attrs [...] :matchers [...] :instances [...]}}
```

Every native descriptor is retained; duplicate text or structured identity fails.
Anonymous declarations, noncanonical numeric components and numbers above the
current Java bridge's signed nonnegative 63-bit range fail. No Name is recovered
from a printed string. Option-like or NUL root text fails early; actual native
syntax equality and existence still require native preflight. Unselected GLOBAL
references must also resolve to descriptors. Matcher discriminant annotations
remain local and do not request declarations.

An observation is `role -> {:capture-id ... :roots [requested-text ...]
:names [actual-exported-text ...] :raw-sha256 ...}`. It must match the issued
ordered effective roots and contain every requested identity. Unknown identities,
duplicated names and a shrinking actual export closure fail. The host must supply
analyses of exact captured raw bytes after closing owned parser resources; hashes
and these supplied maps alone establish no producer or CI authority.

Results separate immutable `:original-roots`, stable appended `:derived-roots`
and `:effective-roots`. Only changed roles request another export. Each request
contains typed descriptors and ordered provenance. Configured roots carry their
original index. Derived roots carry metadata edge kind, source/target, kernel
role, original global corpus row index, selected row index and first round.
CSimp witness and target edges remain distinct. Duplicate registrations retain
their different row addresses while sharing one target request. Per-role
`:selection-provenance` maps selected row positions to original corpus indices;
these indices and the captured vectors identify the exact selected rows.
`:observed-kernel-closure` labels actual exported names beyond the requested roots,
with their raw hash and round. It does not invent a kernel dependency parent.

Limits require positive primitive integers for `:items :scalar-bytes :depth
:rounds :observations :roots :reasons :edges :names`; depth is at most 256.
Only standard immutable vectors/maps and scalar data are accepted. Child slot
counts precede traversal; UTF16 storage bytes precede hashing. Captured input is
charged once; each observation batch adds to the same lineage's usage. Root
budget charges every issued effective request root, including shared roots in
different roles and roots repeated in later requests. Name budget charges actual
observation name counts. Reasons charge newly retained registration addresses.
Edge budget conservatively charges all global reference slots once on capture,
then three complete corpora per observed transition, before invoking the planner.
Rounds include initialization and each observed transition. These conservative
charges bound planning work; they are not exact native resource measurements.

State is reusable and pure: replaying or branching earlier state creates another
lineage. **The host owns aggregate bounds over branches, retries and native
invocations.** No hidden one-shot state, global invocation cap or process budget
is provided here. Input, observation and output data must remain materialized;
there are no launch callbacks, lazy parser views or borrowed native resources.

Every result states `:authority :none` and `:promotion :not-performed`. Native
preflight, captured producer, exact native CI binding, kernel replay, axiom types,
proof assumptions, implemented_by and serialization remain pending. Closure is
only a fact about the supplied GLOBAL metadata and supplied exported name sets.
