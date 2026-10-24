# Diagnostic role CI and CSimp comparison

`ansatz.bundle-semantic-policy/compare-role-bounded` takes four explicit inputs:
a standard vector of role CIs, an ordered vector of CSimp rows, a vector of
independent axiom templates, and finite input/comparison limit maps. It performs
bounded data comparison and syntactic field checks. It does not kernel-check the
supplied CIs, authenticate templates, issue receipts or activate any metadata.

Rows have exactly `:source`, `:target`, `:witness` as actual Name objects and
`:global-ordinal` as an increasing nonnegative primitive integer. Repeated sources
and registrations remain in order. The function checks ordinal ordering; it does
not establish correspondence to a native global corpus. Existing native Name
and planner adapters remain the future integration points; there is no dotted
text fallback or new serialized companion profile.

The syntactic rule is pinned Lean commit
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`:

- `src/Lean/Util/Recognizers.lean:33-45`: `eq?` recognizes exactly three arguments
  applied to `Eq`, without normalization.
- `src/Lean/Compiler/CSimpAttr.lean:18-49`: both endpoints must be constants with
  identical ordered universe arguments, all distinct `Level.param` values.
  The function does not add a requirement that this vector equals the witness's
  whole universe-parameter vector; unused witness parameters are allowed.
- `src/Lean/Declaration.lean:453-465`: definition safety distinguishes unsafe and
  partial, theorems have no unsafe flag, and opaque declarations carry one.

The diagnostic witness policy is stricter than native registration: require a
body-bearing theorem, safe definition, or safe opaque declaration. Reject both
unsafe and partial definitions, unsafe opaque declarations, axiom witnesses and
missing bodies. This checks fields/body presence, not proof-body typing or its
allowed assumptions.

Every observed role axiom needs an exact complete-CI match against its explicitly
supplied template, including Name, tag, safety, ordered universe parameters and
full type. Unused template entries may describe other roles. Template provenance
and independence are the caller's responsibility and remain unestablished by this
function. There is no stock type guessed from an axiom name or expected count.
An explicitly templated runtime/compiler-marker axiom can occur in an image;
that does not permit it as an assumption of a safe proof. Full witness dependency
and assumption discharge is a separate pending gate.

Input limits are `:declarations`, `:templates`, `:registrations`, `:name-components`,
`:name-bytes`, `:name-depth` (at most 256), and `:level-slots`, under `:inputs`.
`:comparison` supplies all existing full-CI comparator limits. Count gates precede
input walks. Iterative tagged-segment Name keys use only scalar equality/hash,
never recursive AST equality or Name text conversion. A single comparison batch
shares completeness/identity-pair budgets across all CIs, templates and axiom
pairs. Unknown collections, metadata payloads, cycles and exhausted bounds fail
closed. Materialized inputs and mutable CI fields/arrays must remain quiescent.

Results contain detached counts and row-order diagnostics with `:authority :none`.
`:native-binding` and `:proof-assumptions` are `:pending`; `:implemented-by` is
`:pending-lossless-native-eqv-bridge`. Binder-sensitive full-CI equality here does
not implement native `Expr.eqv` for implemented_by. The missing native oracle must
bind exact candidate CIs to independently captured types, including any required
lossless representation/projection bridge. Caller flags, hashes, a sentinel or a
diagnostic result cannot authorize producer-2 serialization or promotion.

Tests use deliberately synthetic CI shapes, not kernel-admitted or native proof
receipts. Existing producer, planner, activation paths and shipped resources are
unchanged by this helper.
