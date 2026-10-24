# Strict WF role preparation

`ansatz.wf-supplement/prepare-strict-role` takes a captured session, `:lex` or
`:sizeof`, and explicit finite limits. It returns a complete, unactivated
ProofContext. It does not install that context or change the shipped legacy WF
entry points. A caller must not infer frontend WF success from preparation alone.

The checked-in schema-1 bundle remains on its existing legacy path. The strict
entry requires an actual verified schema-2 snapshot with companion provenance;
a sentinel or descriptive artifact profile cannot establish that authority.
Existing base trust is retained: exact overlap does not kernel-check the base.

## Preparation contract

1. Capture one verified bundle snapshot, check captured base cohort constraints,
   and require the selected role's actual generation roots and sentinel in its
   decoded declarations. Export JSON remains trusted producer infrastructure.
   Explicit inflated-byte, line, record, index and Level-construction work gates
   precede raw assembly; the shared materializer bounds the complete CI batch.
2. Preserve original inductive records. Ordinary packages must contain their
   exact mutual heads, constructor tables and primary recursors. The primary
   name rule is `head.rec`, derived from pinned Lean v4.33.1,
   `src/kernel/inductive.cpp` (`mk_rec_name` and `declare_recursors`), commit
   `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`. Nested packages are refused by
   strict v1. Quotient declarations must form the complete canonical package.
3. Check standalone kernel dependencies and selected companion references
   against actual exported Name objects. Companion profile 1 uses dotted name
   text; declaration components requiring Lean escapes are refused instead of
   joining ambiguous text aliases. Numeric Name components retain their numeric
   identity through the existing parser. Binder and universe names are unaffected.
4. Partition the captured base using direct local lookup and a single bounded
   captured-root evidence call for nonlocals. The call proves absent names
   without a full PSS scan or normal cache hydration. Local shadows, hidden names,
   unsupported external views and backend failures do not establish absence.
   Compare every overlap in one bounded exact full-CI batch, including bodies,
   reducibility hints and variant-specific fields.
5. Refuse a package containing both present and missing members. Seed a fresh
   uncached replay view with only exact-matched present role CIs, requiring that
   retained subset to be standalone. Replay whole missing packages through the
   existing strict kernel protocol. Out-of-role lookups are unavailable.
   Quotient state is enabled only by a complete matched or newly checked role
   package; unrelated original flags are not inherited into replay.
6. Transplant only newly checked missing CIs onto the original Env. Existing
   entries, body policy and captured external/index views remain attached to that
   Env. Keep `addConstant`'s duplicate guard: it performs exactly one additional
   ordinary name-tree point lookup per missing declaration, bounded by candidate
   `:declarations`. The captured stable handler uses the same raw shell tree;
   an absent shell returns before any Expr/name/level resolver reads. This is
   explicit duplicate absence work, not an unbounded general body lookup or scan.
   The external-handler cache isolation prerequisite prevents another handler's
   cached CI from crossing into this view. Prepare the bounded companion overlay
   with the existing pure session helper. Record descriptive role history only after admission and overlay.
7. Close parser resources before returning. Parse, evidence, closure, replay,
   overlay and close failures return no prepared result and make no session-slot
   writes. A close failure is suppressed on the original error when one exists.
   The borrowed captured store is neither reopened nor closed by preparation.

Limits cover entire stage batches rather than resetting for individual CI pairs,
requested names or dependency roots. Separate explicit limit maps cover input,
candidate materialization, captured store evidence, exact comparison and metadata
preparation. They do not bound all allocation within the existing JSON/PSS/CBOR
infrastructure or kernel checking; this API is not an untrusted-decoder boundary.

## Activation boundary

Conditional session activation is separate and is not implemented by this API.
The campaign uses the existing cooperative session lock; this is not isolation
from unlocked writers or atomic visibility across every global atom. A later
installer must reject captured-slot/cache drift before publication, perform one
Env CAS without retry, and report actual best-effort restoration after failures.
Atom watches can throw after changing an atom, so an installation exception alone
cannot establish that the old state remained installed.

Focused tests use valid toy declarations for strict admission behavior and the
actual legacy lex package tables for closure checks. These do not claim a new
schema-2 production cohort, full Mathlib validation, or frontend WF success.
