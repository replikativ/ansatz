# Hole Elaboration And Meta Search

This branch is moving Ansatz toward Lean's hole model without making the
trusted kernel understand holes.

Lean's split is:

- the kernel checks closed CIC expressions;
- `MetavarContext` stores expression mvar declarations, expression
  assignments, level assignments, and delayed assignments;
- elaboration and tactics manipulate `MVarId`s in that metacontext;
- before kernel checking, terms are `instantiateMVars`/zonked so unresolved
  holes cannot cross the kernel boundary.

The local Ansatz shape now follows that split:

- `ansatz.meta/empty-context` is a persistent metacontext value;
- the metacontext now exposes Lean-style assignability/depth predicates,
  assigned/assignable scans, declaration instantiation, and conservative
  dependency checks over unassigned mvar local contexts;
- `ansatz.meta/infer-type` accepts real expression mvars and infers their
  types from the metacontext, matching Lean's Meta-layer `inferType` shape
  inference rather than kernel validation;
- expression and universe mvars have checked assignment helpers that enforce
  freshness, depth, occurs checks, and local-context safety; expression
  assignment can also type-check closed values against the mvar declaration;
- proof states carry `:meta-mctx` beside the legacy `:mctx`;
- tactic continuation goals declare real `Expr.mvar` ids in `:meta-mctx` and
  default to Lean-style `syntheticOpaque`, so ordinary unification cannot
  silently close the current goal;
- apply-style theorem argument holes remain assignable metavariables: regular
  forall-telescope arguments are `natural`, while instance-implicit arguments
  are `synthetic`, matching Lean's `forallMetaTelescopeReducing` rule;
- surface elaboration now uses real `Expr.mvar` nodes for expression holes and
  real `Level.mvar` nodes for universe holes;
- surface expression mvar declarations live in `:meta-mctx`; surface `:mctx`
  now keeps compatibility metadata/solutions instead of duplicated types;
- surface type inference and WHNF for terms containing holes now route through
  `:meta-mctx` and `ansatz.meta`;
- surface universe-level unification now routes through the persistent
  metacontext level unifier and syncs assignments back to the compatibility
  level context;
- surface expression unification now routes through `ansatz.meta/is-def-eq`
  and syncs expression/level assignments back to compatibility contexts;
- the metacontext unifier handles direct assignments, Miller-pattern
  assignments under binders, universe assignments, closed kernel delegation,
  and Lean-style synthetic-vs-natural assignment preference;
- the tactic fvar-backed unifier API now bridges into the Lean-shaped
  metacontext unifier as the single implementation path and syncs successful
  assignments back;
- tactic assignments still keep legacy extraction recipes, but also mirror a
  Lean-style expression assignment when possible;
- tactic proof states now keep declarations in `:meta-mctx` and extraction
  recipes in `:recipes`; `:mctx` is a compatibility view for older tactic
  plumbing;
- tactic `refine` now elaborates a surface term in the current proof
  metacontext, saves the fresh mvar boundary, assigns the current goal, and
  turns the freshly-created non-natural holes into goals; `refine-prime`
  mirrors Lean's `refine'` by allowing natural holes to become goals too, and
  both are exposed through the public surface tactic forms `(refine ...)` and
  `(refine' ...)`;
- `ansatz.tactic.elab-term/elab-term-with-holes` is now the shared
  tactic-level helper for Lean-style hole collection, diagnostics, metacontext
  installation, and goal tagging; it supports both goal-expected elaboration
  and Lean's explicit no-expected-type mode used by tactics such as
  `specialize`;
- collecting elaboration now mirrors Lean's `collectFreshMVars` boundary more
  closely by exposing only fresh unassigned holes reachable from the zonked
  elaborated value, so unused scratch metavariables are not promoted to goals;
- `refine`/`refine-prime` tag anonymous collected goals using Lean's
  `tagUntaggedGoals` convention: one anonymous child inherits the parent tag,
  while multiple anonymous children receive stable `refine_i`/`refine'_i`
  suffix tags;
- `refine-prime` elaborates with a Lean-style `holesAsSyntheticOpaque` mode,
  so explicit `_` holes become synthetic-opaque tactic goals rather than
  ordinary natural metavariables;
- `refine-prime` collection also mirrors Lean's scoped
  `withAssignableSyntheticOpaque`: during elaboration only, synthetic-opaque
  placeholders may be assigned by unification when later arguments determine
  them; the returned metacontext strips that temporary permission;
- default `refine` rejection for natural holes now reports typed diagnostics
  in `ex-data`, giving REPL/search tooling the unfilled-hole ids, display
  names, kinds, and types;
- named synthetic holes reuse an existing metacontext user-name entry when one
  is available, matching Lean's synthetic-hole lookup behavior;
- `refine` mirrors Lean's main-goal guard: refining with the main goal keeps it
  open, while values that merely depend on the main goal metavariable are
  rejected;
- `refine` assigns the instantiated elaborated value when no child goals remain,
  while preserving delayed-abstraction metadata when child goals are still open;
- public `exact` now uses the same tactic-level elaboration helper in strict
  mode: it elaborates against the current target and rejects fresh unassigned
  natural or synthetic holes instead of promoting them to goals;
- inline public `have h : T proof` closes the generated proof subgoal through
  the same strict `exact` path, so holes in the proof are rejected instead of
  bypassing the tactic metacontext;
- `clear` now checks Lean-style local-context and target dependencies before
  removing a hypothesis;
- `specialize` mirrors Lean's `ElabTerm.lean` shape: it elaborates a local
  hypothesis application without an expected type, lets argument holes become
  goals, asserts the specialized result, tries to clear the original
  hypothesis, and orders generated holes before the body goal;
- target-only `change` now uses the same collection helper to elaborate a
  replacement target, solve placeholders by defeq against the current target,
  and create a def-eq child goal plus any remaining synthetic holes;
- `show` builds on the same target-elaboration path but searches the open-goal
  list like Lean: the first goal whose target is definitionally equal to the
  pattern is changed and moved to the front, with earlier goals kept after it;
- `extract` now defaults to zonking `(mvar root)` through `:meta-mctx` and
  refuses to return if mvars remain; `extract-legacy` is kept for parity checks.

The important hardening point is delayed abstraction under binders. A child
goal introduced under `intro`, `have`, `cases`, or branch binders may be solved
with local free variables from its declaration context. Direct substitution
would leak those fvars into a lambda. The meta layer therefore supports delayed
abstraction markers that abstract the relevant fvars after child mvars have
been zonked, which is the local version of Lean's delayed assignment discipline.

## Current Boundary

This is not yet a full replacement for the legacy proof-state compatibility
map or the surface elaborator.

- `extract` uses the metacontext path for modern proof states.
- `extract-legacy` remains as a migration/debugging path while tactic writers
  still construct legacy recipes.
- Surface elaboration uses real expression and universe mvars internally, but
  `:mctx`/`:level-mctx` remain compatibility views.
- The kernel still rejects raw mvars by construction: callers must zonk first.

That is deliberate. It lets us migrate tactic families and elaborator code
against one explicit invariant: no unresolved expression or level mvars are
allowed at kernel-check time.

## Relational Search Direction

The metacontext is a good search state because it is persistent and forkable.
A relational elaborator or Barliman-style proof search can treat a state as:

- an environment and local context;
- a goal queue of `MVarId`s;
- a metacontext with partial expression and level assignments;
- constraints generated by elaboration, tactics, unification, typeclass search,
  rewriting, or domain-specific solvers;
- a trace and cost model.

The search operator does not have to be a Prolog black box. It can be an
interleaving scheduler over small deterministic steps:

- elaborate one syntax node;
- WHNF only when demanded by a constraint;
- run one tactic expansion on a selected goal;
- ask unification to solve one metavariable;
- ask an e-graph/datalog index for candidate rewrites;
- synthesize one typeclass instance;
- call an LLM or learned policy to rank branches.

Because states are immutable values, branch forking can be cheap. The same
representation can support DFS, fair interleaving, beam search, SMC/importance
sampling, or cost-based planning. The critical correctness rule remains Lean's:
search may propose assignments, but the final zonked proof term is accepted
only if the kernel checks it.

## Next Fidelity Targets

1. Remove the remaining surface compatibility maps where callers can read
   directly from `:meta-mctx`.
2. Extend the tactic-level `refine` path toward fuller Lean
   `elabTermWithHoles` parity: better diagnostics for natural holes,
   term-elaboration variants for `apply`, and handling let-rec/style auxiliary
   holes.
3. Extend the mvar-aware unifier beyond the current common tactic paths. The meta
   unifier now handles direct expression assignments, Miller-pattern
   assignment, universe assignments, closed kernel delegation, and structural
   recursion; remaining Lean gaps include richer proof/instance heuristics,
   delayed assignment integration in unification, and stronger stuck/cheap
   defeq modes.
4. Continue parity tests for larger tactic families and proof extraction
   recipes as more assignment recipes are replaced by direct metacontext proof
   terms.
5. Collapse the remaining compatibility views once the surface compatibility
   maps and tactic assignment recipes are replaced by direct metacontext proof
   terms.
