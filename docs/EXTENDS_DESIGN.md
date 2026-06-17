# Structure inheritance (`extends`) — Lean-4-faithful design

Grounded in a detailed read of `../lean4/src/Lean/Elab/Structure.lean` (Lean 4, `Lean.Elab.Command.Structure`).
The goal: follow Lean's actual model for our core, so the hierarchy we build (`WAddMonoid ⊂ WSemiring …`)
matches Lean's representation and the path to multiple inheritance is the same one Lean walks.

## What Lean 4 actually does (not "packed vs flattened" — a per-field hybrid)

Lean classifies **every** field of a structure into one of five kinds (`StructFieldKind`,
Structure.lean:108-135). This is the crux and it is finer than the binary we discussed:

| kind | in constructor? | own projection? | meaning |
|---|---|---|---|
| `newField` | yes | yes | a genuinely new field declared here |
| `subobject structName` | **yes** | **yes** (`toParent`) | a parent embedded **whole** as one field (the PACKED parent) |
| `fromSubobject` | no | **no** | a field that lives *inside* a `subobject`; accessed by projecting the subobject |
| `copiedField` | yes | yes | a parent field re-materialized as a NEW field of the child (the FLATTENED parent field) |
| `otherParent structName` | no | only if direct | a parent projection reconstructed from copied fields (no embedded subobject) |

The parent-projection name is `to` ++ parentName (`mkToParentName`, Structure.lean:852) — i.e.
`WSemiring.toWAddMonoid`. Exactly our chosen name.

### The decision rule (Structure.lean:805-826)

For each parent, in `extends` order:
- If we're **already inside a subobject**, this parent can't be its own subobject → `otherParent`.
- Else if the parent has **no fields**, or **any of its fields overlaps** a field already present
  (the diamond!) → represent it as `otherParent` and **copy/reuse** the individual fields
  (`copiedField` / `fromSubobject`) instead of embedding.
- **Else embed it as a `subobject`** — a single packed `toParent` field.

So **the first parent of a fresh structure becomes a packed `subobject`**; additional parents that
would overlap get **flattened** (their non-shared fields copied, shared fields reused once). Lean
mixes packing and flattening *per parent*, driven by overlap.

### Diamonds → C3 linearization (Python's MRO)

When parents overlap, Lean computes a **C3 linearization** of the ancestor DAG
(`computeStructureResolutionOrder` / `mergeStructureResolutionOrders`, Structure.lean:1500-1518) —
the *same* algorithm Python uses for method-resolution order. `structureDiamondWarning` and
`structure.strictResolutionOrder` (Structure.lean:21-29) gate warnings when C3 can't find a strict
order. The resolution order decides which parent "owns" each shared field so there is **one** copy,
keeping all `toParent` paths defeq-coherent (the property Mathlib depends on).

### Field access through a subobject

A `fromSubobject` field gets **no projection constant** of its own. `s.add` on a `WSemiring`
resolves at *elaboration* by finding `add` in the ancestor `WAddMonoid` and inserting the subobject
projection: `WAddMonoid.add s.toWAddMonoid`. Lean stores **no** `WSemiring.add` constant — access is
"flattened" only at the dot-notation layer, not in the environment.

## Our adaptation (Lean-faithful core, single-inheritance first)

We implement Lean's **subobject** case exactly, and leave the `copiedField`/`otherParent`/C3 path as
a mapped-out extension that does not change the surface syntax:

1. **Surface.** `(a/structure WSemiring [S Type] :extends (WAddMonoid S) (mul …) (mul_add …) …)`.
   Multiple parents allowed in syntax from day one; >1 overlapping parent is a *not-yet-implemented*
   error (we compute overlap and say so) rather than silent miscompile.

2. **Representation = `subobject`.** Prepend one real constructor field `toWAddMonoid : WAddMonoid S`
   before the declared fields. `WSemiring.mk` takes the **parent instance** then the new fields
   (compositional instances — DRY, matches Lean's subobject ctor).

3. **`toParent` projection = free.** The existing projection loop already emits the field-0
   projection; named `toWAddMonoid` it *is* Lean's parent projection.

4. **Inherited access.** Lean resolves `s.add` at elaboration with no stored constant. We have no
   subobject-aware dot-notation yet, so we make a **documented, deliberate deviation**: generate
   convenience accessor defs `WSemiring.add := λ {S} (s : WSemiring S) => WAddMonoid.add (WSemiring.toWAddMonoid s)`
   for each ancestor field (introspected from the parent constructor's telescope). These are
   `:abbrev` defs that unfold to the same projection Lean would inline. (Alternative, more faithful:
   teach the elaborator subobject-aware field resolution and emit no defs — a later option.)

5. **Synthesis = already done.** `resolve-basic-instance` (core.clj:255-324) consumes a
   `{Child}.to{Parent}` coercion: a law needing `[_ : WAddMonoid S]` auto-derives it from a
   `WSemiring S` instance via `WSemiring.toWAddMonoid`. No new synthesis code.

### Multiple inheritance — the mapped path (not built yet)

To reach Mathlib-style diamonds later, mirror Lean: keep the first parent a `subobject`; for further
parents, detect field overlap, **copy** non-shared fields as `copiedField`, **reuse** shared fields
per a **C3 linearization** of the ancestor DAG, and synthesize `otherParent` reconstruction
projections. The surface `:extends (A …) (B …)` is unchanged; only the desugaring grows. Until then,
overlapping multiple parents are rejected with a clear message.

## How this relates to Clojure (`../clojure`)

Different axis. Clojure separates behavior from data and dispatches at runtime:

- **Protocols** — a vtable keyed by arg-0's type; open (`extend-type` from outside); **no laws**.
- **Multimethods + `derive`/`isa?`** (`core.clj:5621`/`5683`/`1824`) — an **open, multiple-inheritance
  `:ancestors` DAG** with diamonds resolved *dynamically* by `prefer-method`. This is the runtime
  analogue of Lean's `extends` DAG, but conflict resolution happens at the call site, by hand, instead
  of statically via C3 in the representation.

Two sharp contrasts:
- **Proofs.** A Clojure "Semiring protocol" can declare `add`/`mul`/`zero` but cannot enforce
  associativity. `WSemiring` *cannot be constructed* without `add_assoc` as a kernel-checked field. The
  typeclass is a protocol **+ a verified algebraic contract carried by value**; `toParent` is the
  by-value, statically-checked version of a `derive` edge.
- **When the diamond is resolved.** Clojure: runtime, via `prefer-method` on the global hierarchy.
  Lean/ours: compile/elaboration time, via C3 linearization baked into the field layout. Same problem,
  opposite era.

Open extension (adding an instance for a type from outside, à la `extend-type`) ansatz already supports
independently of `extends` — instances are just defs in the instance-index. `extends` only adds
structural sharing of fields/proofs up the hierarchy; it does not close the instance world.
