# The Ansatz Kernel

This document explains how the Ansatz type-checking kernel works, what it
implements from the Calculus of Inductive Constructions (CIC), and how the
Java code maps to the theory.

**Audience**: Clojure/Java developers who know functional programming but may
not have a background in type theory or proof assistants.

**Cross-references**: The kernel is a faithful reimplementation of the Lean 4
kernel (`src/kernel/` in the [lean4 repository](https://github.com/leanprover/lean4)).
Where the algorithms match exactly, Lean 4 source file and line numbers are cited.
The Lean 4 kernel was authored by Leonardo de Moura; this Java port follows the
same type-theoretic algorithm as described in the Lean 4 source and the
dependent type theory literature.

---

## 1. What is a kernel, and why does it have one?

A **proof assistant kernel** is the small, trusted core that decides whether a
proof term is valid. Everything else — tactics, elaboration, type class search,
pretty-printing — is "untrusted" tooling that helps a user *construct* proof
terms. The kernel only needs to *check* them.

This split matters because tactics can be complex and buggy. If `simp` has a
bug it might produce a wrong proof term, but the kernel will reject it. As long
as the kernel is correct, no tactic bug can sneak an invalid theorem into the
environment. This is the **de Bruijn criterion**: the trusted base stays small.

The Lean 4 kernel is ~3,000 lines of C++. The Ansatz Java kernel is a
comparable size. Both implement exactly two things:

1. **Type inference**: given a term, compute its type.
2. **Definitional equality**: decide whether two terms are "the same" up to
   computation.

Everything else is above the kernel boundary.

---

## 2. CIC in 10 minutes

### 2.1 The expression language

Every term in the kernel is one of these (see `Expr.java`, tags 0–12):

| Tag | Name | Meaning | Example |
|-----|------|---------|---------|
| `BVAR` | Bound variable | De Bruijn index | `#0`, `#1` |
| `SORT` | Universe | `Prop`, `Type 0`, `Type 1`, … | `Sort(u)` |
| `CONST` | Global constant | Named definition with universe args | `Nat.add [u]` |
| `APP` | Application | Function applied to argument | `f a` |
| `LAM` | Lambda | Anonymous function | `fun x : T => body` |
| `FORALL` | Pi type | Dependent function type | `(x : A) → B x` |
| `LET` | Let binding | Local definition | `let x : T := v; body` |
| `LIT_NAT` | Nat literal | Efficient big integers | `42` |
| `LIT_STR` | String literal | UTF-8 string | `"hello"` |
| `MDATA` | Metadata | Transparent annotation | (ignored during checking) |
| `PROJ` | Projection | Structure field access | `p.1` |
| `FVAR` | Free variable | Local hypothesis in context | `h`, `x` |

There are no `MVAR` (metavariable) terms at the kernel level — those are
elaborator concepts. The kernel only sees fully elaborated, closed terms.

### 2.2 De Bruijn indices

Lambda and Pi binders use **de Bruijn indices**: bound variables are
represented as numbers counting "how many binders out" the variable is bound,
rather than names.

```
fun x => fun y => x     becomes     lam _ => lam _ => bvar(1)
fun x => fun y => y     becomes     lam _ => lam _ => bvar(0)
```

The number is the index into the binder stack: `bvar(0)` is the innermost
binder, `bvar(1)` is one level out, etc. This representation makes alpha-
equivalence free — `fun x => x` and `fun y => y` are literally the same term.

**Substitution** replaces `bvar(0)` with a value and decrements all other
indices. **Lifting** shifts indices upward when passing under a binder to avoid
capture. These are the `instantiate` and `lift` operations in `Reducer.java`.

### 2.3 A note on decidability

Type checking in Lean 4 is technically **undecidable** — Abel and Coquand showed
that type checking with proof irrelevance and universe polymorphism can diverge.
The kernel implements a decidable **under-approximation** using the fuel
counter: if the checker runs out of fuel it rejects the term conservatively
(never incorrectly accepts). In practice all known Lean/Mathlib proofs check
well within the 20M-step default.

Unique typing (each term has at most one type up to definitional equality) and
definitional inversion (`Sort ≢ ∀`) are **conjectured** but not yet formally
proven for Lean 4's full type theory. For details see Carneiro's
[Lean4Lean paper](https://arxiv.org/abs/2403.14064).

### 2.5 Universes

Types are stratified into **universes** to avoid Russell's paradox (`Type :
Type` would be inconsistent). The universe hierarchy is:

```
Prop  ⊆  Type 0  ⊆  Type 1  ⊆  Type 2  ⊆  ...
```

`Prop` is the universe of propositions. It is **proof-irrelevant**: any two
proofs of the same proposition are definitionally equal (more on this in
§4.3). `Type 0` (also written `Type`) contains ordinary data types like `Nat`.

Lean 4 uses **universe polymorphism**: definitions can be parameterized by
universe level variables `u`, `v`, etc. The level algebra (`Level.java`) has:

| Constructor | Meaning |
|-------------|---------|
| `ZERO` | The level of `Prop` |
| `SUCC(u)` | One level above `u`; `Type u = Sort(SUCC(u))` |
| `MAX(u, v)` | Maximum of two levels |
| `IMAX(u, v)` | `0` if `v = 0`, else `MAX(u, v)` |
| `PARAM(n)` | Universe parameter named `n` |

`IMAX` exists to handle Pi types correctly. The type of `(x : A) → B x` lives
in `imax(level(A), level(B))`. Formally:

> `imax(u, v) = 0` if `v = 0`, else `max(u, v)`

If `B` is always in `Prop` (level 0), then `imax(u, 0) = 0`, so the Pi type
is also in `Prop` regardless of what universe `A` lives in — this is
**impredicativity of Prop**, which allows propositions to quantify over all
types without universe issues. (Quoted from de Moura et al., "The Lean Theorem
Prover", 2015.)

The level comparison algorithm (`Level.leq`) is in `Level.java` and
`../lean4/src/kernel/level.cpp`.

### 2.6 Typing rules

The kernel enforces these rules (notation: `Γ ⊢ t : T` means "in context Γ,
term `t` has type `T`"):

**Sort**
```
──────────────────────────────
Γ ⊢ Sort(u) : Sort(succ(u))
```
Every universe has a type one level higher. `Prop = Sort(0)`, `Type 0 = Sort(1)`.

**Variable** (free variable in local context)
```
x : A ∈ Γ
──────────
Γ ⊢ x : A
```

**Constant** (global definition, with universe instantiation)
```
c : ∀ {u₁ … uₙ}, T ∈ Env    levels = [l₁ … lₙ]
──────────────────────────────────────────────────
Γ ⊢ c.{l₁ … lₙ} : T[l₁/u₁ … lₙ/uₙ]
```

**Application**
```
Γ ⊢ f : (x : A) → B    Γ ⊢ a : A
──────────────────────────────────
Γ ⊢ f a : B[a/x]
```

**Lambda**
```
Γ ⊢ A : Sort(u)    Γ, x:A ⊢ b : B
───────────────────────────────────
Γ ⊢ (fun x : A => b) : (x : A) → B
```

**Pi (Forall)**
```
Γ ⊢ A : Sort(u)    Γ, x:A ⊢ B : Sort(v)
──────────────────────────────────────────
Γ ⊢ ((x : A) → B) : Sort(imax(u, v))
```

**Let**
```
Γ ⊢ A : Sort(u)    Γ ⊢ val : A    Γ, x:A := val ⊢ body : B
─────────────────────────────────────────────────────────────
Γ ⊢ (let x : A := val; body) : B[val/x]
```

### 2.7 Definitional equality

Two terms are **definitionally equal** if they compute to the same value. This
is more than syntactic equality — it includes:

- **α-equivalence**: `fun x => x` ≡ `fun y => y` (names don't matter)
- **β-reduction**: `(fun x => body) a` ≡ `body[a/x]`
- **δ-reduction**: unfold definitions — `Nat.succ 0` ≡ `1`
- **ζ-reduction**: inline let bindings — `let x := 3; x + 1` ≡ `4`
- **ι-reduction**: recursor/constructor reduction — the computation rule for
  inductive types
- **η-expansion**: `f` ≡ `fun x => f x` when `f : A → B`
- **Proof irrelevance**: any two proofs of the same `Prop` are equal

The kernel's `isDefEq` algorithm (§4) decides definitional equality. The
application rule requires `a : A` *up to definitional equality* — the argument
type need not be syntactically identical to the domain, just definitionally equal.

---

## 3. Data structures

### 3.1 `Expr.java` — compact expression nodes

Each expression is a single Java object with:
- A `byte tag` (0–12, the expression kind)
- A `long data` packing bvarRange (20 bits), structural hash (32 bits), hasFVar
  (1 bit), hasLevelParam (1 bit)
- Up to 4 object fields (`o0`–`o3`) for children
- A `long longVal` for literals

This gives ~72 bytes per node (vs ~200 for a Clojure persistent vector), a 64%
memory reduction for large proof trees.

**Hash-consing** (intern table): factory methods (`Expr.app`, `Expr.lam`, etc.)
look up structurally equal expressions in a thread-local `HashMap` and return
the *same object* if found. After interning, pointer equality (`==`) implies
structural equality. This is how Lean 4's C++ arena allocator achieves the same
effect — two allocations of identical terms land at the same pointer.

**`shareCommon()`**: Before checking a declaration, all expressions in the
proof are run through a bottom-up pass that rebuilds the tree with canonical
pointers. This makes the identity-based caches (`IdentityHashMap`) in
`TypeChecker` and `Reducer` effective — two syntactically identical
subexpressions will share one cache entry.

**`deepReIntern()`**: After reduction produces a new expression, it may contain
subterms not yet in the intern table. `deepReIntern` walks the result bottom-up
and inserts everything, ensuring future pointer comparisons work.

**Lean 4 reference**: `src/kernel/expr.h`, `src/kernel/expr.cpp`

### 3.2 `Level.java` — universe level algebra

Levels normalize **at construction time** (matching `mk_max`, `mk_imax` in
`lean4/src/kernel/level.cpp`):

- `succ(max(a, b))` is immediately rewritten to `max(succ(a), succ(b))`
- `max(u, 0)` simplifies to `u`
- `imax(u, 0)` simplifies to `0`
- `imax(u, succ(v))` simplifies to `max(u, succ(v))`

This means two level expressions that are provably equal will often be the same
object after construction, enabling pointer equality checks.

`Level.simplify()` performs full normalization: flattens max trees, removes
subsumed constants, and sorts components into a canonical order.

**Lean 4 reference**: `src/kernel/level.cpp`, functions `geq_core`, `geq_go`.

### 3.3 `Env.java` — immutable global environment

The environment maps constant names to `ConstantInfo` (type + optional value +
reducibility hint). It is **immutable** — `addConstant` returns a new `Env`.
This is important because:

- Type checking a declaration produces a new `Env` with that declaration added.
- The old `Env` is still valid (structural sharing via Clojure's
  `PersistentHashMap`).
- Fork is free — no copying needed.

For large stores (Mathlib's 648K declarations), a `SoftReference` cache wraps
an external PSS lookup. Declarations are fetched from disk on demand and cached
with soft references so the JVM can reclaim cold entries under memory pressure.

**Lean 4 reference**: `src/kernel/environment.h`, `src/kernel/environment.cpp`

---

## 4. The two main algorithms

### 4.1 WHNF — weak head normal form

`whnf(e)` reduces a term until its *head* (outermost constructor) cannot be
reduced further. It applies these reductions in order:

| Rule | Name | Example |
|------|------|---------|
| **β** | Beta | `(fun x => body) a  →  body[a/x]` |
| **δ** | Delta | `Nat.add  →  (its definition body)` |
| **ζ** | Zeta | `let x := v; body  →  body[v/x]` |
| **ι** | Iota | `Nat.rec z s (Nat.succ n)  →  s n (Nat.rec z s n)` |
| **η** | Eta | `f  →  fun x => f x` (only for equality, not WHNF) |

The implementation in `Reducer.java` (`whnfCoreImpl`) is a loop:

1. Collect arguments via `getAppFnArgs` (avoids allocation for single apps)
2. Reduce the function head recursively
3. If head became a `LAM`: beta-reduce (substitute all args at once via `instantiateRev`)
4. If head is a recursor `CONST` applied to enough args: iota-reduce via `reduceRecursor`
5. If head is a `LET` fvar: zeta-reduce
6. If expression is a `PROJ`: try to extract constructor field (`reduceProj`)

Results are cached in an `IdentityHashMap` — once a term is reduced, the result
is reused for any pointer-identical occurrence.

**`cheapRec` / `cheapProj` flags**: During `isDefEq`, the first whnf call uses
`cheapRec=false, cheapProj=true`. This avoids expensive recursor unfolding on
the first pass but still handles projections. A second full-reduction pass fires
only if needed.

**Lean 4 reference**: `src/kernel/type_checker.cpp:449` (`whnf_core`).

### 4.2 `isDefEq` — definitional equality

`isDefEq(t, s)` is the heart of the kernel. It returns `true` iff `t` and `s`
are definitionally equal. The algorithm is a sequence of increasingly expensive
checks that short-circuit as soon as an answer is found.

Here are the steps, in order, matching `type_checker.cpp:1117`
(`is_def_eq_core`) in Lean 4:

#### Step 1: Quick check (`quick_is_def_eq`, `use_hash=true`)

Before doing any work, ask the `EquivManager` (union-find, §5): have we already
proven these equal? Also handles trivial structural cases:
- Same pointer → equal
- Both `SORT` with equal levels → equal
- Both `CONST` with same name and equal levels → equal
- Both `BVAR` with same index → equal
- Both literals with same value → equal
- Both `LAM`/`FORALL` — check domain and body (ignoring binder names)

Returns `true`, `false`, or `unknown`.

**Lean 4 reference**: `type_checker.cpp:801` (`quick_is_def_eq`),
`type_checker.h:85` (`use_hash = false` default in the header).

#### Step 2: Bool.true shortcut

If `s` is `Bool.true` and `t` has no free variables: reduce `t` to whnf and
check if it is also `Bool.true`. Lean 4 uses this for the `decide` tactic.

**Lean 4 reference**: `type_checker.cpp:1131`.

#### Step 3: `whnf_core` (cheap pass)

Reduce both sides with `whnfCore(e, cheapRec=false, cheapProj=true)` — this
handles β, ζ, projections, but avoids expensive recursor unfolding. Then repeat
the quick check on the reduced forms.

#### Step 4: Proof irrelevance

If both terms have a type that is in `Prop` (a proposition), they are
definitionally equal regardless of their structure — proof irrelevance is a
theorem of CIC. This is checked by inferring the types and asking if they are
equal propositions.

Note: the Ansatz kernel has an *extra* proof-irrelevance check (Step 13 in
`TypeChecker.java`) applied after full delta reduction, not present in Lean 4.
This is sound (proof irrelevance holds in CIC) but is an extension.

**Lean 4 reference**: `type_checker.cpp:1152` (`is_def_eq_proof_irrel`).

#### Step 5: Lazy delta reduction (the key loop)

This is the most important step for performance. It unfolds definitions *one at
a time*, guided by **reducibility hints**, rather than eagerly reducing both
sides to normal form.

Each definition carries a hint:
- `opaque` — never unfold (unless transparency=all)
- `abbrev` — unfold first (low hint weight)
- `regular n` — unfold with weight `n` (higher weight = unfold later)

The loop in `lazy_delta_reduction` (`type_checker.cpp:1034`):

```
while true:
  1. Nat offset check: strip Nat.succ, compare nat literals
  2. Native/builtin reduction (Nat arithmetic without free vars)
  3. lazy_delta_reduction_step:
     - Neither side is a definition → unknown, exit loop
     - Only left is a definition → unfold left
     - Only right is a definition → unfold right
     - Both are definitions, same hint weight:
         • Try comparing args WITHOUT unfolding (fail cache check)
         • If args match → equal (avoid unfolding)
         • Otherwise → unfold both
     - Both are definitions, different hint weights → unfold cheaper one
  4. After each unfold: run quick_is_def_eq (use_hash=false)
```

The `use_hash=false` in the post-unfold quick check is critical: after
unfolding, structurally different but previously-proven-equal expressions need
the union-find lookup to succeed. The hash fast-reject would block it. (See §5
for details.)

**Lean 4 reference**: `type_checker.cpp:938` (`lazy_delta_reduction_step`),
`type_checker.cpp:1034` (`lazy_delta_reduction`).

#### Step 6: Same-head constant / free variable

After lazy delta, if both sides have the same head constant (same name, equal
universe levels) or same free variable id → equal.

Also handles projections with same index via `lazy_delta_proj_reduction`.

#### Step 7: Second `whnf_core` (full pass)

Reduce with `whnfCore(e, cheapRec=false, cheapProj=false)` — now with recursor
unfolding enabled. If either side changed, recurse into `isDefEqCore`.

#### Step 8: Application equality

If both sides are applications with the same structure, check the function and
all arguments pairwise.

#### Step 9: Binding equality

If both sides are `LAM`/`FORALL` chains: walk them together, create fresh free
variables for each binder (when the body uses the variable), and recurse on the
bodies.

Optimization: if domains are pointer-identical, skip the domain check entirely.

#### Step 10: Eta expansion

If one side is a lambda and the other is not, try eta-expanding: `f ≡ fun x => f x`.

#### Step 11: Eta struct

If one side is a structure constructor and the other is a struct value, try
eta-expanding to field comparisons.

#### Step 12: String literal expansion

If one side is a string literal, expand it to the constructor form
(`String.mk (List Char)`) and recurse. Lean 4 represents string literals
compactly at the kernel level but expands them for equality checks.

**Lean 4 reference**: `type_checker.cpp:1218` (`try_string_lit_expansion`).

#### Step 13: Unit-like types

If both terms have a type with zero fields (a "unit-like" structure, e.g.
`PUnit`), they are equal regardless of value.

#### After success: record in `EquivManager`

If `isDefEqCore` returns `true`, `isDefEq` records the pair in the
`EquivManager` union-find. Future calls with the same pair (or transitively
proven pairs) will hit the quick check at Step 1.

**Lean 4 reference**: `type_checker.cpp:1237` (`is_def_eq` calls
`m_st->m_eqv_manager.add_equiv(t, s)`).

### 4.3 Type inference (`inferType`)

`inferType(e)` computes the type of expression `e` in the current local context.
It dispatches on the expression kind:

| Kind | Result |
|------|--------|
| `BVAR` | *(should not appear — bvars are always under a binder)* |
| `FVAR` | Look up in local context `lctx`, return declared type |
| `SORT(u)` | `SORT(succ(u))` |
| `CONST(c, levels)` | Look up `c` in env, instantiate level params |
| `APP(f, a)` | Infer type of `f` (must be Pi), check `a : domain`, return `codomain[a/x]` |
| `LAM(x:A, body)` | Walk binder chain, infer body type, return Pi |
| `FORALL(x:A, B)` | Walk binder chain, compute `Sort(imax(level(A), level(B)))` |
| `LET(x:A:=v, body)` | Check `v : A`, infer body type |
| `PROJ(idx, e)` | Infer type of `e`, find inductive, extract field type |
| `LIT_NAT` | `Nat` |
| `LIT_STR` | `String` |
| `MDATA(_, e)` | Recurse on inner expression |

The `infer_only` flag (used in `APP` inference for speed): when `true`, skip
type-checking the argument and just compute the return type. This avoids
redundant `isDefEq` calls when the argument type is already known to be correct.

**Lean 4 reference**: `type_checker.cpp:318` (`infer_type_core`).

---

## 5. The EquivManager and why `use_hash` matters

`EquivManager.java` is a **union-find** data structure over expressions. Every
time `isDefEq` proves `t ≡ s`, it calls `addEquiv(t, s)`, merging them into
the same equivalence class. Future calls to `isEquiv(t, s)` can then return
`true` immediately (Step 1 of `isDefEq`) without re-checking.

The critical subtlety is the `use_hash` parameter. `EquivManager.isEquiv` can
do two things:

1. **Hash fast-reject** (`use_hash=true`): compute structural hash of both
   expressions and reject if they differ. This is cheap but wrong for
   structurally different but provably-equal expressions.

2. **Union-find lookup** (`use_hash=false`): skip the hash check and go
   directly to the union-find, which correctly handles expressions that were
   proven equal by earlier reduction steps.

Lean 4's `quick_is_def_eq` defaults to `use_hash=false` (see
`type_checker.h:85`). The Ansatz Java implementation matches this in the
lazy delta loop: the post-unfold `quickIsDefEq(tn, sn, false)` calls in
`lazyDeltaReduction` and `lazyDeltaReductionStep` use `use_hash=false`.

**Why this matters**: During lazy delta reduction, each unfolding step produces
expressions that are structurally different from the originals but may be equal
to previously-seen forms. If the hash check fires first, it rejects pairs that
the union-find would have recognized as equal, forcing the loop to continue
unfolding unnecessarily.

**The `localCohomology.diagramComp` case**: This Mathlib declaration required
>3.9M steps with `use_hash=true` (diverging) and 5,891 steps with
`use_hash=false`. The fix was a one-line change matching Lean 4's default.

**Lean 4 reference**: `src/kernel/equiv_manager.h`, `src/kernel/equiv_manager.cpp`.

---

## 6. Checking a declaration

`TypeChecker.checkConstant(env, ci, fuel)` is the top-level entry point. It:

1. **`shareCommon`**: Run all expressions in the declaration (type + value)
   through the pointer-sharing pass. This makes identity-based caches work.

2. **`Expr.seedIntern`**: Insert all shared expressions into the intern table,
   so `deepReIntern` results can match them by pointer.

3. For **theorems and definitions** (`checkType`):
   - Infer the type of the value: `T_inferred = inferType(value)`
   - Check `T_inferred ≡ T_declared` via `isDefEq`
   - This is the core correctness check: the proof really proves what it claims

4. For **inductives** (`checkConstant` with tag 5):
   - `validateInductiveResultSort`: universe of the result type is correct
   - `validateConstructor`: each constructor type is well-formed
   - `validateRecursorRules`: computation rules match constructor patterns

5. **Tracing**: Both kernels support NDJSON trace output, but the Lean 4 side
   requires a patched build. We added `LEAN_KERNEL_TRACE` support to our local
   Lean 4 fork (commit `55f80e10` in `../lean4`) — it is not in upstream Lean 4.
   Set `LEAN_KERNEL_TRACE=/tmp/trace.ndjson` (optionally scoped with
   `LEAN_KERNEL_TRACE_DECL=name`). In Ansatz, use `TypeChecker/checkConstantTraced`
   with a `FileWriter`. Both emit NDJSON lines with `{s, d, l, r, res, by}` —
   sequence, depth, lhs/rhs fingerprints, result, and which step resolved it.

6. **Fuel**: Each `isDefEq` step decrements a fuel counter. If it reaches zero,
   checking fails with a fuel-exhaustion error. The default is 20M steps, which
   is sufficient for all known Mathlib declarations (heaviest: ~6K steps for
   `localCohomology.diagramComp` after the `use_hash` fix).

The returned `Env` has the new declaration added. The caller threads this new
`Env` to the next declaration, building up the cumulative environment.

---

## 7. What the kernel does NOT do

The kernel's job is narrow by design. It does **not**:

- **Elaborate**: resolve implicit arguments, fill in universe levels, infer
  type class instances. This is done by the elaborator in `ansatz.tactic`.
- **Search**: find proofs, apply tactics, synthesize instances.
- **Parse**: read surface syntax. Proofs arrive as fully explicit CIC terms.
- **Pretty-print**: no display logic.
- **Handle metavariables**: `MVAR` expressions are an elaborator concept. The
  kernel only sees closed, fully-instantiated terms.

The boundary is `TypeChecker/checkConstant`. Everything above it is untrusted
tooling that helps construct terms; everything below is the trusted checker.

---

## 8. Quick reference

### Expression kinds

```java
// Expr.java tag constants
BVAR    = 0   // bvar(idx)           — bound variable (de Bruijn)
SORT    = 1   // sort(level)         — universe
CONST   = 2   // const(name, levels) — global reference
APP     = 3   // app(fn, arg)        — application
LAM     = 4   // lam(name, type, body)
FORALL  = 5   // forall(name, type, body) — Pi type
LET     = 6   // let(name, type, value, body)
LIT_NAT = 7   // litNat(BigInteger)
LIT_STR = 8   // litStr(String)
MDATA   = 9   // mdata(data, expr)   — transparent metadata
PROJ    = 10  // proj(name, idx, expr)
FVAR    = 11  // fvar(id)            — free variable (local hypothesis)
MVAR    = 12  // mvar(id)            — metavariable (elaborator only)
```

### `isDefEq` step summary

| Step | Name | Fires when |
|------|------|-----------|
| 1 | Quick / EquivManager | Same pointer, trivial structure, or previously proven equal |
| 2 | Bool.true shortcut | `s = Bool.true`, `t` has no fvars |
| 3 | whnfCore (cheap) | Either side reduces under cheap flags |
| 4 | Proof irrelevance | Both terms are proofs of the same `Prop` |
| 5 | Lazy delta reduction | Either or both sides are unfoldable definitions |
| 6 | Same-head check | Same constant name or same fvar id after delta |
| 7 | whnfCore (full) | Either side reduces with recursor unfolding |
| 8 | Application | Both sides are applications with equal fn and args |
| 9 | Binding | Both sides are `LAM`/`FORALL` chains |
| 10 | Eta expansion | One side is `LAM`, other can be eta-expanded |
| 11 | Eta struct | One side is a struct constructor |
| 12 | String literal expansion | One side is a string literal |
| 13 | Unit-like | Both sides have a zero-field type |

### Key Lean 4 source cross-references

| Concept | Lean 4 file | Lines |
|---------|-------------|-------|
| `is_def_eq_core` | `src/kernel/type_checker.cpp` | 1117–1235 |
| `whnf_core` | `src/kernel/type_checker.cpp` | 449–530 |
| `lazy_delta_reduction_step` | `src/kernel/type_checker.cpp` | 945–1002 |
| `lazy_delta_reduction` | `src/kernel/type_checker.cpp` | 1034–1060 |
| `quick_is_def_eq` | `src/kernel/type_checker.cpp` | 801 |
| `use_hash` default | `src/kernel/type_checker.h` | 85 |
| `infer_type_core` | `src/kernel/type_checker.cpp` | 318 |
| `equiv_manager` | `src/kernel/equiv_manager.h/cpp` | — |
| `level.cpp` geq algorithm | `src/kernel/level.cpp` | — |

### Further reading

- **ammkrn**, [*Type Checking in Lean 4*](https://ammkrn.github.io/type_checking_in_lean4/)
  — The best single reference for the Lean 4 kernel. Covers expressions,
  universes, WHNF, definitional equality, and inductive types with the same
  level of detail as this document. Cross-reads well with the C++ source.

- **Mario Carneiro**, [*Lean4Lean: Verifying a Typechecker for Lean, in Lean*](https://arxiv.org/abs/2403.14064)
  (2024) — An independent Lean 4 typechecker written in Lean itself, verifying
  all of Mathlib. The paper formalizes Lean's type theory and already found one
  soundness bug in the reference kernel.

- **Mario Carneiro**, [*The Type Theory of Lean*](https://github.com/digama0/lean-type-theory)
  (2019, MS thesis) — Formalizes Lean's CIC variant in Metamath Zero. The
  foundational reference for Lean 4's consistency argument and universe
  polymorphism semantics including `imax`.

- **Thierry Coquand and Gérard Huet**, *The Calculus of Constructions* (1988,
  Information and Computation 76(2–3):95–120) — The original CoC paper.
  Inductive types were added by Thierry Coquand and Christine Paulin-Mohring.

- **Leonardo de Moura et al.**, [*The Lean Theorem Prover (system description)*](https://lean-lang.org/papers/system.pdf)
  (CADE 2015) — Original system paper. Introduces universe polymorphism,
  `imax`, and the definitional equality algorithm. Most of the kernel design
  described here originates here.

- **Leonardo de Moura and Sebastian Ullrich**, *The Lean 4 Theorem Prover and
  Programming Language* (CADE 2021) — Describes Lean 4's redesign: dependent
  pattern matching, do-notation, and the macro system. The kernel algorithm
  itself did not change substantially from Lean 3.

- **Rocq/Coq CIC reference**, [*Typing rules*](https://rocq-prover.org/doc/V9.1.0/refman/language/cic.html)
  — The Coq/Rocq manual has the most complete formal presentation of CIC typing
  rules. Lean 4's type theory is similar but differs in universe polymorphism
  details (`imax` vs Coq's cumulativity).

- **Lean 4 source**: [`src/kernel/`](https://github.com/leanprover/lean4/tree/master/src/kernel)
  in the lean4 repository. The C++ reference implementation is the authoritative
  source for Ansatz's algorithm.

### Other external type checkers for Lean 4

Ansatz is one of several independent reimplementations of the Lean 4 kernel.
Others to compare against:

| Project | Language | Notes |
|---------|----------|-------|
| [lean4lean](https://github.com/digama0/lean4lean) | Lean 4 | First complete independent checker; verified all of Mathlib; found one soundness bug |
| [nanoda_lib](https://github.com/ammkrn/nanoda_lib) | Rust | Author also wrote "Type Checking in Lean 4" guide |
| [lean4checker](https://github.com/leanprover/lean4checker) | Lean 4 | Official lightweight re-checker |
| Ansatz | Java/Clojure | This project; verified all 648,612 Mathlib declarations |
