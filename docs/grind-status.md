# Grind Tactic — Architecture and Status

## Architecture (following Lean 4)

Pure Clojure implementation across 4 files:
- **egraph.clj** (~550 lines) — persistent E-graph with CC, propositional propagators (And/Or/Not/Eq/ite), constructor injection/discrimination
- **proof.clj** (~300 lines) — kernel-verified proof reconstruction from E-graph paths (Eq.refl/symm/trans, congrArg/congrFun/congr)
- **ematch.clj** (~280 lines) — E-matching engine for automatic theorem instantiation with generation tracking and instance dedup
- **solver.clj** (~160 lines) — theory solver protocol with omega/ring/order adapters
- **grind.clj** (~400 lines) — main loop with strategy chain, fast paths, simp integration

## What Works (kernel-verified)

### E-Graph Congruence Closure
| Test | Time | Notes |
|------|------|-------|
| `n = n` | 0.4ms | Reflexivity |
| `a = b → b = a` | 1ms | Symmetry |
| `a=b, b=c → a=c` | 1ms | Transitivity |
| `a=b → f(a) = f(b)` | 0.7ms | Congruence |
| `a=b → g(f(a)) = g(f(b))` | 1ms | Deep congruence |
| `a=b, xs=ys → cons a xs = cons b ys` | 1ms | Multi-arg congruence |
| `f=g, a=b → f(a) = g(b)` | 1ms | Function equality |

### Constructor Theory
| Test | Time | Notes |
|------|------|-------|
| `cons a xs = cons b ys → a = b` | 0.5ms | Injection via T.ctor.inj |
| `cons a xs = nil → False` | 0.5ms | Discrimination via noConfusion |
| `a=true, b=false, a=b → False` | 0.7ms | Indirect discrimination (subst chain) |
| `a=nil, b=cons, a=b → False` | 4ms | List noConfusion with HEq |

### Logic and Propositions
| Test | Time | Notes |
|------|------|-------|
| `P, P→Q ⊢ Q` | 1ms | Modus ponens |
| `P, P→Q, Q→R, R→S ⊢ S` | 1ms | Chained implications |
| `P∧Q ⊢ P` | 0.5ms | And.left |
| `P∧Q ⊢ Q` | 0.5ms | And.right |
| `P ⊢ P∨Q` | 1ms | Or.inl (constructor) |
| `False ⊢ P` | 0.4ms | False.elim fast path |

### E-Matching and Arithmetic
| Test | Time | Notes |
|------|------|-------|
| `a+b = b+a` via Nat.add_comm | 3ms | E-matching |
| `(a+b)+c = a+(b+c)` via Nat.add_assoc | 6ms | E-matching |
| `n + 0 = n` | 1ms | Omega |
| `not(not b) = b` | 4ms | Bool case-split fast path |

### Induction + Grind (CSLib-level)
| Property | Proof |
|----------|-------|
| `len (map f l) = len l` | `(induction l) (all_goals (grind "lmap" "llen"))` |
| `map f (xs++ys) = (map f xs)++(map f ys)` | `(induction xs) (all_goals (grind "lmap" "lappend"))` |
| `filter p (xs++ys) = (filter p xs)++(filter p ys)` | `(induction xs) (simp_all+grind)` |
| `(xs++ys)++zs = xs++(ys++zs)` | `(induction xs) (all_goals (grind "lappend"))` |
| `xs++[] = xs` | `(induction xs) (simp_all+grind)` |
| `len(xs++ys) = len xs + len ys` | `(induction xs) (simp_all "Nat.add_assoc"+grind)` |
| `map id l = l` | `(induction l) (simp_all+grind)` |
| `Sorted l → Sorted (insertSorted x l)` | `(induction h) (grind "insertSorted")` |
| `ValidRB l → ValidRB r → ValidRB (balance1 l v r)` | `(cases hl) (simp+grind) (cases...) (simp+grind)` |

## Performance (vs Lean 4)

| Category | Lean 4 | Ansatz | Ratio |
|----------|--------|--------|-------|
| Core CC | 0.2-0.7ms | 0.4-1ms | 1.5-2x |
| Constructor theory | 0.2-0.7ms | 0.5-4ms | 1-6x |
| E-matching | 0.3ms | 3-6ms | 10-19x |
| Bool case-split | 0.2ms | 4ms | 17x |
| False.elim | 0.2ms | 0.4ms | 1.7x |

Core CC is within 2x of Lean 4. E-matching is 10-19x due to Clojure persistent map overhead. Bool case-split gap is from strategy iteration (Lean 4 uses CPS-based direct dispatch).

## Key Design Decisions

1. **Persistent E-graph** — Clojure immutable maps give free backtracking for case splits (no save/restore needed)
2. **Transparency-controlled WHNF** — equation theorems use `reducible` mode, preserving `+` as `HAdd.hAdd` (not `Nat.brecOn`)
3. **Fast paths** — False hypothesis and Bool Eq goals detected before strategy chain
4. **Generation tracking** — E-matching terms get gen>0, only gen=0 candidates matched (prevents infinite loops)
5. **Structural equality in proofs** — proof.clj uses `.equals` not `identical?` for chain walking (handles E-match-created terms)

## Remaining Gaps vs Lean 4

- **`@[grind]` attribute system** — we pass lemma names as strings, no attribute scan
- **`grind only [...]`** — scoped lemma lists not implemented
- **Directional lemmas** — `=_`, `<=`, `=>` hints not parsed
- **Or.inr** — constructor strategy tries Or.inl first, needs try-all approach
- **Non-chronological backtracking** — forward-only (persistent data gives free forking but no pruning)
- **Full Lean 4 preprocessing pipeline** — we use simp as post-processing, not preprocessing
