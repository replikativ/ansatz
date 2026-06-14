;; A native formalization of the EDN / Clojure value universe in Ansatz.
;;
;; Clojure's data is essentially EDN: nil, booleans, numbers, strings, keywords,
;; symbols, lists/vectors, maps, sets. We model the whole universe as a single
;; inductive `Value` (cons-cell style, since Ansatz's `a/inductive` supports
;; direct recursion but not nesting under `List`). Every Clojure value is a
;; `Value`; every core operation is a total function over `Value`s.
;;
;; This is the foundation for verified optimization of real Clojure data
;; pipelines: the runtime↔kernel bridge is just an ENCODING (the kernel `Value`
;; IS the EDN AST), the tightest possible link.
;;
;; Map representation: an entry-chain (`ventry k v rest` … `vnil`) tagged by
;; `vmap`. `vassoc` prepends (shadowing); `vget1` reads the head. Canonical
;; (sorted, deduped) maps with scanning `get`/`dissoc` and decidable key equality
;; are the next layer.
;;
;; Requires the env seeded with Lean `Init` (Nat, Bool, Int, String). Call
;; `install-core!` after `(a/init! …)` or after replaying an Init export.

(ns ansatz.surface.data
  "The DATA leg of ansatz's Clojure↔kernel bridge (sibling of the code leg in ansatz.surface.*): the
   universal `Value`/EDN universe — one inductive carrying every Clojure value (nil/bool/int/str/kw/
   list/vec/map/set/float) + structural ops + the edn->value/value->edn runtime boundary + the
   native-Clojure-over-Value surface (`:k`/`get`/`int?`/`==`/`count`/`assoc` over dynamic data). The
   schema leg (malli→type/conformance) is ansatz.surface.schema. Opt-in: install-core! (Value type/ops)
   + install-surface! (the native verbs), against an Init env."
  (:require [ansatz.core :as a]
            [ansatz.surface.api :as api]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.env :as env]))

(defn- head-name
  "Head constant name of a kernel type/term expr (\"Int\" for `Int`, \"List\" for `(List Nat)`), or nil."
  [t]
  (let [[h _] (when t (e/get-app-fn-args t))]
    (when (and h (e/const? h)) (name/->string (e/const-name h)))))

(defn- kw-str [k] (subs (str k) 1))   ;; full keyword incl. namespace, matching edn->value

(def ^:private core-forms
  '[;; The EDN value universe. (vfloat/vset appended last to keep ctor indices stable.)
    (ansatz.core/inductive Value []
                           (vnil)
                           (vbool [b Bool])
                           (vint  [i Int])
                           (vstr  [s String])
                           (vkw   [s String])
                           (vcons [head Value] [tail Value])        ;; list/vector payload
                           (vvec  [items Value])
                           (vmap  [entries Value])                  ;; tag an entry-chain as a map
                           (ventry [k Value] [v Value] [rest Value])
                           (vfloat [f Float])                       ;; EDN double
                           (vset  [items Value]))                   ;; tag a cons-chain as a set

    ;; assoc = prepend an entry (shadowing semantics).
    (ansatz.core/defn vassoc [m :- Value, k :- Value, v :- Value] Value
      (Value.ventry k v m))

    ;; map-level put — `(assoc mapValue k v)`: prepend into the vmap's entry-chain (shadowing),
    ;; re-tagging as a vmap. A non-map receiver becomes a fresh single-entry map (assoc nil → {}).
    (ansatz.core/defn vput [m :- Value, k :- Value, val :- Value] Value
      (match m Value Value
        (vnil (Value.vmap (Value.ventry k val (Value.vnil))))
        (vbool [b] (Value.vmap (Value.ventry k val (Value.vnil))))
        (vint [i] (Value.vmap (Value.ventry k val (Value.vnil))))
        (vstr [s] (Value.vmap (Value.ventry k val (Value.vnil))))
        (vkw [s] (Value.vmap (Value.ventry k val (Value.vnil))))
        (vcons [h t] (Value.vmap (Value.ventry k val (Value.vnil))))
        (vvec [it] (Value.vmap (Value.ventry k val (Value.vnil))))
        (vmap [e] (Value.vmap (Value.ventry k val e)))
        (ventry [ek ev r] (Value.vmap (Value.ventry k val m)))
        (vfloat [f] (Value.vmap (Value.ventry k val (Value.vnil))))
        (vset [it] (Value.vmap (Value.ventry k val (Value.vnil))))))

    ;; get-head: the value of the first entry (vnil if not a map-entry).
    (ansatz.core/defn vget1 [m :- Value] Value
      (match m Value Value
             (vnil (Value.vnil)) (vbool [b] (Value.vnil)) (vint [i] (Value.vnil))
             (vstr [s] (Value.vnil)) (vkw [s] (Value.vnil)) (vcons [h t] (Value.vnil))
             (vvec [it] (Value.vnil)) (vmap [en] (Value.vnil)) (ventry [k v r] v)
             (vfloat [f] (Value.vnil)) (vset [it] (Value.vnil))))

    ;; Structural node count — recursive (compiles via the auto-sizeOf measure).
    (ansatz.core/defn vcount [m :- Value] Nat
      (match m Value Nat
             (vnil 0) (vbool [b] 0) (vint [i] 0) (vstr [s] 0) (vkw [s] 0)
             (vcons [h t] (Nat.succ (Nat.add (vcount h) (vcount t))))
             (vvec [it] (Nat.succ (vcount it)))
             (vmap [en] (Nat.succ (vcount en)))
             (ventry [k v r] (Nat.succ (Nat.add (vcount k) (Nat.add (vcount v) (vcount r)))))
             (vfloat [f] 0) (vset [it] (Nat.succ (vcount it)))))

    ;; First law: get-after-assoc holds definitionally (assoc prepends, get reads
    ;; the head), discharged by rfl.
    (ansatz.core/theorem vget-vassoc [m :- Value, k :- Value, v :- Value]
                         (= Value (vget1 (vassoc m k v)) v)
                         (rfl))

    ;; ── SCHEMA-AS-REFINEMENT layer: a malli schema is a conformance PREDICATE over Value.
    ;; Type predicates (match on the constructor).
    (ansatz.core/defn vint?   [v :- Value] Bool (match v Value Bool (vnil false) (vbool [b] false) (vint [i] true)  (vstr [s] false) (vkw [s] false) (vcons [h t] false) (vvec [it] false) (vmap [e] false) (ventry [k w r] false) (vfloat [f] false) (vset [it] false)))
    (ansatz.core/defn vstr?   [v :- Value] Bool (match v Value Bool (vnil false) (vbool [b] false) (vint [i] false) (vstr [s] true)  (vkw [s] false) (vcons [h t] false) (vvec [it] false) (vmap [e] false) (ventry [k w r] false) (vfloat [f] false) (vset [it] false)))
    (ansatz.core/defn vbool?  [v :- Value] Bool (match v Value Bool (vnil false) (vbool [b] true)  (vint [i] false) (vstr [s] false) (vkw [s] false) (vcons [h t] false) (vvec [it] false) (vmap [e] false) (ventry [k w r] false) (vfloat [f] false) (vset [it] false)))
    (ansatz.core/defn vmap?   [v :- Value] Bool (match v Value Bool (vnil false) (vbool [b] false) (vint [i] false) (vstr [s] false) (vkw [s] false) (vcons [h t] false) (vvec [it] false) (vmap [e] true)  (ventry [k w r] false) (vfloat [f] false) (vset [it] false)))
    (ansatz.core/defn vnil?   [v :- Value] Bool (match v Value Bool (vnil true)  (vbool [b] false) (vint [i] false) (vstr [s] false) (vkw [s] false) (vcons [h t] false) (vvec [it] false) (vmap [e] false) (ventry [k w r] false) (vfloat [f] false) (vset [it] false)))
    (ansatz.core/defn vkw?    [v :- Value] Bool (match v Value Bool (vnil false) (vbool [b] false) (vint [i] false) (vstr [s] false) (vkw [s] true)  (vcons [h t] false) (vvec [it] false) (vmap [e] false) (ventry [k w r] false) (vfloat [f] false) (vset [it] false)))
    (ansatz.core/defn vvec?   [v :- Value] Bool (match v Value Bool (vnil false) (vbool [b] false) (vint [i] false) (vstr [s] false) (vkw [s] false) (vcons [h t] false) (vvec [it] true)  (vmap [e] false) (ventry [k w r] false) (vfloat [f] false) (vset [it] false)))
    (ansatz.core/defn vfloat? [v :- Value] Bool (match v Value Bool (vnil false) (vbool [b] false) (vint [i] false) (vstr [s] false) (vkw [s] false) (vcons [h t] false) (vvec [it] false) (vmap [e] false) (ventry [k w r] false) (vfloat [f] true)  (vset [it] false)))
    (ansatz.core/defn vset?   [v :- Value] Bool (match v Value Bool (vnil false) (vbool [b] false) (vint [i] false) (vstr [s] false) (vkw [s] false) (vcons [h t] false) (vvec [it] false) (vmap [e] false) (ventry [k w r] false) (vfloat [f] false) (vset [it] true)))
    ;; :any (always true) and :some (non-nil).
    (ansatz.core/defn vany?  [v :- Value] Bool true)
    (ansatz.core/defn vsome? [v :- Value] Bool (match v Value Bool (vnil false) (vbool [b] true)  (vint [i] true)  (vstr [s] true)  (vkw [s] true)  (vcons [h t] true)  (vvec [it] true)  (vmap [e] true)  (ventry [k w r] true) (vfloat [f] true) (vset [it] true)))

    ;; Decidable structural equality over the whole Value universe (for :enum / := / :not=).
    ;; Scalars compared by ==/Bool-iff; compounds by structural recursion. Total (fuel on x).
    ;; ^:partial: veq IS structurally terminating (every recursive call is on a field
    ;; of x), but the kernel-enforced WF encoder currently can't afford the 11x11
    ;; nested-match refinement (121 branches x embedded decrease proofs) — encoder
    ;; scaling is a filed follow-up. The TYPE is still kernel-checked.
    (ansatz.core/defn ^:partial veq [x :- Value, y :- Value] Bool
      (match x Value Bool
        (vnil (match y Value Bool (vnil true) (vbool [b] false) (vint [i] false) (vstr [s] false) (vkw [s] false) (vcons [h t] false) (vvec [it] false) (vmap [e] false) (ventry [k w r] false) (vfloat [f] false) (vset [it] false)))
        (vbool [b1] (match y Value Bool (vnil false) (vbool [b2] (if b1 b2 (Bool.not b2))) (vint [i] false) (vstr [s] false) (vkw [s] false) (vcons [h t] false) (vvec [it] false) (vmap [e] false) (ventry [k w r] false) (vfloat [f] false) (vset [it] false)))
        (vint [i1] (match y Value Bool (vnil false) (vbool [b] false) (vint [i2] (== i1 i2)) (vstr [s] false) (vkw [s] false) (vcons [h t] false) (vvec [it] false) (vmap [e] false) (ventry [k w r] false) (vfloat [f] false) (vset [it] false)))
        (vstr [s1] (match y Value Bool (vnil false) (vbool [b] false) (vint [i] false) (vstr [s2] (== s1 s2)) (vkw [s] false) (vcons [h t] false) (vvec [it] false) (vmap [e] false) (ventry [k w r] false) (vfloat [f] false) (vset [it] false)))
        (vkw [s1] (match y Value Bool (vnil false) (vbool [b] false) (vint [i] false) (vstr [s] false) (vkw [s2] (== s1 s2)) (vcons [h t] false) (vvec [it] false) (vmap [e] false) (ventry [k w r] false) (vfloat [f] false) (vset [it] false)))
        (vcons [h1 t1] (match y Value Bool (vnil false) (vbool [b] false) (vint [i] false) (vstr [s] false) (vkw [s] false) (vcons [h2 t2] (Bool.and (veq h1 h2) (veq t1 t2))) (vvec [it] false) (vmap [e] false) (ventry [k w r] false) (vfloat [f] false) (vset [it] false)))
        (vvec [it1] (match y Value Bool (vnil false) (vbool [b] false) (vint [i] false) (vstr [s] false) (vkw [s] false) (vcons [h t] false) (vvec [it2] (veq it1 it2)) (vmap [e] false) (ventry [k w r] false) (vfloat [f] false) (vset [it] false)))
        (vmap [e1] (match y Value Bool (vnil false) (vbool [b] false) (vint [i] false) (vstr [s] false) (vkw [s] false) (vcons [h t] false) (vvec [it] false) (vmap [e2] (veq e1 e2)) (ventry [k w r] false) (vfloat [f] false) (vset [it] false)))
        (ventry [k1 v1 r1] (match y Value Bool (vnil false) (vbool [b] false) (vint [i] false) (vstr [s] false) (vkw [s] false) (vcons [h t] false) (vvec [it] false) (vmap [e] false) (ventry [k2 v2 r2] (Bool.and (veq k1 k2) (Bool.and (veq v1 v2) (veq r1 r2)))) (vfloat [f] false) (vset [it] false)))
        (vfloat [f1] (match y Value Bool (vnil false) (vbool [b] false) (vint [i] false) (vstr [s] false) (vkw [s] false) (vcons [h t] false) (vvec [it] false) (vmap [e] false) (ventry [k w r] false) (vfloat [f2] (== f1 f2)) (vset [it] false)))
        (vset [it1] (match y Value Bool (vnil false) (vbool [b] false) (vint [i] false) (vstr [s] false) (vkw [s] false) (vcons [h t] false) (vvec [it] false) (vmap [e] false) (ventry [k w r] false) (vfloat [f] false) (vset [it2] (veq it1 it2))))))

    ;; Scalar extractors — pull a primitive out of a Value (default for the wrong ctor; under a
    ;; conforms refinement the default is unreachable). Let native arithmetic/compare on EDN
    ;; fields work: `(< 18 (:age r))` elaborates the Value field via `vint-val`.
    (ansatz.core/defn vint-val [v :- Value] Int
      (match v Value Int (vnil (Int.ofNat 0)) (vbool [b] (Int.ofNat 0)) (vint [i] i) (vstr [s] (Int.ofNat 0)) (vkw [s] (Int.ofNat 0)) (vcons [h t] (Int.ofNat 0)) (vvec [it] (Int.ofNat 0)) (vmap [e] (Int.ofNat 0)) (ventry [k w r] (Int.ofNat 0)) (vfloat [f] (Int.ofNat 0)) (vset [it] (Int.ofNat 0))))
    (ansatz.core/defn vfloat-val [v :- Value] Float
      (match v Value Float (vnil 0.0) (vbool [b] 0.0) (vint [i] 0.0) (vstr [s] 0.0) (vkw [s] 0.0) (vcons [h t] 0.0) (vvec [it] 0.0) (vmap [e] 0.0) (ventry [k w r] 0.0) (vfloat [f] f) (vset [it] 0.0)))
    (ansatz.core/defn vstr-val [v :- Value] String
      (match v Value String (vnil "") (vbool [b] "") (vint [i] "") (vstr [s] s) (vkw [s] s) (vcons [h t] "") (vvec [it] "") (vmap [e] "") (ventry [k w r] "") (vfloat [f] "") (vset [it] "")))
    (ansatz.core/defn vbool-val [v :- Value] Bool
      (match v Value Bool (vnil false) (vbool [b] b) (vint [i] false) (vstr [s] false) (vkw [s] false) (vcons [h t] false) (vvec [it] false) (vmap [e] false) (ventry [k w r] false) (vfloat [f] false) (vset [it] false)))

    ;; Element count — `(count v)` over a Value. vchain-len walks a vcons/ventry chain; vsize
    ;; gives the top-level element count (vstr → its String.length, like Clojure `count`).
    (ansatz.core/defn vchain-len [c :- Value] Nat
      (match c Value Nat (vnil 0) (vbool [b] 0) (vint [i] 0) (vstr [s] 0) (vkw [s] 0)
        (vcons [h t] (Nat.succ (vchain-len t))) (vvec [it] 0) (vmap [e] 0)
        (ventry [k v r] (Nat.succ (vchain-len r))) (vfloat [f] 0) (vset [it] 0)))
    (ansatz.core/defn vsize [v :- Value] Nat
      (match v Value Nat (vnil 0) (vbool [b] 0) (vint [i] 0) (vstr [s] (String.length s)) (vkw [s] 0)
        (vcons [h t] (Nat.succ (vchain-len t))) (vvec [it] (vchain-len it)) (vmap [e] (vchain-len e))
        (ventry [k v r] 0) (vfloat [f] 0) (vset [it] (vchain-len it))))

    ;; Key equality (keyword keys via String ==).
    (ansatz.core/defn vkeq [x :- Value, y :- Value] Bool
      (match x Value Bool (vnil false) (vbool [b] false) (vint [i] false) (vstr [s] false)
        (vkw [s1] (match y Value Bool (vnil false) (vbool [b] false) (vint [i] false) (vstr [s] false)
                    (vkw [s2] (== s1 s2)) (vcons [h t] false) (vvec [it] false) (vmap [e] false) (ventry [k w r] false) (vfloat [f] false) (vset [it] false)))
        (vcons [h t] false) (vvec [it] false) (vmap [e] false) (ventry [k w r] false) (vfloat [f] false) (vset [it] false)))

    ;; Per-type key checkers — "key k of map m holds a value of type T". Bool-returning
    ;; RECURSION over the entry-chain (Value-returning vget hits the custom-recursion gap, so
    ;; we inline the type-check instead). One per scalar malli type.
    (ansatz.core/defn key-int? [k :- Value, m :- Value] Bool
      (match m Value Bool (vnil false) (vbool [b] false) (vint [i] false) (vstr [s] false) (vkw [s] false)
        (vcons [h t] false) (vvec [it] false) (vmap [en] (key-int? k en))
        (ventry [ek ev rest] (if (vkeq k ek) (vint? ev) (key-int? k rest))) (vfloat [f] false) (vset [it] false)))
    (ansatz.core/defn key-str? [k :- Value, m :- Value] Bool
      (match m Value Bool (vnil false) (vbool [b] false) (vint [i] false) (vstr [s] false) (vkw [s] false)
        (vcons [h t] false) (vvec [it] false) (vmap [en] (key-str? k en))
        (ventry [ek ev rest] (if (vkeq k ek) (vstr? ev) (key-str? k rest))) (vfloat [f] false) (vset [it] false)))
    (ansatz.core/defn key-bool? [k :- Value, m :- Value] Bool
      (match m Value Bool (vnil false) (vbool [b] false) (vint [i] false) (vstr [s] false) (vkw [s] false)
        (vcons [h t] false) (vvec [it] false) (vmap [en] (key-bool? k en))
        (ventry [ek ev rest] (if (vkeq k ek) (vbool? ev) (key-bool? k rest))) (vfloat [f] false) (vset [it] false)))

    ;; vget — lookup key `k` in map `m`, returning the VALUE (vnil if absent). A general
    ;; Value-RETURNING recursion (works since the #58 fuel-base-case fix).
    (ansatz.core/defn vget [k :- Value, m :- Value] Value
      (match m Value Value (vnil (Value.vnil)) (vbool [b] (Value.vnil)) (vint [i] (Value.vnil))
        (vstr [s] (Value.vnil)) (vkw [s] (Value.vnil)) (vcons [h t] (Value.vnil)) (vvec [it] (Value.vnil))
        (vmap [en] (vget k en))
        (ventry [ek ev rest] (if (vkeq k ek) ev (vget k rest))) (vfloat [f] (Value.vnil)) (vset [it] (Value.vnil))))

    ;; vgetD — `get` with a DEFAULT: the value at key `k`, or `d` when absent (vnil).
    ;; nil = vnil over the dynamic Value universe — no Option needed; vnil IS the absence.
    (ansatz.core/defn vgetD [k :- Value, m :- Value, d :- Value] Value
      (let [g (vget k m)] (if (vsome? g) g d)))

    ;; ── more native-over-Value map verbs (contains?/keys/vals/dissoc/merge) ──
    ;; contains? — does key k exist in map m? Bool recursion over the entry-chain.
    (ansatz.core/defn vcontains? [k :- Value, m :- Value] Bool
      (match m Value Bool (vnil false) (vbool [b] false) (vint [i] false) (vstr [s] false) (vkw [s] false)
        (vcons [h t] false) (vvec [it] false) (vmap [en] (vcontains? k en))
        (ventry [ek ev rest] (if (vkeq k ek) true (vcontains? k rest))) (vfloat [f] false) (vset [it] false)))

    ;; map-chain extract (entry-chain of a vmap, vnil otherwise).
    (ansatz.core/defn vmap-chain [m :- Value] Value
      (match m Value Value (vnil (Value.vnil)) (vbool [b] (Value.vnil)) (vint [i] (Value.vnil)) (vstr [s] (Value.vnil)) (vkw [s] (Value.vnil))
        (vcons [h t] (Value.vnil)) (vvec [it] (Value.vnil)) (vmap [e] e)
        (ventry [k v r] (Value.vnil)) (vfloat [f] (Value.vnil)) (vset [it] (Value.vnil))))

    ;; keys/vals — collect the entry-chain's keys/values into a vcons chain, wrapped as a vvec.
    (ansatz.core/defn vkeys-chain [c :- Value] Value
      (match c Value Value (vnil (Value.vnil)) (vbool [b] (Value.vnil)) (vint [i] (Value.vnil)) (vstr [s] (Value.vnil)) (vkw [s] (Value.vnil))
        (vcons [h t] (Value.vnil)) (vvec [it] (Value.vnil)) (vmap [e] (Value.vnil))
        (ventry [k v rest] (Value.vcons k (vkeys-chain rest))) (vfloat [f] (Value.vnil)) (vset [it] (Value.vnil))))
    (ansatz.core/defn vkeys [m :- Value] Value (Value.vvec (vkeys-chain (vmap-chain m))))
    (ansatz.core/defn vvals-chain [c :- Value] Value
      (match c Value Value (vnil (Value.vnil)) (vbool [b] (Value.vnil)) (vint [i] (Value.vnil)) (vstr [s] (Value.vnil)) (vkw [s] (Value.vnil))
        (vcons [h t] (Value.vnil)) (vvec [it] (Value.vnil)) (vmap [e] (Value.vnil))
        (ventry [k v rest] (Value.vcons v (vvals-chain rest))) (vfloat [f] (Value.vnil)) (vset [it] (Value.vnil))))
    (ansatz.core/defn vvals [m :- Value] Value (Value.vvec (vvals-chain (vmap-chain m))))

    ;; dissoc — drop key k (rebuild the entry-chain without it). Value-returning recursion.
    (ansatz.core/defn vdissoc-chain [k :- Value, c :- Value] Value
      (match c Value Value (vnil (Value.vnil)) (vbool [b] (Value.vnil)) (vint [i] (Value.vnil)) (vstr [s] (Value.vnil)) (vkw [s] (Value.vnil))
        (vcons [h t] (Value.vnil)) (vvec [it] (Value.vnil)) (vmap [e] (Value.vnil))
        (ventry [ek ev rest] (if (vkeq k ek) (vdissoc-chain k rest) (Value.ventry ek ev (vdissoc-chain k rest)))) (vfloat [f] (Value.vnil)) (vset [it] (Value.vnil))))
    (ansatz.core/defn vdissoc [k :- Value, m :- Value] Value (Value.vmap (vdissoc-chain k (vmap-chain m))))

    ;; merge — b's entries shadow a's (prepend b's chain onto a's, matching Clojure merge).
    (ansatz.core/defn vmerge-chain [src :- Value, dst :- Value] Value
      (match src Value Value (vnil dst) (vbool [b] dst) (vint [i] dst) (vstr [s] dst) (vkw [s] dst)
        (vcons [h t] dst) (vvec [it] dst) (vmap [e] dst)
        (ventry [k v rest] (Value.ventry k v (vmerge-chain rest dst))) (vfloat [f] dst) (vset [it] dst)))
    (ansatz.core/defn vmerge [a :- Value, b :- Value] Value
      (Value.vmap (vmerge-chain (vmap-chain b) (vmap-chain a))))])

(defn install-core!
  "Define the `Value` type and core ops/laws on the current `ansatz.core` env.
   Requires the env to already contain Lean `Init`. Returns the updated env."
  []
  (binding [a/*verbose* false]
    (doseq [form core-forms]
      (eval form)))
  (a/env))

;; ── runtime EDN ↔ Value boundary (#59) ────────────────────────────────────────
;; The runtime representation of `Value` is the general TAGGED inductive rep produced by
;; ansatz.core's codegen: `[cidx field…]`, ctor index first. These mirror that encoding so
;; the kernel-verified conformance predicates / `vget` / `vassoc` RUN on real Clojure data —
;; and can be differential-tested against malli (`m/validate`) and Clojure `get`.
;;
;;   0 vnil · 1 vbool b · 2 vint i · 3 vstr s · 4 vkw s
;;   5 vcons h t · 6 vvec items · 7 vmap entries · 8 ventry k v rest
;;
;; Maps/vectors are entry/cons chains terminated by vnil; map keys keep insertion order, and
;; first occurrence shadows (matching `vassoc` prepend semantics).

(defn edn->value
  "Encode a Clojure EDN value into the runtime `Value` tagged rep."
  [x]
  (cond
    (nil? x)        [0]
    (boolean? x)    [1 x]
    (integer? x)    [2 (long x)]
    (string? x)     [3 x]
    ;; keep the FULL keyword (namespace included): (subs (str :a/b) 1) = "a/b". `value->edn`
    ;; round-trips via (keyword "a/b") = :a/b; (name :a/b) would drop the namespace.
    (keyword? x)    [4 (subs (str x) 1)]
    (double? x)     [9 x]
    (map? x)        [7 (reduce (fn [acc [k v]] [8 (edn->value k) (edn->value v) acc])
                               [0] (reverse (seq x)))]
    (set? x)        [10 (reduce (fn [acc e] [5 (edn->value e) acc])
                                [0] (reverse (seq x)))]
    (sequential? x) [6 (reduce (fn [acc e] [5 (edn->value e) acc])
                               [0] (reverse (seq x)))]
    :else (throw (ex-info "edn->value: unsupported EDN" {:x x :class (class x)}))))

(declare value->edn)

(defn- vchain->seq [c]
  (loop [c c, acc []]
    (case (long (nth c 0))
      0 acc
      5 (recur (nth c 2) (conj acc (value->edn (nth c 1))))
      (throw (ex-info "value->edn: malformed cons chain" {:c c})))))

(defn- ventries->map [c]
  (loop [c c, acc {}]
    (case (long (nth c 0))
      0 acc
      8 (let [k (value->edn (nth c 1)), v (value->edn (nth c 2))]
          ;; head shadows: keep the first occurrence of a key
          (recur (nth c 3) (if (contains? acc k) acc (assoc acc k v))))
      (throw (ex-info "value->edn: malformed entry chain" {:c c})))))

(defn value->edn
  "Decode a runtime `Value` tagged rep back into a Clojure EDN value (inverse of edn->value
   on the canonical encoding; map keys keep first-occurrence/shadowing semantics)."
  [v]
  (case (long (nth v 0))
    0 nil
    1 (nth v 1)
    2 (nth v 1)
    3 (nth v 1)
    4 (keyword (nth v 1))
    5 (vchain->seq v)
    6 (vchain->seq (nth v 1))
    7 (ventries->map (nth v 1))
    8 (throw (ex-info "value->edn: bare ventry has no EDN form" {:v v}))
    9 (nth v 1)
    10 (set (vchain->seq (nth v 1)))))

;; ── typed bridge: dynamic Value ↔ typed record (#62) ──────────────────────────
;; Commit to a malli schema → a `def-record` typed structure (O(1) field projection at
;; runtime, vs vget's O(chain) walk) + the richer relational algebra. `conforms` (#57) is the
;; OPTIONAL boundary that upgrades a dynamic Value to the typed record (gradual: the caller
;; chooses whether to check; not forced). These are the runtime coercions across that boundary.

(defn value->record
  "Upgrade a conforming EDN `Value` (a vmap) to a typed defrecord via its `map->X` factory. After
   this, field access is an O(1) struct projection (not vget's chain walk) and the typed
   relational laws apply. The boundary conforms-check is the caller's choice — see [[malli-value-refinement]]."
  [map->factory v]
  (map->factory (value->edn v)))

(defn record->value
  "Demote a typed defrecord back to a dynamic EDN `Value` (for serialization / the dynamic path)."
  [r]
  (edn->value (into {} r)))

;; ── native-Clojure-over-Value surface (#60) ───────────────────────────────────
;; So existing Clojure code is portable onto dynamic EDN `Value`: native ops lower onto the
;; `v*` primitives when the operand is a `Value`. Keyword access `(:k v)` is handled in
;; ansatz.core; the symbol-headed ops below register elaborators (no core change).


(defn- value-typed? [est ex] (= "Value" (head-name (api/arg-type est ex))))

(defn- const0 [s] (e/const' (name/from-string s) []))

(defn- vkey-expr
  "Surface key as a `Value`: a keyword literal → `(Value.vkw \"k\")`; else assume it already
   elaborates to a Value."
  [est kform]
  (if (keyword? kform)
    (e/app (const0 "Value.vkw") (e/lit-str (kw-str kform)))
    (api/elab est kform)))

(def ^:private surface-preds
  "Clojure predicate symbol → the kernel Value predicate it lowers to (when the operand is a Value)."
  {'int? "vint?" 'integer? "vint?" 'string? "vstr?" 'boolean? "vbool?" 'keyword? "vkw?"
   'nil? "vnil?" 'map? "vmap?" 'vector? "vvec?" 'set? "vset?" 'double? "vfloat?" 'float? "vfloat?"
   'some? "vsome?" 'any? "vany?"})

;; For a NON-Value operand, fall back to core's normal handling (so e.g. `(some? opt)` over an
;; Option still becomes Option.isSome, and unknown predicates error exactly as before). This is
;; what keeps these global registrations side-effect-free for non-EDN code.
(defn- vpred-elaborator [sym vpred]
  (fn [est args]
    (let [v (api/elab est (first args))]
      (if (value-typed? est v)
        (e/app (const0 vpred) v)
        (throw (ex-info (str "`" sym "` is only supported over a dynamic EDN Value in a "
                             "verified body (operand type is not Value)") {:pred sym}))))))

(declare to-value-operand)

(defn- get-elaborator
  "`(get v k)` over a Value → `(vget (Value.vkw k) v)`; `(get v k default)` → `(vgetD … d)`
   (the default returned when the key is absent — nil = vnil over the Value universe).
   Other receivers fall back to core's keyword-projection sugar (get r :k ≡ (:k r))."
  [est args]
  (let [v (api/elab est (first args))]
    (if (value-typed? est v)
      (if (= 3 (count args))
        (e/app* (const0 "vgetD") (vkey-expr est (second args)) v
                (to-value-operand est (api/elab est (nth args 2))))
        (e/app* (const0 "vget") (vkey-expr est (second args)) v))
      (api/elab est (list (second args) (first args))))))

(defn- to-int-operand
  "Coerce a comparison operand to `Int`: a Value via vint-val (0 off-int), a Nat via
   Int.ofNat, an Int as-is; default assumes Value."
  [est x]
  (case (head-name (api/arg-type est x))
    "Nat"   (e/app (const0 "Int.ofNat") x)
    "Int"   x
    (e/app (const0 "vint-val") x)))

(defn- to-value-operand
  "Coerce a comparison operand to `Value` (for structural veq): a literal wraps in its
   Value ctor, a Value stays."
  [est x]
  (case (head-name (api/arg-type est x))
    "Value"  x
    "String" (e/app (const0 "Value.vstr") x)
    "Nat"    (e/app (const0 "Value.vint") (e/app (const0 "Int.ofNat") x))
    "Int"    (e/app (const0 "Value.vint") x)
    "Bool"   (e/app (const0 "Value.vbool") x)
    x))

(defn- value-cmp-handler
  "Type-directed comparison over a dynamic-EDN Value (registered via the comparison seam):
   `<`/`<=` compare the int payloads (Int via vint-val), `==` is structural veq with the
   other operand coerced to a Value."
  [est rel a0 b0]
  (case rel
    (:lt :le) (let [ai (to-int-operand est a0) bi (to-int-operand est b0)
                    propc (if (= rel :lt) "Int.lt" "Int.le")
                    decc  (if (= rel :lt) "Int.decLt" "Int.decLe")]
                (e/app* (const0 "Decidable.decide")
                        (e/app* (const0 propc) ai bi)
                        (e/app* (const0 decc) ai bi)))
    :eq (e/app* (const0 "veq") (to-value-operand est a0) (to-value-operand est b0))))

(defn install-surface!
  "Register native-Clojure-over-Value surface elaborators (get / int?/map?/string?/… +
   keyword access `(:k v)` via the type-directed keyword-access seam). Idempotent;
   safe to call after `install-core!`."
  []
  (a/register-term-elaborator! 'get get-elaborator)
  ;; (:k v) over a Value receiver → (vget (Value.vkw "k") v) — full keyword incl. namespace,
  ;; matching edn->value's key encoding. Registered structures keep native projection;
  ;; this only fires for Value-typed receivers (the seam dispatches on the type head).
  (api/register-keyword-access! "Value"
    (fn [_est kw v-expr]
      (e/app* (const0 "vget") (e/app (const0 "Value.vkw") (e/lit-str (kw-str kw))) v-expr)))
  (api/register-comparison! "Value" value-cmp-handler)
  ;; (when c x) over a Value body → (if c x (Value.vnil)) — nil = vnil. Intercepted as a
  ;; term elaborator (before macroexpansion to a 3-elem if) so the absence is typed vnil.
  (a/register-term-elaborator! 'when
    (fn [est args]
      (let [x (api/elab est (second args))]
        (if (value-typed? est x)
          (api/elab est (list 'if (first args) (second args) '(Value.vnil)))
          (throw (ex-info "when in a verified body is supported over a dynamic EDN Value body (nil = vnil)"
                          {:kind :when-nonvalue}))))))
  ;; (keep f xs) over Value elements → map then drop vnil: (filterv vsome? (mapv f xs)).
  (a/register-term-elaborator! 'keep
    (fn [est args]
      (api/elab est (list 'filterv '(fn [v] (vsome? v)) (list 'mapv (first args) (second args))))))
  ;; map verbs over a dynamic EDN Value: contains?/keys/vals/dissoc/merge lower to the v* ops;
  ;; update/get-in compose existing ops at the surface (no new kernel op).
  (letfn [(value-verb! [sym f]
            (a/register-term-elaborator! sym
              (fn [est args]
                (let [m (api/elab est (first args))]
                  (if (value-typed? est m)
                    (f est m args)
                    (throw (ex-info (str "`" sym "` in a verified body is supported over a dynamic EDN Value")
                                    {:verb sym})))))))]
    (value-verb! 'contains? (fn [est m args] (e/app* (const0 "vcontains?") (vkey-expr est (second args)) m)))
    (value-verb! 'keys      (fn [_est m _args] (e/app (const0 "vkeys") m)))
    (value-verb! 'vals      (fn [_est m _args] (e/app (const0 "vvals") m)))
    (value-verb! 'dissoc    (fn [est m args] (e/app* (const0 "vdissoc") (vkey-expr est (second args)) m)))
    (value-verb! 'merge     (fn [est m args] (e/app* (const0 "vmerge") m (api/elab est (second args)))))
    ;; (update m k f) → (vput m k (f (vget k m)))
    (value-verb! 'update    (fn [est m args]
                              (let [kexpr (vkey-expr est (second args))]
                                (e/app* (const0 "vput") m kexpr
                                        (e/app (api/elab est (nth args 2)) (e/app* (const0 "vget") kexpr m))))))
    ;; (get-in m [k1 k2 …]) → nested vget over a literal key path
    (value-verb! 'get-in    (fn [est m args]
                              (let [path (second args)]
                                (if (vector? path)
                                  (reduce (fn [acc k] (e/app* (const0 "vget") (vkey-expr est k) acc)) m path)
                                  (throw (ex-info "get-in needs a literal key vector over a Value" {:verb 'get-in})))))))
  (doseq [[sym vpred] surface-preds]
    (a/register-term-elaborator! sym (vpred-elaborator sym vpred)))
  :installed)
