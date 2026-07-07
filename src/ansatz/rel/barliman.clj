;; Barliman-over-Clojure: fill holes in everyday surface syntax by measurable
;; relational search, kernel-certified. A thin toolkit over ansatz.rel + the
;; surface elaborator, whose holes (`?x`, `_`) already elaborate to typed
;; kernel metavariables.
(ns ansatz.rel.barliman
  (:require [ansatz.rel :as r]
            [ansatz.surface.elaborate :as elab]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as nm]))

(def NAT (e/const' (nm/from-string "Nat") []))
(def BOOL (e/const' (nm/from-string "Bool") []))

(defn arrows
  "Right-associated function type A → B → … → R."
  [& ts]
  (reduce (fn [acc t] (e/arrow t acc)) (last ts) (reverse (butlast ts))))

(defn lit [n] (e/lit-nat n))
(defn cst [s] (e/const' (nm/from-string s) []))
(defn ap [f & args] (reduce e/app f args))

(defn from-surface
  "Elaborate surface `sexpr` (which may contain `?holes`) against `expected`;
   return a rel search state seeded with the elaboration metacontext, plus the
   whole expr and the hole mvars (occurrence order).

   The surface elaborator turns `?x` into a real (synthetic-opaque) metavariable
   whose type is inferred bidirectionally — so the returned holes are exactly
   the search variables, already typed by the surrounding code."
  [env sexpr expected & {:keys [lctx]}]
  (let [{:keys [expr holes meta-mctx]} (elab/elaborate-collecting env sexpr expected)
        st (r/state env :mctx meta-mctx :lctx (or lctx {})
                    :next-id (max 90000000 (long (:mvar-counter meta-mctx 0))))]
    {:state st :expr expr :holes (mapv :expr holes)
     :hole1 (:expr (first holes))}))

;; --- generators: proposal distributions over hole fillings ---
;; They fill a (synthetic-opaque) surface hole via `assigno` (the exact/tactic
;; path), since `===` refuses to unify an opaque goal away.

(defn nat-lito
  "?x ranges over Nat literals 0..n, small values preferred (prior ∝ 1/(i+1))."
  [x n]
  (apply r/condw
         (for [i (range (inc n))]
           [(/ 1.0 (inc i)) (r/assigno x (lit i))])))

(defn oneofo
  "?x ranges over an explicit candidate set (uniform prior)."
  [x candidates]
  (apply r/condw (for [c candidates] [1 (r/assigno x c)])))
