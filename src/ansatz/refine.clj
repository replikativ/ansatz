(ns ansatz.refine
  "A2 — read refinement FACTS back out of a kernel type `Expr`, for the planner / refinement-fact
   lattice. This is the read-side inverse of `ansatz.malli/schema->type-expr`'s refinement encoding:
   given a type, recover the structured facts the optimizer can gate rewrites on — the decoded
   numeric range of a `Subtype Nat`, the inner type of an `Option`/`List`, the components of a
   `Prod`, and (once the structure-preserving functor lands) the key/uniqueness fact of a refined
   relation carrier.

   Pure, env-free, syntactic on the elaborated `Expr` — the planner asks \"what does this term's
   TYPE already prove?\" and gets a fact map, not an opaque predicate. The refinement PROOF that a
   value carries (a `Subtype`'s `.property`) is recovered separately at the rewrite site via the
   carrier's projection; this namespace recovers the *shape* of the fact so a gate can branch on it."
  (:require [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]))

(defn- cname [x] (when (e/const? x) (name/->string (e/const-name x))))
(defn- const-named? [x s] (= (cname x) s))
(defn- nat-lit-of [x] (when (e/lit-nat? x) (long (e/lit-nat-val x))))

;; ── Subtype-Nat range decode ────────────────────────────────────────────────────────────────
;; Decode one atomic bound conjunct over the refinement var `(bvar 0)`, the inverse of
;; ansatz.malli/bound-prop:
;;   (LE.le Nat _ (lit k) (bvar))  k ≤ v  → {:min k}
;;   (LE.le Nat _ (bvar) (lit m))  v ≤ m  → {:max m}
;;   (LT.lt Nat _ (bvar) (lit m))  v < m  → {:max (dec m)}
;;   (LT.lt Nat _ (lit k) (bvar))  k < v  → {:min (inc k)}
(defn- decode-bound [b]
  (let [[h args] (e/get-app-fn-args b)
        lhs (nth args 2 nil) rhs (nth args 3 nil)]
    (case (cname h)
      "LE.le" (cond (and (nat-lit-of lhs) (e/bvar? rhs)) {:min (nat-lit-of lhs)}
                    (and (e/bvar? lhs) (nat-lit-of rhs)) {:max (nat-lit-of rhs)}
                    :else nil)
      "LT.lt" (cond (and (e/bvar? lhs) (nat-lit-of rhs)) {:max (dec (nat-lit-of rhs))}
                    (and (nat-lit-of lhs) (e/bvar? rhs)) {:min (inc (nat-lit-of lhs))}
                    :else nil)
      nil)))

(defn- decode-range-body
  "A `Subtype` predicate body is a single bound or `(And lo hi)`; recover {:min :max} (partial)."
  [body]
  (let [[h args] (e/get-app-fn-args body)]
    (if (const-named? h "And")
      (merge (decode-bound (nth args 0 nil)) (decode-bound (nth args 1 nil)))
      (decode-bound body))))

;; ── the public fact extractor ───────────────────────────────────────────────────────────────
(defn type-facts
  "Structured refinement facts carried by a kernel type `Expr` `ty`. Returns a map with `:kind`:
     :subtype {:base :pred [:range {:min :max}]}  — a `Subtype B p`; `:range` present when `p`
                                                    decodes to Nat lower/upper bounds.
     :option  {:inner}                            — `Option T`.
     :list    {:elem}                             — `List T`.
     :prod    {:fst :snd}                         — `Prod A B`.
     :opaque  {:type}                             — anything else (no refinement to read).
   Never throws; an unrecognized shape is `:opaque`."
  [ty]
  (let [[h args] (e/get-app-fn-args ty)]
    (case (cname h)
      "Subtype" (let [pred (nth args 1 nil)
                      rng  (when (e/lam? pred) (decode-range-body (e/lam-body pred)))]
                  (cond-> {:kind :subtype :base (nth args 0 nil) :pred pred}
                    (seq rng) (assoc :range rng)))
      "Option"  {:kind :option :inner (nth args 0 nil)}
      "List"    {:kind :list   :elem  (nth args 0 nil)}
      "Prod"    {:kind :prod   :fst   (nth args 0 nil) :snd (nth args 1 nil)}
      {:kind :opaque :type ty})))

(defn nat-range
  "The decoded {:min :max} (either bound optional) of a `Subtype Nat …` type, else nil.
   The planner's selectivity hook reads this to turn a comparator guess into a sound bound."
  [ty]
  (let [f (type-facts ty)]
    (when (and (= :subtype (:kind f)) (const-named? (:base f) "Nat") (:range f))
      (:range f))))

(defn refinement-pred
  "The raw refinement predicate `Expr` (`λ v. P v`) of a `Subtype`, else nil — for a gate that
   needs to discharge `P` as a filter-elimination obligation rather than read a numeric range."
  [ty]
  (let [f (type-facts ty)]
    (when (= :subtype (:kind f)) (:pred f))))
