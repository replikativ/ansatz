(ns ansatz.meta.match.simp-h
  "The constructor part of Lean/Meta/Match/SimpH.lean. A precedence condition
   says that a later alternative cannot match an earlier one."
  (:require [ansatz.kernel.expr :as e]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.tc :as tc]
            [ansatz.meta.constructions.util :as u]))

(defn- constructor-app [environment expr]
  (let [[h args] (e/get-app-fn-args expr)
        ci (when (e/const? h) (env/lookup environment (e/const-name h)))
        nat-value (cond
                    (e/lit-nat? expr) (e/lit-nat-val expr)
                    (and (e/const? h) (= "OfNat.ofNat" (name/->string (e/const-name h)))
                         (= 3 (count args))
                         (e/const? (first args))
                         (= "Nat" (name/->string (e/const-name (first args))))
                         (e/lit-nat? (nth args 1)))
                    (e/lit-nat-val (nth args 1)))]
    (cond
      (some? nat-value)
      (if (zero? nat-value)
        {:name (name/from-string "Nat.zero") :fields []}
        {:name (name/from-string "Nat.succ")
         :fields [(e/lit-nat (dec nat-value))]})
      (and ci (.isCtor ci))
      {:name (e/const-name h)
       :fields (subvec (vec args) (.numParams ci))})))

(defn- pattern-equalities [environment lhs rhs]
  (let [a (constructor-app environment lhs)
        b (constructor-app environment rhs)]
    (cond
      (and a b (not= (:name a) (:name b))) nil
      (and a b (= (:name a) (:name b))
           (= (count (:fields a)) (count (:fields b))))
      (reduce (fn [acc [x y]]
                (when acc (when-let [more (pattern-equalities environment x y)]
                            (into acc more))))
              [] (map vector (:fields a) (:fields b)))
      :else [[lhs rhs]])))

(defn not-alt
  "Instantiate Lean's mkNotAlt at current-patterns, then simplify constructor
   equalities as simpH? does. prior-fields are local declarations in order.
   nil means the patterns have distinct constructors and need no guard."
  [environment lctx current-patterns prior-patterns prior-fields]
  (let [lctx (reduce (fn [lc d] (assoc lc (:id d) d)) lctx prior-fields)
        ctx (atom (tc/attach-lctx (tc/mk-tc-state environment) lctx))
        pairs (reduce (fn [acc [x y]]
                        (when acc (when-let [more (pattern-equalities environment x y)]
                                    (into acc more))))
                      [] (map vector current-patterns prior-patterns))]
    (when pairs
      (let [equalities (mapv #(u/mk-eq-heq ctx (first %) (second %)) pairs)
            impossible (reduce (fn [body eq] (e/arrow eq body))
                               (e/const' (name/from-string "False") [])
                               (reverse equalities))
            field-fvars (mapv (comp e/fvar :id) prior-fields)]
        (u/mk-forall-fvars ctx field-fvars impossible)))))
