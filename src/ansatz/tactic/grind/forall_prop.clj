(ns ansatz.tactic.grind.forall-prop
  "Lean/Meta/Tactic/Grind/ForallProp.lean, checkout v4.33.1:
   propagateForallPropDown and propagateExistsDown, with checked Init proof terms."
  (:require [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.tc :as tc]
            [ansatz.tactic.grind.theorem :as theorem]))

(defn- c [n] (e/const' (name/from-string n) []))
(defn- app [n & args] (reduce e/app (c n) args))
(defn- neg [p] (e/app (c "Not") p))
(defn- lambda [st type f]
  (let [id (swap! (:next-id st) inc)]
    (e/lam "h" type (e/abstract1 (f (e/fvar id)) id) :default)))
(defn- by-contradiction [p h]
  (app "Decidable.byContradiction" p (app "Classical.propDecidable" p) h))
(defn- sort-level [st alpha]
  (e/sort-level (#'tc/cached-whnf st (tc/infer-type st alpha))))
(defn- apply-predicate [predicate x]
  (if (e/lam? predicate) (e/instantiate1 (e/lam-body predicate) x) (e/app predicate x)))

(defn eq-false-of-imp-eq-true
  "ForallProp.propagateForallPropUp/Down: (a -> b), not b entail not a.
   Build the exported primitives behind Grind.eq_false_of_imp_eq_true."
  [st imp hp hnb gen]
  (when (and (e/forall? imp) (zero? (e/bvar-range (e/forall-body imp)))
             (theorem/prop? st (e/forall-type imp)))
    (let [a (e/forall-type imp)]
      {:prop (neg a) :proof (lambda st a #(e/app hnb (e/app hp %))) :gen gen})))

(defn propagate-forall-prop-down
  "Refuted data/dependent forall -> existential counterexample, at the same generation."
  [st prop hn gen]
  (when (and (e/forall? prop)
             (or (pos? (e/bvar-range (e/forall-body prop)))
                 (not (theorem/prop? st (e/forall-type prop)))))
    (let [alpha (e/forall-type prop) body (e/forall-body prop)
          u (sort-level st alpha)
          predicate (e/lam (e/forall-name prop) alpha (neg body) (e/forall-info prop))
          exists (e/app* (e/const' (name/from-string "Exists") [u]) alpha predicate)
          ;; Bundled Init does not export Grind.of_forall_eq_false. Construct its
          ;; ordinary classical proof; no new axiom or unverified declaration.
          proof (by-contradiction
                 exists
                 (lambda st (neg exists)
                         (fn [hne]
                           (e/app hn
                                  (lambda st alpha
                                          (fn [x]
                                            (let [px (e/instantiate1 body x)]
                                              (by-contradiction
                                               px
                                               (lambda st (neg px)
                                                       (fn [hnpx]
                                                         (e/app hne
                                                                (e/app* (e/const' (name/from-string "Exists.intro") [u])
                                                                        alpha predicate x hnpx))))))))))))]
      {:prop exists :proof proof :gen gen})))

(defn propagate-exists-down
  "Refuted Exists -> forall not (ForallProp.lean propagateExistsDown, headBeta)."
  [st prop hn gen]
  (let [[head args] (e/get-app-fn-args prop)]
    (when (and (e/const? head) (= "Exists" (name/->string (e/const-name head))) (= 2 (count args)))
      (let [[alpha predicate] args u (sort-level st alpha)
            result (e/forall' "x" alpha (neg (apply-predicate predicate (e/bvar 0))) :default)
            ;; forall_not_of_not_exists is also absent from the bundled export.
            proof (lambda st alpha
                          (fn [x]
                            (lambda st (apply-predicate predicate x)
                                    (fn [hp]
                                      (e/app hn (e/app* (e/const' (name/from-string "Exists.intro") [u])
                                                       alpha predicate x hp))))))]
        {:prop result :proof proof :gen gen}))))
