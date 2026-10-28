(ns ansatz.elab.structural-test
  (:require [clojure.test :refer [deftest is]]
            [ansatz.core :as a]
            [ansatz.config :as config]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]))

(deftest recursive-matcher-brecon-is-kernel-checked-and-runs
  (let [saved @a/ansatz-env]
    (try
      (binding [a/*verbose* false] (a/load-init!))
      (binding [config/*lean-structural-matchers* true]
        (let [f (a/define-verified 'structuralNat '[^Nat n] 'Nat
                  '(match n [0 0] [(Nat.succ k) (Nat.succ (structuralNat k))]))
              ci (env/lookup! (a/env) (name/from-string "structuralNat"))]
          (is (= 4 (f 4)))
          (is (.contains (e/->string (.value ci)) "Nat.brecOn"))
          (is (some? (env/lookup (a/env) (name/from-string "structuralNat.match_1")))))
        (let [f (a/define-verified 'structuralNested '[^Nat n] 'Nat
                  '(match n [0 0]
                          [(Nat.succ k)
                           (match k [0 1] [(Nat.succ j) (structuralNested j)])]))]
          (is (= 1 (f 5))))
        (let [f (a/define-verified 'structuralChanging '[^Nat m ^Nat n] 'Nat
                  '(match n [0 m]
                          [(Nat.succ k) (structuralChanging (Nat.succ m) k)]))]
          (is (= 7 (f 3 4))))
        (let [f (a/define-verified 'structuralPoly '[S :- Type, xs :- (List S)] 'Nat
                  '(match xs [nil 0]
                          [(List.cons h t) (Nat.succ (structuralPoly S t))]))]
          (is (= 3 (f 'Nat '(1 2 3)))))
        (let [f (a/define-verified 'structuralScrutinee '[^Nat n] 'Nat
                  '(match n [0 0]
                          [(Nat.succ k)
                           (match (structuralScrutinee k)
                             [0 1] [(Nat.succ j) j])]))]
          (is (= 0 (f 4))))
        (let [f (a/define-verified 'structuralLet '[^Nat n] 'Nat
                  '(match n [0 0]
                          [(Nat.succ k)
                           (let [x (structuralLet k)] (Nat.succ x))]))]
          (is (= 4 (f 4)))))
      (finally (reset! a/ansatz-env saved)))))
