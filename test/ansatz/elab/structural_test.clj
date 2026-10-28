(ns ansatz.elab.structural-test
  (:require [clojure.test :refer [deftest is]]
            [ansatz.core :as a]
            [ansatz.config :as config]
            [ansatz.inductive :as ind]
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
          (is (some? (env/lookup (a/env) (name/from-string "structuralNat.match_1"))))
          (is (some? (env/lookup (a/env) (name/from-string "structuralNat.eq_1"))))
          (is (some? (env/lookup (a/env) (name/from-string "structuralNat.eq_2"))))
          (is (not (.contains
                    (e/->string (.type (env/lookup! (a/env) (name/from-string "structuralNat.eq_2"))))
                    "brecOn")))
          (is (empty? (:errors (:equation-generation (meta f))))))
        (let [f (a/define-verified 'structuralNested '[^Nat n] 'Nat
                  '(match n [0 0]
                          [(Nat.succ k)
                           (match k [0 1] [(Nat.succ j) (structuralNested j)])]))]
          (is (= 1 (f 5)))
          (is (some? (env/lookup (a/env) (name/from-string "structuralNested.eq_2"))))
          (is (empty? (:errors (:equation-generation (meta f))))))
        (let [f (a/define-verified 'structuralChanging '[^Nat m ^Nat n] 'Nat
                  '(match n [0 m]
                          [(Nat.succ k) (structuralChanging (Nat.succ m) k)]))]
          (is (= 7 (f 3 4)))
          (is (some? (env/lookup (a/env) (name/from-string "structuralChanging.eq_2")))))
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

(deftest let-wrapped-match-uses-structural-compiler
  (let [saved @a/ansatz-env]
    (try
      (binding [a/*verbose* false] (a/load-init!))
      (let [f (a/define-verified 'wrappedListProbe '[xs :- (List Nat)] 'Nat
                '(let [z 0]
                   (match xs [nil z]
                          [(cons h t) (Nat.succ (wrappedListProbe t))])))]
        (is (= 3 (f '(1 2 3))))
        (is (some? (env/lookup (a/env) (name/from-string "wrappedListProbe.match_1"))))
        (is (some? (env/lookup (a/env) (name/from-string "wrappedListProbe.eq_2"))))
        (is (empty? (:errors (:equation-generation (meta f))))))
      (finally (reset! a/ansatz-env saved)))))

(deftest explicit-ih-shorthand-uses-structural-matcher
  (let [saved @a/ansatz-env]
    (try
      (binding [a/*verbose* false] (a/load-init!))
      (let [f (a/define-verified 'explicitIhLength
                '[xs :- (List Nat)] 'Nat
                '(match xs (List Nat) Nat
                        (nil 0)
                        (cons [hd tl] (Nat.succ ih_tail))))
            ci (env/lookup! (a/env) (name/from-string "explicitIhLength"))]
        (is (= 3 (f '(1 2 3))))
        (is (.contains (e/->string (.value ci)) "List.brecOn"))
        (is (some? (env/lookup (a/env) (name/from-string "explicitIhLength.match_1"))))
        (is (empty? (:errors (:equation-generation (meta f))))))
      (finally (reset! a/ansatz-env saved)))))

(deftest indexed-vector-recursion-has-checked-constructor-equations
  (let [saved @a/ansatz-env]
    (try
      (binding [a/*verbose* false] (a/load-init!))
      (reset! a/ansatz-env
              (ind/define-inductive (a/env) "IndexedLengthVec" '[a Type]
                [['nil [] [0]]
                 ['cons '[n Nat x a xs (IndexedLengthVec a n)] ['(Nat.succ n)]]]
                :indices '[n Nat]))
      (let [f (a/define-verified 'indexedLength
                '[n :- Nat, v :- (IndexedLengthVec Nat n)] 'Nat
                '(match v [nil 0]
                        [(cons k x xs) (Nat.succ (indexedLength k xs))]))]
        (is (= 2 (f 2 [1 17 [0 9 nil]])))
        (is (some? (env/lookup (a/env) (name/from-string "indexedLength.match_1"))))
        (is (some? (env/lookup (a/env) (name/from-string "indexedLength.eq_1"))))
        (is (some? (env/lookup (a/env) (name/from-string "indexedLength.eq_2"))))
        (is (empty? (:errors (:equation-generation (meta f))))))
      (let [f (a/define-verified 'indexedLengthPoly
                '[S :- Type, n :- Nat, v :- (IndexedLengthVec S n)] 'Nat
                '(match v [nil 0]
                        [(cons k x xs) (Nat.succ (indexedLengthPoly S k xs))]))]
        (is (= 2 (f 'Nat 2 [1 17 [0 9 nil]])))
        (is (some? (env/lookup (a/env) (name/from-string "indexedLengthPoly.eq_2"))))
        (is (empty? (:errors (:equation-generation (meta f))))))
      (reset! a/ansatz-env
              (ind/define-inductive (a/env) "TwoIndexedVec" '[a Type]
                [['nil [] [0 0]]
                 ['cons '[n Nat m Nat x a xs (TwoIndexedVec a n m)]
                  ['(Nat.succ n) '(Nat.succ m)]]]
                :indices '[n Nat m Nat]))
      (let [f (a/define-verified 'twoIndexedLength
                '[n :- Nat, m :- Nat, v :- (TwoIndexedVec Nat n m)] 'Nat
                '(match v [nil 0]
                        [(cons k l x xs) (Nat.succ (twoIndexedLength k l xs))]))]
        (is (= 2 (f 2 2 [1 1 17 [0 0 9 nil]])))
        (is (some? (env/lookup (a/env) (name/from-string "twoIndexedLength.eq_1"))))
        (is (some? (env/lookup (a/env) (name/from-string "twoIndexedLength.eq_2"))))
        (is (empty? (:errors (:equation-generation (meta f))))))
      (finally (reset! a/ansatz-env saved)))))

(deftest dependent-index-types-use-structural-matcher
  (let [saved @a/ansatz-env]
    (try
      (binding [a/*verbose* false] (a/load-init!))
      (reset! a/ansatz-env
              (ind/define-inductive (a/env) "StructuralFin" '[]
                [['zero '[n Nat] ['(Nat.succ n)]]
                 ['succ '[n Nat i (StructuralFin n)] ['(Nat.succ n)]]]
                :indices '[n Nat]))
      (reset! a/ansatz-env
              (ind/define-inductive (a/env) "DependentIndexVec" '[]
                [['nil [] [0 '(StructuralFin.zero 0)]]
                 ['cons '[n Nat i (StructuralFin (Nat.succ n))
                          xs (DependentIndexVec n i)]
                  ['(Nat.succ n) '(StructuralFin.succ (Nat.succ n) i)]]]
                :indices '[n Nat i (StructuralFin (Nat.succ n))]))
      (let [f (a/define-verified 'dependentIndexLength
                '[n :- Nat, i :- (StructuralFin (Nat.succ n))
                  v :- (DependentIndexVec n i)] 'Nat
                '(match v [nil 0]
                        [(cons k j xs) (Nat.succ (dependentIndexLength k j xs))]))]
        (is (= 2 (f 2 nil [1 nil [0 nil nil]])))
        (is (some? (env/lookup (a/env) (name/from-string "dependentIndexLength.match_1"))))
        (is (some? (env/lookup (a/env) (name/from-string "dependentIndexLength.eq_1"))))
        (is (some? (env/lookup (a/env) (name/from-string "dependentIndexLength.eq_2"))))
        (is (empty? (:errors (:equation-generation (meta f))))))
      (let [f (a/define-verified 'dependentIndexLengthExtra
                '[n :- Nat, i :- (StructuralFin (Nat.succ n))
                  v :- (DependentIndexVec n i)
                  t :- (StructuralFin (Nat.succ n))] 'Nat
                '(match v [nil 0]
                        [(cons k j xs)
                         (Nat.succ (dependentIndexLengthExtra k j xs j))]))]
        (is (= 2 (f 2 nil [1 nil [0 nil nil]] nil)))
        (is (some? (env/lookup (a/env) (name/from-string "dependentIndexLengthExtra.eq_1"))))
        (is (some? (env/lookup (a/env) (name/from-string "dependentIndexLengthExtra.eq_2"))))
        (is (empty? (:errors (:equation-generation (meta f))))))
      (finally (reset! a/ansatz-env saved)))))

(deftest enclosing-forms-can-contain-the-structural-match
  (let [saved @a/ansatz-env]
    (try
      (binding [a/*verbose* false] (a/load-init!))
      (let [f (a/define-verified 'wrappedIfRec
                '[flag :- Bool, n :- Nat] 'Nat
                '(if flag
                   (match n [0 0]
                          [(Nat.succ k) (Nat.succ (wrappedIfRec flag k))])
                   0))]
        (is (= 3 (f true 3)))
        (is (= 0 (f false 3)))
        (is (some? (env/lookup (a/env) (name/from-string "wrappedIfRec.match_1"))))
        (is (some? (env/lookup (a/env) (name/from-string "wrappedIfRec.eq_1"))))
        (is (empty? (:errors (:equation-generation (meta f))))))
      (let [f (a/define-verified 'outerMatchRec
                '[flag :- Bool, n :- Nat] 'Nat
                '(match flag
                   [true (match n [0 0]
                                [(Nat.succ k) (Nat.succ (outerMatchRec flag k))])]
                   [false 0]))]
        (is (= 3 (f true 3)))
        (is (= 0 (f false 3)))
        (is (some? (env/lookup (a/env) (name/from-string "outerMatchRec.eq_1"))))
        (is (empty? (:errors (:equation-generation (meta f))))))
      (finally (reset! a/ansatz-env saved)))))

(deftest structural-compiler-tries-later-matched-argument
  (let [saved @a/ansatz-env]
    (try
      (binding [a/*verbose* false] (a/load-init!))
      (let [f (a/define-verified 'trySecondArgRec
                '[m :- Nat, n :- Nat] 'Nat
                '(match m
                   [0 (match n [0 m]
                             [(Nat.succ k) (trySecondArgRec (Nat.succ m) k)])]
                   [(Nat.succ j)
                    (match n [0 m]
                           [(Nat.succ k) (trySecondArgRec (Nat.succ m) k)])]))]
        (is (= 3 (f 0 3)))
        (is (= 5 (f 2 3)))
        (is (some? (env/lookup (a/env) (name/from-string "trySecondArgRec.match_1"))))
        (is (some? (env/lookup (a/env) (name/from-string "trySecondArgRec.eq_1"))))
        (is (empty? (:errors (:equation-generation (meta f))))))
      (finally (reset! a/ansatz-env saved)))))

(deftest unchanged-noninductive-parameters-stay-outside-motive
  (let [saved @a/ansatz-env]
    (try
      (binding [a/*verbose* false] (a/load-init!))
      (let [f (a/define-verified 'fixedFlagRec
                '[flag :- Bool, m :- Nat, n :- Nat] 'Nat
                '(match n [0 m]
                        [(Nat.succ k) (fixedFlagRec flag (Nat.succ m) k)]))
            ci (env/lookup! (a/env) (name/from-string "fixedFlagRec"))]
        (is (= 7 (f true 3 4)))
        (is (= 7 (f false 3 4)))
        (is (.contains (e/->string (.value ci))
                       "Nat.brecOn.{1} (fun : Nat => (∀ : Nat, Nat))"))
        (is (some? (env/lookup (a/env) (name/from-string "fixedFlagRec.eq_2"))))
        (is (empty? (:errors (:equation-generation (meta f))))))
      (finally (reset! a/ansatz-env saved)))))

(deftest nested-comparison-match-generalizes-with-elaboration-metavariables
  (let [saved @a/ansatz-env]
    (try
      (binding [a/*verbose* false] (a/load-init!))
      (let [f (a/define-verified 'nestedCmpRec '[n :- Nat, k :- Nat] 'Bool
                '(match n [0 false]
                        [(Nat.succ j)
                         (match (< k j)
                           [true (nestedCmpRec j k)]
                           [false (match (== k j)
                                    [true true]
                                    [false false])])]))]
        (is (true? (f 4 1)))
        (is (false? (f 1 2)))
        (is (some? (env/lookup (a/env) (name/from-string "nestedCmpRec.match_1"))))
        (is (empty? (:errors (:equation-generation (meta f))))))
      (finally (reset! a/ansatz-env saved)))))
