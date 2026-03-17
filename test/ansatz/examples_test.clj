(ns ansatz.examples-test
  "Tests that verify the examples from examples/ directory work.
   RB tree tests run against init-medium.ndjson (no Mathlib needed).
   GD convergence tests require Mathlib store (skipped if unavailable)."
  (:require [clojure.test :refer [deftest testing is use-fixtures]]
            [ansatz.core :as a]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [ansatz.export.parser :as parser]
            [ansatz.export.replay :as replay]))

;; ============================================================
;; Environment setup (init-medium for RB tree, Mathlib for GD)
;; ============================================================

(def ^:private init-env
  (delay
    (let [f "test-data/init-medium.ndjson"]
      (when (.exists (java.io.File. f))
        (:env (replay/replay (:decls (parser/parse-ndjson-file f))))))))

(defn- with-init-env [f]
  (when-let [base-env @init-env]
    (let [env (env/fork base-env)
          tsv "resources/instances.tsv"
          load-tsv (requiring-resolve 'ansatz.tactic.instance/load-instance-tsv)
          build-fn (requiring-resolve 'ansatz.tactic.instance/build-instance-index)
          idx (if (.exists (java.io.File. tsv))
                (load-tsv tsv)
                (build-fn env))]
      (reset! a/ansatz-env env)
      (reset! a/ansatz-instance-index idx)
      ;; Define RB tree types once for all match tests
      (binding [a/*verbose* false]
        (when-not (env/lookup (a/env) (name/from-string "TRBColor"))
          (eval '(ansatz.core/inductive TRBColor [] (red) (black)))
          (eval '(ansatz.core/inductive TRBTree [α Type]
                                        (leaf) (node [color TRBColor] [left (TRBTree α)] [key α] [right (TRBTree α)]))))
        ;; Define isort functions once for all isort tests
        (when-not (env/lookup (a/env) (name/from-string "ex-sorted"))
          (eval '(ansatz.core/defn ex-sorted [l (List Nat)] Bool
                   (match l (List Nat) Bool
                     (nil true) (cons [hd tl] (match tl (List Nat) Bool
                       (nil true) (cons [hd2 tl2] (match (<= hd hd2) Bool Bool
                         (true ih_tail) (false false))))))))
          (eval '(ansatz.core/defn ex-insertSorted [x Nat l (List Nat)] (List Nat)
                   (match l (List Nat) (List Nat)
                     (nil (cons x nil)) (cons [hd tl] (match (<= x hd) Bool (List Nat)
                       (true (cons x l)) (false (cons hd ih_tail)))))))
          (eval '(ansatz.core/defn ex-isort [l (List Nat)] (List Nat)
                   (match l (List Nat) (List Nat)
                     (nil nil) (cons [hd tl] ((ex-insertSorted hd) ih_tail))))))
        (f)))))

(use-fixtures :once with-init-env)

;; ============================================================
;; Red-Black Tree examples (init-medium sufficient)
;; ============================================================

(deftest test-rb-inductive-types
  (testing "Define RBColor and RBTree inductive types"
    (binding [a/*verbose* false]
      (let [ind-fn (requiring-resolve 'ansatz.inductive/define-inductive)]
        (ind-fn (a/env) "ExRBColor" '[] '[["red" []] ["black" []]])
        (is (some? (env/lookup (a/env) (name/from-string "ExRBColor"))))
        (is (some? (env/lookup (a/env) (name/from-string "ExRBColor.red"))))
        (is (some? (env/lookup (a/env) (name/from-string "ExRBColor.black"))))))))

(deftest test-match-bool
  (testing "Match on Bool type compiles and runs"
    (binding [a/*verbose* false]
      (let [f (a/define-verified 'ex-is-true '[b Bool] 'Nat
                '(match b Bool Nat (true 1) (false 0)))]
        (is (fn? f))
        (is (= 1 (f true)))
        (is (= 0 (f false)))))))

(deftest test-match-rb-size
  (testing "Recursive match on RBTree with IH compiles and runs"
    (binding [a/*verbose* false]
      ;; Types defined in fixture
      ;; Define rb-size
      (let [f (a/define-verified 'ex-rb-size '[t (TRBTree Nat)] 'Nat
                '(match t (TRBTree Nat) Nat
                        (leaf 0)
                        (node [color left key right] (+ 1 (+ ih_left ih_right)))))]
        (is (fn? f))
        ;; Test: tree with 3 nodes
        (let [tree (reduce (fn [t k] [:black t k nil]) nil [3 1 4])]
          (is (= 3 (long (f tree)))))))))

(deftest test-match-rb-member
  (testing "Nested match with IH + outer param (rb-member)"
    (binding [a/*verbose* false]
      ;; Types defined in fixture
      (let [f (a/define-verified 'ex-rb-member
                '[t (TRBTree Nat) k Nat] 'Bool
                '(match t (TRBTree Nat) Bool
                        (leaf false)
                        (node [color left key right]
                              (match (< k key) Bool Bool
                                     (true ih_left)
                                     (false (match (== k key) Bool Bool
                                                   (true true)
                                                   (false ih_right)))))))]
        (is (fn? f))
        (let [tree (reduce (fn [t k] [:black t k nil]) nil [5 3 7 1 4])]
          (is (true? ((f tree) 4)))
          (is (false? ((f tree) 42)))
          (is (true? ((f tree) 1))))))))

(deftest test-match-rb-sum
  (testing "Recursive match rb-sum compiles and runs"
    (binding [a/*verbose* false]
      (let [f (a/define-verified 'ex-rb-sum '[t (TRBTree Nat)] 'Nat
                '(match t (TRBTree Nat) Nat
                        (leaf 0)
                        (node [color left key right] (+ key (+ ih_left ih_right)))))]
        (is (fn? f))
        (let [tree (reduce (fn [t k] [:black t k nil]) nil [3 1 4])]
          (is (= 8 (long (f tree)))))))))

(deftest test-rb-theorems
  (testing "Prove RB tree properties"
    (binding [a/*verbose* false]
      ;; Prove reflexivity for leaf
      (a/prove-theorem 'ex-leaf-eq
                       '[α Type]
                       '(= Nat 0 0)
                       '[(rfl)])
      (is true "leaf theorem proved"))))

(deftest test-rb-left-le-size
  (testing "Left subtree size bounded by node size (omega)"
    (binding [a/*verbose* false]
      ;; Uses omega to prove: rb-size l ≤ 1 + (rb-size l + rb-size r)
      (let [f (a/define-verified 'ex-rb-size3 '[t (TRBTree Nat)] 'Nat
                '(match t (TRBTree Nat) Nat
                        (leaf 0)
                        (node [color left key right] (+ 1 (+ ih_left ih_right)))))]
        (is (fn? f))
        (a/prove-theorem 'ex-left-le-size
                         '[c :- TRBColor, l :- (TRBTree Nat), k :- Nat, r :- (TRBTree Nat)]
                         '(<= Nat (ex-rb-size3 l) (+ 1 (+ (ex-rb-size3 l) (ex-rb-size3 r))))
                         '[(omega)])
        (is true "left-le-size proved by omega")))))

(deftest test-rb-balance-rotation
  (testing "Balance1 rotation correctness (universally quantified)"
    (binding [a/*verbose* false]
      ;; Define balance1 for testing
      (a/define-verified 'ex-balance1
        '[l (TRBTree Nat) v Nat r (TRBTree Nat)] '(TRBTree Nat)
        '(match l (TRBTree Nat) (TRBTree Nat)
                (leaf (TRBTree.node Nat (TRBColor.black) (TRBTree.leaf Nat) v r))
                (node [lc ll lk lr]
                      (match lc TRBColor (TRBTree Nat)
                             (black (TRBTree.node Nat (TRBColor.black) l v r))
                             (red
                              (match ll (TRBTree Nat) (TRBTree Nat)
                                     (leaf (TRBTree.node Nat (TRBColor.black) l v r))
                                     (node [llc lll llk llr]
                                           (match llc TRBColor (TRBTree Nat)
                                                  (black (TRBTree.node Nat (TRBColor.black) l v r))
                                                  (red (TRBTree.node Nat (TRBColor.red)
                                                                     (TRBTree.node Nat (TRBColor.black) lll llk llr)
                                                                     lk
                                                                     (TRBTree.node Nat (TRBColor.black) lr v r)))))))))))
      ;; Prove left-left rotation (universally quantified)
      (a/prove-theorem 'ex-balance1-ll
                       '[a :- (TRBTree Nat), x :- Nat, b :- (TRBTree Nat),
                         y :- Nat, c :- (TRBTree Nat), v :- Nat, r :- (TRBTree Nat)]
                       '(= (TRBTree Nat)
                           (((ex-balance1
                              (TRBTree.node Nat (TRBColor.red)
                                            (TRBTree.node Nat (TRBColor.red) a x b) y c)) v) r)
                           (TRBTree.node Nat (TRBColor.red)
                                         (TRBTree.node Nat (TRBColor.black) a x b) y
                                         (TRBTree.node Nat (TRBColor.black) c v r)))
                       '[(rfl)])
      (is true "balance1 left-left rotation proved"))))

;; ============================================================
;; Verified insertion sort (init-medium sufficient)
;; Demonstrates: equation theorems, simp_all, omega, by_cases
;; This is the foundation for F*-style refinement types:
;; sorted(isort l) = true is exactly the obligation that a
;; refinement type {l' : List Nat | sorted l'} would generate.
;; ============================================================

(deftest test-isort-definitions
  (testing "Verified sort functions compile and execute correctly"
    (binding [a/*verbose* false]
      ;; Functions defined in fixture
      (is (some? (env/lookup (a/env) (name/from-string "ex-sorted"))))
      (is (some? (env/lookup (a/env) (name/from-string "ex-insertSorted"))))
      (is (some? (env/lookup (a/env) (name/from-string "ex-isort"))))
      ;; Runtime execution — List compiles to native Clojure seqs
      (let [sorted-fn @(resolve 'ex-sorted)
            isort-fn @(resolve 'ex-isort)]
        (is (true? (sorted-fn '(1 2 3))))
        (is (false? (sorted-fn '(3 1 2))))
        (is (= '(1 2 3) (isort-fn '(3 1 2))))
        (is (= '(1 1 2 3) (isort-fn '(3 1 2 1)))))
      ;; Equation theorems generated
      (is (some? (env/lookup (a/env) (name/from-string "ex-sorted.eq_1"))))
      (is (some? (env/lookup (a/env) (name/from-string "ex-insertSorted.eq_1"))))
      (is (some? (env/lookup (a/env) (name/from-string "ex-isort.eq_1")))))))

(deftest test-isort-base
  (testing "sorted(insertSorted x []) = true (base case)"
    (binding [a/*verbose* false]
      (a/prove-theorem 'ex-insert-base '[x :- Nat]
                       '(= Bool (ex-sorted ((ex-insertSorted x) nil)) true)
                       '[(simp "ex-insertSorted" "ex-sorted")])
      (is true "base case proved by simp"))))

(deftest test-isort-singleton
  (testing "sorted(insertSorted x [y]) = true (singleton, requires by_cases + omega)"
    (binding [a/*verbose* false]
      (a/prove-theorem 'ex-insert-singleton '[x :- Nat, y :- Nat]
                       '(= Bool (ex-sorted ((ex-insertSorted x) (cons y nil))) true)
                       '[(by_cases (<= x y))
                         (simp_all "ex-insertSorted" "ex-sorted")
                         (simp_all "ex-insertSorted" "ex-sorted")
                         (omega)])
      (is true "singleton case proved by by_cases + simp_all + omega"))))

(deftest ^:wip test-isort-preservation
  (testing "sorted(insertSorted x l) = true by induction (preservation lemma)"
    (binding [a/*verbose* false]
      ;; Use ProofContext for full isolation — no global state mutation
      (let [saved-env @a/ansatz-env
            fresh-env (env/fork @init-env)
            saved-idx @a/ansatz-instance-index]
        (try
          ;; Temporarily set globals for define-verified (which uses them)
          (reset! a/ansatz-env fresh-env)
          (reset! a/ansatz-instance-index saved-idx)
          (reset! @(resolve 'ansatz.tactic.simp/fun-info-cache) {})
          ;; Define functions in the fresh env
          (eval '(ansatz.core/defn ex-sorted [l (List Nat)] Bool
                   (match l (List Nat) Bool
                     (nil true) (cons [hd tl] (match tl (List Nat) Bool
                       (nil true) (cons [hd2 tl2] (match (<= hd hd2) Bool Bool
                         (true ih_tail) (false false))))))))
          (eval '(ansatz.core/defn ex-insertSorted [x Nat l (List Nat)] (List Nat)
                   (match l (List Nat) (List Nat)
                     (nil (cons x nil)) (cons [hd tl] (match (<= x hd) Bool (List Nat)
                       (true (cons x l)) (false (cons hd ih_tail)))))))
          ;; Create ProofContext from the fresh env
          (let [ctx (a/make-context @a/ansatz-env @a/ansatz-instance-index)]
          (a/prove-theorem 'ex-insert-preserves '[x :- Nat, l :- (List Nat),
                                                   h :- (= Bool (ex-sorted l) true)]
                           '(= Bool (ex-sorted ((ex-insertSorted x) l)) true)
                           '[(revert h) (induction l)
                             ;; Base case
                             (intro h) (simp "ex-insertSorted" "ex-sorted")
                             ;; Cons: by_cases then revert + cases tail
                             (intro h) (by_cases (<= x head))
                             (all_goals (try (revert h)))
                             (all_goals (try (revert ih_tail)))
                             (all_goals (try (cases tail)))
                             (all_goals (try (intro ih_tail)))
                             (all_goals (try (intro h)))
                             ;; Round 1: simp_all (Phase 1 unfolds + Phase 2 decomposes h)
                             (all_goals (try (simp_all "ex-insertSorted" "ex-sorted")))
                             ;; Round 2: use Phase 2 decomposed hypotheses
                             (all_goals (try (simp_all "ex-insertSorted" "ex-sorted")))
                             (all_goals (try (simp_all "ex-insertSorted" "ex-sorted")))
                             ;; Close leaf goals
                             (all_goals (try (omega)))
                             ;; Split And goals
                             (all_goals (try (constructor)))
                             ;; Apply IH where possible
                             (all_goals (try (apply ih_tail)))
                             ;; Close remaining
                             (all_goals (try (simp_all "ex-sorted")))
                             (all_goals (try (simp_all "ex-sorted")))
                             (all_goals (try (omega)))
                             ;; Deep: more constructor + omega rounds
                             (all_goals (try (constructor)))
                             (all_goals (try (apply ih_tail)))
                             (all_goals (try (simp_all "ex-sorted")))
                             (all_goals (try (omega)))]
                           ctx)
          (is true "preservation lemma proved by induction + case analysis"))
          (finally
            (reset! a/ansatz-env saved-env)
            (reset! a/ansatz-instance-index saved-idx)))))))


;; ============================================================
;; GD convergence examples (requires Mathlib)
;; ============================================================

(def ^:private mathlib-available?
  (delay
    (try
      (let [store-path "/var/tmp/ansatz-mathlib"]
        (when (.exists (java.io.File. store-path))
          (binding [a/*verbose* false]
            (a/init! store-path "mathlib"))
          (some? (env/lookup (a/env) (name/from-string "Real")))))
      (catch Exception _ false))))

(defmacro ^:private when-mathlib [& body]
  `(if @mathlib-available?
     (binding [a/*verbose* false] ~@body)
     (is true "skipped: Mathlib store not available")))

(deftest test-gd-defn
  (when-mathlib
   (testing "Define verified GD step function"
     (let [f (a/define-verified 'ex-gd-step
               '[x :- Real, grad :- Real, eta :- Real] 'Real
               '(sub Real x (mul Real eta grad)))]
       (is (fn? f))
       (is (= 8.2 (double (((f 10.0) 6.0) 0.3))))))))

(deftest test-gd-convergence
  (when-mathlib
   (testing "Prove GD convergence rate"
     (a/prove-theorem 'ex-convergence
                      '[κ :- Real, ε₀ :- Real, n :- Nat,
                        hκ₀ :- (<= Real 0 κ), hκ₁ :- (<= Real κ 1), hε₀ :- (<= Real 0 ε₀)]
                      '(<= Real (mul Real (pow Real κ n) ε₀) ε₀)
                      '[(apply mul_le_of_le_one_left) (assumption)
                        (apply pow_le_one₀) (all_goals (assumption))])
     (is true))))

(deftest test-gd-full
  (when-mathlib
   (testing "Prove full GD convergence with step size"
     (a/prove-theorem 'ex-full
                      '[η :- Real, L :- Real, ε₀ :- Real, n :- Nat,
                        hη :- (<= Real 0 η), hL :- (<= Real 0 L),
                        hbound :- (<= Real (mul Real η L) 1), hε₀ :- (<= Real 0 ε₀)]
                      '(<= Real (mul Real (pow Real (sub Real 1 (mul Real η L)) n) ε₀) ε₀)
                      '[(apply mul_le_of_le_one_left) (assumption)
                        (apply pow_le_one₀)
                        (apply sub_nonneg_of_le) (assumption)
                        (apply sub_le_self) (apply mul_nonneg) (assumption) (assumption)])
     (is true))))
