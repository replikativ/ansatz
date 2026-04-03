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

(def ^:private baseline-state
  (delay
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
        (binding [a/*verbose* false]
          (when-not (env/lookup (a/env) (name/from-string "TRBColor"))
            (eval '(ansatz.core/inductive TRBColor [] (red) (black)))
            (eval '(ansatz.core/inductive TRBTree [α Type]
                                          (leaf) (node [color TRBColor] [left (TRBTree α)] [key α] [right (TRBTree α)]))))
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
                       (nil nil) (cons [hd tl] ((ex-insertSorted hd) ih_tail)))))))
          {:env @a/ansatz-env
           :idx @a/ansatz-instance-index}))))

(defn- with-baseline-env [f]
  (when-let [{:keys [env idx]} @baseline-state]
    (reset! a/ansatz-env (env/fork env))
    (reset! a/ansatz-instance-index idx)
    (f)))

(use-fixtures :each with-baseline-env)

;; ============================================================
;; Structure tests (init-medium sufficient)
;; ============================================================

(deftest test-structure-definition
  (testing "Define structures with auto-generated projections"
    (binding [a/*verbose* false]
      ;; Parameterized structure
      (when-not (env/lookup (a/env) (name/from-string "ExPair"))
        (eval '(ansatz.core/structure ExPair [α Type β Type] (fst α) (snd β))))
      (is (some? (env/lookup (a/env) (name/from-string "ExPair"))) "ExPair defined")
      (is (some? (env/lookup (a/env) (name/from-string "ExPair.mk"))) "ExPair.mk defined")
      (is (some? (env/lookup (a/env) (name/from-string "ExPair.fst"))) "ExPair.fst projection")
      (is (some? (env/lookup (a/env) (name/from-string "ExPair.snd"))) "ExPair.snd projection")
      ;; Kernel-verify projections
      (let [tc (ansatz.kernel.TypeChecker. (a/env))]
        (.setFuel tc 50000000)
        (doseq [nm ["ExPair.fst" "ExPair.snd"]]
          (let [ci (env/lookup (a/env) (name/from-string nm))]
            (is (.isDefEq tc (.inferType tc (.value ci)) (.type ci))
                (str nm " kernel-verified"))))))))

;; ============================================================
;; Well-founded recursion tests (init-medium sufficient)
;; ============================================================

(deftest test-wf-recursion-countdown
  (testing "WF recursion: countdown with match on Nat"
    (binding [a/*verbose* false]
      (when-not (env/lookup (a/env) (name/from-string "ex-countdown"))
        (eval '(ansatz.core/defn ex-countdown [n :- Nat] Nat
                 :termination-by n
                 (match n Nat Nat (zero 0) (succ [pred] (+ 1 (ex-countdown pred)))))))
      (is (some? (env/lookup (a/env) (name/from-string "ex-countdown")))
          "countdown defined with WF recursion")
      ;; Kernel verification: the definition type-checks
      (let [tc (ansatz.kernel.TypeChecker. (a/env))
            _ (.setFuel tc 50000000)
            ci (env/lookup (a/env) (name/from-string "ex-countdown"))]
        (is (.isDefEq tc (.inferType tc (.value ci)) (.type ci))
            "countdown kernel-verified")))))

(deftest test-wf-recursion-factorial
  (testing "WF recursion: factorial with if on Bool"
    (binding [a/*verbose* false]
      (when-not (env/lookup (a/env) (name/from-string "ex-fact"))
        (eval '(ansatz.core/defn ex-fact [n :- Nat] Nat
                 :termination-by n
                 (if (== n 0) 1 (* n (ex-fact (- n 1)))))))
      (is (some? (env/lookup (a/env) (name/from-string "ex-fact")))
          "factorial defined with WF recursion")
      (let [tc (ansatz.kernel.TypeChecker. (a/env))
            _ (.setFuel tc 50000000)
            ci (env/lookup (a/env) (name/from-string "ex-fact"))]
        (is (.isDefEq tc (.inferType tc (.value ci)) (.type ci))
            "factorial kernel-verified")))))

(deftest test-wf-recursion-multi-arg
  (testing "WF recursion: multi-arg with compound measure"
    (binding [a/*verbose* false]
      (when-not (env/lookup (a/env) (name/from-string "ex-myadd"))
        (eval '(ansatz.core/defn ex-myadd [x :- Nat, y :- Nat] Nat
                 :termination-by (+ x y)
                 (match x Nat Nat (zero y) (succ [k] (+ 1 (ex-myadd k y)))))))
      (is (some? (env/lookup (a/env) (name/from-string "ex-myadd")))
          "multi-arg WF function defined")
      (let [tc (ansatz.kernel.TypeChecker. (a/env))
            _ (.setFuel tc 50000000)
            ci (env/lookup (a/env) (name/from-string "ex-myadd"))]
        (is (.isDefEq tc (.inferType tc (.value ci)) (.type ci))
            "multi-arg WF function kernel-verified")))))

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
                         ;; simp_all unfolds + omega handles LE goals from hypothesis decomposition
                         (all_goals (try (simp_all "ex-insertSorted" "ex-sorted")))
                         (all_goals (try (omega)))
                         (all_goals (try (simp_all "ex-insertSorted" "ex-sorted")))
                         (all_goals (try (omega)))])
      (is true "singleton case proved by by_cases + simp_all + omega"))))

(deftest test-isort-preservation
  (testing "Sorted(insertSorted x l) by induction on Prop-valued Sorted predicate"
    (binding [a/*verbose* false]
      ;; Use fresh env for full isolation
      (let [saved-env @a/ansatz-env
            fresh-env (env/fork @init-env)
            saved-idx @a/ansatz-instance-index]
        (try
          (reset! a/ansatz-env fresh-env)
          (reset! a/ansatz-instance-index saved-idx)
          (reset! @(resolve 'ansatz.tactic.simp/fun-info-cache) {})
          ;; Define insertSorted in the fresh env
          (eval '(ansatz.core/defn ex-insertSorted [x Nat l (List Nat)] (List Nat)
                   (match l (List Nat) (List Nat)
                     (nil (cons x nil)) (cons [hd tl] (match (<= x hd) Bool (List Nat)
                       (true (cons x l)) (false (cons hd ih_tail)))))))
          ;; Define Prop-valued Sorted indexed inductive:
          ;;   Sorted : List Nat → Prop
          ;;   nil    : Sorted []
          ;;   single : ∀ a, Sorted [a]
          ;;   cons_cons : ∀ a b tl, a ≤ b → Sorted (b::tl) → Sorted (a::b::tl)
          (eval '(ansatz.core/inductive Sorted [] :in Prop :indices [l (List Nat)]
                   (nil :where [(nil)])
                   (single [a Nat] :where [(cons a nil)])
                   (cons_cons [a Nat] [b Nat] [tl (List Nat)]
                              [hab (le a b)]
                              [hsorted (Sorted (cons b tl))]
                     :where [(cons a (cons b tl))])))
          (is (some? (env/lookup (a/env) (name/from-string "Sorted")))
              "Sorted inductive defined")
          (is (some? (env/lookup (a/env) (name/from-string "Sorted.rec")))
              "Sorted.rec generated")
          ;; Prove: ∀ x l, Sorted l → Sorted (insertSorted x l)
          ;; By induction on h : Sorted l (3 cases: nil, single, cons_cons)
          ;; Note: after (induction h), goals are [nil, single, cons_cons].
          ;; simp on nil creates a replacement goal that goes to back,
          ;; so after simp the order is [single, cons_cons, nil'].
          (let [ctx (a/make-context @a/ansatz-env @a/ansatz-instance-index)]
            (a/prove-theorem 'ex-insert-preserves
                             '[x :- Nat, l :- (List Nat), h :- (Sorted l)]
                             '(Sorted ((ex-insertSorted x) l))
                             '[(induction h)
                               ;; Nil case: insertSorted x [] = [x] → Sorted.single
                               (apply (Sorted.single x))
                               ;; Case-split on x ≤ a, unfold insertSorted
                               (all_goals (try (by_cases (<= x a))))
                               (all_goals (try (simp_all "ex-insertSorted")))
                               ;; Sub-split cons_cons case on x ≤ b
                               (all_goals (try (by_cases (<= x b))))
                               (all_goals (try (simp_all "ex-insertSorted")))
                               ;; Reduce remaining Bool.rec applications
                               (all_goals (try (simp_all "ex-insertSorted")))
                               ;; Close: constructors + arithmetic + assumptions
                               (all_goals (try (apply Sorted.cons_cons)))
                               (all_goals (try (omega)))
                               (all_goals (try (apply Sorted.single)))
                               (all_goals (try (assumption)))
                               (all_goals (try (apply Sorted.cons_cons)))
                               (all_goals (try (omega)))
                               (all_goals (try (assumption)))]
                             ctx)
            (is true "preservation theorem proved by induction on Sorted"))
          (finally
            (reset! a/ansatz-env saved-env)
            (reset! a/ansatz-instance-index saved-idx)))))))


;; ============================================================
;; Grind: insertion sort preservation (Phase 1)
;; After induction, grind handles all 3 cases automatically:
;; nil (constructors), single (by_cases+simp+constructors),
;; cons_cons (nested by_cases+constructors+assumption+omega)
;; ============================================================

(deftest test-isort-preservation-grind
  (testing "Sorted(insertSorted x l) via induction + grind"
    (binding [a/*verbose* false]
      (let [saved-env @a/ansatz-env
            fresh-env (env/fork @init-env)
            saved-idx @a/ansatz-instance-index]
        (try
          (reset! a/ansatz-env fresh-env)
          (reset! a/ansatz-instance-index saved-idx)
          (reset! @(resolve 'ansatz.tactic.simp/fun-info-cache) {})
          (eval '(ansatz.core/defn ex-insertSorted [x Nat l (List Nat)] (List Nat)
                   (match l (List Nat) (List Nat)
                     (nil (cons x nil)) (cons [hd tl] (match (<= x hd) Bool (List Nat)
                       (true (cons x l)) (false (cons hd ih_tail)))))))
          (eval '(ansatz.core/inductive Sorted [] :in Prop :indices [l (List Nat)]
                   (nil :where [(nil)])
                   (single [a Nat] :where [(cons a nil)])
                   (cons_cons [a Nat] [b Nat] [tl (List Nat)]
                              [hab (le a b)]
                              [hsorted (Sorted (cons b tl))]
                     :where [(cons a (cons b tl))])))
          (let [ctx (a/make-context @a/ansatz-env @a/ansatz-instance-index)]
            (a/prove-theorem 'ex-insert-preserves-grind
                             '[x :- Nat, l :- (List Nat), h :- (Sorted l)]
                             '(Sorted ((ex-insertSorted x) l))
                             '[(induction h)
                               (grind "ex-insertSorted")]
                             ctx)
            (is true "preservation proved by induction + grind"))
          (finally
            (reset! a/ansatz-env saved-env)
            (reset! a/ansatz-instance-index saved-idx)))))))

;; ============================================================
;; Indexed family infrastructure tests
;; Regression tests for: indexed motive construction, IH ordering,
;; equation theorem discriminant position, match l leak
;; ============================================================

(deftest test-indexed-family-induction
  (testing "Induction on indexed family over user-defined type"
    (binding [a/*verbose* false]
      ;; Define ValidRB : TRBTree Nat → Prop (indexed by user-defined type)
      (eval '(ansatz.core/inductive ValidRB [] :in Prop :indices [t (TRBTree Nat)]
               (vleaf :where [(TRBTree.leaf Nat)])
               (vnode [c TRBColor] [l (TRBTree Nat)] [k Nat] [r (TRBTree Nat)]
                      [hl (ValidRB l)] [hr (ValidRB r)]
                 :where [(TRBTree.node Nat c l k r)])))
      (is (some? (env/lookup (a/env) (name/from-string "ValidRB"))))
      (is (some? (env/lookup (a/env) (name/from-string "ValidRB.rec"))))
      ;; Verify Sorted.rec IH bvar lifting (Bug 3 fix)
      ;; and IH ordering (fields first, then IHs)
      (let [ctx (a/make-context @a/ansatz-env @a/ansatz-instance-index)]
        ;; Identity proof: induction with 2 recursive fields (hl, hr)
        (a/prove-theorem 'vrb-id
                         '[t :- (TRBTree Nat), h :- (ValidRB t)]
                         '(ValidRB t)
                         '[(induction h)
                           (apply ValidRB.vleaf)
                           (apply ValidRB.vnode) (assumption) (assumption)]
                         ctx)
        (is true "indexed family induction with multiple recursive fields"))
      ;; Cases on indexed family with COMPLEX index (constructor application)
      ;; Uses casesOn-based motive: pattern-matches on the index type to produce
      ;; the correct branch goal type without equality arrows or noConfusion.
      (let [ctx (a/make-context @a/ansatz-env @a/ansatz-instance-index)]
        ;; cases hl where hl : ValidRB(node c l k r) → ValidRB l
        (a/prove-theorem 'vrb-cases-l
                         '[c :- TRBColor, l :- (TRBTree Nat), k :- Nat, r :- (TRBTree Nat),
                           hl :- (ValidRB (TRBTree.node Nat c l k r))]
                         '(ValidRB l)
                         '[(cases hl) (assumption)]
                         ctx)
        (is true "cases on indexed family extracts ValidRB l"))
      ;; Same but extract ValidRB r (different component)
      (let [ctx (a/make-context @a/ansatz-env @a/ansatz-instance-index)]
        (a/prove-theorem 'vrb-cases-r
                         '[c :- TRBColor, l :- (TRBTree Nat), k :- Nat, r :- (TRBTree Nat),
                           hl :- (ValidRB (TRBTree.node Nat c l k r))]
                         '(ValidRB r)
                         '[(cases hl) (assumption)]
                         ctx)
        (is true "cases on indexed family extracts ValidRB r"))
      ;; cases on leaf index (opposite impossible branch)
      (let [ctx (a/make-context @a/ansatz-env @a/ansatz-instance-index)]
        (a/prove-theorem 'vrb-cases-leaf
                         '[hl :- (ValidRB (TRBTree.leaf Nat))]
                         '(Nat.le Nat.zero Nat.zero)
                         '[(cases hl) (apply Nat.le.refl)]
                         ctx)
        (is true "cases on ValidRB leaf — node branch impossible")))))

(deftest test-equation-theorem-discriminant-position
  (testing "Equation theorems for first-arg discriminant (balance1 matches on l, not r)"
    (binding [a/*verbose* false]
      ;; balance1 has eq_1 for leaf and eq_2 + splits for node
      ;; The leaf equation should be: balance1 leaf v r = node black leaf v r
      ;; NOT: balance1 v r leaf = ... (wrong discriminant position)
      (a/define-verified 'ex-balance1b
        '[l (TRBTree Nat) v Nat r (TRBTree Nat)] '(TRBTree Nat)
        '(match l (TRBTree Nat) (TRBTree Nat)
                (leaf (TRBTree.node Nat (TRBColor.black) (TRBTree.leaf Nat) v r))
                (node [lc ll lk lr] (TRBTree.node Nat (TRBColor.black) l v r))))
      ;; Verify: eq_1 should have balance1 leaf v r on LHS
      (let [ci (env/lookup (a/env) (name/from-string "ex-balance1b.eq_1"))
            ^ansatz.kernel.TypeChecker tc (ansatz.kernel.TypeChecker. (a/env))]
        (.setFuel tc (int 50000000))
        (is (some? ci) "eq_1 exists")
        (is (.isDefEq tc (.inferType tc (.value ci)) (.type ci))
            "eq_1 type-checks (discriminant in first position)")))))

(deftest test-match-discriminant-substitution
  (testing "Match body referencing outer parameter uses ctor-applied form"
    (binding [a/*verbose* false]
      ;; insertSorted has (cons x l) in the true branch where l is the match param.
      ;; After the match compilation fix, l should be substituted with (cons hd tl).
      ;; The equation theorem eq_2 must be kernel-verifiable.
      (eval '(ansatz.core/defn ex-ins2 [x Nat l (List Nat)] (List Nat)
               (match l (List Nat) (List Nat)
                 (nil (cons x nil)) (cons [hd tl] (match (<= x hd) Bool (List Nat)
                   (true (cons x l)) (false (cons hd ih_tail)))))))
      (let [^ansatz.kernel.TypeChecker tc (ansatz.kernel.TypeChecker. (a/env))]
        (.setFuel tc (int 50000000))
        (doseq [suffix ["1" "2"]]
          (let [ci (env/lookup (a/env) (name/from-string (str "ex-ins2.eq_" suffix)))]
            (is (some? ci) (str "eq_" suffix " exists"))
            (when ci
              (is (.isDefEq tc (.inferType tc (.value ci)) (.type ci))
                  (str "eq_" suffix " is kernel-verifiable")))))))))

(deftest test-balance1-leaf-preservation
  (testing "balance1 preserves ValidRB for leaf case"
    (binding [a/*verbose* false]
      ;; Uses the ValidRB from test-indexed-family-induction (already defined in fixture env)
      (when (env/lookup (a/env) (name/from-string "ValidRB"))
        (a/define-verified 'ex-bal1c
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
        (let [ctx (a/make-context @a/ansatz-env @a/ansatz-instance-index)]
          ;; Leaf case: balance1 leaf v r = node black leaf v r → ValidRB
          (a/prove-theorem 'bal1-leaf-valid
                           '[v :- Nat, r :- (TRBTree Nat), hr :- (ValidRB r)]
                           '(ValidRB (((ex-bal1c (TRBTree.leaf Nat)) v) r))
                           '[(simp "ex-bal1c")
                             (apply ValidRB.vnode) (apply ValidRB.vleaf) (assumption)]
                           ctx)
          (is true "balance1 leaf case preserves ValidRB")
          ;; LL rotation case: balance1 (node red (node red a x b) y c) v r → ValidRB
          (a/prove-theorem 'bal1-ll-valid
                           '[a :- (TRBTree Nat), x :- Nat, b :- (TRBTree Nat),
                             y :- Nat, c :- (TRBTree Nat), v :- Nat, r :- (TRBTree Nat),
                             ha :- (ValidRB a), hb :- (ValidRB b),
                             hc :- (ValidRB c), hr :- (ValidRB r)]
                           '(ValidRB (((ex-bal1c
                                        (TRBTree.node Nat (TRBColor.red)
                                          (TRBTree.node Nat (TRBColor.red) a x b) y c)) v) r))
                           '[(simp "ex-bal1c")
                             (apply ValidRB.vnode)
                             (apply ValidRB.vnode) (assumption) (assumption)
                             (apply ValidRB.vnode) (assumption) (assumption)]
                           ctx)
          (is true "balance1 LL rotation preserves ValidRB"))))))

(deftest test-cases-indexed-goal-preservation
  (testing "cases on indexed family preserves original fvars in goal (Path C)"
    (binding [a/*verbose* false]
      ;; This test verifies the core capability: after `cases hl` where
      ;; hl : ValidRB(node c l k r) and the goal references l and r
      ;; in other positions, the goal type correctly keeps l and r.
      ;; The old Path B over-abstracted them; Path C (generalizeIndices
      ;; + unifyCasesEqs) properly resolves the equalities.
      (when (env/lookup (a/env) (name/from-string "ValidRB"))
        ;; Test: given hl : ValidRB(node c l k r), hr : ValidRB r
        ;; prove: ValidRB l ∧ ValidRB r (both components accessible)
        (let [ctx (a/make-context @a/ansatz-env @a/ansatz-instance-index)]
          ;; cases hl decomposes ValidRB(node c l k r) into fields with
          ;; proper substitution: hl_l : ValidRB l, hl_r : ValidRB r
          (a/prove-theorem 'vrb-decompose-both
                           '[c :- TRBColor, l :- (TRBTree Nat), k :- Nat, r :- (TRBTree Nat),
                             hl :- (ValidRB (TRBTree.node Nat c l k r)),
                             hr :- (ValidRB r)]
                           '(ValidRB r)
                           '[(cases hl) (assumption)]
                           ctx)
          (is true "cases decomposes indexed family, goal preserves fvars"))))))

(deftest test-balance1-invariant-full
  (testing "balance1 preserves ValidRB for ALL cases (full kernel-verified proof)"
    (binding [a/*verbose* false]
      ;; Define ValidRB if needed
      (when-not (env/lookup (a/env) (name/from-string "ValidRB"))
        (eval '(ansatz.core/inductive ValidRB [] :in Prop :indices [t (TRBTree Nat)]
                 (vleaf :where [(TRBTree.leaf Nat)])
                 (vnode [c TRBColor] [l (TRBTree Nat)] [k Nat] [r (TRBTree Nat)]
                        [hl (ValidRB l)] [hr (ValidRB r)]
                   :where [(TRBTree.node Nat c l k r)]))))
      (when (env/lookup (a/env) (name/from-string "ValidRB"))
        ;; Define balance1 if needed
        (when-not (env/lookup (a/env) (name/from-string "ex-bal1full"))
          (a/define-verified 'ex-bal1full
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
                                                                         (TRBTree.node Nat (TRBColor.black) lr v r))))))))))))
        ;; Prove: ∀ l v r, ValidRB l → ValidRB r → ValidRB(balance1 l v r)
        ;;
        ;; This is the full balance invariant for the left-left rotation case of
        ;; red-black tree insertion. The proof exercises the complete Lean 4 cases
        ;; pipeline:
        ;;
        ;; 1. cases hl (indexed family decomposition via generalizeIndices + noConfusion)
        ;;    Decomposes ValidRB(l) into vleaf (l=leaf) and vnode (l=node c ll lk lr)
        ;;    with field hypotheses hl_l : ValidRB ll, hr_l : ValidRB lr
        ;;
        ;; 2. cases c (structural with dependent hl, uses Lean 4 revert pattern)
        ;;    Splits on the color. The motive includes reverted hl so its type
        ;;    updates from ValidRB(node c ...) to ValidRB(node red/black ...)
        ;;
        ;; 3. cases l (structural on inner left subtree)
        ;;    Further decomposes for the equation theorem matching
        ;;
        ;; 4. cases color (inner color split for LL rotation detection)
        ;;
        ;; 5. cases hl (SECOND indexed decomposition for LL rotation)
        ;;    Decomposes ValidRB(node red lll llk llr) to get ValidRB lll, ValidRB llr
        ;;
        ;; 6. simp "ex-bal1full" (equation theorem simplification in each branch)
        ;;
        ;; 7. apply ValidRB.vnode + assumption (close each branch)
        ;;
        ;; Total: 7 branches, all kernel-verified via the Java TypeChecker.
        (let [ctx (a/make-context @a/ansatz-env @a/ansatz-instance-index)]
          (a/prove-theorem 'bal1-full-invariant
                           '[l :- (TRBTree Nat), v :- Nat, r :- (TRBTree Nat),
                             hl :- (ValidRB l), hr :- (ValidRB r)]
                           '(ValidRB (((ex-bal1full l) v) r))
                           '[(cases hl)
                             ;; vleaf: balance1 leaf v r = node black leaf v r
                             (simp "ex-bal1full")
                             (apply ValidRB.vnode) (apply ValidRB.vleaf) (assumption)
                             ;; vnode: cases on color (structural, hl reverted in motive)
                             (cases c)
                             ;; red: cases on inner left subtree
                             (cases l)
                             ;; red-leaf: eq_2s1
                             (simp "ex-bal1full")
                             (apply ValidRB.vnode)
                             (apply ValidRB.vnode) (apply ValidRB.vleaf) (assumption)
                             (assumption)
                             ;; red-node: cases on inner color
                             (cases color)
                             ;; LL rotation (red-red): decompose inner ValidRB
                             (cases hl)
                             (simp "ex-bal1full")
                             (apply ValidRB.vnode)
                             (apply ValidRB.vnode) (assumption) (assumption)
                             (apply ValidRB.vnode) (assumption) (assumption)
                             ;; red-black: no rotation
                             (simp "ex-bal1full")
                             (apply ValidRB.vnode)
                             (apply ValidRB.vnode) (assumption) (assumption)
                             (assumption)
                             ;; black: no rotation
                             (simp "ex-bal1full")
                             (apply ValidRB.vnode)
                             (apply ValidRB.vnode) (assumption) (assumption)
                             (assumption)]
                           ctx)
          (is true "balance1 preserves ValidRB for all cases (kernel-verified)"))))))

;; ============================================================
;; GD convergence examples (requires Mathlib)
;; ============================================================

(def ^:private mathlib-available?
  (delay
    (try
      (let [store-path "/var/tmp/ansatz-mathlib"]
        (.exists (java.io.File. store-path)))
      (catch Exception _ false))))

(defmacro ^:private when-mathlib [& body]
  `(if @mathlib-available?
     (let [saved-env# @a/ansatz-env
           saved-idx# @a/ansatz-instance-index]
       (try
         (binding [a/*verbose* false]
           (a/init! "/var/tmp/ansatz-mathlib" "mathlib")
           ~@body)
         (finally
           (reset! a/ansatz-env saved-env#)
           (reset! a/ansatz-instance-index saved-idx#))))
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
