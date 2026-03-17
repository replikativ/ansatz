(ns ansatz.tactic.simp-test
  "Tests for enhanced simp tactic and norm_cast."
  (:require [clojure.test :refer [deftest testing is]]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.tc :as tc]
            [ansatz.tactic.proof :as proof]
            [ansatz.tactic.basic :as basic]
            [ansatz.tactic.simp :as simp]
            [ansatz.tactic.norm-cast :as nc]
            [ansatz.tactic.extract :as extract]
            [ansatz.export.parser :as parser]
            [ansatz.export.replay :as replay]))

(def ^:private init-medium-env
  (delay
    (let [f "test-data/init-medium.ndjson"]
      (when (.exists (java.io.File. f))
        (let [st (parser/parse-ndjson-file f)
              result (replay/replay (:decls st))]
          (:env result))))))

(defn- require-env []
  (or @init-medium-env
      (throw (ex-info "init-medium.ndjson not found" {}))))

;; ============================================================
;; simp-expr tests (expression-level simplification)
;; ============================================================

(deftest test-simp-expr-nat-literal-reduction
  (testing "Nat.add 3 4 reduces to 7 via WHNF"
    (let [env (require-env)
          st (tc/mk-tc-state env)
          expr (e/app* (e/const' (name/from-string "Nat.add") [])
                       (e/lit-nat 3) (e/lit-nat 4))
          result (simp/simp-expr st env {} expr 20)]
      (is (e/lit-nat? result))
      (is (= 7 (e/lit-nat-val result))))))

(deftest test-simp-expr-nat-mul-reduction
  (testing "Nat.mul 6 7 reduces to 42 via WHNF"
    (let [env (require-env)
          st (tc/mk-tc-state env)
          expr (e/app* (e/const' (name/from-string "Nat.mul") [])
                       (e/lit-nat 6) (e/lit-nat 7))
          result (simp/simp-expr st env {} expr 20)]
      (is (e/lit-nat? result))
      (is (= 42 (e/lit-nat-val result))))))

(deftest test-simp-expr-with-lemma
  (testing "Simplification using Nat.add_zero lemma"
    (let [env (require-env)
          st (tc/mk-tc-state env)
          lemmas (simp/make-simp-lemmas env ["Nat.add_zero"])
          idx (simp/build-lemma-index st env lemmas)]
      ;; Nat.add_zero has LHS head = HAdd.hAdd
      (is (= 1 (count lemmas)))
      (is (= :eq (:kind (first lemmas)))))))

(deftest test-simp-expr-nested-reduction
  (testing "Nested arithmetic: Nat.add (Nat.mul 3 2) (Nat.add 1 0)"
    (let [env (require-env)
          st (tc/mk-tc-state env)
          nat-add (name/from-string "Nat.add")
          nat-mul (name/from-string "Nat.mul")
          inner1 (e/app* (e/const' nat-mul []) (e/lit-nat 3) (e/lit-nat 2))
          inner2 (e/app* (e/const' nat-add []) (e/lit-nat 1) (e/lit-nat 0))
          expr (e/app* (e/const' nat-add []) inner1 inner2)
          result (simp/simp-expr st env {} expr 20)]
      (is (e/lit-nat? result))
      (is (= 7 (e/lit-nat-val result))))))

;; ============================================================
;; simp lemma extraction tests
;; ============================================================

(deftest test-make-simp-lemmas
  (testing "Extracts simp lemmas from environment"
    (let [env (require-env)
          lemmas (simp/make-simp-lemmas env ["Nat.add_zero" "Nat.zero_add"
                                             "Nat.mul_one" "Nat.one_mul"])]
      (is (= 4 (count lemmas)))
      (doseq [l lemmas]
        (is (:name l))
        (is (= :eq (:kind l)))
        (is (= 1 (:num-params l)))
        (is (:head-name l))))))

(deftest test-make-simp-lemmas-missing
  (testing "Missing lemma names are silently skipped"
    (let [env (require-env)
          lemmas (simp/make-simp-lemmas env ["Nat.add_zero" "NoSuchLemma"])]
      (is (= 1 (count lemmas))))))

(deftest test-build-lemma-index
  (testing "Builds discrimination tree index"
    (let [env (require-env)
          lemmas (simp/make-simp-lemmas env ["Nat.add_zero" "Nat.zero_add"])
          idx (simp/build-lemma-index lemmas)]
      ;; Tree should contain 2 lemmas
      (is (= 2 (ansatz.tactic.discr-tree/tree-size idx))))))

;; ============================================================
;; SimpResult / proof tracking tests
;; ============================================================

(deftest test-simp-result-structure
  (testing "simp-expr* returns well-formed SimpResult"
    (let [env (require-env)
          st (tc/mk-tc-state env)
          ;; Simple expr that should be simplified by WHNF
          expr (e/app* (e/const' (name/from-string "Nat.add") [])
                       (e/lit-nat 2) (e/lit-nat 3))
          result (#'simp/simp-expr* st env {} expr
                                    {:max-depth 20 :single-pass? false :max-steps (atom 0)})]
      (is (map? result))
      (is (contains? result :expr))
      (is (contains? result :proof?))
      (is (e/lit-nat? (:expr result)))
      (is (= 5 (e/lit-nat-val (:expr result)))))))

;; ============================================================
;; norm_cast tests
;; ============================================================

(deftest test-norm-cast-classify-lemma
  (testing "Classifies norm_cast lemmas correctly (when available)"
    (let [env (require-env)]
      ;; These may not be in init-medium, so check if they exist first
      (when (env/lookup env (name/from-string "Nat.cast_add"))
        (is (= :move (nc/classify-lemma env "Nat.cast_add"))))
      (when (env/lookup env (name/from-string "Nat.cast_mul"))
        (is (= :move (nc/classify-lemma env "Nat.cast_mul"))))
      (when (env/lookup env (name/from-string "Nat.cast_inj"))
        (is (= :elim (nc/classify-lemma env "Nat.cast_inj")))))))

(deftest test-norm-cast-coercion-names
  (testing "Coercion name detection works"
    (let [env (require-env)
          nc-app (e/app* (e/const' (name/from-string "Nat.cast") [lvl/zero])
                         (e/const' (name/from-string "Int") [])
                         (e/const' (name/from-string "instNatCastInt") [])
                         (e/lit-nat 5))]
      ;; The is-coe-app? function should detect this
      (is (true? (#'nc/is-coe-app? nc-app))))))

;; ============================================================
;; Iff lemma support tests
;; ============================================================

(deftest test-iff-lemma-extraction
  (testing "Iff lemmas are extracted correctly"
    (let [env (require-env)]
      ;; Look for an Iff lemma in init-medium
      (when-let [ci (env/lookup env (name/from-string "Nat.lt_iff_add_one_le"))]
        (let [lemma (#'simp/extract-simp-lemma env ci 1000)]
          (when lemma
            (is (= :iff (:kind lemma)))))))))

;; ============================================================
;; Enhanced simproc tests
;; ============================================================

(deftest test-simproc-nat-succ
  (testing "Nat.succ n reduces to n+1 for literal n"
    (let [env (require-env)
          st (tc/mk-tc-state env)
          expr (e/app (e/const' (name/from-string "Nat.succ") []) (e/lit-nat 5))
          result (simp/simp-expr st env {} expr 20)]
      (is (e/lit-nat? result))
      (is (= 6 (e/lit-nat-val result))))))

(deftest test-simproc-nat-div
  (testing "Nat.div reduces on literals"
    (let [env (require-env)
          st (tc/mk-tc-state env)
          expr (e/app* (e/const' (name/from-string "Nat.div") [])
                       (e/lit-nat 10) (e/lit-nat 3))
          result (simp/simp-expr st env {} expr 20)]
      (is (e/lit-nat? result))
      (is (= 3 (e/lit-nat-val result))))))

(deftest test-simproc-nat-mod
  (testing "Nat.mod reduces on literals"
    (let [env (require-env)
          st (tc/mk-tc-state env)
          expr (e/app* (e/const' (name/from-string "Nat.mod") [])
                       (e/lit-nat 10) (e/lit-nat 3))
          result (simp/simp-expr st env {} expr 20)]
      (is (e/lit-nat? result))
      (is (= 1 (e/lit-nat-val result))))))

(deftest test-simproc-nat-sub-floor
  (testing "Nat.sub floors at 0 (Nat subtraction)"
    (let [env (require-env)
          st (tc/mk-tc-state env)
          expr (e/app* (e/const' (name/from-string "Nat.sub") [])
                       (e/lit-nat 3) (e/lit-nat 7))
          result (simp/simp-expr st env {} expr 20)]
      (is (e/lit-nat? result))
      (is (= 0 (e/lit-nat-val result))))))

(deftest test-simp-max-steps
  (testing "simp terminates with max-steps"
    (let [env (require-env)
          st (tc/mk-tc-state env)
          ;; Even on a complex expression, should not hang
          expr (e/app* (e/const' (name/from-string "Nat.add") [])
                       (e/lit-nat 1) (e/lit-nat 1))
          result (simp/simp-expr st env {} expr 20)]
      (is (e/lit-nat? result))
      (is (= 2 (e/lit-nat-val result))))))

;; ============================================================
;; Int simproc tests
;; ============================================================

(deftest test-simproc-int-add
  (testing "Int.add reduces on literals"
    (let [env (require-env)
          st (tc/mk-tc-state env)
          int-ofnat (name/from-string "Int.ofNat")
          ;; Build Int.add (Int.ofNat 3) (Int.ofNat 4)
          a (e/app (e/const' int-ofnat []) (e/lit-nat 3))
          b (e/app (e/const' int-ofnat []) (e/lit-nat 4))
          expr (e/app* (e/const' (name/from-string "Int.add") []) a b)
          result (simp/simp-expr st env {} expr 20)]
      ;; Should reduce to Int.ofNat 7
      (let [[head args] (e/get-app-fn-args result)]
        (is (e/const? head))
        (when (e/const? head)
          (is (= "Int.ofNat" (name/->string (e/const-name head)))))
        (when (= 1 (count args))
          (is (e/lit-nat? (nth args 0)))
          (is (= 7 (e/lit-nat-val (nth args 0)))))))))

(deftest test-simproc-int-neg
  (testing "Int.neg reduces on literals"
    (let [env (require-env)
          st (tc/mk-tc-state env)
          ;; Build Int.neg (Int.ofNat 5)
          a (e/app (e/const' (name/from-string "Int.ofNat") []) (e/lit-nat 5))
          expr (e/app (e/const' (name/from-string "Int.neg") []) a)
          result (simp/simp-expr st env {} expr 20)]
      ;; Should reduce to Int.negSucc 4
      (let [[head args] (e/get-app-fn-args result)]
        (is (e/const? head))
        (when (e/const? head)
          (is (= "Int.negSucc" (name/->string (e/const-name head)))))))))

;; ============================================================
;; Perm check tests
;; ============================================================

(deftest test-perm-detection
  (testing "Perm flag is set for commutative lemmas"
    (let [env (require-env)
          ;; Nat.add_comm has same head on both sides
          lemmas (simp/make-simp-lemmas env ["Nat.add_comm"])]
      (when (seq lemmas)
        (is (:perm (first lemmas)))))))

(deftest test-ac-lt-ordering
  (testing "AC-LT term ordering works"
    ;; bvar < fvar < const < app
    (is (#'simp/ac-lt? (e/bvar 0) (e/fvar 1)))
    (is (#'simp/ac-lt? (e/fvar 1) (e/const' (name/from-string "Nat") [])))
    (is (not (#'simp/ac-lt? (e/const' (name/from-string "Nat") []) (e/bvar 0))))
    ;; Same constructor: compare values
    (is (#'simp/ac-lt? (e/lit-nat 3) (e/lit-nat 5)))
    (is (not (#'simp/ac-lt? (e/lit-nat 5) (e/lit-nat 3))))))

;; ============================================================
;; Discrimination tree index tests
;; ============================================================

;; ============================================================
;; Core simproc tests (ite, ctor-eq)
;; ============================================================

(deftest test-reduce-ite-true
  (testing "ite True a b reduces to a"
    (let [env (require-env) st (tc/mk-tc-state env)
          nat-e (e/const' (name/from-string "Nat") [])
          tt (e/const' (name/from-string "True") [])
          inst (e/const' (name/from-string "instDecidableTrue") [])
          expr (e/app* (e/const' (name/from-string "ite") [(lvl/succ lvl/zero)])
                       nat-e tt inst (e/lit-nat 42) (e/lit-nat 0))
          result (simp/simp-expr st env {} expr 20)]
      (is (e/lit-nat? result))
      (is (= 42 (e/lit-nat-val result))))))

(deftest test-reduce-ctor-eq-different-literals
  (testing "1 = 0 reduces to False"
    (let [env (require-env) st (tc/mk-tc-state env)
          nat-e (e/const' (name/from-string "Nat") [])
          expr (e/app* (e/const' (name/from-string "Eq") [(lvl/succ lvl/zero)])
                       nat-e (e/lit-nat 1) (e/lit-nat 0))
          result (simp/simp-expr st env {} expr 20)]
      (is (e/const? result))
      (is (= "False" (name/->string (e/const-name result)))))))

(deftest test-reduce-ctor-eq-same-literals
  (testing "5 = 5 does NOT reduce to False"
    (let [env (require-env) st (tc/mk-tc-state env)
          nat-e (e/const' (name/from-string "Nat") [])
          expr (e/app* (e/const' (name/from-string "Eq") [(lvl/succ lvl/zero)])
                       nat-e (e/lit-nat 5) (e/lit-nat 5))
          result (simp/simp-expr st env {} expr 20)]
      ;; Should NOT be False
      (is (not (and (e/const? result)
                    (= "False" (name/->string (e/const-name result)))))))))

(deftest test-proof-skip-is-correct
  (testing "is-proof-term? does NOT skip propositions (types in Prop)"
    (let [env (require-env) st (tc/mk-tc-state env)
          ;; Eq Nat 1 0 is a Prop (a type), NOT a proof
          nat-e (e/const' (name/from-string "Nat") [])
          prop-expr (e/app* (e/const' (name/from-string "Eq") [(lvl/succ lvl/zero)])
                            nat-e (e/lit-nat 1) (e/lit-nat 0))]
      ;; A proposition is NOT a proof — should not be skipped
      (is (not (#'simp/is-proof-term? st prop-expr))))))

;; ============================================================
;; propext and rfl tests
;; ============================================================

(deftest test-rfl-detection
  (testing "RFL theorems are detected"
    (let [env (require-env)]
      ;; Some lemmas are definitional equalities (rfl proofs)
      ;; Check that the :rfl flag is set appropriately
      (let [lemmas (simp/make-simp-lemmas env ["Nat.add_zero"])]
        (when (seq lemmas)
          ;; :rfl may or may not be true depending on the proof
          (is (contains? (first lemmas) :rfl)))))))

;; ============================================================
;; Lambda funext tests
;; ============================================================

;; ============================================================
;; Transparency + close-goal tests
;; ============================================================

(deftest test-zero-add-simp
  (testing "0 + n = n closed by simp [Nat.zero_add]"
    (let [env (require-env)
          nat-e (e/const' (name/from-string "Nat") [])
          u1 (lvl/succ lvl/zero)
          hadd (fn [a b] (e/app* (e/const' (name/from-string "HAdd.hAdd") [lvl/zero lvl/zero lvl/zero])
                                 nat-e nat-e nat-e
                                 (e/app* (e/const' (name/from-string "instHAdd") [lvl/zero])
                                         nat-e (e/const' (name/from-string "instAddNat") []))
                                 a b))
          goal (e/forall' "n" nat-e
                          (e/app* (e/const' (name/from-string "Eq") [u1]) nat-e
                                  (hadd (e/lit-nat 0) (e/bvar 0)) (e/bvar 0)) :default)
          [ps _] (proof/start-proof env goal)
          ps (basic/intro ps "n")
          ps (simp/simp ps ["Nat.zero_add"])]
      (is (proof/solved? ps)))))

(deftest test-add-zero-simp
  (testing "n + 0 = n closed by simp [Nat.add_zero]"
    (let [env (require-env)
          nat-e (e/const' (name/from-string "Nat") [])
          u1 (lvl/succ lvl/zero)
          hadd (fn [a b] (e/app* (e/const' (name/from-string "HAdd.hAdd") [lvl/zero lvl/zero lvl/zero])
                                 nat-e nat-e nat-e
                                 (e/app* (e/const' (name/from-string "instHAdd") [lvl/zero])
                                         nat-e (e/const' (name/from-string "instAddNat") []))
                                 a b))
          goal (e/forall' "n" nat-e
                          (e/app* (e/const' (name/from-string "Eq") [u1]) nat-e
                                  (hadd (e/bvar 0) (e/lit-nat 0)) (e/bvar 0)) :default)
          [ps _] (proof/start-proof env goal)
          ps (basic/intro ps "n")
          ps (simp/simp ps ["Nat.add_zero"])]
      (is (proof/solved? ps)))))

(deftest test-lambda-no-delta-in-simp
  (testing "Simp does not delta-unfold Nat.add (uses lemmas instead)"
    (let [env (require-env) st (tc/mk-tc-state env)
          nat-e (e/const' (name/from-string "Nat") [])
          ;; λ x : Nat => Nat.add x 0 — without lemmas, stays as-is
          ;; (simp uses whnf-no-delta, so Nat.add is NOT unfolded)
          body (e/app* (e/const' (name/from-string "Nat.add") []) (e/bvar 0) (e/lit-nat 0))
          expr (e/lam "x" nat-e body :default)
          result (simp/simp-expr st env {} expr 20)]
      ;; Without Nat.add_zero lemma, body stays as Nat.add x 0
      (is (e/lam? result)))))

(deftest test-lambda-funext-with-proof
  (testing "Lambda body rewritten via lemma produces funext proof"
    (let [env (require-env) st (tc/mk-tc-state env)
          lemmas (simp/make-simp-lemmas env ["Nat.add_zero"])
          idx (simp/build-lemma-index st env lemmas)
          nat-e (e/const' (name/from-string "Nat") [])
          lhs (:lhs-pattern (first lemmas))]
      (when lhs
        (let [expr (e/lam "x" nat-e lhs :default)
              result (#'simp/simp-expr* st env idx expr
                                        {:max-depth 20 :single-pass? false :max-steps (atom 0)
                                         :cache (atom {}) :to-unfold #{} :discharge-depth 0})]
          ;; Should have a proof (funext)
          (is (some? (:proof? result))))))))

;; ============================================================
;; @[congr] theorem tests
;; ============================================================

;; ============================================================
;; Ground evaluation tests (equation theorems)
;; ============================================================

(defn- mk-nat-list
  "Build a Ansatz List Nat from a Clojure vector of nats."
  [ns]
  (let [nat (e/const' (name/from-string "Nat") [])
        u1 (lvl/succ lvl/zero)
        nil-nat (e/app (e/const' (name/from-string "List.nil") [u1]) nat)]
    (reduce (fn [rest n]
              (e/app* (e/const' (name/from-string "List.cons") [u1]) nat (e/lit-nat n) rest))
            nil-nat
            (reverse ns))))

(deftest test-ground-eval-list-length-nil
  (testing "List.length [] = 0 via equation theorems (when available)"
    (let [env (require-env)]
      (when (env/lookup env (name/from-string "List.length.eq_1"))
        (let [st (tc/mk-tc-state env)
              u1 (lvl/succ lvl/zero)
              nat-e (e/const' (name/from-string "Nat") [])
              expr (e/app* (e/const' (name/from-string "List.length") [u1])
                           nat-e (mk-nat-list []))
              result (simp/simp-expr st env {} expr 40)]
          (is (e/lit-nat? result))
          (is (= 0 (e/lit-nat-val result))))))))

(deftest test-ground-eval-list-length-cons
  (testing "List.length [1,2,3] = 3 via equation theorems (when available)"
    (let [env (require-env)]
      (when (env/lookup env (name/from-string "List.length.eq_1"))
        (let [st (tc/mk-tc-state env)
              u1 (lvl/succ lvl/zero)
              nat-e (e/const' (name/from-string "Nat") [])
              expr (e/app* (e/const' (name/from-string "List.length") [u1])
                           nat-e (mk-nat-list [1 2 3]))
              result (simp/simp-expr st env {} expr 40)]
          (is (e/lit-nat? result))
          (is (= 3 (e/lit-nat-val result))))))))

(deftest test-ground-eval-list-append
  (testing "List.append [1,2] [3] = [1,2,3] via equation theorems (when available)"
    (let [env (require-env)]
      (when (env/lookup env (name/from-string "List.append.eq_1"))
        (let [st (tc/mk-tc-state env)
              u1 (lvl/succ lvl/zero)
              nat-e (e/const' (name/from-string "Nat") [])
              expr (e/app* (e/const' (name/from-string "List.append") [u1])
                           nat-e (mk-nat-list [1 2]) (mk-nat-list [3]))
              result (simp/simp-expr st env {} expr 40)]
          ;; Result should be [1,2,3] — check it's a List.cons
          (let [[head args] (e/get-app-fn-args result)]
            (is (e/const? head))
            (is (= "List.cons" (name/->string (e/const-name head))))))))))

(deftest test-ground-eval-eqn-discovery
  (testing "Equation theorems discovered by name pattern (when available)"
    (let [env (require-env)]
      ;; These may only be in full mathlib, not init-medium
      (when (env/lookup env (name/from-string "List.length.eq_1"))
        (is (some? (env/lookup env (name/from-string "List.length.eq_1"))))
        (is (some? (env/lookup env (name/from-string "List.length.eq_2")))))
      (when (env/lookup env (name/from-string "List.map.eq_1"))
        (is (some? (env/lookup env (name/from-string "List.map.eq_1"))))
        (is (some? (env/lookup env (name/from-string "List.map.eq_2"))))))))

(deftest test-congr-theorem-registry
  (testing "Known congr theorems are registered"
    (is (= "ite_congr" (get @#'simp/known-congr-theorems "ite")))))

(deftest test-discrimination-tree-index
  (testing "Discrimination tree indexes and retrieves lemmas"
    (let [env (require-env)
          lemmas (simp/make-simp-lemmas env ["Nat.add_zero" "Nat.zero_add"])
          idx (simp/build-lemma-index lemmas)]
      ;; Tree should have depth > 1 (multi-level indexing)
      (is (pos? (ansatz.tactic.discr-tree/tree-depth idx)))
      ;; Looking up HAdd.hAdd Nat Nat Nat inst n 0 should find Nat.add_zero
      ;; Looking up HAdd.hAdd Nat Nat Nat inst 0 n should find Nat.zero_add
      (is (= 2 (ansatz.tactic.discr-tree/tree-size idx))))))

;; ============================================================
;; dsimp-expr + type annotation protection tests
;; ============================================================

(deftest test-dsimp-preserves-type-annotations
  (testing "dsimp-expr preserves type annotations (Bool, List Nat) in motives"
    (let [env (require-env)
          lctx {}
          bool-type (e/const' (name/from-string "Bool") [])
          nat-type (e/const' (name/from-string "Nat") [])
          list-nat (e/app (e/const' (name/from-string "List") [lvl/zero]) nat-type)
          ;; fun (_ : Bool) => Bool  (typical Bool.rec motive)
          motive (e/lam "_" bool-type bool-type :default)
          result (#'simp/dsimp-expr env lctx motive 20)]
      (is (= result motive) "dsimp preserves fun _ : Bool => Bool")
      ;; fun (_ : List Nat) => Bool  (typical List.rec motive)
      (let [list-motive (e/lam "_" list-nat bool-type :default)
            result2 (#'simp/dsimp-expr env lctx list-motive 20)]
        (is (= result2 list-motive) "dsimp preserves fun _ : List Nat => Bool")))))

(deftest test-simp-all-preserves-type-annotations
  (testing "simp_all doesn't corrupt Bool → True in hypothesis types"
    (let [env (require-env)
          st (tc/mk-tc-state env)
          nat (e/const' (name/from-string "Nat") [])
          bool (e/const' (name/from-string "Bool") [])
          fv-x (e/fvar 900001) fv-y (e/fvar 900002)
          ble-xy (e/app* (e/const' (name/from-string "Nat.ble") []) fv-x fv-y)
          bool-true (e/const' (name/from-string "Bool.true") [])
          hyp-type (e/app* (e/const' (name/from-string "Eq") [(lvl/succ lvl/zero)])
                           bool ble-xy bool-true)
          lctx {900001 {:tag :local :id 900001 :name "x" :type nat}
                900002 {:tag :local :id 900002 :name "y" :type nat}
                900003 {:tag :local :id 900003 :name "h" :type hyp-type}}
          st (assoc st :lctx lctx)
          ;; Simplify the hypothesis type
          lemmas (simp/make-simp-lemmas env ["Nat.ble_eq"])
          lemma-index (simp/build-lemma-index st env lemmas)
          config {:max-depth 10 :single-pass? false :decide? true
                  :max-steps (atom 0) :cache (atom {})
                  :to-unfold #{} :discharge-depth 0}
          result (#'simp/simp-expr* st env lemma-index hyp-type config)
          simplified (:expr result)
          [head args] (e/get-app-fn-args simplified)]
      ;; Check the Eq type parameter is NOT True
      (when (and (e/const? head) (= 3 (count args)))
        (is (not= (first args) (e/const' (name/from-string "True") []))
            "Eq type param should not be corrupted to True")))))
