(ns cic.surface.match-test
  "Tests for match expression compilation and theorem/def macros."
  (:require [clojure.test :refer [deftest testing is use-fixtures]]
            [cic.kernel.expr :as e]
            [cic.kernel.env :as env]
            [cic.kernel.name :as name]
            [cic.kernel.level :as lvl]
            [cic.kernel.reduce :as red]
            [cic.kernel.tc :as tc]
            [cic.surface.elaborate :as elab]
            [cic.surface.match :as match]
            [cic.tactic.proof :as proof]
            [cic.tactic.basic :as basic]
            [cic.tactic.extract :as extract]
            [cic.tactic.repl :as repl]
            [cic.export.parser :as parser]
            [cic.export.replay :as replay])
  (:import [cic.kernel TypeChecker]))

;; ============================================================
;; Test environment
;; ============================================================

(def ^:private init-medium-env
  (delay
    (let [f "test-data/init-medium.ndjson"]
      (when (.exists (java.io.File. f))
        (let [st (parser/parse-ndjson-file f)
              result (replay/replay (:decls st))]
          (:env result))))))

(defn- require-env []
  (let [env @init-medium-env]
    (when-not env
      (throw (ex-info "init-medium.ndjson not found" {})))
    env))

(defn- whnf [env expr]
  (red/whnf env expr))

;; ============================================================
;; Match expression tests
;; ============================================================

(deftest test-bool-match
  (testing "Match on Bool constants"
    (let [env (require-env)]
      (let [r (whnf env (elab/elaborate env '(match Bool.true
                                               [Bool.false 0]
                                               [Bool.true 1])))]
        (is (e/lit-nat? r))
        (is (= 1 (e/lit-nat-val r))))
      (let [r (whnf env (elab/elaborate env '(match Bool.false
                                               [Bool.false 0]
                                               [Bool.true 1])))]
        (is (e/lit-nat? r))
        (is (= 0 (e/lit-nat-val r)))))))

(deftest test-nat-match-zero-succ
  (testing "Match on Nat with zero and succ patterns"
    (let [env (require-env)]
      ;; match 0 [zero => 10] [(succ n) => n]
      (let [r (whnf env (elab/elaborate env '(match Nat.zero
                                               [Nat.zero 10]
                                               [(Nat.succ n) n])))]
        (is (e/lit-nat? r))
        (is (= 10 (e/lit-nat-val r))))
      ;; match (succ (succ 0)) [zero => 10] [(succ n) => n]
      (let [r (whnf env (elab/elaborate env '(match (Nat.succ (Nat.succ Nat.zero))
                                               [Nat.zero 10]
                                               [(Nat.succ n) n])))]
        (is (e/lit-nat? r))
        (is (= 1 (e/lit-nat-val r)))))))

(deftest test-nat-literal-patterns
  (testing "Nat literal patterns desugar to zero/succ chains"
    (let [env (require-env)]
      (let [r0 (whnf env (elab/elaborate env '(match Nat.zero
                                                [0 100] [1 200] [_ 999])))
            r1 (whnf env (elab/elaborate env '(match (Nat.succ Nat.zero)
                                                [0 100] [1 200] [_ 999])))
            r2 (whnf env (elab/elaborate env '(match (Nat.succ (Nat.succ Nat.zero))
                                                [0 100] [1 200] [_ 999])))]
        (is (= 100 (e/lit-nat-val r0)))
        (is (= 200 (e/lit-nat-val r1)))
        (is (= 999 (e/lit-nat-val r2)))))))

(deftest test-wildcard-pattern
  (testing "Wildcard pattern matches any constructor"
    (let [env (require-env)]
      (let [r (whnf env (elab/elaborate env '(match (Nat.succ Nat.zero)
                                               [_ 42])))]
        (is (e/lit-nat? r))
        (is (= 42 (e/lit-nat-val r)))))))

(deftest test-match-in-lambda
  (testing "Match inside a lambda abstracts correctly"
    (let [env (require-env)
          term (elab/elaborate env '(lam [b Bool]
                                     (match b
                                       [Bool.false 0]
                                       [Bool.true 1])))
          st (tc/mk-tc-state env)
          ty (tc/infer-type st term)]
      ;; Type should be Bool → Nat (after WHNF)
      (is (e/forall? ty))
      ;; Apply to Bool.true and reduce
      (let [applied (e/app term (e/const' (name/from-string "Bool.true") []))
            reduced (whnf env applied)]
        (is (= 1 (e/lit-nat-val reduced)))))))

(deftest test-match-type-checks
  (testing "Match result type-checks via kernel TypeChecker"
    (let [env (require-env)
          term (elab/elaborate env '(match (Nat.succ Nat.zero)
                                     [Nat.zero 0]
                                     [(Nat.succ n) n]))
          tc (TypeChecker. env)
          inferred (.inferType tc term)]
      ;; Should type-check without error
      (is (some? inferred)))))

(deftest test-list-match
  (testing "Match on List with head extraction"
    (let [env (require-env)
          list-nat (e/app (e/const' (name/from-string "List") [lvl/zero])
                          (e/const' (name/from-string "Nat") []))
          ;; Build: λ (xs : List Nat) => match xs [nil => 0] [(cons x _) => x]
          term (elab/elaborate-in-context
                env
                {42 {:tag :local :name "xs" :type list-nat}}
                '(match xs
                   [List.nil 0]
                   [(List.cons x _) x]))
          ;; Type check in context
          st (tc/mk-tc-state env)
          st (assoc st :lctx (red/lctx-add-local {} 42 "xs" list-nat))
          ty (tc/infer-type st term)
          ty-whnf (whnf env ty)]
      ;; Return type should be Nat
      (is (e/const? ty-whnf))
      (is (= (name/from-string "Nat") (e/const-name ty-whnf))))))

;; ============================================================
;; Nested pattern tests
;; ============================================================

(deftest test-nested-nat-patterns
  (testing "Nested Nat patterns (matching specific successor depths)"
    (let [env (require-env)]
      ;; match n [0 => "zero"] [(succ 0) => "one"] [(succ (succ _)) => "many"]
      ;; Using Nat return type since strings require more setup
      (let [r0 (whnf env (elab/elaborate env '(match Nat.zero
                                                [0 0]
                                                [(Nat.succ Nat.zero) 1]
                                                [(Nat.succ (Nat.succ _)) 2])))
            r1 (whnf env (elab/elaborate env '(match (Nat.succ Nat.zero)
                                                [0 0]
                                                [(Nat.succ Nat.zero) 1]
                                                [(Nat.succ (Nat.succ _)) 2])))
            r2 (whnf env (elab/elaborate env '(match (Nat.succ (Nat.succ Nat.zero))
                                                [0 0]
                                                [(Nat.succ Nat.zero) 1]
                                                [(Nat.succ (Nat.succ _)) 2])))
            r5 (whnf env (elab/elaborate env '(match (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))))
                                                [0 0]
                                                [(Nat.succ Nat.zero) 1]
                                                [(Nat.succ (Nat.succ _)) 2])))]
        (is (= 0 (e/lit-nat-val r0)))
        (is (= 1 (e/lit-nat-val r1)))
        (is (= 2 (e/lit-nat-val r2)))
        (is (= 2 (e/lit-nat-val r5)))))))

;; ============================================================
;; theorem and define macros
;; ============================================================

(deftest test-theorem-macro
  (testing "theorem macro defines and verifies a proof"
    (let [env (require-env)
          env' (repl/theorem env 'id_prop
                             '(forall [a Prop, h a] a)
                             (fn [ps]
                               (-> ps
                                   (repl/intro "a")
                                   (repl/intro "h")
                                   (repl/assumption))))]
      ;; The theorem should be in the environment
      (let [ci (env/lookup env' (name/from-string "id_prop"))]
        (is (some? ci))
        (is (env/thm? ci))))))

(deftest test-define-macro
  (testing "define macro adds a constant to the environment"
    (let [env (require-env)
          env' (repl/define env 'my_nat 'Nat '(Nat.succ Nat.zero))]
      (let [ci (env/lookup env' (name/from-string "my_nat"))]
        (is (some? ci))
        (is (env/def? ci))
        ;; The value should reduce to 1
        (let [val (env/ci-value ci)
              reduced (whnf env' val)]
          (is (= 1 (e/lit-nat-val reduced))))))))

;; ============================================================
;; Cross-stack test 1: Verified ground polynomial arithmetic
;; ============================================================

(deftest test-ground-polynomial
  (testing "Ground polynomial identity: (2+1)*(2+1) = 9 verified via decide"
    (let [env (require-env)
          ;; Prove: (2+1)*(2+1) = 9
          ;; This is a ground decidable Nat equality
          nat (e/const' (name/from-string "Nat") [])
          u1 (lvl/succ lvl/zero)
          two (e/app (e/const' (name/from-string "Nat.succ") [])
                     (e/app (e/const' (name/from-string "Nat.succ") [])
                            (e/const' (name/from-string "Nat.zero") [])))
          three (e/app (e/const' (name/from-string "Nat.succ") []) two)
          nine (e/lit-nat 9)
          ;; (2+1) = Nat.add 2 1
          add (e/const' (name/from-string "Nat.add") [])
          one (e/app (e/const' (name/from-string "Nat.succ") [])
                     (e/const' (name/from-string "Nat.zero") []))
          lhs (e/app* add two one)   ;; 2 + 1
          product (e/app* (e/const' (name/from-string "Nat.mul") [])
                          lhs lhs)     ;; (2+1) * (2+1)
          eq-type (e/app* (e/const' (name/from-string "Eq") [u1])
                          nat product nine)
          ;; Prove this via decide tactic
          ps (first (proof/start-proof env eq-type))]
      ;; This should be provable by kernel evaluation
      (let [ps' (repl/decide ps)]
        (is (proof/solved? ps'))
        ;; Verify the proof term
        (let [term (extract/verify ps')]
          (is (not (e/has-fvar-flag term))))))))

(deftest test-ground-polynomial-multiple
  (testing "Multiple ground identities: verified arithmetic"
    (let [env (require-env)
          nat (e/const' (name/from-string "Nat") [])
          u1 (lvl/succ lvl/zero)
          eq-name (name/from-string "Eq")
          add-name (name/from-string "Nat.add")
          mul-name (name/from-string "Nat.mul")]
      ;; Test several ground equalities
      (doseq [[a b result op-name desc]
              [[3 4 7 add-name "3 + 4 = 7"]
               [5 5 25 mul-name "5 * 5 = 25"]
               [0 100 0 mul-name "0 * 100 = 0"]
               [1 1 2 add-name "1 + 1 = 2"]]]
        (testing desc
          (let [lhs (e/app* (e/const' op-name [])
                            (e/lit-nat a) (e/lit-nat b))
                eq-type (e/app* (e/const' eq-name [u1])
                                nat lhs (e/lit-nat result))
                ps (first (proof/start-proof env eq-type))
                ps' (repl/decide ps)]
            (is (proof/solved? ps') (str "Failed: " desc))
            (extract/verify ps')))))))

;; ============================================================
;; Cross-stack test 2: Verified ODE error bound (Nat arithmetic)
;; ============================================================

(deftest test-ode-error-bound
  (testing "ODE step error bound: for step h, error ≤ h*h (ground check)"
    (let [env (require-env)
          nat (e/const' (name/from-string "Nat") [])
          u1 (lvl/succ lvl/zero)
          ;; Define: euler_error(h) = h (simplistic)
          ;; Bound: h ≤ h*h when h ≥ 1
          ;; For concrete h=3: prove 3 ≤ 3*3 = 9
          ;; Nat.ble 3 9 = true, so (Eq Bool (Nat.ble 3 9) Bool.true)
          ble (e/const' (name/from-string "Nat.ble") [])
          three (e/lit-nat 3)
          nine (e/lit-nat 9)
          ble-result (e/app* ble three nine)
          bool-true (e/const' (name/from-string "Bool.true") [])
          bool (e/const' (name/from-string "Bool") [])
          eq-type (e/app* (e/const' (name/from-string "Eq") [u1])
                          bool ble-result bool-true)
          ps (first (proof/start-proof env eq-type))
          ps' (repl/decide ps)]
      (is (proof/solved? ps'))
      (let [term (extract/verify ps')]
        (is (not (e/has-fvar-flag term)))))))

;; ============================================================
;; Cross-stack test 3: Verified rewrite rule lookup
;; ============================================================

(deftest test-rewrite-rule-lookup
  (testing "Look up Nat.add_comm from env and use in proof"
    (let [env (require-env)
          ;; Check if Nat.add_comm exists
          add-comm-ci (env/lookup env (name/from-string "Nat.add_comm"))]
      (when add-comm-ci
        ;; Nat.add_comm : ∀ (n m : Nat), n + m = m + n
        ;; Use it to prove: 0 + 1 = 1 + 0
        (let [nat (e/const' (name/from-string "Nat") [])
              u1 (lvl/succ lvl/zero)
              zero-n (e/const' (name/from-string "Nat.zero") [])
              one (e/app (e/const' (name/from-string "Nat.succ") []) zero-n)
              add (e/const' (name/from-string "Nat.add") [])
              lhs (e/app* add zero-n one)   ;; 0 + 1
              rhs (e/app* add one zero-n)   ;; 1 + 0
              eq-type (e/app* (e/const' (name/from-string "Eq") [u1])
                              nat lhs rhs)
              ;; Prove via: Nat.add_comm 0 1
              add-comm (e/const' (name/from-string "Nat.add_comm") [])
              proof (e/app* add-comm zero-n one)
              ps (first (proof/start-proof env eq-type))
              ps' (basic/exact ps proof)]
          (is (proof/solved? ps'))
          (let [term (extract/verify ps')]
            (is (not (e/has-fvar-flag term)))))))))

(deftest test-certified-rewrite
  (testing "Prove an identity and register it as a theorem for reuse"
    (let [env (require-env)
          add-comm-ci (env/lookup env (name/from-string "Nat.add_comm"))]
      (when add-comm-ci
        ;; Step 1: Prove 0 + n = n for all n (using Nat.zero_add if available,
        ;; or Nat.add_comm + simplification)
        (let [zero-add-ci (env/lookup env (name/from-string "Nat.zero_add"))]
          (when zero-add-ci
            ;; Register a derived theorem: ∀ n, 0 + n = n + 0
            (let [env' (repl/theorem env 'zero_add_comm
                                     '(forall [n Nat] (Eq (Nat.add Nat.zero n) (Nat.add n Nat.zero)))
                                     (fn [ps]
                                       (let [ps (repl/intro ps "n")
                                             ;; Use Nat.add_comm 0 n
                                             goal (proof/current-goal ps)
                                             n-fvar (e/fvar (first (keys (:lctx goal))))
                                             add-comm-term (e/app* (e/const' (name/from-string "Nat.add_comm")
                                                                             [])
                                                                   (e/const' (name/from-string "Nat.zero") [])
                                                                   n-fvar)]
                                         (basic/exact ps add-comm-term))))]
              ;; The theorem is registered
              (is (some? (env/lookup env' (name/from-string "zero_add_comm")))))))))))

;; ============================================================
;; Pattern parsing tests
;; ============================================================

(deftest test-pattern-parsing
  (testing "Pattern parsing correctly identifies constructors vs variables"
    (let [env (require-env)]
      ;; Nat.zero is a constructor
      (let [p (match/parse-pattern env 'Nat.zero)]
        (is (= :ctor (:tag p))))
      ;; 'n' is a variable
      (let [p (match/parse-pattern env 'n)]
        (is (= :var (:tag p))))
      ;; _ is a wildcard
      (let [p (match/parse-pattern env '_)]
        (is (= :wildcard (:tag p))))
      ;; 42 is a nat literal
      (let [p (match/parse-pattern env 42)]
        (is (= :lit-nat (:tag p)))
        (is (= 42 (:val p))))
      ;; (Nat.succ n) is a constructor with variable arg
      (let [p (match/parse-pattern env '(Nat.succ n))]
        (is (= :ctor (:tag p)))
        (is (= 1 (count (:args p))))
        (is (= :var (:tag (first (:args p)))))))))

(deftest test-non-exhaustive-error
  (testing "Non-exhaustive patterns throw an error"
    (let [env (require-env)]
      ;; Match on Nat with only zero case — succ is missing
      (is (thrown-with-msg? Exception #"non-exhaustive"
            (elab/elaborate env '(match Nat.zero
                                   [Nat.zero 0])))))))
