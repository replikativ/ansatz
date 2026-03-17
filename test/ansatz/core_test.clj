(ns ansatz.core-test
  "Tests for the public API: defn, theorem, inductive.
   Uses init-medium.ndjson (2997 declarations, ~1.5s load)."
  (:require [clojure.test :refer [deftest testing is use-fixtures]]
            [ansatz.core :as a]
            [ansatz.export.storage :as storage]
            [ansatz.export.parser :as parser]
            [ansatz.export.replay :as replay]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]))

;; ============================================================
;; Environment setup
;; ============================================================

(def ^:private init-medium-env
  (delay
    (let [f "test-data/init-medium.ndjson"]
      (when (.exists (java.io.File. f))
        (let [st (parser/parse-ndjson-file f)
              env (:env (replay/replay (:decls st)))]
          env)))))

(defn- require-env []
  (or @init-medium-env
      (throw (ex-info "test-data/init-medium.ndjson not found" {}))))

(defn- with-env [f]
  (let [env (require-env)]
    (reset! a/ansatz-env env)
    ;; Load instance index from TSV if available, otherwise build
    (let [tsv "resources/instances.tsv"
          load-tsv (requiring-resolve 'ansatz.tactic.instance/load-instance-tsv)
          build-fn (requiring-resolve 'ansatz.tactic.instance/build-instance-index)
          idx (if (.exists (java.io.File. tsv))
                (load-tsv tsv)
                (build-fn env))]
      (reset! a/ansatz-instance-index idx))
    (binding [a/*verbose* false]
      (f))))

(use-fixtures :once with-env)

;; ============================================================
;; defn tests
;; ============================================================

(deftest test-defn-identity
  (testing "Define identity function on Nat"
    (binding [a/*verbose* false]
      (let [f (a/define-verified 'id-nat '[n Nat] 'Nat 'n)]
        (is (fn? f))
        (is (= 42 (f 42)))
        (is (= 0 (f 0)))))))

(deftest test-defn-addition
  (testing "Define addition function on Nat"
    (binding [a/*verbose* false]
      (let [f (a/define-verified 'add-nat '[a Nat b Nat] 'Nat '(+ a b))]
        (is (fn? f))
        (is (= 5 ((f 2) 3)))
        (is (= 0 ((f 0) 0)))))))

(deftest test-defn-with-separator
  (testing "Define function using :- separator syntax"
    (binding [a/*verbose* false]
      (let [f (a/define-verified 'double '[n :- Nat] 'Nat '(+ n n))]
        (is (fn? f))
        (is (= 10 (f 5)))))))

;; ============================================================
;; theorem tests
;; ============================================================

(deftest test-theorem-rfl
  (testing "Prove trivial equality by rfl"
    (binding [a/*verbose* false]
      (a/prove-theorem 'eq-rfl '[n Nat] '(= Nat n n) '[(rfl)])
      (is true "theorem proved"))))

(deftest test-theorem-simp
  (testing "Prove Nat.add_zero by simp"
    (binding [a/*verbose* false]
      (a/prove-theorem 'add-zero-test '[n Nat] '(= Nat (+ n 0) n) '[(simp "Nat.add_zero")])
      (is true "theorem proved"))))

(deftest test-theorem-assumption
  (testing "Prove by assumption"
    (binding [a/*verbose* false]
      (a/prove-theorem 'assume-test '[n Nat h (= Nat n n)] '(= Nat n n) '[(assumption)])
      (is true "theorem proved"))))

(deftest test-theorem-induction
  (testing "Prove by induction on Nat"
    (binding [a/*verbose* false]
      (a/prove-theorem 'add-zero-ind '[n Nat] '(= Nat (+ n 0) n)
                       '[(induction n) (rfl) (simp "Nat.add_succ")])
      (is true "theorem proved"))))

(deftest test-theorem-with-separator
  (testing "Prove theorem using :- separator syntax"
    (binding [a/*verbose* false]
      (a/prove-theorem 'rfl-sep '[n :- Nat] '(= Nat n n) '[(rfl)])
      (is true "theorem proved"))))

;; ============================================================
;; inductive tests
;; ============================================================

(deftest test-inductive-simple
  (testing "Define simple enumeration type"
    (binding [a/*verbose* false]
      (let [ind-fn (requiring-resolve 'ansatz.inductive/define-inductive)]
        (ind-fn (a/env) "TestColor" '[] '[["red" []] ["green" []] ["blue" []]])
        (is (some? (env/lookup (a/env) (name/from-string "TestColor")))
            "TestColor type should exist in env")
        (is (some? (env/lookup (a/env) (name/from-string "TestColor.red")))
            "TestColor.red constructor should exist")))))

;; ============================================================
;; Error handling tests
;; ============================================================

(deftest test-theorem-fails-on-wrong-tactic
  (testing "Wrong tactic application throws"
    (binding [a/*verbose* false]
      (is (thrown? clojure.lang.ExceptionInfo
                   (a/prove-theorem 'bad-proof '[n Nat] '(= Nat (+ n 1) n) '[(rfl)]))))))

(deftest test-theorem-fails-wrong-tactic
  (testing "Wrong tactic throws"
    (binding [a/*verbose* false]
      (is (thrown? clojure.lang.ExceptionInfo
                   (a/prove-theorem 'bad-tac '[n Nat] '(= Nat n n) '[(omega-nonexistent)]))))))
