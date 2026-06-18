(ns ansatz.tactic.unify-test
  "Unit tests for the metavar-aware, reduction-aware is-def-eq! (Lean Meta.isDefEq analog)."
  (:require [clojure.test :refer [deftest testing is]]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.tc :as tc]
            [ansatz.tactic.unify :as u]
            [ansatz.export.parser :as parser]
            [ansatz.export.replay :as replay]))

(def ^:private init-medium-env
  (delay
    (let [f "test-data/init-medium.ndjson"]
      (when (.exists (java.io.File. f))
        (:env (replay/replay (:decls (parser/parse-ndjson-file f))))))))

(defn- require-env []
  (or @init-medium-env (throw (ex-info "init-medium.ndjson not found" {}))))

(defn- c [s] (e/const' (name/from-string s) []))
(defn- nadd [a b] (e/app* (c "Nat.add") a b))

(deftest test-bare-mvar-assign
  (testing "a bare metavariable unifies with any term and gets assigned"
    (let [env (require-env)
          st (tc/mk-tc-state env)
          mctx (atom {})
          m (u/fresh-mvar! mctx 1000 (c "Nat"))]
      (is (u/is-def-eq! st mctx m (e/lit-nat 5)))
      (is (= (e/lit-nat 5) (u/zonk mctx m))))))

(deftest test-app-with-mvar
  (testing "Nat.add ?x 0 unifies with Nat.add 3 0, binding ?x := 3"
    (let [env (require-env)
          st (tc/mk-tc-state env)
          mctx (atom {})
          m (u/fresh-mvar! mctx 1001 (c "Nat"))]
      (is (u/is-def-eq! st mctx (nadd m (e/lit-nat 0)) (nadd (e/lit-nat 3) (e/lit-nat 0))))
      (is (= (e/lit-nat 3) (u/zonk mctx m))))))

(deftest test-mvar-free-delegates-to-kernel
  (testing "no metavariables → reduction-based kernel defeq (Nat.add 2 3 ≡ 5)"
    (let [env (require-env)
          st (tc/mk-tc-state env)
          mctx (atom {})]
      (is (u/is-def-eq! st mctx (nadd (e/lit-nat 2) (e/lit-nat 3)) (e/lit-nat 5)))
      (is (not (u/is-def-eq! st mctx (e/lit-nat 4) (e/lit-nat 5)))))))

(deftest test-whnf-retry-then-assign
  (testing "reduction is applied before assignment: id ?x ≡ 5 reduces id then assigns ?x := 5"
    (let [env (require-env)
          ;; reducible abbrev  Test.id : Nat → Nat := fun n => n
          natC (c "Nat")
          idval (e/lam "n" natC (e/bvar 0) :default)
          idty (e/forall' "n" natC natC :default)
          env2 (env/check-constant env (env/mk-def (name/from-string "Test.id") [] idty idval :hints :abbrev))
          st (tc/mk-tc-state env2)
          mctx (atom {})
          m (u/fresh-mvar! mctx 1002 natC)
          idapp (e/app (c "Test.id") m)]
      (is (u/is-def-eq! st mctx idapp (e/lit-nat 5)))
      (is (= (e/lit-nat 5) (u/zonk mctx m))))))

(deftest test-occurs-check-rejects
  (testing "occurs check: ?x cannot be assigned a term containing ?x"
    (let [env (require-env)
          st (tc/mk-tc-state env)
          mctx (atom {})
          m (u/fresh-mvar! mctx 1003 (c "Nat"))]
      ;; ?x =?= Nat.add ?x 0  → must fail (occurs)
      (is (not (u/is-def-eq! st mctx m (nadd m (e/lit-nat 0))))))))

(deftest test-mismatch-fails
  (testing "genuinely distinct closed terms do not unify"
    (let [env (require-env)
          st (tc/mk-tc-state env)
          mctx (atom {})
          m (u/fresh-mvar! mctx 1004 (c "Nat"))]
      ;; Nat.add ?x 1  vs  Nat.add 3 2  → arg mismatch 1≠2
      (is (not (u/is-def-eq! st mctx (nadd m (e/lit-nat 1)) (nadd (e/lit-nat 3) (e/lit-nat 2))))))))
