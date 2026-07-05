(ns ansatz.tactic.unify-test
  "Unit tests for metavariable-aware, reduction-aware unification
   (Lean Meta.isDefEq analog, `ansatz.meta/is-def-eq`)."
  (:require [clojure.test :refer [deftest testing is]]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.tc :as tc]
            [ansatz.meta :as meta]
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

(defn- fresh-ctx [id type]
  (meta/add-expr-mvar-decl meta/empty-context id type {}))

(deftest test-bare-mvar-assign
  (testing "a bare metavariable unifies with any term and gets assigned"
    (let [env (require-env)
          st (tc/mk-tc-state env)
          mctx (fresh-ctx 1000 (c "Nat"))
          solved (meta/is-def-eq mctx st (e/mvar 1000) (e/lit-nat 5))]
      (is solved)
      (is (= (e/lit-nat 5) (meta/zonk-expr solved (e/mvar 1000)))))))

(deftest test-app-with-mvar
  (testing "Nat.add ?x 0 unifies with Nat.add 3 0, binding ?x := 3"
    (let [env (require-env)
          st (tc/mk-tc-state env)
          mctx (fresh-ctx 1001 (c "Nat"))
          solved (meta/is-def-eq mctx st
                                 (nadd (e/mvar 1001) (e/lit-nat 0))
                                 (nadd (e/lit-nat 3) (e/lit-nat 0)))]
      (is solved)
      (is (= (e/lit-nat 3) (meta/zonk-expr solved (e/mvar 1001)))))))

(deftest test-mvar-free-delegates-to-kernel
  (testing "no metavariables → reduction-based kernel defeq (Nat.add 2 3 ≡ 5)"
    (let [env (require-env)
          st (tc/mk-tc-state env)]
      (is (meta/is-def-eq meta/empty-context st
                          (nadd (e/lit-nat 2) (e/lit-nat 3)) (e/lit-nat 5)))
      (is (nil? (meta/is-def-eq meta/empty-context st
                                (e/lit-nat 4) (e/lit-nat 5)))))))

(deftest test-whnf-retry-then-assign
  (testing "reduction is applied before assignment: id ?x ≡ 5 reduces id then assigns ?x := 5"
    (let [env (require-env)
          natC (c "Nat")
          idval (e/lam "n" natC (e/bvar 0) :default)
          idty (e/forall' "n" natC natC :default)
          env2 (env/check-constant env (env/mk-def (name/from-string "Test.id") [] idty idval :hints :abbrev))
          st (tc/mk-tc-state env2)
          mctx (fresh-ctx 1002 natC)
          solved (meta/is-def-eq mctx st (e/app (c "Test.id") (e/mvar 1002)) (e/lit-nat 5))]
      (is solved)
      (is (= (e/lit-nat 5) (meta/zonk-expr solved (e/mvar 1002)))))))

(deftest test-reducing-self-equation-does-not-assign
  (testing "?x ≡ Nat.add ?x 0 succeeds by reduction without a cyclic assignment"
    (let [env (require-env)
          st (tc/mk-tc-state env)
          mctx (fresh-ctx 1005 (c "Nat"))
          solved (meta/is-def-eq mctx st (e/mvar 1005) (nadd (e/mvar 1005) (e/lit-nat 0)))]
      (is solved)
      (is (nil? (meta/expr-assignment solved 1005))))))

(deftest test-occurs-check-rejects
  (testing "occurs check: ?x cannot be assigned a term containing ?x"
    (let [env (require-env)
          st (tc/mk-tc-state env)
          mctx (fresh-ctx 1003 (c "Nat"))]
      ;; ?x =?= Nat.add 0 ?x  → must fail (occurs; unlike Nat.add ?x 0, this is stuck)
      (is (nil? (meta/is-def-eq mctx st (e/mvar 1003)
                                (nadd (e/lit-nat 0) (e/mvar 1003))))))))

(deftest test-mismatch-fails
  (testing "genuinely distinct closed terms do not unify"
    (let [env (require-env)
          st (tc/mk-tc-state env)
          mctx (fresh-ctx 1004 (c "Nat"))]
      ;; Nat.add ?x 1  vs  Nat.add 3 2  → arg mismatch 1≠2
      (is (nil? (meta/is-def-eq mctx st
                                (nadd (e/mvar 1004) (e/lit-nat 1))
                                (nadd (e/lit-nat 3) (e/lit-nat 2))))))))
