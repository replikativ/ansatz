(ns ansatz.tactic.sorry-test
  "`sorry` and `admit`, as in Lean v4.33.1; reference: test/lean/sorry.lean."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [clojure.string :as str]
            [ansatz.core :as a]
            [ansatz.export.writer :as w]
            [ansatz.fixtures :as fixtures]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]))

(use-fixtures :once fixtures/isolated-session
  (fn [f] (binding [*ns* (the-ns 'ansatz.tactic.sorry-test) a/*verbose* false]
            (a/load-init!) (f))))

(defn- prove
  "Prove a theorem; return the warnings it printed."
  [nm params goal tactics]
  (let [err (java.io.StringWriter.)]
    (binding [*err* err] (a/prove-theorem nm params goal tactics))
    (str err)))

(defn- value [nm] (.value (env/lookup (a/env) (name/from-string (str nm)))))

(deftest sorry-closes-the-goal-and-warns
  (testing "the tactic"
    (is (str/includes? (prove 'sorry-closes '[] '(= Nat 1 2) '[(sorry)])
                       "declaration uses `sorry`: sorry-closes"))
    (is (e/uses-const? (value 'sorry-closes) (name/from-string "sorryAx"))))
  (testing "admit is a synonym"
    (is (str/includes? (prove 'admit-closes '[] '(= Nat 1 2) '[(admit)])
                       "declaration uses `sorry`")))
  (testing "the term, at the goal's type"
    (is (str/includes? (prove 'term-sorry '[n :- Nat] '(= Nat (+ n 0) n) '[(exact sorry)])
                       "declaration uses `sorry`")))
  (testing "a proof without sorry does not warn"
    (is (= "" (prove 'no-sorry '[n :- Nat] '(= Nat n n) '[(rfl)])))))

(deftest each-sorry-is-unique
  (testing "Lean's unique sorry: two are not definitionally equal"
    (is (str/includes? (prove 'sorry-statement '[] '(= Nat sorry sorry) '[(sorry)]) "uses `sorry`")
        "the statement elaborates")
    (is (thrown-with-msg? Exception #"not definitionally equal"
                          (binding [*err* (java.io.StringWriter.)]
                            (a/prove-theorem 'unique-sorries '[] '(= Nat sorry sorry) '[(rfl)])))))
  (testing "it is applied to a fresh tag of type Lean.Name"
    (prove 'tagged-sorry '[] '(= Nat 3 4) '[(sorry)])
    (is (e/uses-const? (value 'tagged-sorry) (name/from-string "Lean.Name.num")))))

(deftest sorry-is-an-axiom-to-lean
  (prove 'exported-sorry '[] '(= Nat 5 6) '[(sorry)])
  (let [{:keys [axioms]} (w/write-closure! (a/env) ["exported-sorry"] (java.io.StringWriter.))]
    (is (some #{"sorryAx"} axioms) "the Lean re-check reports it, like #print axioms")))

(deftest a-definition-may-use-sorry
  (let [err (java.io.StringWriter.)]
    (binding [*err* err]
      (eval '(ansatz.core/defn sorry-fn [n :- Nat] Nat sorry)))
    (is (str/includes? (str err) "declaration uses `sorry`: sorry-fn")))
  (testing "running it is Lean's lean_sorry panic"
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"executed 'sorry'"
                          ((ns-resolve 'ansatz.tactic.sorry-test 'sorry-fn) 3)))))
