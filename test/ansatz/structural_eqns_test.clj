(ns ansatz.structural-eqns-test
  "Structural equation theorems for a definition over an indexed family (Lean
   Elab/PreDefinition/Structural/Eqns.lean). Lean parity: test/lean-parity/dsl/structural_eqns.lean."
  (:require [clojure.test :refer [deftest testing is use-fixtures]]
            [clojure.string :as str]
            [ansatz.test-env :as test-env]
            [ansatz.core :as a]
            [ansatz.eqns :as eqns]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.tc :as tc]
            [ansatz.elab.structural-eqns :as structural-eqns]))

(defn- with-env [f]
  (let [saved @a/ansatz-env]
    (try (reset! a/ansatz-env @test-env/bundled-init-env)
         (binding [*ns* (the-ns 'ansatz.structural-eqns-test) a/*verbose* false]
           (eval '(ansatz.core/inductive SeqV [α Type] :indices [k Nat]
                                         (nil :where [0])
                                         (cons [n Nat] [x α] [xs (SeqV α n)] :where [(Nat.succ n)])))
           (eval '(ansatz.core/defn seqv-depth [α :- Type, n :- Nat, v :- (SeqV α n)] Nat
                    (match v (SeqV.nil) 0 (SeqV.cons m x xs) (+ (seqv-depth α m xs) 1))))
           (f))
         (finally (reset! a/ansatz-env saved)))))

(use-fixtures :once with-env)

(defn- ci [n] (env/lookup (a/env) (name/from-string n)))

(deftest indexed-family-equations
  (testing "eq_1, eq_2 and eq_def exist and are kernel-checked theorems"
    (doseq [n ["seqv-depth.eq_1" "seqv-depth.eq_2" "seqv-depth.eq_def"]]
      (is (some? (ci n)) n)
      (when (ci n) (is (env/verifies? (a/env) (.type (ci n)) (.value (ci n))) n))))
  (testing "eq_def unfolds the definition on a variable of the indexed family"
    (let [t (.type (ci "seqv-depth.eq_def"))
          body (loop [t t] (if (e/forall? t) (recur (e/forall-body t)) t))
          [_ lhs rhs] (e/get-app-args body)]
      (is (= "seqv-depth" (str (e/const-name (e/get-app-fn lhs)))))
      (is (every? e/bvar? (e/get-app-args lhs)) "f α n v on variables")
      (is (str/starts-with? (str (e/const-name (e/get-app-fn rhs))) "seqv-depth.match_"))))
  (testing "as in Lean, the unfolding equation needs a proof: the sides are not definitionally equal"
    (let [t (.type (ci "seqv-depth.eq_def"))
          ctx (ansatz.meta.constructions.util/context (a/env))
          [xs body] (ansatz.meta.constructions.util/forall-telescope ctx t)
          [_ lhs rhs] (e/get-app-args body)]
      (is (not (tc/is-def-eq @ctx lhs rhs)))))
  (testing "the proof rewrites with the `.brecOn.eq` theorem, as Lean's goUnfold does"
    (is (re-find #"SeqV\.brecOn\.eq" (e/->string (.value (ci "seqv-depth.eq_def")))))))

(deftest an-unprovable-unfold-equation-is-reported
  (testing "a failure is recorded with the definition's equation errors and printed"
    (let [err (java.io.StringWriter.)]
      (with-redefs [structural-eqns/unfold-equation (fn [& _] (throw (ex-info "injected eq_def failure" {})))]
        (binding [*err* err *ns* (the-ns 'ansatz.structural-eqns-test) a/*verbose* false]
          (eval '(ansatz.core/defn seqv-len [α :- Type, n :- Nat, v :- (SeqV α n)] Nat
                   (match v (SeqV.nil) 0 (SeqV.cons m x xs) (+ (seqv-len α m xs) 1))))))
      (is (re-find #"seqv-len\.eq_def" (str err)))
      (is (some #(= "seqv-len.eq_def" (:lemma %))
                (get (env/get-extension (a/env) :eqns-errors {}) (name/from-string "seqv-len")))))))
