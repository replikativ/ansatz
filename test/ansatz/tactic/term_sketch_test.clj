(ns ansatz.tactic.term-sketch-test
  (:require [clojure.test :refer [deftest is testing]]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.name :as name]
            [ansatz.tactic.proof :as proof]
            [ansatz.tactic.term-sketch :as term-sketch]))

(def prop (e/sort' lvl/zero))

(defn- prop-id-goal []
  ;; forall (a : Prop), a -> a
  (e/forall' "a" prop
             (e/forall' "h" (e/bvar 0) (e/bvar 1) :default)
             :default))

(deftest lambda-hole-is-filled-by-tactic-search
  (testing "a term-level hole delegates to sketch/search under introduced binders"
    (let [result (term-sketch/solve-term-sketch
                  (env/empty-env)
                  (prop-id-goal)
                  '(lam [a Prop] (lam [h a] _))
                  {:max-steps 12
                   :beam-width 4
                   :verify? true})]
      (is (= :solved (:status result)))
      (is (proof/solved? (:ps result)))
      (is (some? (:proof result)))
      (is (= [:intro :intro :assumption]
             (mapv :name (:path result)))))))

(deftest lambda-concrete-body-is-elaborated-as-exact
  (testing "a non-hole leaf is elaborated in the current local context"
    (let [result (term-sketch/solve-term-sketch
                  (env/empty-env)
                  (prop-id-goal)
                  '(lam [a Prop h a] h)
                  {:max-steps 4
                   :verify? true})]
      (is (= :solved (:status result)))
      (is (proof/solved? (:ps result)))
      (is (= [:intro :intro :exact-term]
             (mapv :name (:path result)))))))

(deftest top-level-hole-can-use-env-premise
  (testing "term sketches can start as a bare hole and use env premise search"
    (let [p-name (name/from-string "p")
          env (env/add-constant (env/empty-env) (env/mk-axiom p-name [] prop))
          result (term-sketch/solve-term-sketch env prop '_
                                                {:max-steps 4
                                                 :beam-width 4
                                                 :premise-limit 4
                                                 :verify? true})]
      (is (= :solved (:status result)))
      (is (= [:exact-const] (mapv :name (:path result))))
      (is (= ["p"] (get-in result [:path 0 :args]))))))

(deftest lambda-binder-annotation-is-checked
  (testing "term-sketch annotations must match the expected Pi domain"
    (is (thrown-with-msg?
         clojure.lang.ExceptionInfo
         #"Binder annotation does not match expected goal domain"
         (term-sketch/solve-term-sketch
          (env/empty-env)
          (prop-id-goal)
          '(lam [a Type] (lam [h a] h))
          {:verify? false})))))
