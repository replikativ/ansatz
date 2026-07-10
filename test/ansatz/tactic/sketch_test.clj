(ns ansatz.tactic.sketch-test
  (:require [clojure.test :refer [deftest is testing]]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.name :as name]
            [ansatz.tactic.proof :as proof]
            [ansatz.tactic.sketch :as sketch]))

(def prop (e/sort' lvl/zero))

(defn- prop-id-goal []
  ;; forall (a : Prop), a -> a
  (e/forall' "a" prop
             (e/forall' "h" (e/bvar 0) (e/bvar 1) :default)
             :default))

(deftest sketch-prefix-with-holes-solves-prop-id
  (testing "holes delegate to ordinary tactic search"
    (let [[ps _] (proof/start-proof (env/empty-env) (prop-id-goal))
          result (sketch/solve-sketch ps [[:intro "a"] '_ '_]
                                      {:max-steps 20
                                       :beam-width 6
                                       :verify? true})]
      (is (= :solved (:status result)))
      (is (proof/solved? (:ps result)))
      (is (= [:intro :intro :assumption]
             (mapv :name (:path result))))
      (is (= :sketch (get-in result [:path 0 :source]))))))

(deftest sketch-exact-elaborates-local-hypothesis
  (testing "exact terms are elaborated against the current local context"
    (let [[ps _] (proof/start-proof (env/empty-env) (prop-id-goal))
          result (sketch/solve-sketch ps [[:intro "a"] [:intro "h"] [:exact 'h]]
                                      {:max-steps 8
                                       :beam-width 4
                                       :verify? true})]
      (is (= :solved (:status result)))
      (is (= [:intro :intro :exact-term]
             (mapv :name (:path result))))
      (is (= ["h"] (get-in result [:path 2 :args]))))))

(deftest sketch-exact-elaborates-env-constant
  (testing "exact terms can refer to constants in the proof state's env"
    (let [id-name (name/from-string "idP")
          env (env/add-constant (env/empty-env)
                                (env/mk-axiom id-name [] (prop-id-goal)))
          [ps _] (proof/start-proof env (prop-id-goal))
          result (sketch/solve-sketch ps [[:exact 'idP]]
                                      {:max-steps 4
                                       :beam-width 2
                                       :verify? true})]
      (is (= :solved (:status result)))
      (is (= [:exact-term] (mapv :name (:path result))))
      (is (= ["idP"] (get-in result [:path 0 :args]))))))

(deftest sketch-after-stop-exhausts-when-unsolved
  (testing "a consumed sketch can intentionally stop instead of falling back"
    (let [[ps _] (proof/start-proof (env/empty-env) (prop-id-goal))
          result (sketch/solve-sketch ps [[:intro "a"]]
                                      {:max-steps 8
                                       :beam-width 4
                                       :verify? false
                                       :sketch-after :stop})]
      (is (= :exhausted (:status result)))
      (is (= 1 (count (:transitions result))))
      (is (false? (get-in result [:transitions 0 :after :solved?]))))))
