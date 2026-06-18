(ns ansatz.prelude.algebra-test
  "Phase 1 of the wandler reimpl: the owned algebraic spine verifies end-to-end."
  (:require [clojure.test :refer [deftest testing is use-fixtures]]
            [ansatz.core :as a]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [ansatz.export.parser :as parser]
            [ansatz.export.replay :as replay]
            [ansatz.prelude.algebra :as alg]))

(def ^:private init-medium-env
  (delay
    (let [f "test-data/init-medium.ndjson"]
      (when (.exists (java.io.File. f))
        (:env (replay/replay (:decls (parser/parse-ndjson-file f))))))))

(defn- with-env [t]
  (when-let [e @init-medium-env] (reset! a/ansatz-env e))
  (t))
(use-fixtures :once with-env)
(defn- ready? [] (some? @init-medium-env))
(defn- has? [s] (some? (env/lookup (a/env) (name/from-string s))))

(deftest classes-install
  (when (ready?)
    (testing "WAddMonoid ⊂ WSemiring define into the env"
      (alg/install-classes!)
      (is (has? "WAddMonoid"))
      (is (has? "WSemiring"))
      (is (has? "WSemiring.mul"))
      (is (has? "WSemiring.add") "inherited accessor (subobject)")
      (is (has? "WSemiring.toWAddMonoid") "packed parent projection"))))

(deftest nat-instance-verifies
  (when (ready?)
    (testing "the Nat WSemiring instance kernel-verifies through the subobject"
      (let [r (alg/install-instance! "Nat" alg/nat-row)]
        (is (= :verified (:status r)) (str "expected :verified, got " r))
        (is (has? "instWAddMonoid_Nat"))
        (is (has? "instWSemiring_Nat"))))))
