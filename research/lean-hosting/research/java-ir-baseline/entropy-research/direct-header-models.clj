(ns java-entropy-original-random-direct-header-models-v1
  (:require [clojure.test :refer [deftest is run-tests]]
            [java-entropy-original-random-gate-v1 :as gate]))
(deftest occurrence-dependencies-are-not-the-external-header-borrow-set
  (let [self ["str" ["anonymous"] "self"] other ["str" ["anonymous"] "other"]
        another ["num" ["anonymous"] "7"]
        original {"name" self "dependencies" [self other other another self other]
                  "ir" {"fdecl" {"body" [{"fap" {"c" self}} {"fap" {"c" other}}
                                           {"pap" {"c" other}} {"fap" {"c" another}}]}}}
        before (get original "dependencies")]
    (is (= [other another] (gate/direct-names original)))
    (is (identical? before (get original "dependencies")))
    (is (= [self other other another self other] (get original "dependencies"))))
  (is (= [] (gate/direct-names {"name" ["anonymous"] "dependencies" [["anonymous"]]})))
  (is (thrown? Exception (gate/direct-names {"name" ["anonymous"] "dependencies" []
                                             "ir" {"fdecl" {"body" {"fap" {"c" ["anonymous"]}}}}}))))
(defn check! [] (run-tests 'java-entropy-original-random-direct-header-models-v1))
