(ns prototype.test-runner
  (:require [clojure.test :as t]
            [prototype.lean-ir-test]
            [prototype.mutable-test]
            [prototype.numeric-compile-test]
            [prototype.block-compile-test]
            [prototype.region-compile-test]))

(defn -main [& _]
  (let [result (t/run-tests 'prototype.lean-ir-test 'prototype.mutable-test
                            'prototype.numeric-compile-test 'prototype.block-compile-test
                            'prototype.region-compile-test)]
    (shutdown-agents)
    (when (pos? (+ (:fail result) (:error result))) (System/exit 1))))
