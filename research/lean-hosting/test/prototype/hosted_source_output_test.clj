(ns prototype.hosted-source-output-test
  "Replay actual hosted A/B compiler output, not module import or kernel proofs.
   The real guest import/check/compile evidence is hosted-source-import.json;
   these small worlds intentionally carry no manufactured source authority."
  (:require [clojure.test :refer [deftest is]]
            [prototype.machine :as m] [prototype.program-install :as install]
            [prototype.raw-interop :as raw]))

(deftest actual-two-file-output-replays-without-replacing-a-or-running-initializers
  (doseq [backend [:reference :mutable :jvm]]
    (let [a (install/install (m/world {}) (slurp "fixtures/hosted/PreludeIdentity.ir.jsonl"))
          before (:world a)
          b (install/install before (slurp "fixtures/hosted/PreludeSecond.ir.jsonl"))
          world (:world b)
          target (get (:boxed-entrypoints b) ["str" ["anonymous"] "second"])
          session (raw/open-functions (:functions world) {} {:backend backend})
          [world child] (m/allocate world :ctor 0 [])
          [world value] (m/allocate world :ctor 7 [child])
          scalar (raw/call session world target [m/erased 42])
          left (raw/call session world target [m/erased value])
          right (raw/call session world target [m/erased value])]
      (is (= 42 (:value scalar)))
      (is (every? (fn [[name function]] (identical? function (get-in world [:functions name])))
                  (:functions before)))
      (is (empty? (:pending-local-initializers a)))
      (is (empty? (:pending-local-initializers b)))
      (is (= value (:value left) (:value right)))
      (is (= (:state left) (:state right)))
      (is (= 1 (:rc (m/node world value))))
      (is (empty? (:heap (m/release (:state left) value 1)))))))
