(ns general-command-receipt-checks-v1
  "Pure bounds/IR/capability models. No actual parser or CommandReceipt issuance."
  (:require [clojure.test :refer [deftest is run-tests]]
            [general-command-receipt-v1 :as command]
            [ansatz.research.ir.node-decoder-v1 :as decoder]))
(deftest generic-decoder-policy-cannot-exceed-real-decoder-ceilings
  (let [limits (#'command/decode-limits)]
    (doseq [[key value] (dissoc limits :deadline-nanos)]
      (is (and (integer? value) (pos? value) (<= value (get decoder/defaults key)))))
    (is (integer? (:deadline-nanos limits)))
    (is (= 2000000 (:max-chars limits)))))
(deftest complete-ir-map-keeps-empty-code-and-unsupported-execution-kinds
  (let [a ["str" ["anonymous"] "a"] b ["str" ["anonymous"] "b"]
        f {"fdecl" {"f" a "xs" [] "type" "tobject"}}
        e {"extern" {"f" b "xs" [] "type" "tobject"}}]
    (is (= {} (#'command/ir-map! [] 2)))
    (is (= {a {:kind "fdecl" :declaration (get f "fdecl")}
            b {:kind "extern" :declaration (get e "extern")}}
           (#'command/ir-map! [f e] 2)))
    (is (thrown? Exception (#'command/ir-map! [f f] 2)))
    (is (thrown? Exception (#'command/ir-map! [f e] 1)))
    (is (thrown? Exception (#'command/ir-map! [{"unknown" {"f" a}}] 2)))))
(deftest unissued-runs-and-summaries-cannot-authorize-batches
  (doseq [value [nil {} {:status :sealed} (command/->CommandRun) (command/->CommandReceipt)]]
    (is (thrown? Exception (command/with-command! value identity)))
    (is (thrown? Exception (command/owner-packet value)))))
(defn check! [] (run-tests 'general-command-receipt-checks-v1))
