(ns generated-command-receipt-checks-v1
  "Pure structural/issuance negatives only; no compiler execution authority."
  (:require [clojure.test :refer [deftest is run-tests]]
            [generated-command-receipt-v1 :as receipt]))
(deftest unissued-batches-have-no-linking-or-summary-authority
  (doseq [x [nil {} {:compiled true} (receipt/->CodeBatch)]]
    (is (thrown? Exception (receipt/batch-summary x)))))
(deftest trusted-provider-requires-all-lifecycle-hooks
  (is (thrown? Exception (receipt/source-captures {})))
  (is (thrown? Exception (receipt/source-captures
                          {:check! identity :before-command! identity
                           :before-call! identity :after-taken! identity}))))
(deftest deadline-rebase-requires-issued-custody
  (doseq [x [nil {} (receipt/->CommandRun)]]
    (is (thrown? Exception (receipt/rebase-idle-deadline! x 60000)))))
(deftest owner-free-canonical-summary-cannot-hide-mutable-carriers
  (is (= {"a" [1 "safe"] "z" true}
         (#'receipt/frozen-host {:z true :a [1 :safe]})))
  (doseq [x [(Object.) (object-array [1]) (byte-array 1) (atom {}) #{1}
             {:same 1 "same" 2} (nth (iterate vector 0) 130)]]
    (is (thrown? Exception (#'receipt/frozen-host x)))))
(deftest exact-local-ir-domain-rejects-duplicates-and-externs
  (let [n ["str" ["anonymous"] "identity"] d {"fdecl" {"f" n}}]
    (is (= {n {"f" n}} (#'receipt/ir-map! [d])))
    (is (thrown? Exception (#'receipt/ir-map! [d d])))
    (is (thrown? Exception (#'receipt/ir-map! [{"extern" {"f" n}}])))))
(deftest static-runtime-frontier-is-explicit
  (let [n ["str" ["anonymous"] "identity"]]
    (is (= #{n} (#'receipt/static-calls! {"fap" {"c" n "ys" []}})))
    (is (= #{n} (#'receipt/static-calls! {"pap" {"c" n "ys" []}})))
    (is (thrown? Exception (#'receipt/static-calls! {"ap" {"x" 1}}))))
  (let [root ["str" ["anonymous"] "identity"] boxed ["str" root "_boxed"]
        x {"idx" 1} y {"idx" 2} argument (fn [id] {"var" {"id" id}})
        raw {"f" root "xs" [{"x" x "borrow" true "ty" "tobject"}]
             "type" "tobject" "body" ["inc" x 1 true false ["ret" (argument x)]]}
        wrapper {"f" boxed "xs" [{"x" x "borrow" false "ty" "tobject"}]
                 "type" "tobject" "body" ["vdecl" y "tobject" {"fap" {"c" root "ys" [(argument x)]}}
                                            ["dec" x 1 true false ["ret" (argument y)]]]}
        rows {root raw boxed wrapper}]
    (is (nil? (#'receipt/first-batch! rows root boxed)))
    (is (thrown? Exception (#'receipt/first-batch! (assoc-in rows [root "xs" 0 "borrow"] false) root boxed)))
    (is (thrown? Exception (#'receipt/first-batch! (assoc-in rows [boxed "xs" 0 "borrow"] true) root boxed)))
    (is (thrown? Exception (#'receipt/first-batch! (assoc-in rows [root "type"] "object") root boxed)))
    (is (thrown? Exception (#'receipt/first-batch! (assoc-in rows [boxed "body"] ["ret" (argument x)]) root boxed)))))
(defn check! [] (run-tests 'generated-command-receipt-checks-v1))
