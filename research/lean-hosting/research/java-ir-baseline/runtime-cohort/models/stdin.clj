(ns original-stdin-configuration-checks-v1
  "Pure fixed-source/early-rejection models; no real default stream/engine setup."
  (:require [clojure.test :refer [deftest is]] [original-stdin-configuration-v1 :as stdin]
            [java-ir-baseline :as j] [ansatz.research.ir.source-setup :as source]
            [ansatz.research.ir.authenticated-demand :as demand] [sequential-frontend-probe :as sp]))
(deftest fixed-factory-and-six-method-pins-are-distinct
  (is (= 9 (count stdin/pins)))
  (is (= 9 (count (set (map first stdin/pins)))))
  (is (every? #(re-matches #"[0-9a-f]{64}" (second %)) stdin/pins)))
(deftest source-header-authentication-and-preconstruction-rejection
  (let [binding (Object.) token (Object.) journal (atom {})
        child {:code-receipt (Object.) :lab-heartbeat-provider token
               :driver {:source binding :lab-heartbeat-provider token :current-ctx (atom {}) :engine (Object.)}
               :startup-status (atom {:state :pending})}]
    (is (thrown? clojure.lang.ExceptionInfo (stdin/configure-child! child journal)))
    (is (empty? @journal))
    (with-redefs [source/guard-source! (fn [_ actual] (is (identical? binding actual)))
                  j/phase (fn [_ _] "idle") j/request-value (fn [h k] (get h k))
                  demand/ensure-header! (fn [_ name]
                                         (let [[_ sha] (first (filter #(= name (sp/typed-name (first %))) stdin/pins))]
                                           {"name" name "originalSha256" sha "source" binding "kind" "fdecl"}))]
      (is (= 9 (count (#'stdin/headers! child))))
      (with-redefs [demand/ensure-header! (fn [_ name] {"name" name "originalSha256" (apply str (repeat 64 "0")) "source" binding "kind" "fdecl"})]
        (is (thrown? clojure.lang.ExceptionInfo (#'stdin/headers! child)))))))
