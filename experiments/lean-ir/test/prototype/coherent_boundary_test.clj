(ns prototype.coherent-boundary-test
  (:require [clojure.test :refer [deftest is]]
            [prototype.coherent-jvm-slice :as slice]))

(deftest completed-spans-preserve-values-and-never-retain-them
  (let [state-var (ns-resolve 'prototype.coherent-jvm-slice 'state)
        boundary (ns-resolve 'prototype.coherent-jvm-slice 'boundary!)
        state (atom {:active-call :example}) value (Object.)]
    (with-redefs-fn {state-var state}
      #(do
         (is (identical? value (boundary :outer (fn [] (boundary :inner (fn [] value))))))
         (let [rows (slice/boundary-measurements)]
           (is (= [:inner :outer] (mapv :operation rows)))
           (is (every? (fn [row] (and (= :caller-thread (:scope row)) (:inclusive row)
                                     (= :example (:call row))
                                     (= #{:wall-ns :cpu-ns :allocated-bytes} (set (keys (:metrics row))))
                                     (not (contains? row :result)))) rows)))
         (let [failure (ex-info "partial guest operation" {})]
           (is (identical? failure (try (boundary :failed (fn [] (throw failure)))
                                       (catch Throwable e e))))
           (is (= 2 (count (slice/boundary-measurements)))))))))
