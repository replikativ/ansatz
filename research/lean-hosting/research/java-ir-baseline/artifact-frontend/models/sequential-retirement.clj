(ns sequential-retirement-checks-v1
  "Owner-journal/preflight models only; actual callback release is not simulated
   as a successful guest cleanup."
  (:require [clojure.test :refer [deftest is run-tests]]
            [sequential-frontend-probe :as sp]))
(deftest expired-release-preflight-preserves-original-owner-and-idle-journal
  (let [value (Object.) s {:owners (atom {:one value}) :in-flight (atom nil)}]
    (with-redefs-fn {#'sp/release-engine! (fn [_])
                    #'sp/check-time! (fn [_] (throw (ex-info "expired" {})))
                    #'sp/release-prepared! (fn [_] (throw (AssertionError. "must not start")))}
      #(do
         (is (thrown? Exception (sp/drop! s :one)))
         (is (identical? value (get @(:owners s) :one)))
         (is (nil? @(:in-flight s)))
         (is (thrown? Exception (sp/release-value! s value)))
         (is (nil? @(:in-flight s)))
         (is (thrown? Exception (sp/release-session! s)))
         (is (identical? value (get @(:owners s) :one)))))))
(deftest drop-publishes-known-custody-without-post-removal-deadline-gap
  (let [value (Object.) s {:owners (atom {:one value}) :in-flight (atom nil)} checks (atom 0)]
    (with-redefs-fn {#'sp/release-engine! (fn [_])
                    #'sp/check-time! (fn [_] (swap! checks inc))
                    #'sp/release-prepared! (fn [actual]
                         (is (identical? s actual))
                         (is (empty? @(:owners actual)))
                         (is (= :not-started (:stage @(:in-flight actual))))
                         (is (identical? value (:value @(:in-flight actual)))))}
      #(sp/drop! s :one))
    (is (= 1 @checks))))
(deftest only-recorded-not-started-release-can-transfer-into-caller-journal
  (let [value (Object.) flight (atom {:operation :release :stage :not-started :value value})
        s {:in-flight flight} output (object-array 1)]
    (with-redefs-fn {#'sp/release-engine! (fn [_])}
      #(do
         (is (identical? value (sp/take-not-started-release-owner! s output)))
         (is (identical? value (aget output 0)))
         (is (nil? @flight))
         (is (thrown? AssertionError (sp/take-not-started-release-owner! s (object-array 1))))
         (doseq [stage [:owner-transfer-pending :starting :started :take-pending :released]]
           (reset! flight {:operation :release :stage stage :value value})
           (let [other (object-array 1)]
             (is (thrown? AssertionError (sp/take-not-started-release-owner! s other)))
             (is (nil? (aget other 0)))
             (is (= stage (:stage @flight)))))
         (reset! flight {:operation :call :stage :not-started :value value})
         (is (thrown? AssertionError (sp/take-not-started-release-owner! s (object-array 1))))))))
(defn check! [] (run-tests 'sequential-retirement-checks-v1))
