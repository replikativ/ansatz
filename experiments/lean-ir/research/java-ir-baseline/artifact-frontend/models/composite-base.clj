(ns java-composite-base-models-v1
  "Closed routing models only, never actual source/base issuance."
  (:require [clojure.test :refer [deftest is run-tests]]
            [java-composite-artifact-base-v1 :as dispatch]
            [java-matched-artifact-base-v1 :as fixed]
            [java-prelude-finalizer-lineage-v1 :as finalizer]))
(deftest fixed-prelude-operations-retain-their-exact-guard-path
  (let [token (Object.) seen (atom [])]
    (with-redefs [fixed/guard! (fn [t] (swap! seen conj [:guard t]) t)
                  fixed/with-env! (fn [t f] (swap! seen conj [:env t]) (f :actual))
                  fixed/with-version! (fn [t e f] (swap! seen conj [:version t e]) (f e))
                  fixed/domain-names (fn [t] (swap! seen conj [:domain t]) #{:actual})
                  fixed/base-count (fn [t] (swap! seen conj [:count t]) 2314)
                  fixed/validate-base-info! (fn [t w o i] (swap! seen conj [:info t w o i]) :readback)
                  fixed/assert-session! (fn [t e s r] (swap! seen conj [:session t e s r]) t)
                  fixed/revoke! (fn [t] (swap! seen conj [:revoke t]) nil)]
      (is (identical? token (dispatch/guard! token)))
      (is (= :actual (dispatch/with-env! token identity)))
      (is (= :env (dispatch/with-version! token :env identity)))
      (is (= #{:actual} (dispatch/domain-names token)))
      (is (= 2314 (dispatch/base-count token)))
      (is (= :readback (dispatch/validate-base-info! token :world :ops :ci)))
      (is (identical? token (dispatch/assert-session! token :engine :source :run)))
      (is (nil? (dispatch/revoke! token))))
    (is (= [:guard :env :version :domain :count :info :session :revoke] (mapv first @seen)))
    (is (every? #(identical? token (second %)) @seen))))
(deftest source-dispatch-is-a-closed-operation-list-not-a-provider-map
  (let [token (Object.) seen (atom [])]
    (with-redefs-fn {#'dispatch/source-base? #(identical? token %)
                    #'dispatch/source-operation (fn [name] (fn [& args] (swap! seen conj [name args]) :actual-source-result))}
      #(do
         (is (= :actual-source-result (dispatch/guard! token)))
         (is (= :actual-source-result (dispatch/with-env! token identity)))
         (is (= :actual-source-result (dispatch/with-version! token :env identity)))
         (is (= :actual-source-result (dispatch/domain-names token)))
         (is (= :actual-source-result (dispatch/base-count token)))
         (is (= :actual-source-result (dispatch/validate-base-info! token :w :ops :i)))
         (is (= :actual-source-result (dispatch/assert-session! token :e :s :r)))
         (is (= :actual-source-result (dispatch/revoke! token)))))
    (is (= '[guard! with-env! with-version! domain-names base-count validate-base-info! assert-session! revoke!]
           (mapv first @seen)))
    (is (every? #(identical? token (first (second %))) @seen))))
(deftest caller-envs-maps-and-public-empty-base-do-not-issue-views
  (doseq [x [nil {} {:with-env! identity} (java_matched_artifact_base_v1.Base.)]]
    (is (thrown? Exception (dispatch/guard! x)))
    (is (thrown? Exception (dispatch/with-env! x identity)))))
(deftest original-finalizer-dispatch-keeps-original-issuer-and-basis
  (let [run (Object.) actual (Object.)]
    (with-redefs [finalizer/inspect! (fn [r] (is (identical? run r)) actual)]
      (is (identical? actual (dispatch/finalized-view run))))
    (is (= :actual-original-finalizer-only (dispatch/finalized-basis run))))
  (is (thrown? Exception (dispatch/finalized-view {}))))
(defn check! [] (run-tests 'java-composite-base-models-v1))
