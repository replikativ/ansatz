(ns general-command-foundation-checks-v1
  "Pure transition/owner-journal models. Guards are explicitly mocked; these
   fixtures cannot issue an actual Base/CommandReceipt or successful file."
  (:require [clojure.test :refer [deftest is run-tests]]
            [java-ir-baseline :as j]
            [java-matched-artifact-base-v1 :as base]
            [artifact-checked-declaration-adapter-v4 :as adapter]))
(deftest finite-and-general-session-ceilings-remain-explicit
  (with-redefs-fn {#'adapter/open-session-with-ceiling (fn [ceiling & _] ceiling)}
    #(do (is (= 16 (adapter/open-session nil nil nil nil nil nil nil)))
         (is (= 512 (adapter/open-general-session nil nil nil nil {:artifact-baseline! identity} nil nil)))
         (is (thrown? Exception (adapter/open-general-session nil nil nil nil {} nil nil))))))
(defn- fake-session []
  {:source (Object.) :basis {} :engine {} :matched-base (Object.)
   :authority {:layout-receipt-sha256 (apply str (repeat 64 "a"))}
   :options {:max-declarations 4} :versions (atom []) :invocation (atom nil)
   :events (atom []) :base-operation (atom nil) :published-count (atom 0) :phase (atom :idle)})
(deftest baseline-retain-failures-preserve-prepublished-exact-targets
  (doseq [failure-call [1 2]]
    (let [session (fake-session) environment (Object.) root (Object.) constant-map (Object.) calls (atom 0)
          witnesses (atom 0)
          session (assoc-in session [:authority :artifact-baseline!]
                            (fn [_ actual]
                              (is (identical? environment actual)) (swap! witnesses inc)
                              {:kernel-root root :constant-map constant-map :guest-environment environment
                               :quot true :source-binding (:source session)
                               :layout-receipt-sha256 (get-in session [:authority :layout-receipt-sha256])
                               :origin :authenticated-idle-finalized-artifact-baseline}))]
      (with-redefs-fn {#'adapter/source-live! (fn [_]) #'base/guard! (fn [_])
                      #'j/phase (fn [& _] "idle")
                      #'j/retain! (fn [& _] (when (= failure-call (swap! calls inc)) (throw (ex-info "uncertain retain" {}))))}
        #(do
           (is (thrown? Exception (adapter/establish-base! session environment)))
           (let [operation @(:base-operation session) root-slot ^objects (:kernel-root operation)
                 map-slot ^objects (:constant-map operation)]
             (is (= :failed @(:phase session) (:stage operation)))
             (is (identical? root (aget root-slot 0)))
             (is (= (if (= 1 failure-call) :retain-pending :owned) (aget root-slot 1)))
             (is (= (if (= 1 failure-call) :pending :retain-pending) (aget map-slot 1)))
             (when (= 2 failure-call) (is (identical? constant-map (aget map-slot 0))))
             (is (empty? @(:versions session))))
           (is (thrown? Exception (adapter/establish-base! session environment)))
           (is (= 1 @witnesses)))))))
(defn- history-model [f]
  (with-redefs-fn {#'adapter/source-live! (fn [_]) #'adapter/validate-versions! (fn [_])
                  #'j/phase (fn [& _] "idle") #'adapter/private-value (fn [x k] (get x (keyword k)))} f))
(deftest zero-publication-command-needs-real-retained-version-zero
  (history-model
    #(let [s (fake-session)]
       (is (thrown? Exception (adapter/complete-command-history! s 0)))
       (reset! (:versions s) [{:id 0 :parent nil}])
       (is (= [] (adapter/complete-command-history! s 0)))
       (is (empty? @(:events s))))))
(deftest multiple-publications-require-matching-cleanup-replies-and-monotone-parents
  (history-model
    #(let [s (fake-session) request1 {:call {:replyClaimed true}} request2 {:call {:replyClaimed true}}
           events (vec (for [[id request] [[1 request1] [2 request2]] phase [:cleanup-finished :reply-transferred]]
                         {:phase phase :version-id id :request request}))]
       (reset! (:versions s) [{:id 0 :parent nil} {:id 1 :parent 0} {:id 2 :parent 1}])
       (reset! (:events s) events)
       (is (= [{:id 1 :parent 0} {:id 2 :parent 1}] (adapter/complete-command-history! s 0)))
       (is (= 2 (count (filter (fn [event] (= :reply-finished (:phase event))) @(:events s)))))
       (adapter/complete-command-history! s 0)
       (is (= 6 (count @(:events s))))
       (swap! (:versions s) assoc-in [2 :parent] 0)
       (is (thrown? Exception (adapter/complete-command-history! s 0)))
       (swap! (:versions s) assoc-in [2 :parent] 1)
       (reset! (:events s) (vec (remove (fn [event] (and (= 2 (:version-id event)) (= :reply-transferred (:phase event)))) events)))
       (is (thrown? Exception (adapter/complete-command-history! s 0))))))
(defn check! [] (run-tests 'general-command-foundation-checks-v1))
