(ns general-command-foundation-checks-v1
  "Pure transition/owner-journal models. Guards are explicitly mocked; these
   fixtures cannot issue an actual Base/CommandReceipt or successful file."
  (:require [clojure.test :refer [deftest is run-tests]]
            [java-ir-baseline :as j]
            [java-matched-artifact-base-v1 :as base]
            [artifact-declaration-authority-v4 :as authority]
            [artifact-declaration-driver-v4 :as driver]
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
(deftest unrelated-host-guest-results-are-not-kernel-witnesses
  (let [state {:driver {:engine (Object.) :current-ctx (atom {})} :request (atom nil)}]
    (with-redefs [j/host-guest-result (fn [& _] (throw (AssertionError. "No registered kernel request: do not inspect other controller result")))]
      (is (nil? (#'authority/observe-result! state))))
    (reset! (:request state) (Object.))
    (with-redefs [j/host-guest-result (fn [& _] (Object.))]
      (is (thrown? Exception (#'authority/observe-result! state))))))
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
(deftest all-publications-require-full-completion-and-earlier-retained-parents
  (history-model
    #(let [s (fake-session) request1 {:request-id 1 :call {:replyClaimed true}} request2 {:request-id 2 :call {:replyClaimed true}}
           events (vec (for [[id parent request] [[1 0 request1] [2 1 request2]]
                            phase [:checked :published :committed :cleanup-finished :reply-transferred]]
                         {:phase phase :version-id id :parent-id parent :request request}))]
       (reset! (:versions s) [{:id 0 :parent nil} {:id 1 :parent 0} {:id 2 :parent 1}])
       (reset! (:events s) events) (reset! (:published-count s) 2)
       (is (= [{:id 1 :parent 0} {:id 2 :parent 1}] (adapter/complete-command-history! s 0)))
       (is (= 2 (count (filter (fn [event] (= :reply-finished (:phase event))) @(:events s)))))
       (adapter/complete-command-history! s 0)
       (is (= 12 (count @(:events s))))
       (swap! (:versions s) assoc-in [2 :parent] 2)
       (is (thrown? Exception (adapter/complete-command-history! s 0)))
       (swap! (:versions s) assoc-in [2 :parent] 1)
       (reset! (:events s) (vec (remove (fn [event] (and (= 2 (:version-id event)) (= :reply-transferred (:phase event)))) events)))
       (is (thrown? Exception (adapter/complete-command-history! s 0))))))
(deftest driver-factories-capture-the-selected-session-before-routing
  (let [e (Object.) source (Object.) current (atom {}) seen (atom [])
        d {:engine e :source source :current-ctx current}
        auth {:check-source! (fn [actual actual-source]
                               (is (identical? e actual)) (is (identical? source actual-source)))}
        session (fn [profile options] {:profile profile :options options :phase (atom :idle)})]
    (with-redefs [authority/open-authority (fn [& _] auth)
                  adapter/open-session (fn [_ _ _ _ _ _ opts] (session :finite opts))
                  adapter/open-general-session (fn [_ _ _ _ _ _ opts] (session :general opts))
                  adapter/begin! (fn [actual _] (swap! seen conj [:begin actual]) (reset! (:phase actual) :active))
                  adapter/poll! (fn [actual] (swap! seen conj [:poll actual]) {:status :active})
                  j/host-request (fn [& _] :request) j/request-value (fn [& _] "lean_elab_add_decl")]
      (doseq [[factory profile limit options] [[driver/open-driver :finite 16 {}]
                                               [driver/open-general-driver :general 512 {}]
                                               [driver/open-general-driver :general 23 {:max-declarations 23}]]]
        (let [opened (factory {:driver d} :base :run (assoc options :heartbeat-step! identity))
              actual (:adapter opened)]
          (reset! seen [])
          (is (= profile (:profile actual)))
          (is (= limit (get-in actual [:options :max-declarations])))
          ((:runtime-step! opened) {:driver d})
          (is (= [:begin :poll] (mapv first @seen)))
          (is (every? #(identical? actual (second %)) @seen))
          (is (= 1 @(:begun opened) @(:ticks opened))))))))
(deftest general-driver-invalid-policy-rejects-before-authority-opening
  (with-redefs [authority/open-authority (fn [& _] (throw (AssertionError. "must reject before authority")))]
    (doseq [limit [nil 0 -1 513 1.5]]
      (is (thrown? clojure.lang.ExceptionInfo
            (driver/open-general-driver nil nil nil {:max-declarations limit :heartbeat-step! identity}))))
    (is (thrown? clojure.lang.ExceptionInfo (driver/open-general-driver nil nil nil {})))))
(deftest dag-history-keeps-side-branches-and-uses-a-separate-next-command-watermark
  (history-model
    #(let [s (assoc (fake-session) :options {:max-declarations 16})
           versions [{:id 0 :parent nil} {:id 1 :parent 0} {:id 2 :parent 1}
                     {:id 3 :parent 1} {:id 4 :parent 1} {:id 5 :parent 2} {:id 6 :parent 3}]
           requests (into {} (for [i (range 1 7)] [i {:request-id i :call {:replyClaimed true}}]))
           events (vec (for [entry (rest versions) phase [:checked :published :committed :cleanup-finished :reply-transferred]]
                         {:version-id (:id entry) :parent-id (:parent entry) :request (get requests (:id entry)) :phase phase}))]
       (reset! (:versions s) versions) (reset! (:published-count s) 6) (reset! (:events s) events)
       ;; Prior selected3, old ledger already5; only NEW6 belongs to this interval.
       (is (= [{:id 6 :parent 3}] (adapter/complete-command-history! s 5 3)))
       (is (= [0 1 3 6] (adapter/version-ancestry s 6)))
       (is (= 6 (adapter/publication-watermark s)))
       ;; Earlier interval validates EVERY sibling branch, regardless of selection.
       (is (= (mapv (fn [entry] (select-keys entry [:id :parent])) (subvec versions 1))
              (adapter/complete-command-history! s 0 0)))
       (is (= 6 (count (filter (fn [event] (= :reply-finished (:phase event))) @(:events s)))))
       (let [bad (update (first @(:events s)) :parent-id (constantly 5))]
         (swap! (:events s) assoc 0 bad)
         (is (thrown? Exception (adapter/complete-command-history! s 0 0)))))))
(defn check! [] (run-tests 'general-command-foundation-checks-v1))
