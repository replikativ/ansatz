(ns prototype.coherent-jvm-lifecycle-test
  "Staged developer orchestration models; no restore, guest code or native owner."
  (:require [clojure.test :refer [deftest is]]
            [prototype.coherent-jvm-slice :as slice]
            [prototype.coherent-consumer-profile :as profile]
            [prototype.coherent-source-preparation :as source]
            [prototype.coherent-helper-value :as helper]))

(def approved {:implementation-sha256 (apply str (repeat 64 "a"))
               :execution (:frontend profile/execution-roles)})
(def contract-sha (apply str (repeat 64 "b")))
(defn private-var [name] (ns-resolve 'prototype.coherent-jvm-slice name))
(defn phases [stages] (mapv #(hash-map :stage %) stages))

(defn with-model [body]
  (let [state (atom nil) ledger (atom {:phase :ready}) events (atom []) owner (Object.)
        redefinitions
        {(private-var 'state) state (private-var 'ownership) ledger
         #'slice/construct!
         (fn [input]
           (when-not (compare-and-set! state nil {:phase :constructed :bootstrap input
                                                 :approved-contract {:sha256 contract-sha}
                                                 :application {:execution-roles profile/execution-roles
                                                               :corpus [{:id "model" :calls [{:args [10]}]}]}
                                                 :phases [] :corpus [] :effects []})
             (throw (ex-info "Model constructor is one-shot" {})))
           (swap! events conj :construct))
         (private-var 'restore-and-prepare!)
         (fn [] (swap! events conj :restore)
           (swap! ledger assoc :lease owner :unsafe-partial? false)
           (swap! state assoc :phase :prepared :phases (phases (subvec profile/jvm-stages 0 8))))
         (private-var 'prepare-prefix!) (fn [] (swap! events conj :prefix))
         (private-var 'perform!)
         (fn [stage f]
           (let [result (f)]
             (swap! state update :phases conj {:stage stage})
             result))
         (private-var 'applications!)
         (fn applications
           ([] (applications :all))
           ([mode]
            (swap! events conj (case mode :all :applications :prepare :applications-prepare :finish :applications-finish))
            (swap! state update :phases into
                   (phases (case mode :all (subvec profile/jvm-stages 9 16)
                                      :prepare (subvec profile/jvm-stages 9 11)
                                      :finish (subvec profile/jvm-stages 11 16))))
            (when-not (= :prepare mode)
              (swap! state assoc :corpus [{:id "model"}] :effects ["callback"]))))
         (private-var 'with-route-observation) (fn [f] (f))
         (private-var 'call-version!)
         (fn [row version role]
           (when-not (= :a version) (throw (AssertionError. "Only A may be sampled")))
           (swap! events conj [:sample-call (:id row) role])
           [{:value 55 :carrier "java.lang.Long" :artifacts [1]}])
         #'slice/dispose!
         (fn [] (swap! events conj :dispose)
           (swap! ledger assoc :disposal-phase :disposed)
           {:disposal-phase :disposed})
         #'source/checking-checkpoint (constantly nil)
         #'source/checkpoint (constantly nil) #'helper/checkpoint (constantly nil)}]
    (with-redefs-fn redefinitions #(body {:state state :ledger ledger :events events :owner owner}))))

(defn caught [f] (try (f) nil (catch Throwable failure failure)))

(deftest initialized-developer-stage-retains-owners-until-explicit-continuation
  (with-model
    (fn [{:keys [state ledger events owner]}]
      (let [result (slice/initialize! approved)]
        (is (= :development-initialized (:status result)))
        (is (= (subvec profile/jvm-stages 0 9) (:stages result)))
        (is (= :initialized (:phase @state)))
        (is (identical? owner (:lease @ledger)))
        (is (nil? (:disposal-phase @ledger)))
        (is (= [:construct :restore :prefix] @events))
        (is (not-any? #(identical? owner %) (vals result))))
      (let [result (slice/continue!)]
        (is (= :passed (:status result)))
        (is (= :disposed (:disposal-phase result)))
        (is (= profile/jvm-stages (:stages result)))
        (is (= #{:corpus :callback :phases} (set (keys (:measurements result)))))
        (is (= {:loading-effects 0 :invocation-effects 1} (get-in result [:measurements :callback])))
        (is (= :passed (:phase @state)))
        (is (= [:construct :restore :prefix :applications :dispose] @events))))))

(deftest original-run-entry-keeps-the-exact-finite-result-shape
  (with-model
    (fn [{:keys [events]}]
      (let [result (slice/run! approved)]
        (is (= #{:status :disposal-phase :stages :consumer-contract-sha256
                 :consumer-implementation-sha256 :compatibility-profile :backend :fuel
                 :compile-threshold :application-execution :measurements}
               (set (keys result))))
        (is (= contract-sha (:consumer-contract-sha256 result)))
        (is (= (:implementation-sha256 approved) (:consumer-implementation-sha256 result)))
        (is (= (:application profile/execution-roles) (:application-execution result)))
        (is (= (merge (:execution approved) {:status :passed :disposal-phase :disposed})
               (select-keys result [:backend :fuel :compile-threshold :status :disposal-phase])))
        (is (= [:construct :restore :prefix :applications :dispose] @events))))))

(deftest invalid-or-duplicate-stage-claims-never-dispose-another-operation
  (with-model
    (fn [{:keys [state events]}]
      (is (thrown? clojure.lang.ExceptionInfo (slice/continue!)))
      (is (empty? @events))
      (slice/initialize! approved)
      (is (thrown? clojure.lang.ExceptionInfo (slice/initialize! approved)))
      (is (= [:construct :restore :prefix] @events))
      (swap! state assoc :phase :continuing)
      (is (thrown? clojure.lang.ExceptionInfo (slice/continue!)))
      (is (= [:construct :restore :prefix] @events))
      (swap! state assoc :phase :initialized)
      (slice/continue!)
      (is (thrown? clojure.lang.ExceptionInfo (slice/continue!)))
      (is (= [:construct :restore :prefix :applications :dispose] @events)))))

(deftest initialization-failure-preserves-the-first-failure-and-cleans-known-owners-once
  (with-model
    (fn [{:keys [state events]}]
      (let [failure (ex-info "prefix failed" {})]
        (with-redefs-fn {(private-var 'prepare-prefix!) (fn [] (throw failure))}
          #(is (identical? failure (caught (fn [] (slice/initialize! approved))))))
      (is (= :failed (:phase @state)))
      (is (= [:construct :restore :dispose] @events))
      (is (thrown? clojure.lang.ExceptionInfo (slice/continue!)))
      (is (= [:construct :restore :dispose] @events))))))

(deftest continuation-failure-retains-unsafe-partials-and-never-retries-cleanup
  (doseq [unsafe? [false true] cleanup-fails? [false true]]
    (with-model
      (fn [{:keys [state ledger events]}]
        (slice/initialize! approved)
        (let [failure (ex-info "application failed" {}) cleanup (ex-info "close failed" {})
              dispose slice/dispose!]
          (with-redefs-fn
            {(private-var 'applications!) (fn [] (swap! events conj :failed-application)
                                           (swap! ledger assoc :unsafe-partial? unsafe?) (throw failure))
             #'slice/dispose! (fn [] (if cleanup-fails?
                                      (do (swap! events conj :failed-close)
                                          (swap! ledger assoc :disposal-phase :failed :unsafe-partial? true)
                                          (throw cleanup))
                                      (dispose)))}
            #(is (identical? failure (caught slice/continue!))))
          (is (= :failed (:phase @state)))
          (is (= (if unsafe? :unresolved nil) (:disposal-phase @state)))
          (is (= (if (and (not unsafe?) cleanup-fails?) [cleanup] [])
                 (vec (.getSuppressed ^Throwable failure))))
          (let [before @events]
            (is (thrown? clojure.lang.ExceptionInfo (slice/continue!)))
            (is (= before @events)))
          (is (= (cond unsafe? [:construct :restore :prefix :failed-application]
                       cleanup-fails? [:construct :restore :prefix :failed-application :failed-close]
                       :else [:construct :restore :prefix :failed-application :dispose]) @events)))))))

(deftest disposed-or-incompletely-initialized-stages-cannot-continue
  (with-model
    (fn [{:keys [events]}]
      (slice/initialize! approved)
      (slice/dispose!)
      (is (thrown? clojure.lang.ExceptionInfo (slice/continue!)))
      (is (= [:construct :restore :prefix :dispose] @events))))
  (with-model
    (fn [{:keys [state events]}]
      (with-redefs-fn {(private-var 'restore-and-prepare!)
                      (fn [] (swap! state assoc :phases []) (swap! events conj :incomplete-restore))}
        #(is (thrown-with-msg? clojure.lang.ExceptionInfo #"Incomplete retained Init"
                              (slice/initialize! approved))))
      (is (= :failed (:phase @state)))
      (is (= [:construct :incomplete-restore :prefix] @events)))))

(deftest prepared-a-can-be-sampled-without-reloading-before-finite-continuation
  (with-model
    (fn [{:keys [state events]}]
      (slice/initialize! approved)
      (let [prepared (slice/prepare-applications!) retained (subvec profile/jvm-stages 0 11)]
        (is (= :development-applications-ready (:status prepared)))
        (is (= retained (:stages prepared)))
        (is (thrown? clojure.lang.ExceptionInfo (slice/prepare-applications!)))
        (doseq [batch (range 1 5)]
          (let [result (slice/sample-a!)]
            (is (= :development-sampled (:status result)))
            (is (= batch (:batch result)))
            (is (= [{:id "model" :calls [{:value 55 :carrier "java.lang.Long" :artifacts [1]}]}] (:results result)))
            (is (= :applications-ready (:phase @state)))
            (is (= retained (mapv :stage (:phases @state))))))
        (let [before @events]
          (is (thrown? clojure.lang.ExceptionInfo (slice/sample-a!)))
          (is (= before @events)))
        (is (= profile/jvm-stages (:stages (slice/continue!))))
        (is (= 1 (count (filter #{:applications-prepare} @events))))
        (is (= 1 (count (filter #{:applications-finish} @events))))
        (is (= 4 (count (filter vector? @events))))
        (is (= :dispose (last @events)))))))

(deftest sampling-refuses-corpus-owner-and-lifecycle-budgets-before-invocation
  (doseq [change [(fn [state ledger] (swap! state assoc-in [:application :corpus] [{:id "one"} {:id "two"}]))
                  (fn [state ledger] (swap! ledger assoc :contexts (vec (repeat 64 {}))))
                  (fn [state ledger] (swap! ledger assoc :unsafe-partial? true))
                  (fn [state ledger] (swap! ledger assoc :disposal-phase :disposed))]]
    (with-model
      (fn [{:keys [state ledger events]}]
        (slice/initialize! approved)
        (is (thrown? clojure.lang.ExceptionInfo (slice/sample-a!)))
        (slice/prepare-applications!)
        (change state ledger)
        (let [before @events]
          (is (thrown? clojure.lang.ExceptionInfo (slice/sample-a!)))
          (is (= before @events)))
        (is (= :applications-ready (:phase @state)))
        (is (zero? (:sample-batches @state)))))))

(deftest sampling-error-or-unexpected-effect-is-terminal-without-replay
  (doseq [unexpected-effect? [false true]]
    (with-model
      (fn [{:keys [state events]}]
        (slice/initialize! approved)
        (slice/prepare-applications!)
        (let [calls (atom 0) failure (ex-info "sample failed" {})
              error (with-redefs-fn
                      {(private-var 'call-version!)
                       (fn [& _]
                         (swap! calls inc)
                         (if unexpected-effect?
                           (do (swap! state update :effects conj "unexpected") [])
                           (throw failure)))}
                      #(caught slice/sample-a!))]
          (if unexpected-effect?
            (is (re-find #"unexpected callback" (.getMessage ^Throwable error)))
            (is (identical? failure error)))
          (is (= :failed (:phase @state)))
          (is (= 1 (:sample-batches @state)))
          (is (= :dispose (last @events)))
          (is (thrown? clojure.lang.ExceptionInfo (slice/sample-a!)))
          (is (= 1 @calls)))))))

(deftest application-preparation-failure-does-not-reset-the-initialization-nonce
  (with-model
    (fn [{:keys [state events]}]
      (slice/initialize! approved)
      (let [failure (ex-info "A preparation failed" {})]
        (with-redefs-fn {(private-var 'applications!) (fn [mode] (is (= :prepare mode)) (throw failure))}
          #(is (identical? failure (caught slice/prepare-applications!)))))
      (is (= :failed (:phase @state)))
      (is (= [:construct :restore :prefix :dispose] @events))
      (is (thrown? clojure.lang.ExceptionInfo (slice/prepare-applications!)))
      (is (thrown? clojure.lang.ExceptionInfo (slice/initialize! approved)))
      (is (= [:construct :restore :prefix :dispose] @events)))))
