(ns artifact-declaration-authority-v4-models
  "Controller-only models. Real Header/HostGuest validation is not replaced by these fixtures in production."
  (:require [clojure.test :refer [deftest is run-tests]]
            [artifact-declaration-authority-v4 :as authority]
            [java-prelude-finalizer-lineage-v1 :as finalized]))
(defn- model-need!
  ([condition] (model-need! condition "model source guard"))
  ([condition message] (when-not condition (throw (ex-info message {})))))
(defn fixture [f]
  (let [engine (Object.) src (Object.) receipt (Object.) run (Object.) env (Object.)
        kernel (Object.) constant-map (Object.) constants (Object.) fields (vec (repeatedly 7 #(Object.)))
        driver {:engine engine :source src :current-ctx (atom {})}
        prefix (atom {:engine engine :source src :code-receipt receipt
                      :environment env :kernel-root kernel :constant-map constant-map :constants constants
                      :quot 1 :empty 0 :basis :actual-original-finalizer-only})
        retired (atom false) retirement-calls (atom 0) source-live (atom true)
        view {:kernel-root kernel :constant-map constant-map :header-fields fields :const2mod-map (Object.)}
        verify (fn [driver* receipt*]
                 (model-need! @source-live "source lease revoked")
                 (model-need! (identical? driver driver*)) (model-need! (identical? receipt receipt*)) {})]
    (with-redefs-fn
      {#'authority/live-driver! verify
       #'authority/read-layout! (fn [_] {})
       #'authority/kernel-view! (fn [_ _ k] (model-need! (identical? k kernel)) view)
       #'authority/environment-view! (fn [_ _ e] (model-need! (identical? e env)) view)
       #'authority/observe-result! (fn [_] nil)
       ;; These models exercise only new prefix/once/close decisions. Genuine
       ;; taken-token, owner and source checks stay in unchanged observed! code.
       #'authority/observed! (fn [_ environment k m bundle mode]
                              (model-need! (= :model-taken bundle))
                              {:guest-environment environment :kernel-root k :constant-map m :origin mode :quot true})
       #'finalized/inspect! (fn [candidate]
                             (when-not (identical? candidate run) (throw (ex-info "forged Run" {})))
                             (when @retired (throw (ex-info "retired Run" {}))) @prefix)
       #'finalized/take-retirement-owners! (fn [_] (swap! retirement-calls inc))}
      #(f {:driver driver :engine engine :source src :receipt receipt :run run
           :environment env :kernel kernel :map constant-map :prefix prefix :view view
           :retired retired :retirement-calls retirement-calls :source-live source-live
           :open (fn [r] (authority/open-authority driver {:code-receipt receipt :finalized-run r :layout-directory :model}))}))))

(deftest pending-artifact-seed-has-no-bootstrap-or-java-checking-authority
  (fixture
    (fn [{:keys [open run engine source environment kernel map]}]
      (let [a (open run)]
        (is (fn? (:artifact-environment! a)))
        (is (not (contains? a :bootstrap-environment!)))
        (is (not (contains? a :java-env)))
        (is (thrown? Exception ((:checked-environment! a) engine environment kernel map :model-taken :input)))
        (is (nil? ((:check-source! a) engine source)))
        ((:close! a))))))

(deftest genuine-prefix-map-is-required-and-seeded-once
  (fixture
    (fn [{:keys [open run engine environment kernel map]}]
      (let [a (open run)]
        (is (thrown? Exception ((:artifact-environment! a) engine environment kernel (Object.) :model-taken)))
        (is (= :authenticated-finalized-artifact-prefix
               (:origin ((:artifact-environment! a) engine environment kernel map :model-taken))))
        (is (thrown? Exception ((:artifact-environment! a) engine environment kernel map :model-taken)))
        (is (= :input (:origin ((:checked-environment! a) engine environment kernel map :model-taken :input))))
        ((:close! a))))))

(deftest descriptive-foreign-or-retired-run-does-not-seed
  (fixture
    (fn [{:keys [open run prefix retired]}]
      (is (thrown? Exception (open @prefix)))
      (swap! prefix assoc :quot 0)
      (is (thrown? Exception (open run)))
      (swap! prefix assoc :quot 1 :engine (Object.))
      (is (thrown? Exception (open run)))
      (reset! retired true)
      (is (thrown? Exception (open run))))))

(deftest source-and-prefix-lifetime-remain-live-guards-close-does-not-retire-owners
  (fixture
    (fn [{:keys [open run engine source retired retirement-calls source-live]}]
      (let [a (open run)]
        (reset! source-live false)
        (is (thrown? Exception ((:check-source! a) engine source)))
        (reset! source-live true) (reset! retired true)
        (is (thrown? Exception ((:check-source! a) engine source)))
        ((:close! a)) ((:close! a))
        (is (zero? @retirement-calls))
        (is (thrown? Exception ((:check-source! a) engine source)))))))

(deftest header-main-module-can-change-but-imported-header-profile-cannot
  (let [fields (vec (repeatedly 7 #(Object.))) state {:prefix-view {:header-fields fields}}
        reader #'authority/imported-profile!
        updated {:header-fields (assoc fields 0 (Object.))}]
    (is (identical? updated (reader state updated)))
    (doseq [i (range 1 7)]
      (is (thrown? Exception (reader state {:header-fields (assoc fields i (Object.))}))))))

(deftest imported-const2mod-map-stays-fixed-while-compiler-extensions-may-change
  (let [fields (vec (repeatedly 7 #(Object.))) imported (Object.)
        prefix {:header-fields fields :const2mod-map imported :extensions (Object.) :ir-base-exts (Object.)}
        state {:prefix-view prefix} reader #'authority/imported-profile!
        extension-update (assoc prefix :extensions (Object.))
        ir-update (assoc prefix :ir-base-exts (Object.))]
    (is (identical? extension-update (reader state extension-update)))
    (is (identical? ir-update (reader state ir-update)))
    (is (thrown? Exception (reader state (assoc prefix :const2mod-map (Object.)))))))

(defn check! [] (run-tests 'artifact-declaration-authority-v4-models))
