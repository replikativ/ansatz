(ns prototype.coherent-source-preparation-test
  "Small trusted-controller MODEL gates. Factory/constructor facts and private
   escrow atoms are rebound explicitly; no full Init/profile/provider acceptance."
  (:require [clojure.test :refer [deftest is]]
            [prototype.coherent-source-preparation :as source]
            [prototype.full-init-admission :as admission]
            [prototype.coherent-stage-guards :as guards]
            [prototype.globals-consumer-factory :as factory]
            [prototype.compact-import-check :as compact]
            [prototype.artifact-association-test :as fixture]
            [prototype.imported-kernel :as kernel]
            [prototype.module-import :as imports]
            [prototype.machine :as m]
            [prototype.raw-interop :as raw]))

(defn private-var [name] (ns-resolve 'prototype.coherent-source-preparation name))
(defn failure [f] (try (f) nil (catch clojure.lang.ExceptionInfo failure failure)))
(defn model-contract [artifact?]
  (cond-> {:composition
           {:controllers [{:id source/controller-resource
                           :entrypoints (if artifact? source/admitted-controller-entrypoints source/controller-entrypoints)}
                          {:id "prototype/coherent_helper_value.clj"
                           :entrypoints ["prototype.coherent-helper-value/initialize!"]}]
            :stages [:helper-value]}
           :kernel-policy factory/kernel-policy}
    artifact? (assoc :kernel-base-admission {:basis :trusted-artifact :profile admission/supported-profile})))

(defn with-model
  ([f] (with-model true f))
  ([artifact? f]
   (fixture/with-issued
     (fn [{:keys [world context values source projection environment admission] :as issued}]
       (let [actual-factory (Object.)
             contract (model-contract artifact?)
             descriptor {:consumer-contract-sha256 "model-contract" :producer-preparation :model-producer}
             certificate (when-not artifact? (kernel/verify-constants world values {:allow-axioms? true :allow-unsafe? true}))
             ;; A strict baseline is genuinely checked at this tiny boundary;
             ;; only the surrounding full-cohort controller facts are modelled.
             [world environment] (if artifact? [world environment]
                                   (fixture/environment (dissoc world :kernel-environments) values))
             world (if artifact? world (kernel/associate-checked context world environment imports/helpers certificate))
             world (assoc world :status :done :frames [] :result 0)
             session (raw/open-functions (:functions world) {} {:backend :reference :fuel 500000000})
             support {:source source :session session :kernel-helpers imports/helpers :catalogue {:manifests [{}]}}
             restored (merge descriptor {:status :restored-precheck :strictly-checked? false
                                        :world world :session session :resource-lease (Object.)})
             result (merge {:status :ok :world world :session session :environment environment}
                           (if artifact?
                             {:checked-result projection :admission admission :kernel-provenance (:kernel-provenance projection)}
                             {:certificate certificate}))
             checking (atom nil) preparation (atom nil) baseline (atom nil)
             input {:factory actual-factory :restored restored :support support}]
         (with-redefs-fn
           {(private-var 'check-state) checking (private-var 'state) preparation
            (private-var 'initialization-baseline) baseline
            #'factory/coherent-contract (fn [candidate]
                                         (is (identical? actual-factory candidate))
                                         {:sha256 "model-contract" :contract contract})
            #'factory/descriptor (fn [candidate]
                                  (is (identical? actual-factory candidate)) descriptor)}
           #(f {:input input :result result :checking checking :preparation preparation :baseline baseline
                :issued issued :contract contract :artifact? artifact?})))))))

(defn model-facts! [facts]
  (is (= 17 (:constants facts) (:projected facts))))

(deftest admission-uses-the-actual-constructor-result-and-an-independent-admitted-phase
  (with-model
    (fn [{:keys [input result checking]}]
      (let [calls (atom 0)]
        (with-redefs [admission/admit-restored! (fn [actual]
                                               (is (identical? input actual)) (swap! calls inc) result)
                      guards/admitted-init-facts! (fn [facts]
                                                   (model-facts! facts)
                                                   (is (= :trusted-artifact (:base-basis facts)))
                                                   (is (true? (:artifact-admission? facts))))
                      guards/init-facts! (fn [& _] (throw (AssertionError. "Artifact admission used strict facts")))
                      compact/prepare (fn [& _] (throw (AssertionError. "Artifact admission invoked proof checking")))]
          (is (identical? result (source/admit-restored! input)))
          (is (= :admitted (:phase @checking)))
          (is (identical? result (:result @checking)))
          (is (identical? input (:entry @checking)))
          (is (false? (get-in @checking [:entry :restored :strictly-checked?])))
          (is (not (contains? result :certificate)))
          (is (thrown-with-msg? Exception #"one-shot" (source/admit-restored! input)))
          (is (= 1 @calls)))))))

(deftest mode-rejection-precedes-a-private-claim
  (with-model
    (fn [{:keys [input checking]}]
      (is (thrown-with-msg? Exception #"strict Init check rejects" (source/check-restored! input)))
      (is (nil? @checking))))
  (with-model false
    (fn [{:keys [input checking]}]
      (is (thrown-with-msg? Exception #"explicit supported contract mode" (source/admit-restored! input)))
      (is (nil? @checking)))))

(deftest admission-failure-retains-original-restore-lease-and-the-actual-child-packet
  (with-model
    (fn [{:keys [input checking result]}]
      (let [cause (ex-info "model actual constructor failed"
                           {:checkpoint (assoc (:world result) :model-newer true)
                            :checkpoint-session (:session result)
                            :full-init-admission-owners {:environment (:environment result)}})]
        (with-redefs [admission/admit-restored! (fn [_] (throw cause))]
          (is (identical? cause (failure #(source/admit-restored! input))))
          (is (= :failed (:phase @checking)))
          (is (identical? cause (:failure @checking)))
          (is (identical? (get-in input [:restored :resource-lease])
                          (get-in @checking [:entry :restored :resource-lease])))
          (is (:model-newer (:checkpoint (ex-data (:failure @checking)))))
          (is (thrown-with-msg? Exception #"one-shot" (source/admit-restored! input))))))))

(deftest prepare-admitted-requires-its-exact-private-phase-result-and-support
  (with-model
    (fn [{:keys [input result checking preparation]}]
      (reset! checking {:phase :admitted :entry input :result result})
      (let [request {:factory (:factory input) :admitted result :support (:support input) :resolve-artifact identity}]
        (doseq [bad [(assoc request :admitted (with-meta result {:copy true}))
                     (assoc request :support (with-meta (:support input) {:copy true}))
                     (assoc request :certificate {})]]
          (is (thrown-with-msg? Exception #"matching Init basis/result/support" (source/prepare-admitted! bad)))
          (is (nil? @preparation)))
        (is (thrown? Exception (source/prepare! {:factory (:factory input) :checked result
                                              :support (:support input) :resolve-artifact identity})))
        (reset! checking {:phase :checked :entry input :result result})
        (is (thrown? Exception (source/prepare-admitted! request)))
        (reset! checking {:phase :admitted :entry input :result result})
        (let [stop (ex-info "MODEL reached shared preparation mechanics" {})]
          (with-redefs-fn {(private-var 'preparation-inputs) (fn [& _] (throw stop))}
            #(is (= :failed (:phase (source/prepare-admitted! request)))))
          (is (identical? request (:entry @preparation)))
          (is (identical? stop (:failure @preparation))))))))

(deftest explicit-packet-fields-do-not-launder-artifact-projections-into-certificates
  (doseq [artifact? [true false]]
    (with-model artifact?
      (fn [{:keys [input result artifact?]}]
        (let [basis (if artifact? :trusted-artifact :strict-fresh)
              projection (get result (if artifact? :checked-result :certificate))
              prepared ((private-var 'retain-base-projection) {:profile source/profile-id} basis result projection)]
          (is (identical? projection (:kernel-projection prepared)))
          (if artifact?
            (do (is (not (contains? prepared :certificate)))
                (is (not (contains? prepared :original-checked)))
                (is (identical? result (:original-admitted prepared)))
                (is (identical? (:admission result) (:admission prepared))))
            (do (is (identical? projection (:certificate prepared)))
                (is (identical? result (:original-checked prepared))))))))))
