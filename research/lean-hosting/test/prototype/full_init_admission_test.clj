(ns prototype.full-init-admission-test
  "Small admission engine tests, with MODELLED Factory authentication and a
   privately rebound 17-CI profile. No full Init/profile/provider acceptance."
  (:require [clojure.test :refer [deftest is]]
            [prototype.full-init-admission :as admission]
            [prototype.kernel-artifact :as artifact]
            [prototype.globals-consumer-factory :as factory]
            [prototype.restore-consumer :as restore]
            [prototype.module-store :as store]
            [prototype.imported-kernel :as kernel]
            [prototype.imported-kernel-test :as fixture]
            [prototype.artifact-association-test :as association]
            [prototype.raw-interop :as raw]
            [prototype.machine :as m])
  (:import [ansatz.kernel Env]))

(defn model []
  (let [loaded (store/load-file (m/world {}) "fixtures/imported-kernel-native.jsonl")
        source (:source loaded) values (fixture/values loaded)
        root {:params [1] :body [:let 2 [:project [:var 1] 0]
                                [:inc [:var 2] 1 [:return [:var 2]]]]}
        constants {:params [1] :body [:let 2 [:project [:var 1] 0]
                                     [:let 3 [:project [:var 2] 0]
                                      [:inc [:var 3] 1 [:return [:var 3]]]]]}
        functions {(:root factory/helpers) root (:constants factory/helpers) constants
                   (:constant-map factory/helpers) constants
                   (:quot-init? factory/helpers) {:params [1] :body [:return [:imm 1]]}}
        [world environment] (association/environment (assoc (:world loaded) :functions functions) values)
        [world io] (m/allocate world :ctor 0 [environment])
        world (assoc world :status :done :frames [] :result io)
        session (raw/open-functions functions {} {:backend :reference :fuel 1000000})
        lease (restore/->ResourceLease (atom [source]))
        profile (assoc @#'admission/profile :id artifact/native17-profile :source (:digest source)
                       :base (:base source) :nodes (:size source) :count 17 :axioms #{"A"}
                       :source-bytes (.size ^java.nio.channels.FileChannel (:channel source))
                       :index-bytes (.length ^java.io.RandomAccessFile (:index source)))
        recipe {:artifacts {:archive {:sha256 (:archive profile)}
                            :transport-descriptor {:sha256 (:descriptor profile)}}}
        preparation {:catalogue-recipe recipe}
        descriptor {:producer-preparation preparation :consumer-implementation-sha256 "model-implementation"
                    :compatibility-profile "model-profile" :consumer-contract-sha256 "model-contract"}
        contract {:sha256 "model-contract"
                  :contract {:kernel-base-admission {:basis :trusted-artifact :profile (:id profile)}}}
        restored (merge descriptor {:status :restored-precheck :strictly-checked? false
                                    :manifest-sha256 (:manifest profile) :world world :session session
                                    :io-result io :roots {:io-result io} :resource-lease lease})
        support {:source source :session session :kernel-helpers factory/helpers}]
    {:input {:factory ::model-factory :restored restored :support support}
     :profile profile :contract contract :descriptor descriptor :source source :environment environment
     :world world :io io :values values :lease lease}))

(defn with-model [f]
  (let [model (model)]
    (try
      (with-redefs-fn {#'admission/profile (:profile model)
                      #'factory/coherent-contract (fn [factory]
                                                   (is (= ::model-factory factory)) (:contract model))
                      #'factory/descriptor (fn [factory]
                                            (is (= ::model-factory factory)) (:descriptor model))}
        #(f model))
      (finally (.close ^java.io.Closeable (:lease model))))))
(defn failure [f] (try (f) nil (catch clojure.lang.ExceptionInfo cause cause)))

(deftest actual-opaque-factory-and-fixed-full-profile-are-required
  (is (= artifact/full-init-profile admission/supported-profile))
  (is (thrown? Exception
        (admission/admit-restored! {:factory {} :restored {} :support {}})))
  (with-model
    (fn [{:keys [input profile]}]
      ;; Public full-profile operation rejects the tiny Store before effects.
      (with-redefs-fn {#'admission/profile (assoc profile :source "different-supported-source")}
        #(is (thrown-with-msg? Exception #"exact attached supported Store"
               (admission/admit-restored! input)))))))

(deftest private-tiny-engine-model-admits-the-actual-io-without-proof-replay-or-source-reopen
  (with-model
    (fn [{:keys [input world io environment source]}]
      (let [result (with-redefs [kernel/verify-constants (fn [& _] (throw (ex-info "No proof replay" {})))
                                kernel/verify-module-data (fn [& _] (throw (ex-info "No module replay" {})))
                                store/load-file (fn [& _] (throw (ex-info "No source reopen" {})))
                                store/open-verified (fn [& _] (throw (ex-info "No source reopen" {})))]
                     (admission/admit-restored! input))
            checked (:checked-result result)
            root (first (:fields (m/node (:world result) environment)))]
        (is (= :ok (:status result)))
        (is (= 17 (count (:constants checked)) (.size ^Env (:env checked))))
        (is (= :trusted-artifact (get-in result [:kernel-provenance :base-basis])))
        (is (identical? (:admission result) (get-in result [:kernel-provenance :artifact-admission])))
        (is (identical? (:env checked) (get-in result [:world :kernel-environments (:id root) :env])))
        (is (= environment (:environment result)))
        (is (not (contains? (:heap (:world result)) (:id io))))
        (is (contains? (:heap world) (:id io)))
        (is (not-any? #(contains? result %) [:certificate :strictly-checked?]))
        (is (not-any? #(contains? checked %) [:certificate :order]))
        (is (false? @(:closed source)))
        (is (thrown-with-msg? Exception #"already claimed" (admission/admit-restored! input)))))))

(deftest pure-preflight-rejects-mode-checkpoint-lease-io-and-independent-code-without-claim
  (with-model
    (fn [{:keys [input contract world source]}]
      (let [calls (atom 0) call raw/call]
        (with-redefs [raw/call (fn [& args] (swap! calls inc) (apply call args))]
          (with-redefs [factory/coherent-contract (fn [_] (update contract :contract dissoc :kernel-base-admission))]
            (is (thrown-with-msg? Exception #"does not select" (admission/admit-restored! input))))
          (doseq [bad [(assoc-in input [:restored :manifest-sha256] "foreign")
                       (assoc-in input [:restored :strictly-checked?] true)
                       (assoc-in input [:restored :resource-lease] (restore/->ResourceLease (atom [])))
                       (assoc-in input [:restored :roots :io-result] (m/->Ref -1))
                       (update-in input [:support :session :functions] dissoc (:constants factory/helpers))]]
            (is (some? (failure #(admission/admit-restored! bad)))))
          (is (zero? @calls)))
        ;; Rejected preflights did not consume the original branch or claim lease.
        (is (= :ok (:status (admission/admit-restored! input))))
        (is (false? @(:closed source)))
        (is (some? (m/node world (get-in input [:restored :io-result]))))))))

(deftest incomplete-native-map-failure-is-terminal-and-retains-owned-environment
  (with-model
    (fn [{:keys [input environment source]}]
      (let [call raw/call
            error (with-redefs [raw/call
                                (fn [session world target args]
                                  (if (= target (:constants factory/helpers))
                                    (let [[world value] (m/allocate world :array 246 [])]
                                      {:state world :session session :value value})
                                    (call session world target args)))]
                    (failure #(admission/admit-restored! input)))
            {:keys [checkpoint temporary-owners full-init-admission-owners]} (ex-data error)]
        (is (re-find #"complete unique native" (.getMessage error)))
        (is (= environment (:environment full-init-admission-owners)))
        (is (identical? checkpoint (:checkpoint full-init-admission-owners)))
        (is (= 1 (count temporary-owners)))
        (is (= 1 (:rc (m/node checkpoint (first temporary-owners)))))
        (is (= 1 (:rc (m/node checkpoint environment))))
        (is (false? @(:closed source)))
        (is (thrown-with-msg? Exception #"already claimed" (admission/admit-restored! input)))))))

(deftest late-helper-failure-keeps-latest-session-and-every-prior-child-alias-credit
  (with-model
    (fn [{:keys [input environment world source]}]
      (let [call raw/call constants (atom nil) session-token (Object.)
            error (with-redefs [raw/call
                                (fn [session world target args]
                                  (if (= target (:quot-init? factory/helpers))
                                    (let [world (m/retain world @constants 1)
                                          [world scratch] (m/allocate world :ctor 0 [])
                                          world (m/release world scratch 1)]
                                      (throw (ex-info "late helper failed"
                                                      {:checkpoint world :checkpoint-session session-token
                                                       :temporary-owners [@constants]})))
                                    (let [called (call session world target args)]
                                      (when (= target (:constants factory/helpers)) (reset! constants (:value called)))
                                      called)))]
                    (failure #(admission/admit-restored! input)))
            {:keys [checkpoint checkpoint-session temporary-owners full-init-admission-owners]} (ex-data error)
            cleaned (reduce #(m/release %1 %2 1) checkpoint (conj temporary-owners environment))]
        (is (identical? session-token checkpoint-session))
        (is (= [@constants] temporary-owners))
        (is (identical? checkpoint (:checkpoint full-init-admission-owners)))
        (is (> (:next-id checkpoint) (:next-id world)))
        (is (= (:heap (m/release world (get-in input [:restored :io-result]) 1)) (:heap cleaned)))
        (is (false? @(:closed source)))))))

(deftest late-association-failure-preserves-both-layers-of-an-aliased-root-owner
  (with-model
    (fn [{:keys [input environment world]}]
      (let [call raw/call root (atom nil) quot-calls (atom 0)
            error (with-redefs [raw/call
                                (fn [session world target args]
                                  (if (and (= target (:quot-init? factory/helpers))
                                           (= 2 (swap! quot-calls inc)))
                                    (throw (ex-info "late association child alias"
                                                    {:checkpoint (m/retain world @root 1)
                                                     :temporary-owners [@root]}))
                                    (let [called (call session world target args)]
                                      (when (= target (:root factory/helpers)) (reset! root (:value called)))
                                      called)))]
                    (failure #(admission/admit-restored! input)))
            {:keys [checkpoint temporary-owners association-temporary-owners
                    full-init-admission-temporary-owners]} (ex-data error)
            cleaned (reduce #(m/release %1 %2 1) checkpoint (conj temporary-owners environment))]
        (is (= 2 @quot-calls))
        (is (= [] full-init-admission-temporary-owners))
        (is (= 2 (count association-temporary-owners)))
        (is (= (into [@root] association-temporary-owners) temporary-owners))
        (is (= 2 (count (filter #(= @root %) temporary-owners))))
        (is (nil? (get-in checkpoint [:kernel-environments (:id @root)])))
        (is (= (:heap (m/release world (get-in input [:restored :io-result]) 1)) (:heap cleaned)))))))
