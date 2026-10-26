(ns prototype.coherent-campaign
  "Source-only reviewed-entrypoint proposal. Constructor smoke acquires no native
   Source. run! continues the SAME process through fresh checking, the exact
   emitted helper value, genuine stages and explicit managed disposal. Unknown
   partial failures retain canonical escrow/lease and throw; they never fabricate
   success or disposal. No initializer replay, retry or checkpoint handoff."
  (:require [clojure.data.json :as json]
            [prototype.checkpoint-wire :as wire]
            [prototype.globals-consumer-factory :as factory]
            [prototype.restore-consumer :as restore]
            [prototype.coherent-source-preparation :as source]
            [prototype.coherent-stage-guards :as guards]
            [prototype.coherent-helper-value :as helper]
            [prototype.coherent-execution :as execution]
            [prototype.machine :as m]
            [prototype.raw-interop :as raw]))

(defonce ^:private state (atom nil))
(defn checkpoint "Borrow exact escrow, including all native Source leases." [] @state)
(defn- ack! [stage facts]
  (let [receipt (assoc facts :stage stage :status :passed)]
    (swap! state update :receipts (fnil conj []) receipt)
    (println (json/write-str receipt)) (flush) receipt))
(defn- input-row [approved id]
  (let [rows (filter #(= id (:id %)) (get-in approved [:manifest :direct-inputs]))]
    (wire/check (= 1 (count rows)) "Campaign requires one declared direct input")
    (first rows)))
(defn- read-input [approved id bound]
  (let [file ((:resolve-input approved) id)
        bytes (wire/read-file-bytes file bound)]
    (wire/check (= (:sha256 (input-row approved id)) (wire/sha256 bytes)) "Campaign captured input drift")
    bytes))
(defn- producer-id [id]
  (str "producer/" (if (keyword? id) (name id) id)))
(defn- factory-options [approved]
  (let [producer (wire/decode (read-input approved "producer/preparation" (* 4 1024 1024)))
        recipe (wire/utf8-string (read-input approved "producer/recipe" (* 4 1024 1024)))
        index-file ((:resolve-input approved) "producer/declaration-index")
        store-root (-> index-file .getParentFile .getParentFile .getPath)]
    {:producer-preparation producer :producer-recipe-source recipe
     :producer-resolve-artifact (fn [id] ((:resolve-input approved) (producer-id id)))
     :store-root store-root :consumer-inventory (:inventory approved)
     :expected-consumer-implementation-sha256 (:implementation-sha256 approved)
     :loaded-consumer-implementation-sha256 (:implementation-sha256 approved)
     :consumer-resolve-source (fn [id]
                                (if (some #(= id (:id %)) (:inventory approved))
                                  ((:resolve-consumer-source approved) id)
                                  ((:resolve-input approved) id)))
     :consumer-contract-source (:contract-source approved)
     :expected-consumer-contract-sha256 (:contract-sha256 approved)}))

(defn construct!
  "Actual captured-cohort constructor smoke only. No restore, native Source,
   guest steps or checking. Independent bootstrap must authenticate every source,
   class and dependency BEFORE requiring this namespace."
  [approved]
  (wire/check (compare-and-set! state nil {:phase :constructing :bootstrap approved}) "Campaign is one-shot")
  (try
    (let [options (factory-options approved)
          capability (factory/make-coherent-frontend-factory options)
          contract (factory/coherent-contract capability)
          description (factory/descriptor capability)
          _ (source/validate-approved-composition! capability)
          _ (wire/check (= [:fresh-init :graph-helpers :panic :ordinary-helpers :typed-eio :cases-on :seal
                            :helper-value :project :typed-io :ordinary-module :chain :diamond :reload]
                           (get-in contract [:contract :composition :stages]))
                        "Actual campaign requires its complete approved stage program before restore")
          _ (doseq [[id entries] {"prototype/coherent_campaign.clj" ["prototype.coherent-campaign/construct!" "prototype.coherent-campaign/run!"]
                                  "prototype/coherent_helper_value.clj" ["prototype.coherent-helper-value/initialize!"]
                                  "prototype/coherent_execution.clj" ["prototype.coherent-execution/run!"]
                                  "prototype/coherent_typed_eio.clj" ["prototype.coherent-typed-eio/prepare-prefix!"
                                                                      "prototype.coherent-typed-eio/assert-no-compilation-effects!"
                                                                      "prototype.coherent-typed-eio/invoke!"
                                                                      "prototype.coherent-typed-eio/dispose-call-failure!"
                                                                      "prototype.coherent-typed-eio/close-contexts!"]}]
              (let [rows (filter #(= id (:id %)) (get-in contract [:contract :composition :controllers]))]
                (wire/check (and (= 1 (count rows)) (= entries (:entrypoints (first rows))))
                            "Campaign actual controller roles/entrypoints incomplete before restore")))]
      (swap! state assoc :phase :constructed :factory capability :options options :approved-contract contract)
      (guards/constructor-result!
        (merge (:execution approved) {:status :constructed :consumer-contract-sha256 (:sha256 contract)
         :consumer-implementation-sha256 (:consumer-implementation-sha256 description)
         :compatibility-profile (:compatibility-profile description)
         :native-resources-acquired false :guest-executed false :strictly-checked? false})
        (:contract-sha256 approved) (:implementation-sha256 approved) (:execution approved)))
    (catch Throwable failure
      (swap! state assoc :phase :failed :failure failure)
      (throw failure))))

(defn- continuation-failure! [failure]
  ;; Preserve the same canonical owners and controller diagnostics in both phases.
  (swap! state assoc :phase :failed :failure failure
         :checking-escrow (source/checking-checkpoint) :preparation-escrow (source/checkpoint))
  (throw failure))

(defn- restore-only!
  "Restore once into canonical escrow; return no owners or checking authority."
  []
  (let [{:keys [phase bootstrap factory options] :as entry} @state]
    (wire/check (and (= :constructed phase) factory
                     (compare-and-set! state entry (assoc entry :phase :restoring))) "Actual constructed cohort required once")
    (try
      (let [manifest ((:resolve-input bootstrap) "checkpoint/manifest")
            restored (restore/restore! manifest
                       {:expected-manifest-sha256 (:sha256 (input-row bootstrap "checkpoint/manifest"))
                        :producer-preparation (:producer-preparation options)
                        :consumer-implementation-sha256 (:implementation-sha256 bootstrap)
                        :factory factory :backend (get-in bootstrap [:execution :backend]) :fuel (get-in bootstrap [:execution :fuel])
                        :resolve-resource (fn [id]
                                            {:descriptor-path ((:resolve-input bootstrap) (str "resource/" id "/descriptor"))
                                             :source-path ((:resolve-input bootstrap) (str "resource/" id "/source"))})})
            _ (swap! state assoc :restored restored)
            _ (wire/check (= (get-in bootstrap [:execution :compile-threshold])
                              (get-in restored [:session :compile-threshold])) "Reader's fixed threshold differs from explicit launch policy")
            restored (assoc restored :session (raw/open-functions (get-in restored [:world :functions])
                                                                  (:trusted-bindings restored) (:execution bootstrap)))
            _ (swap! state assoc :phase :restored :restored restored)]
        {:phase :restored})
      (catch Throwable failure (continuation-failure! failure)))))

(defn- check-and-prepare! []
  (let [{:keys [phase bootstrap factory restored] :as entry} @state]
    (wire/check (and (= :restored phase) factory restored
                     (compare-and-set! state entry (assoc entry :phase :preparing-check)))
                "Actual restored cohort required once")
    (try
      (let [branch (source/prepare-bootstrap-support factory restored (:resolve-input bootstrap))
            _ (swap! state assoc :phase :checking :bootstrap-support branch)
            checked (source/check-restored! {:factory factory :restored (:candidate branch) :support (:support branch)})
            _ (swap! state assoc :phase :preparing :checked checked)
            _ (ack! :fresh-init {:constants 65994 :projected 65994 :axioms 15 :live-association true})
            summary (source/prepare! {:factory factory :checked checked :support (:support branch)
                                     :resolve-artifact (:resolve-input bootstrap)})]
        (let [escrow (source/checkpoint)
              phase (guards/preparation-phase! summary escrow source/pure-value-target)]
          (swap! state assoc :phase phase :preparation-summary summary :preparation-escrow escrow)
          (ack! :preparation {:helper-value-required (= :helper-value-required phase)
                              :cases-on-before-seal true :callback-captured true})
          summary))
      (catch Throwable failure (continuation-failure! failure)))))

(defn- restore-and-prepare!
  "Compatibility continuation: identical restore, checking and preparation order."
  []
  (restore-only!)
  (check-and-prepare!))

(defn- dispose-pre-context!
  "Only a known quiescent checked Env before Context transfer is released here.
   Unknown partial helper/association failure retains canonical escrow and lease."
  []
  (let [checked (:checked @state) h (helper/checkpoint)
        prepared (or (:prepared h) (get-in @state [:preparation-escrow :prepared]))
        e (execution/checkpoint)]
    (wire/check (= :ready (:phase e)) "Execution already owns the Context/lease disposition")
    (wire/check (and checked (= :ok (:status checked))
                     (or (nil? h) (= :initialized (:phase h)))
                     (or (nil? h) (= :released (:result-owner-state h))))
                "Pre-Context canonical owner disposition unresolved; lease retained")
    (let [world (or (:world prepared) (:world checked))
          world (m/release world (:environment checked) 1)]
      (swap! state assoc :disposed-world world :checked-environment-state :released)
      (.close ^java.io.Closeable (get-in @state [:restored :resource-lease]))
      (swap! state assoc :disposal-phase :disposed))))

(defn run!
  "Complete SAME-process genuine stages and disposal. Constructor smoke remains a
   separate no-resource entrypoint. Failure never becomes prepared or passed."
  [approved]
  (construct! approved)
  (try
    (restore-and-prepare!)
    (wire/check (= :helper-value-required (:phase @state))
                "Exact pinned archive must require the reviewed emitted helper value")
    (when (= :helper-value-required (:phase @state))
      (let [summary (helper/initialize!) escrow (helper/checkpoint)]
        (swap! state assoc :helper-escrow escrow)
        (when (= :failed (:phase escrow)) (throw (:failure escrow)))
        (guards/helper-value-facts! summary)
        (swap! state assoc :phase :prepared :prepared (:prepared escrow))
        (ack! :helper-value {:guest-invocation-count 1 :guest-steps-delta 5 :result-release-count 1})))
    (let [prepared (or (:prepared @state) (get-in @state [:preparation-escrow :prepared]))]
      (wire/check (and (= :prepared (:phase @state)) (true? (:runnable? prepared))
                       (empty? (:missing-helper-values prepared))) "Runnable actual prepared packet required")
      (let [result (execution/run! approved (:factory @state) (:checked @state) prepared (:restored @state))]
        (wire/check (and (= :passed (:status result)) (= :disposed (:disposal-phase result)))
                    "Campaign missing completed stages/disposal")
        (let [result (merge (:execution approved) (update result :stages #(into (mapv :stage (:receipts @state)) %)))]
          (swap! state assoc :phase :passed :disposal-phase :disposed :result result)
          result)))
    (catch Throwable failure
      (swap! state assoc :phase :failed :failure failure
             :helper-escrow (helper/checkpoint) :execution-escrow (execution/checkpoint)
             :checking-escrow (source/checking-checkpoint) :preparation-escrow (source/checkpoint))
      (when (= :ready (:phase (execution/checkpoint)))
        (try (dispose-pre-context!)
             (catch Throwable cleanup
               (swap! state assoc :disposal-phase :unresolved :disposal-failure cleanup)
               (.addSuppressed ^Throwable failure cleanup))))
      (throw failure))))
