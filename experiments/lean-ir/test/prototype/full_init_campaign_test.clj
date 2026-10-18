(ns prototype.full-init-campaign-test
  "Orchestration/ownership models using a real tiny guest finalizer and driver.
   No native Store, full Init graph, kernel certificate or math compatibility."
  (:require [clojure.test :refer [deftest is use-fixtures]]
            [clojure.java.io :as io]
            [prototype.raw-interop :as raw]
            [prototype.machine :as m]
            [prototype.module-import :as module-import]
            [prototype.native-heap :as native-heap])
  (:import [java.io StringWriter Writer]
           [java.nio.file Files]
           [java.nio.file.attribute FileAttribute]))

;; The script is definitions-only. Bind the caller's namespace so helper scripts
;; cannot change which namespace the rest of this test file is compiled into.
(binding [*ns* *ns*] (load-file "scripts/full-init-campaign.clj"))
(alias 'campaign 'prototype.full-init-campaign)
(alias 'driver 'prototype.cooperative-driver-draft)

(defn- campaign-atom [] (var-get (ns-resolve 'prototype.full-init-campaign 'campaign)))
(defn- failure [f] (try (f) nil (catch clojure.lang.ExceptionInfo e e)))
(defn- identical-value? [a b] (identical? a b))
(def ^:dynamic *directory*)
(defn- prefix [] (str (io/file *directory* "campaign")))

(use-fixtures :each
  (fn [run]
    (let [state (campaign-atom)
          directory (.toFile (Files/createTempDirectory "ansatz-campaign-model-" (make-array FileAttribute 0)))]
      (when @state (throw (ex-info "Campaign model tests require fresh process-local state" {})))
      (try
        (binding [*directory* directory *out* (StringWriter.)] (run))
        (finally
          ;; Only fake source/guest state exists in these tests. Never invoke a
          ;; production discard/Store-close or release another snapshot's owner.
          (when-let [^Writer writer (:writer @state)] (.close writer))
          (reset! state nil)
          (doseq [file (reverse (file-seq directory))] (.delete ^java.io.File file)))))))

;; Map-compatible fake lifetime only. It owns no native IDs and never supplies
;; an imported node; this does not attest a real Store or native import graph.
(defrecord ModelSource [closed]
  native-heap/NativeSource
  (contains-id? [_ _] false)
  (lookup-node [_ _] nil))

(defn- prepared-fixture []
  (let [target (campaign/full-init-assembly-target "ModuleDataTransport" "finalizeTransport")
        functions {target {:params [1 2 3] :body [:return [:var 1]]}}
        session (raw/open-functions functions {} {:backend :reference})
        [world env] (m/allocate (m/world functions) :ctor 0 [42])
        [world io] (m/allocate world :ctor 0 [env])
        catalogue {:model-catalogue (Object.)}
        source (->ModelSource (atom false))
        world (assoc world :native-imports [source])
        prepared {:world world :state io :imports 0 :session session
                  :source source :catalogue catalogue :kernel-helpers {} :kernel-policy {}
                  :profile (atom {}) :start-claimed? (atom false)
                  :summary {:scope :tiny-orchestration-model}}]
    {:prepared prepared :io io :env env :session session :source source :catalogue catalogue}))

(defn- with-preparation [fixture run]
  (let [restored (select-keys (:prepared fixture) [:world :source :session])
        assembled (assoc (:prepared fixture) :assembly-model true)
        calls (atom []) namespace-proof (atom nil)]
    (with-redefs [campaign/restore-full-init-runtime
                  (fn [] (swap! calls conj :restore) restored)
                  campaign/assemble-full-init-only
                  (fn [value]
                    (is (true? (identical-value? restored value)))
                    (swap! calls conj :assemble) assembled)
                  campaign/prepare-full-init-shared-witness
                  (fn [value]
                    (is (true? (identical-value? assembled value)))
                    (swap! calls conj :prepare)
                    (reset! namespace-proof {:namespace (ns-name *ns*)
                                             :prepare-ir-witness-resolved? (boolean (resolve 'prepare-ir-witness))})
                    (:prepared fixture))
                  campaign/tw-assembly-preflight!
                  (fn [value]
                    (is (true? (identical-value? (:prepared fixture) value)))
                    (swap! calls conj :preflight) value)]
      (run calls namespace-proof))))

(deftest preparation-retains-independent-support-and-the-helper-namespace
  (let [{:keys [prepared catalogue session source] :as fixture} (prepared-fixture)]
    (with-preparation fixture
      (fn [calls namespace-proof]
        (is (= :prepared (:phase (campaign/prepare! (prefix)))))
        (is (= [:restore :assemble :prepare] @calls))
        (is (= {:namespace 'prototype.full-init-campaign :prepare-ir-witness-resolved? true} @namespace-proof))
        (let [record (campaign/checkpoint) support (:support record)]
          (is (true? (identical-value? prepared (:prepared record))))
          (is (true? (identical-value? catalogue (:catalogue support))))
          (is (true? (identical-value? session (:session support))))
          (is (true? (identical-value? source (:source support))))
          (is (not-any? #(contains? support %) [:world :state :imports :start-claimed?])))
        (is (false? @(:closed source)))))))

(deftest actual-driver-finalizer-transfers-the-owned-io-once-without-replay
  (let [{:keys [prepared io env source session catalogue] :as fixture} (prepared-fixture)]
    (with-preparation fixture
      (fn [calls _]
        (campaign/prepare! (prefix))
        (is (= :finalized (:phase (campaign/finalize!))))
        (let [record (campaign/checkpoint) event (:finalized-event record) state (:state event)]
          (is (= :done (:status event)))
          (is (= io (:value event)))
          (is (= [env] (:fields (m/node state io))))
          (is (= [42] (:fields (m/node state env))))
          (is (= 1 (:rc (m/node state io))))
          (is (= 1 (:rc (m/node state env))))
          (is (true? @(:start-claimed? prepared)))
          (is (not (contains? record :prepared)))
          (is (true? (identical-value? catalogue (get-in record [:support :catalogue]))))
          (is (true? (identical-value? session (get-in record [:support :session]))))
          (is (true? (identical-value? event (:event (driver/checkpoint (:driver record))))))
          (is (= 1 (get-in state [:stats :steps]))))
        (is (failure #(campaign/finalize!)))
        (is (= [:restore :assemble :prepare :preflight] @calls))
        (is (false? @(:closed source)))))))

(deftest strict-failure-after-consuming-a-model-owner-is-terminal-and-retains-checkpoint
  (let [{:keys [io source] :as fixture} (prepared-fixture)
        strict-effects (atom 0) cause (atom nil)]
    (with-preparation fixture
      (fn [_ _]
        (campaign/prepare! (prefix))
        (campaign/finalize!)
        (with-redefs [module-import/finish-finalization
                      (fn [world value _ options]
                        (is (= io value))
                        (is (= {:helpers {} :kernel-policy {}} options))
                        (swap! strict-effects inc)
                        (let [error (ex-info "model strict failure after consuming IO"
                                            {:checkpoint (m/release world value 1)
                                             :owned-finalizer-result {:checkpoint world :raw-result value}})]
                          (reset! cause error) (throw error)))]
          (is (= :failed (:phase (campaign/strict-check!))))
          (is (= 1 @strict-effects))
          (let [record (campaign/checkpoint)]
            (is (= :checking (:failed-phase record)))
            (is (true? (identical-value? @cause (:failure record))))
            (is (empty? (get-in (ex-data (:failure record)) [:checkpoint :heap])))
            (is (= 1 (:rc (m/node (get-in record [:finalized-event :state]) io)))))
          (is (failure #(campaign/strict-check!)))
          (is (= 1 @strict-effects)))
        (is (false? @(:closed source)))))))

(deftest existing-output-file-fails-before-any-bootstrap-work
  (let [{:keys [prepared source] :as fixture} (prepared-fixture)
        path (str (prefix) ".events.jsonl")]
    (spit path "existing-output-must-remain")
    (with-preparation fixture
      (fn [calls _]
        (is (= :failed (:phase (campaign/prepare! (prefix)))))
        (is (= :preparing (:failed-phase (campaign/checkpoint))))
        (is (empty? @calls))
        (is (= "existing-output-must-remain" (slurp path)))
        (is (false? @(:start-claimed? prepared)))
        (is (false? @(:closed source)))))))

(deftest log-failure-retains-actual-done-io-in-the-terminal-driver
  (let [{:keys [io source] :as fixture} (prepared-fixture)]
    (with-preparation fixture
      (fn [_ _]
        (campaign/prepare! (prefix))
        (let [emit-var (ns-resolve 'prototype.full-init-campaign 'emit!) original-emit @emit-var]
          (with-redefs-fn {emit-var (fn [record]
                                     (if (= :done (:status record))
                                       (throw (ex-info "model JSONL failure on owned done result" {}))
                                       (original-emit record)))}
            #(is (= :failed (:phase (campaign/finalize!))))))
        (let [record (campaign/checkpoint) saved (driver/checkpoint (:driver record))
              event (:event saved) state (:state event)]
          (is (= :finalizing (:failed-phase record)))
          (is (= :failed (:phase saved)))
          (is (= :done (:status event)))
          (is (= io (:value event)))
          (is (= 1 (:rc (m/node state io))))
          (is (not (contains? record :prepared)))
          (is (nil? (:finalized-event record)))
          (is (failure #(campaign/finalize!))))
        (is (false? @(:closed source)))))))

(deftest typed-preparation-failure-retains-the-assembled-owner-packet-and-source
  (let [{:keys [io source prepared] :as fixture} (prepared-fixture)
        received (atom nil)]
    (with-preparation fixture
      (fn [calls _]
        (with-redefs [campaign/prepare-full-init-shared-witness
                      (fn [assembled]
                        (swap! calls conj :prepare)
                        (reset! received assembled)
                        (throw (ex-info "model typed preparation failure" {})))]
          (is (= :failed (:phase (campaign/prepare! (prefix))))))
        (let [record (campaign/checkpoint) entry (:preparation-entry record) packet (:packet entry)]
          (is (= :preparing (:failed-phase record)))
          (is (= :assembled (:stage entry)))
          (is (true? (identical-value? @received packet)))
          (is (true? (identical-value? source (:source packet))))
          (is (= io (:state packet)))
          (is (= 1 (:rc (m/node (:world packet) io))))
          (is (false? @(:start-claimed? prepared)))
          (is (not (contains? record :prepared)))
          (is (not (contains? record :driver))))
        (is (= [:restore :assemble :prepare] @calls))
        (is (false? @(:closed source)))))))

(deftest strict-success-before-logger-failure-retains-the-associated-owned-environment
  (let [{:keys [io env source] :as fixture} (prepared-fixture)
        effects (atom 0) associated-world (atom nil)]
    (with-preparation fixture
      (fn [_ _]
        (campaign/prepare! (prefix))
        (campaign/finalize!)
        (let [emit-var (ns-resolve 'prototype.full-init-campaign 'emit!) original-emit @emit-var]
          (with-redefs [module-import/finish-finalization
                        (fn [world value _ _]
                          (is (= io value))
                          (swap! effects inc)
                          (let [world (-> world (m/retain env 1) (m/release io 1))]
                            (reset! associated-world world)
                            {:status :ok :world world :environment env
                             :certificate {:constants {} :axioms #{}}}))]
            (with-redefs-fn {emit-var (fn [record]
                                       (if (= :checked-certificate (:phase record))
                                         (throw (ex-info "model certificate log failure" {}))
                                         (original-emit record)))}
              #(is (= :failed (:phase (campaign/strict-check!)))))))
        (let [record (campaign/checkpoint) associated (:associated record) world (:world associated)]
          (is (= :checking (:failed-phase record)))
          (is (= :ok (:status associated)))
          (is (= env (:environment associated)))
          (is (true? (identical-value? @associated-world world)))
          (is (= 1 (:rc (m/node world env))))
          (is (not (contains? (:heap world) (:id io))))
          (is (true? (identical-value? source (first (:native-imports world)))))
          (is (failure #(campaign/strict-check!)))
          (is (= 1 @effects)))
        (is (false? @(:closed source)))))))

(deftest final-preparation-announcement-is-unclaimable-until-publication
  (let [{:keys [prepared] :as fixture} (prepared-fixture)
        attempts (atom [])]
    (with-preparation fixture
      (fn [_ _]
        (let [emit-var (ns-resolve 'prototype.full-init-campaign 'emit!) original-emit @emit-var]
          (with-redefs-fn {emit-var (fn [record]
                                     (when (= :prepared (:phase record))
                                       (swap! attempts conj
                                              {:phase (:phase (campaign/checkpoint))
                                               :rejected? (boolean (failure #(campaign/finalize!)))
                                               :owner-unclaimed? (false? @(:start-claimed? prepared))}))
                                     (original-emit record))}
            #(is (= :prepared (:phase (campaign/prepare! (prefix)))))))
        (is (= [{:phase :preparing :rejected? true :owner-unclaimed? true}] @attempts))
        (is (= :prepared (:phase (campaign/checkpoint))))
        (is (= :finalized (:phase (campaign/finalize!))))))))

(deftest failed-final-preparation-announcement-cannot-clobber-a-claimed-finalizer
  (let [{:keys [prepared source] :as fixture} (prepared-fixture)
        rejected (atom false)]
    (with-preparation fixture
      (fn [_ _]
        (let [emit-var (ns-resolve 'prototype.full-init-campaign 'emit!) original-emit @emit-var]
          (with-redefs-fn {emit-var (fn [record]
                                     (if (= :prepared (:phase record))
                                       (do (reset! rejected (boolean (failure #(campaign/finalize!))))
                                           (throw (ex-info "model final preparation log failure" {})))
                                       (original-emit record)))}
            #(is (= :failed (:phase (campaign/prepare! (prefix)))))))
        (is @rejected)
        (is (= :preparing (:failed-phase (campaign/checkpoint))))
        (is (true? (identical-value? prepared (:prepared (campaign/checkpoint)))))
        (is (false? @(:start-claimed? prepared)))
        (is (not (contains? (campaign/checkpoint) :driver)))
        (is (false? @(:closed source)))))))
