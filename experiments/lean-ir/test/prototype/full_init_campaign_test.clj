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

(deftest malformed-witness-policy-is-rejected-before-resource-or-phase-acquisition
  (let [restores (atom 0)]
    (with-redefs [campaign/restore-full-init-runtime (fn [] (swap! restores inc))]
      (doseq [policy [nil [] {:unknown true} {:shared-linear nil}
                      {:shared-linear {:artifact "candidate.json"}}
                      {:shared-linear {:artifact "" :expected-sha256 (apply str (repeat 64 "0"))}}
                      {:shared-linear {:artifact "candidate.json" :expected-sha256 "unverified"}}]]
        (is (failure #(campaign/prepare! (prefix) policy)))
        (is (nil? @(campaign-atom)))
        (is (not (.exists (io/file (str (prefix) ".events.jsonl"))))))
    (is (zero? @restores)))))

(deftest explicit-additive-policy-is-forwarded-before-independent-authority-capture
  (let [fixture (prepared-fixture)
        ;; Host model only: no candidate artifact is read or authenticated here.
        policy {:shared-linear {:artifact "target/model-candidate.json"
                                :expected-sha256 (apply str (repeat 64 "0"))}}
        received (atom nil)]
    (with-preparation fixture
      (fn [calls _]
        (with-redefs [campaign/prepare-full-init-shared-witness
                      (fn [assembled actual]
                        (is (true? (:assembly-model assembled)))
                        (reset! received actual)
                        (:prepared fixture))]
          (is (= :prepared (:phase (campaign/prepare! (prefix) policy))))
          (is (= policy @received))
          (is (= [:restore :assemble] @calls))
          (is (identical? (get-in fixture [:prepared :session])
                         (get-in (campaign/checkpoint) [:support :session]))))))))

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

(defn- with-witness-stage-model
  "MODEL only: replace artifact stages, retain actual final session construction.
   No source bytes/Lean compiler/native imports or evalConst execution are used."
  [fixture reject-stage4? run]
  (let [calls (atom []) selected (atom nil) captured (atom nil)
        signature {:params [] :return-type "object"}
        old-binding {:signature signature :handler (fn [_ world _] [world 0])}
        other-binding {:signature signature :handler (fn [_ world _] [world 0])}
        base-functions (get-in fixture [:prepared :session :functions])
        bindings {"lean_eval_const" old-binding "model_unrelated" other-binding}
        base-session (raw/open-functions base-functions bindings {:backend :reference})
        ;; The real preparation preflight requires BOTH transferred assembly
        ;; roots to be references. Other campaign models intentionally use0.
        [assembly-world imports-owner] (m/allocate (get-in fixture [:prepared :world]) :array 246 [])
        assembly-world (assoc assembly-world :status :done :frames [])
        assembled (-> (:prepared fixture)
                      (assoc :status :assembled-only :session base-session
                             :world assembly-world :imports imports-owner)
                      (assoc :loaded {:source (:source fixture) :world assembly-world}))
        linked (atom nil)
        stage (fn [number]
                (fn [catalogue functions actual-bindings & rest]
                  (is (identical? bindings actual-bindings))
                  (when-let [previous @selected]
                    (is (identical? (:catalogue previous) catalogue))
                    (is (identical? (:functions previous) functions)))
                  (swap! calls conj (keyword (str "stage" number)))
                  (when (= 4 number)
                    (is (= [{:artifact "model-authenticated-candidate.json"
                             :expected-sha256 (apply str (repeat 64 "0"))}] rest))
                    (when reject-stage4?
                      (throw (ex-info "model shared-linear artifact authentication rejected" {:stage :authentication}))))
                  (let [name (keyword (str "stage-target-" number))
                        result {:catalogue {:model-stage number :identity (Object.)}
                                :functions (assoc functions name {:params [] :body [:return [:imm 0]]})
                                :target name :artifact-sha256 (apply str (repeat 64 "0"))
                                :added-declarations 1 :added-functions 1}]
                    (reset! selected result) result)))
        original-open raw/open-functions
        ns (the-ns 'prototype.full-init-campaign)
        redefinitions {(ns-resolve ns 'tw-stage-json) (stage 1)
                       (ns-resolve ns 'prepare-ir-witness) (stage 2)
                       (ns-resolve ns 'prepare-shared-names-witness) (stage 3)
                       (ns-resolve ns 'prepare-shared-names-linear-witness) (stage 4)
                       #'prototype.preparation/complete-functions
                       (fn [catalogue functions roots _]
                         (swap! calls conj :complete)
                         (is (identical? (:catalogue @selected) catalogue))
                         (is (identical? (:functions @selected) functions))
                         (is (= [(:target @selected) (var-get (ns-resolve ns 'tw-exporter))] roots))
                         (reset! linked (assoc functions :model-final-closure
                                              {:params [] :body [:return [:imm 0]]})))
                       #'prototype.eval-const/make-binding
                       (fn [_ options]
                         (swap! calls conj :capture)
                         (is (identical? (:catalogue @selected) (:catalogue options)))
                         (is (identical? @linked (:trusted-functions options)))
                         (is (= (:target @selected) (:witness options)))
                         (is (= :typed-ir (:witness-format options)))
                         (reset! captured options)
                         {:signature signature :handler (fn [_ world _] [world 0])})
                       #'raw/open-functions
                       (fn [functions actual-bindings options]
                         (swap! calls conj :open)
                         (is (identical? @linked functions))
                         (is (identical? other-binding (get actual-bindings "model_unrelated")))
                         (original-open functions actual-bindings options))}]
    (with-redefs-fn redefinitions
      #(binding [*ns* ns]
         (run {:assembled assembled :calls calls :selected selected :captured captured
               :linked linked :base-functions base-functions :other-binding other-binding})))))

(deftest selected-witness-stages-finish-before-final-capability-captures-authority
  (let [fixture (prepared-fixture)
        optional {:shared-linear {:artifact "model-authenticated-candidate.json"
                                  :expected-sha256 (apply str (repeat 64 "0"))}}]
    (doseq [options [{} optional]]
      (with-witness-stage-model fixture false
        (fn [{:keys [assembled calls selected captured linked base-functions other-binding]}]
          (let [result (if (empty? options)
                         (campaign/prepare-full-init-shared-witness assembled)
                         (campaign/prepare-full-init-shared-witness assembled options))]
            (is (= (if (empty? options)
                     [:stage1 :stage2 :stage3 :complete :capture :open]
                     [:stage1 :stage2 :stage3 :stage4 :complete :capture :open]) @calls))
            (is (= (if (empty? options) 3 4) (count (get-in result [:summary :stage-additions]))))
            (is (identical? (:catalogue @selected) (:catalogue result)))
            (is (identical? @linked (get-in result [:world :functions])))
            (is (identical? @linked (get-in result [:session :functions])))
            (is (identical? (:catalogue result) (:catalogue @captured)))
            (doseq [[name function] base-functions]
              (is (identical? function (get @linked name))))
            (is (identical? other-binding (get-in result [:session :bindings "model_unrelated"])))
            (is (identical? (:state assembled) (:state result)))
            (is (identical? (:imports assembled) (:imports result)))
            (is (= 1 (:rc (m/node (:world result) (:state result)))))
            (is (= 1 (:rc (m/node (:world result) (:imports result)))))
            (is (false? @(:closed (:source fixture))))))))))

(deftest additive-authentication-failure-keeps-assembled-owners-and-captures-no-capability
  (let [fixture (prepared-fixture)
        options {:shared-linear {:artifact "model-authenticated-candidate.json"
                                 :expected-sha256 (apply str (repeat 64 "0"))}}]
    (with-witness-stage-model fixture true
      (fn [{:keys [assembled calls captured]}]
        (with-redefs [campaign/restore-full-init-runtime (fn [] :model-restored)
                      campaign/assemble-full-init-only (fn [_] assembled)]
          (is (= :failed (:phase (campaign/prepare! (prefix) options))))
          (let [record (campaign/checkpoint) packet (get-in record [:preparation-entry :packet])]
            (is (= [:stage1 :stage2 :stage3 :stage4] @calls))
            (is (nil? @captured))
            (is (= :assembled (get-in record [:preparation-entry :stage])))
            (is (identical? assembled packet))
            (is (identical? (:source fixture) (:source packet)))
            (is (= 1 (:rc (m/node (:world packet) (:state packet)))))
            (is (= 1 (:rc (m/node (:world packet) (:imports packet)))))
            (is (not (contains? record :prepared)))
            (is (not (contains? record :support)))
            (is (false? @(:closed (:source fixture))))))))))
