(ns prototype.coherent-helper-value
  "Definitions-only one-shot execution of the reviewed helper UInt32 value.
   This is a separate explicit guest stage for preparation v2. It never mutates the preparation
   controller, closes a source/lease, imports modules or manufactures a value."
  (:require [prototype.machine :as m]
            [prototype.raw-interop :as raw]
            [prototype.eval-const :as eval]
            [prototype.coherent-source-preparation :as source]
            [prototype.globals-consumer-factory :as factory]
            [prototype.coherent-stage-guards :as guards])
  (:import [ansatz.kernel Env]))

(def profile-id "ansatz-coherent-native-init-helper-value/1")
(def preparation-profile "ansatz-coherent-native-init-source-graph-preparation/1")
(def pure-value-target
  ["str" ["str" ["str" ["anonymous"] "SourceModuleImport"] "finalizeClassic"] "_boxed_const_1"])
(def initializer-target ["str" pure-value-target "_ansatz_global_initializer"])
(defonce ^:private state (atom nil))

(defn checkpoint "Borrow owned/diagnostic packets; never print this entire map." [] @state)
(defn- check! [condition message]
  (when-not condition (throw (ex-info message {}))))
(defn- preparation-record [] (source/checkpoint))
(defn- init-preserved! [world] (source/assert-initialization-preserved! world))
(defn summary []
  (let [record @state]
    {:scope profile-id :phase (:phase record)
     :guest-invocation-count (get record :guest-invocation-count 0)
     :result-release-count (get record :result-release-count 0)
     :initialization-preservation (:initialization-after record)
     :result-owner-state (:result-owner-state record)
     :runnable? (true? (get-in record [:prepared :runnable?]))
     :guest-steps-delta (or (:guest-steps-delta record)
                            (when (and (:guest-steps-before record) (:latest-world record))
                              (- (get-in record [:latest-world :stats :steps])
                                 (:guest-steps-before record))))
     :native-import-replayed false :native-initializers-replayed false
     :host-value-seeded false :preparation-controller-mutated false
     :failure-message (when-let [failure (:failure record)]
                        (let [message (or (.getMessage ^Throwable failure) "")]
                          (subs message 0 (min 900 (count message)))))}))

(defn initialize!
  "Claim and execute exactly the missing reviewed pure helper value once.
   Reads the actual preparation controller's escrow, never a caller-forged map.
   No arguments or host seed. raw/call enters the actual trusted :global wrapper,
   executes its emitted UInt32-zero body, and publishes the real ready marker.
   Success releases the returned owner exactly once and escrows a NEW prepared
   packet. Failure is terminal and retains the latest world/session and any
   returned owner; it never authorizes retry or automatic release guessing."
  []
  (check! (compare-and-set! state nil {:phase :claiming :guest-invocation-count 0
                                     :result-release-count 0})
          "Helper value stage already claimed; no retry")
  (try
    (let [entry (preparation-record)
          _ (swap! state assoc :preparation-entry entry)
          prepared (:prepared entry)
          approved (factory/coherent-contract (:actual-factory prepared))
          _ (check! (= (:sha256 approved) (:consumer-contract-sha256 prepared)) "Helper Factory composition mismatch")
          controller (filter #(= "prototype/coherent_helper_value.clj" (:id %)) (get-in approved [:contract :composition :controllers]))
          _ (check! (and (= 1 (count controller))
                         (= ["prototype.coherent-helper-value/initialize!"] (:entrypoints (first controller)))
                         (some #{:helper-value} (get-in approved [:contract :composition :stages])))
                    "Actual Factory does not approve the exact helper-value controller/stage")
          world (:world prepared) session (:session prepared)
          registry (:trusted-functions prepared) globals (:globals world)
          _ (swap! state assoc :initialization-before (init-preserved! world))
          source (get-in prepared [:support :source])
          _ (check! (and (= :prepared-missing-helper-values (:phase entry))
                         (= preparation-profile (:profile prepared))
                         (false? (:runnable? prepared))
                         (= [pure-value-target] (:missing-helper-values prepared))
                         (= [pure-value-target] (get-in entry [:evidence :missing-helper-values]))
                         (= 0 (get-in entry [:evidence :new-initialization-actions]))
                         (= 1 (get-in entry [:evidence :existing-value-actions]))
                         (= :done (:status world)) (empty? (:frames world)) (nil? (:host-request world))
                         (identical? (:functions world) (:functions session))
                         (= 500000000 (:fuel session))
                         (= 1 (count (:native-imports world)))
                         (identical? source (first (:native-imports world)))
                         (false? @(:closed source))
                         (instance? Env (get-in prepared [:certificate :env]))
                         (not (contains? globals pure-value-target)))
                    "Helper stage requires the exact nonrunnable authenticated preparation")
          _ (check! (= {:params [] :body [:global pure-value-target initializer-target]}
                       (get registry pure-value-target))
                    "Reviewed helper global wrapper changed")
          _ (check! (= {:params []
                        :body [:let 1 [:literal 0]
                               [:let 2 [:box "uint32" [:var 1]] [:return [:var 2]]]]}
                       (select-keys (get registry initializer-target) [:params :body]))
                    "Reviewed helper initializer no longer executes only emitted UInt32 zero")
          _ (eval/validate-executables! world registry [pure-value-target])
          before (get-in world [:stats :steps])
          ;; Escrow precedes the only guest invocation. Claim count records an
          ;; attempted call even if entry validation inside raw/call rejects it.
          _ (swap! state assoc :phase :invoking :entry-world world :entry-session session
                               :latest-world world :latest-session session
                               :guest-invocation-count 1 :guest-steps-before before)
          called (raw/call session world pure-value-target [])
          _ (swap! state assoc :phase :returned :call-result called
                               :latest-world (:state called) :latest-session (:session called)
                               :result-owner-state :owned :owned-result (:value called))
          completed (:state called) latest-session (:session called) value (:value called)
          ready (get-in completed [:globals pure-value-target])
          _ (swap! state assoc :initialization-after-call (init-preserved! completed))
          _ (check! (and (= :done (:status completed)) (empty? (:frames completed))
                         (= value (:result completed))
                         (identical? (:functions completed) (:functions latest-session))
                         (identical? (:functions world) (:functions completed))
                         (= :ready (:status ready))
                         (= 0 (m/unbox-value completed "uint32" (:value ready)))
                         (= 0 (m/unbox-value completed "uint32" value))
                         (= (inc (count globals)) (count (:globals completed))))
                    "Actual helper invocation did not publish the expected completed value")
          _ (doseq [[name old] globals]
              (check! (identical? old (get-in completed [:globals name]))
                      "Helper value execution changed another global"))
          _ (doseq [key [:kernel-environments :native-imports :source-modules
                         :source-regions :eval-const-authorizations]]
              (check! (identical? (get world key) (get completed key))
                      "Helper value execution changed import/kernel/source authority"))
          _ (check! (= 5 (- (get-in completed [:stats :steps]) before))
                    "Helper stage did not execute actual guest instructions")
          ;; Release ONLY the actually returned owner, once. A verification
          ;; failure above keeps that owner in escrow for explicit disposal.
          _ (swap! state assoc :phase :releasing :result-owner-state :release-started)
          released (m/release completed value 1)
          _ (swap! state assoc :phase :released :latest-world released
                               :result-owner-state :released :result-release-count 1)
          result (assoc prepared :world released :session latest-session
                                 :runnable? true :missing-helper-values [])
          delta (- (get-in released [:stats :steps]) before)
          _ (swap! state assoc :initialization-after (init-preserved! released))]
      ;; Only this controller adopts a new packet. Preparation escrow remains
      ;; exactly the original missing-value snapshot and may not be executed.
      (swap! state assoc :phase :initialized :prepared result :guest-steps-delta delta)
      (guards/helper-value-facts! (summary)))
    (catch Throwable failure
      (let [data (ex-data failure)]
        (swap! state
               (fn [record]
                 (cond-> (assoc record :phase :failed :failure failure)
                   (:checkpoint data) (assoc :latest-world (:checkpoint data))
                   (:checkpoint-session data) (assoc :latest-session (:checkpoint-session data))))))
      (summary))))
