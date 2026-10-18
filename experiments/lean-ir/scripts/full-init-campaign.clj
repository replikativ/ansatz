(ns prototype.full-init-campaign
  "Definitions-only REPL orchestration. Loading performs no guest/native work.
   Phase failures are terminal. All printed/returned results are scalar summaries;
   checkpoint deliberately exposes borrowed diagnostic alternatives only."
  (:refer-clojure :exclude [finalize])
  (:require [clojure.java.io :as io]
            [clojure.data.json :as campaign-json]
            [prototype.machine :as campaign-machine]
            [prototype.raw-interop :as campaign-raw]
            [prototype.eval-const :as campaign-eval]
            [prototype.module-import :as campaign-import])
  (:import [java.nio.file Files StandardOpenOption OpenOption]
           [java.nio.charset StandardCharsets]
           [java.io Writer Closeable]))

(doseq [path ["scripts/full-init-assembly-probe.clj"
              "scripts/prepare-ir-witness.clj"
              "scripts/prepare-shared-names-witness.clj"
              "scripts/typed-witness-next.clj"
              "scripts/cooperative-full-init-drive.clj"]]
  (binding [*ns* (the-ns 'prototype.full-init-campaign)] (load-file path)))
(alias 'campaign-driver 'prototype.cooperative-driver-draft)

(defonce ^:private campaign (atom nil))
(defn- fail [message data] (throw (ex-info message data)))
(defn- short-message [cause]
  (when cause (let [s (or (.getMessage ^Throwable cause) "")] (subs s 0 (min 700 (count s))))))

(defn checkpoint
  "Borrow the live phase record, NEVER print/serialize it. It can contain owned
   roots, terminal raw checkpoints and a borrowed Store. No retry is authorized."
  [] @campaign)

(defn- summary-of [record]
  (let [event (or (:finalized-event record)
                  (when-let [driver (:driver record)] (:event (campaign-driver/checkpoint driver))))
        world (or (get-in record [:associated :world]) (:state event) (get-in record [:prepared :world])
                  (get-in record [:preparation-entry :packet :world]))
        profile (some-> record :support :profile deref)
        source (or (get-in record [:support :source]) (get-in record [:preparation-entry :packet :source])
                   (:source (ex-data (:failure record))))
        runtime (Runtime/getRuntime)]
    {:phase (:phase record) :guest-status (:status world)
     :guest-steps (when (and world (number? (:guest-base record)))
                    (- (get-in world [:stats :steps]) (:guest-base record)))
     :functions (count (:functions world)) :heap-objects (count (:heap world))
     :kernel-associations (count (:kernel-environments world))
     :eval-const-calls (get-in profile [:eval-const :calls] 0)
     :eval-const-failures (get-in profile [:eval-const :failures] 0)
     :source-open (when source (false? @(:closed source)))
     :heap-used (- (.totalMemory runtime) (.freeMemory runtime)) :heap-maximum (.maxMemory runtime)
     :failed-phase (:failed-phase record) :failure-message (short-message (:failure record))}))
(defn summary [] (summary-of @campaign))

(defn- emit! [record]
  (when-let [^Writer writer (:writer @campaign)]
    (locking writer (.write writer (str (campaign-json/write-str record) "\n")) (.flush writer))))
(defn- announce! [] (let [s (summary)] (emit! s) (println (campaign-json/write-str s)) (flush) s))
(defn- finish-phase! [phase]
  ;; Save owners before this function. Keep the current phase unclaimable while
  ;; observers can still fail; publish readiness only after capturing the return.
  (let [before @campaign after (assoc before :phase phase) result (summary-of after)]
    (emit! result) (println (campaign-json/write-str result)) (flush)
    (when-not (compare-and-set! campaign before after)
      (fail "Campaign changed during phase publication" {}))
    result))
(defn- claim! [expected entered]
  (let [before @campaign]
    (when-not (and (= expected (:phase before))
                  (compare-and-set! campaign before (assoc before :phase entered)))
      (fail "Campaign phase already claimed or unavailable"
            {:expected expected :actual (:phase @campaign)}))))
(defn- terminal! [phase cause]
  ;; Keep the actual Throwable and its separately named owner/checkpoint pairs.
  ;; Logging never traverses ex-data; default CLI exception printing is avoided.
  (swap! campaign assoc :phase :failed :failed-phase phase :failure cause)
  (let [s (summary)]
    (try (emit! s) (catch Throwable _ nil))
    (println (campaign-json/write-str s)) (flush) s))

(defn prepare!
  "Authenticate/restore/assemble once, retaining the original catalogue/helpers/
   policy/session independently of the execution candidate. PREFIX is explicit;
   its JSONL file must not exist. Caller owns the process/resource guard."
  [prefix]
  (when-not (and (string? prefix) (seq prefix)) (fail "Expected output prefix" {}))
  (when-not (compare-and-set! campaign nil {:phase :preparing})
    (fail "Campaign already exists; no implicit restart" {}))
  (try
    (let [path (io/file (str prefix ".events.jsonl"))
          _ (io/make-parents path)
          writer (Files/newBufferedWriter (.toPath path) StandardCharsets/UTF_8
                   (into-array OpenOption [StandardOpenOption/CREATE_NEW StandardOpenOption/WRITE]))
          _ (swap! campaign assoc :writer writer)
          prepared (binding [*ns* (the-ns 'prototype.full-init-campaign)]
                     ;; The existing preparation scripts resolve helper Vars in
                     ;; the calling namespace. Preserve that explicit context.
                     (let [restored (restore-full-init-runtime)
                           _ (swap! campaign assoc :preparation-entry {:stage :restored :packet restored})
                           assembled (assemble-full-init-only restored)
                           _ (swap! campaign assoc :preparation-entry {:stage :assembled :packet assembled})]
                       (prepare-full-init-shared-witness assembled)))
          support (select-keys prepared [:source :catalogue :kernel-helpers :kernel-policy :session :profile :summary])]
      (swap! campaign #(-> % (assoc :prepared prepared :support support
                                    :guest-base (get-in prepared [:world :stats :steps]))
                            (dissoc :preparation-entry)))
      (emit! {:phase :preparation-evidence :evidence (:summary prepared)})
      (finish-phase! :prepared))
    (catch Throwable cause (terminal! :preparing cause))))

(defn finalize!
  "Drive the actual guest finalizer automatically, stopping on owned IO success
   BEFORE Java checking. Uses default mutable execution, 2M outer steps/run and
   20M aggregate helper steps/completion. No prefix runtime option is installed.
   Source remains open for the entire campaign and any borrowed diagnostic fork."
  []
  (claim! :prepared :finalizing)
  (try
    (let [prepared (:prepared @campaign)
          _ (tw-assembly-preflight! prepared)
          _ (when-not (compare-and-set! (:start-claimed? prepared) false true)
              (fail "Finalizer owner transfer already claimed" {}))
          session (assoc (:session prepared) :fuel 2000000)
          world (campaign-machine/start (:world prepared)
                  (full-init-assembly-target "ModuleDataTransport" "finalizeTransport")
                  [(:state prepared) (:imports prepared) campaign-machine/erased])
          driver (campaign-driver/make-driver session world
                   {:allowed-bindings (:bindings session) :helper-fuel 20000000
                    :source (:source prepared) :source-open? #(false? @(:closed %))
                    :observe! emit!})]
      ;; These assembly roots transferred into the guest invocation. Keep only
      ;; the new driver and the small independent preparation-authority record.
      (swap! campaign #(-> % (assoc :driver driver) (dissoc :prepared)))
      (loop []
        (let [slice (campaign-driver/drive-slice! driver {:max-operations 1000 :wall-ms 10000})]
          (if (= :done (:status slice))
            (let [event (:event (campaign-driver/checkpoint driver))
                  io (campaign-machine/node (:state event) (:value event))]
              (when-not (and (= :ctor (:kind io)) (contains? #{0 1} (:tag io)) (= 1 (count (:fields io))))
                (fail "Malformed actual finalizer IO result" {}))
              (swap! campaign assoc :finalized-event event)
              (finish-phase! (if (= 0 (:tag io)) :finalized :guest-io-error)))
            (do (announce!) (recur))))))
    (catch Throwable cause (terminal! :finalizing cause))))

(defn strict-check!
  "Consume the actual successful finalizer IO owner once, check its whole map,
   then associate the exact guest kernel roots. Requires an explicit remaining
   heap/wall-budget decision by the caller; no catalogue reopening or replay."
  []
  (claim! :finalized :checking)
  (try
    (let [{:keys [support finalized-event]} @campaign
          {:keys [kernel-helpers kernel-policy session]} support
          world (:state finalized-event)
          source (:source support)
          _ (when-not (and (false? @(:closed source)) (= 1 (count (:native-imports world)))
                          (identical? source (first (:native-imports world))))
              (fail "Strict phase requires the same singleton open source" {}))
          _ (campaign-eval/validate-executables! world (:functions session) (vals kernel-helpers))
          _ (doseq [[symbol binding] (:bindings session)]
              (when-not (identical? binding (get-in finalized-event [:session :bindings symbol]))
                (fail "Strict phase host binding drift" {:symbol symbol})))
          active (atom (assoc (:session finalized-event) :fuel 20000000))
          progress (atom nil)
          _ (swap! campaign assoc :strict-progress progress)
          invoke (fn [state target args]
                   (reset! progress {:phase :entry :world state :session @active :target target :args args})
                   (let [called (campaign-raw/call @active state target args)]
                     (reset! active (:session called))
                     (reset! progress {:phase :return :world (:state called) :session @active
                                       :target target :value (:value called)})
                     [(:state called) (:value called)]))
          associated (assoc (campaign-import/finish-finalization
                              world (:value finalized-event) invoke
                              {:helpers kernel-helpers :kernel-policy kernel-policy})
                            :session @active)]
      (when-not (= :ok (:status associated)) (fail "Strict finalization did not succeed" {}))
      ;; Its Environment/certificate/session must survive an observer failure.
      (swap! campaign assoc :associated associated)
      (emit! {:phase :checked-certificate :constants (count (get-in associated [:certificate :constants]))
              :axioms (sort (map str (get-in associated [:certificate :axioms])))})
      (finish-phase! :checked))
    (catch Throwable cause (terminal! :checking cause))))
