(ns prototype.coherent-execution
  "Same-process acceptance/disposal proposal, source-only until its reviewed
   combined-cohort gates run. Uses issued public Project/Context/prefix APIs.
   Every returned owner is escrowed before assertions. Unknown partial failures
   retain the Source lease and fail closed; they never receive disposal success."
  (:require [clojure.java.io :as io] [clojure.data.json :as json]
            [prototype.checkpoint-wire :as wire]
            [prototype.coherent-source-preparation :as source]
            [prototype.coherent-typed-eio :as eio]
            [prototype.resident-preparation :as preparation]
            [prototype.resident-frontend :as resident]
            [prototype.resident-init-prefix :as prefix]
            [prototype.project-loader :as project]
            [prototype.project-source :as provider]
            [prototype.globals-consumer-factory :as factory]
            [ansatz.kernel.name :as name])
  (:import [java.nio.file Files StandardCopyOption]))

(defonce ^:private state (atom {:phase :ready :projects [] :receipts []}))
(defn checkpoint "Borrow canonical owners/controls/failures; never serialize." [] @state)
(defn- check! [ok message] (wire/check ok message))
(defn- ack! [stage facts]
  (let [receipt (assoc facts :stage stage :status :passed)]
    (swap! state update :receipts conj receipt)
    (println (json/write-str receipt)) (flush) receipt))
(def limits
  {:discovery {:max-roots 2 :max-native-modules 1024 :max-modules 4 :max-depth 4 :max-edges 16
               :max-source-bytes 16384 :max-header-output-bytes 65536 :max-name-nodes 64
               :max-name-bytes 4096 :max-total-name-bytes 32768}
   :header {:max-source-bytes 4096 :max-file-name-bytes 4096 :max-output-bytes 16384 :max-json-depth 64
            :max-imports 1026 :max-diagnostics 16 :max-name-nodes 64 :max-name-bytes 4096 :max-total-name-bytes 32768}
   :max-exports 4 :max-export-name-bytes 4096 :max-view-bytes 4096 :max-owned-contexts 8 :max-operations 262144})
(def policies
  ;; Existing finite v4 graph policy. Any change is a new reviewed controller
  ;; source/composition, never automatic fuel escalation or broader kernel flags.
  (let [child {:kernel-policy {:allow-axioms? true :allow-unsafe? true :fuel 500000000}
               :budgets {:outer-fuel 2000000 :helper-fuel 120000000 :attempt-fuel 1000000000}}]
    {:discovery-budgets {:helper-fuel 20000000 :attempt-fuel 500000000}
     :publication-budgets {:helper-fuel 20000000 :attempt-fuel 500000000}
     :import-options child :native-options child}))
(defn- wire-name [s] ["str" ["anonymous"] s])
(defn- exported [module member] (name/mk-str (name/mk-str (name/anonymous) module) member))
(defn- own-project! [p] (swap! state update :projects conj {:project p :closed? false}) p)
(defn- close-project! [p]
  (project/close-project! p)
  (swap! state update :projects (fn [rows] (mapv #(if (identical? p (:project %)) (assoc % :closed? true) %) rows))))
(defn- call! [p module member input expected]
  (let [codec (if (string? input) :string :nat)
        result (project/invoke p (wire-name module) (exported module member) [input]
                               {:arguments [codec] :result codec})]
    (swap! state assoc :active-call result)
    (own-project! (:project result))
    (check! (= expected (:value result)) "Actual Project invocation disagrees with fixture")
    (close-project! (:project result)) (swap! state dissoc :active-call)))
(defn- load! [p module exports expected-order]
  ;; Explicit staged load permits disposal through the ACTUAL control if advance
  ;; fails, rather than losing it inside a convenience wrapper.
  (let [started (project/prepare-load p {:roots [(wire-name module)]
                                        :exports (mapv (fn [[m members]]
                                                         {:module (wire-name m) :roots (mapv #(exported m %) members)}) exports)})
        control (:control started)]
    (swap! state assoc :active-load control)
    (loop []
      (let [next (project/advance-load! control {:max-operations 32 :wall-ms 250})]
        (when-not (= :complete (get-in next [:progress :phase])) (recur))))
    (let [result (project/finish-load! control)]
      (swap! state assoc :load-result result)
      (swap! state update :file-receipts (fnil conj []) {:project (:project result) :files (:files result)})
      (own-project! (:project result))
      (swap! state dissoc :active-load)
      (check! (and (= expected-order (get-in result [:modules :order]))
                   (= (count expected-order) (get-in result [:modules :count]))
                   (= (set expected-order) (set (keys (:files result))))
                   (every? #(instance? prototype.resident_frontend.FileHandle %) (vals (:files result))))
              "Actual checked source graph/order/FileHandles disagree")
      (swap! state dissoc :active-load)
      (:project result))))
(defn- initialize-provider! [approved]
  (let [root (:output-root approved) path (.toPath (io/file root "provider"))]
    (check! (not (Files/exists path (make-array java.nio.file.LinkOption 0))) "New campaign provider root required")
    (Files/createDirectories path (make-array java.nio.file.attribute.FileAttribute 0))
    (doseq [module ["CoherentOrdinary" "CoherentA" "CoherentB" "CoherentC" "CoherentE" "CoherentD" "ProjectAppEIO"]]
      (Files/copy (.toPath ^java.io.File ((:resolve-input approved) (str "fixtures/" module ".lean")))
                  (.resolve path (str module ".lean")) (make-array java.nio.file.CopyOption 0)))
    (swap! state assoc :provider-path path)
    (provider/provider [path] 4096)))
(defn- open-project! [context configuration init-prefix readiness prepared provider]
  (own-project!
    (project/open-project context
      {:configuration configuration :prefix init-prefix :profile (:graph-profile prepared)
       :native-readiness readiness :provider provider :native-modules [(wire-name "Init")]
       :limits limits :policies policies})))

(defn dispose!
  "Retire actual issued failure/load controls first, successful Project versions,
   typed-IO contexts, prefix and resident Contexts; close lease LAST. Unrecognized
   partial adoption/check failures deliberately retain canonical escrow/lease."
  []
  (let [{:keys [unsafe-partial? failure active-load]} @state]
    (check! (not unsafe-partial?) "Partial non-Project operation needs its named canonical owner disposition; lease retained")
    (swap! state assoc :disposal-phase :disposing)
    (try
      (when-let [capsule (:project-failure-diagnostic (ex-data failure))]
        (project/dispose-failure! capsule))
      (when (and active-load (nil? (:project-failure-diagnostic (ex-data failure))))
        (project/dispose-load! active-load))
      (doseq [{:keys [project closed?]} (reverse (:projects @state)) :when (not closed?)]
        (close-project! project))
      (when (= :prefix-ready (:phase (eio/checkpoint)))
        (let [r (:prefix-result (eio/checkpoint)) released (prefix/release-prefix (:context r) (:prefix r))]
          (swap! state assoc :eio-prefix-release released)
          (resident/close! (:context released))
          (eio/close-contexts!)))
      (when-let [r (:prefix-result @state)]
        (let [released (prefix/release-prefix (:context r) (:prefix r))]
          (swap! state assoc :prefix-release released)
          (resident/close! (:context released))
          (resident/close! (:context r))))
      (when-let [context (:resident-context @state)] (resident/close! context))
      (check! (every? :closed? (:projects @state)) "Source lease cannot close before every tracked Project version")
      (when-let [lease (:lease @state)] (.close ^java.io.Closeable lease))
      (when-let [native-source (:native-source @state)]
        (check! (true? @(:closed native-source)) "Native Source lease did not close after retiring borrowers"))
      (swap! state assoc :disposal-phase :disposed)
      {:phase :disposed :guest-replayed false}
      (catch Throwable failure
        (swap! state assoc :disposal-phase :failed :disposal-failure failure)
        (throw failure)))))

(defn run!
  "Continue the SAME actual Factory/checked/prepared lineage. All fixtures are
   direct immutable launch inputs. No arbitrary callback or duplicate helper pins."
  [approved actual-factory checked prepared restored]
  (let [before @state]
    (check! (and (= :ready (:phase before))
                 (compare-and-set! state before
                   {:phase :opening :projects [] :receipts [] :lease (:resource-lease restored)}))
            "Execution campaign is one-shot"))
  (try
    (let [contract (factory/coherent-contract actual-factory)
          _ (check! (= (:sha256 contract) (:consumer-contract-sha256 prepared)) "Execution Factory/prepared composition mismatch")
          _ (doseq [[id entrypoints] {"prototype/coherent_execution.clj" ["prototype.coherent-execution/run!"]
                                      "prototype/coherent_typed_eio.clj" ["prototype.coherent-typed-eio/prepare-prefix!"
                                                                      "prototype.coherent-typed-eio/assert-no-compilation-effects!"
                                                                          "prototype.coherent-typed-eio/invoke!"
                                                                          "prototype.coherent-typed-eio/dispose-call-failure!"
                                                                          "prototype.coherent-typed-eio/close-contexts!"]}]
              (let [rows (filter #(= id (:id %)) (get-in contract [:contract :composition :controllers]))]
                (check! (and (= 1 (count rows)) (= entrypoints (:entrypoints (first rows)))) "Execution controller entrypoints not Factory-approved")))
          configuration {:catalogue (:catalogue prepared) :trusted-functions (:trusted-functions prepared)
                         :trusted-bindings (get-in prepared [:support :session :bindings])
                         :kernel-helpers (get-in prepared [:support :kernel-helpers])
                         :frontend-configuration (:frontend-configuration prepared)}
          original (get-in prepared [:original-support :session :bindings])
          native (:prefix-native-bindings prepared)
          _ (source/validate-prefix-native-bindings! original native (:trusted-bindings configuration))
          _ (swap! state assoc :unsafe-partial? true)
          context (preparation/open-checked prepared configuration)
          _ (swap! state assoc :resident-context context :unsafe-partial? false)
          _ (ack! :resident {:live-checked-context true})
          _ (swap! state assoc :unsafe-partial? true)
          r (prefix/prepare-init-prefix context checked {:configuration configuration :native-bindings native})
          _ (swap! state assoc :prefix-result r :unsafe-partial? false)
          _ (ack! :prefix {:constant-count (get-in r [:receipt :constant-count])})
          native-source (get-in prepared [:support :source])
          _ (swap! state assoc :native-source native-source)
          binding (get original "lean_run_mod_init_core")
          readiness (factory/native-init-readiness actual-factory native-source binding)
          _ (swap! state assoc :native-readiness readiness)
          provider (initialize-provider! approved)
          p0 (open-project! (:context r) configuration (:prefix r) readiness prepared provider)
          _ (ack! :project {:native-readiness-issued true})
          admission {:configuration configuration :opened-context context :prefix-native-bindings native
                     :checked-record {:checked checked :support (:original-support prepared)}}
          _ (swap! state assoc :unsafe-partial? true)
          _ (eio/prepare-prefix! admission)
          _ (swap! state assoc :unsafe-partial? false)
          app (eio/checkpoint) app-r (:prefix-result app)
          app-p (open-project! (:context app-r) (:configuration app) (:prefix app-r) readiness prepared provider)
          app-loaded (load! app-p "ProjectAppEIO" [["ProjectAppEIO" ["run" "handled" "twice"]]] [["ProjectAppEIO"]])
          _ (eio/assert-no-compilation-effects!)
          _ (doseq [[member input] [["run" "ok"] ["handled" "domain-error"] ["twice" "two"]]]
              (let [called (eio/invoke! app-loaded (wire-name "ProjectAppEIO") (exported "ProjectAppEIO" member)
                            [input] {:arguments [:string] :result :string} 2)]
                (own-project! (:project called))
                (check! (= input (:value called)) "Typed IO actual success/domain result disagrees")
                (close-project! (:project called))))
          _ (try
              (let [called (eio/invoke! app-loaded (wire-name "ProjectAppEIO") (exported "ProjectAppEIO" "run")
                             ["host-failure"] {:arguments [:string] :result :string} 1)]
                (own-project! (:project called))
                (check! false "Expected actual host failure was not transported"))
              (catch Throwable failure
                (let [expected (:expected-host-failure (eio/checkpoint))
                      matching? (loop [e failure left 32]
                                  (cond (identical? e expected) true (or (nil? e) (zero? left)) false
                                        :else (recur (.getCause ^Throwable e) (dec left))))]
                  (check! matching? "Unexpected typed IO failure; no retry")
                  (eio/dispose-call-failure! failure))))
          _ (let [called (eio/invoke! app-loaded (wire-name "ProjectAppEIO") (exported "ProjectAppEIO" "run")
                          ["after"] {:arguments [:string] :result :string} 1)]
              (own-project! (:project called)) (check! (= "after" (:value called)) "Post-disposal typed IO call disagrees")
              (close-project! (:project called)))
          _ (check! (= ["ok" "domain-error" "two" "two" "host-failure" "after"] (:effects (eio/checkpoint)))
                    "Typed IO effects duplicated, skipped or reordered")
          _ (ack! :typed-io {:service-effects 6 :host-failure-disposed true})
          _ (close-project! app-loaded)
          _ (close-project! app-p)
          _ (let [released (prefix/release-prefix (:context app-r) (:prefix app-r))]
              (swap! state assoc :eio-prefix-release released)
              (resident/close! (:context released))
              (eio/close-contexts!))
          ordinary (load! p0 "CoherentOrdinary" [["CoherentOrdinary" ["nat" "text" "answer"]]] [["CoherentOrdinary"]])
          _ (call! ordinary "CoherentOrdinary" "nat" 41 41)
          _ (call! ordinary "CoherentOrdinary" "text" "λ 🦉" "λ 🦉")
          _ (call! ordinary "CoherentOrdinary" "answer" 0 1)
          _ (ack! :ordinary-module {:calls 3 :actual-inductive-path true})
          _ (close-project! ordinary)
          chain-exports [["CoherentA" ["add"]] ["CoherentB" ["add"]] ["CoherentC" ["add"]]]
          chain (load! p0 "CoherentC" chain-exports [["CoherentA"] ["CoherentB"] ["CoherentC"]])
          _ (call! chain "CoherentC" "add" 10 13)
          _ (ack! :chain {:modules 3 :result 13})
          diamond (load! p0 "CoherentD" [["CoherentA" ["add"]] ["CoherentB" ["add"]] ["CoherentE" ["add"]] ["CoherentD" ["add"]]]
                         [["CoherentA"] ["CoherentB"] ["CoherentE"] ["CoherentD"]])
          _ (call! diamond "CoherentD" "add" 10 25)
          _ (ack! :diamond {:modules 4 :shared-parent-once true})
          _ (close-project! diamond)
          _ (Files/copy (.toPath ^java.io.File ((:resolve-input approved) "fixtures/CoherentA-reload.lean"))
                       (.resolve ^java.nio.file.Path (:provider-path @state) "CoherentA.lean")
                       (into-array java.nio.file.CopyOption [StandardCopyOption/REPLACE_EXISTING]))
          reloaded (load! chain "CoherentC" chain-exports [["CoherentA"] ["CoherentB"] ["CoherentC"]])
          _ (check! (not (identical? chain reloaded)) "Reload reused old issued Project identity")
          _ (let [files-for (fn [p] (:files (first (filter #(identical? p (:project %)) (:file-receipts @state)))))
                  old (files-for chain) fresh (files-for reloaded)]
              (doseq [module [["CoherentA"] ["CoherentB"] ["CoherentC"]]]
                (let [before (get old module) after (get fresh module)]
                  (check! (and before after (not (identical? before after)))
                          "Reload did not produce fresh parent/dependent FileHandles")
                  (let [changed? (not= (.-digest ^prototype.resident_frontend.FileHandle before)
                                       (.-digest ^prototype.resident_frontend.FileHandle after))]
                    (when (= ["CoherentA"] module)
                      (check! changed? "Changed parent source retained its old executable unit digest"))
                    (swap! state assoc-in [:reload-unit-digest-changes (first module)] changed?)))))
          _ (call! reloaded "CoherentC" "add" 10 22)
          _ (call! chain "CoherentC" "add" 10 13)
          _ (ack! :reload {:new-result 22 :retained-old-result 13 :fresh-version true :unit-digest-changes (:reload-unit-digest-changes @state)})
          _ (close-project! reloaded)
          _ (close-project! chain)]
      (dispose!)
      (swap! state assoc :phase :passed)
      {:status :passed :consumer-contract-sha256 (:sha256 contract) :disposal-phase :disposed
       :stages (mapv :stage (:receipts @state))})
    (catch Throwable failure
      (swap! state assoc :phase :failed :failure failure)
      (try (dispose!) (catch Throwable cleanup (.addSuppressed ^Throwable failure cleanup)))
      (throw failure))))
