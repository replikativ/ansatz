(ns java-source-closure-v1
  "Owned exact-Prelude source closures and actual repeated normal finalization.
   Existing fixed Prelude Run issuance remains one-shot and unchanged."
  (:require [java-source-module-exchange-v1 :as exchange]
            [java-prelude-finalizer-lineage-v1 :as lineage]
            [java-matched-prelude-module-v4 :as module]
            [java-matched-artifact-base-v1 :as prelude]
            [java-ir-baseline :as j]
            [ansatz.research.ir.source-setup :as source]
            [ansatz.research.ir.authenticated-demand :as demand]
            [prototype.kernel-projection-snapshot :as snapshot])
  (:import [java.util WeakHashMap]))
(defonce ^:private closures (WeakHashMap.))
(defonce ^:private runs (WeakHashMap.))
(defn- need [ok message] (when-not ok (throw (ex-info message {:profile :source-closure-v1}))))
(defn- issued [registry token]
  (locking registry (or (.get ^WeakHashMap registry token) (throw (ex-info "Actual source closure/finalizer capability required" {})))))
(defn- put! [registry token holder] (locking registry (.put ^WeakHashMap registry token holder)) token)
(defn- plan! [runtime-holder root-modules]
  (need (and (vector? root-modules) (<= 1 (count root-modules) 16)) "Bounded nonempty source root list required")
  (let [names (mapv #(get (#'exchange/module! % true) :module) root-modules)]
    (need (= (count names) (count (set names))) "Duplicate source root module")
    (loop [todo (mapv #(vector :enter % 1) (rseq root-modules)) colors {} versions {} heights {} order [] edges 0]
      (need (and (<= (count versions) 16) (<= edges 64)) "Source closure module/edge bounds")
      (if (empty? todo) order
        (let [[op token depth] (peek todo) tail (pop todo)
              m (#'exchange/module! token true) name (:module m) parents (:parents m)
              parent-names (mapv #(get (#'exchange/module! % false) :module) parents)]
          (need (and (:file-retired m) (identical? runtime-holder (:runtime-holder m))
                     (not= exchange/prelude-name name) (<= depth 16)
                     (or (nil? (get versions name)) (identical? token (get versions name))))
                "Foreign/unretired/conflicting source module or dependency depth")
          (cond
            (= :leave op)
            (let [height (inc (reduce max 0 (map #(get heights % 0) parent-names)))]
              (need (<= (+ depth height -1) 16) "Shared source dependency depth exceeds bound")
              (recur tail (assoc colors name :done) versions (assoc heights name height) (conj order token) edges))
            (= :active (get colors name)) (throw (ex-info "Cyclic source module dependencies" {}))
            (= :done (get colors name))
            (do (need (<= (+ depth (get heights name) -1) 16) "Shared source dependency depth exceeds bound")
                (recur tail colors versions heights order edges))
            :else
            (recur (into (conj tail [:leave token depth]) (map #(vector :enter % (inc depth)) (rseq parents)))
                   (assoc colors name :active) (assoc versions name token) heights order (+ edges (count parents)))))))))
(defn- array! [cell key values]
  (let [empty (#'exchange/call! cell [key :empty] "Array.mkEmpty" [0 0])]
    (reduce (fn [array [i item]] (#'exchange/call! cell [key :push i] "Array.push" [0 array item]))
            empty (map-indexed vector values))))
(defn- prefix! [cell native]
  (let [s @cell r (#'exchange/runtime! (:runtime-holder s))
        roots (#'exchange/array-values r (:aggregate native) 5)
        input (get-in native [:census :manifest :input]) m (first (:modules input))
        _ (need (and (= 1 (count (:modules input))) (= exchange/prelude-name (:module m))) "Exact native Prelude input required")
        wrap (fn [kind i part]
               (let [root-index (:rootIndex part) artifact (:artifact part)]
                 (need (and (integer? root-index) (<= 0 root-index 4) (<= 0 (:mappedBytes artifact) Long/MAX_VALUE)) "Invalid native Prelude part descriptor")
                 (#'exchange/call! cell [:native-part kind i] "JavaModuleImport.mkVirtualPart"
                   [(nth roots root-index) (:filePath artifact) (long (:mappedBytes artifact))])))
        parts (array! cell :native-parts (mapv #(wrap :main %1 %2) (range) (:parts m)))
        ir-parts (array! cell :native-ir-parts (mapv #(wrap :ir %1 %2) (range) (:irParts m)))
        effective (:effectiveImport m)
        _ (need (= {:module exchange/prelude-name :importAll true :isExported false :isMeta false} effective)
                "Native Prelude effective profile changed")
        imported (#'exchange/call! cell :native-imported "JavaModuleImport.mkImportedModule._boxed"
                   ["Init.Prelude" 1 0 0 2 1 0 parts ir-parts])]
    (#'exchange/call! cell :native-state "JavaModuleImport.assembleImportState._boxed"
      [(array! cell :native-imported-array [imported])])))
(defn- ready-code! [r modules]
  (let [program (:program (#'exchange/context r))
        bodies ^objects (#'exchange/field program "preparedBodies")]
    (doseq [token modules [_ {:keys [header]}] (get-in (#'exchange/module! token true) [:view :rows])]
      (let [method (.getMethod (class program) "functionId" (into-array Class [(class header)]))
            id (int (.invoke method program (object-array [header])))]
        (need (and (<= 0 id) (< id (alength bodies)) (some? (aget bodies id)))
              "Selected source module code is not canonically materialized")))))
(defn- closure! [token full?]
  (let [holder (issued closures token) s @holder]
    (need (contains? #{:prepared :finalizing :finalized} (:status s)) "Source closure is revoked or failed")
    (let [r (#'exchange/runtime! (:runtime-holder s))]
      (prelude/assert-session! (:prelude-base s) (:engine r) (:source r) (:prelude-run r))
      (doseq [m (:selected s)] (#'exchange/module! m full?))
      (doseq [segment (:snapshot-segments (:view s))] (snapshot/validate-segment-values segment))
      (need (= :owned (#'exchange/root-state (:regions-slot s))) "Logical region owner was retired")
      (when (= :prepared (:status s))
        (need (every? #(= :owned (#'exchange/root-state %)) [(:state-slot s) (:imports-slot s)])
              "Source closure inputs were already transferred"))
      s)))
(defn with-closure! [token f]
  (let [s (closure! token true) r (#'exchange/runtime! (:runtime-holder s))]
    (#'exchange/read-only! r #(try (f (:view s)) (finally (closure! token true))))))
(defn prepare-closure!
  "Build real source ImportState over the exact native Prelude via actual source
   constructors and bounded graph assembler. Every selected SourceModule must
   have completed real file/adapter retirement. Fresh Prelude Base is borrowed."
  [runtime root-modules fresh-prelude-base]
  (let [rh (#'exchange/issued @#'exchange/runtimes runtime) r (#'exchange/runtime! rh)
        _ (prelude/assert-session! fresh-prelude-base (:engine r) (:source r) (:prelude-run r))
        selected (plan! rh root-modules)
        native-domain (prelude/domain-names fresh-prelude-base)
        index (reduce (fn [out token]
                        (reduce-kv (fn [out name info]
                                     (need (and (not (contains? native-domain name)) (not (contains? out name)))
                                           "Source CI domain overlaps native/source modules")
                                     (assoc out name info)) out (get-in (#'exchange/module! token true) [:view :source-index]))) {} selected)
        segments (vec (mapcat #(get-in (#'exchange/module! % true) [:view :snapshot-segments]) selected))
        _ (need (and (<= (count index) 4096) (<= (count segments) 512)) "Source closure CI/snapshot budget")
        _ (ready-code! r selected)
        [operation cell] (#'exchange/operation! runtime)]
    (try
      (let [prefix (prefix! cell (module/inspect! (:module-lease r)))
            parts (mapv (fn [i token]
                          (let [view (:view (#'exchange/module! token true))]
                            (#'exchange/call! cell [:source-input i] "SourceModuleGraphPrelude.mkInput"
                              [(:name-node view) (:data view) (str "source-module:" (java.util.UUID/randomUUID))])))
                        (range) selected)
            part-array (array! cell :source-parts parts)
            root-names (mapv #(get (#'exchange/module! % true) :module) root-modules)
            requests (mapv (fn [i name]
                             (#'exchange/call! cell [:source-request i] "JavaModuleImport.mkRequestedImport._boxed"
                               [(source/label name) 0 1 0]))
                           (range) (into [exchange/prelude-name] root-names))
            request-array (array! cell :source-requests requests)
            limits (#'exchange/call! cell :source-limits "SourceModuleGraphPrelude.mkLimits" exchange/graph-limits)
            result (#'exchange/call! cell :assembly-result "SourceModuleGraphPrelude.assembleClassicGraphOverPrelude._boxed"
                     [prefix part-array request-array limits])
            ok (:fields (#'exchange/ordinary r result 1 1 #{0}))
            assembly (:fields (#'exchange/ordinary r (aget ^objects ok 0) 0 3 #{0}))
            state (aget ^objects assembly 0) imports (aget ^objects assembly 1) regions (aget ^objects assembly 2)
            _ (need (identical? imports request-array) "Source assembler changed exact requested import Array")
            _ (#'exchange/retain! cell :closure-state state)
            _ (#'exchange/retain! cell :closure-imports imports)
            _ (#'exchange/retain! cell :closure-regions regions)
            _ (#'exchange/clean! cell #{:closure-state :closure-imports :closure-regions})
            _ (doseq [token selected] (#'exchange/module! token true))
            _ (prelude/guard! fresh-prelude-base)
            _ (ready-code! r selected)
            expected (+ (prelude/base-count fresh-prelude-base) (count index))
            view {:driver (:driver r) :engine (:engine r) :source (:source r) :code-receipt (:code-receipt r)
                  :module-lease (:module-lease r) :prelude-base fresh-prelude-base :source-index index
                  :snapshot-segments segments :module-roots selected
                  :effective-modules (into [exchange/prelude-name] (mapv #(get (#'exchange/module! % false) :module) selected))
                  :requests (mapv (fn [n] {:module n :importAll false :isExported true :isMeta false}) (into [exchange/prelude-name] root-names))
                  :constant-count expected}
            holder (atom {:status :prepared :runtime-holder rh :selected selected :prelude-base fresh-prelude-base :view view
                          :state-slot (get-in @cell [:owners :closure-state]) :imports-slot (get-in @cell [:owners :closure-imports])
                          :regions-slot (get-in @cell [:owners :closure-regions])})]
        (#'exchange/finish! cell)
        (reset! cell {:status :closure-custody :owners (select-keys (:owners @cell) [:closure-state :closure-imports :closure-regions])})
        (put! closures (exchange/->SourceClosure) holder))
      (catch Throwable cause
        (#'exchange/fail! cell cause)
        (throw (ex-info "Source closure assembly failed; preserve actual operation owners" {:operation operation} cause))))))

(defn- cheap-lease! [holder]
  ;; Called at each paused root step. Full graph/snapshot/readiness validation is
  ;; at start, completed-root inspection and every association publication borrow.
  (let [s @holder r (#'exchange/runtime! (:runtime-holder s))]
    (need (contains? #{:finalizing :finalized} (:status s)) "Source finalizer closure is not active")
    (when (= :finalizing (:status s))
      (need (identical? (:attempt-marker s) (:active @(:runtime-holder s))) "Source finalizer lost exclusive runtime custody"))
    (doseq [token (:selected s)]
      (let [m @(#'exchange/issued @#'exchange/modules token)]
        (need (and (= :sealed (:status m)) (:file-retired m)
                   (every? #(= :owned (#'exchange/root-state %)) (vals (:owners m))))
              "Selected source module lease/owner was revoked")))
    (need (= :owned (#'exchange/root-state (:regions-slot s))) "Source closure region lease was retired")
    r))
(defn begin-finalizer!
  "Start the original finalizer from this issued closure's actual owned inputs.
   Reuses existing normal-root owner machinery/Run registry, never resets the
   fixed Prelude per-engine marker and never accepts a preexisting Env/result."
  [closure]
  (let [holder (issued closures closure) s (closure! closure true)
        _ (need (= :prepared (:status s)) "Source closure finalizer may be attempted only once")
        r (#'exchange/runtime! (:runtime-holder s)) d (:driver r) parent (:parent r)
        _ (need (= "idle" (j/phase (#'exchange/context r) (:engine r))) "Source finalizer requires idle engine")
        _ (need (nil? (:active r)) "Another source runtime operation is active")
        header (demand/ensure-header! d (reduce (fn [p x] ["str" p x]) ["anonymous"] ["JavaModuleImport" "finalize" "_boxed"]))
        _ (need (= lineage/finalizer-sha (j/request-value header "originalSha256")) "Source finalizer must be pinned original body")
        run-token (lineage/->Run)
        state {:status :active :stage :finalizer :driver d :engine (:engine r) :source (:source r)
               :code-receipt (:code-receipt r) :parent parent :thread (:thread r)
               :extra-code-overlays (:extra-code-overlays r)
               :startup-status (:startup-status parent)
               :startup-snapshot (select-keys @(:startup-status parent) [:state :label :actual-body-executed :result-released])
               :startup-header (first (get-in parent [:configuration :local-action-headers]))
               :options {:check-leases! #(cheap-lease! holder) :expected-constants (get-in s [:view :constant-count])
                         :deadline-nanos (+ (System/nanoTime) 120000000000) :max-instructions 50000000
                         :max-transitions 100000 :quantum 1000
                         :service-code! (fn [driver request]
                                          (need (identical? request (j/code-request @(:current-ctx driver) (:engine driver))) "Foreign finalizer Code request")
                                          (demand/service-code! driver))
                         :service-host! (fn [actual-parent request]
                                          (need (and (identical? parent actual-parent)
                                                     (identical? request (j/host-request @(:current-ctx d) (:engine d)))) "Foreign finalizer Host request")
                                          (allocation-heartbeat-cohort-v1/host-step! parent))}
               :owners {:state-input (:state-slot s) :imports-input (:imports-slot s)}
               :history [] :call nil :transitions 0}
        cell (atom state)
        helper-headers (into {} (for [[label key result] lineage/helpers
                                     :let [h (get-in parent [:configuration :helper-headers (str "KernelBridgeShim." label "._boxed")])
                                           entry (source/lookup-entry (:code-receipt r) (j/lean-name-data (j/request-value h "name")))]]
                                 [key (#'lineage/registered-header! state h (str "KernelBridgeShim." label "._boxed") (:sha256 entry)
                                        ["object"] [false] result)]))
        token (exchange/->FinalizedSourceRun) marker (Object.)]
    (#'lineage/registered-header! state header lineage/finalizer-label lineage/finalizer-sha
      ["object" "object" "tagged"] [false false false] "object")
    (swap! cell assoc :helper-headers helper-headers)
    (#'exchange/watch-owners! (:runtime-holder s) cell)
    ;; No Run token is stored in the Closure value, preventing cross-weak cycles.
    (try
      (swap! holder assoc :status :finalizing :attempt-marker marker)
      (swap! (:runtime-holder s) assoc :active marker)
      (put! @#'lineage/runs run-token cell)
      (put! runs token {:closure closure :lineage-run run-token :cell cell})
      (#'lineage/start-call! cell :io-result header lineage/finalizer-label
        [(#'exchange/root-value (:state-slot s)) (#'exchange/root-value (:imports-slot s)) 0]
        [(:state-slot s) (:imports-slot s)])
      token
      (catch Throwable cause
        (#'lineage/fail! cell cause)
        (swap! holder assoc :status :failed)
        (swap! (:runtime-holder s) assoc :status :failed :active nil)
        (throw (ex-info "Source finalizer start failed; preserve actual Run and Closure owners" {:run token :closure closure} cause))))))
(defn poll-finalizer! [token budget]
  ;; Argument rejection is pre-effect and must not quarantine a live attempt.
  (need (and (integer? budget) (<= 1 budget 20000)) "Bounded finalizer poll budget required")
  (let [{:keys [closure lineage-run]} (issued runs token)
        holder (issued closures closure) rh (:runtime-holder @holder)]
    (try
      (let [result (lineage/poll! lineage-run budget)]
        (when (= :ready (:status result))
          (closure! closure true)
          (let [actual (lineage/inspect! lineage-run)]
            (swap! holder assoc :status :finalized)
            (swap! rh assoc :active nil)
            (locking runs (.put runs token (assoc (issued runs token)
                                            :view (assoc actual :closure closure :basis :actual-source-closure-finalizer-only))))))
        (when (= :failed (:status result))
          (swap! holder assoc :status :failed)
          (swap! rh assoc :status :failed :active nil))
        result)
      (catch Throwable cause
        (swap! (issued closures closure) assoc :status :failed)
        (swap! rh assoc :status :failed :active nil)
        (throw cause)))))
(defn with-finalized! [token f]
  (let [{:keys [closure lineage-run view]} (issued runs token)
        holder (issued closures closure) s (closure! closure true)
        _ (need (= :finalized (:status s)) "Source finalizer has not actually completed")
        r (#'exchange/runtime! (:runtime-holder s))
        actual (lineage/inspect! lineage-run)]
    (need (and view (every? (fn [key] (identical? (get view key) (get actual key)))
                            [:engine :source :environment :kernel-root :constant-map :constants :code-receipt])
               (= [1 0 (:constant-count view)] [(:quot actual) (:empty actual) (:constant-count actual)]))
          "Actual source finalizer anchors changed")
    (#'exchange/read-only! r
      #(try (f view) (finally (lineage/inspect! lineage-run) (closure! closure true))))))
(defn owner-packet [token]
  (let [{:keys [closure lineage-run status] :as entry} (issued runs token)]
    (if (= :retired status) entry
      {:run (lineage/owner-packet lineage-run)
       :closure (select-keys @(issued closures closure) [:status :state-slot :imports-slot :regions-slot])})))
(defn closure-owner-packet [token]
  (select-keys @(issued closures token) [:status :state-slot :imports-slot :regions-slot :retirement-output]))
(defn take-finalizer-retirement-owners!
  "Transfer only actual healthy completed finalizer occurrences. Revoke the
   checked adapter/Base first; this closes no borrowed original Prelude lease."
  [token]
  (let [{:keys [closure lineage-run] :as entry} (issued runs token)
        holder (issued closures closure) s (closure! closure true)
        r (#'exchange/runtime! (:runtime-holder s)) output (object-array 1)]
    (need (and (= :finalized (:status s)) (nil? (:active r))
               (= "idle" (j/phase (#'exchange/context r) (:engine r)))) "Source Run retirement requires ready idle custody")
    (with-finalized! token identity)
    (put! runs token (assoc entry :retirement-output output))
    (let [packet (lineage/take-retirement-owners! lineage-run)]
      (aset ^objects output 0 packet)
      (swap! holder assoc :status :run-retired)
      (put! runs token {:status :retired :retirement-output output})
      packet)))
(defn take-closure-retirement-owners!
  "Transfer prepared inputs/regions, or the remaining regions after Run owners
   were transferred. A pending/failed normal root is never unwound here."
  [token]
  (let [holder (issued closures token) s @holder
        _ (need (contains? #{:prepared :run-retired} (:status s)) "Source Closure still has active/failed finalizer custody")
        r (#'exchange/runtime! (:runtime-holder s))
        owned (#'exchange/known-owned-slots! r [(:state-slot s) (:imports-slot s) (:regions-slot s)])
        packet (mapv #'exchange/root-value owned) output (object-array [packet])]
    (swap! holder assoc :retirement-output output :status :retirement-prepared)
    (doseq [slot owned] (aset ^objects slot 1 :external-retirement))
    (reset! holder {:status :retired :retirement-output output})
    packet))

(defn revoke-runtime-metadata!
  "Internal terminal callback AFTER runtime owner-slot transfer. No guest release
   or implicit ownership discharge; caller already owns the actual output table."
  [runtime-holder]
  (locking runs
    (doseq [entry (.entrySet runs)
            :let [value (.getValue ^java.util.Map$Entry entry)
                  closure-cell (when (:closure value) (issued closures (:closure value)))]
            :when (and closure-cell (identical? runtime-holder (:runtime-holder @closure-cell)))]
      (reset! (:cell value) {:status :retired})
      (.setValue ^java.util.Map$Entry entry {:status :retired})))
  (locking closures
    (doseq [entry (.entrySet closures) :let [cell (.getValue ^java.util.Map$Entry entry)]
            :when (identical? runtime-holder (:runtime-holder @cell))]
      (reset! cell {:status :retired}))) nil)
