(ns java-prelude-finalizer-lineage-v1
  "Trusted normal-root execution wrapper. Owns actual start/take transitions,
   never accepts a preexisting Env/result as a successful finalizer certificate.
   No paired-artifact, kernel association, imported proof or IR authority."
  (:require [java-ir-baseline :as j] [ansatz.research.ir.source-setup :as source]
            [ansatz.research.ir.composite-source-v4 :as v4])
  (:import [java.util WeakHashMap]
           [java.lang.reflect InvocationTargetException]))
(deftype Run [])
(defonce ^:private runs (WeakHashMap.))
(defonce ^:private engines (WeakHashMap.)) ; weak engine -> immutable marker, no key-retaining value
(def finalizer-label "JavaModuleImport.finalize._boxed")
(def finalizer-sha "f2d9a2b94540985d6cee145a6d0d2f60b2b96a38d2fa268b568aa7bcf915f53b")
(def helpers [["checkedKernelRoot" :kernel "object"] ["checkedConstantMapRoot" :map "object"]
              ["checkedQuotInit" :quot "tagged"] ["checkedEnvironmentIsEmpty" :empty "tagged"]
              ["checkedConstants" :constants "object"]])
(defn- need [condition message] (when-not condition (throw (ex-info message {:profile :actual-finalizer-lineage-v1}))))
(defn- field [object key]
  (.get (doto (.getDeclaredField (class object) key) (.setAccessible true)) object))
(defn- guard-node [engine method value]
  (try (.invoke (doto (.getDeclaredMethod (class engine) method (into-array Class [Object])) (.setAccessible true))
                engine (object-array [value]))
       (catch InvocationTargetException cause (throw (.getCause cause)))))
(defn- entry [run]
  (locking runs (or (.get runs run) (throw (ex-info "Actual issued finalizer Run required" {})))))
(defn- context [state] @(:current-ctx (:driver state)))
(defn- value [slot] (aget ^objects slot 0))
(defn- disposition [slot] (aget ^objects slot 1))
(defn- status! [slot status] (aset ^objects slot 1 status))
(defn- new-owner! [cell key item status]
  (need (not (contains? (:owners @cell) key)) "Duplicate lineage owner occurrence")
  (let [slot (object-array [item status])]
    (swap! cell assoc-in [:owners key] slot) slot))
(defn- registered-header! [state header label expected-sha params borrowed result]
  (let [ctx (context state) src (:source (:driver state))
        row-entry (source/lookup-entry (:code-receipt state) (j/lean-name-data (j/request-value header "name")))
        _ (need (= expected-sha (:sha256 row-entry)) "Finalizer/helper original source SHA differs")
        _ (source/authenticate-canonical-header! src (:row row-entry) expected-sha header)
        id (.invoke (.getMethod (class (:program ctx)) "functionId" (into-array Class [(class header)]))
                    (:program ctx) (object-array [header]))]
    (need (and (= id (j/function-id ctx label)) (= "fdecl" (j/request-value header "kind"))
               (= params (vec (j/request-value header "paramTypes")))
               (= borrowed (vec (j/request-value header "borrowed")))
               (= result (j/request-value header "resultType"))) "Finalizer/helper registered Header ABI differs")
    header))
(def startup-sha "4f9e45cb51441d02006a0a8404f9feb1d13ecffad196cc95d1642d81ed44f66d")
(defn- startup-cache! [s]
  (let [header (:startup-header s) ctx (context s) e (:engine s)
        _ (registered-header! s header "JavaModuleImport.finalize._boxed_const_1" startup-sha [] [] "tobject")
        id (int (j/function-id ctx "JavaModuleImport.finalize._boxed_const_1"))
        ready ^booleans (field e "constantReady") retired ^booleans (field e "constantRetired")
        values ^objects (field e "constants")]
    (need (and (<= 0 id) (< id (alength ready)) (< id (alength retired)) (< id (alength values))
               (aget ready id) (not (aget retired id))
               (instance? Long (aget values id)) (= 0 (aget values id)))
          "Actual same-source UInt32-zero local startup cache is not ready")))
(defn- live! [cell]
  (let [s @cell]
    (need (contains? #{:active :ready} (:status s)) "Finalizer lineage is failed or retired")
    (need (identical? (:thread s) (Thread/currentThread)) "Finalizer lineage is thread confined")
    (let [d (:driver s) ctx (context s) engine (:engine d)]
    (need (and (identical? (:class ctx) (class engine)) (identical? (:engine s) engine)
               (identical? (:source s) (:source d)) (identical? (:program ctx) (field engine "program"))) "Foreign engine/source/current Program")
    (doseq [key ["closed" "disposed" "untrackedFailure" "advancing"]]
      (need (false? (field engine key)) "Engine lifecycle cannot lend finalizer lineage"))
    (source/guard-source! (:code-receipt s) (:source d))
    (let [profile (source/code-profile (:code-receipt s)) entries (get profile "overlays")]
      (need (and (= 2 (count entries))
                 (= v4/shim-pins (select-keys (first entries) (keys v4/shim-pins)))
                 (= v4/module-pins (select-keys (second entries) (keys v4/module-pins)))
                 (= v4/actions (get profile "local_initialization_actions"))) "Wrong fixed composite source/action profile"))
    ((:check-leases! (:options s)))
    (need (= (:startup-snapshot s) (select-keys @(:startup-status s) [:state :label :actual-body-executed :result-released])) "Actual startup status changed")
    (startup-cache! s)
    (when (= :active (:status s))
      (need (<= (System/nanoTime) (get-in s [:options :deadline-nanos])) "Finalizer lineage execution deadline exceeded"))
    s)))
(defn- fail! [cell cause]
  (when (= :active (:status @cell))
    (let [text (or (.getMessage ^Throwable cause) "Finalizer wrapper failure")]
      (swap! cell assoc :status :failed :failure {:message (subs text 0 (min 900 (count text))) :class (.getName (class cause))})))
  {:status (:status @cell) :failure (:failure @cell)})
(defn- retain! [cell key item]
  (let [s (live! cell) slot (new-owner! cell key item :retain-pending)]
    (j/retain! (context s) (:engine s) item)
    (status! slot :owned) slot))
(defn- start-call! [cell call-key header label args input-slots]
  (let [s (live! cell) ctx (context s) e (:engine s)]
    (need (= "idle" (j/phase ctx e)) "Normal root call requires IDLE")
    (need (nil? (:call s)) "Normal root call already active")
    ;; Record before start. A thrown start is not assumed to roll back ownership.
    (swap! cell assoc :call {:key call-key :header header :label label :args args :last-instructions 0 :taken? false})
    (doseq [slot input-slots] (need (= :owned (disposition slot)) "Input occurrence not owned") (status! slot :start-pending))
    (j/start! ctx e label args)
    (doseq [slot input-slots] (status! slot :transferred))
    nil))
(defn- current-root! [cell]
  (let [s (live! cell) call (:call s) ctx (context s) e (:engine s)
        actual (field e "entry") instructions (j/instructions ctx e)]
    (need (and call actual (identical? (:header call) (field actual "header"))) "Actual normal root Header changed or result was taken")
    (need (<= (:last-instructions call) instructions (get-in s [:options :max-instructions])) "Normal root instruction bound/progression differs")
    (swap! cell assoc-in [:call :last-instructions] instructions)
    s))
(defn- fields [s node] (.get ^java.lang.reflect.Field (:fields (context s)) node))
(defn- ordinary! [s node tag count]
  (guard-node (:engine s) "constructorNode" node)
  (need (and (nil? (field node "closure")) (= tag (.getInt ^java.lang.reflect.Field (:tag (context s)) node))
             (= count (alength ^objects (fields s node)))
             (zero? (alength ^bytes (.get ^java.lang.reflect.Field (:scalars (context s)) node)))) "Wrong IO success constructor representation")
  node)
(defn- take-call! [cell]
  (let [s (current-root! cell) ctx (context s) e (:engine s) call (:call @cell)]
    (need (= "complete" (j/phase ctx e)) "Normal root did not actually complete")
    ;; Publish a reserved occurrence BEFORE claiming the engine result. No
    ;; allocation is required between take-result! and assigning that owner.
    (let [slot (new-owner! cell (:key call) nil :take-pending)
          answer (j/take-result! ctx e)]
      (aset ^objects slot 0 answer) (status! slot :owned)
      (swap! cell #(-> % (update :history conj (assoc call :taken? true :result-slot slot)) (assoc :call nil)))
      (if (= :io-result (:key call))
        (let [s @cell _ (ordinary! s answer 0 1) env (aget ^objects (fields s answer) 0)]
          (guard-node e "constructorNode" env)
          (retain! cell :environment env)
          (swap! cell assoc :helper-index 0 :stage :helpers))
        (swap! cell update :helper-index inc)))))
(defn- start-next-helper! [cell]
  (let [s (live! cell) i (:helper-index s)]
    (if (= i (count helpers))
      (let [owner #(value (get (:owners s) %))
            array (guard-node (:engine s) "array" (owner :constants))
            n (.arraySize array)]
        (need (and (instance? Long (owner :quot)) (= 1 (owner :quot))
                   (instance? Long (owner :empty)) (= 0 (owner :empty))
                   (= (get-in s [:options :expected-constants]) n)) "Actual finalizer helper quotient/empty/domain witness differs")
        (guard-node (:engine s) "constructorNode" (owner :kernel))
        (guard-node (:engine s) "constructorNode" (owner :map))
        (swap! cell assoc :status :ready :stage :ready :constant-count n))
      (let [[label key _] (nth helpers i) env (value (get-in s [:owners :environment]))
            input (retain! cell (keyword (str "helper-input-" i)) env)
            header (get (:helper-headers s) key)]
        (start-call! cell key header (str "KernelBridgeShim." label "._boxed") [env] [input])))))
(defn begin!
  "Trusted parent hands actual owned state/import occurrence slots to this run.
   Input/lease callbacks independently check admitted module/request ownership and
   actual flags; this wrapper fixes neither importAll nor isExported. Callbacks
   may service only the supplied current Code/Host request, never start/take a root.
   Returns a pending opaque Run, or throws before start; never seals an old Env."
  [parent {:keys [finalizer-header state-slot imports-slot check-leases! validate-inputs! service-code! service-host!
                 quantum max-transitions max-instructions deadline-nanos expected-constants] :as options}]
  (need (and (every? fn? [check-leases! validate-inputs! service-code! service-host!])
             (every? #(and (integer? %) (pos? %)) [quantum max-transitions max-instructions deadline-nanos expected-constants])
             (<= quantum 1000) (<= expected-constants 10000)) "Explicit finite root execution/lease/input policy required")
  (let [d (:driver parent) e (:engine d) startup (:startup-status parent) snapshot (select-keys @startup [:state :label :actual-body-executed :result-released])
        s {:driver d :engine e :source (:source d) :code-receipt (:code-receipt parent) :parent parent
           :thread (Thread/currentThread) :startup-status startup :startup-snapshot snapshot
           :startup-header (first (get-in parent [:configuration :local-action-headers])) :options options
           :status :active :stage :finalizer :owners {} :history [] :call nil :transitions 0}
        cell (atom s) token (Run.)]
    (need (= {:state :ready :label "JavaModuleImport.finalize._boxed_const_1" :actual-body-executed true :result-released true}
             (select-keys snapshot [:state :label :actual-body-executed :result-released])) "Actual local startup is not ready")
    (need (= 1 (count (get-in parent [:configuration :local-action-headers]))) "Exactly one actual local startup Header required")
    (live! cell)
    (need (= "idle" (j/phase (context s) e)) "Finalizer wrapper needs a fresh IDLE root boundary")
    (locking engines (need (not (.containsKey engines e)) "Finalizer engine already has an issued run"))
    (doseq [slot [state-slot imports-slot]]
      (need (and (instance? (class (object-array 0)) slot) (= 2 (alength ^objects slot)) (= :owned (disposition slot))) "Actual owned input occurrence slots required")
      )
    (guard-node e "constructorNode" (value state-slot))
    (guard-node e "array" (value imports-slot))
    (need (not (identical? state-slot imports-slot)) "Distinct input occurrences require distinct slots")
    (validate-inputs! e (:source d) (value state-slot) (value imports-slot))
    (registered-header! s finalizer-header finalizer-label finalizer-sha ["object" "object" "tagged"] [false false false] "object")
    (let [hs (into {} (for [[label key result] helpers
                           :let [h (get-in parent [:configuration :helper-headers (str "KernelBridgeShim." label "._boxed")])
                                 row (source/lookup-entry (:code-receipt s) (j/lean-name-data (j/request-value h "name")))]]
                       [key (registered-header! s h (str "KernelBridgeShim." label "._boxed") (:sha256 row) ["object"] [false] result)]))]
      (swap! cell assoc :helper-headers hs :owners {:state-input state-slot :imports-input imports-slot})
      (locking engines
        (need (not (.containsKey engines e)) "Finalizer engine already has an issued run")
        (.put engines e true))
      (locking runs (.put runs token cell))
      (try (start-call! cell :io-result finalizer-header finalizer-label [(value state-slot) (value imports-slot) 0] [state-slot imports-slot])
           token
           (catch Throwable cause (fail! cell cause) (throw (ex-info "Finalizer start failed; preserve issued Run owner packet" {:run token} cause)))))))
(defn poll!
  "Drive at most BUDGET transitions. Pause leaves the same pending normal root;
   no callback's descriptive return value can publish completion or readiness."
  [run budget]
  (need (and (integer? budget) (<= 1 budget 20000)) "Bounded finalizer poll budget required")
  (let [cell (entry run)]
    (try
      (loop [left budget]
        (let [s (live! cell) ctx (context s) e (:engine s)]
          (cond
            (= :ready (:status s)) {:status :ready :constants (:constant-count s)}
            (zero? left) {:status :budget :stage (:stage s) :phase (j/phase ctx e)}
            :else
            (do
              (need (< (:transitions s) (get-in s [:options :max-transitions])) "Finalizer total transition budget exceeded")
              (swap! cell update :transitions inc)
              (if-not (:call s)
                (do (start-next-helper! cell) (recur (dec left)))
                (let [_ (current-root! cell) phase (j/phase ctx e)]
                  (case phase
                    "running" (do (j/advance! ctx e (get-in s [:options :quantum])) (recur (dec left)))
                    "complete" (do (take-call! cell) (recur (dec left)))
                    "code-call" (let [request (j/code-request ctx e)]
                                  ((get-in s [:options :service-code!]) (:driver s) request)
                                  (current-root! cell)
                                  (if (identical? request (j/code-request (context @cell) e))
                                    {:status :needs-code :request request} (recur (dec left))))
                    "host-call" (let [request (j/host-request ctx e)]
                                  ((get-in s [:options :service-host!]) (:parent s) request)
                                  (current-root! cell)
                                  (if (identical? request (j/host-request (context @cell) e))
                                    {:status :needs-host :request request} (recur (dec left))))
                    (throw (ex-info "Unexpected normal-root phase" {:phase phase})))))))))
      (catch Throwable cause (fail! cell cause)))))
(defn inspect! [run]
  (let [cell (entry run) s (live! cell) owner #(value (get (:owners s) %))]
    (need (= :ready (:status s)) "Finalizer Run is not ready")
    (doseq [key [:io-result :environment :kernel :map :quot :empty :constants]]
      (need (= :owned (disposition (get (:owners s) key))) "Lineage owner occurrence was retired"))
    (ordinary! s (owner :io-result) 0 1)
    (need (identical? (owner :environment) (aget ^objects (fields s (owner :io-result)) 0)) "Original IO result Env changed")
    (doseq [key [:environment :kernel :map]] (guard-node (:engine s) "constructorNode" (owner key)))
    (let [array (guard-node (:engine s) "array" (owner :constants))]
      (need (= (:constant-count s) (get-in s [:options :expected-constants]) (.arraySize array))
            "Sealed checkedConstants Array/count changed"))
    (need (and (instance? Long (owner :quot)) (= 1 (owner :quot))
               (instance? Long (owner :empty)) (= 0 (owner :empty))) "Sealed quotient/empty result changed")
    {:engine (:engine s) :source (:source s) :code-receipt (:code-receipt s)
     :environment (owner :environment) :kernel-root (owner :kernel) :constant-map (owner :map)
     :quot (owner :quot) :empty (owner :empty) :constants (owner :constants) :constant-count (:constant-count s)
     :calls (mapv #(select-keys % [:key :header :args :taken? :last-instructions]) (:history s))
     :basis :actual-original-finalizer-only :kernel-association false}))
(defn owner-packet [run]
  (let [s @(entry run)] (select-keys s [:status :stage :owners :call :failure :transitions])))
(defn take-retirement-owners! [run]
  (let [cell (entry run) s @cell]
    (need (and (= :ready (:status s)) (= "idle" (j/phase (context s) (:engine s)))) "Lineage retirement requires ready IDLE boundary")
    (inspect! run)
    (let [owned (vec (for [[key slot] (:owners s) :when (= :owned (disposition slot))] [key (value slot)]))]
      (doseq [[_ slot] (:owners s) :when (= :owned (disposition slot))] (status! slot :external-retirement))
      (reset! cell {:status :retired})
      owned)))
