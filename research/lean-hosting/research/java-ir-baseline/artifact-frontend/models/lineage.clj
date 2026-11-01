(ns java-prelude-finalizer-lineage-models-v1
  "Control/owner metadata models only. Engine guards and canonical Header IO are
   modeled here; actual compiled-engine/source acceptance is a separate probe."
  (:require [clojure.test :refer [deftest is run-tests]]
            [java-prelude-finalizer-lineage-v1 :as l] [java-ir-baseline :as j]
            [ansatz.research.ir.source-setup :as source] [ansatz.research.ir.composite-source-v4 :as v4]))
(definterface Sized (arraySize []))
(deftype ModelArray [owner items] Sized (arraySize [_] (count items)))
(defn model [f]
  (let [program (Object.) engine (atom {:program program :phase "idle" :starts 0 :takes 0 :instructions 0
                                       :constantReady (boolean-array [true]) :constantRetired (boolean-array [false]) :constants (object-array [0])})
        src (Object.) code (Object.) headers (atom {}) startup {:label "JavaModuleImport.finalize._boxed_const_1" :sha l/startup-sha}
        finalizer {:label l/finalizer-label :sha l/finalizer-sha}
        hs (into {} (for [[label key result] l/helpers]
                       [(str "KernelBridgeShim." label "._boxed") {:label (str "KernelBridgeShim." label "._boxed") :sha (name key)}]))
        _ (reset! headers (into {l/finalizer-label finalizer (:label startup) startup} (map (fn [[k h]] [k h])) hs))
        ctor (fn [fields] {:owner engine :kind :ctor :tag 0 :fields (object-array fields)})
        env (ctor []) kernel (ctor []) cmap (ctor []) io (ctor [env])
        state (ctor []) imports (ModelArray. engine [::request]) constants (ModelArray. engine (repeat 2 ::ci))
        ctx (atom {:class (class engine) :program program})
        parent {:driver {:engine engine :source src :current-ctx ctx} :code-receipt code
                :startup-status (atom {:state :ready :label (:label startup) :actual-body-executed true :result-released true})
                :configuration {:local-action-headers [startup] :helper-headers hs}}
        responses {l/finalizer-label io "KernelBridgeShim.checkedKernelRoot._boxed" kernel
                   "KernelBridgeShim.checkedConstantMapRoot._boxed" cmap "KernelBridgeShim.checkedQuotInit._boxed" 1
                   "KernelBridgeShim.checkedEnvironmentIsEmpty._boxed" 0 "KernelBridgeShim.checkedConstants._boxed" constants}
        state-slot (object-array [state :owned]) imports-slot (object-array [imports :owned])
        opts {:finalizer-header finalizer :state-slot state-slot :imports-slot imports-slot
              :check-leases! (fn []) :validate-inputs! (fn [& _]) :service-code! (fn [& _]) :service-host! (fn [& _])
              :quantum 1000 :max-transitions 100 :max-instructions 10000 :deadline-nanos (+ (System/nanoTime) 10000000000) :expected-constants 2}
        node! (fn [e method v]
                (case method
                  "array" (do (assert (and (instance? ModelArray v) (identical? e (.-owner ^ModelArray v)))) v)
                  "constructorNode" (do (assert (and (= :ctor (:kind v)) (identical? e (:owner v)))) v)))
        low-field (fn [x key] (get (if (instance? clojure.lang.IDeref x) @x x) (keyword key)
                                  (when (contains? #{"closed" "disposed" "untrackedFailure" "advancing"} key) false)))]
    (with-redefs-fn
      {#'l/field low-field #'l/guard-node node!
       #'l/fields (fn [_ v] (:fields v))
       #'l/ordinary! (fn [_ v tag count] (assert (= tag (:tag v))) (assert (= count (alength ^objects (:fields v)))) v)
       #'l/registered-header! (fn [_ h label sha params borrowed result]
                               (assert (= label (:label h))) (assert (= sha (:sha h))) h)
       #'source/guard-source! (fn [receipt binding] (assert (identical? code receipt)) (assert (identical? src binding)))
       #'source/code-profile (fn [_] {"overlays" [v4/shim-pins v4/module-pins] "local_initialization_actions" v4/actions})
       #'source/lookup-entry (fn [_ name] {:sha256 (:sha (get @headers name))})
       #'j/request-value (fn [v k] (if (= k "name") (:label v) (get v (keyword k))))
       #'j/function-id (fn [& _] 0)
       #'j/phase (fn [_ e] (:phase @e)) #'j/instructions (fn [_ e] (:instructions @e))
       #'j/code-request (fn [_ e] (:code @e)) #'j/host-request (fn [_ e] (:host @e))
       #'j/start! (fn [_ e label args]
                    (assert (= "idle" (:phase @e)))
                    (swap! e #(-> % (update :starts inc) (assoc :entry {:header (get @headers label)} :phase "running"
                                                              :instructions 0 :response (get responses label)))))
       #'j/advance! (fn [_ e _] (swap! e assoc :phase "complete" :instructions 1))
       #'j/take-result! (fn [_ e] (assert (= "complete" (:phase @e)))
                          (let [r (:response @e)] (swap! e #(-> % (update :takes inc) (assoc :phase "idle" :entry nil))) r))
       #'j/retain! (fn [_ _ _])}
      #(f {:parent parent :options opts :engine engine :state-slot state-slot :imports-slot imports-slot :headers headers
           :env env :kernel kernel :map cmap :code code :source src}))))
(deftest complete-path-owns-every-actual-start-take-and-retirement
  (model (fn [{:keys [parent options engine state-slot imports-slot env]}]
           (let [run (l/begin! parent options)]
             (is (= :transferred (aget ^objects state-slot 1)))
             (is (= :transferred (aget ^objects imports-slot 1)))
             (is (= :ready (:status (l/poll! run 100))))
             (is (= 6 (:starts @engine) (:takes @engine)))
             (is (identical? env (:environment (l/inspect! run))))
             (is (= 7 (count (l/take-retirement-owners! run))))
             (is (thrown? Exception (l/inspect! run)))
             (is (thrown? Exception (l/begin! parent options)))))))
(deftest fake-header-cache-and-foreign-engine-refuse-before-start
  (model (fn [{:keys [parent options engine state-slot]}]
           (is (thrown? Throwable (l/begin! parent (assoc options :finalizer-header {:label l/finalizer-label :sha "forged"}))))
           (is (zero? (:starts @engine))) (is (= :owned (aget ^objects state-slot 1)))
           (let [program (:program @engine)]
             (swap! engine assoc :program (Object.))
             (is (thrown? Throwable (l/begin! parent options)))
             (is (zero? (:starts @engine)))
             (swap! engine assoc :program program))
           (aset ^booleans (:constantReady @engine) 0 false)
           (is (thrown? Throwable (l/begin! parent options)))
           (is (zero? (:starts @engine))))))
(deftest code-pause-never-restarts-or-accepts-callback-completion-flag
  (model (fn [{:keys [parent options engine]}]
           (let [run (l/begin! parent (assoc options :service-code! (fn [& _] {:status :ready :result :fake}))) request (Object.)]
             (swap! engine assoc :phase "code-call" :code request)
             (is (= :needs-code (:status (l/poll! run 2))))
             (is (= 1 (:starts @engine))) (is (zero? (:takes @engine)))
             (swap! engine assoc :phase "running" :code nil)
             (is (= :ready (:status (l/poll! run 100))))))))
(deftest foreign-root-or-stolen-result-is-terminal-and-preserves-slots
  (model (fn [{:keys [parent options engine]}]
           (let [run (l/begin! parent options)]
             (swap! engine assoc :entry {:header :foreign})
             (is (= :failed (:status (l/poll! run 2))))
             (is (= :failed (:status (l/owner-packet run))))
             (is (= 1 (:starts @engine))) (is (zero? (:takes @engine)))
             (is (thrown? Exception (l/begin! parent options)))))))
(deftest wrong-io-result-and-retain-failure-cannot-publish-ready-lineage
  (model (fn [{:keys [parent options engine]}]
           (let [run (l/begin! parent options)]
             (swap! engine assoc :response {:tag 1 :fields (object-array [])})
             (is (= :failed (:status (l/poll! run 3))))
             (is (= :owned (aget ^objects (get-in (l/owner-packet run) [:owners :io-result]) 1))))))
  (model (fn [{:keys [parent options]}]
           (with-redefs [j/retain! (fn [& _] (throw (ex-info "retention failure" {})))]
             (let [run (l/begin! parent options)]
               (is (= :failed (:status (l/poll! run 3))))
               (is (= :owned (aget ^objects (get-in (l/owner-packet run) [:owners :io-result]) 1)))
               (is (= :retain-pending (aget ^objects (get-in (l/owner-packet run) [:owners :environment]) 1))))))))
(defn check! [] (run-tests 'java-prelude-finalizer-lineage-models-v1))

(deftest additional-code-is-explicit-exact-and-startup-neutral
  (let [contract {"source_sha256" (apply str (repeat 64 "a"))
                  "local_ir_sha256" (apply str (repeat 64 "b"))
                  "export_receipt_sha256" (apply str (repeat 64 "c"))
                  "producer_sha256" v4/producer-sha "base_index_sha256" v4/index-sha
                  "module" ["str" ["anonymous"] "ObserverModel"]}
        plan {"schema" "lean-init-plan/1" "module" (get contract "module") "actions" []}
        base {"overlays" [v4/shim-pins v4/module-pins] "local_initialization_actions" v4/actions}
        extended (update base "overlays" conj (assoc contract "initializationPlan" plan))]
    (is (nil? (#'l/check-code-profile! base [])))
    (is (nil? (#'l/check-code-profile! extended [contract])))
    (is (thrown? Exception (#'l/check-code-profile! extended [])))
    (is (thrown? Exception (#'l/check-code-profile! base [contract])))
    (doseq [changed [(assoc-in extended ["overlays" 2 "local_ir_sha256"] (apply str (repeat 64 "d")))
                     (assoc-in extended ["overlays" 2 "initializationPlan" "actions"] [::action])
                     (assoc-in extended ["overlays" 2 "initializationPlan" "module"] ["anonymous"])
                     (assoc-in extended ["overlays" 2 "initializationPlan" "schema"] "other")
                     (assoc-in extended ["overlays" 2 "base_index_sha256"] (apply str (repeat 64 "d")))
                     (assoc-in extended ["overlays" 2 "producer_sha256"] (apply str (repeat 64 "e")))
                     (assoc extended "local_initialization_actions" [])
                     (update extended "overlays" conj (last (get extended "overlays")))]]
      (is (thrown? Exception (#'l/check-code-profile! changed [contract]))))
    (is (thrown? Exception (#'l/check-code-profile! extended [(assoc contract "unreviewed" true)])))))

(deftest explicit-overlay-policy-is-frozen-before-run-publication
  (model
    (fn [{:keys [parent options]}]
      (let [contract {"source_sha256" (apply str (repeat 64 "a"))
                      "local_ir_sha256" (apply str (repeat 64 "b"))
                      "export_receipt_sha256" (apply str (repeat 64 "c"))
                      "producer_sha256" v4/producer-sha "base_index_sha256" v4/index-sha
                      "module" ["str" ["anonymous"] "ObserverModel"]}
            plan {"schema" "lean-init-plan/1" "module" (get contract "module") "actions" []}
            profile {"overlays" [v4/shim-pins v4/module-pins (assoc contract "initializationPlan" plan)]
                     "local_initialization_actions" v4/actions}
            mutable-contract (java.util.HashMap. contract)
            mutable-list (doto (java.util.ArrayList.) (.add mutable-contract))]
        (with-redefs [source/code-profile (fn [_] profile)]
          (let [run (l/begin! parent (assoc options :extra-code-overlays mutable-list))]
            (.clear mutable-contract)
            (.clear mutable-list)
            (is (= :ready (:status (l/poll! run 100))))
            (is (= 7 (count (l/take-retirement-owners! run))))))))))


(deftest start-failure-reserves-pending-inputs-and-forbids-replay
  (model (fn [{:keys [parent options state-slot imports-slot]}]
           (with-redefs [j/start! (fn [& _] (throw (ex-info "start failed after preflight" {})))]
             (let [failure (try (l/begin! parent options) nil (catch Throwable cause cause))
                   run (:run (ex-data failure))]
               (is run)
               (is (= :failed (:status (l/owner-packet run))))
               (is (= :start-pending (aget ^objects state-slot 1)))
               (is (= :start-pending (aget ^objects imports-slot 1)))
               (is (thrown? Exception (l/begin! parent options))))))))
(deftest host-pause-preserves-same-active-root-and-ignores-callback-ready-flag
  (model (fn [{:keys [parent options engine]}]
           (let [run (l/begin! parent (assoc options :service-host! (fn [& _] {:status :ready}))) request (Object.)]
             (swap! engine assoc :phase "host-call" :host request)
             (is (= :needs-host (:status (l/poll! run 2))))
             (is (= 1 (:starts @engine))) (is (zero? (:takes @engine)))))))
