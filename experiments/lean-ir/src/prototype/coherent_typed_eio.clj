(ns prototype.coherent-typed-eio
  "Captured experiment controller. Definitions only; no automatic preparation.
   Genuine source/Project acceptance requires a separately admitted stage."
  (:require [prototype.typed-eio :as eio]
            [prototype.resident-frontend :as resident]
            [prototype.resident-init-prefix :as prefix]
            [prototype.project-loader :as project]))

(defonce ^:private state (atom {:phase :ready :contexts [] :effects [] :returned []}))
(def ^:private symbol-name "ansatz_app_eio_text")
(def builders {:ok ["str" ["str" ["anonymous"] "EIOResultBuilders"] "success"]
               :error ["str" ["str" ["anonymous"] "EIOResultBuilders"] "failure"]})
(defn checkpoint "Private ownership packet; never print or serialize." [] @state)
(defn- check! [condition message] (when-not condition (throw (ex-info message {}))))
(defn- public-op [space member]
  (let [v (some-> (find-ns space) (ns-resolve member))]
    (check! (and (var? v) (bound? v) (fn? @v) (not (:private (meta v))))
            "Actual reviewed public controller operation missing") @v))
(defn- own! [context] (swap! state update :contexts conj context) context)
(defn- preserved! []
  (let [{:keys [borrowed-context borrowed-before source]} @state]
    (check! (and borrowed-context (false? @(:closed source))
                 (identical? borrowed-before (resident/snapshot borrowed-context)))
            "Borrowed original admission/Source changed or closed")))

(defn prepare-prefix!
  "Borrow the fresh checked pre-prefix admission. EIO helper code must ALREADY
   have joined its independent registry before graph/evaluator sealing. Create
   and retain four private Context wrappers; source/lease remain borrowed."
  [admission]
  (let [before @state]
    (check! (and (= :ready (:phase before))
                 (compare-and-set! state before (assoc before :phase :preparing)))
            "EIO application prefix preparation already claimed"))
  (try
    (let [configuration (:configuration admission) borrowed (:opened-context admission)
          before (resident/snapshot borrowed) source (first (get-in before [:world :native-imports]))
          _ (swap! state assoc :borrowed-context borrowed :borrowed-before before :source source)
          _ (check! (and (map? configuration) (empty? (:application-extern-symbols configuration))
                         (not (contains? (:trusted-bindings configuration) symbol-name)))
                    "Original independent application configuration required")
          _ (doseq [[_ name] builders]
              (check! (and (get-in configuration [:trusted-functions name])
                           (identical? (get-in configuration [:trusted-functions name])
                                       (get-in before [:world :functions name])))
                      "EIO builder was not independently linked before sealing"))
          selected (ex-info "Expected JVM service failure" {:application-host-exception true})
          service (eio/controller
                   {:signature eio/signature :builders builders
                    :fn (fn [text]
                          (check! (and (string? text) (<= (count text) 4096))
                                  "Bounded immutable service input required")
                          (let [old @state]
                            (check! (< (count (:effects old)) 32) "Finite EIO service event cap exhausted"))
                          ;; This external state is shared by all guest forks.
                          (swap! state update :effects conj text)
                          (cond (= text "host-failure") (throw selected)
                                (= text "domain-error") {:error text}
                                :else {:ok text}))})
          app {symbol-name (:binding service)}
          _ (swap! state assoc :service service :expected-host-failure selected)
          native (:prefix-native-bindings admission)
          original-native (get-in admission [:checked-record :support :session :bindings])
          routing #{"lean_compacted_region_read" "lean_compacted_region_free" "lean_eval_const"}
          _ (check! (and (map? native) (map? original-native)
                         (= (set (keys native)) (set (keys (:trusted-bindings configuration))))
                         (every? (fn [[symbol binding]]
                                   (or (contains? routing symbol)
                                       (identical? binding (get-in configuration [:trusted-bindings symbol])))) native)
                         (identical? (get original-native "lean_run_mod_init_core")
                                     (get native "lean_run_mod_init_core"))
                         (not (contains? native symbol-name)))
                    "Independently retained prepared native registry required; preserve original initializer")
          allow (assoc configuration :application-extern-symbols #{symbol-name})
          admitted (own! (resident/adopt-prepared before allow))
          configured (own! (resident/with-externs admitted app))
          independent (update allow :trusted-bindings merge app)
          native-next (merge native app)
          application (own! (resident/adopt-prepared (resident/snapshot configured) independent))
          fresh (prefix/prepare-init-prefix application (get-in admission [:checked-record :checked])
                                            {:configuration independent :native-bindings native-next})
          _ (own! (:context fresh))]
      (swap! state assoc :configuration independent :prefix-result fresh :phase :prefix-ready)
      (preserved!)
      {:phase :prefix-ready :owned-contexts 4 :service-effects 0 :source-closed false})
    (catch Throwable cause
      (swap! state assoc :phase :failed :failure cause)
      (throw cause))))

(defn assert-no-compilation-effects! []
  (check! (and (= :prefix-ready (:phase @state)) (empty? (:effects @state)))
          "EIO service effects occurred during source compilation")
  (preserved!) true)

(defn invoke!
  "Perform one explicit public IO call with a bounded service allowance. Caller
   must retain/close the returned child Project. A thrown call cannot be followed
   by another call until its issued failure capsule has been disposed."
  [version module name values signature maximum-calls]
  (let [{:keys [service phase pending-failure returned]} @state]
    (check! (and (= :prefix-ready phase) (nil? pending-failure) (< (count returned) 16))
            "EIO service call unavailable, failed or invocation cap exhausted")
    (try
      (let [result ((:invoke! service) maximum-calls
                    #(project/invoke-io version module name values signature))]
        ;; Capture the issued child before any additional fallible assertion.
        (swap! state update :returned conj result)
        (preserved!) result)
      (catch Throwable cause
        (swap! state assoc :pending-failure cause)
        (throw cause)))))

(defn dispose-call-failure!
  "Retire only this controller's exact pending issued failure. Expected failure
   classification belongs to the stage; this function never silently consumes an
   arbitrary error. No external effect is undone or retried."
  [cause]
  (check! (and (= :prefix-ready (:phase @state))
               (identical? cause (:pending-failure @state))
               (:project-failure-diagnostic (ex-data cause)))
          "Matching pending issued Project failure required")
  (let [receipt (project/dispose-failure! (:project-failure-diagnostic (ex-data cause)))]
    (preserved!)
    (swap! state dissoc :pending-failure)
    receipt))

(defn close-contexts!
  "Call after all issued Projects and children have closed. Retire only the four
   owned prefix/adoption wrappers, then drop their private strong references."
  []
  (let [{:keys [phase contexts effects pending-failure]} @state]
    (check! (and (= :prefix-ready phase) (nil? pending-failure) (= 4 (count contexts)))
            "Normal EIO cleanup requires completed call disposition")
    (doseq [context (reverse contexts)] (resident/close! context))
    (preserved!)
    (reset! state {:phase :closed :closed-contexts 4 :service-effects (count effects)})
    {:phase :closed :closed-contexts 4 :service-effects (count effects)
     :original-admission-preserved true :borrowed-source-closed false}))
