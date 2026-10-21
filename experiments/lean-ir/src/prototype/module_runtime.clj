(ns prototype.module-runtime
  "Link and execute producer-ordered module initialization on a guest world.
   Native kernel FFI and missing extern implementations are not supplied here.
   Pinned Lean 4.33.1 LCNF.EmitC.emitInitFn sets its once guard before imports
   and keeps it set after failure. Checkpoint resume explicitly restores an
   earlier world; it is never a retry on that partially initialized world."
  (:refer-clojure :exclude [run])
  (:require [prototype.module-plan :as module-plan]
            [prototype.initialization :as initialization]
            [prototype.import-ir :as ir]
            [prototype.runtime-abi :as abi]
            [prototype.machine :as m]
            [prototype.mutable :as u]
            [prototype.lazy-runtime :as lazy]))

(defn- plans-from [catalogue]
  (reduce (fn [plans manifest]
            (if-let [plan (:initializationPlan manifest)]
              (let [module (:module plan)]
                (when-not (= "lean-init-plan/1" (:schema plan))
                  (m/fail "Unsupported producer module initialization plan" {:module module :schema (:schema plan)}))
                (when (and (contains? plans module) (not= (get plans module) plan))
                  (m/fail "Conflicting producer module initialization plans" {:module module}))
                (assoc plans module plan))
              plans)) {} (:manifests catalogue)))

(defn link
  "Link ROOTS and all actions reached by ROOT-MODULE's phase (default :all).
   Options :initialized-modules skips already entered module/phase guards.
   Optional :lower supplies a row lowerer (e.g. explicit public host bindings
   followed by the deferred raw ABI); producer ABI is still recorded here.
   Keep original ABI manifests and export aliases while replacing their plans
   with one classic execution plan; no producer runtime profiles are invented."
  ([catalogue root-module roots] (link catalogue root-module roots {}))
  ([catalogue root-module roots {:keys [phase initialized-modules lower existing-functions existing-program-abi]
                               :or {phase :all initialized-modules #{} existing-functions {} existing-program-abi {}}}]
   (let [plans (plans-from catalogue)
         expanded (module-plan/expand plans root-module phase initialized-modules)
         synthetic {:schema "lean-init-plan/1" :moduleSystem false
                    :module root-module :imports [] :actions (:actions expanded)}
         manifests (mapv #(dissoc % :initializationPlan) (:manifests catalogue))
         execution-catalogue (assoc catalogue :manifests
                                    (assoc-in manifests [0 :initializationPlan] synthetic))
         program-abi (atom existing-program-abi)
         linked (initialization/link-local-plan
                 execution-catalogue roots
                 (fn [row]
                   (when-let [decl (or (get-in row [:ir :fdecl]) (get-in row [:ir :extern]))]
                     (swap! program-abi assoc (:name row)
                            {:params (mapv #(select-keys % [:ty :borrow]) (:xs decl))
                             :return-type (:type decl)}))
                   ((or lower #(abi/lower-deferred-catalogue catalogue %)) row))
                 {:existing-functions existing-functions})]
     (assoc linked :expanded expanded :module-plans plans :root-module root-module
            :phase phase :previously-initialized initialized-modules
            :runtime-profiles (set (map #(select-keys % [:schema :leanVersion :runtimeProfile]) (:manifests catalogue)))
            :program-abi @program-abi))))

(defn- target-for [functions {:keys [action]}]
  (case (:kind action)
    "initialize" (or (get-in functions [(:name action) :init-target])
                     (m/fail "Initialized module value has no initializer wrapper" {:name (:name action)}))
    "value" (:name action)
    "io" ["str" (:name action) "_ansatz_io_initializer"]
    (m/fail "Unknown module initialization action" {:action action})))

(defn- reference-run [state fuel current]
  ;; Retain the latest immutable state if a later instruction throws. The
  ;; normal reference runner otherwise discards that state while unwinding.
  (loop [state state remaining fuel]
    (reset! current state)
    (if (or (not= :running (:status state)) (zero? remaining))
      (let [state (m/run state 0)] (reset! current state) state)
      (let [result (m/run state 1)
            result (if (and (= :paused (:status result)) (> remaining 1))
                     (m/resume result nil) result)]
        (recur result (dec remaining))))))

(defn- validate-options! [backend fuel {:keys [checkpoint checkpoint-every] :or {checkpoint-every 100}}]
   (when-not (contains? #{:reference :mutable :jvm} backend)
     (m/fail "Unknown module initialization backend" {:backend backend}))
   (when-not (and (integer? fuel) (<= 0 fuel)) (m/fail "Invalid step budget" {:fuel fuel}))
   (when-not (and (integer? checkpoint-every) (pos? checkpoint-every))
     (m/fail "Invalid module checkpoint interval" {:checkpoint-every checkpoint-every}))
   (when (and checkpoint (not (instance? clojure.lang.IAtom checkpoint)))
     (m/fail "Module checkpoint destination must be an atom" {})))

(defn- progress [linked next-action]
  {:root-module (:root-module linked) :phase (:phase linked) :next-action next-action})

(defn- make-checkpoint [linked expanded initialized next-action state complete?]
  {:schema "lean-module-checkpoint/1"
   :root-module (:root-module linked) :phase (:phase linked)
   :module-plans (:module-plans linked) :actions (:actions expanded)
   :runtime-profiles (:runtime-profiles linked) :program-abi (:program-abi linked)
   :base-initialized initialized :next-action next-action :complete? complete?
   :snapshot (if complete? state
               (assoc state :module-initialization-progress (progress linked next-action)))})

(defn- execute
  [linked initial expanded initialized start-index backend fuel
   {:keys [checkpoint checkpoint-every code-cache] :or {checkpoint-every 100}}]
  (let [functions (:functions linked) actions (:actions expanded)
           current (atom (if (= :reference backend) initial (u/thaw initial)))
           snapshot #(if (= :reference backend) @current (u/freeze @current))
           program (when (= :jvm backend)
                     (if code-cache (lazy/open-program functions {} code-cache) (lazy/open-program functions)))
           clean (atom nil)
           publish! (fn [next-action state complete?]
                      (let [boundary (make-checkpoint linked expanded initialized next-action state complete?)]
                        (reset! clean boundary)
                        (when checkpoint (reset! checkpoint boundary))))]
       ;; This snapshot precedes any action, so even the first failed initializer
       ;; has a clean rollback point. Never replace it with the failing heap.
       (publish! start-index initial false)
       (doseq [index (range start-index (count actions)) :let [action (nth actions index)]]
         (try
           (let [target (target-for functions action)
                 status (if (= :reference backend)
                          (let [started (m/start @current target [])]
                            (reset! current started)
                            (:status (reference-run started fuel current)))
                          (do (u/start! @current target [])
                              (reset! current (if (= :jvm backend) (lazy/run! program @current fuel)
                                                 (u/run! @current fuel)))
                              (u/status @current)))]
             (when-not (= :done status)
               (m/fail "Module initializer did not complete" {:status status}))
             (when (zero? (mod (inc index) checkpoint-every))
               (publish! (inc index) (snapshot) false)))
           (catch Exception cause
             (let [state (assoc (snapshot) :module-initialization-failure (progress linked index))]
               (throw (ex-info (str "Module initialization failed: " (.getMessage cause))
                               (assoc (ex-data cause) :module-action action :action-index index
                                      :snapshot state :checkpoint @clean) cause))))))
       (let [result (-> (snapshot) initialization/finish
                        (assoc :initialized-modules (:initialized expanded)))]
         (publish! (count actions) result true)
         result)))

(defn run
  "Execute module actions with FUEL per action; mutable/JVM backends thaw once.
   :checkpoint atom receives clean boundaries initially, every :checkpoint-every
   actions (default100), and on success. On failure its last clean boundary is
   preserved; exception data contains that :checkpoint and a separate partial
   :snapshot which must never be used as a fresh world. Use resume to roll back.
   Interval1 captures every completed action. Larger intervals replay actions
   after the saved boundary in the restored guest world. External side effects
   cannot be rolled back and are unsupported by this initialization runner."
  ([linked world backend fuel] (run linked world backend fuel {}))
  ([{:keys [functions module-plans root-module phase previously-initialized] :as linked}
    world backend fuel options]
   (validate-options! backend fuel options)
   (when-not (identical? functions (:functions world))
     (m/fail "Module initialization program mismatch" {}))
   (when (or (:module-initialization-progress world) (:module-initialization-failure world)
             (contains? world :initialization-scope))
     (m/fail "Module initialization world is incomplete; use a clean checkpoint with resume" {}))
   (when (contains? #{:running :paused :suspended :host-call} (:status world))
     (m/fail "Module initialization would discard an active continuation" {:status (:status world)}))
   (let [initialized (or (:initialized-modules world) #{})]
     (when-not (every? initialized previously-initialized)
       (m/fail "World lacks module guards assumed during linkage" {}))
     (execute linked (initialization/begin world)
              (module-plan/expand module-plans root-module phase initialized)
              initialized 0 backend fuel options))))

(defn- validate-upgrade! [linked boundary]
  (let [old-functions (get-in boundary [:snapshot :functions]) functions (:functions linked)]
    (when-not (= (:runtime-profiles boundary) (:runtime-profiles linked))
      (m/fail "Checkpoint producer runtime ABI mismatch" {}))
    (when-not (and (every? #(contains? functions %) (keys old-functions))
                   (= (:program-abi boundary)
                      (select-keys (:program-abi linked) (keys (:program-abi boundary))))
                   (every? (fn [[name function]]
                             (and (= (count (:params function)) (count (:params (get functions name))))
                                  ;; Synthetic/external preserved code may lack
                                  ;; a producer ABI. Such bodies cannot change.
                                  (or (contains? (:program-abi boundary) name)
                                      (and (= function (get functions name))
                                           (= (meta function) (meta (get functions name))))))) old-functions))
      (m/fail "Checkpoint program upgrade changed an existing declaration ABI" {}))))

(defn resume
  "Continue from a clean immutable checkpoint, possibly on another backend.
   Validate root, phase, producer plans, action order, boundary and scope first.
   Normally require the same linked functions object. :allow-program-upgrade
   explicitly permits implementation changes (e.g. replacing a trapped extern)
   with unchanged existing declaration ABI and producer runtime profile. Extra
   dependencies may be linked; old declarations cannot disappear or change arity.
   Replaces snapshot functions intentionally in that case, then starts exactly
   at :next-action. Failed partial snapshots are not accepted as checkpoints."
  ([linked boundary backend fuel] (resume linked boundary backend fuel {}))
  ([{:keys [module-plans root-module phase functions] :as linked}
    boundary backend fuel {:keys [allow-program-upgrade] :as options}]
   (validate-options! backend fuel options)
   (when-not (= "lean-module-checkpoint/1" (:schema boundary))
     (m/fail "Unsupported module checkpoint" {}))
   (when-not (and (= root-module (:root-module boundary)) (= phase (:phase boundary))
                  (= module-plans (:module-plans boundary)))
     (m/fail "Checkpoint module plan/root/phase mismatch" {}))
   (let [initialized (:base-initialized boundary)
         expanded (module-plan/expand module-plans root-module phase initialized)
         actions (:actions expanded) index (:next-action boundary) world (:snapshot boundary)]
     (when-not (and (= actions (:actions boundary)) (integer? index) (<= 0 index (count actions))
                    (contains? #{true false} (:complete? boundary)))
       (m/fail "Checkpoint action sequence or boundary mismatch" {}))
     (when-not (every? initialized (:previously-initialized linked))
       (m/fail "Checkpoint lacks module guards assumed during linkage" {}))
     (when (:module-initialization-failure world) (m/fail "Failed partial world is not a clean checkpoint" {}))
     (when (or (contains? #{:running :paused :suspended :host-call} (:status world)) (seq (:frames world)))
       (m/fail "Checkpoint contains an active action" {}))
     (if (:complete? boundary)
       (when-not (and (= index (count actions))
                      (= (:initialized expanded) (:initialized-modules world))
                      (not (contains? world :initialization-scope))
                      (not (:module-initialization-progress world)))
         (m/fail "Completed checkpoint has invalid module guards or scope" {}))
       (when-not (and (true? (:initializing? world)) (map? (:initialization-scope world))
                      (every? #{:initializing?} (keys (:initialization-scope world)))
                      (= (progress linked index) (:module-initialization-progress world))
                      (= initialized (or (:initialized-modules world) #{})))
         (m/fail "Checkpoint initialization scope or module guards mismatch" {})))
     (when-not (identical? functions (:functions world))
       (if allow-program-upgrade (validate-upgrade! linked boundary)
         (m/fail "Checkpoint program mismatch; implementation upgrades require explicit opt-in" {})))
     (let [world (-> world (assoc :functions functions) (dissoc :module-initialization-progress))]
       (if (:complete? boundary)
         (do (when-let [checkpoint (:checkpoint options)]
               (reset! checkpoint (make-checkpoint linked expanded initialized index world true))) world)
         (execute linked world expanded initialized index backend fuel options))))))
