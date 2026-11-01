(ns prototype.initialization
  "Explicit selected-global initialization. This does not reconstruct Lean's
  complete module initializer order or anonymous parser registrations."
  (:require [prototype.machine :as m]
            [prototype.import-ir :as ir]
            [prototype.mutable :as u]
            [prototype.lazy-runtime :as lazy]))

(defn begin [world]
  (when (contains? #{:running :paused :suspended :host-call} (:status world))
    (m/fail "Initialization would discard an active continuation" {:status (:status world)}))
  (if (:initialization-scope world) world
    (assoc world :initializing? true
           :initialization-scope (select-keys world [:initializing?]))))

(defn finish
  "Restore initialization mode after a completed explicit initialization scope.
  A paused initializer retains its scope through snapshot/resume."
  [world]
  (when (contains? #{:running :paused :suspended :host-call} (:status world))
    (m/fail "Cannot finish an active initialization" {:status (:status world)}))
  (if-let [previous (:initialization-scope world)]
    (merge (dissoc world :initializing? :initialization-scope) previous)
    world))

(defn start [world name]
  (when (contains? #{:running :paused :suspended :host-call} (:status world))
    (m/fail "Initialization would discard an active continuation" {:status (:status world)}))
  (let [target (get-in world [:functions name :init-target])]
    (when-not target (m/fail "Not an explicitly initialized global" {:name name}))
    (m/start (begin world) target [])))

(defn run
  "Initialize the explicitly ordered selected globals in one world. Every action
  must complete within fuel; errors retain the last guest state in ex-data.
  Native module imports and anonymous registrations need their own ordered plan."
  ([world names] (run world names :reference 1000000))
  ([world names backend fuel]
   (when-not (contains? #{:reference :mutable :jvm} backend)
     (m/fail "Unknown initialization backend" {:backend backend}))
   (let [program (when (= backend :jvm) (lazy/open-program (:functions world)))]
     (finish (reduce (fn [world name]
               (let [initial (start world name)
                     result (case backend
                              :reference (m/run initial fuel)
                              :mutable (u/freeze (u/run! (u/thaw initial) fuel))
                              :jvm (u/freeze (lazy/run! program (u/thaw initial) fuel)))]
                 (when-not (= :done (:status result))
                   (m/fail "Global initializer did not complete" {:name name :snapshot result}))
                 result)) world names)))))

(defn action-names [plan]
  (when-not (= "lean-init-plan/1" (:schema plan))
    (m/fail "Unsupported initialization plan" {:schema (:schema plan)}))
  (mapv (fn [{:keys [action]}]
          (case (:kind action)
            ("value" "initialize") (:name action)
            "io" (:target action)
            (m/fail "Unknown initialization action" {:action action}))) (:actions plan)))

(defn link-local-plan
  "Link user roots AND every action of one producer-time local plan. Import
  module plans are deliberately not synthesized from sorted imported IR."
  ([catalogue roots lower] (link-local-plan catalogue roots lower {}))
  ([catalogue roots lower options]
  (let [plans (keep :initializationPlan (:manifests catalogue))]
    (when-not (= 1 (count plans)) (m/fail "Expected one source-time initialization plan" {}))
    (let [plan (first plans)
          functions (ir/load-closure catalogue (into (vec roots) (action-names plan)) lower options)
          functions
          (reduce (fn [functions {:keys [action]}]
                    (if (= "io" (:kind action))
                      (let [name (:name action) target (:target action)
                            callee (get functions target)
                            wrapper ["str" name "_ansatz_io_initializer"]]
                        (when (contains? functions wrapper) (m/fail "IO initializer name collision" {:name name}))
                        (when-not (contains? #{[] ["void"] ["erased"]} (:runtime-param-types (meta callee)))
                          (m/fail "IO initializer must accept only an erased world" {:name name}))
                        (assoc functions wrapper {:params [] :body [:begin-init [::io name] target
                                                                    (mapv (constantly [:imm m/erased]) (:params callee)) "object"]}))
                      functions)) functions (:actions plan))]
      {:plan plan :functions functions}))))

(defn run-local-plan
  "Run one module's local actions in producer order. Imports must be initialized
  separately; this function does not claim a fully initialized Lean environment.
  Module-system phase selection is intentionally rejected until modeled."
  [{:keys [plan functions]} world backend fuel]
  (when (contains? #{:running :paused :suspended :host-call} (:status world))
    (m/fail "Initialization would discard an active continuation" {:status (:status world)}))
  (when (:moduleSystem plan) (m/fail "Module-system initialization phases are not implemented" {}))
  (when-not (= functions (:functions world)) (m/fail "Initialization program mismatch" {}))
  (when-not (contains? #{:reference :mutable :jvm} backend) (m/fail "Unknown initialization backend" {:backend backend}))
  (let [program (when (= backend :jvm) (lazy/open-program functions))]
    (finish (reduce (fn [world {:keys [action]}]
              (let [name (:name action)
                    initial (case (:kind action)
                              "initialize" (start world name)
                              "value" (m/start world name [])
                              "io" (m/start world ["str" name "_ansatz_io_initializer"] []))
                    result (case backend
                             :reference (m/run initial fuel)
                             :mutable (u/freeze (u/run! (u/thaw initial) fuel))
                             :jvm (u/freeze (lazy/run! program (u/thaw initial) fuel)))]
                (when-not (= :done (:status result))
                  (m/fail "Local module initializer did not complete" {:action action :snapshot result}))
                result)) (begin world) (:actions plan)))))
