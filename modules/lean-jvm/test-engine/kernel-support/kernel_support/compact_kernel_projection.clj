(ns kernel-support.compact-kernel-projection
  "Experimental world-scoped compact memo for the existing checking projection.
   Compile java/prototype/TypedLongMemo.java into an isolated classpath directory.
   No validation or Lean semantics are replaced: specification is borrowed from
   kernel-bridge's explicit default-world decomposition reader. Alternate memo
   storage does not replace semantic checks. No private Var lookup, redefs or
   global mutation is used. Drop the returned projector/context after bulk projection to
   free its memo. Complete-constant scopes can retire temporary lists/maps early."
  (:require [kernel-support.carrier :as m]
            [kernel-support.kernel-bridge :as bridge]
            [kernel-support.imported-kernel :as kernel])
  (:import [prototype TypedLongMemo]
           [java.util HashMap ArrayDeque]))

(def ^:private kinds
  (zipmap [:nat :string :name :level :names :levels :literal :expr
           :constant-val :hints :axiom-val :axiom-declaration
           :compiler-marker-constant :compiler-marker-val
           :compiler-marker-declaration :definition-val :declaration]
          (map byte (range 1 18))))

(defn- scratch-tables [] [(TypedLongMemo.) (HashMap.)])

(defn- projection-context
  [world scratch-kinds]
  (let [specification (bridge/default-world-specification-reader world)
        memo (TypedLongMemo.)
        fallback (HashMap.)
        scratch (volatile! nil)
        busy? (volatile! false)
        absent (Object.) active (Object.)
        compact-key? (fn [[kind value]]
                       (and (contains? kinds kind) (m/ref? value) (= 1 (count value))
                            (integer? (:id value)) (<= Long/MIN_VALUE (:id value) Long/MAX_VALUE)))
        ensure-scratch! (fn []
                          ;; Accessed only under memo lock. Retirement allocates
                          ;; nothing; a later scratch lookup recreates its tables.
                          (or @scratch (let [tables (scratch-tables)]
                                         (vreset! scratch tables) tables)))
        table (fn [kind] (if (contains? scratch-kinds kind) (first (ensure-scratch!)) memo))
        fallback-table (fn [kind] (if (contains? scratch-kinds kind) (second (ensure-scratch!)) fallback))
        get-value (fn [[kind value :as key]]
                    (if (compact-key? key)
                      (.get ^TypedLongMemo (table kind) (long (:id value)) (byte (get kinds kind)) absent)
                      (.getOrDefault ^HashMap (fallback-table kind) key absent)))
        put-value! (fn [[kind value :as key] result]
                     (if (compact-key? key)
                       (.put ^TypedLongMemo (table kind) (long (:id value)) (byte (get kinds kind)) result)
                       (.put ^HashMap (fallback-table kind) key result)))]
    {:project
     (fn [current-world kind value]
      (when-not (identical? world current-world)
        (throw (ex-info "Kernel projector belongs to a different world" {})))
      (locking memo
        (when @busy? (throw (ex-info "Reentrant projection is unsupported" {})))
        (vreset! busy? true)
        (let [root [kind value] work (ArrayDeque.)]
          (.push work [:visit root])
          (try
            (loop []
              (if (.isEmpty work)
                {:value (get-value root) :projected-nodes (+ (.size memo) (.size fallback)
                                    (if-let [[^TypedLongMemo t ^HashMap f] @scratch]
                                      (+ (.size t) (.size f)) 0))}
                (let [[op key spec] (.pop work)]
                  (case op
                    :visit
                    (let [cached (get-value key)]
                      (when (identical? cached active)
                        (throw (ex-info "Cyclic guest kernel value" {:kind (first key)})))
                      (when (identical? cached absent)
                        (let [spec (specification (first key) (second key))]
                          (put-value! key active)
                          (.push work [:build key spec])
                          (doseq [child (reverse (:children spec))]
                            (.push work [:visit child])))))
                    :build
                    (put-value! key ((:build spec) (mapv get-value (:children spec)))))
                  (recur))))
            (catch Throwable failure
              ;; Preserve successful children, remove only unfinished markers.
              ;; This exceptional cleanup is not scratch retirement.
              ;; Cleanup can itself fail under resource exhaustion. Never mask
              ;; the original failure; no reuse is promised after failed cleanup.
              (try
                (doseq [^TypedLongMemo t (cond-> [memo] @scratch (conj (first @scratch)))]
                  (.removeValue t active))
                (doseq [^HashMap t (cond-> [fallback] @scratch (conj (second @scratch)))]
                  (.removeIf (.values t)
                             (reify java.util.function.Predicate
                               (test [_ value] (identical? value active)))))
                (catch Throwable _ nil))
              (throw failure))
            (finally (vreset! busy? false))))))
     :assert-idle
     (fn []
       (locking memo
         (when @busy? (throw (ex-info "Reentrant projection is unsupported" {})))))
     :release-scratch
     (fn []
       (locking memo
         (when @busy? (throw (ex-info "Cannot release scratch during projection" {})))
         ;; Completed CI constructors have copied these lists/maps into their
         ;; final fields. Replace only scratch tables, never scan the core memo.
         (vreset! scratch nil)))}))

(defn make-projector
  "Original bulk [world kind value] interface and cumulative memo semantics.
   Ref IDs use primitive full-width long keys and a separate kind byte; fallback
   keys retain typed-vector equality. Active markers are removed on failure."
  [world]
  (:project (projection-context world #{})))

(defn make-scoped-projector
  "Project complete ConstantInfos with one-CI scratch list/map lifetime.
   Returns :project [world kind value] for inspection and :project-constant
   [world guest-ci] for bulk checking. Only the complete-CI operation releases
   :constant-val/:names/:levels scratch, on both success and failure. Core
   :expr/:name/:level and other kinds retain cross-constant DAG sharing.
   Scratch release is private and cannot interleave component projections.
   :projected-nodes reports current table entries, not historical work."
  [world]
  (let [{:keys [project release-scratch assert-idle]}
        (projection-context world #{:constant-val :names :levels})
        operation-lock (Object.)
        constant-active? (volatile! false)]
    {:project (fn [current-world kind value]
                (locking operation-lock (project current-world kind value)))
     :project-constant
     (fn [current-world value]
       ;; Reject before reading even the envelope or retiring valid inspection
       ;; scratch. Equality of two world maps is not projection authority.
       (when-not (identical? world current-world)
         (throw (ex-info "Kernel projector belongs to a different world" {})))
       (locking operation-lock
         (when @constant-active?
           (throw (ex-info "Reentrant constant projection is unsupported" {})))
         (assert-idle)
         (vreset! constant-active? true)
         (try
           (kernel/project-constant current-world value project)
           (finally
             (release-scratch)
             (vreset! constant-active? false)))))}))
