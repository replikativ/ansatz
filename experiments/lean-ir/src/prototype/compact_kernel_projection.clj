(ns prototype.compact-kernel-projection
  "Experimental world-scoped compact memo for the existing checking projection.
   Compile java/prototype/TypedLongMemo.java into an isolated classpath directory.
   No validation or Lean semantics are replaced: specification is borrowed from
   kernel-bridge via a read-only private Var lookup. This explicit experimental
   coupling must be reviewed if the pinned bridge changes. No redefs or globals
   are mutated. Drop the returned function after bulk projection to free its memo."
  (:require [prototype.machine :as m]
            [prototype.kernel-bridge])
  (:import [prototype TypedLongMemo]
           [java.util HashMap ArrayDeque]))

(def ^:private kinds
  (zipmap [:nat :string :name :level :names :levels :literal :expr
           :constant-val :hints :axiom-val :axiom-declaration
           :compiler-marker-constant :compiler-marker-val
           :compiler-marker-declaration :definition-val :declaration]
          (map byte (range 1 18))))

(defn make-projector
  "The same [world kind value] interface as kernel-bridge/make-projector.
   Ref IDs use primitive full-width long keys and a separate kind byte; all
   other keys preserve the original typed-vector HashMap equality semantics.
   Active markers detect cycles and are removed on failure. Successful child
   projections remain reusable, as with the original memo. No world mutation."
  [world]
  (let [specification (deref (ns-resolve 'prototype.kernel-bridge 'specification))
        memo (TypedLongMemo.)
        fallback (HashMap.)
        absent (Object.) active (Object.)
        compact-key? (fn [[kind value]]
                       (and (contains? kinds kind) (m/ref? value) (= 1 (count value))
                            (integer? (:id value)) (<= Long/MIN_VALUE (:id value) Long/MAX_VALUE)))
        get-value (fn [[kind value :as key]]
                    (if (compact-key? key)
                      (.get memo (long (:id value)) (byte (get kinds kind)) absent)
                      (.getOrDefault fallback key absent)))
        put-value! (fn [[kind value :as key] result]
                     (if (compact-key? key)
                       (.put memo (long (:id value)) (byte (get kinds kind)) result)
                       (.put fallback key result)))]
    (fn [current-world kind value]
      (when-not (identical? world current-world)
        (throw (ex-info "Kernel projector belongs to a different world" {})))
      (locking memo
        (let [root [kind value] work (ArrayDeque.)]
          (.push work [:visit root])
          (try
            (loop []
              (if (.isEmpty work)
                {:value (get-value root) :projected-nodes (+ (.size memo) (.size fallback))}
                (let [[op key spec] (.pop work)]
                  (case op
                    :visit
                    (let [cached (get-value key)]
                      (when (identical? cached active)
                        (throw (ex-info "Cyclic guest kernel value" {:kind (first key)})))
                      (when (identical? cached absent)
                        (let [spec (specification world (first key) (second key))]
                          (put-value! key active)
                          (.push work [:build key spec])
                          (doseq [child (reverse (:children spec))]
                            (.push work [:visit child])))))
                    :build
                    (put-value! key ((:build spec) (mapv get-value (:children spec)))))
                  (recur))))
            (catch Throwable failure
              (.removeValue memo active)
              (.removeIf (.values fallback)
                         (reify java.util.function.Predicate
                           (test [_ value] (identical? value active))))
              (throw failure))))))))
