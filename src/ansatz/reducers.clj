;; Verified reducer/transducer experiments for Clojure-facing pipelines.
;;
;; This namespace intentionally does not modify the core Ansatz compiler.  It
;; gives us a small, explicit reducer calculus that can later be connected to
;; kernel-checked definitions and proofs.

(ns ansatz.reducers
  (:refer-clojure :exclude [cat eduction empty filter group-by into map mapcat reduce remove transduce])
  (:require [clojure.core :as core]
            [clojure.core.reducers :as reducers]))

;; ============================================================
;; Pipeline AST
;; ============================================================

(defrecord Pipeline [steps])

(def empty
  "The identity reducer pipeline."
  (->Pipeline []))

(defn pipeline?
  "True when `x` is an Ansatz reducer pipeline."
  [x]
  (instance? Pipeline x))

(defn- ensure-pipeline [x]
  (cond
    (nil? x) empty
    (pipeline? x) x
    :else (throw (ex-info "Expected ansatz.reducers/Pipeline" {:value x}))))

(defn- append-step [pipeline step]
  (->Pipeline (conj (:steps (ensure-pipeline pipeline)) step)))

(defn map
  "Append a stateless map transform, or create a one-step pipeline."
  ([f] (map empty f))
  ([pipeline f]
   (append-step pipeline {:op :map :f f :fold-safe? true})))

(defn filter
  "Append a stateless filter transform, or create a one-step pipeline."
  ([pred] (filter empty pred))
  ([pipeline pred]
   (append-step pipeline {:op :filter :pred pred :fold-safe? true})))

(defn remove
  "Append a stateless remove transform, or create a one-step pipeline."
  ([pred] (remove empty pred))
  ([pipeline pred]
   (append-step pipeline {:op :remove :pred pred :fold-safe? true})))

(defn cat
  "Append Clojure's `cat` transducer, or create a one-step pipeline."
  ([] (cat empty))
  ([pipeline]
   (append-step pipeline {:op :cat :fold-safe? true})))

(defn mapcat
  "Append a stateless mapcat transform, or create a one-step pipeline."
  ([f] (mapcat empty f))
  ([pipeline f]
   (append-step pipeline {:op :mapcat :f f :fold-safe? true})))

(def flat-map
  "Alias for `mapcat`; closer to lean-reducers naming."
  mapcat)

(defn compose
  "Compose pipelines left-to-right, matching normal threading order."
  [& pipelines]
  (->Pipeline (vec (core/mapcat (comp :steps ensure-pipeline) pipelines))))

(defn fold-safe?
  "Whether a pipeline can be applied inside `reducers/fold` chunks.

   This prototype only exposes stateless transforms, so every built-in step is
   fold-safe. Stateful/early-terminating transforms should set this false until
   their completion and `reduced` semantics are modeled explicitly."
  [pipeline]
  (every? :fold-safe? (:steps (ensure-pipeline pipeline))))

(defn- step->xform [{:keys [op f pred]}]
  (case op
    :map (core/map f)
    :filter (core/filter pred)
    :remove (core/remove pred)
    :cat core/cat
    :mapcat (core/mapcat f)))

(defn xform
  "Compile a pipeline to an ordinary Clojure transducer."
  [pipeline]
  (let [steps (:steps (ensure-pipeline pipeline))]
    (if (seq steps)
      (apply comp (core/map step->xform steps))
      identity)))

(defn explain
  "Return a small data summary of the pipeline."
  [pipeline]
  {:steps (mapv #(select-keys % [:op :fold-safe?]) (:steps (ensure-pipeline pipeline)))
   :fold-safe? (fold-safe? pipeline)})

;; ============================================================
;; Sequential terminals
;; ============================================================

(defn transduce
  "Run a pipeline with Clojure's `transduce`."
  ([pipeline rf coll]
   (core/transduce (xform pipeline) rf coll))
  ([pipeline rf init coll]
   (core/transduce (xform pipeline) rf init coll)))

(defn reduce
  "Run a pipeline with a plain two-arity reducing function."
  [pipeline rf init coll]
  (transduce pipeline (core/completing rf) init coll))

(defn into
  "Collect a pipeline into `to`, using Clojure's transducer-aware `into`."
  [to pipeline coll]
  (core/into to (xform pipeline) coll))

(defn eduction
  "Return a reducible/iterable eduction for a pipeline."
  [pipeline coll]
  (core/eduction (xform pipeline) coll))

;; ============================================================
;; Law-carrying monoids
;; ============================================================

(def required-laws
  #{:assoc :left-identity :right-identity})

(defrecord MonoidSpec [name unit-fn combine laws metadata])

(defn monoid-spec
  "Create a law-carrying monoid descriptor.

   `unit-fn` is a zero-arity function because Clojure reducers call the
   combining function with zero arguments to obtain a fresh identity value.
   `laws` is a map containing at least `:assoc`, `:left-identity`, and
   `:right-identity`.  Today these are carried as certificates/theorem refs;
   the next step is to validate them against Ansatz kernel declarations."
  [{:keys [name unit-fn combine laws metadata]}]
  (when-not (fn? unit-fn)
    (throw (ex-info "MonoidSpec requires :unit-fn" {:name name})))
  (when-not (fn? combine)
    (throw (ex-info "MonoidSpec requires :combine" {:name name})))
  (->MonoidSpec name unit-fn combine (or laws {}) metadata))

(defn lawful?
  "True when a MonoidSpec carries all laws needed by parallel fold."
  [spec]
  (and (instance? MonoidSpec spec)
       (every? #(contains? (:laws spec) %) required-laws)))

(defn- assert-lawful! [spec]
  (when-not (lawful? spec)
    (throw (ex-info "Parallel fold requires a lawful MonoidSpec"
                    {:name (:name spec)
                     :required required-laws
                     :present (set (keys (:laws spec)))})))
  spec)

(defn unit
  "Produce the monoid identity value."
  [spec]
  ((:unit-fn (assert-lawful! spec))))

(defn combine
  "Combine two monoid values."
  [spec left right]
  ((:combine (assert-lawful! spec)) left right))

(defn combinef
  "Compile a MonoidSpec to Clojure reducers' 0/2-arity combine function."
  [spec]
  (let [{:keys [unit-fn combine]} (assert-lawful! spec)]
    (fn
      ([] (unit-fn))
      ([left right] (combine left right)))))

(def nat-add
  "Law certificate for exact non-negative integer addition.

   The law refs name Lean/Ansatz theorem declarations. This prototype carries
   them; it does not yet check that the runtime function is the compiled form of
   the referenced CIC operation."
  (monoid-spec
   {:name :nat/add
    :unit-fn (constantly 0)
    :combine (fn [left right] (+ left right))
    :laws {:assoc 'Nat.add_assoc
           :left-identity 'Nat.zero_add
           :right-identity 'Nat.add_zero}
    :metadata {:ansatz/type 'Nat
               :ansatz/op 'Nat.add}}))

(def int-add
  "Law certificate for exact integer addition."
  (monoid-spec
   {:name :int/add
    :unit-fn (constantly 0)
    :combine (fn [left right] (+ left right))
    :laws {:assoc 'Int.add_assoc
           :left-identity 'Int.zero_add
           :right-identity 'Int.add_zero}
    :metadata {:ansatz/type 'Int
               :ansatz/op 'Int.add}}))

;; ============================================================
;; Parallel terminals
;; ============================================================

(defn- assert-fold-safe! [pipeline]
  (when-not (fold-safe? pipeline)
    (throw (ex-info "Pipeline contains transforms that are not fold-safe"
                    (explain pipeline))))
  pipeline)

(defn fold-map
  "Lawful parallel map-then-fold.

   This is the safe parallel primitive: every element is mapped to a monoid
   value, chunk results are combined with the same monoid, and Clojure's
   `reducers/fold` handles the chunk tree. Arbitrary `step` folds are excluded
   from the safe API because they additionally need a homomorphism law."
  ([pipeline spec f coll]
   (fold-map pipeline spec f coll {}))
  ([pipeline spec f coll {:keys [grain] :or {grain 512}}]
   (let [pipeline (assert-fold-safe! (ensure-pipeline pipeline))
         {:keys [combine]} (assert-lawful! spec)
         xf (xform pipeline)
         reducef (xf (fn [acc x] (combine acc (f x))))]
     (reducers/fold grain (combinef spec) reducef coll))))

(defn unchecked-fold-map
  "Parallel map-then-fold without law checking.

   This mirrors lean-reducers' explicit unchecked path. Use only when the caller
   accepts Clojure reducers' regrouping semantics."
  ([pipeline unit-fn combine f coll]
   (unchecked-fold-map pipeline unit-fn combine f coll {}))
  ([pipeline unit-fn combine f coll {:keys [grain] :or {grain 512}}]
   (let [pipeline (assert-fold-safe! (ensure-pipeline pipeline))
         xf (xform pipeline)
         reducef (xf (fn [acc x] (combine acc (f x))))
         combinef (fn
                    ([] (unit-fn))
                    ([left right] (combine left right)))]
     (reducers/fold grain combinef reducef coll))))

(def ^:private missing-value
  (Object.))

(defn- merge-groups [value-spec left right]
  (let [value-combine (:combine (assert-lawful! value-spec))]
    (core/reduce-kv
     (fn [groups k rv]
       (let [lv (get groups k missing-value)]
         (assoc groups k (if (identical? lv missing-value)
                           rv
                           (value-combine lv rv)))))
     left
     right)))

(defn- group-monoid [value-spec]
  (assert-lawful! value-spec)
  (monoid-spec
   {:name [:group-by (:name value-spec)]
    :unit-fn hash-map
    :combine (partial merge-groups value-spec)
    :laws {:assoc {:derived :pointwise-map-assoc
                   :from (:name value-spec)}
           :left-identity {:derived :empty-map-left-identity
                           :from (:name value-spec)}
           :right-identity {:derived :empty-map-right-identity
                            :from (:name value-spec)}}
    :metadata {:derived-from value-spec}}))

(defn group-by
  "Lawful parallel grouping.

   `value-f` maps each input to a contribution for its key. Values with the same
   key are merged using `value-spec`."
  ([pipeline value-spec key-f value-f coll]
   (group-by pipeline value-spec key-f value-f coll {}))
  ([pipeline value-spec key-f value-f coll opts]
   (fold-map pipeline
             (group-monoid value-spec)
             (fn [x] {(key-f x) (value-f x)})
             coll
             opts)))
