(ns prototype.slot-count
  "Register sizing with weak identity caches. The bounded global program cache
   also accepts widths derived by constructing an append-only program itself.
   These are storage hints, never executable or kernel authority. Live bindings
   are sized separately; no width travels in a snapshot's metadata."
  (:require [prototype.walk :as walk])
  (:import [java.lang.ref WeakReference ReferenceQueue]
           [java.util Map Collection HashMap ArrayList]
           [clojure.lang IPersistentCollection IPersistentMap PersistentHashMap PersistentArrayMap]))

(defn cache
  "One weak program identity and its scalar slot count. This explicit two-arity
   cache keeps its original contract; global program proofs use a separate cache."
  [] (atom nil))

(def ^:private program-cache-limit 16)
(defonce ^:private program-cache (atom []))
(defn- standard-map? [value]
  (or (= PersistentHashMap (class value)) (= PersistentArrayMap (class value))))
(def ^:private standard-collection-classes
  ;; MapEntry nodes are yielded while walking ordinary persistent maps. Custom
  ;; persistent collections can still be sized, but must not get reusable proofs.
  #{clojure.lang.PersistentHashMap clojure.lang.PersistentArrayMap
    clojure.lang.PersistentVector
    clojure.lang.PersistentList clojure.lang.PersistentList$EmptyList
    clojure.lang.PersistentHashSet clojure.lang.MapEntry})
(defn- mutable-collection? [value]
  (or (and value (.isArray (class value)))
      ;; ArraySeq borrows a mutable array despite persistent collection interfaces.
      (and (instance? clojure.lang.ISeq value)
           (not (instance? clojure.lang.IPersistentList value)))
      (and (or (instance? Map value) (instance? Collection value))
           (not (instance? IPersistentCollection value)))))

(defonce ^:private function-cache
  ;; Weak functions and scalar proofs only. No proof captures the function graph.
  {:buckets (HashMap.) :queue (ReferenceQueue.)})

(defn- measure-function [function]
  (when-not (and (vector? (:params function)) (vector? (:body function)))
    (throw (ex-info "Register sizing requires immutable parameter and body vectors" {})))
  (let [parameter-max (reduce max 0 (filter integer? (:params function)))
        reusable? (volatile! (standard-map? function))
        maximum (reduce
                  (fn [n form]
                    (when (mutable-collection? form)
                      (throw (ex-info "Register sizing rejects mutable program collections" {})))
                    (when (and (instance? IPersistentCollection form)
                               (not (contains? standard-collection-classes (class form))))
                      (vreset! reusable? false))
                    (if (vector? form)
                      (let [ids (case (first form)
                                  (:var :let :call :suspend) [(second form)]
                                  :host [(nth form 3)]
                                  :join (nth form 2)
                                  [])]
                        (reduce max n (filter integer? ids))) n))
                  parameter-max (walk/forms function))]
    {:slots (inc maximum) :reusable? @reusable?}))

(defn- cached-function-proof [function]
  (when-not (instance? IPersistentMap function)
    (throw (ex-info "Register sizing requires immutable function definitions" {})))
  (locking function-cache
    (let [^HashMap buckets (:buckets function-cache)
          ^ReferenceQueue queue (:queue function-cache)]
      (loop []
        (when-let [dead (.poll queue)]
          (let [key (.hashCode dead) ^ArrayList bucket (.get buckets key)]
            (when bucket
              (loop [i (dec (.size bucket))]
                (when (<= 0 i)
                  (when (identical? dead (first (.get bucket i))) (.remove bucket (int i)))
                  (recur (dec i))))
              (when (.isEmpty bucket) (.remove buckets key))))
          (recur)))
      (let [key (System/identityHashCode function)
            ^ArrayList bucket (or (.get buckets key) (ArrayList.))
            found (some (fn [[^WeakReference reference proof]]
                          (when (identical? function (.get reference)) proof)) bucket)]
        (or found
            (let [proof (measure-function function)]
              (when (:reusable? proof)
                ;; Proxy callback captures only a scalar identity hash.
                (let [reference (proxy [WeakReference] [function queue] (hashCode [] key))]
                  (.add bucket [reference proof])
                  (.put buckets key bucket)))
              proof))))))

(defn function-slots
  "Maximum register ID plus one for one immutable function. Deep custom
   collection graphs are measured exactly and never cached by identity."
  [function]
  (:slots (cached-function-proof function)))

(defn- measure-program [functions reuse-functions?]
  (when-not (instance? IPersistentMap functions)
    (throw (ex-info "Register sizing requires an immutable function map" {})))
  (let [reusable? (volatile! (standard-map? functions))
        slots (reduce
                (fn [slots [_ function]]
                  (when-not (instance? IPersistentMap function)
                    (throw (ex-info "Register sizing requires immutable function definitions" {})))
                  (let [proof (if reuse-functions? (cached-function-proof function) (measure-function function))]
                    (when-not (:reusable? proof) (vreset! reusable? false))
                    (max slots (:slots proof))))
                1 functions)]
    {:slots slots :reusable? @reusable?}))

(defn- remembered-width [functions]
  ;; Caller holds program-cache monitor. At most16 weak referents, no structural
  ;; hash/equality, identity-hash collision buckets or unbounded eviction history.
  (let [live (filterv #(some? (.get ^WeakReference (:program %))) @program-cache)
        found (some #(when (identical? functions (.get ^WeakReference (:program %))) %) live)]
    (reset! program-cache (if found (into [found] (remove #(identical? found %) live)) live))
    (:slots found)))
(defn- remember-program! [functions slots]
  ;; Caller holds monitor; the stored values retain no strong program/delta/base.
  (let [entry {:program (WeakReference. functions) :slots slots}]
    (reset! program-cache
            (into [entry] (take (dec program-cache-limit)
                               (remove #(let [p (.get ^WeakReference (:program %))]
                                          (or (nil? p) (identical? p functions))) @program-cache))))))

(defn program-slots
  "Exact register width. Global cache retains up to16 weak program identities;
   independently equal programs never inherit a proof. Explicit CACHE preserves
   the original one-entry weak atom contract and full function validation."
  ([functions]
   (locking program-cache
     (or (remembered-width functions)
         (let [{:keys [slots reusable?]} (measure-program functions true)]
           (when reusable? (remember-program! functions slots))
           slots))))
  ([functions cache]
   (locking cache
     (let [{:keys [program slots]} @cache]
       (if (and program (identical? functions (.get ^WeakReference program))) slots
         (let [slots (:slots (measure-program functions false))]
           (reset! cache {:program (WeakReference. functions) :slots slots})
           slots))))))

(defn append-functions
  "Construct BASE plus ADDITIONS with ordinary merge semantics. Only standard
   immutable maps, disjoint new names, an actual cached exact base width, and
   fully validated final function graphs permit incremental width propagation.
   Every final addition is sized/validated eagerly, regardless of cache state;
   malformed trusted lowerer output therefore fails here even for a cold base.
   Missing base proofs/custom code/replacements require normal exact program
   sizing on use. No supplied target map, width, metadata or authority is accepted."
  [base additions]
  (when-not (and (instance? IPersistentMap base) (instance? IPersistentMap additions))
    (throw (ex-info "Register sizing requires immutable function maps" {})))
  (let [{:keys [slots reusable?]} (measure-program additions true)
        functions (merge base additions)]
    (when (and reusable? (standard-map? base) (standard-map? additions)
               (not-any? #(contains? base %) (keys additions)))
      (locking program-cache
        (when-let [base-width (remembered-width base)]
          (remember-program! functions (max base-width slots)))))
    functions))

(defn local-slots
  "Live bindings can introduce registers absent from the immutable program."
  [locals]
  (inc (reduce max 0 (filter integer? (keys locals)))))

;; Owner baseline for optional scalar regions bypassing repeated call layout work.
(def ^:private tail-layout-generation (Object.))
(def ^:private tail-layout-roots [function-slots program-slots local-slots cached-function-proof measure-function standard-map? mutable-collection? standard-collection-classes])
(defn tail-layout-token [] [tail-layout-generation (walk/tail-walk-token)])
(defn builtin-tail-layout? []
  (let [[f p l c measure standard mutable classes] tail-layout-roots]
    (and (walk/builtin-tail-walk?) (identical? f function-slots) (identical? p program-slots) (identical? l local-slots)
         (identical? c cached-function-proof) (identical? measure measure-function) (identical? standard standard-map?)
         (identical? mutable mutable-collection?) (identical? classes standard-collection-classes))))
