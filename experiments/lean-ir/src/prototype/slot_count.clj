(ns prototype.slot-count
  "Program register sizing with a bounded weak identity cache. Code is immutable;
   live snapshot bindings are sized separately and never cached with the program."
  (:require [prototype.walk :as walk])
  (:import [java.lang.ref WeakReference ReferenceQueue]
           [java.util Map Collection HashMap ArrayList]
           [clojure.lang IPersistentCollection IPersistentMap]))

(defn cache
  "One weak program identity and its scalar slot count. Replacing an entry
   retains neither its old program nor any code reachable only from that program."
  [] (atom nil))

(defonce ^:private program-cache (cache))

(defn- mutable-collection? [value]
  (or (and value (.isArray (class value)))
      ;; ArraySeq implements persistent collection interfaces while borrowing
      ;; a mutable array. Normalized code uses vectors, never borrowed seqs.
      (and (instance? clojure.lang.ISeq value)
           (not (instance? clojure.lang.IPersistentList value)))
      (and (or (instance? Map value) (instance? Collection value))
           (not (instance? IPersistentCollection value)))))

(defonce ^:private function-cache
  ;; Keys are identity hash integers; values hold only weak functions and sizes.
  ;; The queue removes dead entries even when their bucket is never queried again.
  {:buckets (HashMap.) :queue (ReferenceQueue.)})

(defn- measure-function [function]
  (when-not (and (vector? (:params function)) (vector? (:body function)))
    (throw (ex-info "Register sizing requires immutable parameter and body vectors" {})))
  (let [parameter-max (reduce max 0 (filter integer? (:params function)))]
    (inc
     (reduce
      (fn [n form]
        (when (mutable-collection? form)
          (throw (ex-info "Register sizing rejects mutable program collections" {})))
        (if (vector? form)
          (let [ids (case (first form)
                      (:var :let :call :suspend) [(second form)]
                      :host [(nth form 3)]
                      :join (nth form 2)
                      [])]
            (reduce max n (filter integer? ids))) n))
      parameter-max (walk/forms function)))))

(defn- cached-function-slots [function]
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
            found (some (fn [[^WeakReference reference slots]]
                          (when (identical? function (.get reference)) slots)) bucket)]
        (or found
            (let [slots (measure-function function)
                  ;; The callback captures the scalar identity hash, never function.
                  reference (proxy [WeakReference] [function queue] (hashCode [] key))]
              (.add bucket [reference slots])
              (.put buckets key bucket)
              slots))))))


(defn function-slots
  "Maximum register ID plus one for one immutable function. Cache reuse is by
   function identity only; entries retain weak functions and scalar widths."
  [function]
  (when-not (instance? IPersistentMap function)
    (throw (ex-info "Register sizing requires immutable function definitions" {})))
  (cached-function-slots function))

(defn- measure
  ([functions] (measure functions false))
  ([functions reuse-functions?]
   (when-not (instance? IPersistentMap functions)
     (throw (ex-info "Register sizing requires an immutable function map" {})))
   (reduce
    (fn [slots [_ function]]
      (when-not (instance? IPersistentMap function)
        (throw (ex-info "Register sizing requires immutable function definitions" {})))
      (max slots (if reuse-functions? (cached-function-slots function) (measure-function function))))
    1 functions)))

(defn program-slots
  "Count registers in immutable FUNCTIONS. Cache hits compare identity only;
   equal independently constructed programs are measured independently."
  ([functions] (program-slots functions program-cache))
  ([functions cache]
   (locking cache
     (let [{:keys [program slots]} @cache]
       (if (and program (identical? functions (.get ^WeakReference program))) slots
         (let [slots (measure functions (identical? cache program-cache))]
           (reset! cache {:program (WeakReference. functions) :slots slots})
           slots))))))

(defn local-slots
  "Live bindings can introduce registers absent from the immutable program."
  [locals]
  (inc (reduce max 0 (filter integer? (keys locals)))))
