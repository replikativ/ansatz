(ns prototype.native-call
  "Optional prepared Nat call regions over the existing mutable interpreter.
   No program-specific code generation; ordinary execution handles declines."
  (:refer-clojure :exclude [run!])
  (:require [prototype.mutable :as u]
            [prototype.machine :as m]
            [prototype.code-provenance :as provenance]
            [prototype.native-nat :as native])
  (:import [java.util ArrayDeque IdentityHashMap]))

(def ^:private generation (Object.))
(def ^:private object-array-class (class (object-array 0)))
(def ^:private long-array-class (class (long-array 0)))
(defn- vector-code? [x] (identical? clojure.lang.PersistentVector (class x)))
(defn- ordinary-map? [x]
  (contains? #{clojure.lang.PersistentArrayMap clojure.lang.PersistentHashMap} (class x)))
(defn- index? [x]
  (and (or (instance? Long x) (instance? Integer x)) (<= 0 (long x) 999998)))
(defn- name? [x]
  (loop [x x]
    (cond
      (or (keyword? x) (string? x)) true
      (not (vector-code? x)) false
      (and (= 1 (count x)) (= "anonymous" (nth x 0))) true
      (and (= 3 (count x)) (= "str" (nth x 0)) (string? (nth x 2))) (recur (nth x 1))
      :else false)))
(defn- operand-id? [operand id]
  (and (vector-code? operand) (= 2 (count operand))
       (= :var (nth operand 0)) (index? (nth operand 1)) (= id (nth operand 1))))
(defn- operand? [operand]
  (and (vector-code? operand) (= 2 (count operand))
       (or (= :imm (nth operand 0))
           (and (= :var (nth operand 0)) (index? (nth operand 1))))))
(defn- wrapper? [{:keys [params body runtime-extern]}]
  (and (vector-code? params) (= 2 (count params)) (every? index? params)
       (not= (nth params 0) (nth params 1)) (string? runtime-extern)
       (vector-code? body) (= 4 (count body)) (= :let (nth body 0))
       (index? (nth body 1)) (= (inc (max (nth params 0) (nth params 1))) (nth body 1))
       (let [expression (nth body 2) tail (nth body 3)]
         (and (vector-code? expression) (= 3 (count expression))
              (= :runtime (nth expression 0)) (string? (nth expression 1))
              (= runtime-extern (nth expression 1))
              (let [args (nth expression 2)]
                (and (vector-code? args) (= 2 (count args))
                     (operand-id? (nth args 0) (nth params 0))
                     (operand-id? (nth args 1) (nth params 1))))
              (vector-code? tail) (= 2 (count tail)) (= :return (nth tail 0))
              (operand-id? (nth tail 1) (nth body 1))))))

(defn open-program
  "Prepare canonical immutable source calls only. Plans contain code facts,
   never runtime bodies or guest values. Unknown/custom graphs remain ordinary."
  [functions]
  (let [wrappers (if-not (ordinary-map? functions) {}
                   (into {} (keep (fn [[name function]]
                                    (when (and (name? name) (ordinary-map? function) (wrapper? function))
                                      (when-let [descriptor (native/prepare-op (:runtime-extern function))]
                                        [name {:function function :descriptor descriptor
                                               :width (inc (nth (:body function) 1))}])))) functions))
        bodies (IdentityHashMap.) calls (IdentityHashMap.)]
    (when (ordinary-map? functions)
      (doseq [function (vals functions) :when (ordinary-map? function)]
        (provenance/admit-body! bodies (:body function))))
    (doseq [body (.keySet bodies)]
      (when (and (= :call (nth body 0 nil)) (= 5 (count body))
                 (index? (nth body 1)) (vector-code? (nth body 4)))
        (let [target (nth body 2) args (nth body 3)]
          (when (and (vector-code? target) (= 2 (count target)) (= :direct (nth target 0))
                     (name? (nth target 1)) (vector-code? args) (= 2 (count args))
                     (every? operand? args))
            (when-let [wrapper (get wrappers (nth target 1))]
              (.put calls body wrapper))))))
    {:functions functions :wrappers wrappers :calls calls
     :generation generation :call-token (u/call-step-token)}))

(defn- cache-compatible? [s wrapper]
  (let [cache (:function-slot-cache s)]
    (or (nil? cache)
        (and (identical? IdentityHashMap (class cache))
             (let [cached (.get ^IdentityHashMap cache (:function wrapper))]
               (or (nil? cached)
                   (and (or (instance? Long cached) (instance? Integer cached))
                        (= cached (:width wrapper)))))))))
(defn- machine-storage? [s]
  (and (identical? prototype.mutable.Machine (class s))
       (identical? object-array-class (class (:control s)))
       (>= (alength ^objects (:control s)) 7)
       (identical? long-array-class (class (:counters s)))
       (>= (alength ^longs (:counters s)) 4)
       (identical? ArrayDeque (class (:frames s)))))

(defn run!
  "Run with ordinary fuel and World observations. Eligible calls consume
   call/let/return together when three steps fit; other instructions use step!.
   Five-argument form supplies an internal disable/control flag and optional
   volatile scalar census for bounded profiling, not guest state or authority."
  ([program machine fuel] (run! program machine fuel true nil))
  ([program machine fuel fuse? census]
   (when-not (identical? (:functions program) (:functions machine))
     (m/fail "Fusion program does not match machine code identity" {}))
   (if-not (and (identical? generation (:generation program)) (machine-storage? machine)
                (identical? IdentityHashMap (class (:calls program)))
                (not (.isEmpty ^IdentityHashMap (:calls program)))
                (some? (:call-token program))
                (identical? (:call-token program) (u/call-step-token)))
     (u/run! machine fuel)
     (let [^IdentityHashMap calls (:calls program)
           ^objects control (:control machine)
           ^longs counters (:counters machine)
           dispatch
           (fn ^long [s ^long remaining]
             (let [body (aget control 0)
                   wrapper (when (and fuse? (>= remaining 3)) (.get calls body))]
               (if-not (and wrapper (identical? (:call-token program) (u/call-step-token)))
                 (do (u/step! s) (long 1))
                 (long
                  (u/call-step-with!
                   s
                   (fn [ordinary s target args dest continuation]
                     (let [locals (aget control 1)
                           eligible? (and (identical? (:call-token program) (u/call-step-token))
                                          (identical? ordinary u/call-values!)
                                          (identical? body (aget control 0))
                                          (nil? (:register-layouts s))
                                          (identical? object-array-class (class locals))
                                          (identical? target (nth body 2))
                                          (identical? continuation (nth body 4))
                                          (= dest (nth body 1))
                                          (< (long dest) (alength ^objects locals))
                                          (= 2 (count args))
                                          (<= (aget counters 2) (- Long/MAX_VALUE 2))
                                          (cache-compatible? s wrapper))
                           result (when eligible? (native/try-op (:descriptor wrapper) (nth args 0) (nth args 1)))]
                       (if (and eligible? (not (native/decline? result)))
                         (do
                           (aset-long counters 3 (max (aget counters 3)
                                                      (inc (.size ^ArrayDeque (:frames s)))))
                           (u/add-steps! s 2)
                           (aset ^objects locals (int dest) result)
                           (u/set-body! s continuation)
                           (when census (vswap! census update :fused (fnil inc 0)))
                           3)
                         (do
                           (ordinary s target args dest continuation)
                           (when census (vswap! census update :ordinary (fnil inc 0)))
                           1)))))))))]
       (u/run-prepared! machine fuel calls dispatch)))))
