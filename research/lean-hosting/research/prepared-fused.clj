(ns prepared-fused
  "Research follow-up: two fused :let shapes using the already-loaded
  prepared-interpreter Instruction protocol. Never reload its protocols/types."
  (:refer-clojure :exclude [run!])
  (:require [prepared-interpreter :as p]
            [prototype.mutable :as u]
            [prototype.machine :as m])
  (:import [java.util IdentityHashMap Map$Entry]))

(def ^:private ctl-var (ns-resolve 'prototype.mutable 'ctl))
(def ^:private put-var (ns-resolve 'prototype.mutable 'put!))
(def ^:private bump-var (ns-resolve 'prototype.mutable 'bump!))
(def ^:private expr-var (ns-resolve 'prototype.mutable 'expr!))
(def ^:private value-var (ns-resolve 'prototype.mutable 'value))
(def ^:private node-var (ns-resolve 'prototype.mutable 'node))
(def ^:private field-var (ns-resolve 'prototype.mutable 'field-at))
(def ^:private owner-roots @(ns-resolve 'prototype.mutable 'scalar-wrapper-roots))
(def ^:private stock-step (nth owner-roots 5))
(def ^:private stock-expr (nth owner-roots 6))
(def ^:private stock-value (nth owner-roots 7))
(def ^:private stock-ctl (nth owner-roots 9))
(def ^:private stock-bump (nth owner-roots 11))
(def ^:private object-array-class (class (object-array 0)))

(deftype FusedLiteral [destination value continuation]
  p/Instruction
  (execute-instruction! [_ s]
    (when-not (= :running (@ctl-var s 4))
      (m/fail "Machine is not running" {:status (@ctl-var s 4)}))
    (@bump-var s 2 1)
    (let [locals (@ctl-var s 1)
          index (int destination)]
      (aset ^objects locals index value)
      (@put-var s 0 continuation))
    s))

(deftype FusedProjectSlot [destination operand-slot field-slot continuation]
  p/Instruction
  (execute-instruction! [_ s]
    (when-not (= :running (@ctl-var s 4))
      (m/fail "Machine is not running" {:status (@ctl-var s 4)}))
    (@bump-var s 2 1)
    (let [locals (@ctl-var s 1)
          index (int destination)
          ;; Resolve field then node helpers before the operand read can run
          ;; a host hook. The local helper itself selects its root before ctl.
          value (@field-var
                 (:fields (@node-var s (u/read-local (@ctl-var s 1) operand-slot)))
                 field-slot)]
      (aset ^objects locals index value)
      ;; Select put after expression/store, matching ordinary u/step!.
      (@put-var s 0 continuation))
    s))

(defn- static-vector? [value]
  (identical? (class value) clojure.lang.PersistentVector))

(defn prepare-program
  "Reuse old immutable static-body preparation, replacing only literal and
  project-from-local entries with fused instructions before exposing the table.
  Other supported entries retain their original implementation."
  [functions]
  (let [started (System/nanoTime)
        program (p/prepare-program functions)
        ^IdentityHashMap table (:instructions program)
        counts (long-array 2)]
    (doseq [^Map$Entry entry (.entrySet table)]
      (let [body (.getKey entry)
            destination (nth body 1)
            expression (nth body 2)
            continuation (nth body 3 nil)]
        (case (first expression)
          :literal (do (.setValue entry (FusedLiteral. destination (nth expression 1 nil) continuation))
                       (aset-long counts 0 (inc (aget counts 0))))
          :project (let [operand (nth expression 1 nil)]
                     (when (and (static-vector? operand) (= :var (first operand)))
                       (.setValue entry (FusedProjectSlot. destination (nth operand 1 nil)
                                                          (nth expression 2 nil) continuation))
                       (aset-long counts 1 (inc (aget counts 1)))))
          nil)))
    (assoc program :fused-literals (aget counts 0) :fused-projects (aget counts 1)
                   :preparation-ns (- (System/nanoTime) started))))

(defn- check-program! [program machine]
  (when-not (identical? (:functions program) (:functions machine))
    (m/fail "Prepared program does not match machine code identity" {})))

(defn- unchecked-step!
  "Identity was checked at the public boundary. Guard stock ctl before the
  extra PC lookup; defer the other guards until a prepared instruction exists."
  [program machine]
  (if (and (identical? stock-step @#'u/step!)
           (identical? stock-ctl @ctl-var))
    (if-let [instruction (.get ^IdentityHashMap (:instructions program) (@ctl-var machine 0))]
      (if (and (identical? stock-expr @expr-var)
               (identical? stock-value @value-var)
               (identical? stock-bump @bump-var))
        (p/execute-instruction! instruction machine)
        (u/step! machine))
      (u/step! machine))
    (u/step! machine)))

(defn step! [program machine]
  (check-program! program machine)
  (unchecked-step! program machine))

(defn run!
  ([program machine] (run! program machine 10000000))
  ([program machine fuel]
   (check-program! program machine)
   (let [control (:control machine)]
     (if (and (instance? Long fuel)
              (instance? prototype.mutable.Machine machine)
              (identical? object-array-class (class control))
              (>= (alength ^objects control) 7))
       (do
         (when (neg? (long fuel))
           (m/fail "Invalid step budget" {:fuel fuel}))
         ;; Machine.functions is an immutable record field. The program check
         ;; is sufficient once here; the loop never replaces its machine.
         (loop [remaining (long fuel)]
           (cond
             (not= :running (@ctl-var machine 4)) machine
             (zero? remaining) (do (@put-var machine 4 :paused) machine)
             :else (do (unchecked-step! program machine)
                       (recur (unchecked-dec remaining))))))
       (p/run! program machine fuel)))))

(defn open [functions]
  {:program (prepare-program functions) :run! run! :step! step!})
