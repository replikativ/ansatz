(ns prepared-runtime
  "Research-only binary runtime-call fusion over prepared-fused's exact-step
  driver. Reuses existing Instruction protocol/classes; no runtime eval."
  (:refer-clojure :exclude [run!])
  (:require [prepared-interpreter :as p]
            [prepared-fused :as fused]
            [prepared-native-ops :as native]
            [prototype.mutable :as u]
            [prototype.machine :as m])
  (:import [java.util IdentityHashMap Map$Entry]))

(def ^:private ctl-var (ns-resolve 'prototype.mutable 'ctl))
(def ^:private put-var (ns-resolve 'prototype.mutable 'put!))
(def ^:private bump-var (ns-resolve 'prototype.mutable 'bump!))
(def ^:private value-var (ns-resolve 'prototype.mutable 'value))
(def ^:private owner-roots @(ns-resolve 'prototype.mutable 'scalar-wrapper-roots))
(def ^:private stock-runtime (nth owner-roots 0))
(def ^:private stock-value (nth owner-roots 7))

(deftype Runtime2SlotConstant
  [destination symbol descriptor
   first-local? first-data first-operand second-local? second-data second-operand
   continuation]
  p/Instruction
  (execute-instruction! [_ s]
    (when-not (= :running (@ctl-var s 4))
      (m/fail "Machine is not running" {:status (@ctl-var s 4)}))
    (@bump-var s 2 1)
    (let [locals (@ctl-var s 1)
          index (int destination)
          ;; Clojure selects runtime-value!'s function before mapv evaluates
          ;; either operand. Never replace a selected custom entry point merely
          ;; because an operand subsequently restores the Var's stock root.
          fallback u/runtime-value!
          first-value-fn @value-var
          a (if (identical? stock-value first-value-fn)
              (if first-local? (u/read-local (@ctl-var s 1) first-data) first-data)
              (first-value-fn s first-operand))
          ;; The first read may redefine private value. Select it again here,
          ;; before ctl/read-local, matching the original mapv callback.
          second-value-fn @value-var
          b (if (identical? stock-value second-value-fn)
              (if second-local? (u/read-local (@ctl-var s 1) second-data) second-data)
              (second-value-fn s second-operand))
          value (if (identical? stock-runtime fallback)
                  (let [result (native/try-op descriptor a b)]
                    (if (native/decline? result)
                      (fallback s symbol [a b])
                      result))
                  (fallback s symbol [a b]))]
      (aset ^objects locals index value)
      (@put-var s 0 continuation))
    s))

(defn- static-vector? [value]
  (identical? (class value) clojure.lang.PersistentVector))

(defn- operand? [value]
  (and (static-vector? value) (contains? #{:var :imm} (first value))))

(defn prepare-program
  "Replace eligible static binary runtime entries. Descriptor preparation is
  once per distinct symbol, including declines; all other entries stay intact.
  Descriptors, nodes and this cache live only in host program preparation."
  [functions]
  (let [started (System/nanoTime)
        program (fused/prepare-program functions)
        ^IdentityHashMap table (:instructions program)
        descriptors (java.util.HashMap.)
        sites (long-array 1)]
    (doseq [^Map$Entry entry (.entrySet table)]
      (let [body (.getKey entry)
            expression (nth body 2)]
        (when (= :runtime (first expression))
          (let [symbol (nth expression 1 nil)
                arguments (nth expression 2 nil)]
            (when (and (string? symbol)
                       (static-vector? arguments) (= 2 (count arguments))
                       (operand? (nth arguments 0)) (operand? (nth arguments 1)))
              (let [descriptor
                    (if (.containsKey descriptors symbol)
                      (.get descriptors symbol)
                      (let [descriptor (native/prepare-op symbol)]
                        (.put descriptors symbol descriptor)
                        descriptor))]
                (when descriptor
                  (let [a (nth arguments 0) b (nth arguments 1)]
                    (.setValue entry
                               (Runtime2SlotConstant.
                                (nth body 1) symbol descriptor
                                (= :var (first a)) (nth a 1 nil) a
                                (= :var (first b)) (nth b 1 nil) b
                                (nth body 3 nil)))
                    (aset-long sites 0 (inc (aget sites 0)))))))))))
    (assoc program :prepared-native-sites (aget sites 0)
                   :native-symbols-considered (.size descriptors)
                   :preparation-ns (- (System/nanoTime) started))))

(defn step! [program machine] (fused/step! program machine))

(defn run!
  ([program machine] (fused/run! program machine))
  ([program machine fuel] (fused/run! program machine fuel)))

(defn open [functions]
  {:program (prepare-program functions) :run! run! :step! step!})
