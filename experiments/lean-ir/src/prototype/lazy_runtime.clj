(ns prototype.lazy-runtime
  "Demand-compiled regions with a shared in-memory code cache and immutable worlds."
  (:refer-clojure :exclude [run!])
  (:require [prototype.block-compile :as b]
            [prototype.machine :as m]
            [prototype.mutable :as u]))

(defn code-cache [] (atom {}))

(defn open-program
  ([functions] (open-program functions {} (code-cache)))
  ([functions options] (open-program functions options (code-cache)))
  ([functions options cache]
   (let [options (merge {:lexical-joins true
                         :direct-linking (boolean (:direct-linking *compiler-options*))} options)]
     (b/runtime-block-key functions [:return [:imm 0]] options)
     {:functions functions :options options :cache cache
      :generation (b/compiler-token) :dispatch (atom {})
      :counts (atom {:compiled 0 :cache-hits 0})})))

(defn summary [program]
  (assoc @(:counts program) :dispatch-blocks (count @(:dispatch program))
         :cached-blocks (count @(:cache program))))

(defn- check! [program machine]
  (when-not (identical? (:generation program) (b/compiler-token))
    (m/fail "Reopen lazy program after compiler reload" {}))
  (when-not (= (:functions program) (:functions machine))
    (m/fail "Compiled program does not match machine code" {})))

(defn- block! [program body]
  (or (get @(:dispatch program) body)
      (let [key (b/runtime-block-key (:functions program) body (:options program))
            cache (:cache program)
            block (locking cache
                    (if-let [block (get @cache key)]
                      (do (swap! (:counts program) update :cache-hits inc) block)
                      (let [block (b/compile-runtime-block (:functions program) body (:options program))]
                        (swap! cache assoc key block)
                        (swap! (:counts program) update :compiled inc)
                        block)))]
        (swap! (:dispatch program) assoc body block)
        block)))

(defn step-region! [program machine]
  (check! program machine)
  (when-not (= :running (u/status machine)) (m/fail "Machine is not running" {:status (u/status machine)}))
  ((:execute! (block! program (u/body-of machine)))
   (assoc machine :leaf-plans nil :register-layouts nil))
  machine)

(defn run!
  ([program machine] (run! program machine 10000000))
  ([program machine fuel]
   (check! program machine)
   (when-not (and (integer? fuel) (not (neg? fuel))) (m/fail "Invalid step budget" {:fuel fuel}))
   (loop [remaining fuel machine (assoc machine :leaf-plans nil :register-layouts nil)]
     (cond
       (not= :running (u/status machine)) machine
       (zero? remaining) (u/pause! machine)
       :else
       (let [block (block! program (u/body-of machine))]
         (if (>= remaining (:max-cost block))
           (let [before (u/steps machine)]
             ((:execute! block) machine)
             (recur (- remaining (- (u/steps machine) before)) machine))
           (u/run! machine remaining)))))))
