(ns native-wrapper-fusion
  "Research-only direct binary Nat wrapper call fusion. Single-thread, stock
   helper definitions; no custom callbacks or private host-storage reuse."
  (:refer-clojure :exclude [run!])
  (:require [prototype.mutable :as u]
            [prototype.machine :as m]
            [prototype.code-provenance :as provenance]
            [prototype.slot-count :as slots]
            [prepared-native-ops :as native])
  (:import [java.util ArrayDeque IdentityHashMap]))

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

(defn- current-runtime? []
  (and (some? (slots/program-layout-token))
   (every?
   (fn [[root-name names]]
     (let [roots @(ns-resolve 'prototype.mutable root-name)]
       (and (= (count roots) (count names))
            (every? true? (map (fn [root name]
                                (identical? root @(ns-resolve 'prototype.mutable name))) roots names)))))
   [['scalar-wrapper-roots
     '[runtime-value! runtime-ops node take-entropy! replace-node! step! expr! value
       read-local ctl put! bump! locals-array add-steps! set-body!]]
    ['tail-region-roots
     '[call-values! callee-slots bind-params! registers deliver! push-frame!
       tail-entry-state? tail-peak! materialize-tail-entry! materialize-tail-return!
       has-frames? status steps function-slots tail-frame-depth]]])))

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

(defn prepare [functions]
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
                     (name? (nth target 1)) (vector-code? args) (= 2 (count args)))
            (when-let [wrapper (get wrappers (nth target 1))]
              (.put calls body wrapper))))))
    {:functions functions :wrappers wrappers :calls calls}))

(defn run!
  "Same explicit PC/fuel API. A fused call consumes call/let/return together
   only when all three steps fit. Partial budgets use ordinary instructions.
   FUSE? false is the identical absolute-budget driver control."
  ([program machine fuel] (run! program machine fuel true nil))
  ([program machine fuel fuse? census]
   (when-not (identical? (:functions program) (:functions machine))
     (m/fail "Fusion program does not match machine code identity" {}))
   (let [counters ^longs (:counters machine)
         initial (aget counters 2)
         ctl @(ns-resolve 'prototype.mutable 'ctl)
         put! @(ns-resolve 'prototype.mutable 'put!)
         ordinary u/call-values!]
     (if-not (and (current-runtime?) (instance? Long fuel) (<= 0 initial) (<= 0 (long fuel))
                  (<= (long fuel) (- Long/MAX_VALUE initial)))
       (u/run! machine fuel)
       (let [limit (+ initial (long fuel))
             call! (fn [s target args dest continuation]
                     (let [body (ctl s 0)
                           locals (ctl s 1)
                           wrapper (when (and fuse? (identical? machine s)
                                              (nil? (:register-layouts s))
                                              (.containsKey ^IdentityHashMap (:calls program) body)
                                              (identical? target (nth body 2 nil))
                                              (identical? continuation (nth body 4 nil))
                                              (= dest (nth body 1))
                                              (< -1 (long dest) (alength ^objects locals))
                                              (= 2 (count args))
                                              (<= 2 (- limit (aget counters 2))))
                                     (.get ^IdentityHashMap (:calls program) body))
                           cache (:function-slot-cache s)
                           cached (when (and wrapper (identical? IdentityHashMap (class cache)))
                                    (.get ^IdentityHashMap cache (:function wrapper)))
                           wrapper (when (and wrapper
                                              (or (nil? cache)
                                                  (and (identical? IdentityHashMap (class cache))
                                                       (or (nil? cached)
                                                           (and (or (instance? Long cached) (instance? Integer cached))
                                                                (= cached (:width wrapper))))))) wrapper)
                           result (if wrapper
                                    (native/try-op (:descriptor wrapper) (nth args 0) (nth args 1))
                                    nil)]
                       (if (and wrapper (not (native/decline? result)))
                         (do
                           ;; The stock call instruction already charged one.
                           ;; Reproduce the logical callee frame peak, even
                           ;; though no physical callee frame/registers exist.
                           (aset-long counters 3 (max (aget counters 3)
                                                      (inc (.size ^ArrayDeque (:frames s)))))
                           (aset-long counters 2 (+ 2 (aget counters 2)))
                           (aset ^objects locals (int dest) result)
                           (put! s 0 continuation)
                           (when census (vswap! census update :fused (fnil inc 0))))
                         (do
                           (when census (vswap! census update :ordinary (fnil inc 0)))
                           ;; Arguments were already evaluated once by call!.
                           (ordinary s target args dest continuation)))))]
         (with-redefs [u/call-values! call!]
           (loop []
             (cond
               (not= :running (ctl machine 4)) machine
               (= limit (aget counters 2)) (do (put! machine 4 :paused) machine)
               :else (do (u/step! machine) (recur))))))))))

(defn workload [context driver]
  (let [[mk fold callback] (:names context)
        seed (m/run (m/start (m/world (:functions context)) callback []) 10000)]
    (fn [n]
      (let [machine (u/thaw (m/start seed mk [n]))]
        (driver machine 2000000)
        (assert (= :done (u/status machine)))
        (u/start! machine fold [(:result seed) (aget ^objects (:control machine) 5) 0])
        (driver machine 2000000)
        (u/freeze machine)))))

(defn probe [context sizes]
  (let [measure (resolve 'prototype.unchanged-program-benchmark/measure)
        started (System/nanoTime) program (prepare (:functions context))
        preparation (- (System/nanoTime) started)
        modes [:ordinary :absolute-driver :fusion]
        runners {:ordinary (workload context u/run!)
                 :absolute-driver (workload context #(run! program %1 %2 false nil))
                 :fusion (workload context #(run! program %1 %2 true nil))}]
    (doseq [_ (range 10) mode modes] ((runners mode) 100))
    {:scope "Private raw RBMap build/fold/final freeze; same absolute driver with fusion disabled; full World parity outside timing."
     :preparation-ns preparation :wrappers (count (:wrappers program))
     :sites (.size ^IdentityHashMap (:calls program))
     :runs (vec (for [n sizes
                      :let [expected ((get-in context [:workloads :reference]) n)]
                      trial (range 7)
                      mode (if (even? trial) modes (reverse modes))]
                  (let [[actual metrics] (measure #((runners mode) n))]
                    (assert (= expected actual))
                    (assoc metrics :n n :trial trial :mode mode))))}))
