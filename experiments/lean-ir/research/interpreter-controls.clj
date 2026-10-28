(ns interpreter-controls
  "Bounded interpreter controls. Load runtime-feasibility.clj first."
  (:require [prototype.mutable :as u]
            [prototype.machine :as m]))

(defn primitive-fuel-run!
  "Long-only driver control. BigInt and other fuel carriers retain ordinary
   behavior. This changes no opcode implementation or helper/root policy."
  [ordinary]
  (let [ctl (ns-resolve 'prototype.mutable 'ctl)
        put! (ns-resolve 'prototype.mutable 'put!)]
    (fn [machine fuel]
      (if-not (= Long (class fuel)) (ordinary machine fuel)
        (do
          (when (neg? fuel) (m/fail "Invalid step budget" {:fuel fuel}))
          (loop [remaining (long fuel)]
            (cond
              (not= :running (ctl machine 4)) machine
              (zero? remaining) (do (put! machine 4 :paused) machine)
              :else (do (u/step! machine) (recur (unchecked-dec remaining))))))))))

(defn rc-census [run n]
  (let [counts (atom {}) release u/release!
        node (ns-resolve 'prototype.mutable 'node)
        record! (fn [machine value count persistent?]
                  (let [branch
                        (cond
                          (not (m/ref? value)) :scalar
                          (m/native-reference? machine value) :imported
                          :else
                          (let [{:keys [kind rc queued?]} (node machine value)]
                            (cond
                              (and (= :task kind) queued?) :queued-task
                              (zero? rc) :immortal
                              (> rc count) :positive-rc
                              (= rc count) :destroy-root
                              :else :underflow)))]
                    (swap! counts update branch (fnil inc 0))
                    (release machine value count persistent?)))
        result (with-redefs [u/release! (fn
                                        ([machine value count] (record! machine value count false))
                                        ([machine value count persistent?]
                                         (record! machine value count persistent?)))]
                 (run n))]
    {:scope "Root release entries only; recursive worklist children are not separate public release calls. Diagnostic reads/counters excluded from timing."
     :n n :counts @counts :result (:result result) :stats (:stats result)}))

(defn compare-prepared [context program prepared-run sizes]
  (let [ordinary (get-in context [:workloads :mutable-private])
        fast-driver (primitive-fuel-run! u/run!)
        [mk fold callback] (:names context)
        functions (:functions context)
        seed (m/run (m/start (m/world functions) callback []) 10000)
        callback-value (:result seed)
        run (fn [mode n]
              (let [machine (u/thaw (m/start seed mk [n]))
                    run! (fn [machine]
                           (case mode
                             :prepared (prepared-run program machine 2000000)
                             :primitive-driver (fast-driver machine 2000000)
                             :ordinary (u/run! machine 2000000)))]
                (run! machine)
                (assert (= :done (u/status machine)))
                (let [tree (aget ^objects (:control machine) 5)]
                  (u/start! machine fold [callback-value tree 0]))
                (run! machine)
                (u/freeze machine)))]
    (doseq [_ (range 8) mode [:ordinary :primitive-driver :prepared]] (run mode 100))
    {:preparation (select-keys program [:preparation-ns :prepared-lets :visited-bodies])
     :scope "Same mutable machine ABI; two guest entries, private tree/fold, final freeze; no eval per program. Full World parity outside timed intervals."
     :runs
     (vec (for [n sizes
                :let [expected ((get-in context [:workloads :reference]) n)]
                trial (range 7)
                mode (if (even? trial) [:ordinary :primitive-driver :prepared]
                         [:prepared :primitive-driver :ordinary])]
            (let [[actual metrics] (prototype.unchanged-program-benchmark/measure #(run mode n))]
              (assert (= expected actual))
              (assoc metrics :n n :trial trial :mode mode))))}))
