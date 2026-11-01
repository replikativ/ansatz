(ns klara-branch-probe
  "Load into the existing small REPL; no Init, Source, or native resources."
  (:require [prototype.branch-lab :as lab]
            [prototype.mutable :as u]
            [prototype.lazy-runtime :as lazy]))

(defn sample [f n]
  (let [^com.sun.management.ThreadMXBean bean
        (java.lang.management.ManagementFactory/getThreadMXBean)
        tid (.threadId (Thread/currentThread))
        _ (when-not (and (.isThreadAllocatedMemorySupported bean)
                         (.isThreadAllocatedMemoryEnabled bean))
            (throw (ex-info "Thread allocation accounting is unavailable" {})))
        before (.getThreadAllocatedBytes bean tid)
        start (System/nanoTime)]
    (dotimes [_ n] (f))
    (let [elapsed (- (System/nanoTime) start)
          allocated (- (.getThreadAllocatedBytes bean tid) before)]
      {:ns-per-trial (/ (double elapsed) n)
       :allocated-bytes-per-trial (/ (double allocated) n)})))

(defn benchmark
  "Tiny-fixture costs, not steady-state Lean throughput. Five samples after
   warming each operation. Allocation includes ledger/control materialization.
   All external callbacks are replaced with no-ops. No retained-heap claim."
  ([] (benchmark 500))
  ([n]
   (let [{:keys [world functions]} (lab/fixture)]
     {:java (System/getProperty "java.version")
      :max-heap-bytes (.maxMemory (Runtime/getRuntime))
      :iterations-per-sample n :samples 5
      :backends
      (into (sorted-map)
            (for [backend [:persistent :mutable :compiled]
                  :let [run (lab/runner backend functions)
                        complete (fn [x] (run (run world x) 0))
                        operations
                        {:two-resumes (fn [] (complete 10) (complete 20))
                         :provision-and-fork
                         (fn [] (let [s (lab/session world {})]
                                  (lab/fork! s (:initial s))))
                         :fork-two-resumes-adopt
                         (fn []
                           (let [s (lab/session world {})
                                 [a b] (lab/fork! s (:initial s))
                                 a (lab/advance! s a run 10)]
                             (lab/advance! s b run 20)
                             (lab/adopt! s a (fn [_] :ack))))}]]
              [backend
               (into (sorted-map)
                     (for [[name f] operations]
                       (do (dotimes [_ n] (f))
                           [name (vec (repeatedly 5 #(sample f n)))])))]))})))

(defn fork-scaling []
  (let [{:keys [world]} (lab/fixture)]
    (into (sorted-map)
          (for [extra-nodes [0 1000 10000]
                :let [world (reduce (fn [w _] (first (prototype.machine/allocate w :ctor 0 [0])))
                                    world (range extra-nodes))
                      f (fn [] (let [s (lab/session world {})]
                                 (lab/fork! s (:initial s))))]]
            (do (dotimes [_ 500] (f))
                [extra-nodes (vec (repeatedly 5 #(sample f 500)))])))))

(defn klara-basis-check
  "Optional live integration with a supplied Klara world.clj. Reads its source;
   changes only newly created in-memory worlds. Checks basis preservation,
   NOT calling Klara definitions from Lean or executing Klara in the Lean VM."
  [world-source]
  (load-file world-source)
  (let [api #(ns-resolve 'klara.world %)
        make-world (api 'make-world) publish! (api 'publish!)
        put-entry (api 'put-entry) snapshot (api 'snapshot)
        fiber (api 'fiber) fork (api 'fork) basis (api 'basis)
        entry (fn [n] {:kind :def :value n :code-id (str n)
                       :value-id (str n) :reads #{}})
        parent (make-world)
        _ (publish! parent #(put-entry % 'counter (entry 1)))
        pinned (fiber parent) child (fork parent)
        {:keys [world functions]} (lab/fixture)
        s (lab/session world (basis pinned))
        [a b] (lab/fork! s (:initial s))
        _ (publish! parent #(put-entry % 'counter (entry 2)))
        run (lab/runner :compiled functions)
        a (lab/advance! s a run 10) b (lab/advance! s b run 20)
        value #(get-in % [:defs 'counter :value])
        packets (mapv #(lab/snapshot s %) [a b])
        result {:parent (value (snapshot parent)) :klara-child (value (snapshot child))
                :pinned-fiber (value (basis pinned))
                :lean-branch-bases (mapv #(value (:basis %)) packets)
                :lean-results (mapv #(get-in % [:world :result]) packets)}]
    (assert (= {:parent 2 :klara-child 1 :pinned-fiber 1
                :lean-branch-bases [1 1] :lean-results [10 20]} result))
    result))

(defn sample-inputs
  "All mutable inputs are prepared before accounting. Each is used once;
   repeated freezing of one warmed machine would measure a different operation."
  [prepare operation n]
  (let [inputs (mapv (fn [_] (prepare)) (range n))
        index (volatile! -1)]
    (sample #(operation (nth inputs (vswap! index inc))) n)))

(defn boundary-attribution
  ([] (boundary-attribution 200))
  ([n]
   (let [{:keys [world functions]} (lab/fixture)]
     {:iterations-per-sample n :samples 5 :input-preparation :excluded
      :backends
      (into (sorted-map)
            (for [backend [:mutable :compiled]
                  :let [program (when (= backend :compiled) (lazy/open-program functions))
                        run! (if program #(lazy/run! program % 10000) #(u/run! % 10000))
                        to-host (fn [] (run! (u/resume! (u/thaw world) 10)))
                        host-world (u/freeze (to-host))
                        to-done (fn [] (run! (u/resume! (u/thaw host-world) 0)))
                        phases
                        {:first-thaw [(constantly world) u/thaw]
                         :resume-to-host [#(u/thaw world) #(run! (u/resume! % 10))]
                         :first-freeze [to-host u/freeze]
                         :second-thaw [(constantly host-world) u/thaw]
                         :resume-to-done [#(u/thaw host-world) #(run! (u/resume! % 0))]
                         :second-freeze [to-done u/freeze]}]]
              [backend
               (into (sorted-map)
                     (for [[phase [prepare operation]] phases]
                       (do (dotimes [_ n] (operation (prepare)))
                           [phase (vec (repeatedly 5 #(sample-inputs prepare operation n)))])))]))})))

(defn scoped-comparison
  "Matched fork-two-resumes-adopt trials. Fixture must already be at an
   admitted suspension; all code preparation is outside sampled operations."
  ([fixture] (scoped-comparison fixture 500))
  ([{:keys [world functions store]} n]
   {:iterations-per-sample n :samples 5
    :backends
    (into (sorted-map)
          (for [backend [:persistent :mutable :compiled]]
            [backend
             (into (sorted-map)
                   (for [scoped? [false true]
                         :let [run ((if scoped? lab/scoped-runner lab/runner) backend functions)
                               advance! (if scoped? lab/advance-scoped! lab/advance!)
                               f (fn []
                                   (let [s (lab/session world {} store)
                                         [a b] (lab/fork! s (:initial s))
                                         a (advance! s a run 10)]
                                     (advance! s b run 20)
                                     (lab/adopt! s a (fn [_] :ack))))]]
                     (do (dotimes [_ n] (f))
                         [(if scoped? :scoped :materialized)
                          (vec (repeatedly 5 #(sample f n)))])))]))}))
