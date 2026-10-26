(ns prototype.unchanged-program-benchmark
  "Resident REPL only. Native-exported original code, not hosted source loading."
  (:require [prototype.import-ir :as ir]
            [prototype.runtime-abi :as abi]
            [prototype.machine :as m]
            [prototype.mutable :as u]
            [prototype.lazy-runtime :as lazy]))

(defn target [catalogue label]
  (or (first (filter #(= label (ir/name-label %)) (keys (:declarations catalogue))))
      (throw (ex-info "Missing original declaration" {:label label}))))

(defn measure [f]
  (let [bean ^com.sun.management.ThreadMXBean (java.lang.management.ManagementFactory/getThreadMXBean)
        tid (.getId (Thread/currentThread))
        _ (when-not (and (.isCurrentThreadCpuTimeSupported bean) (.isThreadCpuTimeEnabled bean)
                         (.isThreadAllocatedMemorySupported bean) (.isThreadAllocatedMemoryEnabled bean))
            (throw (ex-info "Thread CPU/allocation metrics unavailable" {})))
        gc #(reduce + (map (fn [^java.lang.management.GarbageCollectorMXBean b] (max 0 (.getCollectionCount b)))
                           (java.lang.management.ManagementFactory/getGarbageCollectorMXBeans)))
        collections (gc) bytes (.getThreadAllocatedBytes bean tid)
        cpu (.getCurrentThreadCpuTime bean) wall (System/nanoTime) result (f)
        wall-end (System/nanoTime) cpu-end (.getCurrentThreadCpuTime bean)
        bytes-end (.getThreadAllocatedBytes bean tid)]
    [result {:cpu-ns (- cpu-end cpu)
             :wall-ns (- wall-end wall)
             :allocated-bytes (- bytes-end bytes)
             :gc-collections (- (gc) collections)}]))

(defn setup [path roots]
  (let [catalogue (ir/index-bundles [path])
        names (mapv #(target catalogue %) roots)
        fs (ir/load-closure catalogue names abi/lower)
        [program preparation] (measure #(lazy/open-program fs))]
    {:catalogue catalogue :names names :functions fs :program program :preparation preparation
     :runners {:reference #(m/run %1 %2)
               :mutable #(u/freeze (u/run! (u/thaw %1) %2))
               :jvm #(u/freeze (lazy/run! program (u/thaw %1) %2))}}))

(defn describe [world]
  {:status (:status world) :stats (:stats world)
   :heap-nodes (count (:heap world)) :next-id (:next-id world)
   :tree-at-fold-start (:tree-at-fold-start (meta world))})

(defn rbmap [path sizes trials]
  (let [{:keys [names functions program runners preparation]} (setup path ["mkMap" "fold._redArg" "main._closed_0"])
        [mk fold callback] names
        callback-world (m/run (m/start (m/world functions) callback []) 10000)
        callback-value (:result callback-world)
        initial #(m/start callback-world mk [%])
        run (fn [backend state]
              (let [runner (runners backend) tree-world (runner state 2000000)]
                (when-not (= :done (:status tree-world)) (throw (ex-info "Tree budget exhausted" (describe tree-world))))
                (with-meta (runner (m/start tree-world fold [callback-value (:result tree-world) 0]) 2000000)
                  {:tree-at-fold-start (select-keys (describe tree-world) [:heap-nodes :next-id :stats])})))
        cold (mapv (fn [backend] (let [[actual metrics] (measure #(run backend (initial 11)))]
                                  (assoc metrics :backend backend :result (:result actual) :world (describe actual))))
                   [:reference :mutable :jvm])
        _ (doseq [_ (range 2) backend [:reference :mutable :jvm]] (run backend (initial 11)))
        results (vec
                 (for [n sizes :let [expected (run :reference (initial n))]
                       trial (range trials)
                       backend (if (even? trial) [:reference :mutable :jvm] [:jvm :mutable :reference])]
                   (let [[actual metrics] (measure #(run backend (initial n)))]
                     (when-not (= expected actual) (throw (ex-info "Complete World mismatch" {:n n :backend backend})))
                     (when-not (= (quot (+ n 9) 10) (:result actual))
                       (throw (ex-info "Original rbmap fold result mismatch" {:n n :result (:result actual)})))
                     (assoc metrics :n n :trial trial :backend backend :result (:result actual) :world (describe actual)))))]
    {:schema "unchanged-rbmap-runtime/1" :scope "Native frontend exported exact source; raw trusted IR runtime. Hosted loading and Ansatz kernel admission not tested. Fresh Worlds; thaw/run/freeze plus fold start included. Two n11 warmups per backend; steady state not established."
     :function-count (count functions) :prepare preparation :cold-n11 cold
     :runs results :jvm-route (lazy/summary program)}))

(defn compiler-ir [path trials]
  (let [prefix "Mcmc.Executable.Finite.CompilerIR."
        labels (mapv #(str prefix %) ["categoricalProgram" "metropolisHastingsProgram" "twoStateTarget" "twoStateProposal"])
        {:keys [names functions program runners preparation]} (setup path labels)
        results (vec (for [[label name] (map vector labels names)
                           :let [initial (m/start (m/world functions) name [])
                                 expected ((runners :reference) initial 100000)]
                           trial (range trials) backend [:reference :mutable :jvm]]
                       (let [[actual metrics] (measure #((runners backend) initial 100000))]
                         (when-not (= expected actual) (throw (ex-info "CompilerIR complete World mismatch" {:label label :backend backend})))
                         (assoc metrics :label label :trial trial :backend backend :world (describe actual)))))]
    {:schema "unchanged-compiler-ir-runtime/1" :scope "Original sampler DSL constructor values only; no sampling/interpreter/hosted loader/proof checking claim. Backend complete World parity; no independent native value oracle yet."
     :function-count (count functions) :prepare preparation :runs results :jvm-route (lazy/summary program)}))
