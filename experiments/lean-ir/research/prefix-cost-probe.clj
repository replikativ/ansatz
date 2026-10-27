(ns prototype.prefix-cost-probe
  "Small fixture only: 17 checked native constants and explicitly modeled guest helpers.
   Synthetic runtime-dependency edges are authority-walk load, never guest calls.
   No full Init, actual frontend, native IR export, or gate acceptance is exercised."
  (:require [prototype.resident-init-prefix-test :as fixture]
            [prototype.resident-init-prefix :as prefix]
            [prototype.resident-frontend :as resident]
            [prototype.module-import :as imports]
            [prototype.source-import :as source]
            [prototype.raw-interop :as raw]
            [prototype.machine :as m]))

(defonce ^:private escrow (atom nil)) ; Private experiment owners/failure: never print or serialize.
(defn- require! [condition message] (when-not condition (throw (ex-info message {}))))
(defn- measure [invoke capture]
  (let [bean ^com.sun.management.ThreadMXBean (java.lang.management.ManagementFactory/getThreadMXBean)
        tid (.getId (Thread/currentThread))
        cpu? (and (.isCurrentThreadCpuTimeSupported bean) (.isThreadCpuTimeEnabled bean))
        alloc? (and (.isThreadAllocatedMemorySupported bean) (.isThreadAllocatedMemoryEnabled bean))
        cpu (when cpu? (.getCurrentThreadCpuTime bean))
        bytes (when alloc? (.getThreadAllocatedBytes bean tid)) wall (System/nanoTime)
        result (invoke) _ (capture result)
        end-wall (System/nanoTime) end-cpu (when cpu? (.getCurrentThreadCpuTime bean))
        end-bytes (when alloc? (.getThreadAllocatedBytes bean tid))]
    [result {:wall-ns (- end-wall wall) :cpu-ns (when cpu? (- end-cpu cpu))
             :allocated-bytes (when alloc? (- end-bytes bytes))}]))

(defn- helper-name [i] ["str" ["str" ["anonymous"] "PrefixCostProbe"] (str "helper" i)])
(defn- grow-fixture [{:keys [context configuration] :as original} n own!]
  (let [before (resident/snapshot context)
        nodes (into {} (for [i (range n)]
                         [(helper-name i) (cond-> {:params [] :body [:return [:imm 0]]}
                                           (< (inc i) n) (assoc :runtime-dependencies [(helper-name (inc i))]))]))
        root (:root imports/helpers)
        old (get-in configuration [:trusted-functions root])
        changed (cond-> old (pos? n) (update :runtime-dependencies (fnil conj []) (helper-name 0)))
        trusted (assoc (into (:trusted-functions configuration) nodes) root changed)
        functions (assoc (into (get-in before [:world :functions]) nodes) root changed)
        independent (assoc configuration :trusted-functions trusted)
        prepared (-> before (assoc-in [:world :functions] functions)
                     (assoc :session (raw/open-functions functions (:trusted-bindings independent)
                                       (raw/session-options (:session before)))))
        ;; The new independent registry is constructed deliberately before adoption;
        ;; it is never inferred from an installed live image or a successful receipt.
        [candidate _] (measure #(resident/adopt-prepared prepared independent) own!)]
    (assoc original :context candidate :configuration independent)))

(defn- instrument [rows phase own! invoke]
  (let [specs [['prototype.resident-init-prefix 'preparation-readiness! :preparation-readiness]
               ['prototype.resident-frontend 'adoption-readiness! :adoption-readiness]
               ['prototype.resident-frontend 'adopt-prepared :adoption]
               ['prototype.source-import 'release-init-prefix :registry-release]
               ['prototype.eval-const 'validate-executables! :executable-closure]
               ['prototype.eval-const 'check-function-closure! :identity-closure-walk]
               ['prototype.resident-code-validation 'validate! :code-proof-validation]
               ['prototype.resident-code-validation 'validate-mappings! :code-identity-loops]]
        wrappers (into {} (keep (fn [[space name label]]
                                 (when-let [v (some-> (find-ns space) (ns-resolve name))]
                                   (let [original @v]
                                     [v (fn [& args]
                                          (let [[result metrics] (measure #(apply original args)
                                                                   (if (= label :adoption) own! (constantly nil)))]
                                            (swap! rows conj {:phase phase :operation label :inclusive true
                                                              :scope :caller-thread :metrics metrics})
                                            result))])))) specs)]
    (with-redefs-fn wrappers invoke)))

(defn- median [values]
  (when (every? number? values)
    (let [sorted (vec (sort values)) n (count sorted) middle (quot n 2)]
      (if (odd? n) (nth sorted middle) (/ (+ (nth sorted (dec middle)) (nth sorted middle)) 2.0)))))
(defn run-size
  "Prepare once; SAMPLES independent releases per lane (1..10). Instrumentation
   is inclusive and overlapping; baseline release timing is the primary metric."
  ([n] (run-size n 10))
  ([n samples]
   (require! (contains? #{0 1000 10000} n) "Use synthetic dependency count 0,1000,10000")
   (require! (and (integer? samples) (<= 1 samples 10)) "Use 1..10 samples per lane")
   (let [source-cell (volatile! nil)
         result
         (fixture/with-fixture :mutable
           (fn [{:keys [source] :as original}]
             (vreset! source-cell source)
             (let [owned (atom []) closed (java.util.IdentityHashMap.)
                   own! (fn [context]
                          (when-not (some #(identical? context %) @owned) (swap! owned conj context))
                          (swap! escrow assoc :owners @owned) context)
                   close! (fn [context]
                            (when-not (.containsKey closed context)
                              (resident/close! context) (.put closed context true)))
                   spans (atom [])]
               (reset! escrow {:phase :opening :source source :owners []})
               (try
                 (let [grown (grow-fixture original n own!)
                       [prepared prepare-time]
                       (measure #(instrument spans :prepare own! (fn [] (fixture/prepare grown)))
                                (fn [packet] (swap! escrow assoc :prepared packet) (own! (:context packet))))
                       context (:context prepared) capability (:prefix prepared)
                       pristine (resident/snapshot context)
                       registry (get-in pristine [:world :source-import-prefixes])
                       raw-prefix (first (vals registry)) root (:state raw-prefix)
                       root-rc (:rc (m/node (:world pristine) root))
                       protected (count (:protected-functions
                                         (resident/adoption-readiness! pristine (:configuration grown))))
                       _ (require! (and (= 1 (count registry)) (= 1 root-rc)
                                        (= 17 (:constant-count (prefix/descriptor capability)))
                                        (= source/init-requests (:producer-imports (prefix/descriptor capability))))
                                   "Prepared fixture prefix registry/RC/descriptor differs")
                       trials
                       (vec (for [lane [:baseline :instrumented] trial (range samples)]
                              (let [release #(prefix/release-prefix context capability)
                                    [packet timing]
                                    (measure #(if (= lane :instrumented)
                                                (instrument spans [:release trial] own! release) (release))
                                             (fn [packet] (swap! escrow assoc :last-returned packet) (own! (:context packet))))
                                    branch (:context packet)
                                    after (resident/snapshot branch)
                                    _ (require! (and (empty? (get-in after [:world :source-import-prefixes]))
                                                     (not (contains? (get-in after [:world :heap]) (:id root)))
                                                     (identical? pristine (resident/snapshot context))
                                                     (= root-rc (:rc (m/node (:world (resident/snapshot context)) root)))
                                                     (= (:environment pristine) (:environment after))
                                                     (= (:options pristine) (:options after))
                                                     (= (:receipt packet) (prefix/descriptor capability))
                                                     (false? @(:closed source)))
                                                "Release branch registry/RC/root/persistence control failed")
                                    [_ close-time] (measure #(close! branch) (constantly nil))]
                                {:lane lane :trial trial :release timing :close close-time
                                 :registry-count 0 :prefix-root-present false :pristine-root-rc root-rc})))
                       summary {:schema "tiny-prefix-cost-probe/1" :synthetic-dependencies n :samples-per-lane samples
                                :scope "17 verified native constants; modeled guest helpers; synthetic unexecuted runtime-dependency chain. No full Init/frontend/gate. Baseline uninstrumented; nested instrumented spans inclusive and overlapping. Caller-thread CPU/allocation, elapsed wall; owner escrow and instrument wrappers included. Missing nested spans mean unobserved, not zero cost."
                                :constant-count 17 :protected-functions protected :prefix-registry-count 1 :prefix-root-rc root-rc
                                :preparation {:instrumented true :metrics prepare-time}
                                :runs trials :spans @spans
                                :baseline-medians (into {} (for [metric [:wall-ns :cpu-ns :allocated-bytes]]
                                                             [metric (median (map #(get-in % [:release metric])
                                                                                 (filter #(= :baseline (:lane %)) trials)))]))}]
                   (swap! escrow assoc :phase :complete :summary summary)
                   summary)
                 (catch Throwable failure (swap! escrow assoc :phase :failed :failure failure) (throw failure))
                 (finally
                   ;; Close known returned Contexts before with-fixture closes the
                   ;; actual borrowed Source/Store. Never replay release to clean up.
                   (doseq [context (reverse @owned)] (close! context)))))))
         closed? (true? @(:closed @source-cell))]
     (require! closed? "Fixture did not close its actual native Source")
     (reset! escrow {:phase :closed :summary result})
     (assoc result :source-closed-after-fixture true))))

(defn run-probe ([] (run-probe [0 1000 10000] 10))
  ([sizes samples] (mapv #(run-size % samples) sizes)))
