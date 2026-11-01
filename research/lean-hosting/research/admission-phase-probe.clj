(ns admission-phase-probe
  "Tiny 17-CI admission MODEL instrumentation; no full image or runtime authority."
  (:require [prototype.full-init-admission :as admission]
            [prototype.full-init-admission-test :as model]
            [prototype.kernel-artifact :as artifact]
            [prototype.kernel-projection-snapshot :as snapshot]
            [prototype.imported-kernel :as kernel]
            [clojure.pprint :as pp]))
(def ^:dynamic *parent* nil)
(defn run-once [iteration]
  (let [events (atom []) ids (atom 0)
        bean ^com.sun.management.ThreadMXBean (java.lang.management.ManagementFactory/getThreadMXBean)
        tid (.threadId (Thread/currentThread))
        _ (assert (and (.isCurrentThreadCpuTimeSupported bean) (.isThreadCpuTimeEnabled bean)
                       (.isThreadAllocatedMemorySupported bean) (.isThreadAllocatedMemoryEnabled bean))
                  "Enabled caller CPU/allocation counters are required")
        targets {#'admission/admit-restored! :admission-operation
                 #'admission/projection :project-complete-native-map
                 #'artifact/issue-admitted-projection :publish-artifact
                 #'artifact/inspect-for-world :inspect-artifact
                 #'snapshot/snapshot-projection :snapshot-java-projection
                 #'snapshot/validate-projection :validate-java-projection
                 #'snapshot/validate-segments :validate-java-segments
                 #'kernel/associate-projection-progress :associate-actual-map}
        wrappers (into {} (map (fn [[v label]]
                                (let [original @v]
                                  [v (fn [& args]
                                       (let [id (swap! ids inc) parent *parent*
                                             wall (System/nanoTime) cpu (.getCurrentThreadCpuTime bean)
                                             allocation (.getThreadAllocatedBytes bean tid)]
                                         (binding [*parent* id]
                                           (try (apply original args)
                                                (finally (swap! events conj {:id id :parent parent :phase label
                                                                             :wall-ns (- (System/nanoTime) wall)
                                                                             :cpu-ns (- (.getCurrentThreadCpuTime bean) cpu)
                                                                             :allocated-bytes (- (.getThreadAllocatedBytes bean tid) allocation)}))))))])) targets))]
    (model/with-model
      (fn [{:keys [input]}]
        (let [result (with-redefs-fn wrappers #(admission/admit-restored! input))]
          (assert (= :ok (:status result)))
          (assert (= 17 (count (get-in result [:checked-result :constants])))))))
    (let [records (sort-by :id @events)
          children (group-by :parent records)
          spans (mapv (fn [r] (reduce (fn [r k]
                                      (assoc r (keyword (str "exclusive-" (name k)))
                                             (- (k r) (reduce + 0 (map k (get children (:id r)))))))
                                    r [:wall-ns :cpu-ns :allocated-bytes])) records)
          counts (frequencies (map :phase spans))]
      (assert (= {:admission-operation 1 :project-complete-native-map 1
                  :publish-artifact 1 :snapshot-java-projection 1
                  :inspect-artifact 4 :validate-java-projection 4
                  :associate-actual-map 1 :validate-java-segments 2} counts))
      (doseq [metric [:wall-ns :cpu-ns :allocated-bytes]
              :let [exclusive (keyword (str "exclusive-" (name metric)))]]
        (assert (every? #(not (neg? (exclusive %))) spans))
        (assert (= (metric (first spans)) (reduce + (map exclusive spans)))))
      {:iteration iteration :modelled-native-ci-count 17 :counts counts :spans spans})))
(defn run! []
  {:scope :tiny-admission-model-only :full-init false :backend :reference
   :limits ["Privately modelled Factory/profile seams; not admission of the full profile."
            "Timings include instrumentation overhead; no full-DAG scaling or startup benefit inferred."
            "No storage/raw-driver functions redefined; existing identity guards remain intact."]
   :runs (mapv run-once (range 4))})
