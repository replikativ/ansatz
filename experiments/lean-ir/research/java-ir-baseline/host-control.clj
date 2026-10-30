(ns java-ir-host-control
  "Paired no-host computational control; never restores Init or runs a frontend."
  (:require [java-ir-baseline :as j]
            [prototype.unchanged-program-benchmark :as benchmark]))
(defn run-mode [artifacts explicit?]
  (let [rows (j/rows "test/fixtures/unchanged-programs/rbmap-main.jsonl")
        contexts (into {} (for [[label artifact] artifacts
                                :let [basis (j/class-basis artifact)
                                      ctx (assoc basis :explicit explicit?
                                                 :program (j/invoke-static (:prepare basis) [rows]))
                                      engine (j/machine ctx)]]
                            [label {:ctx ctx :engine engine
                                    :ids (mapv #(int (j/function-id ctx %))
                                               ["mkMap" "fold._redArg" "main._closed_0"])}]))
        run (fn [label]
              (let [{:keys [ctx engine ids]} (contexts label)]
                (.invoke ^java.lang.reflect.Method (:batch ctx) engine
                         (object-array (concat ids [(int 1000) (int 100)])))))]
    (try
      (dotimes [_ 3]
        (doseq [label [:prior :host]] (assert (= 10050 (run label)))))
      {:explicit explicit?
       :runs (vec (for [trial (range 7)
                        label (if (even? trial) [:prior :host] [:host :prior])]
                    (let [[answer metrics] (benchmark/measure #(run label))]
                      (assert (= 10050 answer))
                      {:trial trial :artifact label :repetitions 100 :metrics metrics})))}
      (finally
        (doseq [[_ {:keys [ctx engine]}] contexts] (j/close! ctx engine))))))
(defn run! [prior host]
  {:scope :paired-rbmap-computation-only
   :limits ["Warmed retained 384 MiB development JVM, shared machine."
            "Alternating inputs 1000/1001; seven alternating-order batches of 100."
            "Measures no-host ordinary execution, not host latency, frontend speed or native/JIT performance."
            "First control attempt rejected an incorrect checksum expectation; this complete rerun uses 10050."]
   :modes (mapv #(run-mode {:prior prior :host host} %) [false true])})
