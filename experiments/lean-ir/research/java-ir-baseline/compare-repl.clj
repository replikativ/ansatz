(ns java-ir-comparison
  "Bounded old/new engine control, usable in a retained REPL."
  (:require [java-ir-baseline :as j]
            [prototype.unchanged-program-benchmark :as benchmark]))

(defn compare-engines [previous current]
  (let [bases [[:previous (j/open-program previous "test/fixtures/unchanged-programs/rbmap.jsonl")]
               [:current (j/open-program current "test/fixtures/unchanged-programs/rbmap.jsonl")]]
        engines (vec (for [[generation basis] bases mode [:recursive :explicit]
                           :let [ctx (assoc basis :explicit (= mode :explicit))]]
                       {:generation generation :mode mode :basis ctx :engine (j/machine ctx)
                        :ids (mapv #(int (j/function-id ctx %)) ["mkMap" "fold._redArg" "main._closed_0"])}))
        run (fn [{:keys [basis engine ids]}]
              (.invoke ^java.lang.reflect.Method (:batch basis) engine
                       (object-array (into ids [(int 1000) (int 100)]))))]
    (try
      (doseq [_ (range 5) entry engines] (assert (= 10050 (run entry))))
      {:scope "Paired computational RBMap1000/1001; one retained engine per generation/driver; preparation excluded"
       :repetitions 100 :warmup-batches-per-engine 5
       :samples (vec (for [trial (range 7) entry (if (even? trial) engines (reverse engines))]
                       (let [[answer metrics] (benchmark/measure #(run entry))]
                         (assert (= 10050 answer))
                         (merge metrics (select-keys entry [:generation :mode])
                                {:trial trial :checksum answer}))))}
      (finally (doseq [{:keys [basis engine]} engines] (j/close! basis engine))))))
