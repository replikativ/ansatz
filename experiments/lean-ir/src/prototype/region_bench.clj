(ns prototype.region-bench
  "ABBA comparison of compiled blocks and opt-in lexical regions."
  (:require [clojure.data.json :as json]
            [prototype.bench :as stats]
            [prototype.block-compile :as b]
            [prototype.compact-bench :as provenance]
            [prototype.heap-bench :as heap-bench]
            [prototype.heap-examples :as h]))

(defn -main [& [warmup samples]]
  (let [warmup (Long/parseLong (or warmup "60"))
        samples (Long/parseLong (or samples "21"))
        paths ["src/prototype/region_bench.clj" "src/prototype/block_compile.clj"
               "src/prototype/mutable.clj" "src/prototype/machine.cljc"
               "src/prototype/heap_bench.clj" "src/prototype/heap_examples.clj"
               "src/prototype/bench.clj" "src/prototype/compact_bench.clj"
               "fixtures/list-map.jsonl" "fixtures/list-fold.jsonl"
               "fixtures/list-reverse.jsonl" "fixtures/tree-mirror.jsonl"]
        hashes #(into {} (map (fn [path] [path (provenance/sha256 path)]) paths))
        source-hashes (hashes)
        functions (h/functions)
        phases
        (binding [*compiler-options* (assoc *compiler-options* :direct-linking false)]
          (mapv (fn [lexical?]
                  (let [compiled (stats/measure #(b/compile-program functions nil {:lexical-joins lexical?}))
                        program (:value compiled)]
                    {:backend (if lexical? :regions :blocks)
                     :compilation (dissoc compiled :value)
                     :blocks (count (:blocks program))
                     :inlined-jumps (reduce + (map :inlined-jumps (vals (:blocks program))))
                     :execution (mapv #(heap-bench/execution functions program % :blocks warmup samples)
                                      (heap-bench/cases))
                     :safepoints (mapv #(heap-bench/safepoint functions program % warmup samples)
                                       [100 1000 10000])
                     :edit-turnaround (heap-bench/edit-turnaround functions program samples)}))
                [false true true false]))]
    (when-not (= source-hashes (hashes))
      (throw (ex-info "Sources changed during region comparison" {})))
    (println (json/write-str
              {:java-version (System/getProperty "java.version")
               :java-vendor (System/getProperty "java.vendor")
               :java-vm-version (System/getProperty "java.vm.version")
               :clojure-version (clojure-version) :warmup warmup :samples samples
               :source-sha256 source-hashes :order "ABBA" :phases phases
               :limitations ["Same JVM; GC, JIT and scheduling affect times"
                             "No native or sustained-throughput comparison"
                             "Execution excludes restore, freeze and reference equality checks"
                             "Calls and observable safepoints still spill full diagnostic locals"]}))
    (shutdown-agents)))
