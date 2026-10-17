(ns prototype.call-bench
  "Compare lexical regions, per-function registers and guarded scalar calls."
  (:require [clojure.data.json :as json]
            [prototype.bench :as stats]
            [prototype.block-compile :as b]
            [prototype.compact-bench :as provenance]
            [prototype.heap-bench :as heap-bench]
            [prototype.heap-examples :as h]))

(def profiles
  {:regions {:lexical-joins true}
   :registers {:lexical-joins true :compact-registers true}
   :leaves {:lexical-joins true :leaf-calls true}
   :combined {:lexical-joins true :leaf-calls true :compact-registers true}})

(defn -main [& [warmup samples]]
  (let [warmup (Long/parseLong (or warmup "60")) samples (Long/parseLong (or samples "21"))
        paths ["src/prototype/call_bench.clj" "src/prototype/leaf_compile.clj"
               "src/prototype/block_compile.clj" "src/prototype/mutable.clj"
               "src/prototype/machine.cljc" "src/prototype/heap_bench.clj"
               "src/prototype/heap_examples.clj" "src/prototype/bench.clj"
               "src/prototype/compact_bench.clj" "fixtures/list-map.jsonl"
               "fixtures/list-fold.jsonl" "fixtures/list-reverse.jsonl" "fixtures/tree-mirror.jsonl"]
        hashes #(into {} (map (fn [path] [path (provenance/sha256 path)]) paths))
        before (hashes) functions (h/functions)
        cases (concat (heap-bench/cases)
                      (for [shared? [false true]]
                        {:workload :map :guest-callback? true :size 1000 :shared? shared?}))
        phases
        (binding [*compiler-options* (assoc *compiler-options* :direct-linking false)]
          (mapv (fn [profile]
                  (let [compiled (stats/measure #(b/compile-program functions nil (profiles profile)))
                        program (:value compiled)]
                    {:profile profile :compilation (dissoc compiled :value)
                     :leaf-plans (count (:leaf-plans program))
                     :leaf-sites (reduce + (map :leaf-sites (vals (:blocks program))))
                     :register-widths (vec (sort (vals (:register-layouts program))))
                     :execution (mapv #(heap-bench/execution functions program % :blocks warmup samples) cases)
                     :safepoints (mapv #(heap-bench/safepoint functions program % warmup samples) [100 1000 10000])
                     :edit-turnaround (heap-bench/edit-turnaround functions program samples)}))
                [:regions :combined :registers :leaves :combined :regions]))]
    (when-not (= before (hashes)) (throw (ex-info "Sources changed during call benchmark" {})))
    (println (json/write-str
              {:java-version (System/getProperty "java.version")
               :java-vendor (System/getProperty "java.vendor")
               :java-vm-version (System/getProperty "java.vm.version")
               :clojure-version (clojure-version) :source-sha256 before
               :warmup warmup :samples samples :phases phases
               :limitations ["One JVM with shared JIT, GC and scheduling history"
                             "Execution excludes restore, freeze and reference comparisons"
                             "Register layouts are per function, not live-only spills"
                             "Scalar specialization is bounded to eight pure guest instructions"
                             "No native throughput comparison"]}))
    (shutdown-agents)))
