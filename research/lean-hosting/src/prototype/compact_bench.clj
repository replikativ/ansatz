(ns prototype.compact-bench
  "Same-process ABBA comparison of two runtime implementations with one snapshot ABI."
  (:require [clojure.data.json :as json]
            [prototype.bench :as stats]
            [prototype.block-compile :as b]
            [prototype.heap-bench :as heap-bench]
            [prototype.heap-examples :as h]
            [prototype.mutable]
            [prototype.repl :as repl])
  (:import [java.security MessageDigest]
           [java.math BigInteger]))

(defn sha256 [path]
  (format "%064x" (BigInteger. 1 (.digest (MessageDigest/getInstance "SHA-256")
                                         (.getBytes (slurp path) "UTF-8")))))

(defn -main [& [baseline warmup samples]]
  (when-not baseline (throw (ex-info "Supply baseline mutable.clj source path" {})))
  (let [warmup (Long/parseLong (or warmup "40"))
        samples (Long/parseLong (or samples "15"))
        current "src/prototype/mutable.clj"
        sources (into {} (map (fn [path] [path (sha256 path)])
                              [baseline current "src/prototype/compact_bench.clj"
                               "src/prototype/block_compile.clj" "src/prototype/heap_bench.clj"
                               "src/prototype/heap_examples.clj" "src/prototype/machine.cljc"
                               "src/prototype/repl.clj" "src/prototype/bench.clj"
                               "fixtures/list-map.jsonl" "fixtures/list-fold.jsonl"
                               "fixtures/list-reverse.jsonl" "fixtures/tree-mirror.jsonl"]))
        functions (h/functions)
        phases
        (mapv (fn [[label path]]
                ;; Normal Var dispatch makes refreshed helpers visible to blocks.
                ;; Never refresh while holding live mutable machines or direct-linked code.
                (binding [*compiler-options* (assoc *compiler-options* :direct-linking false)]
                  (repl/refresh-functions! 'prototype.mutable path)
                  (let [program (b/compile-program functions)]
                    {:implementation label
                     :execution (vec (for [scenario (heap-bench/cases) backend [:mutable :blocks]]
                                       (heap-bench/execution functions program scenario backend warmup samples)))
                     :safepoints (mapv #(heap-bench/safepoint functions program % warmup samples)
                                       [100 1000 10000])
                     :edit-turnaround (heap-bench/edit-turnaround functions program samples)})))
              [[:baseline baseline] [:compact current] [:compact current] [:baseline baseline]])]
    (doseq [[path digest] sources]
      (when-not (= digest (sha256 path))
        (throw (ex-info "Source changed during comparison" {:path path}))))
    (println (json/write-str
              {:java-version (System/getProperty "java.version")
               :java-vendor (System/getProperty "java.vendor")
               :java-vm-version (System/getProperty "java.vm.version")
               :clojure-version (clojure-version) :warmup warmup :samples samples
               :source-sha256 sources :order "ABBA" :phases phases
               :limitations ["Same JVM; JIT invalidation, GC and scheduling affect timings"
                             "No native comparison in this experiment"
                             "Kernel timing excludes restore and freeze"
                             "Full snapshot equality checked outside each measured execution"]}))
    (shutdown-agents)))
