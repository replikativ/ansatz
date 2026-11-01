(ns prototype.store-bench
  "Synthetic declaration I/O and edit-turnover experiment; not a cold-start benchmark."
  (:require [clojure.data.json :as json]
            [clojure.java.io :as io]
            [prototype.bench :as timing]
            [prototype.compact-bench :as provenance]
            [prototype.declaration-store :as store]
            [prototype.import-ir :as ir]
            [prototype.lazy-runtime :as lazy]
            [prototype.machine :as m]
            [prototype.mutable :as u]
            [prototype.module-bench :as modules]))

(defn- run-selected [catalogue cache]
  (let [functions (ir/load-closure catalogue [modules/entry])
        program (lazy/open-program functions {} cache)
        initial (m/start (m/world functions) modules/entry [])]
    {:state (u/freeze (lazy/run! program (u/thaw initial)))
     :initial initial :counts (lazy/summary program)}))

(defn- check-result! [result expected]
  (when-not (and (= expected (get-in result [:state :result]))
                 (= (m/run (:initial result)) (:state result)))
    (throw (ex-info "Store execution differs from reference" {:expected expected}))))

(defn one-case [size samples]
  (let [input (str "target/store-module-" size ".jsonl")
        _ (modules/write-module! size input)
        ;; Each run gets a new directory: pack timing includes first publication.
        root (.toFile (java.nio.file.Files/createTempDirectory
                       (.toPath (io/file "target")) (str "declarations-" size "-")
                       (make-array java.nio.file.attribute.FileAttribute 0)))
        packed (timing/measure #(store/pack! root [input]))
        checkpoint (timing/measure #(store/checkpoint! (:value packed)))
        hash (:value checkpoint)
        opens
        (mapv (fn [sample]
                ;; Alternate order across samples to limit a fixed order bias.
                (let [open #(timing/measure (fn [] (store/open-index root hash)))
                      raw #(timing/measure (fn [] (ir/index-bundles [input])))
                      measured (if (even? sample)
                                 (let [a (raw) b (open)] {:raw a :store b})
                                 (let [b (open) a (raw)] {:raw a :store b}))]
                  (update-vals measured #(dissoc % :value)))) (range samples))
        reopened (store/open-index root hash)
        raw (ir/index-bundles [input])
        before (store/stats reopened)
        lowering (timing/measure #(ir/load-closure reopened [modules/entry]))
        _ (when-not (= (:value lowering) (ir/load-closure raw [modules/entry]))
            (throw (ex-info "Store/raw lowering mismatch" {})))
        after (store/stats reopened)
        cache (lazy/code-cache)
        first-run (timing/measure #(run-selected reopened cache))
        _ (check-result! (:value first-run) 42)
        edits
        (mapv (fn [i]
                (let [expected (+ 43 i)
                      before (store/stats reopened)
                      measured (timing/measure
                                #(let [edited (store/with-declaration!
                                               reopened (modules/declaration modules/value-name expected))]
                                   (run-selected edited cache)))
                      result (:value measured)
                      after (store/stats reopened)]
                  (check-result! result expected)
                  (assoc (dissoc measured :value)
                         :compiled (get-in result [:counts :compiled])
                         :reused (get-in result [:counts :cache-hits])
                         :blob-reads (- (:blob-reads after) (:blob-reads before))
                         :blob-publishes (- (:blob-publishes after) (:blob-publishes before)))))
              (range samples))
        old-again (run-selected reopened cache)
        _ (check-result! old-again 42)]
    {:total-declarations (+ size 2) :selected-declarations (count (:value lowering))
     :input-bytes (.length (io/file input))
     :index-bytes (:index-bytes before) :selected-blob-bytes (- (:blob-bytes after) (:blob-bytes before))
     :pack (dissoc packed :value) :checkpoint (dissoc checkpoint :value)
     :raw-json-reopen (timing/summarize (map :raw opens))
     :store-index-reopen (timing/summarize (map :store opens))
     :blobs-read-on-open (:blob-reads before)
     :selected-load (dissoc lowering :value) :selected-blob-reads (- (:blob-reads after) (:blob-reads before))
     :selected-first-load-run-freeze (dissoc first-run :value)
     :first-counts (get-in first-run [:value :counts])
     :edit-publish-load-run-freeze (timing/summarize edits)
     :edit-compiled (mapv :compiled edits) :edit-reused (mapv :reused edits)
     :edit-blob-reads (mapv :blob-reads edits) :edit-blob-publishes (mapv :blob-publishes edits)
     :old-world-result (get-in old-again [:state :result])}))

(defn experiment
  ([] (experiment [100 1000 10000] 7))
  ([sizes samples]
   (let [paths ["src/prototype/declaration_store.clj" "src/prototype/store_bench.clj"
                "src/prototype/import_ir.clj" "src/prototype/module_bench.clj"
                "src/prototype/lazy_runtime.clj" "src/prototype/block_compile.clj"
                "src/prototype/leaf_compile.clj" "src/prototype/machine.cljc"
                "src/prototype/mutable.clj" "src/prototype/bench.clj"
                "src/prototype/compact_bench.clj"]
         hashes #(into {} (map (fn [p] [p (provenance/sha256 p)]) paths))
         before (hashes) cases (mapv #(one-case % samples) sizes)]
     (when-not (= before (hashes)) (throw (ex-info "Sources changed during store experiment" {})))
     {:java-version (System/getProperty "java.version") :clojure-version (clojure-version)
      :source-sha256 before :samples samples :cases cases
      :limitations ["Synthetic modules with two reachable declarations"
                    "One shared JVM and warm filesystem cache; no isolated cold-start claim"
                    "Pack decodes every declaration once; index reopen and checkpoint remain O(N)"
                    "Edit includes publishing one blob but excludes full index checkpoint"
                    "No Lean elaboration, producer export or proof admission in timings"
                    "Append-only prototype; no blob GC, fsync durability or lower-body cache"]})))

(defn -main [& sizes]
  (println (json/write-str (experiment (if (seq sizes) (mapv #(Long/parseLong %) sizes) [100 1000 10000]) 7)))
  (shutdown-agents))
