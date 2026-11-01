(ns prototype.module-bench
  "Synthetic module-size experiment; not a Lean frontend/elaborator benchmark."
  (:require [clojure.data.json :as json]
            [clojure.java.io :as io]
            [prototype.bench :as stats]
            [prototype.block-compile :as b]
            [prototype.compact-bench :as provenance]
            [prototype.import-ir :as ir]
            [prototype.lazy-runtime :as lazy]
            [prototype.machine :as m]
            [prototype.mutable :as u]))

(defn name-of [s] ["str" ["anonymous"] s])
(def entry (name-of "entry"))
(def value-name (name-of "value"))
(defn literal-body [] ["ret" {:var {:id {:idx 0}}}])
(defn declaration [name n]
  {:kind "decl" :name name :dependencies []
   :ir {:fdecl {:f name :xs [] :type "object"
                :body ["vdecl" {:idx 0} "object" {:lit {:v {:num {:v n}}}} (literal-body)]}}})

(defn write-module! [size path]
  (with-open [out (io/writer path)]
    (doseq [row (concat [{:kind "manifest" :schema "lean-ir-probe/1" :leanVersion "4.33.1" :modules []}
                        {:kind "decl" :name entry :dependencies [value-name]
                         :ir {:fdecl {:f entry :xs [] :type "object"
                                      :body ["vdecl" {:idx 0} "object" {:fap {:c value-name :ys []}}
                                             ["vdecl" {:idx 1} "object" {:lit {:v {:num {:v 7}}}}
                                              ["ret" {:var {:id {:idx 0}}}]]]}}}
                        (declaration value-name 42)]
                       (map #(declaration (name-of (str "cold" %)) (+ 1000 %)) (range size)))]
      (.write out (str (json/write-str row) "\n")))))

(defn one-case [size samples]
  (let [path (str "target/module-" size ".jsonl")
        _ (write-module! size path)
        indexed (stats/measure #(ir/index-bundles [path]))
        catalogue (:value indexed)
        selected (stats/measure #(ir/load-closure catalogue [entry]))
        all (stats/measure #(into {} (map ir/lower-declaration (vals (:declarations catalogue)))))
        functions (:value all)
        initial (m/start (m/world functions) entry [])
        restored (stats/measure #(u/thaw initial))
        cache (lazy/code-cache)
        opened (stats/measure #(lazy/open-program functions {} cache))
        program (:value opened)
        first-run (stats/measure #(lazy/run! program (:value restored)))
        reference (m/run initial)
        _ (when-not (= reference (u/freeze (:value first-run))) (throw (ex-info "Lazy module result mismatch" {})))
        warm (mapv (fn [_]
                     (let [machine (u/thaw initial) run (stats/measure #(lazy/run! program machine))]
                       (when-not (= reference (u/freeze (:value run))) (throw (ex-info "Warm module mismatch" {})))
                       (dissoc run :value))) (range samples))
        edits (mapv (fn [i]
                      (let [expected (+ 43 i)
                            edited (assoc-in functions [value-name :body] [:let 0 [:literal expected] [:return [:var 0]]])
                            start (m/start (m/world edited) entry [])
                            measured (stats/measure #(let [next (lazy/open-program edited {} cache)
                                                           state (u/freeze (lazy/run! next (u/thaw start)))]
                                                       {:state state :counts (lazy/summary next)}))
                            {:keys [state counts]} (:value measured)]
                        (when-not (= (m/run start) state) (throw (ex-info "Edited module mismatch" {})))
                        (assoc (dissoc measured :value) :compiled (:compiled counts) :reused (:cache-hits counts))))
                    (range samples))
        selected-cache (lazy/code-cache)
        selected-run
        (fn [catalogue]
          (let [functions (ir/load-closure catalogue [entry])
                program (lazy/open-program functions {} selected-cache)
                initial (m/start (m/world functions) entry [])
                result (u/freeze (lazy/run! program (u/thaw initial)))]
            {:state result :initial initial :counts (lazy/summary program)}))
        selected-first (stats/measure #(selected-run catalogue))
        _ (when-not (= (m/run (get-in selected-first [:value :initial]))
                       (get-in selected-first [:value :state]))
            (throw (ex-info "Selected module mismatch" {})))
        selected-edits
        (mapv (fn [i]
                (let [catalogue (assoc-in catalogue [:declarations value-name] (declaration value-name (+ 43 i)))
                      measured (stats/measure #(selected-run catalogue))
                      counts (get-in measured [:value :counts])]
                  (when-not (= (m/run (get-in measured [:value :initial])) (get-in measured [:value :state]))
                    (throw (ex-info "Selected edit mismatch" {})))
                  (assoc (dissoc measured :value) :compiled (:compiled counts) :reused (:cache-hits counts))))
              (range samples))
        eager (stats/measure #(b/compile-program functions nil {:lexical-joins true}))]
    {:cold-declarations size :total-declarations (count functions)
     :parse-and-index (dissoc indexed :value) :selected-lowering (dissoc selected :value)
     :selected-declarations (count (:value selected)) :all-lowering (dissoc all :value)
     :restore (dissoc restored :value) :lazy-open (dissoc opened :value)
     :lazy-first-execution (dissoc first-run :value) :lazy-counts (lazy/summary program)
     :lazy-warm-execution (stats/summarize warm) :lazy-edit-restore-run-freeze (stats/summarize edits)
     :edit-compiled (mapv :compiled edits) :edit-reused (mapv :reused edits)
     :selected-first-load-run-freeze (dissoc selected-first :value)
     :selected-warm-edits (stats/summarize selected-edits)
     :selected-edit-compiled (mapv :compiled selected-edits) :selected-edit-reused (mapv :reused selected-edits)
     :selected-edit-excludes [:json-indexing :lean-elaboration :kernel-admission :ir-export]
     :eager-compilation (dissoc eager :value) :eager-blocks (count (:blocks (:value eager)))}))

(defn -main [& args]
  (let [sizes (if (seq args) (mapv #(Long/parseLong %) args) [100 1000 10000])
        paths ["src/prototype/module_bench.clj" "src/prototype/import_ir.clj"
               "src/prototype/lazy_runtime.clj" "src/prototype/block_compile.clj"
               "src/prototype/mutable.clj" "src/prototype/machine.cljc"
               "src/prototype/bench.clj" "src/prototype/leaf_compile.clj" "src/prototype/compact_bench.clj"]
        hashes #(into {} (map (fn [p] [p (provenance/sha256 p)]) paths))
        before (hashes) results (mapv #(one-case % 11) sizes)]
    (when-not (= before (hashes)) (throw (ex-info "Sources changed during module benchmark" {})))
    (println (json/write-str {:java-version (System/getProperty "java.version")
                             :java-vendor (System/getProperty "java.vendor")
                             :java-vm-version (System/getProperty "java.vm.version")
                             :source-sha256 before :cases results
                             :limitations ["Synthetic modules; only list/tree tests use actual Lean exports"
                                           "JSON parsing and raw indexing remain eager"
                                           "Restore still scans the complete function table"
                                           "Same JVM and sequential sizes; no cold-process latency ranking"
                                           "In-memory code cache only, without eviction or proof admission"]}))
    (shutdown-agents)))
