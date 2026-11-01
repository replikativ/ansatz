(require '[cheshire.core :as json])
(load-file "src/prototype/source_graph_plan.clj")
(let [evidence (json/parse-string (slurp (first *command-line-args*)) true)
      native (mapv #(hash-map :module % :const-names [] :extra-names []) (:nativePrefix evidence))
      sources (:sourceModules evidence)
      versions (into {} (map #(vector (:module %) (Object.)) sources))
      ref-for (fn [m] {:module m :version (get versions m)})
      nodes (mapv (fn [source]
                    {:module (:module source) :version (get versions (:module source))
                     :dependencies (mapv #(ref-for (:module %)) (drop 2 (:imports source)))
                     :const-names (:constantNames source) :extra-names (:extraConstantNames source)}) sources)
      limits {:max-modules 1024 :max-roots 16 :max-edges 64 :max-depth 16 :max-names 1000000
              :max-name-nodes 128 :max-name-chars 4096 :max-total-name-chars 67108864}
      plan (prototype.source-graph-plan/plan native nodes [(ref-for (:module (last sources)))] limits)]
  (assert (= (:module-order plan) (mapv :module (:modules evidence))))
  (assert (= 3 (get-in plan [:counts :selected-source-modules])))
  (doseq [node nodes name (concat (:const-names node) (:extra-names node))]
    (assert (= (get (:module-indices plan) (:module node))
               (:module-index (get (:name-attribution plan) name)))))
  (println (json/generate-string
             {:schema "ansatz-source-graph-g0-native-order-comparison/1"
              :module-count (count (:module-order plan))
              :source-count 3
              :native-name-inventory-omitted true
              :scope "Actual G0 ordering/source attribution; native collisions and all final indices separately compared by native oracle."})))
