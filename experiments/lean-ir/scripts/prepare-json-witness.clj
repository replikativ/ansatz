(require '[prototype.import-ir :as json-witness-ir]
         '[prototype.declaration-store :as json-witness-store]
         '[prototype.runtime-abi :as json-witness-abi]
         '[prototype.raw-interop :as json-witness-raw]
         '[prototype.eval-const :as json-witness-eval]
         '[clojure.string :as json-witness-string])

(def json-witness-target
  ["str" ["str" ["anonymous"] "RuntimeCompileShim"] "exportEvalConstWitnessValue"])

(defn prepare-json-witness
  "Link only new helper declarations from the pinned appended-helper artifact.
   Existing catalogue rows and executables remain authoritative. No guest code
   executes here; the caller separately adopts bindings after transport checks."
  ([catalogue functions bindings] (prepare-json-witness catalogue functions bindings {}))
  ([catalogue functions bindings {:keys [refresh-string-helper?]}]
  (let [candidate (json-witness-ir/index-bundles
                    ["target/runtime-compile-shim-json-value-source.jsonl"])
        _ (doseq [manifest (:manifests candidate)]
            (json-witness-ir/validate-manifest! manifest)
            (assert (empty? (get-in manifest [:initializationPlan :actions]))))
        read-row (fn [catalogue name]
                   (if-let [read-row (:read-declaration catalogue)]
                     (read-row name) (get-in catalogue [:declarations name])))
        refresh (if-not refresh-string-helper? #{}
                  (into #{} (comp (filter (fn [[name _]]
                                           (json-witness-string/includes?
                                             (json-witness-ir/name-label name) "exportEvalConstWitness")))
                                  (keep (fn [[name _]]
                                    (when-let [old (read-row catalogue name)]
                                      (let [new (read-row candidate name)]
                                        (when-not (json-witness-eval/ir-equal? (:ir old) (:ir new))
                                          (assert (json-witness-string/includes?
                                                    (json-witness-ir/name-label name) "exportEvalConstWitness"))
                                          (assert (= "ordinary" (get-in old [:runtime :role])
                                                               (get-in new [:runtime :role])))
                                          name)))))) (:declarations candidate)))
        _ (assert (<= (count refresh) 5))
        added (into {} (remove (fn [[name _]] (contains? (:declarations catalogue) name)))
                    (:declarations candidate))
        _ (assert (contains? added json-witness-target))
        selected (merge added (select-keys (:declarations candidate) refresh))
        local (assoc candidate :declarations selected
                :read-declaration
                (fn [name]
                  (when (contains? selected name)
                    (if-let [read-row (:read-declaration candidate)]
                      (read-row name) (get selected name)))))
        base (assoc catalogue :declarations (apply dissoc (:declarations catalogue) refresh)
               :read-declaration (fn [name] (when-not (contains? refresh name) (read-row catalogue name))))
        catalogue (json-witness-store/overlay base local)
        lower (fn [row]
                (if (contains? bindings (some-> row :ir :extern json-witness-abi/symbol-for))
                  (json-witness-raw/lower bindings row)
                  (json-witness-abi/lower-deferred-catalogue catalogue row)))
        roots (cond-> [json-witness-target]
                refresh-string-helper?
                (conj ["str" ["str" ["anonymous"] "RuntimeCompileShim"] "exportEvalConstWitness"]))
        linked (json-witness-ir/load-closure catalogue roots lower
                 {:existing-functions (apply dissoc functions refresh)})]
    (doseq [[name function] functions :when (not (contains? refresh name))]
      (assert (identical? function (get linked name))))
    {:catalogue catalogue :functions linked :target json-witness-target
     :added-declarations (count added)
     :refreshed-bootstrap-declarations refresh
     :added-functions (- (count linked) (count functions))})))
