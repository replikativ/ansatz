(require '[clojure.java.io :as shared-names-witness-io]
         '[prototype.import-ir :as shared-names-witness-ir]
         '[prototype.declaration-store :as shared-names-witness-store]
         '[prototype.runtime-abi :as shared-names-witness-abi]
         '[prototype.raw-interop :as shared-names-witness-raw]
         '[prototype.eval-const :as shared-names-witness-eval])

(def shared-names-witness-target
  ["str" ["str" ["anonymous"] "RuntimeCompileShim"] "exportEvalConstWitnessIRSharedNames"])
(def shared-names-witness-artifact "target/runtime-compile-shim-ir-shared-names-source.jsonl")
(def shared-names-witness-artifact-sha256
  "9864fa3afbf521fa541ef0a00931c34e237ea6538582ddad0746acf5e8e5bed8")

(def shared-names-witness-baseline-artifact "target/runtime-compile-shim-ir-linear-source.jsonl")
(def shared-names-witness-baseline-sha256
  "a78a10859db267efa952f12b2635c6cdc3dfa32ce713f98f04f6a8ea6e2f9e98")

(defn- shared-names-witness-pinned-catalogue [path expected]
  ;; Decode exactly the bytes whose digest was checked, rather than reopening a
  ;; mutable path between verification and indexing.
  (let [bytes (java.nio.file.Files/readAllBytes
                (.toPath (shared-names-witness-io/file path)))
        actual (.formatHex (java.util.HexFormat/of)
                 (.digest (java.security.MessageDigest/getInstance "SHA-256") bytes))]
    (when-not (= expected actual)
      (throw (ex-info "Shared-names typed witness artifact digest mismatch"
               {:artifact path :expected expected :actual actual})))
    (shared-names-witness-ir/index-bundles
      [(java.io.StringReader. (String. bytes java.nio.charset.StandardCharsets/UTF_8))])))

(defn prepare-shared-names-witness
  "Add the pinned shared-names typed-witness helper closure without executing guest code.
   Prove the new additions against the pinned linear-extension artifact independently of
   the global catalogue: unrelated main/string-helper rows are never inspected.
   Drift of an already present new row requires a separate upgrade. Never replaces existing
   declarations, functions, globals, bindings or initializer completion state.
   Only one invocation-local immutable moduleNames projection changes; selected
   declarations, row order, dependency collector and source/ABI evidence remain
   unchanged. No cache, new lookup authority or cross-invocation state is added."
  [catalogue functions bindings]
  (let [baseline (shared-names-witness-pinned-catalogue shared-names-witness-baseline-artifact shared-names-witness-baseline-sha256)
        stage2 (shared-names-witness-pinned-catalogue
                 "target/runtime-compile-shim-ir-value-source.jsonl"
                 "731bb72ce9928e0d46d50728c675df21a3d073c6d0f3c1dde96816af89c09cad")
        linear-only (set (remove #(contains? (:declarations stage2) %)
                                 (keys (:declarations baseline))))
        _ (when-not (= 19 (count linear-only))
            (throw (ex-info "Pinned linear extension must contain exactly 19 declarations" {})))
        candidate (shared-names-witness-pinned-catalogue shared-names-witness-artifact shared-names-witness-artifact-sha256)
        manifests (:manifests candidate)
        _ (when-not (= 1 (count manifests))
            (throw (ex-info "Expected one shared-names typed witness manifest" {})))
        manifest (first manifests)
        _ (when-not (= 491 (count (:declarations baseline)))
            (throw (ex-info "Pinned shared-names witness baseline must contain 492 rows" {})))
        _ (shared-names-witness-ir/validate-manifest! manifest)
        _ (when-not (and (= "lean-init-plan/1" (get-in manifest [:initializationPlan :schema]))
                         (= ["str" ["anonymous"] "RuntimeCompileShim"]
                            (get-in manifest [:initializationPlan :module]))
                         (false? (get-in manifest [:initializationPlan :moduleSystem]))
                         (= [] (get-in manifest [:initializationPlan :actions]))
                         (shared-names-witness-eval/ir-equal? manifests (:manifests baseline)))
            (throw (ex-info "Shared-names typed witness requires the pinned unchanged helper manifest and no initialization actions" {})))
        ;; Check EVERY old row against the exact pinned baseline, never against
        ;; unrelated or conflicting global catalogue entries such as `main`.
        _ (doseq [[name old] (:declarations baseline)]
            (when-not (and (contains? (:declarations candidate) name)
                           (shared-names-witness-eval/ir-equal? old (get-in candidate [:declarations name])))
              (throw (ex-info "Shared-names typed witness changes or removes a pinned linear-extension declaration" {:name name}))))
        additions (apply dissoc (:declarations candidate) (keys (:declarations baseline)))
        _ (when-not (and (= 6 (count additions)) (contains? additions shared-names-witness-target))
            (throw (ex-info "Pinned shared-names typed witness extension must contain exactly six new declarations" {})))
        ;; Prove this helper can load into the actual stage-2 catalogue without
        ;; admitting any of the unadopted linear extension's declarations.
        _ (loop [pending [shared-names-witness-target] seen #{}]
            (when-let [name (peek pending)]
              (when (contains? linear-only name)
                (throw (ex-info "Shared-names helper depends on unadopted linear extension" {:name name})))
              (if (contains? seen name)
                (recur (pop pending) seen)
                (recur (into (pop pending) (get-in candidate [:declarations name :dependencies]))
                       (conj seen name)))))
        read-row (fn [source name]
                   (if-let [reader (:read-declaration source)] (reader name)
                     (get-in source [:declarations name])))
        added
        (reduce-kv
          (fn [out name row]
            (if (contains? (:declarations catalogue) name)
              (let [old (read-row catalogue name)]
                (when-not (shared-names-witness-eval/ir-equal?
                            (select-keys old [:kind :ir :dependencies :redirect :runtime])
                            (select-keys row [:kind :ir :dependencies :redirect :runtime]))
                  (throw (ex-info "Additive shared-names typed witness preparation rejects existing helper drift"
                           {:name name :requires-bootstrap-upgrade true})))
                out)
              (do
                (when (contains? functions name)
                  (throw (ex-info "Shared-names typed witness declaration collides with unbacked existing code" {:name name})))
                (assoc out name row)))) {} additions)
        _ (when-not (contains? (:declarations candidate) shared-names-witness-target)
            (throw (ex-info "Pinned shared-names typed witness target is missing" {})))
        local {:manifests manifests :declarations added}
        catalogue (shared-names-witness-store/overlay catalogue local)
        lower (fn [row]
                (if (contains? bindings (some-> row :ir :extern shared-names-witness-abi/symbol-for))
                  (shared-names-witness-raw/lower bindings row)
                  (shared-names-witness-abi/lower-deferred-catalogue catalogue row)))
        linked (shared-names-witness-ir/load-closure catalogue [shared-names-witness-target] lower
                 {:existing-functions functions})]
    (doseq [[name function] functions]
      (when-not (identical? function (get linked name))
        (throw (ex-info "Shared-names typed witness preparation replaced an existing function" {:name name}))))
    {:catalogue catalogue :functions linked :target shared-names-witness-target
     :artifact-sha256 shared-names-witness-artifact-sha256
     :added-declarations (count added) :added-functions (- (count linked) (count functions))}))
