(require '[clojure.java.io :as linear-ir-witness-io]
         '[prototype.import-ir :as linear-ir-witness-ir]
         '[prototype.declaration-store :as linear-ir-witness-store]
         '[prototype.runtime-abi :as linear-ir-witness-abi]
         '[prototype.raw-interop :as linear-ir-witness-raw]
         '[prototype.eval-const :as linear-ir-witness-eval])

(def linear-ir-witness-target
  ["str" ["str" ["anonymous"] "RuntimeCompileShim"] "exportEvalConstWitnessIRLinear"])
(def linear-ir-witness-artifact "target/runtime-compile-shim-ir-linear-source.jsonl")
(def linear-ir-witness-artifact-sha256
  "a78a10859db267efa952f12b2635c6cdc3dfa32ce713f98f04f6a8ea6e2f9e98")

(def linear-ir-witness-baseline-artifact "target/runtime-compile-shim-ir-value-source.jsonl")
(def linear-ir-witness-baseline-sha256
  "731bb72ce9928e0d46d50728c675df21a3d073c6d0f3c1dde96816af89c09cad")

(defn- linear-ir-witness-pinned-catalogue [path expected]
  ;; Decode exactly the bytes whose digest was checked, rather than reopening a
  ;; mutable path between verification and indexing.
  (let [bytes (java.nio.file.Files/readAllBytes
                (.toPath (linear-ir-witness-io/file path)))
        actual (.formatHex (java.util.HexFormat/of)
                 (.digest (java.security.MessageDigest/getInstance "SHA-256") bytes))]
    (when-not (= expected actual)
      (throw (ex-info "Linear typed witness artifact digest mismatch"
               {:artifact path :expected expected :actual actual})))
    (linear-ir-witness-ir/index-bundles
      [(java.io.StringReader. (String. bytes java.nio.charset.StandardCharsets/UTF_8))])))

(defn prepare-linear-ir-witness
  "Add the pinned linear typed-witness helper closure without executing guest code.
   Prove the nineteen additions against the pinned stage-2 artifact independently of
   the global catalogue: unrelated main/string-helper rows are never inspected.
   Drift of an already present new row requires a separate upgrade. Never replaces existing
   declarations, functions, globals, bindings or initializer completion state."
  [catalogue functions bindings]
  (let [baseline (linear-ir-witness-pinned-catalogue linear-ir-witness-baseline-artifact linear-ir-witness-baseline-sha256)
        candidate (linear-ir-witness-pinned-catalogue linear-ir-witness-artifact linear-ir-witness-artifact-sha256)
        manifests (:manifests candidate)
        _ (when-not (= 1 (count manifests))
            (throw (ex-info "Expected one linear typed witness manifest" {})))
        manifest (first manifests)
        _ (when-not (= 472 (count (:declarations baseline)))
            (throw (ex-info "Pinned linear witness baseline must contain 473 rows" {})))
        _ (linear-ir-witness-ir/validate-manifest! manifest)
        _ (when-not (and (= "lean-init-plan/1" (get-in manifest [:initializationPlan :schema]))
                         (= ["str" ["anonymous"] "RuntimeCompileShim"]
                            (get-in manifest [:initializationPlan :module]))
                         (false? (get-in manifest [:initializationPlan :moduleSystem]))
                         (= [] (get-in manifest [:initializationPlan :actions]))
                         (linear-ir-witness-eval/ir-equal? manifests (:manifests baseline)))
            (throw (ex-info "Linear typed witness requires the pinned unchanged helper manifest and no initialization actions" {})))
        ;; Check EVERY old row against the exact pinned baseline, never against
        ;; unrelated or conflicting global catalogue entries such as `main`.
        _ (doseq [[name old] (:declarations baseline)]
            (when-not (and (contains? (:declarations candidate) name)
                           (linear-ir-witness-eval/ir-equal? old (get-in candidate [:declarations name])))
              (throw (ex-info "Linear typed witness changes or removes a pinned stage-2 declaration" {:name name}))))
        additions (apply dissoc (:declarations candidate) (keys (:declarations baseline)))
        _ (when-not (and (= 19 (count additions)) (contains? additions linear-ir-witness-target))
            (throw (ex-info "Pinned linear typed witness extension must contain exactly nineteen new declarations" {})))
        read-row (fn [source name]
                   (if-let [reader (:read-declaration source)] (reader name)
                     (get-in source [:declarations name])))
        added
        (reduce-kv
          (fn [out name row]
            (if (contains? (:declarations catalogue) name)
              (let [old (read-row catalogue name)]
                (when-not (linear-ir-witness-eval/ir-equal?
                            (select-keys old [:kind :ir :dependencies :redirect :runtime])
                            (select-keys row [:kind :ir :dependencies :redirect :runtime]))
                  (throw (ex-info "Additive linear typed witness preparation rejects existing helper drift"
                           {:name name :requires-bootstrap-upgrade true})))
                out)
              (do
                (when (contains? functions name)
                  (throw (ex-info "Linear typed witness declaration collides with unbacked existing code" {:name name})))
                (assoc out name row)))) {} additions)
        _ (when-not (contains? (:declarations candidate) linear-ir-witness-target)
            (throw (ex-info "Pinned linear typed witness target is missing" {})))
        local {:manifests manifests :declarations added}
        catalogue (linear-ir-witness-store/overlay catalogue local)
        lower (fn [row]
                (if (contains? bindings (some-> row :ir :extern linear-ir-witness-abi/symbol-for))
                  (linear-ir-witness-raw/lower bindings row)
                  (linear-ir-witness-abi/lower-deferred-catalogue catalogue row)))
        linked (linear-ir-witness-ir/load-closure catalogue [linear-ir-witness-target] lower
                 {:existing-functions functions})]
    (doseq [[name function] functions]
      (when-not (identical? function (get linked name))
        (throw (ex-info "Linear typed witness preparation replaced an existing function" {:name name}))))
    {:catalogue catalogue :functions linked :target linear-ir-witness-target
     :artifact-sha256 linear-ir-witness-artifact-sha256
     :added-declarations (count added) :added-functions (- (count linked) (count functions))}))
