;; Definitions only. Workdir experiments/lean-ir. Draft: candidate SHA supplied
;; explicitly after the fresh native build; there is deliberately no default.
(require '[clojure.java.io :as snl-io]
         '[prototype.import-ir :as snl-ir]
         '[prototype.declaration-store :as snl-store]
         '[prototype.runtime-abi :as snl-abi]
         '[prototype.raw-interop :as snl-raw]
         '[prototype.eval-const :as snl-eval]
         '[prototype.preparation :as snl-preparation])

(def shared-names-linear-target
  ["str" ["str" ["anonymous"] "RuntimeCompileShim"] "exportEvalConstWitnessIRSharedNamesLinear"])

(defn- snl-pinned [path expected]
  (when-not (and (string? expected) (re-matches #"[0-9a-f]{64}" expected))
    (throw (ex-info "Explicit authenticated shared-linear artifact SHA required" {})))
  (let [bytes (java.nio.file.Files/readAllBytes (.toPath (snl-io/file path)))
        actual (.formatHex (java.util.HexFormat/of)
                 (.digest (java.security.MessageDigest/getInstance "SHA-256") bytes))]
    (when-not (= actual expected)
      (throw (ex-info "Shared-linear witness digest mismatch" {:artifact path})))
    ;; Parse precisely the authenticated bytes; no verify/reopen race.
    (snl-ir/index-bundles [(java.io.StringReader. (String. bytes java.nio.charset.StandardCharsets/UTF_8))])))

(defn prepare-shared-names-linear-witness
  "PREPARATION ONLY. Preserve every old function identity and all guest state.
   Candidate must preserve ALL rows/manifests of the exact pinned shared-name
   artifact (which includes the previously unadopted linear extension). Admit
   missing trusted linear/helper rows only into the catalogue, then link the
   selected actual closure. Complete existing bodies using the canonical edge
   checker; this executes no guest instructions or initializers.
   Caller must capture a NEW evalConst binding against the returned final
   catalogue/functions, preserving all unrelated bindings and ABI; this function
   deliberately does not silently replace a capability or active session."
  [catalogue functions bindings {:keys [artifact expected-sha256] :as options}]
  (when-not (and (= #{:artifact :expected-sha256} (set (keys options))) (string? artifact))
    (throw (ex-info "Supply only explicit shared-linear artifact and expected SHA" {})))
  (let [stage2 (snl-pinned "target/runtime-compile-shim-ir-value-source.jsonl"
                         "731bb72ce9928e0d46d50728c675df21a3d073c6d0f3c1dde96816af89c09cad")
        baseline (snl-pinned "target/runtime-compile-shim-ir-shared-names-source.jsonl"
                           "9864fa3afbf521fa541ef0a00931c34e237ea6538582ddad0746acf5e8e5bed8")
        candidate (snl-pinned artifact expected-sha256)
        manifests (:manifests candidate)
        _ (when-not (and (= 1 (count manifests))
                         (snl-eval/ir-equal? manifests (:manifests baseline)))
            (throw (ex-info "Shared-linear witness changes pinned manifest" {})))
        manifest (first manifests)
        _ (snl-ir/validate-manifest! manifest)
        _ (when-not (and (= "lean-init-plan/1" (get-in manifest [:initializationPlan :schema]))
                         (= ["str" ["anonymous"] "RuntimeCompileShim"]
                            (get-in manifest [:initializationPlan :module]))
                         (false? (get-in manifest [:initializationPlan :moduleSystem]))
                         (= [] (get-in manifest [:initializationPlan :actions])))
            (throw (ex-info "Shared-linear helper must not introduce initialization actions" {})))
        ;; Full old-row comparison includes the 19 earlier linear rows even if
        ;; none were admitted in the actual stage-2/shared preparation.
        _ (doseq [[name row] (:declarations baseline)]
            (when-not (and (contains? (:declarations candidate) name)
                           (snl-eval/ir-equal? row (get-in candidate [:declarations name])))
              (throw (ex-info "Shared-linear candidate changes/removes old declaration" {:name name}))))
        _ (when-not (and (contains? (:declarations candidate) shared-names-linear-target)
                         (not (contains? (:declarations baseline) shared-names-linear-target)))
            (throw (ex-info "Shared-linear candidate must add fresh named helper" {})))
        ;; Stage2 rows stay owned by their existing canonical provenance.
        ;; This delta includes the old unadopted linear rows plus shared/new
        ;; additions, so bodyDepsLinear can link without special name heuristics.
        delta (apply dissoc (:declarations candidate) (keys (:declarations stage2)))
        read-row (fn [source name]
                   (if-let [reader (:read-declaration source)] (reader name)
                     (get-in source [:declarations name])))
        added (reduce-kv
                (fn [out name row]
                  (if (contains? (:declarations catalogue) name)
                    (let [old (read-row catalogue name)]
                      (when-not (snl-eval/ir-equal?
                                  (select-keys old [:kind :ir :dependencies :redirect :runtime])
                                  (select-keys row [:kind :ir :dependencies :redirect :runtime]))
                        (throw (ex-info "Shared-linear preparation rejects existing helper drift"
                                 {:name name :requires-bootstrap-upgrade true})))
                      out)
                    (do
                      (when (contains? functions name)
                        (throw (ex-info "Shared-linear row collides with unbacked executable" {:name name})))
                      (assoc out name row)))) {} delta)
        catalogue (snl-store/overlay catalogue {:manifests manifests :declarations added})
        lower #(if (contains? bindings (some-> % :ir :extern snl-abi/symbol-for))
                 (snl-raw/lower bindings %) (snl-abi/lower-deferred-catalogue catalogue %))
        linked (snl-preparation/complete-functions catalogue functions [shared-names-linear-target] lower)]
    (doseq [[name function] functions]
      (when-not (identical? function (get linked name))
        (throw (ex-info "Shared-linear preparation replaced executable identity" {:name name}))))
    {:catalogue catalogue :functions linked :target shared-names-linear-target
     :artifact-sha256 expected-sha256 :added-declarations (count added)
     :added-functions (- (count linked) (count functions))}))
