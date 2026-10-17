(require '[clojure.data.json :as source-second-json]
         '[prototype.frontend :as source-second-frontend]
         '[prototype.eval-const :as source-second-eval]
         '[prototype.source-import :as source-second-import]
         '[prototype.guest-encoding :as source-second-encoding]
         '[prototype.import-ir :as ir]
         '[prototype.declaration-store :as store]
         '[prototype.runtime-abi :as abi]
         '[prototype.raw-interop :as raw]
         '[prototype.machine :as m])

;; The argument is finalize-owned-source-probe's successful result. Keep it
;; in its compatible world; never merge its numeric Ref IDs into another fork.
;; Requires the two pinned helper artifacts documented in HOSTED_SOURCE_MODULES.
(defn compile-owned-second-probe [base]
  (let [_ (assert (= :ok (:status base)))
        local (ir/index-bundles ["target/runtime-compile-shim-source-module.jsonl"])
        diff (source-second-json/read-str (slurp "target/runtime-compile-shim-source-module.diff.json") :key-fn keyword)
        changed (mapv :name (:changedDeclarations diff))
        _ (assert (= 5 (count changed)))
        _ (assert (not-any? #(get-in base [:world :eval-const-authorizations :declarations %]) changed)
                  "Trusted helper upgrade must never replace admitted user declarations")
        _ (assert (every? #(= "ordinary" (get-in local [:declarations % :runtime :role])) changed))
        ;; Explicit bootstrap upgrade of the five native-producer-verified
        ;; helper rows only. Generic overlay continues rejecting all body drift.
        catalogue (store/overlay (update (:catalogue base) :declarations #(apply dissoc % changed)) local)
        original (get-in base [:world :functions])
        prior-bindings (get-in base [:session :bindings])
        lower (fn [row] (if (contains? prior-bindings (some-> row :ir :extern abi/symbol-for))
                         (raw/lower prior-bindings row) (abi/lower-deferred-catalogue catalogue row)))
        ;; This old A-world had a named trap for the newly implemented exact
        ;; UInt32 comparison. Relower just that extern; retain every unrelated
        ;; user function and all globals, without initializer execution.
        refreshed [["str" ["str" ["anonymous"] "UInt32"] "decLt"]]
        functions (ir/load-closure catalogue (into changed refreshed) lower
                    {:existing-functions (apply dissoc original (into changed refreshed))})
        exporter ["str" ["str" ["anonymous"] "RuntimeCompileShim"] "exportCompiled"]
        witness ["str" ["str" ["anonymous"] "RuntimeCompileShim"] "exportEvalConstWitness"]
        bindings (assoc prior-bindings "lean_eval_const"
                   (source-second-eval/make-binding exporter
                     {:witness witness :catalogue catalogue :trusted-functions functions :research-traps? true
                      :authorize-source-import source-second-import/authorize-imported-row}))
        world (assoc (:world base) :functions functions)
        session (raw/open-functions functions bindings {:backend :mutable :fuel 50000000})
        path "fixtures/hosted/PreludeSecond.lean"
        start (System/nanoTime)
        compiled (source-second-frontend/compile-file session world
                   {:environment (:environment base) :options (:options base)
                    :text (slurp path) :file-name path
                    :module-name (ansatz.kernel.Name/mkStr ansatz.kernel.Name/ANONYMOUS_NAME "PreludeSecond")
                    :roots [(ansatz.kernel.Name/mkStr ansatz.kernel.Name/ANONYMOUS_NAME "second")]}
                   {:encode-name source-second-encoding/encode-name :encode-names source-second-encoding/encode-names
                    :install-options {:catalogue catalogue :research-traps? true :witness witness
                                      :authorize-source-import source-second-import/authorize-imported-row}})]
    (when-not (:success compiled)
      (throw (ex-info "Second source file has diagnostics" {:diagnostics (:diagnostics compiled)})))
    (let [boxed (get (:boxed-entrypoints compiled) ["str" ["anonymous"] "second"])
          run (raw/call (:session compiled) (:world compiled) boxed [m/erased 42])]
      (assert (= 42 (:value run)))
      {:compiled compiled :run run})))
