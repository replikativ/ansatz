(require '[prototype.hosted-file :as file-probe]
         '[prototype.import-ir :as file-probe-ir]
         '[prototype.declaration-store :as file-probe-store]
         '[prototype.runtime-abi :as file-probe-abi]
         '[prototype.raw-interop :as file-probe-raw]
         '[prototype.machine :as file-probe-m])

(defn prepare-hosted-prelude-probe
  "READY has matching :catalogue/:functions/:world/:bindings. Return a fresh
   owned guest Environment and Options for run-file, without changing READY."
  [{:keys [catalogue functions world bindings]}]
  (let [local (file-probe-ir/index-bundles ["target/hosted-file-probe-source.jsonl"])
        catalogue (file-probe-store/overlay catalogue local)
        target ["str" ["str" ["anonymous"] "HostedFileProbe"] "preparePrelude"]
        lower (fn [row] (if (contains? bindings (some-> row :ir :extern file-probe-abi/symbol-for))
                         (file-probe-raw/lower bindings row)
                         (file-probe-abi/lower-deferred-catalogue catalogue row)))
        functions (file-probe-ir/load-closure catalogue [target] lower {:existing-functions functions})
        session (file-probe-raw/open-functions functions bindings {:backend :mutable :fuel 50000000})
        result (file-probe-raw/call session (assoc world :functions functions) target [file-probe-m/erased])
        world (:state result) wrapper (:value result)
        pair (first (:fields (file-probe-m/node world wrapper)))
        [environment options] (:fields (file-probe-m/node world pair))
        world (-> world (file-probe-m/retain environment 1) (file-probe-m/retain options 1)
                  (file-probe-m/release wrapper 1) (assoc :result 0))]
    {:world world :session (:session result) :catalogue catalogue :environment environment :options options}))

(defn run-hosted-file-probe
  "Exercise the real public runner from independent prepared forks. Returns
   prepared contexts and results with their owned guest values; callers release
   or retain these deliberately. This never compiles through a native process."
  [ready]
  (let [name #(ansatz.kernel.Name/mkStr ansatz.kernel.Name/ANONYMOUS_NAME %)
        prepared (prepare-hosted-prelude-probe ready)
        loaded (file-probe/run-file prepared
                 {:module-name (name "PreludeIdentity") :roots [(name "answer")]
                  :path "fixtures/hosted/PreludeIdentity.lean" :initialization :defer
                  :calls [{:name (name "answer") :args [file-probe-m/erased 42]}]}
                 {:install-options {:research-traps? true}})
        diagnostic-prepared (prepare-hosted-prelude-probe ready)
        failed (file-probe/run-file diagnostic-prepared
                 {:module-name (name "HostedDiagnostic") :roots [(name "broken")]
                  :path "fixtures/hosted/HostedDiagnostic.lean" :initialization :defer
                  :calls [{:name (name "broken") :args [file-probe-m/erased 42]}]}
                 {:install-options {:research-traps? true}})]
    (assert (:success loaded))
    (assert (= [42] (mapv :value (:call-results loaded))))
    (assert (false? (:success failed)))
    (assert (= :not-compiled (:initialization-state failed)))
    (assert (empty? (:call-results failed)))
    (assert (nil? (:handle failed)))
    (assert (nil? (get-in failed [:envelope :bundle])))
    (assert (file-probe-m/ref? (:environment failed)))
    (file-probe-m/node (:world failed) (:environment failed))
    (assert (some #(and (= {:column 43 :line 2} (:pos %))
                       (= "Unknown identifier `missingHostedName`" (:data %))) (:diagnostics failed)))
    (assert (not (contains? (get-in failed [:world :functions]) ["str" ["anonymous"] "broken"])))
    {:prepared prepared :loaded loaded :diagnostic-prepared diagnostic-prepared :diagnostic failed}))
