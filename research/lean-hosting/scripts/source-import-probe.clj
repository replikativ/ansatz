(require '[prototype.module-import :as source-driver-module])
(require '[prototype.source-import :as source-driver])
(require '[prototype.import-ir :as source-driver-ir]
         '[prototype.declaration-store :as source-driver-store]
         '[prototype.runtime-abi :as source-driver-abi]
         '[prototype.raw-interop :as source-driver-raw]
         '[prototype.guest-encoding :as source-driver-encoding]
         '[prototype.machine :as source-driver-m])

;; Load this script to define the experiment, then call it with the successful
;; frontend/compile-file result and source-module/export-classic result for A.
;; Inputs must share compatible immutable world ancestry. This function does not
;; read or mutate a resident REPL's baseline vars, reload namespaces, or run B.
(defn finalize-owned-source-probe [compiled base]
  (let [
        local (source-driver-ir/index-bundles ["target/source-module-import-source.jsonl"])
        catalogue (source-driver-store/overlay (:catalogue base) local)
        bindings (merge (get-in base [:session :bindings]) (source-driver/make-bindings))
        lower (fn [row]
                (if (contains? bindings (some-> row :ir :extern source-driver-abi/symbol-for))
                  (source-driver-raw/lower bindings row)
                  (source-driver-abi/lower-deferred-catalogue catalogue row)))
        ;; All three region extern wrappers must use this source-only session's
        ;; handlers, not the native transport handlers in another world.
        ;; Indexed full catalogues need direct lookup by the pinned declared
        ;; names, avoiding a scan/decode of their hundreds of thousands of rows.
        externs [["str" ["str" ["anonymous"] "Runtime"] "markPersistent"]
                   ["str" ["str" ["str" ["anonymous"] "Lean"] "CompactedRegion"] "read"]
                   ["str" ["str" ["str" ["anonymous"] "Lean"] "CompactedRegion"] "free"]
                   (reduce (fn [p s] (if (integer? s) ["num" p (str s)] ["str" p s]))
                     ["anonymous"] ["_private" "Lean" "Compiler" "InitAttr" 0 "Lean" "runModInitCore"])]
        existing (get-in base [:world :functions])
        functions (source-driver-ir/load-closure catalogue (vec (vals source-driver/helpers)) lower
                    {:existing-functions (apply dissoc existing externs)})
        ;; Relink the externs explicitly even if all callers already existed.
        functions (source-driver-ir/load-closure catalogue externs lower {:existing-functions functions})
        session (atom (source-driver-raw/open-functions functions bindings {:backend :mutable :fuel 50000000}))
        world (assoc (:world base) :functions functions)
        invoke (fn [world target args]
                 (let [r (source-driver-raw/call @session world target args)]
                   (reset! session (:session r)) [(:state r) (:value r)]))
        ;; A genuine factory supplies owned empty Options; keep that owner for B.
        [world factory] (invoke world ["str" ["str" ["anonymous"] "HostedFileProbe"] "preparePrelude"] [source-driver-m/erased])
        pair (first (:fields (source-driver-m/node world factory)))
        options (second (:fields (source-driver-m/node world pair)))
        world (-> world (source-driver-m/retain options 1) (source-driver-m/release factory 1))
        [world module-name] (source-driver-encoding/encode-name world invoke
                             (ansatz.kernel.Name/mkStr ansatz.kernel.Name/ANONYMOUS_NAME "PreludeIdentity"))
        registered (source-driver/register-compiled world invoke compiled module-name)
        assembled (source-driver/assemble (:world registered) invoke
                    ["str" ["anonymous"] "PreludeIdentity"] module-name)
        start (System/nanoTime)
        result (source-driver/finalize assembled invoke options {:kernel-policy {:allow-compiler-markers? true}})
        result (assoc result :world (source-driver-m/release (:world result) module-name 1)
                            :session @session :catalogue catalogue :options options)]
    (assert (= :ok (:status result)))
    result))
