;; Run from experiments/lean-ir after compiling the parent Java sources:
;; clojure -J-Xmx4g -J-Xss16m -M scripts/resident-prelude-probe.clj [paths.edn]
;; Requires the explicitly prepared, ignored artifacts named below. This is an
;; archived PRELUDE-ONLY acceptance probe, not an ordinary/full-Init bootstrap.
;; No native compiler, reload, artifact generation or fallback is performed.
(require '[clojure.edn :as edn]
         '[prototype.bootstrap-archive :as archive]
         '[prototype.declaration-store :as store]
         '[prototype.import-ir :as ir]
         '[prototype.runtime-abi :as abi]
         '[prototype.machine :as m]
         '[prototype.raw-interop :as raw]
         '[prototype.kernel-host :as kernel]
         '[prototype.imported-kernel :as imported]
         '[prototype.module-import :as imports]
         '[prototype.eval-const :as eval]
         '[prototype.guest-encoding :as encoding]
         '[prototype.resident-frontend :as resident])

(def resident-prelude-paths
  {:archive "target/frontend-full-world-archive.edn"
   :index "target/frontend-lean-module-index.edn"
   :store "target/parser-module-store"
   :aliases "target/lean-export-aliases.jsonl"
   :overlays ["target/runtime-compile-shim-source.jsonl"
              "target/kernel-bridge-shim-source.jsonl"
              "target/kernel-bridge-shim-declarations-source.jsonl"
              "target/runtime-compile-shim-files-source.jsonl"
              "target/module-data-transport-header-source.jsonl"
              "target/hosted-file-probe-source.jsonl"
              "fixtures/kernel-encoding.jsonl"]})
(defn probe-name [part] (ansatz.kernel.Name/mkStr ansatz.kernel.Name/ANONYMOUS_NAME part))
(defn probe-target [namespace part] ["str" ["str" ["anonymous"] namespace] part])
(defn probe-check [condition message]
  (when-not condition (throw (ex-info message {:stage :resident-prelude-probe}))))
(defn probe-stage [stage]
  (let [runtime (Runtime/getRuntime)]
    (println {:resident-probe-stage stage
              :heap-used (- (.totalMemory runtime) (.freeMemory runtime))}))
  (flush))
(defn probe-run [paths]
  (let [started (System/nanoTime)
        _ (probe-stage :restore)
        restored (archive/restore (:archive paths)
                   {:expected-sha256 "21acd0e8e735f46232dcb64ea3071600a2b2b0973167d46517e91b0db58b8129"
                    :expected-lean-commit "819816b2e0a3bf405af45ae5c7af2491d8f5bee6"})
        _ (probe-stage :catalogue)
        backing (store/open-index (:store paths) (edn/read-string (slurp (:index paths))))
        catalogue (abi/with-export-aliases
                    (reduce store/overlay backing (map ir/index-bundles (map vector (:overlays paths))))
                    (ir/index-bundles [(:aliases paths)]))
        k #(probe-target "KernelBridgeShim" %)
        r #(probe-target "RuntimeCompileShim" %)
        helpers {:root (k "checkedKernelRoot") :empty? (k "checkedEnvironmentIsEmpty")
                 :constant-map (k "checkedConstantMapRoot") :constants (k "checkedConstants")
                 :quot-init? (k "checkedQuotInit") :definition (k "postCheckSafeDefinition")
                 :definition-any (k "postCheckDefinition") :axiom (k "postCheckSafeAxiom")
                 :theorem (k "postCheckTheorem") :opaque (k "postCheckSafeOpaque")
                 :mutual (k "postCheckMutualDefinitions") :error (k "otherError")
                 :compiler-marker (k "postCheckCompilerMarker")}
        policy {:allow-compiler-markers? true :allow-unsafe? true}
        make-bindings (fn [functions]
                        {"lean_elab_add_decl" (kernel/make-binding helpers policy)
                         "lean_eval_const" (eval/make-binding (r "exportCompiled")
                                             {:witness (r "exportEvalConstWitness") :catalogue catalogue
                                              :trusted-functions functions :research-traps? true})})
        provisional (make-bindings (:functions (:world restored)))
        lower (fn [row]
                (if (contains? provisional (some-> row :ir :extern abi/symbol-for))
                  (raw/lower provisional row) (abi/lower-deferred-catalogue catalogue row)))
        ;; Refresh actual external rows under current exact ABI validation. No
        ;; initializer or compiled declaration is replayed by this installation.
        functions (reduce-kv
                    (fn [out name function]
                      (if (or (:runtime-extern function) (:deferred-extern function) (:raw-extern function))
                        (let [row ((:read-declaration catalogue) name)]
                          (probe-check (get-in row [:ir :extern]) "Missing archived extern backing")
                          (assoc out name (second (lower row))))
                        (assoc out name function))) {} (get-in restored [:world :functions]))
        prepare (probe-target "HostedFileProbe" "preparePrelude")
        roots (vec (concat (vals helpers) [prepare encoding/names-helper
                                          (r "compileImportedFileState") (r "inspectFileHeader")
                                          (r "exportCompiled") (r "exportEvalConstWitness")]))
        functions (ir/load-closure catalogue roots lower {:existing-functions functions})
        bindings (make-bindings functions)
        active (atom (raw/open-functions functions bindings {:backend :mutable :fuel 100000000}))
        invoke (fn [world target args]
                 (let [called (raw/call @active world target args)]
                   (reset! active (:session called)) [(:state called) (:value called)]))
        _ (probe-stage :prepare)
        [world wrapper] (invoke (assoc (:world restored) :functions functions) prepare [m/erased])
        wrapper-node (m/node world wrapper)
        _ (probe-check (and (= 0 (:tag wrapper-node)) (= 1 (count (:fields wrapper-node))))
                       "preparePrelude did not return IO.ok")
        pair (m/node world (first (:fields wrapper-node)))
        _ (probe-check (and (= 0 (:tag pair)) (= 2 (count (:fields pair)))) "Invalid preparation pair")
        [environment options] (:fields pair)
        world (-> world (m/retain environment 1) (m/retain options 1) (m/release wrapper 1) (assoc :result 0))
        [world constants] (invoke world (:constants helpers) [environment])
        constants-node (m/node world constants)
        _ (probe-check (= :array (:kind constants-node)) "Invalid checked constant array")
        certificate (imported/verify-constants world (:fields constants-node) policy)
        _ (probe-check (= #{"lcAny" "lcErased" "lcVoid"} (set (map str (keys (:constants certificate)))))
                       "Prelude preparation must contain exactly the three compiler markers")
        world (m/release world constants 1)
        [world checked] (kernel/inherit-checked-association {:invoke invoke} world environment helpers)
        world (if checked world
                (imported/associate-checked {:invoke invoke} world environment helpers certificate))
        prepared {:world world :session @active :environment environment :options options :catalogue catalogue}
        _ (probe-stage :adopt)
        base (resident/adopt-prepared prepared
               {:trusted-functions (:functions world) :trusted-bindings (:bindings @active)
                :kernel-helpers helpers :application-extern-symbols #{"ansatz_host_identity"}
                :frontend-configuration {:install-options {:research-traps? true}}})
        _ (probe-stage :source-load)
        identity (resident/load-source base {:path "fixtures/hosted/PreludeIdentity.lean"
                                            :module-name (probe-name "PreludeIdentity")
                                            :roots [(probe-name "answer")] :initialization :defer})
        _ (probe-check (:success identity) "Actual identity source failed")
        ready (resident/initialize (:context identity) (:file identity))
        nat-result (resident/call ready (:file identity) (probe-name "answer") [nil 42]
                     {:arguments [:erased :nat] :result :nat})
        text "Lean ↔ Clojure: λ 🦉"
        text-result (resident/call (:context nat-result) (:file identity) (probe-name "answer") [nil text]
                      {:arguments [:erased :string] :result :string})
        _ (probe-check (= [42 text] [(:value nat-result) (:value text-result)]) "Identity result mismatch")
        _ (probe-stage :second-load)
        second-load (resident/load-source (:context text-result)
                      {:text "prelude\ndef secondAnswer.{u} (α : Sort u) (x : α) : α := x\n"
                       :file-name "ResidentSecond.lean" :module-name (probe-name "ResidentSecond")
                       :roots [(probe-name "secondAnswer")] :initialization :run})
        _ (probe-check (:success second-load) "Second source failed")
        second-call (resident/call (:context second-load) (:file second-load) (probe-name "secondAnswer")
                      [nil 42] {:arguments [:erased :nat] :result :nat})
        _ (probe-stage :diagnostic)
        diagnostic (resident/load-source (:context second-call)
                     {:text "prelude\ndef broken := missingResidentName\n" :file-name "ResidentBad.lean"
                      :module-name (probe-name "ResidentBad") :roots [] :initialization :defer})
        _ (probe-check (and (false? (:success diagnostic)) (seq (:diagnostics diagnostic))
                             (nil? (:file diagnostic))) "Expected diagnostic was not preserved")
        calls (atom 0)
        extern {:signature {:params [{:ty "erased" :borrow false} {:ty "tobject" :borrow false}]
                            :return-type "tobject"}
                :handler (fn [_ world [alpha value]]
                           (swap! calls inc) [(m/release world alpha 1) value])}
        bound (resident/with-externs (:context second-call) {"ansatz_host_identity" extern})
        _ (probe-stage :interop)
        interop (resident/load-source bound {:path "fixtures/hosted/PreludeInterop.lean"
                                            :module-name (probe-name "PreludeInterop")
                                            :roots [(probe-name "interopAnswer")] :initialization :run})
        _ (probe-check (:success interop) "Actual interop source failed")
        interop-nat (resident/call (:context interop) (:file interop) (probe-name "interopAnswer")
                      [nil 42] {:arguments [:erased :nat] :result :nat})
        interop-text (resident/call (:context interop-nat) (:file interop) (probe-name "interopAnswer")
                       [nil text] {:arguments [:erased :string] :result :string})
        _ (probe-check (= [42 text 2] [(:value interop-nat) (:value interop-text) @calls])
                       "Actual host callback results/count mismatch")
        summary {:scope :archived-prelude-only :success true :identity 42 :unicode true
                 :second-load (= 42 (:value second-call)) :expected-diagnostic true :host-calls @calls
                 :checked-compiler-markers (count (:constants certificate))
                 :elapsed-ms (/ (- (System/nanoTime) started) 1e6)}]
    (probe-check (:second-load summary) "Second source call mismatch")
    ;; Keep only final success/diagnostic branches; closing consumes roots in
    ;; each independent branch without releasing owners in another branch.
    (doseq [context [base (:context identity) ready (:context nat-result) (:context text-result)
                     (:context second-load) (:context second-call) bound (:context interop) (:context interop-nat)]]
      (resident/close! context))
    {:summary summary :context (:context interop-text) :diagnostic-context (:context diagnostic)}))

(def resident-prelude-result
  (try
    (let [paths (if-let [path (first *command-line-args*)]
                  (merge resident-prelude-paths (edn/read-string (slurp path))) resident-prelude-paths)
          result (probe-run paths)]
      (println (:summary result)) result)
    (catch Throwable cause
      ;; Preserve precise recovery ownership privately; never print its graph.
      (def resident-prelude-failure cause)
      (println {:resident-probe-failure
                (mapv (fn [error]
                        (let [message (or (.getMessage ^Throwable error) "")]
                          {:class (.getName (class error))
                           :message (subs message 0 (min 500 (count message)))}))
                      (take 8 (take-while some? (iterate ex-cause cause))))})
      (flush)
      (throw (ex-info (subs (or (.getMessage cause) "Resident prelude probe failed")
                            0 (min 1000 (count (or (.getMessage cause) "Resident prelude probe failed"))))
                      {:scope :archived-prelude-only :success false})))))
