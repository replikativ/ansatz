;; DRAFT. Load from experiments/lean-ir. Loading defines functions only.
;; No archive restore, native process, guest invocation, or finalizer runs on load.
(require '[clojure.edn :as edn]
         '[clojure.data.json :as json]
         '[clojure.java.io :as io]
         '[prototype.bootstrap-archive :as full-archive]
         '[prototype.declaration-store :as full-store]
         '[prototype.import-ir :as full-ir]
         '[prototype.runtime-abi :as full-abi]
         '[prototype.machine :as full-machine]
         '[prototype.raw-interop :as full-raw]
         '[prototype.kernel-host :as full-kernel]
         '[prototype.eval-const :as full-eval]
         '[prototype.preparation :as full-preparation]
         '[prototype.module-store :as full-modules]
         '[prototype.module-import :as full-import]
         '[prototype.import-capabilities :as full-regions]
         '[prototype.module-init-capabilities :as full-initializers])

(def full-init-assembly-paths
  {:archive "target/frontend-full-world-archive.edn"
   :archive-sha256 "21acd0e8e735f46232dcb64ea3071600a2b2b0973167d46517e91b0db58b8129"
   :lean-commit "819816b2e0a3bf405af45ae5c7af2491d8f5bee6"
   :index "target/frontend-lean-module-index.edn"
   :index-sha256 "74d833d577923821b982e8a9e872a38b5cad011513eb18870b51417e13397f0e"
   :store "target/parser-module-store"
   :aliases "target/lean-export-aliases.jsonl"
   :descriptor "target/module-data-init.verified.json"
   :descriptor-sha256 "62b168762b4ef900ac783589d4e8b4df4fa4712f120722190fbe4b3cfc0de144"
   :module-data "target/module-data-init-closure.jsonl"
   :initializer-witness "target/module-initializer-symbols.json"
   :initializer-witness-sha256 "c735381b25e946357b44ad125f8bb7b188c3aea2009df930d09b491f8a2eac61"
   :overlays ["target/runtime-compile-shim-source.jsonl"
              "target/kernel-bridge-shim-source.jsonl"
              "target/kernel-bridge-shim-declarations-source.jsonl"
              "target/kernel-control-shim-source.jsonl"
              "target/runtime-compile-shim-files-source.jsonl"
              "target/module-data-transport-header-source.jsonl"
              "fixtures/kernel-encoding.jsonl"]})

(defn full-init-assembly-check [condition message]
  (when-not condition (throw (ex-info message {:scope :full-init-assembly-only}))))
(defn full-init-assembly-target [namespace part]
  ["str" ["str" ["anonymous"] namespace] part])
(defn full-init-assembly-sha256 [path]
  (with-open [input (io/input-stream path)]
    (let [digest (java.security.MessageDigest/getInstance "SHA-256") buffer (byte-array 1048576)]
      (loop []
        (let [n (.read input buffer)]
          (when (pos? n) (.update digest buffer 0 n) (recur))))
      (apply str (map #(format "%02x" (bit-and 255 %)) (.digest digest))))))
(defn full-init-assembly-stage [stage]
  (System/gc)
  (let [runtime (Runtime/getRuntime)]
    (println {:full-init-stage stage :heap-used (- (.totalMemory runtime) (.freeMemory runtime))
              :heap-committed (.totalMemory runtime) :heap-max (.maxMemory runtime)
              :host-gc-requested true})
    (flush)))

(defn restore-full-init-runtime
  "Explicit authenticated bootstrap restore only; no Init data/association."
  ([] (restore-full-init-runtime full-init-assembly-paths))
  ([paths]
   (full-archive/restore (:archive paths)
                         {:expected-sha256 (:archive-sha256 paths)
                          :expected-lean-commit (:lean-commit paths)})))

(defn assemble-full-init-only
  "Use one explicit authenticated bootstrap restore; open the existing verified
   ModuleData source and run only batchAssemble. No finalizeImport, checker
   association, source compiler, initializer replay, or resident adoption.
   Return owned :state/:imports plus borrowed :source, which must stay open while
   any returned world/fork refers to it. On failure preserve exact source/session
   checkpoints for deliberate cleanup; never close a source behind a live branch."
  ([restored] (assemble-full-init-only restored full-init-assembly-paths))
  ([restored paths]
   (full-init-assembly-check (= (:archive-sha256 paths) (:sha256 restored)) "Restore SHA mismatch")
   (full-init-assembly-check (= (:lean-commit paths) (get-in restored [:header :lean-commit])) "Restore commit mismatch")
   (full-init-assembly-check (= (:index-sha256 paths) (get-in restored [:header :declaration-index])) "Archive catalogue mismatch")
   (full-init-assembly-check (empty? (get-in restored [:world :kernel-environments])) "Bootstrap unexpectedly has kernel associations")
   (full-init-assembly-check (empty? (get-in restored [:world :native-imports])) "Bootstrap unexpectedly has native sources")
   (let [started (System/nanoTime)
         _ (full-init-assembly-stage :catalogue)
         index (edn/read-string (slurp (:index paths)))
         _ (full-init-assembly-check (= (:index-sha256 paths) index) "Configured catalogue index mismatch")
         backing (full-store/open-index (:store paths) index)
         catalogue (full-abi/with-export-aliases
                     (reduce full-store/overlay backing
                             (map full-ir/index-bundles (map vector (:overlays paths))))
                     (full-ir/index-bundles [(:aliases paths)]))
         k #(full-init-assembly-target "KernelBridgeShim" %)
         r #(full-init-assembly-target "RuntimeCompileShim" %)
         helpers (merge full-kernel/control-helpers
                        {:root (k "checkedKernelRoot") :empty? (k "checkedEnvironmentIsEmpty")
                         :constant-map (k "checkedConstantMapRoot") :constants (k "checkedConstants")
                         :quot-init? (k "checkedQuotInit") :definition (k "postCheckSafeDefinition")
                         :definition-any (k "postCheckDefinition") :axiom (k "postCheckSafeAxiom")
                         :theorem (k "postCheckTheorem") :opaque (k "postCheckSafeOpaque")
                         :mutual (k "postCheckMutualDefinitions") :error (k "otherError")
                         :compiler-marker (k "postCheckCompilerMarker")})
         policy {:allow-axioms? true :allow-unsafe? true :allow-compiler-markers? true}
         compiler-bindings (fn [functions]
                             {"lean_elab_add_decl" (full-kernel/make-binding helpers policy)
                              "lean_eval_const" (full-eval/make-binding
                                                  (r "exportCompiled")
                                                  {:witness (r "exportEvalConstWitness")
                                                   :catalogue catalogue :trusted-functions functions
                                                   :research-traps? true})})
         _ (full-init-assembly-stage :verified-source)
         loaded (full-modules/open-verified
                  (assoc (:world restored) :sharecommon-profile :immutable-text-v1)
                  (:descriptor paths) (:descriptor-sha256 paths)
                  {:source-path (:module-data paths) :cache-size 1024})
         source (:source loaded)
         active (atom nil)
         assembly-entry (atom nil)]
     (try
       (let [witness-path (:initializer-witness paths)
             _ (full-init-assembly-check (= (:initializer-witness-sha256 paths)
                                           (full-init-assembly-sha256 witness-path))
                                        "Initializer witness SHA mismatch")
             witness (json/read-str (slurp witness-path) :key-fn keyword)
             plans (into {} (keep (fn [manifest]
                                   (when-let [plan (:initializationPlan manifest)] [(:module plan) plan])))
                         (:manifests catalogue))
             init-options (full-initializers/options-from-witness plans witness)
             transport-bindings (merge (full-regions/make-bindings loaded)
                                       (full-initializers/make-bindings init-options))
             provisional (merge (compiler-bindings (get-in restored [:world :functions])) transport-bindings)
             lower (fn [row]
                     (if (contains? provisional (some-> row :ir :extern full-abi/symbol-for))
                       (full-raw/lower provisional row) (full-abi/lower-deferred-catalogue catalogue row)))
             _ (full-init-assembly-stage :refresh-externs)
             functions (reduce-kv
                        (fn [out name function]
                          (if (or (:runtime-extern function) (:deferred-extern function) (:raw-extern function))
                            (let [row ((:read-declaration catalogue) name)]
                              (full-init-assembly-check (get-in row [:ir :extern]) "Missing archived extern backing")
                              (assoc out name (second (lower row)))) out))
                        (get-in restored [:world :functions]) (get-in restored [:world :functions]))
             roots (vec (concat (vals helpers) (vals full-import/helpers)
                                [full-import/bulk-helper full-import/header-finalize-helper
                                 (r "compileImportedFileState") (r "inspectFileHeader")
                                 (r "exportCompiled") (r "exportEvalConstWitness")]))
             functions (full-ir/load-closure catalogue roots lower {:existing-functions functions})
             functions (full-preparation/complete-functions catalogue functions roots lower)
             bindings (merge (compiler-bindings functions) transport-bindings)
             _ (reset! active (full-raw/open-functions functions bindings {:backend :mutable :fuel 20000000}))
             invoke (fn [world target args]
                      (let [called (full-raw/call @active world target args)]
                        (reset! active (:session called)) [(:state called) (:value called)]))
             loaded (update loaded :world assoc :functions functions)
             _ (full-init-assembly-stage :batch-assemble)
             _ (reset! assembly-entry {:loaded loaded :session @active})
             assembly (full-import/assemble loaded invoke {:assembly :bulk})
             _ (full-init-assembly-stage :assembled)
             summary {:scope :full-init-assembly-only :status :assembled-only
                      :module-count (count (:modules loaded))
                      :transport-nodes (get-in loaded [:manifest :inventory :nodes])
                      :local-heap-objects (count (get-in assembly [:world :heap]))
                      :functions (count functions)
                      :available-initializer-symbols (count (:initialized-symbols init-options))
                      :finalizer-executed false :strict-association false
                      :elapsed-ms (/ (- (System/nanoTime) started) 1e6)}]
         (full-init-assembly-check (empty? (get-in assembly [:world :kernel-environments]))
                                  "Assembly unexpectedly acquired checking authority")
         (println summary) (flush)
         (assoc assembly :status :assembled-only :summary summary :session @active
                         :catalogue catalogue :source source :loaded loaded :kernel-helpers helpers
                         :kernel-policy policy))
       (catch Throwable failure
         ;; No automatic retry or freeing a source behind a retained checkpoint.
         (throw (ex-info "Full Init assembly-only probe failed"
                         (assoc (ex-data failure) :scope :full-init-assembly-only :source source
                                                 :source-entry loaded :assembly-entry @assembly-entry)
                         failure)))))))
