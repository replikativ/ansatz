(ns ansatz.research.ir.composite-source-v4
  "Fixed KernelBridgeShim + JavaModuleImport source composition. No bootstrap,
   runtime-image admission, startup completion, finalizer or kernel authority."
  (:require [clojure.java.io :as io] [ansatz.research.ir.source-setup :as core]))
(def index-sha "74d833d577923821b982e8a9e872a38b5cad011513eb18870b51417e13397f0e")
(def producer-sha "0b0344058631b8c3dc18a8a1a600f8100611eaf49c3b4ee5ad18a121651e736e")
(def shim-pins
  {"source_sha256" "8d4fa0f2c8cd8b38ae1637945521a584c2f90de0a3820a1ef8b812d993f7ec03"
   "local_ir_sha256" "93a58e710315bb140f3799695aeeaaa687f6fd9cca1f3acc1f06660059de8a0b"
   "export_receipt_sha256" "2dde8b9c4a1c3fc44e902fe5d687e5c371018d2d23fdee572d22d1c87e21b381"
   "producer_sha256" producer-sha "lean_commit" core/lean-pin "base_index_sha256" index-sha})
(def module-pins
  {"source_sha256" "a93f432f8efd32d2fdd9ea42677683542572f3b100efef938df7a57a46ba26aa"
   "local_ir_sha256" "5510d2edbe81dd4799d95b2ad5f5a8b12bd2a32e13b6a54e94df6babeb1a6ba1"
   "export_receipt_sha256" "e50c295b025a8e0c4271e6367a6bdcc96aaf7758bd690b1361a288e29cc9fca6"
   "producer_sha256" producer-sha "lean_commit" core/lean-pin "base_index_sha256" index-sha})
(def value-name ["str" ["str" ["str" ["anonymous"] "JavaModuleImport"] "finalize"] "_boxed_const_1"])
(def value-sha "4f9e45cb51441d02006a0a8404f9feb1d13ecffad196cc95d1642d81ed44f66d")
(def actions [{"action" {"kind" "value" "name" value-name "target" value-name} "meta" false}])
(def helpers ["KernelBridgeShim.postCheckSafeAxiom._boxed" "KernelBridgeShim.postCheckTheorem._boxed"
              "KernelBridgeShim.postCheckSafeDefinition._boxed" "KernelBridgeShim.checkedKernelRoot._boxed"
              "KernelBridgeShim.checkedConstantMapRoot._boxed" "KernelBridgeShim.checkedQuotInit._boxed"
              "KernelBridgeShim.checkedEnvironmentIsEmpty._boxed" "KernelBridgeShim.checkedConstants._boxed"])
(defn authenticate!
  "Authenticate both fixed exports and issue a code receipt. Paths refer to the
   actual accepted producer/source files; no export or runtime execution occurs."
  [catalogue captured-source {:keys [shim-directory module-directory shim-source module-source producer-file original13]}]
  (let [shim (core/authenticate-overlay! catalogue shim-directory
               {:source-file shim-source :producer-file producer-file :module ["str" ["anonymous"] "KernelBridgeShim"]
                :row-count 252 :pins shim-pins :actions []})
        module (core/authenticate-overlay! catalogue module-directory
                 {:source-file module-source :producer-file producer-file :module ["str" ["anonymous"] "JavaModuleImport"]
                  :row-count 28 :pins module-pins :actions actions})
        aliases (core/checked-json (io/file shim-directory "required-guest-exports.json")
                  "7c32ed7a16265b43d6cef8de549cc3550d1de39c53a0047be650b2509bdb20f4" 65536)
        originals (core/checked-json original13 "ac2427476c6bfd38c30715dc32cc2bbeaf99f4253766259a44f063437f2ebdb8" (* 2 1024 1024))
        original-map (into {} (map (fn [entry] [(get entry "label") entry])) originals)
        _ (core/require! (and (= 3 (count aliases)) (= 13 (count originals))) "Fixed source setup inventory differs")
        setup {:evidence-pins {"original13_sha256" "ac2427476c6bfd38c30715dc32cc2bbeaf99f4253766259a44f063437f2ebdb8"
                               "required_guest_exports_sha256" "7c32ed7a16265b43d6cef8de549cc3550d1de39c53a0047be650b2509bdb20f4"}
               :helpers helpers :aliases aliases
               :checked (mapv (fn [label]
                                (let [entry (get original-map label)]
                                  {"name" (get-in entry ["row" "name"]) "sha256" (get entry "sha256")}))
                              ["Lean.Kernel.Environment.addDeclCore" "_private.Lean.Environment.0.Lean.Environment.addDeclCheck"])
               :host-symbols ["lean_add_decl" "lean_elab_add_decl"]}
        receipt (core/compose! catalogue captured-source [shim module] setup)
        action (core/lookup-entry receipt value-name)]
    (core/require! (and (= value-sha (:sha256 action))
                        (= [] (get-in action [:row "dependencies"]))
                        (= [] (get-in action [:row "ir" "fdecl" "xs"]))
                        (= "tobject" (get-in action [:row "ir" "fdecl" "type"]))
                        (= {"initializer" nil "role" "value"} (get-in action [:row "runtime"]))
                        (= actions (get (core/code-profile receipt) "local_initialization_actions")))
                   "Actual ordered local value action differs")
    receipt))
(def source-binding! core/source-binding!)
(def code-profile core/code-profile)
(def configure-context core/configure-context)
(def lookup-entry core/lookup-entry)
(def guard-source! core/guard-source!)
(def configuration-callback core/configuration-callback)
