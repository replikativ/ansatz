(ns prototype.source-module-test
  (:require [clojure.test :refer [deftest is]]
            [clojure.data.json :as json]
            [prototype.source-module :as source]
            [prototype.machine :as m]
            [prototype.runtime-prim :as prim]
            [prototype.runtime-abi :as abi]
            [prototype.import-ir :as ir]
            [prototype.kernel-bridge-test :as guest]
            [prototype.runtime-abi-test :as alias]))

(def module-name ["str" ["anonymous"] "SourceA"])
(def metadata
  {:schema "lean-source-module/1" :producer "SourceModuleExport.exportClassic"
   :leanVersion "4.33.1" :leanCommit (get prim/pinned-build "lean_get_githash")
   :runtimeProfile {:target "x86_64-unknown-linux-gnu" :wordBits 64}
   :module module-name :moduleSystem false :level "private"
   :imports [{:module ["str" ["anonymous"] "Init"] :importAll false :isExported true :isMeta false}
             {:module ["str" ["anonymous"] "Init"] :importAll false :isExported true :isMeta true}]
   :constantNames [["str" ["anonymous"] "answer"]] :constantCount 1
   :extraConstantNames [["str" ["anonymous"] "answer._boxed"]]
   :extensions [{:name ["str" ["anonymous"] "irExtension"] :entryCount 1}]
   :origin "owned-guest-module-data" :initializersExecuted false :environmentSerialized false})

(defn fixture []
  (let [[world env] (m/resource (m/world {}) "compiled-env")
        [world name] (guest/guest-name world "SourceA")]
    {:world world :environment env :name name}))

(defn data-value [world]
  (let [[world init1] (guest/guest-name world "Init")
        [world import1] (guest/ctor world 0 [init1] 3)
        world (guest/scalar! world import1 1 "uint8" 1)
        [world init2] (guest/guest-name world "Init")
        [world import2] (guest/ctor world 0 [init2] 3)
        world (-> world (guest/scalar! import2 1 "uint8" 1) (guest/scalar! import2 2 "uint8" 1))
        [world imports] (m/allocate world :array 246 [import1 import2])
        [world answer] (guest/guest-name world "answer")
        [world names] (m/allocate world :array 246 [answer])
        [world constant] (m/resource world "dummy-constant-info")
        [world constants] (m/allocate world :array 246 [constant])
        [world extra] (guest/guest-name world "answer._boxed")
        [world extras] (m/allocate world :array 246 [extra])
        [world ext-name] (guest/guest-name world "irExtension")
        [world ext-item] (m/resource world "opaque-extension-entry")
        [world ext-items] (m/allocate world :array 246 [ext-item])
        [world ext] (m/allocate world :ctor 0 [ext-name ext-items])
        [world entries] (m/allocate world :array 246 [ext])]
    (guest/ctor world 0 [imports names constants extras entries] 1)))

(defn invoke-model [calls transform & {:keys [io-error?]}]
  ;; This checks the owned typed boundary only. The Lean oracle executes actual
  ;; mkModuleData callbacks and native A→B imports independently.
  (fn [world target [environment name token :as args]]
    (swap! calls conj [target args])
    (let [world (-> world (m/release environment 1) (m/release name 1))]
      (if io-error?
        (let [[world error] (m/resource world "export-error")]
          (m/allocate world :ctor 1 [error]))
        (let [[world data] (data-value world)
              [world pair] (m/allocate world :ctor 0 [data (json/write-str (transform metadata))])]
          (m/allocate world :ctor 0 [pair]))))))

(deftest owned-data-and-actual-import-metadata-without-native-provenance
  (let [{:keys [world environment name]} (fixture) before world calls (atom [])
        result (source/export-classic world (invoke-model calls identity) environment name)
        world (:world result) data (:module-data result)
        released (m/release world data 1)]
    (is (= :ok (:status result)))
    (is (= metadata (:metadata result)))
    (is (= [[source/export-helper [environment name m/erased]]] @calls))
    (is (= [1 1 1] (mapv #(:rc (m/node world %)) [environment name data])))
    (is (nil? (:native-source-id (m/node world data))))
    (is (nil? (:native-imports world)))
    (is (nil? (:initialized-modules world)))
    (is (nil? (:eval-const-authorizations world)))
    (is (= (:heap before) (:heap released)))
    (is (not= (:heap before) (:heap world)))))

(deftest invalid-metadata-retains-diagnostic-owned-result
  (doseq [change [#(assoc % :module ["str" ["anonymous"] "Wrong"])
                  #(assoc % :moduleSystem true) #(assoc % :leanCommit "other")
                  #(assoc % :initializersExecuted true) #(assoc % :constantCount 2)
                  #(assoc-in % [:imports 1 :isMeta] false)
                  #(assoc-in % [:extensions 0 :entryCount] 2)]]
    (let [{:keys [world environment name]} (fixture) calls (atom [])
          error (try (source/export-classic world (invoke-model calls change) environment name)
                     nil (catch clojure.lang.ExceptionInfo e e))
          failed-world (:checkpoint (ex-data error)) result (:io-result (ex-data error))]
      (is (some? error))
      (is (m/ref? result))
      (is (= [1 1] (mapv #(:rc (m/node failed-world %)) [environment name])))
      (is (= (:heap world) (:heap (m/release failed-world result 1)))))))

(deftest io-error-is-owned-and-never-exported-as-success
  (let [{:keys [world environment name]} (fixture)
        result (source/export-classic world (invoke-model (atom []) identity :io-error? true) environment name)]
    (is (= :io-error (:status result)))
    (is (nil? (:module-data result)))
    (is (= (:heap world) (:heap (m/release (:world result) (:io-result result) 1))))))

(deftest exact-ir-export-aliases-use-guest-bodies-and-check-abi
  (doseq [[symbol target] source/ir-export-targets]
    (let [params (if (= symbol "lean_ir_export_entries") [alias/param]
                   [alias/param {:x {:idx 2} :ty "uint8" :borrow false}
                    {:x {:idx 3} :ty "uint8" :borrow false}])
          body (-> alias/target-row (assoc :name target)
                   (assoc-in [:ir :fdecl :f] target) (assoc-in [:ir :fdecl :xs] params))
          ext (-> alias/extern-row
                  (assoc-in [:ir :extern :xs] params)
                  (assoc-in [:ir :extern :ext :entries 0 :standard :fn] symbol))
          catalogue (source/with-ir-export-aliases
                      {:manifests [] :declarations {alias/source-name ext target body}})
          functions (ir/load-closure catalogue [alias/source-name] #(abi/lower-deferred-catalogue catalogue %))
          result (m/run (m/start (m/world functions) alias/source-name
                                (if (= 1 (count params)) [42] [42 2 1])))]
      (is (= 42 (:result result)))
      (is (= target (get-in functions [alias/source-name :export-redirect])))
      (is (thrown-with-msg? Exception #"signature mismatch"
            (abi/lower-deferred-catalogue
              (assoc-in catalogue [:declarations target :ir :fdecl :xs 0 :borrow] true) ext)))
      (is (thrown-with-msg? Exception #"no guest function body"
            (abi/lower-deferred-catalogue (update catalogue :declarations dissoc target) ext))))))
