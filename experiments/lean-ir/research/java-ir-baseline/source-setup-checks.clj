(ns java-ir-source-setup-checks
  "Bounded source/Header metadata models only; no VM, native export or authority."
  (:require [clojure.test :refer [deftest is run-tests]] [clojure.data.json :as json]
            [clojure.java.io :as io] [clojure.string :as str]
            [ansatz.research.ir.source-setup :as core]
            [ansatz.research.ir.composite-source-v4 :as v4]
            [ansatz.research.ir.catalogue :as cat] [java-ir-baseline :as j]))
(def module ["str" ["anonymous"] "SetupModel"])
(defn n [text] ["str" module text])
(def action {"action" {"kind" "value" "name" (n "start") "target" (n "start")} "meta" false})
(defn row [name parameters role result]
  {"kind" "decl" "name" (n name) "sourceModule" module "sourceLocal" true
   "runtime" {"role" role "initializer" nil} "dependencies" [] "redirect" nil
   "ir" {"fdecl" {"f" (n name) "xs" parameters "type" result "info" {} "body" ["unreachable"]}}})
(defn model-rows [] [(row "helper" [{"x" {"idx" 1} "ty" "object" "borrow" false}] "ordinary" "object")
                    (row "start" [] "value" "tobject")])
(defn manifest []
  {"kind" "manifest" "schema" "lean-ir-probe/1" "leanVersion" "4.33.1"
   "runtimeProfile" {"target" "x86_64-unknown-linux-gnu" "wordBits" 64}
   "initializationPlan" {"module" module "schema" "lean-init-plan/1" "kind" "initialization-plan"
                         "actions" [action] "imports" []}})
(defn write! [file value] (spit file value) (core/file-sha file))
(defn fixture [change f]
  (let [root (doto (io/file "target/source-setup-checks") .mkdirs)
        dir (.toFile (java.nio.file.Files/createTempDirectory (.toPath root) "model-" (make-array java.nio.file.attribute.FileAttribute 0)))
        source (io/file dir "SetupModel.lean") producer (io/file dir "producer")
        source-sha (write! source "-- Source authentication model, not native producer evidence\n")
        producer-sha (write! producer "producer model")
        initial {:manifest (manifest) :rows (model-rows)}
        {:keys [manifest rows]} (change initial)
        stream (str (str/join "\n" (map json/write-str (cons manifest rows))) "\n")
        stream-sha (write! (io/file dir "local-ir.jsonl") stream)
        receipt {"schema" "native-source-local-ir-export/1" "exit" 0 "stop" nil "stderr-bytes" 0
                 "no-source-main-execution" true "no-checkpoint-restore" true "no-imported-closure-export" true
                 "source-sha256" source-sha "exporter-binary-sha256" producer-sha "lean-commit" core/lean-pin
                 "raw-output-sha256" stream-sha "raw-output-bytes" (count (.getBytes stream "UTF-8"))}
        receipt-sha (write! (io/file dir "export-receipt.json") (json/write-str receipt))
        spec {:module module :row-count 2 :actions [action] :source-file source :producer-file producer
              :pins {"source_sha256" source-sha "producer_sha256" producer-sha "local_ir_sha256" stream-sha
                     "export_receipt_sha256" receipt-sha "base_index_sha256" "model-index"}}]
    (try (f dir spec)
         (finally
           (with-open [paths (java.nio.file.Files/walk (.toPath dir) (make-array java.nio.file.FileVisitOption 0))]
             (doseq [path (reverse (sort-by #(.getNameCount ^java.nio.file.Path %) (iterator-seq (.iterator paths))))]
               (java.nio.file.Files/delete path)))))))
(defmacro with-catalogue [& body]
  `(with-redefs [cat/descriptor (fn [_#] {"source-index-sha256" "model-index"}) cat/lookup (fn [& _#] nil)] ~@body))
(defn setup [catalogue overlay]
  (core/compose! catalogue {"code_index_sha256" "model-index"} [overlay]
                 {:helpers ["SetupModel.helper"] :aliases [] :checked [] :host-symbols []}))
(deftype ModelSource [acceptedCatalogueSnapshot])
(deftype ModelHeader [source originalSha256 name kind declaration metadata])
(defn accessor [value name]
  (.get (doto (.getDeclaredField (class value) name) (.setAccessible true)) value))
(defn header [source row sha]
  (let [[kind declaration] (first (get row "ir"))]
    (ModelHeader. source sha (get row "name") kind (dissoc declaration "body")
                  (select-keys row ["runtime" "dependencies" "redirect" "sourceLocal" "sourceModule"]))))
(defmacro with-model-java [install & body]
  `(with-redefs [j/source-binding (fn [_# profile#] (ModelSource. profile#))
                 j/request-value accessor j/declaration-header header
                 j/register-headers (fn [ctx# headers# specs#] (swap! ~install inc) (assoc ctx# :headers headers# :specs specs#))
                 j/bind-guest-exports (fn [ctx# _#] ctx#) j/host-guest-policy (fn [& _#] :policy)] ~@body))
(deftest common-core-mints-one-source-and-preserves-real-local-action-header
  (with-catalogue
    (fixture identity
      (fn [dir spec]
        (let [catalogue (Object.) overlay (core/authenticate-overlay! catalogue dir spec)
              receipt (setup catalogue overlay) installed (atom 0)]
          (with-model-java installed
            (let [source (core/source-binding! {} receipt)
                  result (core/configure-context receipt catalogue {} source)]
              (is (= [action] (:local-initialization-actions result)))
              (is (= 1 (count (:local-action-headers result))))
              (is (= 2 (count (:headers-by-sha result))))
              (is (every? #(identical? source (accessor % "source")) (vals (:headers-by-sha result))))
              (is (= 1 @installed))
              (is (not (contains? result :bootstrap-layout)))
              (is (thrown? Exception (core/source-binding! {} receipt))))))))))
(deftest unsupported-module-missing-action-and-changed-action-refuse-before-setup
  (doseq [change [#(assoc-in % [:rows 0 "sourceModule"] ["str" ["anonymous"] "Other"])
                  #(assoc-in % [:manifest "initializationPlan" "actions"] [])
                  #(assoc-in % [:manifest "initializationPlan" "actions" 0 "meta"] true)
                  #(assoc-in % [:manifest "initializationPlan" "actions" 0 "action" "target"] (n "wrong"))
                  #(update-in % [:manifest "initializationPlan" "actions"] conj action)
                  #(assoc-in % [:rows 1 "runtime" "role"] "closed")
                  #(assoc-in % [:rows 1 "sourceLocal"] false)]]
    (with-catalogue
      (fixture change (fn [dir spec] (is (thrown? Exception (core/authenticate-overlay! (Object.) dir spec))))))))
(deftest changed-source-shadowed-name-and-overlapping-overlay-refuse
  (with-catalogue
    (fixture identity
      (fn [dir spec]
        (let [catalogue (Object.) overlay (core/authenticate-overlay! catalogue dir spec)]
          (is (thrown? Exception (core/compose! catalogue {"code_index_sha256" "model-index"} [overlay overlay] {})))
          (with-redefs [cat/lookup (fn [& _] {:row :existing})]
            (is (thrown? Exception (core/authenticate-overlay! catalogue dir spec))))
          (spit (:source-file spec) "changed")
          (is (thrown-with-msg? Exception #"digest mismatch" (core/authenticate-overlay! catalogue dir spec))))))))
(deftest forged-receipts-and-same-sha-altered-or-wrong-source-header-refuse-before-program-setup
  (with-catalogue
    (fixture identity
      (fn [dir spec]
        (let [catalogue (Object.) receipt (setup catalogue (core/authenticate-overlay! catalogue dir spec)) installed (atom 0)]
          (with-model-java installed
            (let [source (core/source-binding! {} receipt)
                  entry (core/lookup-entry receipt (n "helper")) sha (:sha256 entry)
                  changed (header source (assoc-in (:row entry) ["ir" "fdecl" "info"] {"changed" true}) sha)
                  wrong-source (header (ModelSource. (core/code-profile receipt)) (:row entry) sha)
                  metadata (header source (assoc (:row entry) "dependencies" [(n "ChangedDependency")]) sha)]
              (doseq [bad [changed wrong-source metadata]]
                (is (thrown? Exception (core/configure-context receipt catalogue {} source {sha bad}))))
              (is (thrown? Exception (core/configure-context (core/code-profile receipt) catalogue {} source)))
              (is (zero? @installed)))))))))
(deftest bad-helper-abi-refuses-before-program-setup
  (with-catalogue
    (fixture #(assoc-in % [:rows 0 "ir" "fdecl" "xs" 0 "borrow"] true)
      (fn [dir spec]
        (let [catalogue (Object.) receipt (setup catalogue (core/authenticate-overlay! catalogue dir spec)) installed (atom 0)]
          (with-model-java installed
            (is (thrown-with-msg? Exception #"helper ABI"
                  (core/configure-context receipt catalogue {} (core/source-binding! {} receipt))))
            (is (zero? @installed))))))))
(deftest fixed-v4-profile-keeps-exact-typed-action-and-accepted-source-pins
  (is (= "5510d2edbe81dd4799d95b2ad5f5a8b12bd2a32e13b6a54e94df6babeb1a6ba1" (get v4/module-pins "local_ir_sha256")))
  (is (= [{"action" {"kind" "value" "name" v4/value-name "target" v4/value-name} "meta" false}] v4/actions))
  (is (= 8 (count v4/helpers))))
(defn check! [] (run-tests 'java-ir-source-setup-checks))
