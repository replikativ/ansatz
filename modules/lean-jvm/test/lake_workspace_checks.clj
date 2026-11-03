(ns lake-workspace-checks
  "Native-free models over genuine prepared cross-package evidence. Caller maps
   and successful shape checks never issue source or runtime authority."
  (:require [clojure.test :refer [deftest is run-tests]]
            [clojure.java.io :as io] [clojure.data.json :as json]
            [ansatz.lean.jvm.installed :as installed]
            [ansatz.lean.jvm.entry-v3 :as entry]
            [ansatz.lean.jvm.artifact :as artifact]
            [ansatz.lean.jvm.preparation :as preparation])
  (:import [java.util.zip ZipFile]
           [java.nio.file Path]
           [ansatz.lean.jvm ProjectOptions NativeCompilerOptions]))
(def ^:dynamic *artifact* "consumer/resources/lean/lake-workspace.zip")
(defn- contents []
  (with-open [archive (ZipFile. (io/file *artifact*))]
    (into {} (for [entry (enumeration-seq (.entries archive)) :when (not (.isDirectory entry))]
               (with-open [input (.getInputStream archive entry)]
                 [(.getName entry) (.readAllBytes input)])))))
(defn- document [files path] (json/read-str (String. ^bytes (get files path) "UTF-8")))
(defn- refused? [f] (try (f) false (catch clojure.lang.ExceptionInfo _ true)))
(defn- entry-context [inputs doc]
  {:root (get doc "compiledModule") :request (get doc "request") :module-products (get doc "moduleProducts")
   :local-modules (mapv #(get % ":name") (get inputs "modules"))
   :installed-imports (mapv #(get % "module") (get-in inputs ["installedImports" "modules"]))})

(deftest actual-products-and-imported-entries-have-explicit-scope
  (let [files (contents) inputs (document files "provenance/build-inputs.json")
        doc (document files "evidence/entries-0.jsonl") context (entry-context inputs doc)
        workspace (get inputs "workspace") snapshot (get inputs "installedImports")]
    (is (= workspace (installed/validate-workspace! workspace snapshot)))
    (is (= 2 (count (get workspace "packages")) (count (get snapshot "modules"))))
    (is (every? #(= "workspace" (get % "origin")) (get workspace "modules")))
    (is (refused? #(entry/validate-document! context doc)))
    (is (= 3 (count (:entries (entry/validate-document! (assoc context :entry-imports (:installed-imports context)) doc)))))
    (is (= #{"definition"} (set (map #(get % "kind") (get doc "entries")))))
    (is (= "nominal-lake-workspace-v1" (get (document files "manifest.json") "profile")))))

(deftest workspace-provenance-cannot-be-relabelled-or-broadened
  (let [files (contents) inputs (document files "provenance/build-inputs.json")
        workspace (get inputs "workspace") snapshot (get inputs "installedImports")
        reject #(refused? (fn [] (installed/validate-workspace! % snapshot)))]
    (doseq [changed [(dissoc workspace "implementation")
                     (assoc-in workspace ["modules" 0 "origin"] "guessed")
                     (assoc-in workspace ["modules" 0 "imports"] [["str" ["anonymous"] "Other"]])
                     (update workspace "modules" pop)
                     (assoc-in workspace ["packages" 0 "configuration" "../outside"] nil)
                     (update workspace "packages" conj (first (get workspace "packages")))]]
      (is (reject changed)))
    (is (refused? #(installed/validate-workspace! workspace (assoc snapshot "profile" installed/profile))))))

(deftest coherent-file-table-tampering-cannot-change-dependency-products
  (let [files (contents) manifest (document files "manifest.json")
        path "modules/build/Domain.olean" changed (byte-array (get files path))]
    (aset-byte changed 0 (unchecked-byte (bit-xor 1 (aget changed 0))))
    (let [files (assoc files path changed)
          manifest (assoc-in manifest ["files" path] (#'artifact/record changed))]
      (is (refused? #(#'artifact/validate! manifest files))))))

(deftest public-options-select-one-unambiguous-input-policy
  (let [path (Path/of "." (make-array String 0)) compiler (NativeCompilerOptions. path path path)]
    (is (.builtLakeWorkspace (-> (ProjectOptions/builder compiler) (.builtLakeWorkspace) (.function "App.calculate") (.build))))
    (is (false? (.builtLakeWorkspace (-> (ProjectOptions/builder compiler) (.function "App.calculate") (.build)))))
    (is (thrown? IllegalArgumentException (-> (ProjectOptions/builder compiler) (.builtLakeWorkspace) (.sourceRoot "src") (.function "App.calculate") (.build))))
    (is (thrown? IllegalArgumentException (-> (ProjectOptions/builder compiler) (.builtLakeWorkspace) (.installedImport "Std") (.function "App.calculate") (.build))))))

(deftest preparation-cli-selects-workspace-mode-explicitly
  (let [base ["--source" "project" "--sysroot" "sysroot" "--producer-bundle" "bundle"
              "--cache" "cache" "--output" "prepared.zip" "--entry" "App.calculate"]
        options (fn [args] (#'preparation/cli-options (#'preparation/parse-cli args)))]
    (is (false? (.builtLakeWorkspace (options base))))
    (is (.builtLakeWorkspace (options (into base ["--source-mode" "built-lake"]))))
    (is (refused? #(options (into base ["--source-mode" "unknown"]))))))

(defn check!
  ([] (run-tests 'lake-workspace-checks))
  ([file] (binding [*artifact* file] (check!))))
