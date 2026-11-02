(ns installed-import-checks
  "Finite installed product and identity contracts; no Lean/compiler processes."
  (:require [clojure.test :refer [deftest is run-tests]] [clojure.java.io :as io]
            [clojure.data.json :as json] [ansatz.lean.jvm.artifact :as artifact]
            [ansatz.lean.jvm.installed :as installed]
            [ansatz.lean.jvm.compiler.local :as local]
            [ansatz.lean.jvm.startup :as startup]
            [ansatz.lean.jvm :as lean])
  (:import [java.nio.file Files Path LinkOption]
           [java.nio.file.attribute FileAttribute]
           [java.io ByteArrayInputStream ByteArrayOutputStream]
           [java.nio.charset StandardCharsets]
           [java.util.zip ZipInputStream ZipOutputStream ZipEntry]
           [ansatz.lean.jvm ProjectOptions]))

(defn module-name [text]
  (reduce (fn [parent part] ["str" parent part]) ["anonymous"] (.split ^String text "\\.")))
(def fixture-name (module-name "Other.Library"))
(defn fixture []
  {"profile" installed/profile
   "modules" [{"module" fixture-name
               "products" (mapv (fn [path index]
                                   (cond-> {"path" path "present" (zero? index)}
                                     (zero? index) (assoc "bytes" 1 "sha256" (apply str (repeat 64 "a")))))
                                 (installed/product-paths fixture-name) (range))}]})
(defn refused? [f] (try (f) false (catch clojure.lang.ExceptionInfo _ true)))

(deftest finite-modules-and-complete-product-identity
  (is (= (fixture) (installed/validate! (fixture))))
  (is (refused? #(installed/declared! [fixture-name fixture-name])))
  (is (refused? #(installed/declared! [(module-name "Init.System.IO")])))
  (is (refused? #(installed/declared! [(module-name "Other/escape")]))))

(deftest graph-permission-is-exact-not-a-prefix-or-extern-grant
  (let [root (module-name "Main") rows [{"sourceModule" fixture-name}]]
    (is (installed/validate-graph! (fixture) [root] [[root fixture-name (module-name "Init")]] rows))
    (is (refused? #(installed/validate-graph! (fixture) [root]
                    [[root (module-name "Other.Library.Child")]] rows)))
    (is (refused? #(installed/validate-graph! (fixture) [root]
                    [[root fixture-name]] [{"sourceModule" (module-name "Other.Unlisted")}])))))

(deftest malformed-and-incomplete-product-provenance-is-refused
  (is (refused? #(installed/validate! (update-in (fixture) ["modules" 0 "products"] pop))))
  (is (refused? #(installed/validate! (assoc-in (fixture) ["modules" 0 "products" 0 "sha256"] "bad"))))
  (is (refused? #(installed/validate! (assoc-in (fixture) ["modules" 0 "products" 1 "path"] "../escape")))))

(deftest installed-permission-preserves-builtin-and-anonymous-startup-refusals
  (let [empty-module {"regularModuleEntries" [] "regularIREntries" []
                      "builtinModuleEntries" [] "builtinIREntries" []
                      "effectiveImport" {"irPhases" "all"} "initRuntime" true
                      "regularSequence" [] "phaseDecisions" []}
        named [(module-name "target") (module-name "init")]
        anonymous [(module-name "action") ["anonymous"]]]
    (is (= [] (startup/module-plan empty-module false)))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Builtin initialization unsupported"
          (startup/module-plan (assoc empty-module "builtinModuleEntries" [named]) false)))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Anonymous regular initialization unsupported"
          (startup/module-plan
            (assoc empty-module "regularModuleEntries" [anonymous] "regularSequence" [anonymous]
              "phaseDecisions" [{"ordinal" 0 "pair" anonymous "declarationIRPhases" "all" "selected" true}]) false)))))

(deftest public-options-preserve-an-explicit-immutable-finite-list
  (doseq [extra [{} {:installed-imports []}]]
    (is (empty? (.installedImports ^ProjectOptions
                  (lean/project-options (merge {:compiler {:sysroot "." :producer-bundle "." :cache "."}
                                                :entries ["main"]} extra))))))
  (let [options (lean/project-options {:compiler {:sysroot "." :producer-bundle "." :cache "."}
                                      :entries ["main"] :installed-imports ["Other.Library"]})]
    (is (= ["Other.Library"] (vec (.installedImports ^ProjectOptions options)))))
  (is (refused? #(lean/project-options {:compiler {:sysroot "." :producer-bundle "." :cache "."}
                                      :entries ["main"] :installed-imports '("Other.Library")}))))

(defn with-tree [f]
  (let [parent (.toPath (io/file "temp_files"))
        _ (Files/createDirectories parent (make-array FileAttribute 0))
        root (.toAbsolutePath (Files/createTempDirectory parent "installed-contract-" (make-array FileAttribute 0)))]
    (try (f root)
      (finally
        ;; Files.walk does not follow symlinks; delete only this test's own tree.
        (with-open [paths (Files/walk root (make-array java.nio.file.FileVisitOption 0))]
          (doseq [path (reverse (sort-by #(.getNameCount ^Path %) (iterator-seq (.iterator paths))))]
            (Files/deleteIfExists path)))))))

(deftest source-shadowing-is-refused-before-installed-resolution
  (with-tree
    (fn [root]
      (let [source (.resolve root "Other/Library.lean")]
        (is (nil? (#'local/check-installed-shadow! root [fixture-name])))
        (Files/createDirectories (.getParent source) (make-array FileAttribute 0))
        (spit (.toFile source) "def unexpected := 1")
        (is (refused? #(#'local/check-installed-shadow! root [fixture-name])))))))

(deftest installed-product-files-and-directory-ancestors-cannot-be-symlinks
  (with-tree
    (fn [root]
      (let [sysroot (.resolve root "sysroot") real (.resolve root "real")
            product (.resolve sysroot "lib/lean/Other/Library.olean")
            target (.resolve real "Library.olean")]
        (Files/createDirectories (.getParent product) (make-array FileAttribute 0))
        (Files/createDirectories real (make-array FileAttribute 0))
        (spit (.toFile target) "outside the declared module directory")
        (Files/createSymbolicLink product target (make-array FileAttribute 0))
        (is (refused? #(#'local/installed-snapshot! {:sysroot sysroot} [fixture-name])))
        (Files/delete product)
        (Files/delete (.getParent product))
        (Files/createSymbolicLink (.getParent product) real (make-array FileAttribute 0))
        (is (refused? #(#'local/installed-snapshot! {:sysroot sysroot} [fixture-name])))))))

(defn artifact-contents []
  (with-open [input (ZipInputStream. (io/input-stream "consumer/resources/lean/interop.zip") StandardCharsets/UTF_8)]
    (loop [entries []]
      (if-let [entry (.getNextEntry input)]
        (recur (conj entries [(.getName entry) (#'artifact/read-stream! input artifact/max-bytes)])) entries))))
(defn json-bytes [value] (.getBytes (json/write-str value) StandardCharsets/UTF_8))
(defn load-rewritten-artifact [entries transform-inputs transform-manifest]
  ;; Negative mutations of genuine captures are not new native receipts. Keep
  ;; all file references/digests consistent so profile admission is what rejects.
  (let [files (into {} entries)
        manifest (json/read-str (String. ^bytes (get files "manifest.json") StandardCharsets/UTF_8))
        path (get-in manifest ["inputs" "originalBuildInputs" "path"])
        inputs (json/read-str (String. ^bytes (get files path) StandardCharsets/UTF_8))
        data (json-bytes (transform-inputs inputs)) record (#'artifact/record data)
        changed (-> manifest
                    (assoc-in ["files" path] record)
                    (assoc-in ["inputs" "originalBuildInputs"] (assoc record "path" path))
                    transform-manifest)
        manifest-bytes (json-bytes changed)
        output (ByteArrayOutputStream.)]
    (with-open [zip (ZipOutputStream. output StandardCharsets/UTF_8)]
      (doseq [[name bytes] (conj (mapv (fn [[name bytes]] [name (if (= name path) data bytes)])
                                     (remove #(= "manifest.json" (first %)) entries))
                                ["manifest.json" manifest-bytes])]
        (.putNextEntry zip (ZipEntry. name))
        (.write zip ^bytes bytes 0 (alength ^bytes bytes)) (.closeEntry zip)))
    (artifact/load! (ByteArrayInputStream. (.toByteArray output)) (#'artifact/sha manifest-bytes))))

(deftest authenticated-artifact-profiles-cannot-hide-or-invent-installed-provenance
  (let [entries (artifact-contents)]
    ;; The original legacy profile remains loadable without installed metadata.
    (is (not (contains? (:build-inputs (artifact/authenticated-artifact
                                       (load-rewritten-artifact entries identity identity))) "installedImports")))
    (is (refused? #(load-rewritten-artifact entries
                    (fn [inputs] (assoc inputs "installedImports" (fixture))) identity)))
    (is (refused? #(load-rewritten-artifact entries identity
                    (fn [manifest] (assoc manifest "profile" installed/artifact-profile)))))
    (is (refused? #(load-rewritten-artifact entries
                    (fn [inputs] (assoc inputs "profile" installed/preparation-profile))
                    (fn [manifest] (assoc manifest "profile" installed/artifact-profile)))))
    (is (refused? #(load-rewritten-artifact entries
                    (fn [inputs] (assoc inputs "profile" installed/preparation-profile
                                    "installedImports" (assoc-in (fixture) ["modules" 0 "products" 0 "sha256"] "bad")))
                    (fn [manifest] (assoc manifest "profile" installed/artifact-profile)))))))

(deftest actual-byte-and-optional-presence-changes-invalidate-the-snapshot
  (let [parent (.toPath (io/file "temp_files"))
        _ (Files/createDirectories parent (make-array FileAttribute 0))
        root (Files/createTempDirectory parent "installed-contract-" (make-array FileAttribute 0))
        state {:sysroot root}
        olean (.resolve root "lib/lean/Other/Library.olean")
        sidecar (.resolve root "lib/lean/Other/Library.ir")]
    (try
      (Files/createDirectories (.getParent olean) (make-array FileAttribute 0))
      (spit (.toFile olean) "one")
      (let [snapshot (#'local/installed-snapshot! state [fixture-name])]
        (is (nil? (local/verify-installed! state snapshot)))
        (spit (.toFile olean) "two")
        (is (refused? #(local/verify-installed! state snapshot)))
        (spit (.toFile olean) "one")
        (spit (.toFile sidecar) "new optional data")
        (is (refused? #(local/verify-installed! state snapshot)))
        (Files/delete sidecar)
        (Files/delete olean)
        (is (refused? #(local/verify-installed! state snapshot))))
      (finally
        (with-open [paths (Files/walk root (make-array java.nio.file.FileVisitOption 0))]
          (doseq [path (reverse (sort-by #(.getNameCount ^Path %) (iterator-seq (.iterator paths))))]
            (Files/deleteIfExists path)))))))

(defn check! [] (run-tests 'installed-import-checks))
