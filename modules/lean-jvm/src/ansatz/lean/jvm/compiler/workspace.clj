(ns ansatz.lean.jvm.compiler.workspace
  "Preparation of an already built Lake workspace. Inventory is advisory: the
   existing pinned producers authenticate signatures, IR and initialization."
  (:refer-clojure :exclude [run!])
  (:require [ansatz.lean.jvm.compiler.transport :as transport]
            [ansatz.lean.jvm.compiler.local :as local]
            [ansatz.lean.jvm.installed :as installed]
            [clojure.java.io :as io] [clojure.string :as str])
  (:import [java.nio.file Path Files LinkOption OpenOption StandardOpenOption]
           [java.nio.file.attribute FileAttribute]
           [java.nio.charset StandardCharsets] [java.util Locale]))

(def profile "built-lake-workspace/1")
(def ^:private no-links (into-array LinkOption [LinkOption/NOFOLLOW_LINKS]))
(def ^:private attrs (make-array FileAttribute 0))
(def ^:private probe-resource "META-INF/ansatz-lean-jvm/LakeInventory.lean")
(def ^:private implementation-source (#'transport/implementation-source! *file*))
(def ^:private implementation-record (#'transport/source-record! implementation-source))
(defn- need [ok code facts]
  (when-not ok (throw (ex-info "Built Lake workspace preparation refused" (assoc facts :code code)))))
(defn- path! [value]
  (let [path (.normalize (.toAbsolutePath (Path/of (str value) (make-array String 0))))]
    (loop [p path]
      (when p
        (need (not (Files/isSymbolicLink p)) "ModulePathConflict" {:path (str p)})
        (recur (.getParent p))))
    path))
(defn- child! [^Path root relative]
  (need (and (= String (class relative)) (<= 1 (count relative) 4096)) "UnsupportedProjectConfig" {})
  (let [relative (Path/of relative (make-array String 0)) path (path! (.resolve root relative))]
    (need (and (not (.isAbsolute relative)) (.startsWith path root)) "ModulePathConflict" {}) path))
(defn- record! [path maximum] (#'transport/file-record path maximum))
(defn- metadata-file! [path]
  (when (Files/exists ^Path path no-links) (record! path 1048576)))
(defn- configuration-files
  ([root] (configuration-files root nil))
  ([root extra]
   (into {} (map (fn [relative] (let [path (child! root relative)] [path (metadata-file! path)])))
         (distinct (cond-> ["lakefile.lean" "lakefile.toml" "lake-manifest.json" "lean-toolchain"] extra (conj extra))))))
(defn- verify-files! [files]
  (doseq [[path expected] files]
    (need (if expected (= expected (record! path installed/max-product-bytes)) (Files/notExists ^Path path no-links))
          "ArtifactConflict" {:stage :lake-product-mutation})))
(defn- run!
  ([state journal directory label arguments]
   (run! state journal directory label arguments (str (.resolve ^Path (:sysroot state) "lib/lean"))))
  ([state journal directory label arguments search]
   (#'transport/run-process! state journal directory label arguments (#'transport/environment state search))))
(defn- text! [directory receipt]
  (String. ^bytes (#'transport/bytes! (.resolve ^Path directory ^String (get receipt "stdout")) (* 4 1048576))
           StandardCharsets/UTF_8))
(defn- manifest-packages!
  "Check materialized directories before Lake loads its trusted configuration.
   Missing dependencies are rejected here rather than asking Lake to fetch them."
  [root manifest]
  (let [packages (get manifest "packages")
        packages-dir (child! root (get manifest "packagesDir" ".lake/packages"))]
    (need (and (vector? packages) (<= (count packages) 128)
               (= (count packages) (count (set (map #(get % "name") packages))))) "UnsupportedProjectConfig" {:stage :lake-manifest})
    (into [{:name "<root>" :directory root :configuration nil}]
          (map (fn [package]
                 (let [name (get package "name") kind (get package "type")]
                   (need (and (string? name) (<= 1 (count name) 255) (not (#{"." ".."} name))
                              (not-any? #{\/ \\ \u0000} name) (#{"path" "git"} kind))
                         "UnsupportedProjectConfig" {:stage :lake-package})
                   (let [directory (case kind
                                     "path" (path! (.resolve ^Path root ^String (get package "dir")))
                                     "git" (child! packages-dir name))]
                     (need (Files/isDirectory directory no-links) "MissingDependency" {:package name})
                     {:name name :directory directory :kind kind :revision (get package "rev")
                      :configuration (get package "configFile" "lakefile.lean")}))) packages))))
(defn- root-for-product! [path name]
  (let [components (installed/components name)
        root (nth (iterate #(.getParent ^Path %) path) (count components))
        expected (first (installed/product-paths name))]
    (need (and root (= path (.resolve ^Path root expected))) "ModulePathConflict" {:module name}) root))
(defn- module-products! [state rows allowed-roots]
  (need (and (vector? rows) (<= 1 (count rows) installed/max-modules)
             (= (count rows) (count (set (map #(get % "module") rows))))) "BuildResourceLimit" {:stage :lake-modules})
  (let [official (.resolve ^Path (:sysroot state) "lib/lean")
        names (mapv #(get % "module") rows) allowed (set names) total (atom 0)
        folded (mapv #(.toLowerCase ^String (first (installed/product-paths %)) Locale/ROOT) names)]
    (need (= (count names) (count (set folded))) "ModulePathConflict" {:stage :lake-product-case-collision})
    (installed/declared! names)
    (doseq [row rows]
      (need (= #{"module" "olean" "isModule" "imports"} (set (keys row))) "ArtifactConflict" {:stage :lake-module})
      (need (and (boolean? (get row "isModule")) (vector? (get row "imports"))
                 (<= (count (get row "imports")) 4096)
                 (every? #(or (installed/init? %) (contains? allowed %)) (get row "imports")))
            "MissingDependency" {:stage :lake-import-closure}))
    (let [products
          (into {} (map (fn [row]
                          (let [name (get row "module") path (path! (get row "olean")) root (root-for-product! path name)]
                            (need (some #(.startsWith path ^Path %) (conj allowed-roots official))
                                  "ModulePathConflict" {:stage :lake-product-owner :module name})
                            ;; Never silently shadow an installed official module.
                            (when (Files/exists (.resolve official (first (installed/product-paths name))) no-links)
                              (need (= root official) "ModulePathConflict" {:stage :lake-toolchain-shadow :module name}))
                            [name root])) rows))
          files
          (into {} (for [[name root] products relative (installed/product-paths name)
                         :let [path (child! root relative)] :when (Files/exists path no-links)]
                     (let [record (record! path installed/max-product-bytes)]
                       (swap! total + (get record "bytes"))
                       (need (<= @total installed/max-total-bytes) "BuildResourceLimit" {:stage :lake-products})
                       [path record])))
          absent (vec (for [[name root] products relative (installed/product-paths name)
                            :let [path (child! root relative)] :when (Files/notExists path no-links)] path))]
      {:products (into {} (remove #(= official (val %)) products)) :files files :absent absent :names names})))

(defn configure!
  "Configure one fresh source compiler from a built workspace. Returns an empty
   adapter source project importing the original compiled root; no package source
   is rewritten/recompiled and no guest Project or entry authority is issued."
  [compiler source-root root-name]
  (need (= implementation-record (#'transport/source-record! implementation-source)) "ArtifactConflict" {:stage :workspace-implementation})
  (let [state (#'transport/issued compiler) root (path! source-root)
        _ (need (Files/isDirectory root no-links) "UnsupportedProjectConfig" {})
        components (local/module-components root-name)
        _ (doseq [part components]
            (need (not-any? #(or (#{\« \»} %) (Character/isISOControl ^char %)) part)
                  "ModulePathConflict" {:stage :lake-root-name}))
        manifest-file (child! root "lake-manifest.json")
        _ (need (Files/isRegularFile manifest-file no-links) "MissingDependency" {:stage :lake-manifest})
        manifest (#'transport/read-json! manifest-file 1048576)
        packages (manifest-packages! root manifest)
        root-files (configuration-files root)
        _ (need (some? (get root-files (child! root "lean-toolchain"))) "UnsupportedProjectConfig" {:stage :lake-toolchain})
        _ (need (= "leanprover/lean4:v4.33.1" (str/trim (String. ^bytes (#'transport/bytes! (child! root "lean-toolchain") 4096) StandardCharsets/UTF_8)))
                "UnsupportedProjectConfig" {:stage :lake-toolchain})
        _ (need (Files/notExists (child! root (str (get manifest "lakeDir" ".lake") "/package-overrides.json")) no-links)
                "UnsupportedProjectConfig" {:stage :lake-overrides})
        configs (apply merge root-files (map #(configuration-files (:directory %) (:configuration %)) packages))
        lake (#'transport/executable! (.resolve ^Path (:sysroot state) "bin/lake"))
        lake-record (record! lake (* 256 1048576))
        stage (Files/createTempDirectory ^Path (:cache state) ".lake-workspace-" attrs)
        execution (assoc state :working-directory root :diagnostics-executable (str lake))
        journal (atom {:processes []})
        _ (doseq [{:keys [directory kind revision]} packages :when (= "git" kind)]
            (let [receipt (run! (assoc execution :working-directory directory) journal stage
                               (str "revision-" (count (:processes @journal))) ["/usr/bin/git" "rev-parse" "HEAD"])]
              (need (= revision (str/trim (text! stage receipt))) "ArtifactConflict" {:stage :lake-locked-revision})))
        _ (verify-files! configs)
        target (str "+" (str/join "." components) ":leanArts")
        query (run! execution journal stage "lake-up-to-date"
                    [lake "--no-build" "--no-cache" "--rehash" "--quiet" "--json" "query" target])
        _ (need (= "null" (str/trim (text! stage query))) "ArtifactConflict" {:stage :lake-query-protocol})
        _ (verify-files! configs)
        ;; Lake can retain a large elaborated lakefile environment. Obtain its
        ;; search path, then retire Lake before starting the Lean inventory reader
        ;; rather than paying both RSS footprints in one owned process tree.
        search-receipt (run! execution journal stage "lake-search-path"
                             [lake "--no-build" "--no-cache" "--quiet" "env"])
        search-output (text! stage search-receipt)
        search-lines (filterv #(str/starts-with? % "LEAN_PATH=") (str/split search-output #"\n" -1))
        _ (need (= 1 (count search-lines)) "ArtifactConflict" {:stage :lake-search-protocol})
        search (subs (first search-lines) 10)
        _ (need (and (<= 1 (count search) 65536) (not-any? #{\newline \return \u0000} search))
                "ArtifactConflict" {:stage :lake-search-protocol})
        _ (verify-files! configs)
        probe (.resolve stage "LakeInventory.lean")
        probe-bytes (with-open [input (io/input-stream (io/resource probe-resource))] (.readNBytes input 65537))
        _ (need (<= (alength probe-bytes) 65536) "BuildResourceLimit" {})
        _ (Files/write probe probe-bytes (into-array OpenOption [StandardOpenOption/CREATE_NEW StandardOpenOption/WRITE]))
        probe-record (record! probe 65536)
        ;; Elaborating the reader with the stock toolchain exceeded 512 MiB
        ;; on the CI executor. The independent native RSS cap still applies.
        inventory-receipt (run! execution journal stage "lake-inventory"
                               [(.resolve ^Path (:sysroot state) "bin/lean") "-M768" "-j1" "--run" probe
                                (str/join "." components)] search)
        inventory (#'transport/read-json! (.resolve stage (get inventory-receipt "stdout")) (* 4 1048576))
        _ (need (and (= #{"schema" "leanCommit" "leanVersion" "modules"} (set (keys inventory)))
                     (= "lean-lake-product-inventory/1" (get inventory "schema"))
                     (= transport/lean-pin (get inventory "leanCommit")) (= "4.33.1" (get inventory "leanVersion")))
                "ArtifactConflict" {:stage :lake-inventory})
        captured (module-products! state (get inventory "modules") (mapv :directory packages))
        _ (need (some #{root-name} (:names captured)) "MissingDependency" {:stage :lake-root-product})
        metadata {"profile" profile "rootModule" root-name "implementation" implementation-record "lake" lake-record
                  "probeSHA256" (#'transport/digest probe-bytes)
                  "packages" (mapv (fn [{:keys [name directory configuration]}]
                                     {"name" name "configuration" (into (sorted-map)
                                       (map (fn [[path record]] [(str (.relativize ^Path directory ^Path path)) record])
                                            (configuration-files directory configuration)))}) packages)
                  "modules" (mapv #(assoc (dissoc % "olean") "origin"
                                         (if (contains? (:products captured) (get % "module")) "workspace" "toolchain"))
                                  (get inventory "modules"))}
        verify (fn []
                 (need (= implementation-record (#'transport/source-record! implementation-source)) "ArtifactConflict" {:stage :workspace-implementation})
                 (verify-files! (merge configs (:files captured) {lake lake-record probe probe-record}))
                 (doseq [path (:absent captured)]
                   (need (Files/notExists ^Path path no-links) "ArtifactConflict" {:stage :lake-product-presence})))
        _ (verify)
        _ (need (= (#'transport/digest probe-bytes) (get probe-record "sha256")) "ArtifactConflict" {:stage :lake-probe-mutation})
        key (#'transport/digest (#'transport/canonical metadata))
        adapter-name (str "AnsatzLakeWorkspace_" (subs key 0 16))
        adapter-module ["str" ["anonymous"] adapter-name]
        _ (need (not (some #{adapter-module} (:names captured))) "ModulePathConflict" {})
        adapter (.resolve ^Path (:cache state) (str "lake-adapter-" key))
        _ (Files/createDirectories adapter attrs)
        adapter-file (.resolve adapter (str adapter-name ".lean"))
        source (.getBytes (str "import " (str/join "." (map #(str "«" % "»") components)) "\n") StandardCharsets/UTF_8)
        _ (if (Files/exists adapter-file no-links)
            (need (= (#'transport/digest source) (get (record! adapter-file 1048576) "sha256")) "ArtifactConflict" {:stage :lake-adapter})
            (Files/write adapter-file source (into-array OpenOption [StandardOpenOption/CREATE_NEW StandardOpenOption/WRITE])))
        _ (transport/configure-workspace! compiler (assoc captured :metadata metadata :verify! verify))]
    {:project adapter :source-root "." :roots [adapter-module] :installed-imports (:names captured)}))
