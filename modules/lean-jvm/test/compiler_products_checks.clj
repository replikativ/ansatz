(ns ansatz-lean-jvm-compiler-products-checks
  "Tiny private filesystem fixtures; no native execution or issued source proof."
  (:require [clojure.test :refer [deftest is run-tests]]
            [clojure.data.json :as json]
            [ansatz.lean.jvm.compiler.products :as products]
            [ansatz.lean.jvm.compiler.local :as compiler-local]
            [ansatz.lean.jvm.compiler.transport :as transport]
            [ansatz.lean.jvm.installed :as installed]
            [ansatz.lean.jvm.used-products :as used])
  (:import [java.nio.file Path Files LinkOption StandardOpenOption]
           [java.nio.file.attribute FileAttribute]
           [java.nio.charset StandardCharsets]))

(def ^:private attrs (make-array FileAttribute 0))
(def ^:private no-links (into-array LinkOption [LinkOption/NOFOLLOW_LINKS]))
(defn- n [& parts] (reduce #(vector "str" %1 %2) ["anonymous"] parts))
(def local (n "App" "Main"))
(def foreign (n "Other" "Types"))
(def implicit (n "Init" "Data" "Ord" "Basic"))
(def required [local foreign implicit])
(defn- write! [^Path root relative text]
  (let [path (.resolve root ^String relative)]
    (Files/createDirectories (.getParent path) attrs)
    (Files/write path (.getBytes ^String text StandardCharsets/UTF_8)
                 (make-array java.nio.file.OpenOption 0)) path))
(defn- record [path] (#'transport/file-record path installed/max-product-bytes))
(defn- with-tree [f]
  (let [parent (.toAbsolutePath (Path/of ".tmp/compiler-products-fixtures" (make-array String 0)))
        _ (Files/createDirectories parent attrs)
        root (Files/createTempDirectory parent "fixture-" attrs)]
    (try (f root)
         (finally
           (with-open [paths (Files/walk root (make-array java.nio.file.FileVisitOption 0))]
             (doseq [path (reverse (sort-by #(.getNameCount ^Path %) (iterator-seq (.iterator paths))))]
               (Files/deleteIfExists path)))))))
(defn- fixture! [^Path root]
  (let [directory (.resolve root "compiled") build (.resolve directory "build")
        sysroot (.resolve root "sysroot") library (.resolve sysroot "lib/lean")
        _ (Files/createDirectories build attrs) _ (Files/createDirectories library attrs)
        primary (write! build "App/Main.olean" "actual-local-olean")
        optional (write! build "App/Main.ir.sig" "actual-local-ir-signature")
        _ (write! library "Other/Types.olean" "actual-installed-olean")
        _ (write! library "Other/Types.olean.server" "")
        _ (write! library "Init/Data/Ord/Basic.olean" "actual-implicit-init-olean")
        installed {"profile" installed/profile
                   "modules" [{"module" foreign
                               "products" (mapv (fn [relative]
                                                   (let [path (.resolve library ^String relative)]
                                                     (if (Files/exists path no-links)
                                                       (assoc (record path) "path" relative "present" true)
                                                       {"path" relative "present" false})))
                                                 (installed/product-paths foreign))}]}]
    {:state {:sysroot sysroot} :directory directory
     :compiled [{"module" local "source" {"bytes" 1 "sha256" (apply str (repeat 64 "b"))}
                 "olean" "App/Main.olean" "oleanRecord" (record primary)}]
     :files {"build/App/Main.olean" (record primary) "build/App/Main.ir.sig" (record optional)}
     :installed installed}))
(defn- refused? [f]
  (try (f) false (catch clojure.lang.ExceptionInfo _ true)))
(defn- reason [f]
  (try (f) nil (catch clojure.lang.ExceptionInfo e (:reason (ex-data e)))))

(deftest captures-real-primary-bytes-and-every-optional-role
  (with-tree
    (fn [root]
      (let [context (fixture! root) payload (#'products/capture-context! context required)
            doc (:manifest payload) rows (get doc "modules")]
        (is (= required (mapv #(get % "module") rows)))
        (is (= installed/suffixes (mapv #(get % "role") (get (first rows) "products"))))
        (is (= (get-in context [:compiled 0 "oleanRecord" "sha256"]) (get-in rows [0 "productSha256"])))
        (is (not= (get-in context [:compiled 0 "source" "sha256"]) (get-in rows [0 "productSha256"])))
        (is (= {"role" ".olean.private" "present" false} (get-in rows [0 "products" 2])))
        (is (= 0 (get-in rows [1 "products" 1 "bytes"])))
        (is (= doc (used/authorize! doc required [local] [foreign])))
        (is (= (used/digest doc) (:sha256 payload)))
        (is (true? (:requires-v3-rebuild payload)))
        (is (true? (#'products/verify-context! payload)))
        (is (true? (#'products/verify-context! payload)))
        (is (= {"schema" used/schema "modules" []}
               (:manifest (#'products/capture-context! context []))))))))

(deftest inventory-never-grants-import-permission-or-caller-paths
  (with-tree
    (fn [root]
      (let [context (fixture! root)]
        (is (= :undeclared-origin (reason #(#'products/collect! context [(n "Unlisted")]))))
        (is (= :inventory (reason #(#'products/collect! context [local local]))))
        (is (refused? #(#'products/collect! context [(n "..")])))
        (is (refused? #(#'products/collect! context [(n (str (char 0xd800)))])))
        (is (= :local-primary-record
               (reason #(#'products/collect! (assoc-in context [:compiled 0 "olean"] "../../outside.olean") [local]))))
        (is (= :origin-shadowing
               (reason #(#'products/collect! (assoc-in context [:installed "modules" 0 "module"] local) [local]))))
        (is (refused? #(products/capture! (Object.) {:directory "/arbitrary"} [local])))
        (is (= :capture-identity (reason #(products/manifest (Object.)))))))))

(deftest native-resolution-selects-package-and-does-not-fall-through
  (with-tree
    (fn [root]
      (let [context (fixture! root) build (.resolve ^Path (:directory context) "build")]
        (Files/createDirectory (.resolve build "Other") attrs)
        (is (= :native-resolution-shadow (reason #(#'products/collect! context [foreign]))))
        (Files/delete (.resolve build "Other"))
        (write! build "Other.olean" "different-root-module")
        (is (= :native-resolution-shadow (reason #(#'products/collect! context [foreign]))))
        (Files/delete (.resolve build "Other.olean"))
        (Files/createDirectory (.resolve build "Init") attrs)
        (is (= :native-resolution-shadow (reason #(#'products/collect! context [implicit]))))))))

(deftest recheck-detects-primary-sidecar-and-absence-mutation
  (doseq [[relative change] [["Init/Data/Ord/Basic.olean" "changed"]
                             ["Init/Data/Ord/Basic.olean.private" "new-optional"]]]
    (with-tree
      (fn [root]
        (let [context (fixture! root) payload (#'products/capture-context! context required)
              library (.resolve ^Path (get-in context [:state :sysroot]) "lib/lean")]
          (write! library relative change)
          (is (= :used-product-mutation (reason #(#'products/verify-context! payload))))))))
  (with-tree
    (fn [root]
      (let [context (fixture! root) payload (#'products/capture-context! context required)
            build (.resolve ^Path (:directory context) "build")]
        (write! build "App/Main.olean" "changed-local")
        (is (= :local-primary-mutation (reason #(#'products/verify-context! payload)))))))
  (with-tree
    (fn [root]
      (let [context (fixture! root) build (.resolve ^Path (:directory context) "build")]
        (write! build "App/Main.olean.server" "appeared")
        (is (= :local-role-presence (reason #(#'products/collect! context [local]))))
        (Files/delete (.resolve build "App/Main.olean.server"))
        (Files/delete (.resolve build "App/Main.ir.sig"))
        (is (= :local-role-presence (reason #(#'products/collect! context [local])))))))
  (with-tree
    (fn [root]
      (let [context (fixture! root) payload (#'products/capture-context! context required)
            library (.resolve ^Path (get-in context [:state :sysroot]) "lib/lean")]
        (write! library "Other/Types.olean.private" "new-installed-sidecar")
        (is (refused? #(#'products/verify-context! payload)))))))

(deftest path-kind-and-budget-refusals
  (with-tree
    (fn [root]
      (let [context (fixture! root) library (.resolve ^Path (get-in context [:state :sysroot]) "lib/lean")
            primary (.resolve library "Init/Data/Ord/Basic.olean") outside (write! root "outside.olean" "outside")]
        (Files/delete primary)
        (Files/createSymbolicLink primary outside attrs)
        (is (= :symlink (reason #(#'products/collect! context [implicit]))))
        (Files/delete primary)
        (Files/createDirectory primary attrs)
        (is (= :nonregular-product (reason #(#'products/collect! context [implicit]))))
        (Files/delete primary)
        (is (= :primary-missing (reason #(#'products/collect! context [implicit])))))))
  (with-tree
    (fn [root]
      (let [context (fixture! root)]
        ;; Tiny bounds exercise pre-hash budget checks, without large fixtures.
        (with-redefs [installed/max-product-bytes 4]
          (is (= :product-byte-limit (reason #(#'products/collect! context [implicit])))))
        (with-redefs [installed/max-total-bytes 4]
          (is (= :total-byte-limit (reason #(#'products/collect! context [implicit])))))))))

(deftest compiler-configuration-and-owned-baseline-coherency
  ;; Pure model fixtures only: neither this Object nor a map is an issued compiler.
  (with-tree
    (fn [root]
      (let [context (fixture! root)
            state (assoc (:state context) :producer (.resolve ^Path root "producer")
                         :producer-sha256 (apply str (repeat 64 "a")) :launcher (.resolve ^Path root "launcher"))
            inputs {"toolchain" {"policy" "trusted-immutable-installed-official-toolchain/1"
                                 "sysroot" (str (:sysroot state)) "typedSourceProducerPath" (str (:producer state))
                                 "typedSourceProducer" {"sha256" (:producer-sha256 state)}
                                 "resourceLauncherPath" (str (:launcher state))}
                    "installedImports" (:installed context)}
            _ (is (identical? inputs (#'products/compiler-baseline! state inputs)))
            toolchain (java.util.HashMap. ^java.util.Map (get inputs "toolchain"))
            caller-inputs (assoc inputs "toolchain" toolchain)
            parsed (json/read-str (json/write-str {"inputs" caller-inputs "compiled" (:compiled context) "files" (:files context)}))
            sealed (#'products/parsed-context (Object.) state (:directory context) (apply str (repeat 64 "a")) parsed)]
        (is (identical? (get parsed "inputs") (:inputs sealed)))
        (is (identical? (get-in parsed ["inputs" "installedImports"]) (:installed sealed)))
        (.put toolchain "sysroot" "/mutated-caller-path")
        (is (= (str (:sysroot state)) (get-in sealed [:inputs "toolchain" "sysroot"])))
        (doseq [path [["toolchain" "policy"] ["toolchain" "sysroot"]
                      ["toolchain" "typedSourceProducerPath"] ["toolchain" "typedSourceProducer" "sha256"]
                      ["toolchain" "resourceLauncherPath"]]]
          (is (= :compiler-baseline-mismatch
                 (reason #(#'products/compiler-baseline! state (assoc-in inputs path "wrong"))))))
        (is (= :compiler-baseline-mismatch (reason #(#'products/compiler-baseline! state {}))))))))

(deftest compilation-baseline-binds-only-selected-authorized-defining-products
  (with-tree
    (fn [root]
      (let [context (fixture! root) state (:state context)
            snapshot (#'compiler-local/compilation-products! state [implicit] [foreign])
            inputs {"profile" compiler-local/nominal-profile "installedImports" (:installed context)
                    "compilationProducts" snapshot}
            context (assoc context :inputs inputs)
            payload (#'products/capture-context! context required)]
        (is (= #{foreign implicit} (set (map #(get % "module") (get snapshot "modules")))))
        (is (= snapshot (#'compiler-local/compilation-products! state [foreign implicit] [foreign])))
        (is (false? (:requires-v3-rebuild payload)))
        (is (true? (#'products/verify-context! payload)))
        (is (true? (compiler-local/verify-compilation-products! state inputs)))
        ;; Removing a dependency cannot be repaired by later origin discovery.
        (let [partial (assoc inputs "compilationProducts"
                             (#'compiler-local/compilation-products! state [] [foreign]))]
          (is (= :missing-compilation-product
                 (reason #(#'products/capture-context! (assoc context :inputs partial) required)))))
        (write! (.resolve ^Path (:sysroot state) "lib/lean") "Init/Data/Ord/Basic.olean.private" "appeared")
        (is (refused? #(compiler-local/verify-compilation-products! state inputs)))
        (is (refused? #(#'products/verify-context! payload)))))))

(deftest compilation-baseline-profile-and-authorization-are-explicit
  (with-tree
    (fn [root]
      (let [{:keys [state]} (fixture! root)
            empty-baseline (#'compiler-local/compilation-products! state [] [])
            nominal {"profile" compiler-local/nominal-profile "compilationProducts" empty-baseline}]
        (is (= {"schema" used/schema "modules" []} empty-baseline))
        (is (true? (compiler-local/verify-compilation-products! state nominal)))
        (is (true? (compiler-local/verify-compilation-products! state {"profile" compiler-local/profile})))
        (is (refused? #(compiler-local/verify-compilation-products! state (dissoc nominal "compilationProducts"))))
        (is (refused? #(compiler-local/verify-compilation-products! state (assoc nominal "profile" compiler-local/profile))))
        (is (refused? #(#'compiler-local/compilation-products! state [(n "Unlisted")] [])))
        (is (refused? #(#'compiler-local/compilation-products! state [implicit implicit] [])))
        (is (refused? #(#'compiler-local/compilation-products! state [(n "..")] [])))))))

(defn check! [] (run-tests 'ansatz-lean-jvm-compiler-products-checks))
