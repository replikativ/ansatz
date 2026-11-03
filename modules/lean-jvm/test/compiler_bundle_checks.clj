(ns ansatz-lean-jvm-compiler-bundle-checks
  "Private bundle byte-custody models; small fixture bytes are not native proof."
  (:require [clojure.test :refer [deftest is run-tests]]
            [clojure.data.json :as json]
            [ansatz.lean.jvm.compiler.bundle :as bundle]
            [ansatz.lean.jvm.compiler.transport :as transport]
            [ansatz.lean.jvm.entry :as entry]
            [ansatz.lean.jvm.producer :as producer])
  (:import [java.nio.file Path Files LinkOption]
           [java.nio.file.attribute FileAttribute]
           [java.nio.charset StandardCharsets]))
(def ^:dynamic *root* ".")
(def ^:private attrs (make-array FileAttribute 0))
(defn- write! [^Path root name text]
  (let [path (.resolve root ^String name)]
    (Files/createDirectories (.getParent path) attrs)
    (Files/write path (.getBytes ^String text StandardCharsets/UTF_8)
                 (make-array java.nio.file.OpenOption 0)) path))
(defn- record [path] (#'transport/file-record path 1048576))
(defn- sha [path] (get (record path) "sha256"))
(defn- doc! [root name value] (write! root name (json/write-str value)))
(defn- refused? [f] (try (f) false (catch Exception _ true)))
(defn- tree [f]
  (let [parent (.normalize (.toAbsolutePath (Path/of (str *root* "/.tmp/compiler-bundle-fixtures") (make-array String 0))))
        _ (Files/createDirectories parent attrs)
        root (Files/createTempDirectory parent "case-" attrs)]
    (try (f root)
         (finally (with-open [paths (Files/walk root (make-array java.nio.file.FileVisitOption 0))]
                    (doseq [path (reverse (sort-by #(.getNameCount ^Path %) (iterator-seq (.iterator paths))))]
                      (Files/deleteIfExists path)))))))
(defn- fixture! [root]
  (let [names ["NativeEntryTransport" "NativeTypeGraph" "NativeNominalEntryEvidence"]
        rows (mapv (fn [name] (let [p (write! root (str name ".lean") (str "-- model " name))]
                               {"module" ["str" ["anonymous"] name] "source" (str name ".lean") "sha256" (sha p)})) names)
        binary (write! root "bin/entry" "model-executable-not-native-proof")
        _ (.setExecutable (.toFile binary) true false)
        closure (#'bundle/closure-digest rows)
        receipt {"schema" "lean-native-entry-candidate/1" "status" "entry-built-not-published"
                 "leanCommit" transport/lean-pin "sourceClosure" rows "sourceClosureSHA256" closure
                 "products" [(assoc (record binary) "path" "entry")]
                 "processes" [{"label" "link-entry" "exit" 0}]
                 "standaloneLinkConfig" {"supportInterpreter" true "interpreterExportFlag" "-rdynamic"
                                         "linkerThreads" 1 "authority" "pinned Lake.Config.LeanExe.exeOnlyLinkArgs"}}
        receipt-path (doc! root "receipts/entry-build.json" receipt)
        entry {"binary" "bin/entry" "binarySHA256" (sha binary)
               "source" "NativeNominalEntryEvidence.lean" "sourceSHA256" (get (last rows) "sha256")
               "sourceClosure" rows "sourceClosureSHA256" closure
               "buildReceipt" "receipts/entry-build.json" "buildReceiptSHA256" (sha receipt-path)}
        auxiliary (into {} (for [name ["startupHeader" "typedSource"]]
                             (let [b (write! root (str "bin/" name) (str "model-" name))
                                   s (write! root (str "sources/" name ".lean") (str "-- " name))]
                               (.setExecutable (.toFile b) true false)
                               [name {"binary" (str "bin/" name) "binarySHA256" (sha b)
                                      "source" (str "sources/" name ".lean") "sourceSHA256" (sha s)}])))
        descriptor {"schema" "lean-native-producer-bundle/2" "leanCommit" transport/lean-pin
                    "leanVersion" "4.33.1" "target" "x86_64-unknown-linux-gnu" "wordBits" 64
                    "producers" (assoc auxiliary "entry" entry)}
        expected (select-keys entry ["binarySHA256" "sourceSHA256" "sourceClosureSHA256" "buildReceiptSHA256"])]
    (doc! root "producer-bundle.json" descriptor)
    {:descriptor descriptor :expected expected :receipt receipt :rows rows}))
(defn- inspect [root fixture]
  ;; Only auxiliary independent pin lookup is replaced for these tiny bytes.
  ;; Candidate entry NEVER calls public admission or Compiler configuration.
  (with-redefs [producer/supported? (fn [name _ _] (contains? #{"startupHeader" "typedSource"} name))
                transport/configure! (fn [_] (throw (AssertionError. "Candidate must not configure Compiler")))]
    (#'bundle/inspect-candidate! root (:expected fixture))))

(deftest exact-native-builder-wire-and-descriptive-candidate-only
  (tree (fn [root]
          (let [fixture (fixture! root) observed (inspect root fixture)]
            (is (false? (:admission observed)))
            (is (= :byte-correspondence-only (:authority observed)))
            (is (= (:descriptor fixture) (:descriptor observed)))
            (is (= 3 (count (:entry-sources observed))))
            (is (not (contains? observed :compiler)))
            (is (not (contains? observed :evidence-options)))
            (is (refused? #(entry/schema-for-pins! (get-in fixture [:expected "sourceSHA256"])
                                                  (get-in fixture [:expected "binarySHA256"]))))
            (is (refused? #(inspect root (assoc fixture :expected {}))))
            (is (refused? #(inspect root (assoc-in fixture [:expected "binarySHA256"] (apply str (repeat 64 "0"))))))))))

(deftest exact-three-modules-and-builder-order-not-self-reported-source-root
  (tree (fn [root]
          (let [fixture (fixture! root)]
            (doseq [rows [(pop (:rows fixture)) (conj (:rows fixture) (first (:rows fixture)))
                          (vec (reverse (:rows fixture)))
                          (assoc-in (:rows fixture) [0 "source"] "../NativeEntryTransport.lean")
                          (assoc-in (:rows fixture) [0 "extra"] true)]]
              (is (refused? #(#'bundle/closure-digest rows))))
            (let [d (assoc-in (:descriptor fixture) ["producers" "entry" "sourceRoot"] ".")]
              (doc! root "producer-bundle.json" d)
              (is (refused? #(inspect root fixture))))))))

(deftest bytes-receipt-and-auxiliary-cohorts-must-correspond
  (tree (fn [root]
          (let [fixture (fixture! root)]
            (write! root "NativeTypeGraph.lean" "changed dependency")
            (is (refused? #(inspect root fixture)))
            (fixture! root)
            (write! root "bin/entry" "changed binary")
            (is (refused? #(inspect root fixture)))
            (fixture! root)
            (write! root "receipts/entry-build.json" "{}")
            (is (refused? #(inspect root fixture)))
            (fixture! root)
            (is (refused? #(with-redefs [producer/supported? (constantly false)]
                            (#'bundle/inspect-candidate! root (:expected fixture)))))
            (is (refused? #(#'bundle/candidate-receipt!
                            (assoc (:receipt fixture) "sourceClosureSHA256" (apply str (repeat 64 "0")))
                            (get-in fixture [:descriptor "producers" "entry"]) (record (.resolve root "bin/entry")))))
            (is (refused? #(#'bundle/candidate-receipt!
                            (assoc (:receipt fixture) "products" [])
                            (get-in fixture [:descriptor "producers" "entry"]) (record (.resolve root "bin/entry")))))))))

(deftest paths-symlinks-and-hardlink-role-aliases-refuse
  (tree (fn [root]
          (let [fixture (fixture! root) original (.resolve root "NativeTypeGraph.lean")
                moved (.resolve root "graph-real.lean")]
            (doseq [path ["../outside" "/absolute" "a/../NativeTypeGraph.lean"]]
              (is (refused? #(#'bundle/child! root path))))
            (Files/move original moved (make-array java.nio.file.CopyOption 0))
            (Files/createSymbolicLink original (.getFileName moved) attrs)
            (is (refused? #(inspect root fixture)))
            (Files/delete original)
            (Files/move moved original (make-array java.nio.file.CopyOption 0))
            ;; Distinct paths to one inode are also forbidden across roles.
            (let [typed (.resolve root "bin/typedSource") header (.resolve root "bin/startupHeader")
                  _ (Files/delete typed) _ (Files/createLink typed header)
                  d (assoc-in (:descriptor fixture) ["producers" "typedSource" "binarySHA256"] (sha header))]
              (doc! root "producer-bundle.json" d)
              (is (refused? #(inspect root fixture))))))))

(deftest v1-private-validation-shape-keeps-independent-entry-dispatch
  (tree (fn [root]
          (let [fixture (fixture! root) d (get-in fixture [:descriptor "producers" "entry"])
                calls (atom [])]
            (with-redefs [entry/schema-for-pins! (fn [source binary] (swap! calls conj [source binary]) 2)]
              (let [old (select-keys d ["source" "sourceSHA256" "binary" "binarySHA256"])
                    result (#'bundle/producer! root "entry" old)]
                (is (= 2 (:entry-schema result)))
                (is (= [[(get d "sourceSHA256") (get d "binarySHA256")]] @calls))
                (is (refused? #(#'bundle/producer! root "entry" d)))))))))

(defn check! [root]
  (binding [*root* root] (run-tests 'ansatz-lean-jvm-compiler-bundle-checks)))
