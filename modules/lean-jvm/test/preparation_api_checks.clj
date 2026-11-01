(ns ansatz-lean-jvm-preparation-api-checks
  "Public preparation lifetime/error/CLI models. Native compiler and issuer
   seams are mocked deliberately; no fixture here claims native acceptance."
  (:require [clojure.test :refer [deftest is run-tests]]
            [clojure.java.io :as io] [clojure.data.json :as json]
            [ansatz.lean.jvm :as lean] [ansatz.lean.jvm.preparation :as preparation]
            [ansatz.lean.jvm.artifact :as artifact] [ansatz.lean.jvm.ir :as ir]
            [ansatz.lean.jvm.project :as project] [ansatz.lean.jvm.publisher :as publisher]
            [ansatz.lean.jvm.startup :as startup]
            [ansatz.lean.jvm.compiler.bundle :as bundle]
            [ansatz.lean.jvm.compiler.evidence :as evidence]
            [ansatz.lean.jvm.compiler.transport :as transport])
  (:import [ansatz.lean.jvm LeanPreparation PreparedArtifact ProjectOptions NativeCompilerOptions LeanException]
           [java.io ByteArrayOutputStream OutputStream IOException StringWriter]
           [java.nio.file Path Files LinkOption]
           [java.nio.file.attribute FileAttribute]))
(def ^:dynamic *module-root* ".")
(def manifest-sha (apply str (repeat 64 "a")))
(def archive-sha (apply str (repeat 64 "b")))
(defn- path [value] (Path/of value (make-array String 0)))
(defn- options
  ([] (options ["f" "main"]))
  ([names]
   (let [builder (ProjectOptions/builder (NativeCompilerOptions. (path "sysroot") (path "bundle") (path "cache")))]
     (doseq [name names] (.function builder name)) (.build builder))))
(defn- forbidden [& _] (throw (AssertionError. "Preparation entered JVM execution")))
(defn- with-backend [hooks f]
  (let [compiler (Object.) receipt (Object.) calls (atom [])]
    (with-redefs [bundle/open! (fn [options] (swap! calls conj [:open options])
                                {:compiler compiler :project-options {:compile? true} :evidence-options {:entry-schema 2}})
                  evidence/build! (fn [& args] (swap! calls conj (into [:build] args))
                                    (if-let [hook (:build hooks)] (apply hook args) receipt))
                  artifact/export! (fn [actual output] (swap! calls conj [:export actual output])
                                     (if-let [hook (:export hooks)] (hook actual output)
                                       (do (.write ^OutputStream output (.getBytes "fixture" "UTF-8"))
                                           {:manifest-sha256 manifest-sha :archive-sha256 archive-sha :private-receipt (Object.)})))
                  transport/close! (fn [actual] (swap! calls conj [:close actual])
                                     (when-let [hook (:close hooks)] (hook actual)))
                  ir/linked-basis forbidden project/runtime-service! forbidden
                  publisher/prepare-artifact! forbidden publisher/prepare-build-bytes! forbidden startup/open! forbidden]
      (f {:compiler compiler :receipt receipt :calls calls}))))
(defn- caller-output [closed]
  (proxy [ByteArrayOutputStream] [] (close [] (reset! closed true))))
(deftest public-java-preparation-exports-before-closing-without-jvm-startup
  (with-backend {}
    (fn [{:keys [compiler receipt calls]}]
      (let [closed (atom false) output (caller-output closed) source (path "project") opts (options)
            ^PreparedArtifact result (LeanPreparation/prepareProject source opts output)
            build (second @calls)]
        (is (= manifest-sha (.manifestSHA256 result)))
        (is (= archive-sha (.archiveSHA256 result)))
        (is (= [:open :build :export :close] (mapv first @calls)))
        (is (identical? compiler (second build)))
        (is (= {:compile? true :project source :source-root "." :roots [["str" ["anonymous"] "Main"]]} (nth build 2)))
        (is (= ["f" "main"] (mapv #(last (:name %)) (nth build 4))))
        (is (identical? receipt (second (nth @calls 2))))
        (is (= "fixture" (.toString output "UTF-8")))
        (is (not @closed))))))
(deftest clojure-wrapper-returns-only-independent-digest-values
  (with-backend {}
    (fn [_]
      (let [closed (atom false) output (caller-output closed)
            result (lean/prepare-project "project" (options ["f"]) output)]
        (is (= {:manifest-sha256 manifest-sha :archive-sha256 archive-sha} result))
        (is (not @closed))))))
(deftest invalid-names-and-null-inputs-refuse-before-native-service
  (with-backend {}
    (fn [{:keys [calls]}]
      (doseq [names [[""] ["A..f"] ["f" "f"]]]
        (let [error (try (LeanPreparation/prepareProject (path "project") (options names) (ByteArrayOutputStream.))
                         nil (catch LeanException error error))]
          (is (= "EntryRejected" (.code ^LeanException error)))))
      (is (thrown? NullPointerException (LeanPreparation/prepareProject nil (options) (ByteArrayOutputStream.))))
      (is (empty? @calls)))))
(deftest requested-entry-cap-is-checked-at-the-public-boundary
  (let [builder (ProjectOptions/builder (NativeCompilerOptions. (path "sysroot") (path "bundle") (path "cache")))]
    (dotimes [i ProjectOptions/MAX_SELECTED_ENTRIES] (.function builder (str "f" i)))
    (is (= ProjectOptions/MAX_SELECTED_ENTRIES (.size (.entries (.build builder)))))
    (.function builder "oneTooMany")
    (is (thrown? IllegalArgumentException (.build builder)))))
(deftest native-and-stream-failures-retire-compiler-and-preserve-caller-stream
  (doseq [stage [:build :export]]
    (let [failure (ex-info "native preparation failed" {:code "NativeCompileFailed" :private (Object.)})]
      (with-backend {stage (fn [& _] (throw failure))}
        (fn [{:keys [calls]}]
          (let [closed (atom false) output (caller-output closed)
                error (try (LeanPreparation/prepareProject (path "project") (options) output)
                           nil (catch LeanException error error))]
            (is (= "NativeCompileFailed" (.code ^LeanException error)))
            (is (nil? (.getCause ^LeanException error)))
            (is (= :close (first (last @calls))))
            (is (not @closed)))))))
  (let [closed (atom false) failure (IOException. (apply str (repeat 5000 "x")))
        output (proxy [ByteArrayOutputStream] []
                 (write ([value] (throw failure)) ([buffer offset length] (throw failure)))
                 (close [] (reset! closed true)))]
    (with-backend {}
      (fn [{:keys [calls]}]
        (let [^LeanException error (try (LeanPreparation/prepareProject (path "project") (options) output)
                                       nil (catch LeanException error error))]
          (is (= 2048 (count (.getMessage error))))
          (is (nil? (.getCause error)))
          (is (= :close (first (last @calls))))
          (is (not @closed)))))))
(deftest fatal-native-errors-survive-ordinary-compiler-cleanup-failure
  (let [fatal (OutOfMemoryError. "synthetic preparation fault")]
    (with-backend {:build (fn [& _] (throw fatal)) :close (fn [_] (throw (IOException. "cleanup")))}
      (fn [{:keys [calls]}]
        (is (identical? fatal (try (LeanPreparation/prepareProject (path "project") (options) (ByteArrayOutputStream.))
                                  nil (catch Error actual actual))))
        (is (= :close (first (last @calls))))))))
(defn- with-cli-directory [f]
  (let [parent (.resolve (.toAbsolutePath (path *module-root*)) "target/preparation-models")]
    (Files/createDirectories parent (make-array FileAttribute 0))
    (let [directory (Files/createTempDirectory parent "cli-" (make-array FileAttribute 0))]
      (try (f directory)
           (finally (doseq [file (reverse (file-seq (.toFile directory)))] (io/delete-file file)))))))
(defn- cli [arguments]
  (let [output (StringWriter.) error (StringWriter.)
        status (binding [*out* output *err* error] (preparation/cli-status arguments))]
    {:status status :out (str output) :err (str error)}))
(defn- cli-args [destination]
  ["--source" "project" "--sysroot" "sysroot" "--producer-bundle" "bundle"
   "--cache" "cache" "--entry" "f" "--output" (str destination)])
(deftest cli-help-and-argument-errors-do-not-open-native-service
  (with-backend {}
    (fn [{:keys [calls]}]
      (let [help (cli ["--help"]) error (cli ["--unknown" "x"])]
        (is (= 0 (:status help)))
        (is (.contains ^String (:out help) "--producer-bundle"))
        (is (= 2 (:status error)))
        (is (= "InvalidArguments" (get (json/read-str (:err error)) "code")))
        (is (empty? @calls))))))
(deftest cli-publishes-complete-output-without-overwrite-or-temp-leaks
  (with-cli-directory
    (fn [directory]
      (with-backend {}
        (fn [{:keys [calls]}]
          (let [destination (.resolve directory "prepared.zip")
                success (cli (cli-args destination))
                before (Files/readAllBytes destination)
                rejected (cli (cli-args destination))]
            (is (= 0 (:status success)))
            (is (= {"manifest-sha256" manifest-sha "archive-sha256" archive-sha} (json/read-str (:out success))))
            (is (= "fixture" (String. before "UTF-8")))
            (is (= 2 (:status rejected)))
            (is (= "ArtifactExists" (get (json/read-str (:err rejected)) "code")))
            (is (= (vec before) (vec (Files/readAllBytes destination))))
            (is (= 1 (count (filter #(= :open (first %)) @calls))))
            (is (= ["prepared.zip"] (mapv #(.getName %) (filter #(.isFile %) (file-seq (.toFile directory))))))))))))
(deftest cli-failed-preparation-leaves-no-output-or-temp-file
  (with-cli-directory
    (fn [directory]
      (with-backend {:build (fn [& _] (throw (ex-info "compile failed" {:code "NativeCompileFailed"})))}
        (fn [_]
          (let [destination (.resolve directory "prepared.zip") result (cli (cli-args destination))]
            (is (= 2 (:status result)))
            (is (= "NativeCompileFailed" (get (json/read-str (:err result)) "code")))
            (is (Files/notExists destination (make-array LinkOption 0)))
            (is (empty? (filter #(.isFile %) (file-seq (.toFile directory)))))))))))

(defn- export-fixture [output]
  ;; Only authority/file-validation seams are mocked. Actual ZIP write/finish/
  ;; flush and the nonclosing stream adapter remain the implementation under test.
  (with-redefs-fn {#'artifact/source-authenticator (fn [_] {})
                  #'artifact/export-files! (fn [_] (sorted-map "payload.txt" (.getBytes "fixture" "UTF-8")))
                  #'artifact/build-manifest (fn [& _] {}) #'artifact/validate! (fn [& _] nil)}
    #(artifact/export! (Object.) output)))
(deftest zip-export-fatal-write-identity-and-caller-ownership
  (let [fatal (OutOfMemoryError. "synthetic ZIP write fault") writes (atom 0) closed (atom false)
        fail (fn [] (if (= 1 (swap! writes inc)) (throw fatal) (throw (IOException. "secondary ZIP write"))))
        output (proxy [OutputStream] []
                 (write ([value] (fail)) ([buffer offset length] (fail)))
                 (flush [] (throw (IOException. "secondary flush")))
                 (close [] (reset! closed true)))]
    (is (identical? fatal (try (export-fixture output) nil (catch Error actual actual))))
    (is (pos? @writes))
    (is (not @closed))))
(deftest zip-export-success-and-flush-failure-never-close-caller
  (let [closed (atom false) output (caller-output closed) result (export-fixture output)]
    (is (= 64 (count (:manifest-sha256 result))))
    (is (= 64 (count (:archive-sha256 result))))
    (is (pos? (.size output)))
    (is (not @closed)))
  (let [closed (atom false) failure (IOException. "flush failed")
        output (proxy [ByteArrayOutputStream] [] (flush [] (throw failure)) (close [] (reset! closed true)))]
    (is (identical? failure (try (export-fixture output) nil (catch IOException actual actual))))
    (is (not @closed))))
(defn check! [module-root]
  (binding [*module-root* module-root] (run-tests 'ansatz-lean-jvm-preparation-api-checks)))
