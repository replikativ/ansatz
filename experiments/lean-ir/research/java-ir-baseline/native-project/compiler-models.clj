(ns native-project-compiler-models-v1
  "Owner-free metadata/cache and mocked-process models. No Lean/Python/JVM
   process is launched; synthetic cache data is not native build authority."
  (:require [clojure.test :refer [deftest is run-tests]]
            [clojure.java.io :as io]
            [native-project-compiler-v1 :as compiler])
  (:import [java.nio.file Path Files StandardOpenOption]
           [java.nio.file.attribute FileAttribute]
           [java.nio.charset StandardCharsets]))
(def ^:dynamic *directory* nil)
(defn- temp []
  (assert *directory* "Supply an explicit research workspace to check!")
  (Files/createTempDirectory ^Path *directory* "compiler-model-" (make-array FileAttribute 0)))
(defn- write! [^Path directory name text]
  (let [path (.resolve directory name)]
    (Files/createDirectories (.getParent path) (make-array FileAttribute 0))
    (Files/write path (.getBytes ^String text StandardCharsets/UTF_8)
                 (into-array java.nio.file.OpenOption [StandardOpenOption/CREATE_NEW StandardOpenOption/WRITE])) path))
(defn- cache-fixture []
  (let [directory (temp) _ (write! directory "payload" "synthetic owned metadata") inputs {"model" true}
        manifest {"schema" "native-compiled-project/1" "cacheKey" "key" "inputs" inputs
                  "files" (#'compiler/inventory directory)}]
    (#'compiler/write-json! (.resolve directory "manifest.json") manifest)
    [directory inputs]))
(deftest canonical-key-is-order-independent-and-binds-all-compile-inputs
  (let [base {"source" "one" "toolchain" "one" "exporter" "one" "implementation" "one" "options" {"reference" false}}
        key #(-> % (#'compiler/canonical) (#'compiler/digest))]
    (is (= (key base) (key (into (array-map) (reverse (seq base))))))
    (doseq [field ["source" "toolchain" "exporter" "implementation" "options"]]
      (is (not= (key base) (key (assoc base field "changed")))))))
(deftest source-capture-is-immutable-and-fails-on-modified-or-symlinked-files
  (let [directory (temp) path (write! directory "A.lean" "our synthetic source")
        pin (#'compiler/digest (.getBytes "our synthetic source" StandardCharsets/UTF_8))]
    (with-redefs [compiler/source-pins {"A.lean" pin}]
      (let [capture (#'compiler/source-capture directory)]
        (is (= pin (get-in capture ["A.lean" :record "sha256"])))
        (Files/delete path) (write! directory "A.lean" "different source")
        (is (thrown? Exception (#'compiler/source-capture directory)))
        (is (= "our synthetic source" (String. ^bytes (get-in capture ["A.lean" :bytes]) StandardCharsets/UTF_8))))
      (Files/delete path)
      (let [target (write! directory "actual" "our synthetic source")]
        (Files/createSymbolicLink path target (make-array FileAttribute 0))
        (is (thrown? Exception (#'compiler/source-capture directory)))))))
(deftest complete-cache-validation-binds-key-profile-and-every-file
  (let [[directory inputs] (cache-fixture)]
    (is (string? (:sha256 (#'compiler/validate-hit! directory "key" inputs))))
    (is (thrown? Exception (#'compiler/validate-hit! directory "wrong-key" inputs)))
    (is (thrown? Exception (#'compiler/validate-hit! directory "key" {"model" false})))
    (write! directory "unlisted" "extra")
    (is (thrown? Exception (#'compiler/validate-hit! directory "key" inputs)))))
(deftest cache-mutation-and-oversized-directory-fail-before-reuse
  (let [[directory inputs] (cache-fixture)]
    (Files/delete (.resolve directory "payload"))
    (write! directory "payload" "changed bytes")
    (is (thrown? Exception (#'compiler/validate-hit! directory "key" inputs))))
  (let [directory (temp)]
    (doseq [i (range 257)] (Files/createDirectory (.resolve directory (str "d" i)) (make-array FileAttribute 0)))
    (is (thrown? Exception (#'compiler/inventory directory)))))
(deftest low-memory-refuses-before-native-start-or-journal-publication
  (let [directory (temp) journal (atom {})]
    (with-redefs-fn {#'compiler/available-kib (fn [] 1)}
      #(is (thrown? Exception (#'compiler/run-process! {} journal directory "never-started" [] {}))))
    (is (= {} @journal))
    (with-open [files (Files/list directory)] (is (zero? (.count files))))))
(deftest cancellation-preserves-actual-process-and-interruption-without-replay
  (let [process (proxy [Process] []
                  (isAlive [] true)
                  (getOutputStream [] (java.io.ByteArrayOutputStream.))
                  (getInputStream [] (java.io.ByteArrayInputStream. (byte-array 0)))
                  (getErrorStream [] (java.io.ByteArrayInputStream. (byte-array 0)))
                  (waitFor [] 0) (exitValue [] 0) (destroy [] nil))
        slot (object-array [process]) journal (atom {:process-slot slot}) stopped (atom 0)
        prior (Thread/interrupted)]
    (try
      (with-redefs-fn {#'compiler/stop-process! (fn [actual] (is (identical? process actual)) (swap! stopped inc))}
        #(let [error (try (#'compiler/abort! journal (InterruptedException. "model cancellation"))
                         nil (catch Exception e e))
               interrupted (.isInterrupted (Thread/currentThread))]
           (Thread/interrupted)
           (is interrupted) (is (= 1 @stopped))
           (is (identical? slot (get-in (ex-data error) [:journal :process-slot])))
           (is (= :failed (:status @journal)))))
      (finally (Thread/interrupted) (when prior (.interrupt (Thread/currentThread)))))))
(deftest unissued-compiler-cannot-create-cache-or-start-a-process
  (doseq [value [nil {} (compiler/->NativeCompiler)]]
    (is (thrown? Exception (compiler/cache-root value)))
    (is (thrown? Exception (compiler/compile! value "missing" (atom {}))))))
(defn check! [workspace]
  (binding [*directory* (.toRealPath (.toPath (io/file (str workspace))) (make-array java.nio.file.LinkOption 0))]
    (run-tests 'native-project-compiler-models-v1)))
