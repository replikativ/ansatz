(ns native-project-compiler-models-v1
  "Owner-free metadata/cache and mocked-process models. No Lean/Python/JVM
   process is launched; synthetic cache data is not native build authority."
  (:require [clojure.test :refer [deftest is run-tests]]
            [clojure.java.io :as io]
            [native-project-compiler-v1 :as compiler])
  (:import [java.nio.file Path Files StandardOpenOption]
           [java.lang ProcessHandle]
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
(deftest implementation-source-record-supports-disk-and-bundled-jar-bytes
  (let [directory (temp) text "synthetic compiler resource" path (write! directory "compiler-resource.clj" text)
        expected {"bytes" (alength (.getBytes text StandardCharsets/UTF_8))
                  "sha256" (#'compiler/digest (.getBytes text StandardCharsets/UTF_8))}
        jar (.resolve directory "resource.jar")]
    (is (= expected (#'compiler/source-record! (#'compiler/implementation-source! (str path)))))
    (with-open [out (java.util.jar.JarOutputStream. (Files/newOutputStream jar (make-array java.nio.file.OpenOption 0)))]
      (.putNextEntry out (java.util.jar.JarEntry. "compiler-resource.clj"))
      (.write out (.getBytes text StandardCharsets/UTF_8)) (.closeEntry out))
    (let [url (java.net.URL. (str "jar:" (.toUri jar) "!/compiler-resource.clj"))]
      (with-redefs [io/resource (fn [_] url)]
        (is (= expected (#'compiler/source-record! (#'compiler/implementation-source! "nonexistent-model-resource.clj"))))))
    (with-redefs [io/resource (fn [_] (java.net.URL. "https://example.invalid/compiler.clj"))]
      (is (thrown? Exception (#'compiler/implementation-source! "nonexistent-model-resource.clj"))))
    (with-redefs [io/resource (fn [_] (java.net.URL. "jar:https://example.invalid/compiler.jar!/compiler.clj"))]
      (is (thrown? Exception (#'compiler/implementation-source! "nonexistent-model-resource.clj"))))))
(deftest aggregate-process-rss-preserves-known-descendants-and-deduplicates
  ;; Inspect existing JVM/parent handles only; no process is created or killed.
  (let [self (ProcessHandle/current) parent (.orElse (.parent self) nil) handles (atom [])]
    (is (some? parent))
    (#'compiler/remember-process! handles self)
    (#'compiler/remember-process! handles self)
    (#'compiler/remember-process! handles parent)
    (is (= 2 (count @handles)))
    (with-redefs-fn {#'compiler/handle-rss-kib (fn [_] 23)}
      #(is (= 46 (#'compiler/owned-rss-kib handles))))
    (is (= [self parent] @handles))))
(deftest process-evidence-reader-is-bounded-and-does-not-assume-file-length
  (let [directory (temp) text "MemAvailable: 123456 kB\n" path (write! directory "evidence" text)]
    (is (= text (#'compiler/proc-text! (str path))))
    (is (thrown? Exception (#'compiler/proc-text! (str (.resolve directory "missing")))))
    (write! directory "excessive" (apply str (repeat 65537 "a")))
    (is (thrown? Exception (#'compiler/proc-text! (str (.resolve directory "excessive")))))))
(deftest rss-missing-only-for-actual-no-mm-or-exited-processes
  (is (= 123 (#'compiler/rss-from-status! 7 "State:\tR (running)\nVmRSS:\t123 kB\n" true)))
  (doseq [state ["Z" "X" "x"]]
    (is (zero? (#'compiler/rss-from-status! 7 (str "State:\t" state " (dead or zombie)\n") true))))
  ;; A handle can become non-live after the status snapshot was captured.
  (is (zero? (#'compiler/rss-from-status! 7 "State:\tR (running)\n" false)))
  (doseq [text ["State:\tS (sleeping)\n" "Name:\tno-state\n" "State:\tR (running)\nVmRSS:\tinvalid kB\n"]]
    (let [error (try (#'compiler/rss-from-status! 7 text true) nil (catch clojure.lang.ExceptionInfo e e))]
      (is (some? error))
      (is (= 7 (:pid (ex-data error))))
      (is (= text (:status (ex-data error)))))))
(deftest waiting-compile-cannot-start-after-close-returns
  (let [token (compiler/->NativeCompiler) lock (Object.) registry @#'compiler/compilers
        original-issued @#'compiler/issued captured (java.util.concurrent.CountDownLatch. 1)
        journal (atom {}) outcome (atom nil) filesystem-effects (atom 0)
        worker (Thread. (fn [] (try (compiler/compile! token "never-resolve-this-project" journal)
                                   (reset! outcome :unexpected-success)
                                   (catch Throwable error (reset! outcome error)))))
        state {:lock lock}]
    (.setDaemon worker true)
    (locking registry (.put registry token state))
    (try
      (with-redefs-fn
        {#'compiler/issued (fn [actual]
                            (let [value (original-issued actual)]
                              (when (and (identical? actual token) (identical? worker (Thread/currentThread)))
                                (.countDown captured)) value))
         #'compiler/path! (fn [_] (swap! filesystem-effects inc)
                           (throw (ex-info "Model reached forbidden post-close filesystem effect" {})))}
        (fn []
          (locking lock
            (.start worker)
            (is (.await captured 2 java.util.concurrent.TimeUnit/SECONDS))
            ;; Reentrant close wins while the compile thread has captured the
            ;; old registry state but is still waiting on the same monitor.
            (is (nil? (compiler/close! token))))
          (.join worker 2000)
          (is (not (.isAlive worker)))
          (is (zero? @filesystem-effects))
          (is (= {} @journal))
          (is (instance? clojure.lang.ExceptionInfo @outcome))
          (is (= "Actual configured internal Compiler required" (.getMessage ^Throwable @outcome)))
          (is (locking registry (not (.containsKey registry token))))))
      (finally (locking registry (.remove registry token))))))
(deftest missing-live-rss-is-resampled-with-a-strict-bound-and-diagnostics
  (let [process (ProcessHandle/current)
        missing "Name:\tfirst\nState:\tR (running)\n"
        valid "State:\tR (running)\nVmRSS:\t321 kB\n"
        dead "State:\tZ (zombie)\n"
        latest "Name:\tlast\nState:\tS (sleeping)\n"
        observe (fn [texts]
                  (let [calls (atom 0)]
                    (with-redefs-fn {#'compiler/proc-text! (fn [_] (nth texts (min (dec (swap! calls inc)) (dec (count texts)))))
                                    #'compiler/pause-rss-sample! (fn [] nil)}
                      #(try {:rss (#'compiler/handle-rss-kib process) :calls @calls}
                            (catch clojure.lang.ExceptionInfo error {:error error :calls @calls})))))]
    (is (= {:rss 321 :calls 2} (observe [missing valid])))
    (is (= {:rss 0 :calls 2} (observe [missing dead])))
    (let [{:keys [error calls]} (observe [missing missing latest])]
      (is (= 3 calls))
      (is (= 3 (:status-samples (ex-data error))))
      (is (= missing (:first-status (ex-data error))))
      (is (= latest (:latest-status (ex-data error))))
      (is (:rss-unavailable (ex-data error))))))
(deftest interrupted-rss-resampling-preserves-interruption
  (let [prior (Thread/interrupted)]
    (try
      (with-redefs-fn {#'compiler/proc-text! (fn [_] "State:\tR (running)\n")}
        #(do (.interrupt (Thread/currentThread))
             (let [error (try (#'compiler/handle-rss-kib (ProcessHandle/current))
                              nil (catch InterruptedException e e))
                   interrupted (.isInterrupted (Thread/currentThread))]
               (Thread/interrupted)
               (is (instance? InterruptedException error))
               (is interrupted))))
      (finally (Thread/interrupted) (when prior (.interrupt (Thread/currentThread)))))))
(defn check! [workspace]
  (binding [*directory* (.toRealPath (.toPath (io/file (str workspace))) (make-array java.nio.file.LinkOption 0))]
    (run-tests 'native-project-compiler-models-v1)))

(deftest disappearing-proc-read-ioexception-rechecks-liveness-without-native-retry
  (let [dead (reify ProcessHandle (pid [_] 99999999) (isAlive [_] false))
        live (ProcessHandle/current)]
    (with-redefs-fn {#'compiler/proc-text! (fn [_] (throw (java.io.IOException. "No such process")))
                    #'compiler/pause-rss-sample! (fn [] nil)}
      #(do (is (zero? (#'compiler/sample-handle-rss-kib dead)))
           (let [error (try (#'compiler/handle-rss-kib live) nil (catch clojure.lang.ExceptionInfo e e))]
             (is (= 3 (:status-samples (ex-data error))))
             (is (:rss-unavailable (ex-data error)))
             (is (:status-unavailable (ex-data error)))
             (is (= "java.io.IOException" (:read-failure-class (ex-data error))))
             (is (instance? java.io.IOException (.getCause ^Throwable (.getCause ^Throwable error)))))))
    (let [calls (atom 0)]
      (with-redefs-fn {#'compiler/proc-text! (fn [_] (if (= 1 (swap! calls inc))
                                                    (throw (java.io.IOException. "No such process"))
                                                    "State:\tR (running)\nVmRSS:\t321 kB\n"))
                      #'compiler/pause-rss-sample! (fn [] nil)}
        #(do (is (= 321 (#'compiler/handle-rss-kib live))) (is (= 2 @calls)))))))
