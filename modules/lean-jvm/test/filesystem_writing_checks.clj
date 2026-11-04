(ns ansatz-lean-jvm-filesystem-writing-checks
  "Native-free writer artifact policy and custody checks. Scheduler instrumentation
   observes actual provider effects; it is not a public cancellation API."
  (:require [clojure.test :refer [deftest is run-tests]] [clojure.java.io :as io]
            [ansatz.lean.jvm :as lean] [ansatz.lean.jvm.project :as project]
            [ansatz.lean.jvm.startup :as startup] [ansatz.lean.jvm.ir :as ir])
  (:import [ansatz.lean.jvm HostServices FileAccess ReadOnlyFiles LeanException]
           [java.nio.file Path Files] [java.nio.file.attribute FileAttribute]))
(def ^:dynamic *module-root* ".")
(def writer-manifest "891fb3a54939a179033d8edc2bb32ece69e5be2f7f55d24119b063cdcac378f7")
(def feline-manifest "addd36008695cd8494e47eaf8495baff89631621272fbb4aabb736bfdd59335d")
(def input-text "hello é\u0000雪\n")
(defn- invoke-zero [value method]
  (.invoke (.getMethod (class value) method (make-array Class 0)) value (object-array 0)))
(defn- quarantine-count [] (count @(var-get (ns-resolve 'ansatz.lean.jvm.project 'quarantine))))
(defn- artifact [name] (io/file *module-root* (str "consumer/resources/lean/" name ".zip")))
(defn- with-root [f]
  (let [parent (.toPath (io/file *module-root* "temp_files"))
        _ (Files/createDirectories parent (make-array FileAttribute 0))
        root (.toAbsolutePath (Files/createTempDirectory parent "writer-check-" (make-array FileAttribute 0)))]
    (try
      (Files/writeString (.resolve root "input.txt") input-text (make-array java.nio.file.OpenOption 0))
      (f root)
      (finally
        (Thread/interrupted)
        (with-open [paths (Files/walk root (make-array java.nio.file.FileVisitOption 0))]
          (doseq [^Path file (reverse (sort-by #(.getNameCount ^Path %) (iterator-seq (.iterator paths))))]
            (Files/deleteIfExists file)))))))
(defn- failure [f] (try (f) nil (catch LeanException e e)))
(defn- expected-code [code f]
  (let [e (failure f)]
    (is (instance? LeanException e))
    (when e (is (= code (.code ^LeanException e))) (is (nil? (.getCause ^LeanException e))))))
(defn- observe-drive [original observation]
  (fn [ctx engine callable args slot host-calls options]
    (swap! observation assoc :session (#'startup/engine-field engine "fileSession"))
    (original ctx engine callable args slot host-calls options)))
(defn- closed-session [observation]
  (let [session (:session @observation)]
    (is (some? session))
    (when session
      (let [stats (invoke-zero session "stats")]
        (is (.closed stats)) (is (zero? (.liveHandles stats)))
        (is (= (.opened stats) (.closeAttempts stats))) stats))))
(defn- healthy-reader [runtime]
  (with-open [input (io/input-stream (artifact "feline"))
              peer (lean/load-artifact runtime input feline-manifest)]
    (let [r (lean/call peer "main" ["input.txt"])]
      (is (= 0 (:value r))) (is (= input-text (:stdout r))) (is (= "" (:stderr r))))))

(deftest writer-artifact-needs-an-explicit-service-before-startup
  (with-root
    (fn [root]
      (with-open [runtime (lean/open) input (io/input-stream (artifact "writer"))]
        (expected-code "CapabilityMissing" #(lean/load-artifact runtime input writer-manifest)))
      (is (not (Files/exists (.resolve root "output.txt") (make-array java.nio.file.LinkOption 0)))))))

(deftest read-only-policy-refuses-writing-before-output-creation
  (with-root
    (fn [root]
      (let [before (quarantine-count) observations (atom {})
            drive (ns-resolve 'ansatz.lean.jvm.project 'drive!) original (var-get drive)
            services (.build (.files (HostServices/builder) (ReadOnlyFiles/root root)))]
        (with-open [runtime (lean/open services)]
          (with-open [input (io/input-stream (artifact "writer"))
                      loaded (lean/load-artifact runtime input writer-manifest)]
            (with-redefs-fn {drive (observe-drive original observations)}
              #(expected-code "FilesystemPolicy" (fn [] (lean/call loaded "main" ["input.txt" "denied.txt"])))))
          (let [stats (closed-session observations)] (when stats (is (zero? (.bytesWritten stats)))))
          (is (not (Files/exists (.resolve root "denied.txt") (make-array java.nio.file.LinkOption 0))))
          (healthy-reader runtime))
        (is (= before (quarantine-count)))))))

(deftest physical-write-budget-keeps-open-side-effects-and-retires-the-session
  (doseq [preexisting [false true]]
    (with-root
      (fn [root]
        (when preexisting (Files/writeString (.resolve root "limited.txt") "old bytes" (make-array java.nio.file.OpenOption 0)))
        (let [before (quarantine-count) observations (atom {})
              drive (ns-resolve 'ansatz.lean.jvm.project 'drive!) original (var-get drive)
              config (.writeLimits (FileAccess/readWrite root) 1048576 0)
              services (.build (.fileAccess (HostServices/builder) config))]
          (with-open [runtime (lean/open services)]
            (with-open [input (io/input-stream (artifact "writer"))
                        loaded (lean/load-artifact runtime input writer-manifest)]
              (with-redefs-fn {drive (observe-drive original observations)}
                #(expected-code "ResourceLimit" (fn [] (lean/call loaded "main" ["input.txt" "limited.txt"])))))
            ;; .write open creates/truncates before putStr's physical-write admission.
            (is (Files/exists (.resolve root "limited.txt") (make-array java.nio.file.LinkOption 0)))
            (is (zero? (Files/size (.resolve root "limited.txt"))))
            (let [stats (closed-session observations)]
              (when stats (is (zero? (.bytesWritten stats))) (is (pos? (.opened stats)))))
            (healthy-reader runtime))
          (is (= before (quarantine-count))))))))

(defn- cancel-after-physical-write [observations]
  (fn [ctx engine callable args slot host-calls options]
    (assert (empty? host-calls))
    (#'project/deadline! engine (.timeBudgetNanos ^ansatz.lean.jvm.InvocationOptions options))
    (aset ^objects slot 1 :start-pending)
    (ir/start! ctx engine callable args)
    (aset ^objects slot 0 nil) (aset ^objects slot 1 :running)
    (try
      (loop [left 100000]
        (when (zero? left) (throw (AssertionError. "No writable live handle within scheduler bound")))
        (let [stats (invoke-zero engine "fileStats")]
          (if (and (pos? (.bytesWritten stats)) (pos? (.liveHandles stats)))
            (swap! observations assoc :before stats :session (#'startup/engine-field engine "fileSession"))
            (do
              (when-not (= "running" (ir/phase ctx engine))
                (throw (AssertionError. "Writer completed before physical-write cancellation point")))
              (ir/advance! ctx engine 1) (recur (dec left))))))
      (.interrupt (Thread/currentThread))
      (dotimes [_ 100000] (ir/advance! ctx engine 1))
      (throw (AssertionError. "Interrupted writer did not cancel"))
      (finally
        (swap! observations assoc :interrupt-observed (.isInterrupted (Thread/currentThread)))
        (Thread/interrupted)))))

(deftest cancellation-after-physical-output-retains-bytes-and-retires-custody
  (with-root
    (fn [root]
      (let [before (quarantine-count) observations (atom {})
            drive (ns-resolve 'ansatz.lean.jvm.project 'drive!)
            services (.build (.fileAccess (HostServices/builder) (FileAccess/readWrite root)))]
        (with-open [runtime (lean/open services)]
          (with-open [input (io/input-stream (artifact "writer"))
                      loaded (lean/load-artifact runtime input writer-manifest)]
            (with-redefs-fn {drive (cancel-after-physical-write observations)}
              #(expected-code "Cancelled" (fn [] (lean/call loaded "main" ["input.txt" "cancel.txt"])))))
          (is (true? (:interrupt-observed @observations)))
          (let [stats (closed-session observations) prior (:before @observations)]
            (is (some? prior))
            (when (and stats prior)
              (is (pos? (.liveHandles prior))) (is (pos? (.bytesWritten prior)))
              (is (= (.bytesWritten prior) (.bytesWritten stats)))
              (is (= (.bytesWritten stats) (Files/size (.resolve root "cancel.txt"))))))
          (is (= (str "processed\n" input-text) (Files/readString (.resolve root "cancel.txt"))))
          (healthy-reader runtime))
        (is (= before (quarantine-count)))))))
(defn check!
  ([] (check! "."))
  ([module-root] (binding [*module-root* module-root] (run-tests 'ansatz-lean-jvm-filesystem-writing-checks))))
