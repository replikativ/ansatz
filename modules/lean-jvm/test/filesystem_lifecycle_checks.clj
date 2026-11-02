(ns ansatz-lean-jvm-filesystem-lifecycle-checks
  "Native-free public Feline artifact lifecycle with a trusted test scheduler.
   Redefining private drive! is instrumentation, not a public cancellation hook."
  (:require [clojure.test :refer [deftest is run-tests]] [clojure.java.io :as io]
            [ansatz.lean.jvm :as lean] [ansatz.lean.jvm.project :as project]
            [ansatz.lean.jvm.startup :as startup] [ansatz.lean.jvm.ir :as ir])
  (:import [ansatz.lean.jvm HostServices ReadOnlyFiles LeanException]
           [java.nio.file Path Files] [java.nio.file.attribute FileAttribute]))

(def ^:dynamic *module-root* ".")
(def manifest "addd36008695cd8494e47eaf8495baff89631621272fbb4aabb736bfdd59335d")
(defn invoke-zero [value method]
  (.invoke (.getMethod (class value) method (make-array Class 0)) value (object-array 0)))
(defn quarantine-count [] (count @(var-get (ns-resolve 'ansatz.lean.jvm.project 'quarantine))))
(defn cancel-after-open [observations]
  (fn [ctx engine callable args slot]
    (#'project/deadline! engine)
    (aset ^objects slot 1 :start-pending)
    (ir/start! ctx engine callable args)
    ;; Match the real driver's ownership adoption after successful start.
    (aset ^objects slot 0 nil) (aset ^objects slot 1 :running)
    (try
      (loop [left 10000]
        (when (zero? left) (throw (AssertionError. "No open Feline handle within scheduler bound")))
        (let [stats (invoke-zero engine "fileStats")]
          (if (= 1 (.liveHandles stats))
            (swap! observations assoc :before stats :session (#'startup/engine-field engine "fileSession"))
            (do
              (when-not (= "running" (ir/phase ctx engine))
                (throw (AssertionError. "Feline completed before the open-handle cancellation point")))
              (ir/advance! ctx engine 1) (recur (dec left))))))
      (.interrupt (Thread/currentThread))
      ;; The next body instruction need not poll; keep real one-step dispatch
      ;; until a provider/runtime poll observes interruption and throws.
      (dotimes [_ 10000] (ir/advance! ctx engine 1))
      (throw (AssertionError. "Actual interrupted Feline engine did not cancel"))
      (finally
        (swap! observations assoc :interrupt-observed (.isInterrupted (Thread/currentThread)))
        (Thread/interrupted)))))

(deftest interrupted-public-feline-retires-the-real-open-resource
  (let [parent (.toPath (io/file *module-root* "temp_files"))
        _ (Files/createDirectories parent (make-array FileAttribute 0))
        root (.toAbsolutePath (Files/createTempDirectory parent "feline-cancel-" (make-array FileAttribute 0)))
        observations (atom {}) before (quarantine-count)
        drive (ns-resolve 'ansatz.lean.jvm.project 'drive!)]
    (Thread/interrupted)
    (try
      (Files/write (.resolve root "input.bin") (byte-array (repeat 4096 (byte 65)))
        (make-array java.nio.file.OpenOption 0))
      (let [services (.build (.files (HostServices/builder) (ReadOnlyFiles/root root)))
            artifact (io/file *module-root* "consumer/resources/lean/feline.zip")]
        (with-open [runtime (lean/open services)]
          (with-open [input (io/input-stream artifact)
                      loaded (lean/load-artifact runtime input manifest)]
            (let [failure (with-redefs-fn {drive (cancel-after-open observations)}
                            #(try (lean/call-with-options loaded "main" {:stdin-bytes (byte-array 0)} ["input.bin"])
                                  nil (catch LeanException failure failure)))]
              (is (instance? LeanException failure))
              (when failure (is (= "Cancelled" (.code ^LeanException failure))))
              (is (true? (:interrupt-observed @observations)))))
          ;; Public Project.close has now run through the ordinary coordinator.
          (let [session (:session @observations) prior (:before @observations)]
            (is (some? session))
            (when session
              (let [stats (invoke-zero session "stats")]
                (is (= 1 (.liveHandles prior))) (is (= 1 (.opened prior)))
                (is (zero? (.closeAttempts prior)))
                (is (.closed stats)) (is (zero? (.liveHandles stats)))
                (is (= 1 (.closeAttempts stats))))))))
      (is (= before (quarantine-count)))
      (finally
        ;; Observe the real flag in the scheduler, then leave the retained REPL usable.
        (Thread/interrupted)
        (with-open [paths (Files/walk root (make-array java.nio.file.FileVisitOption 0))]
          (doseq [path (reverse (sort-by #(.getNameCount ^Path %) (iterator-seq (.iterator paths))))]
            (Files/deleteIfExists path)))))))

(defn check!
  ([] (check! "."))
  ([module-root] (binding [*module-root* module-root] (run-tests 'ansatz-lean-jvm-filesystem-lifecycle-checks))))
