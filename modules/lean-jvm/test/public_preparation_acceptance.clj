;; Explicit native integration gate; invoke from modules/lean-jvm against the built SDK JAR.
;; Arguments: pinned Lean sysroot, current producer bundle, new empty output directory.
(require '[ansatz.lean.jvm :as lean] '[clojure.java.io :as io]
         '[clojure.data.json :as json] '[clojure.string :as str]
         '[ansatz.lean.jvm.compiler.evidence :as evidence])
(import '[ansatz.lean.jvm LeanPreparation PreparedArtifact ProjectOptions NativeCompilerOptions LeanChoice]
        '[java.io ByteArrayOutputStream ByteArrayInputStream]
        '[java.nio.file Path Files])
(assert (= "jar" (.getProtocol (io/resource "ansatz/lean/jvm.clj"))))
(assert (= 3 (count *command-line-args*)))
(def output (io/file (nth *command-line-args* 2)))
(assert (not (.exists output)) "Acceptance output must be new")
(.mkdirs output)
(def checks (atom 0))
(defn check [value] (swap! checks inc) (assert value))
(def source (io/file output "source"))
(.mkdirs source)
(spit (io/file source "Helper.lean") "def bump (n : Nat) : Nat := n + 1\n")
(spit (io/file source "Main.lean")
      (str "import Helper\n"
           (str/join "\n" (for [i (range 32)] (str "def f" i " (n : Nat) : Nat := bump n + " i)))
           "\ndef mixed (v : Sum (Option Unit) (Unit × Option Unit)) := v\n"
           "def mixedExcept (v : Except String (Option Unit)) := v\n"
           "def main : IO Unit := IO.println \"main-must-not-run\"\n"))
(def names (conj (mapv #(str "f" %) (range 32)) "main" "mixed" "mixedExcept"))
(def options {:compiler {:sysroot (first *command-line-args*)
                         :producer-bundle (second *command-line-args*)
                         :cache (.getPath (io/file output "cache"))}
              :entries names})
(def java-options (lean/project-options options))
(def closed? (atom false))
(def buffer (proxy [ByteArrayOutputStream] [] (close [] (reset! closed? true))))
;; Preparation must neither create a runtime nor invoke guest startup/main.
(def real-build evidence/build!)
(def artifact
  (with-redefs [evidence/build! (fn [& args]
                                (try (apply real-build args)
                                     (catch Throwable failure
                                       ;; Observe the actual failed producer without replacing its
                                       ;; result, receipt or byte custody. Keep only bounded reasons.
                                       (spit (io/file output "native-failure.json")
                                         (json/write-str
                                           (loop [cause failure reasons []]
                                             (if (or (nil? cause) (= 8 (count reasons))) reasons
                                               (let [text (or (.getMessage cause) "")]
                                                 (recur (.getCause cause)
                                                   (conj reasons {:category (.getName (class cause))
                                                                  :message (subs text 0 (min 2048 (count text)))})))))))
                                       (throw failure))))]
    (LeanPreparation/prepareProject (.toPath source) java-options buffer)))
(check (instance? PreparedArtifact artifact))
(doseq [namespace ['ansatz.lean.jvm.project 'ansatz.lean.jvm.ir
                   'ansatz.lean.jvm.startup 'ansatz.lean.jvm.publisher]]
  (check (nil? (find-ns namespace))))
(check (not @closed?))
(check (= 64 (count (.manifestSHA256 artifact))))
(check (= 64 (count (.archiveSHA256 artifact))))
(def bytes (.toByteArray buffer))
(check (pos? (alength bytes)))
(with-open [runtime (lean/open)
            input (ByteArrayInputStream. bytes)
            project (lean/load-artifact runtime input (.manifestSHA256 artifact))]
  (doseq [i (range 32)] (check (= (+ 43 i) (lean/call project (str "f" i) 42))))
  (check (= {:left {:some nil}} (lean/call project "mixed" (LeanChoice/left {:some nil}))))
  (check (= {:right [nil {:some nil}]} (lean/call project "mixed" (LeanChoice/right [nil {:some nil}]))))
  (check (= {:ok {:some nil}} (lean/call project "mixedExcept" (LeanChoice/right {:some nil}))))
  (check (= {:value nil :stdout "main-must-not-run\n" :stderr ""}
            (lean/call project "main"))))
;; Clojure facade independently prepares the same cached sources using an owned output.
(def clj-output (io/file output "prepared.zip"))
(def description
  (with-open [stream (io/output-stream clj-output)]
    (lean/prepare-project (.getPath source) options stream)))
(check (= 64 (count (:manifest-sha256 description))))
(check (= 64 (count (:archive-sha256 description))))
(with-open [runtime (lean/open)
            input (io/input-stream clj-output)
            project (lean/load-artifact runtime input (:manifest-sha256 description))]
  (check (= 75 (lean/call project "f31" 43))))
(spit (io/file output "result.json")
      (json/write-str {:status "pass" :checks @checks :selectedEntries (count names)
                       :manifestSHA256 (.manifestSHA256 artifact)
                       :archiveSHA256 (.archiveSHA256 artifact)}))
(println :public-preparation-acceptance {:checks @checks :selected-entries (count names)})
