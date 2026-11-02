;; Load in a fresh namespace of the retained packaged-SDK REPL. No processes or
;; projects start on load. Invoke source!/native! separately and retain receipts.
(require '[ansatz.lean.jvm :as lean] '[ansatz.lean.jvm.compiler.evidence :as evidence]
         '[clojure.java.io :as io])
(import '[java.util.concurrent TimeUnit])

(defn demand! [ok facts]
  (when-not ok (throw (ex-info "Installed import acceptance differs" facts))))
(defn options [compiler]
  {:compiler compiler :root-module "phashmap_alter"
   :installed-imports ["Lean.Data.PersistentHashMap"] :entries ["main"]})
(def expected {:value nil :stdout "OK\n" :stderr ""})
(defn check-project! [project]
  (let [main (lean/function project "main") results [(main) (main)]]
    (doseq [result results] (demand! (= expected result) {:result result})) results))

(defn source!
  "Public source load, retained handles, cache reuse, artifact preparation/load.
   Returns actual evidence summaries, never calls the native reference main.
   Caller owns runtime; pass a new artifact path and explicit compiler cache."
  [runtime compiler source-directory artifact-path]
  (let [output (io/file artifact-path) receipts (atom []) original evidence/build!]
    (demand! (not (.exists output)) {:reason :fresh-artifact-path})
    (io/make-parents output)
    (with-redefs [evidence/build!
                  (fn [compiler configuration evidence-options entries journal]
                    (let [receipt (original compiler configuration evidence-options entries journal)
                          payload (evidence/authenticated-build receipt)]
                      (swap! receipts conj
                        {:cache-key (:module-cache-key payload) :cache-hit (:cache-hit @journal)
                         :installed-products (get-in payload [:build-inputs "installedImports"])
                         :module-order (get-in payload [:startup "moduleOrder"])
                         :externs (vec (keep #(get-in % ["ir" "extern"]) (vals (:rows payload))))})
                      receipt))]
      (with-open [project (lean/load-project runtime source-directory (options compiler))]
        (check-project! project))
      (with-open [project (lean/load-project runtime source-directory (options compiler))]
        (check-project! project))
      (let [description (with-open [stream (io/output-stream output)]
                          (lean/prepare-project source-directory (options compiler) stream))]
        (with-open [stream (io/input-stream output)
                    project (lean/load-artifact runtime stream (:manifest-sha256 description))]
          (check-project! project))
        (demand! (= 1 (count (set (map :cache-key @receipts)))) {:reason :cache-key-changed :receipts @receipts})
        (demand! (every? :cache-hit (rest @receipts)) {:reason :cache-miss :receipts @receipts})
        {:status :source-cache-artifact-pass :expected expected
         :artifact description :receipts @receipts}))))

(defn native!
  "Explicit independent official executable --run reference. Source preparation
   success alone is not a native differential receipt. Use a fresh receipt dir."
  [sysroot source-directory output-directory]
  (let [output (.getCanonicalFile (io/file output-directory))
        source (.getCanonicalFile (io/file source-directory))
        executable (.getCanonicalPath (io/file sysroot "bin/lean"))
        stdout (io/file output "native.stdout") stderr (io/file output "native.stderr")
        command [executable "-j1" "-M512" "--run" "phashmap_alter.lean"]]
    (demand! (not (.exists output)) {:reason :fresh-native-directory})
    (demand! (.mkdirs output) {:reason :create-native-directory})
    (let [builder (doto (ProcessBuilder. ^java.util.List command)
                    (.directory source) (.redirectOutput stdout) (.redirectError stderr))
          _ (.remove (.environment builder) "LEAN_PATH")
          _ (.put (.environment builder) "LEAN_SYSROOT" (.getCanonicalPath (io/file sysroot)))
          process (.start builder)]
      (when-not (.waitFor process 60 TimeUnit/SECONDS)
        (.destroyForcibly process)
        (throw (ex-info "Native reference timeout" {})))
      (let [result {:exit (.exitValue process) :stdout (slurp stdout) :stderr (slurp stderr)}]
        (spit (io/file output "native.edn") (pr-str {:command command :result result}))
        (demand! (= {:exit 0 :stdout "OK\n" :stderr ""} result) result)
        result))))

(defn compare-native! [source-result native-result]
  (demand! (and (= :source-cache-artifact-pass (:status source-result))
                (= {:exit 0 :stdout "OK\n" :stderr ""} native-result)
                (= expected (:expected source-result)))
    {:source source-result :native native-result})
  {:status :native-source-cache-artifact-pass :native native-result :artifact (:artifact source-result)})
