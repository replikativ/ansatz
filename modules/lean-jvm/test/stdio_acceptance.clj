;; Explicit native differential/source/artifact gate; safe to load in a retained
;; REPL under a separate namespace. No downloads or runtime namespace reloading.
(require '[ansatz.lean.jvm :as lean] '[clojure.java.io :as io]
         '[clojure.data.json :as json])
(import '[java.nio.charset StandardCharsets]
        '[java.util Arrays] '[java.util.concurrent TimeUnit]
        '[ansatz.lean.jvm InvocationOptions LeanException])
(assert (= "jar" (.getProtocol (io/resource "ansatz/lean/jvm.clj"))))
(assert (= 3 (count *command-line-args*)))
(def sysroot (first *command-line-args*))
(def bundle (second *command-line-args*))
(def output (io/file (nth *command-line-args* 2)))
(assert (not (.exists output)) "Use a new output directory")
(.mkdirs output)
(def compiler {:sysroot sysroot :producer-bundle bundle :cache (.getPath (io/file output "cache"))})
(def checks (atom 0))
(def observations (atom []))
(defn check [ok] (swap! checks inc) (assert ok))
(defn utf8 [s] (.getBytes ^String s StandardCharsets/UTF_8))
(defn bytes= [a b] (Arrays/equals ^bytes a ^bytes b))
(defn native! [id source input arguments]
  (let [in (io/file output (str id ".stdin")) out (io/file output (str id ".stdout"))
        err (io/file output (str id ".stderr"))
        command (into ["/usr/bin/prlimit" "--cpu=60:60" "--"
                       (str sysroot "/bin/lean") "-j1" "-M512" "--run"
                       (.getAbsolutePath (io/file source))] arguments)
        _ (with-open [stream (io/output-stream in)] (.write stream ^bytes input))
        builder (doto (ProcessBuilder. ^java.util.List command)
                  (.redirectInput in) (.redirectOutput out) (.redirectError err))
        start (System/nanoTime) process (.start builder)]
    (when-not (.waitFor process 60 TimeUnit/SECONDS)
      (.destroyForcibly process) (throw (ex-info "Native reference timeout" {:case id})))
    (let [result {:exit (.exitValue process)
                  :stdout (java.nio.file.Files/readAllBytes (.toPath out))
                  :stderr (java.nio.file.Files/readAllBytes (.toPath err))}]
      (swap! observations conj {:id id :native-exit (:exit result)
                                :native-ms (/ (- (System/nanoTime) start) 1e6)
                                :stdout-bytes (alength ^bytes (:stdout result))
                                :stderr-bytes (alength ^bytes (:stderr result))}) result)))
(defn compare-program! [project id source input arguments io-unit?]
  (let [reference (native! id source input (if io-unit? [] (first arguments)))
        result (apply lean/call-with-options project "main" {:stdin-bytes input} arguments)]
    (check (= (if io-unit? nil (:exit reference)) (:value result)))
    (when io-unit? (check (zero? (:exit reference))))
    (check (bytes= (:stdout reference) (:stdout-bytes result)))
    (check (bytes= (:stderr reference) (:stderr-bytes result)))))
(def upstream "examples/fp-lean-io")
(with-open [runtime (lean/open)]
  (with-open [project (lean/load-project runtime upstream
                       {:compiler compiler :root-module "HelloName" :entries ["main"]})]
    (doseq [[id input] [["hello-lf" "Ada\n"] ["hello-crlf" "Grace\r\n"]
                        ["hello-empty" ""] ["hello-nul" "A\u0000B\n"]]]
      (compare-program! project id (str upstream "/HelloName.lean") (utf8 input) [] true)))
  (with-open [project (lean/load-project runtime upstream
                       {:compiler compiler :root-module "EarlyReturn" :entries ["main" "Nested.main"]})]
    (doseq [[id input arguments] [["early-ok" "Ada\n" []]
                                  ["early-empty" "" []]
                                  ["early-args" "ignored\n" ["extra"]]]]
      (compare-program! project id (str upstream "/EarlyReturn.lean") (utf8 input) [arguments] false))
    (check (= (dissoc (lean/call-with-options project "main" {:stdin "Ada\n"} []) :stdout-bytes :stderr-bytes)
              (dissoc (lean/call-with-options project "Nested.main" {:stdin "Ada\n"} []) :stdout-bytes :stderr-bytes))))
  (with-open [project (lean/load-project runtime upstream
                       {:compiler compiler :root-module "ForMIO" :entries ["main"]})]
    (compare-program! project "filter-lines" (str upstream "/ForMIO.lean") (utf8 "123\nabc\n456\nλ\n") [[]] false)
    (compare-program! project "filter-args" (str upstream "/ForMIO.lean") (utf8 "ignored\n") [["extra"]] false))
  (let [source "consumer/resources/lean/stdio-source"
        options {:compiler compiler :root-module "Main"
                 :entries ["readBytes" "readLine" "echoBytes" "splitUtf8" "invalidUtf8"
                           "wrongDirectionCaught" "message" "errorMessage"]}]
    (with-open [project (lean/load-project runtime source options)]
      (doseq [[id input] [["line-lf" (utf8 "α\nrest")]
                          ["line-crlf" (utf8 "a\r\nrest")]
                          ["line-eof" (byte-array 0)]
                          ["line-nul" (byte-array [65 0 66 10 67])]
                          ["line-invalid" (byte-array [-64 -128 65 -16 -97 10])]]]
        (let [reference (native! id (str source "/LineOracle.lean") input [])
              result (lean/call-with-options project "readLine" {:stdin-bytes input})]
          (check (zero? (:exit reference)))
          (check (bytes= (:stdout reference) (utf8 (:value result))))
          (check (zero? (alength ^bytes (:stderr reference))))))
      (let [input (byte-array [0 -64 -128 -16 -97 -104 -128 10])
            reference (native! "byte-echo" (str source "/Main.lean") input [])
            result (lean/call-with-options project "echoBytes" {:stdin-bytes input})]
        (check (zero? (:exit reference)))
        (check (bytes= (:stdout reference) (:stdout-bytes result))))
      (check (= "😀" (:stdout (lean/call-with-options project "splitUtf8" {}))))
      (check (= [-64 -128] (vec (:stdout-bytes (lean/call-with-options project "invalidUtf8" {})))))
      (check (true? (:value (lean/call-with-options project "wrongDirectionCaught" {}))))
      (let [input (byte-array [1 2 3])
            function (lean/function project "readBytes" {:stdin-bytes input})]
        (aset-byte input 0 (byte 9))
        (check (= [1 2 3] (vec (:value (function 32)))))
        (check (= [1 2 3] (vec (:value (function 32))))))
      (try (lean/call-with-options project "message" {:stdin "x" :stdin-bytes (byte-array 0)})
           (throw (AssertionError. "Expected invalid options"))
           (catch clojure.lang.ExceptionInfo e (check (= "InvalidArgument" (:code (ex-data e))))))
      (check (= "hello\n" (:stdout (lean/call project "message"))))
      (let [description (with-open [out (io/output-stream (io/file output "stdio.zip"))]
                          (lean/prepare-project source options out))]
        (spit (io/file output "stdio.json") (json/write-str description))
        (with-open [in (io/input-stream (io/file output "stdio.zip"))
                    loaded (lean/load-artifact runtime in (:manifest-sha256 description))]
          (check (= "Ada\n" (:value (lean/call-with-options loaded "readLine" {:stdin "Ada\n"})))))))
    (with-open [limited (lean/load-project runtime source options)]
      (try (lean/call-with-options limited "message" {:stdout-limit-bytes 5})
           (throw (AssertionError. "Expected output limit"))
           (catch LeanException e (check (= "ResourceLimit" (.code e)))))))
  ;; A native source result type alone cannot certify payload provenance through
  ;; unsafe implementation replacements. Keep both source/artifact paths strict.
  (let [options {:compiler compiler :root-module "UnsafeResult" :entries ["checked" "traceChecked"]}
        source "consumer/resources/lean/sharing-boundary-source"]
    (try (lean/load-project runtime source options)
         (throw (AssertionError. "Expected projection refusal"))
         (catch LeanException e (check (= "CapabilityMissing" (.code e)))))
    (let [description (with-open [out (io/output-stream (io/file output "unsafe-result.zip"))]
                        (lean/prepare-project source options out))]
      (with-open [in (io/input-stream (io/file output "unsafe-result.zip"))]
        (try (lean/load-artifact runtime in (:manifest-sha256 description))
             (throw (AssertionError. "Expected artifact projection refusal"))
             (catch LeanException e (check (= "CapabilityMissing" (.code e)))))))))
(def report {:status "pass" :checks @checks :native-cases @observations})
(spit (io/file output "result.json") (json/write-str report))
(println "PASS STDIO_ACCEPTANCE" {:checks @checks :native-cases (count @observations)})
