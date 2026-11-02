;; Explicit producer gate. Run from modules/lean-jvm with SDK JAR, test helpers,
;; and ordinary runtime dependencies on the classpath; never downloads a toolchain.
(require '[ansatz.lean.jvm :as lean] '[ansatz.lean.jvm.artifact :as artifact]
         '[ansatz.lean.jvm.compiler.evidence :as evidence]
         '[ansatz.lean.jvm.compiler.local :as local]
         '[clojure.java.io :as io] '[clojure.data.json :as json])
(import '[java.nio.file Path Files] '[ansatz.lean.jvm LeanException])
(assert (= "jar" (.getProtocol (io/resource "ansatz/lean/jvm.clj"))))
(def arguments (vec *command-line-args*))
(assert (= 3 (count arguments)) "Expected: lean-sysroot producer-bundle new-empty-output-directory")
(def output (io/file (nth arguments 2)))
(assert (not (.exists output)) "Source acceptance output must be new")
(.mkdirs output)
(def cache (io/file output "cache"))
(def compiler {:sysroot (first arguments) :producer-bundle (second arguments) :cache (.getPath cache)})
(def checks (atom 0))
(def observations (atom []))
(def receipts (atom []))
(def timings (atom {}))
(defn check [ok] (swap! checks inc) (assert ok))
(defn options [entries] {:compiler compiler :entries entries})
(defn source-dir [name] (.getPath (io/file output name)))
(defn copy-program [source name]
  (let [target (io/file output name)]
    (doseq [file (file-seq (io/file source)) :when (.isFile file)]
      (let [relative (.relativize (.toPath (io/file source)) (.toPath file))
            dest (.toFile (.resolve (.toPath target) relative))]
        (io/make-parents dest) (io/copy file dest))) target))
(defn timed [label f]
  (let [start (System/nanoTime) result (f)]
    (swap! timings assoc label (/ (- (System/nanoTime) start) 1.0e6)) result))
(defn refused [code f]
  (try (f) (throw (AssertionError. "Expected refusal"))
       (catch LeanException error (check (= code (.code error))) (check (nil? (.getCause error))) error)))
(def common-entries (mapv #(str "Demo." %) ["sumArgs" "negate" "greet" "unitIdentity" "constantBool"
                                           "pairIdentity" "pairSecond" "discardList" "reverseList" "optionUnit"
                                           "nestedOption" "pairs" "effect" "main" "other" "emptyList"]))
(def scalar-entries ["extByte" "extSigned" "extDouble" "extSingle" "extChar" "extWord" "extBytes" "extArray"
                     "extSum" "extExcept" "extConstantByte" "extConstantFloat" "extArrayPush" "extBytesPush"
                     "extOtherMachines" "extIO"])
(def build evidence/build!)
(def compile-modules local/compile-modules!)
(with-open [runtime (lean/open)]
  ;; Observe actual issued results without replacing a producer, receipt or bytes.
  (with-redefs [local/compile-modules! (fn [& args] (let [result (apply compile-modules args)]
                                                   (swap! observations conj (select-keys result [:cache-key :cache-hit])) result))
                evidence/build! (fn [& args] (let [receipt (apply build args)] (swap! receipts conj receipt) receipt))]
    (copy-program "consumer/resources/lean/general-interop-source" "common")
    (with-open [old (timed :common-cold #(lean/load-project runtime (source-dir "common") (options common-entries)))
                warm (timed :common-warm #(lean/load-project runtime (source-dir "common") (options common-entries)))]
      (check (= [false true] (mapv :cache-hit @observations)))
      (check (= 42 (lean/call old "Demo.sumArgs" 20 21 true)))
      (check (= 42 (lean/call warm "Demo.sumArgs" 20 21 true)))
      (check (= {:some nil} (lean/call old "Demo.optionUnit" {:some nil})))
      (check (= [3 2 1] (lean/call old "Demo.reverseList" [1 2 3])))
      (check (= {:value {:some ["sum" 42]} :stdout "effect\n" :stderr ""}
                (lean/call old "Demo.effect" true [20 22])))
      (spit (io/file output "common/Helper.lean") "def helperBump (n : Nat) : Nat := n + 2\n")
      (with-open [updated (timed :reload #(lean/load-project runtime (source-dir "common") (options common-entries)))]
        (check (false? (:cache-hit (last @observations))))
        (check (= 43 (lean/call updated "Demo.sumArgs" 20 21 true)))
        (check (= 42 (lean/call old "Demo.sumArgs" 20 21 true)))
        (let [exported (with-open [out (io/output-stream (io/file output "reload.zip"))]
                         (artifact/export! (last @receipts) out))]
          (with-open [in (io/input-stream (io/file output "reload.zip"))
                      project (timed :artifact-load #(lean/load-artifact runtime in (:manifest-sha256 exported)))]
            (check (= 43 (lean/call project "Demo.sumArgs" 20 21 true))))))
      (copy-program "consumer/resources/lean/scalar-interop-source" "scalar")
      (with-open [project (timed :scalar-cold #(lean/load-project runtime (source-dir "scalar") (options scalar-entries)))]
        (check (= 0 (lean/call project "extByte" 255)))
        (check (= -42 (lean/call project "extSigned" 42)))
        (check (= 1.75 (lean/call project "extDouble" 1.25)))
        (check (= (float 16777216) (lean/call project "extSingle" (float 16777216))))
        (check (= [1 2 3] (lean/call project "extArrayPush" [1 2] 3)))
        (check (= [0 -1 42] (vec (lean/call project "extBytesPush" (byte-array [0 -1]) 42))))
        (check (= {:right true} (lean/call project "extSum" {:left true})))
        (check (= 1.5 (lean/call project "extConstantFloat")))
        (check (= {:value {:ok [1.25 2.5]} :stdout "floats\n" :stderr ""}
                  (lean/call project "extIO" [1.25 2.5]))))
      (doseq [[name text] [["warning" "def warningExample (unused : Nat) : Nat := 42\n"]
                           ["error" "def errorExample : Nat := \"not a Nat\"\n"]
                           ["unsupported" "def unsupported : IO Nat := IO.monoMsNow\n"]
                           ["higherOrder" "def higherOrder (f : Nat → Nat) : Nat := f 0\n"]
                           ["highScalars" "def highU64 : UInt64 := 18446744073709551615\ndef negativeI64 : Int64 := Int64.ofUInt64 18446744073709551615\ndef highWord : USize := 18446744073709551615\ndef singleConstant : Float32 := 1.5\n"]]]
        (io/make-parents (io/file output name "Main.lean"))
        (spit (io/file output name "Main.lean") text))
      (with-open [project (lean/load-project runtime (source-dir "warning") (options ["warningExample"]))]
        (check (= 42 (lean/call project "warningExample" 0))))
      (with-open [project (lean/load-project runtime (source-dir "warning") (options ["warningExample"]))]
        (check (true? (:cache-hit (last @observations))))
        (check (= 42 (lean/call project "warningExample" 0))))
      (let [exported (with-open [out (io/output-stream (io/file output "warning.zip"))]
                       (artifact/export! (last @receipts) out))]
        (with-open [in (io/input-stream (io/file output "warning.zip"))
                    project (lean/load-artifact runtime in (:manifest-sha256 exported))]
          (check (= 42 (lean/call project "warningExample" 0)))))
      (let [error (refused "NativeCompilationFailed" #(lean/load-project runtime (source-dir "error") (options ["errorExample"])))]
        (check (.contains (.getMessage error) "error")))
      (refused "CapabilityMissing" #(lean/load-project runtime (source-dir "unsupported") (options ["unsupported"])))
      (refused "NativeCompilationFailed" #(lean/load-project runtime (source-dir "higherOrder") (options ["higherOrder"])))
      (with-open [project (lean/load-project runtime (source-dir "highScalars")
                                           (options ["highU64" "negativeI64" "highWord" "singleConstant"]))]
        (check (= 18446744073709551615N (lean/call project "highU64")))
        (check (= -1 (lean/call project "negativeI64")))
        (check (= 18446744073709551615N (lean/call project "highWord")))
        (check (= (float 1.5) (lean/call project "singleConstant"))))
      (check (= 42 (lean/call old "Demo.sumArgs" 20 21 true))))))
(copy-program "examples/fp-lean-sort" "tutorial-sort")
(copy-program "consumer/resources/lean/sharing-boundary-source" "sharing-boundaries")
(def sort-options {:compiler compiler :root-module "Tutorial"
                   :entries ["Tutorial.sortNats" "Tutorial.sortStrings" "Tutorial.sortAndOriginal"]})
(defn check-sort [project]
  (doseq [n (range 25) :let [xs (vec (reverse (range n)))]]
    (check (= (vec (range n)) (:value (lean/call project "Tutorial.sortNats" xs))))
    (check (= [(vec (range n)) xs] (:value (lean/call project "Tutorial.sortAndOriginal" xs)))))
  (check (= ["a" "β" "\ue000" "😀"]
            (:value (lean/call project "Tutorial.sortStrings" ["😀" "\ue000" "β" "a"]))))
  (check (= "shared RC array to swap\n"
            (:stderr (lean/call project "Tutorial.sortAndOriginal" [3 2 1])))))
(with-open [runtime (lean/open)
            project (timed :tutorial-sort #(lean/load-project runtime (source-dir "tutorial-sort") sort-options))]
  (check-sort project)
  (let [description (with-open [out (io/output-stream (io/file output "tutorial-sort.zip"))]
                      (lean/prepare-project (source-dir "tutorial-sort") sort-options out))]
    (with-open [input (io/input-stream (io/file output "tutorial-sort.zip"))
                loaded (lean/load-artifact runtime input (:manifest-sha256 description))]
      (check-sort loaded)))
  (doseq [entry ["debugString" "debugNat"]
          :let [config {:compiler compiler :root-module "Boundary" :entries [entry]}]]
    (with-open [loaded (lean/load-project runtime (source-dir "sharing-boundaries") config)]
      (when (= entry "debugNat")
        (check (= 42 (:value (lean/call loaded entry 42)))))
      (refused "RuntimeBoundary" #(lean/call loaded entry
                                    (if (= entry "debugString") "leaf" (.shiftLeft java.math.BigInteger/ONE 80)))))
    ;; Source and artifact calls enforce the same actual-value domain. Entry
    ;; admission does not promise all runtime paths/values are supported.
    (let [archive (io/file output (str entry ".zip"))
          description (with-open [out (io/output-stream archive)]
                        (lean/prepare-project (source-dir "sharing-boundaries") config out))]
      (with-open [input (io/input-stream archive)
                  loaded (lean/load-artifact runtime input (:manifest-sha256 description))]
        (refused "RuntimeBoundary" #(lean/call loaded entry
                                      (if (= entry "debugString") "leaf" (.shiftLeft java.math.BigInteger/ONE 80)))))))
  (with-open [pure (lean/load-project runtime (source-dir "sharing-boundaries")
                    {:compiler compiler :root-module "Boundary" :entries ["debugArrayPure"]})]
    (refused "RuntimeBoundary" #(lean/call pure "debugArrayPure" [3 2 1]))))
;; Source/artifact callbacks also exercise failed-action pure-heap retirement.
(let [options {:compiler compiler :entries ["anyContains" "hasPrefix" "anyFailure"]}
      samples [["" 65 false] ["λ😀\u0000z" 0 true] ["λ😀\u0000z" 128512 true] ["λ😀" 65 false]]
      check! (fn [project]
               (doseq [[text target expected] samples]
                 (check (= expected (:value (lean/call project "anyContains" text target)))))
               (doseq [[prefix text expected] [["" "😀" true] ["λ😀" "λ😀\u0000" true]
                                               ["λ\u0000" "λ😀" false]]]
                 (check (= expected (lean/call project "hasPrefix" prefix text))))
               (check (= false (:value (lean/call project "anyFailure" ""))))
               (try (lean/call project "anyFailure" "x")
                    (throw (AssertionError. "Expected callback boundary failure"))
                    (catch ansatz.lean.jvm.LeanException e
                      (check (= "RuntimeBoundary" (.code e)))
                      (check (.contains (.getMessage e) "heap-leaf ownership is unavailable")))))]
  (with-open [runtime (lean/open)
              project (lean/load-project runtime "examples/string-search" options)] (check! project))
  (let [description (with-open [out (clojure.java.io/output-stream (io/file output "string-search.zip"))]
                      (lean/prepare-project "examples/string-search" options out))]
    (with-open [runtime (lean/open)
                in (clojure.java.io/input-stream (io/file output "string-search.zip"))
                project (lean/load-artifact runtime in (:manifest-sha256 description))]
      (check! project))))
(def report {:schema "ansatz-lean-jvm-source-acceptance/1" :checks @checks :timings-ms @timings
             :module-cache-observations @observations :sdk-resource-protocol "jar" :runtime-heap-mib (quot (.maxMemory (Runtime/getRuntime)) 1048576)
             :scope "Actual public source cold/cache/edit/reload/artifact, common/scalar values, unchanged tutorial sort, runtime sharing-domain source/artifact refusal, warnings, errors, capability and type refusal"})
(spit (io/file output "result.json") (json/write-str report :escape-slash false))
(println "PASS SOURCE_ACCEPTANCE" (dissoc report :module-cache-observations))
(shutdown-agents)
