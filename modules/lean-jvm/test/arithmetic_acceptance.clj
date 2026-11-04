(ns arithmetic-acceptance
  "Native differential for the integer arithmetic externs. Official `lean --run`
   prints every `row i r 0` of test/fixtures/integer-arithmetic; the packaged SDK
   prepares the same source and its calls must concatenate to byte-identical text.
   Works only on a fresh copy of the fixture under the compiler cache."
  (:refer-clojure :exclude [run!])
  (:require [ansatz.lean.jvm :as lean] [clojure.java.io :as io] [clojure.string :as str]
            [clojure.data.json :as json])
  (:import [java.nio.file Files Path] [java.nio.file.attribute FileAttribute]
           [java.security MessageDigest] [java.util.concurrent TimeUnit]))

(def fixture-root "test/fixtures/integer-arithmetic")

(defn- check! [value label data]
  (when-not value (throw (ex-info "Arithmetic acceptance failed" (assoc data :check label)))))
(defn- sha256 [^bytes bytes]
  (apply str (map #(format "%02x" (bit-and % 0xff)) (.digest (MessageDigest/getInstance "SHA-256") bytes))))

(defn native!
  "Compile Main.olean, then run Oracle.lean with the official executable. Returns stdout."
  [sysroot directory]
  (let [lean-bin (.getCanonicalPath (io/file sysroot "bin/lean"))
        logs (io/file directory "native")]
    (check! (.mkdirs logs) :native-log-directory {:path (str logs)})
    (letfn [(run! [stage command]
              (let [stdout (io/file logs (str stage ".stdout")) stderr (io/file logs (str stage ".stderr"))
                    builder (doto (ProcessBuilder. ^java.util.List command)
                              (.directory (io/file directory)) (.redirectOutput stdout) (.redirectError stderr))
                    _ (.put (.environment builder) "LEAN_PATH" (.getPath logs))
                    process (.start builder)]
                (when-not (.waitFor process 300 TimeUnit/SECONDS)
                  (.destroyForcibly process)
                  (throw (ex-info "Native oracle timeout" {:stage stage})))
                (check! (zero? (.exitValue process)) :native-exit {:stage stage :stderr (slurp stderr)})
                (check! (str/blank? (slurp stderr)) :native-stderr {:stage stage :stderr (slurp stderr)})
                (slurp stdout)))]
      (run! "compile" [lean-bin "-j1" "-M768" "-o" (.getPath (io/file logs "Main.olean")) "Main.lean"])
      (run! "oracle" [lean-bin "-j1" "-M768" "--run" "Oracle.lean"]))))

(defn- first-difference [expected actual]
  (let [e (str/split-lines expected) a (str/split-lines actual)
        i (or (first (keep-indexed (fn [i [x y]] (when (not= x y) i)) (map vector e a)))
              (min (count e) (count a)))]
    {:line (inc i) :native (get e i) :jvm (get a i) :native-lines (count e) :jvm-lines (count a)}))

(defn run!
  "CONFIG contains :compiler {:sysroot :producer-bundle :cache}. Returns a report."
  [{:keys [compiler]}]
  (let [cache (io/file (:cache compiler)) _ (.mkdirs cache)
        directory (.toFile (Files/createTempDirectory (.toPath cache) "arithmetic-acceptance-"
                                                      (make-array FileAttribute 0)))
        pins (json/read-str (slurp (io/file fixture-root "expected.json")))]
    (doseq [file ["Main.lean" "Oracle.lean"]] (io/copy (io/file fixture-root file) (io/file directory file)))
    (let [native (native! (:sysroot compiler) directory)
          native-bytes (.getBytes ^String native "UTF-8")]
      ;; The pinned digest detects toolchain drift independently of the JVM result.
      (check! (= (get pins "sha256") (sha256 native-bytes)) :native-reference
              {:expected pins :bytes (alength native-bytes)})
      (with-open [runtime (lean/open)
                  project (lean/load-project runtime directory
                            {:compiler compiler :root-module "Main" :entries ["tableCount" "rowCount" "row"]})]
        (let [row (lean/function project "row")
              rows (fn [] (vec (for [i (range (lean/call project "tableCount" 0))
                                     r (range (lean/call project "rowCount" i 0))]
                                 (row i r 0))))
              parts (rows) jvm (apply str parts)]
          (check! (= native jvm) :native-jvm-differential (first-difference native jvm))
          ;; Retained handles in the same Project reproduce the same text.
          (check! (= parts (rows)) :repeated-calls {})
          {:passed true :workspace (.getPath directory) :calls (count parts)
           :lines (get pins "lines") :sha256 (get pins "sha256")})))))
