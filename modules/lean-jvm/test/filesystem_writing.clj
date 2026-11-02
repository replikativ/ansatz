(ns ansatz-lean-jvm-filesystem-writing
  "Definitions only. Ordinary authored application; separate native and JVM receipts."
  (:require [ansatz.lean.jvm :as lean] [clojure.java.io :as io])
  (:import [ansatz.lean.jvm HostServices FileAccess]
           [java.nio.file Files Path StandardOpenOption CopyOption LinkOption]
           [java.nio.file.attribute FileAttribute]
           [java.security MessageDigest] [java.util HexFormat]
           [java.util.concurrent TimeUnit]))
(def source-files ["Main.lean" "WriterLib.lean" "NativeOracle.lean"])
(def output-files ["input.txt" "output.txt" "output.txt.bin" "output.txt.new" "output.txt.log"])
(defn- path [value] (.toAbsolutePath (.normalize (.toPath (io/file (str value))))))
(defn- demand! [ok facts] (when-not ok (throw (ex-info "Writable filesystem acceptance differs" facts))))
(defn- sha [^bytes bytes] (.formatHex (HexFormat/of) (.digest (MessageDigest/getInstance "SHA-256") bytes)))
(defn source-hashes [source]
  (into (sorted-map) (for [name source-files] [name (sha (Files/readAllBytes (.resolve (path source) name)))])))
(defn- inputs! [value]
  (let [root (path value)]
    (Files/createDirectory root (make-array FileAttribute 0))
    (Files/write (.resolve root "input.txt") (.getBytes "hello é\u0000雪\n" "UTF-8")
                 (into-array java.nio.file.OpenOption [StandardOpenOption/CREATE_NEW StandardOpenOption/WRITE]))
    root))
(defn snapshot [root]
  (with-open [paths (Files/list (path root))]
    (into (sorted-map)
          (for [^Path file (.toList paths)]
            (do (demand! (Files/isRegularFile file (into-array LinkOption [LinkOption/NOFOLLOW_LINKS])) {:file (str file)})
                [(str (.getFileName file)) (mapv #(bit-and 255 %) (Files/readAllBytes file))])))))
(defn- services [root] (.build (.fileAccess (HostServices/builder) (FileAccess/readWrite (path root)))))
(defn- receipt [project root hashes]
  (let [r (lean/call project "main" ["input.txt" "output.txt"])]
    {:source-hashes hashes :stdout (:stdout r) :stderr (:stderr r) :exit (:value r) :files (snapshot root)}))
(defn source! [compiler source-directory fresh-output-directory]
  (let [source (path source-directory) output (path fresh-output-directory)
        _ (Files/createDirectory output (make-array FileAttribute 0))
        roots (mapv #(inputs! (.resolve output %)) ["source" "cache" "artifact"])
        options {:compiler compiler :root-module "Main" :entries ["main"]}
        hashes (source-hashes source)
        run (fn [root] (with-open [runtime (lean/open (services root))
                                  project (lean/load-project runtime source options)]
                         (receipt project root hashes)))
        first-run (run (first roots)) cached (run (second roots))
        artifact (.resolve output "writer.zip")
        prepared (with-open [out (Files/newOutputStream artifact (into-array java.nio.file.OpenOption
                             [StandardOpenOption/CREATE_NEW StandardOpenOption/WRITE]))]
                   (lean/prepare-project source options out))
        loaded (with-open [runtime (lean/open (services (nth roots 2)))
                           in (io/input-stream (.toFile artifact))
                           project (lean/load-artifact runtime in (:manifest-sha256 prepared))]
                 (receipt project (nth roots 2) hashes))
        result {:groups {:source first-run :cache cached :artifact loaded} :artifact prepared}]
    (demand! (= first-run cached loaded) {:reason :source-cache-artifact :result result})
    (spit (.toFile (.resolve output "jvm.edn")) (pr-str result)) result))
(defn native! [sysroot source-directory fresh-output-directory]
  (let [sysroot (path sysroot) source (path source-directory) output (path fresh-output-directory)
        _ (Files/createDirectory output (make-array FileAttribute 0)) root (inputs! (.resolve output "native"))]
    (doseq [file source-files] (Files/copy (.resolve source file) (.resolve output file) (make-array CopyOption 0)))
    (letfn [(run! [label cwd args]
              (let [available (some-> (re-find #"(?m)^MemAvailable:\s+(\d+)\s+kB$"
                                    (Files/readString (Path/of "/proc/meminfo" (make-array String 0)))) second Long/parseLong)
                    _ (demand! (and available (>= available (* 2 1024 1024))) {:code "NativePreflightResourceLimit" :available-kib available})
                    command (into ["/usr/bin/prlimit" "--cpu=60:60" "--core=0:0" "--"
                                   (str (.resolve sysroot "bin/lean")) "-j1" "-M512"] args)
                    stdout (.resolve output (str label ".stdout")) stderr (.resolve output (str label ".stderr"))
                    builder (doto (ProcessBuilder. ^java.util.List command) (.directory (.toFile ^Path cwd))
                              (.redirectOutput (.toFile stdout)) (.redirectError (.toFile stderr)))
                    _ (.put (.environment builder) "LEAN_SYSROOT" (str sysroot))
                    _ (.put (.environment builder) "LEAN_PATH" (str output java.io.File/pathSeparator (.resolve sysroot "lib/lean")))
                    process (.start builder)]
                (when-not (.waitFor process 60 TimeUnit/SECONDS)
                  (.destroyForcibly process) (throw (ex-info "Native writing timeout" {:stage label})))
                (let [r {:stdout (slurp (.toFile stdout)) :stderr (slurp (.toFile stderr)) :exit (.exitValue process)}]
                  (spit (.toFile (.resolve output (str label ".edn"))) (pr-str (assoc r :command command)))
                  (demand! (zero? (:exit r)) {:stage label :receipt r}) r)))]
      (run! "compile" output ["-o" "WriterLib.olean" "WriterLib.lean"])
      (let [r (assoc (run! "oracle" root ["--run" (str (.resolve output "NativeOracle.lean")) "input.txt" "output.txt"])
                    :source-hashes (source-hashes source) :files (snapshot root))]
        (spit (.toFile (.resolve output "native.edn")) (pr-str r)) r))))
(defn compare-native! [jvm native]
  (demand! (= #{:source :cache :artifact} (set (keys (:groups jvm)))) {:reason :missing-jvm-group})
  (doseq [[group result] (:groups jvm)]
    (demand! (= result native) {:reason :native-jvm-difference :group group :native native :jvm result}))
  {:status :filesystem-writing-differential-pass :groups (count (:groups jvm)) :files (count (:files native))})
