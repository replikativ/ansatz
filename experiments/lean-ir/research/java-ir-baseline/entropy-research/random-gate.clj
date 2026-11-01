(ns java-entropy-original-random-gate-v1
  "Research use of a frozen prior native CAS capture, not an artifact issuer."
  (:require [clojure.data.json :as json] [clojure.java.io :as io]
            [clojure.string :as str] [java-ir-baseline :as j])
  (:import [java.nio.file Files] [java.security MessageDigest]))
(def manifest-pin "5221a039d9a7b4770dfe3fa4d691412978f228ba146c77c70090c0b594fbf45c")
(def stream-pin "a56c4b244afe6e5fc52de241d26841fca67c2edbdf386892efd679acbb84c27c")
(defn- sha [bytes] (apply str (map #(format "%02x" (bit-and 255 %)) (.digest (MessageDigest/getInstance "SHA-256") ^bytes bytes))))
(defn- need [p message] (when-not p (throw (ex-info message {:profile :prior-native-random-cas-research-only}))))
(defn- read! [directory file bound]
  (let [path (.toPath (io/file (str directory) file))]
    (need (<= (Files/size path) bound) "Captured file exceeds research bound")
    (let [bytes (Files/readAllBytes path)] (need (<= (alength bytes) bound) "Captured file grew") bytes)))
(defn direct-names [row]
  ;; Metadata edges also contain initializer/redirect associations, which are
  ;; needed for closure capture but are not body-call borrows. Read actual IR
  ;; FAP/PAP targets, then borrow each external canonical Header once.
  (let [targets (for [node (tree-seq coll? seq (get-in row ["ir" "fdecl" "body"]))
                      :when (map? node) [kind value] node :when (#{"fap" "pap"} kind)]
                  (get value "c"))
        declared (set (get row "dependencies"))]
    (need (every? declared targets) "Actual body target missing from original occurrence metadata")
    (vec (distinct (remove #(= (get row "name") %) targets)))))
(defn prepare [basis directory]
  (let [manifest-bytes (read! directory "manifest.json" 1048576) _ (need (= manifest-pin (sha manifest-bytes)) "Research manifest pin differs")
        m (json/read-str (String. manifest-bytes "UTF-8")) stream (read! directory "declarations.jsonl" 16777216)
        _ (need (= stream-pin (sha stream) (get-in m ["declarations" "sha256"])) "Research original stream pin differs")
        lines (str/split-lines (String. stream "UTF-8")) records (get m "rows")
        _ (need (= 63 (count lines) (count records) (get m "rowCount")) "Research union row count differs")
        rows (mapv (fn [line record]
                     (let [raw (.getBytes ^String line "UTF-8") row (json/read-str line)]
                       (need (and (= (get record "sha256") (sha raw)) (= (get record "name") (get row "name"))) "Original row bytes/Name differ")
                       row)) lines records)
        base (j/prepare-host-program basis [] []) source (j/source-binding base {"prior-native-cas-research" manifest-pin})
        headers (into {} (map (fn [row record] [(get row "name") (j/declaration-header source row (get record "sha256"))]) rows records))
        registered (j/register-headers base (vec (vals headers)))
        prepared (reduce (fn [ctx row]
                           (if (get-in row ["ir" "fdecl"])
                             (j/materialize-body ctx (headers (get row "name")) row (mapv headers (direct-names row))) ctx)) registered rows)
        ctx (-> prepared (dissoc :task-runtime :profiling-policy)
                (assoc :explicit true :initializing true :build-identity (j/supported-build-identity basis)))
        entropy-name ["str" ["str" ["anonymous"] "IO"] "getRandomBytes"]
        error-name ["str" ["str" ["anonymous"] "IO"] "userError"]
        cap-class (Class/forName "ansatz.research.ir.Interpreter$EntropyCapability" true (:loader ctx))
        capability (j/invoke-static (.getMethod cap-class "deterministicForTesting" (into-array Class [(class (byte-array 0)) Integer/TYPE]))
                                   [(byte-array (range 8)) (int 8)])
        error-bytes (.getBytes ^String (first (filter #(= error-name (get (json/read-str %) "name")) lines)) "UTF-8")]
    {:ctx ctx :manifest m :headers headers :capability capability :cap-class cap-class
     :entropy-header (headers entropy-name) :error-header (headers error-name) :error-bytes error-bytes
     :global (headers (get m "global")) :action (headers (get m "rawInitializer"))}))
(defn install! [{:keys [ctx cap-class capability entropy-header error-header error-bytes]} engine]
  (.invoke (.getMethod ^Class (:class ctx) "installEntropy"
                       (into-array Class [cap-class (class entropy-header) (class error-header) (class error-bytes)]))
           engine (object-array [capability entropy-header error-header error-bytes])))
(defn begin! [{:keys [ctx global action]} engine]
  (.invoke (.getMethod ^Class (:class ctx) "startInitializer" (into-array Class [(class global) (class action)]))
           engine (object-array [global action])))
(defn drain! [{:keys [ctx]} engine]
  (loop [left 20000]
    (case (j/phase ctx engine)
      "complete" nil
      "running" (do (need (pos? left) "Original initializer bounded work exhausted")
                     (j/advance! ctx engine (min 128 left)) (recur (- left (min 128 left))))
      (throw (ex-info "Original initializer boundary; preserve actual engine" {:phase (j/phase ctx engine)})))))
(defn complete! [{:keys [ctx]} engine]
  (.invoke (.getMethod ^Class (:class ctx) "completeInitializer" (make-array Class 0)) engine (object-array 0)))
(defn status [{:keys [ctx]} engine]
  (.invoke (.getMethod ^Class (:class ctx) "entropyStatus" (make-array Class 0)) engine (object-array 0)))
