(ns ansatz-lean-jvm-filesystem-layout-checks
  "Execute actual native-generated constructor/projection IR in both JVM drivers."
  (:require [clojure.test :refer [deftest is run-tests]]
            [clojure.data.json :as json] [clojure.java.io :as io])
  (:import [ansatz.lean.jvm.internal.exec Interpreter Interpreter$Node]
           [java.nio ByteBuffer ByteOrder]
           [java.security MessageDigest]))
(def fixture "test/fixtures/filesystem-layouts/")
(defn sha [bytes]
  (apply str (map #(format "%02x" (bit-and 255 %)) (.digest (MessageDigest/getInstance "SHA-256") ^bytes bytes))))
(defn load-program []
  (let [provenance (json/read-str (slurp (str fixture "provenance.json")))
        bytes (with-open [input (io/input-stream (io/resource (get-in provenance ["capture" "resource"])))]
                (.readNBytes input 131073))]
    (is (= (get-in provenance ["capture" "sha256"]) (sha bytes)))
    (is (= (get-in provenance ["source" "sha256"])
           (sha (java.nio.file.Files/readAllBytes (.toPath (io/file (str fixture "Main.lean")))))))
    (Interpreter/prepare (mapv json/read-str (rest (clojure.string/split-lines (String. bytes "UTF-8")))))))
(defn call [engine program name & args]
  (.invoke ^Interpreter engine (.functionId program (str "RuntimeLayoutWitness." name)) (object-array (map #(if (instance? clojure.lang.BigInt %) (biginteger %) %) args))))

;; Trusted fixture readers follow the adapter's declared-field reflection seam;
;; encapsulated Node payloads remain unavailable through ordinary public fields.
(def ^:private node-readers
  (into {} (for [name ["tag" "fields" "scalars"]]
             [name (doto (.getDeclaredField Interpreter$Node name) (.setAccessible true))])))
(defn- node-member [^Interpreter$Node node name]
  (.get ^java.lang.reflect.Field (get node-readers name) node))
(defn- node-tag [^Interpreter$Node node] (node-member node "tag"))
(defn- scalars ^bytes [^Interpreter$Node node] (node-member node "scalars"))
(defn scalar32 [^Interpreter$Node node]
  (Integer/toUnsignedLong (.getInt (doto (ByteBuffer/wrap (scalars node)) (.order ByteOrder/LITTLE_ENDIAN)))))
(defn fields [^Interpreter$Node node] (mapv identity (seq (node-member node "fields"))))

(deftest metadata-and-system-time-native-fields-roundtrip
  (let [program (load-program)]
    (doseq [explicit [false true]]
      (with-open [engine (Interpreter. program explicit)]
        (doseq [kind (range 4) size [0 42 18446744073709551615N]]
          (let [at (call engine program "systemTime" -1 999999999)
                mt (call engine program "systemTime" 123 456)
                data (call engine program "metadata" at mt size kind 7)]
            (is (= 0 (node-tag data)))
            (is (= 17 (alength (scalars data))))
            (is (= size (call engine program "fileSize" data)))
            (is (= 7 (call engine program "fileLinks" data)))
            (is (= kind (call engine program "fileKind" data)))
            (doseq [[getter seconds nanos] [["fileAccessed" -1 999999999] ["fileModified" 123 456]]]
              (let [time (call engine program getter data)]
                (is (= seconds (call engine program "timeSeconds" time)))
                (is (= nanos (call engine program "timeNanos" time)))
                (.dec engine time 1)))
            (.dec engine data 1)))
        (doseq [[kind expected] [["dir" 0] ["file" 1] ["symlink" 2] ["other" 3]]]
          (is (= expected (call engine program (str "fileType_" kind) 0))))))))

(def error-kinds
  [["alreadyExists" :optional] ["otherError" :plain] ["resourceBusy" :plain]
   ["resourceVanished" :plain] ["unsupportedOperation" :plain] ["hardwareFault" :plain]
   ["unsatisfiedConstraints" :plain] ["illegalOperation" :plain] ["protocolError" :plain]
   ["timeExpired" :plain] ["interrupted" :path] ["noFileOrDirectory" :path]
   ["invalidArgument" :optional] ["permissionDenied" :optional] ["resourceExhausted" :optional]
   ["inappropriateType" :optional] ["noSuchThing" :optional] ["unexpectedEof" :empty] ["userError" :message]])
(deftest all-error-constructors-native-layout-and-ownership
  (let [program (load-program) message "details λ😀\u0000"]
    (doseq [explicit [false true]]
      (with-open [engine (Interpreter. program explicit)]
        (doseq [[tag [kind shape]] (map-indexed vector error-kinds)
                code [0 2147483648 4294967295]
                some? (if (= shape :optional) [false true] [false])]
          (let [path (if (= shape :optional)
                       (if some? (call engine program "optionSome" "path λ")
                           (call engine program "optionNone" 0)) "path λ")
                arguments (case shape :optional [path code message] :path [path code message]
                                :plain [code message] :empty [0] :message [message])
                value (apply call engine program (str "error_" kind) arguments)]
            (if (= shape :empty)
              (is (= tag value))
              (do
                (is (= tag (node-tag value)))
                (is (= (if (#{:plain :message} shape) 1 2) (count (fields value))))
                (is (= message (last (fields value))))
                (when-not (= shape :message) (is (= code (scalar32 value))))
                (when (= shape :path) (is (= path (first (fields value)))))
                (when (= shape :optional)
                  (let [stored (first (fields value))]
                    (if some?
                      (is (= ["path λ"] (fields stored)))
                      (is (= 0 stored)))))))
            (.dec engine value 1)))
        (let [ok (call engine program "ioSuccess" 42 0)
              err (call engine program "error_userError" message)
              failed (call engine program "ioFailure" err 0)]
          (is (= 0 (node-tag ok))) (is (= [42] (fields ok)))
          (is (= 1 (node-tag failed))) (is (= [err] (fields failed)))
          (.dec engine ok 1) (.dec engine failed 1))))))
(defn check! [] (run-tests 'ansatz-lean-jvm-filesystem-layout-checks))
