(ns ansatz-lean-jvm-producer-checks
  "Genuine artifact compatibility and producer-metadata rejection models only.
   Repacked negatives are not native output or synthetic acceptance evidence."
  (:require [clojure.test :refer [deftest is run-tests]]
            [clojure.java.io :as io] [clojure.data.json :as json]
            [ansatz.lean.jvm.artifact :as artifact]
            [ansatz.lean.jvm.entry :as entry]
            [ansatz.lean.jvm.producer :as producer])
  (:import [java.io ByteArrayInputStream ByteArrayOutputStream]
           [java.nio.charset StandardCharsets] [java.security MessageDigest]
           [java.util.zip ZipInputStream ZipOutputStream ZipEntry]))

(def ^:private fixture-pins
  {"interop.zip" {:archive "5528173ff9018ff2353aa869d15c5d338335a8004fa43ed7654ef9a658e7d3e3"
                   :manifest "fc19283c5ada0f62f291ef11789b04d67874b57c293372a298d101aec0f8ae8b" :entries 3}
   "general-interop.zip" {:archive "86bc5c643a3318b808f2e9a175de8fa3bd84826eec7aa74fbb0a6f012f950bc5"
                           :manifest "be9bd183156ae082eb532a0bc8cb4eff19949813476e17985a6d48420c98f1aa" :entries 16}})
(def ^:private legacy-entry
  ["e89beefe6ebb864d830367a377360d68cbce89c97fa6a5a5e9dab8877b6c6629" "a94b830bcada8032736e3bbd43e7dce559054e2214cb74489bd58709ac486593"])
(def ^:private core-entry
  ["e3e6f269769d2155b2367fc12e685b86b18204248b4303639e9fa6a59325f8ed" "64fc830a0bc395eed1e11280321331c9877021ce0e69b3aec6dfcb8b7646355a"])
(def ^:private expanded-entry
  ["1a8a0bf73fc7d6a18cd2b2d8cf9a693264ad3801cde396bd42190f2ebcca5a13" "736374c5c4baa38d952f1ed4d332754da171d53f67ca8f3a5104b997417a539a"])
(def ^:private startup
  ["f8c92d652c596b9bf656135348b190a5c09cf61ec40c8775835cf180a8833dd1" "2693f971452aa28190ca5c1033bf2b1030f9703b22f53181cd0591b1ab90399c"])
(def ^:private original-typed
  ["a48e00225fe08c1a74b66fff1102fd0c11ecefaaafc20ddcf6e28aaf363c99d3" "83342c9582dd43aef3974ffadb6f989c1f7bd23d66b3c406258ca31223030041"])
(def ^:private diagnostic-typed
  ["ac6ec4462614d39beed124c81f304b3c4875ce5fc6b15fd7b31bd0bbd56ca190" "c28866c7fcf13b141336547d4da1372ad1f90dfe46c04e5f72e5081466ce2d36"])
(def ^:dynamic *fixtures* nil)
(defn- sha [^bytes bytes]
  (apply str (map #(format "%02x" (bit-and 255 %)) (.digest (MessageDigest/getInstance "SHA-256") bytes))))
(defn- read-fixture [root name]
  (let [data (with-open [input (io/input-stream (io/file root "consumer/resources/lean" name))]
               (.readNBytes input 2097153))]
    (when (or (> (alength data) 2097152) (not= (:archive (fixture-pins name)) (sha data)))
      (throw (ex-info "Genuine producer regression fixture differs" {:fixture name})))
    (with-open [zip (ZipInputStream. (ByteArrayInputStream. data) StandardCharsets/UTF_8)]
      (loop [entries [] total 0]
        (if-let [entry (.getNextEntry zip)]
          (let [bytes (.readNBytes zip 4194305) size (alength bytes)]
            (when (or (.isDirectory entry) (> size 4194304) (> (+ total size) 16777216) (>= (count entries) 256))
              (throw (ex-info "Fixture ZIP exceeds structural model budget" {:fixture name})))
            (recur (conj entries [(.getName entry) bytes]) (+ total size)))
          (let [[manifest-path manifest] (peek entries)]
            (when-not (and (= "manifest.json" manifest-path) (= (:manifest (fixture-pins name)) (sha manifest)))
              (throw (ex-info "Genuine fixture manifest/order differs" {:fixture name})))
            {:data data :entries (pop entries) :manifest (json/read-str (String. ^bytes manifest StandardCharsets/UTF_8))}))))))
(defn- repack [fixture update-manifest]
  (let [manifest (.getBytes (json/write-str (update-manifest (:manifest fixture))) StandardCharsets/UTF_8)
        output (ByteArrayOutputStream.)]
    (with-open [zip (ZipOutputStream. output StandardCharsets/UTF_8)]
      ;; Payload bytes, file records and paths are unchanged. Manifest is last.
      (doseq [[name bytes] (conj (:entries fixture) ["manifest.json" manifest])]
        (.putNextEntry zip (ZipEntry. ^String name))
        (.write zip ^bytes bytes 0 (alength ^bytes bytes)) (.closeEntry zip)))
    {:data (.toByteArray output) :expected-manifest (sha manifest)}))
(defn- rejection [fixture update-manifest]
  (let [{:keys [data expected-manifest]} (repack fixture update-manifest)]
    (try (artifact/load! (ByteArrayInputStream. data) expected-manifest) nil
         (catch clojure.lang.ExceptionInfo error (select-keys (ex-data error) [:code :stage])))))
(defn- producer-fields [source-key binary-key [source binary]]
  (fn [manifest] (-> manifest (assoc-in ["producer" source-key "sha256"] source)
                    (assoc-in ["producer" binary-key "sha256"] binary))))
(defn- supported-rejection? [fixture update-manifest]
  (= {:code "ArtifactConflict" :stage :supported-producer} (rejection fixture update-manifest)))

(deftest genuine-v1-and-v2-artifacts-retain-compatibility
  (doseq [[name fixture] *fixtures*]
    (let [receipt (artifact/load! (ByteArrayInputStream. (:data fixture)) (:manifest (fixture-pins name)))
          payload (artifact/authenticated-artifact receipt)]
      (is (= (:entries (fixture-pins name)) (count (:entries payload))))
      (is (false? (:runtime-ready payload))))))

(deftest entry-source-and-binary-are-an-indivisible-admitted-cohort
  (doseq [[schema pair] [[1 legacy-entry] [2 core-entry] [2 expanded-entry]]]
    (is (= schema (apply entry/schema-for-pins! pair))))
  (doseq [source-pair [legacy-entry core-entry expanded-entry]
          binary-pair [legacy-entry core-entry expanded-entry]
          :when (not= source-pair binary-pair)]
    (is (thrown? clojure.lang.ExceptionInfo (entry/schema-for-pins! (first source-pair) (second binary-pair)))))
  (doseq [[name fixture] *fixtures*
          :let [other (if (= name "interop.zip") expanded-entry legacy-entry)]]
    (is (supported-rejection? fixture #(assoc-in % ["producer" "entryHelper" "sha256"] (second other))))
    (is (supported-rejection? fixture #(assoc-in % ["producer" "entryHelperSource" "sha256"] (first other))))))

(deftest non-entry-pure-policy-admits-exact-old-and-diagnostic-cohorts
  (is (apply producer/supported? "startupHeader" startup))
  (is (apply producer/supported? "typedSource" original-typed))
  (is (apply producer/supported? "typedSource" diagnostic-typed))
  (is (producer/binary-supported? "typedSource" (second diagnostic-typed)))
  (is (false? (producer/supported? "typedSource" (first original-typed) (second diagnostic-typed))))
  (is (false? (producer/supported? "typedSource" (first diagnostic-typed) (second original-typed))))
  (is (false? (apply producer/supported? "startupHeader" original-typed)))
  (is (false? (apply producer/supported? "unlisted" startup))))

(deftest both-artifact-versions-refuse-mixed-startup-and-typed-pairs-before-file-provenance
  (doseq [[_ fixture] *fixtures*
          update-manifest [(producer-fields "startupHelperSource" "startupHelper" [(first startup) (second original-typed)])
                           (producer-fields "startupHelperSource" "startupHelper" [(first original-typed) (second startup)])
                           (producer-fields "typedSourceExporterSource" "typedSourceExporter" [(first original-typed) (second diagnostic-typed)])
                           (producer-fields "typedSourceExporterSource" "typedSourceExporter" [(first diagnostic-typed) (second original-typed)])]]
    (is (supported-rejection? fixture update-manifest))))

(deftest an-admitted-new-pair-does-not-relabel-an-old-native-build
  ;; The pure cohort accepts the diagnostic producer, but these old captures
  ;; still bind their original actual build inputs. No new acceptance is minted.
  (doseq [[_ fixture] *fixtures*]
    (is (= {:code "ArtifactConflict" :stage :original-build-cohort}
           (rejection fixture (producer-fields "typedSourceExporterSource" "typedSourceExporter" diagnostic-typed))))))

(defn check!
  ([] (check! "."))
  ([module-root]
   (binding [*fixtures* (into {} (map (fn [name] [name (read-fixture module-root name)]) (keys fixture-pins)))]
     (run-tests 'ansatz-lean-jvm-producer-checks))))
