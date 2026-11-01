(ns ansatz-lean-jvm-release
  "Producer-only identification of exact release bytes. No interpreter loading,
   native processes, publication, credentials or network access."
  (:require [clojure.edn :as edn] [clojure.java.io :as io])
  (:import [java.io ByteArrayInputStream]
           [javax.xml.parsers DocumentBuilderFactory]
           [java.nio.file Files] [java.security MessageDigest]
           [java.util.zip ZipFile]))

(def coordinate 'org.replikativ/ansatz-lean-jvm)
(def pom-entry "META-INF/maven/org.replikativ/ansatz-lean-jvm/pom.xml")
(def metadata-entry "META-INF/ansatz-lean-jvm/runtime.edn")
(defn- need [ok message]
  (when-not ok (throw (ex-info message {:stage :lean-jvm-release}))))
(defn check-version! [version]
  (need (and (string? version) (re-matches #"0\.2\.[0-9]+" version))
        "Expected the coordinated root release version 0.2.<git-count>")
  version)
(defn- digest [bytes]
  (apply str (map #(format "%02x" (bit-and 255 %))
                  (.digest (MessageDigest/getInstance "SHA-256") bytes))))
(defn- file-record [path]
  (let [file (io/file path)]
    (need (and (.isFile file) (<= (.length file) (* 64 1024 1024)))
          "A bounded existing release file is required")
    (let [bytes (Files/readAllBytes (.toPath file))]
      {:path (str path) :bytes (alength bytes) :sha256 (digest bytes)})))
(defn- entry-bytes [^ZipFile archive name]
  (let [entry (.getEntry archive name)]
    (need (and entry (<= 0 (.getSize entry) (* 1024 1024)))
          "Missing or excessive release metadata entry")
    (with-open [input (.getInputStream archive entry)]
      (let [bytes (.readNBytes input (int (inc (* 1024 1024))))]
        (need (<= (alength bytes) (* 1024 1024)) "Release metadata exceeds bound")
        bytes))))
(defn- check-pom! [bytes version]
  (let [factory (DocumentBuilderFactory/newInstance)]
    (.setFeature factory "http://apache.org/xml/features/disallow-doctype-decl" true)
    (.setFeature factory "http://xml.org/sax/features/external-general-entities" false)
    (.setFeature factory "http://xml.org/sax/features/external-parameter-entities" false)
    (.setXIncludeAware factory false)
    (.setExpandEntityReferences factory false)
    (let [document (.parse (.newDocumentBuilder factory) (ByteArrayInputStream. bytes))
          children (.getChildNodes (.getDocumentElement document))
          values (into {} (for [i (range (.getLength children))
                                :let [node (.item children i)]
                                :when (= 1 (.getNodeType node))]
                            [(.getNodeName node) (.getTextContent node)]))]
      (need (= ["org.replikativ" "ansatz-lean-jvm" version]
               (mapv values ["groupId" "artifactId" "version"]))
            "POM coordinate or release version differs"))))
(defn- describe! [jar-file pom-file version]
  (check-version! version)
  (let [jar (file-record jar-file) pom (file-record pom-file)]
    (with-open [archive (ZipFile. (io/file jar-file))]
      (check-pom! (entry-bytes archive pom-entry) version)
      (need (= (:sha256 pom) (digest (entry-bytes archive pom-entry)))
            "External POM does not match the POM packaged in the JAR")
      (let [metadata (edn/read-string (String. (entry-bytes archive metadata-entry)
                                              java.nio.charset.StandardCharsets/UTF_8))]
        (need (= version (:artifact-version metadata)) "JAR metadata release version differs")
        (need (and (= "ansatz-lean-jvm-runtime/1" (:schema metadata))
                   (= 17 (:java-release metadata))
                   (re-matches #"[0-9a-f]{64}" (or (:engine-source-sha256 metadata) "")))
              "Missing supported runtime cohort metadata")
        {:schema "ansatz-lean-jvm-release/1" :coordinate coordinate :version version
         :jar jar :pom pom :runtime metadata
         ;; Artifact identification never upgrades the implementation's claims.
         :public-project-api (:public-project-api metadata)
         :native-compiler-included (:native-compiler-included metadata)}))))
(defn prepare!
  "Write a local review receipt for an already built JAR/POM. Relative paths are
   relative to this module. This identifies bytes; it is not runtime acceptance."
  [{:keys [jar-file pom-file version output]}]
  (let [receipt (describe! jar-file pom-file version)]
    (need (string? output) "A release receipt output path is required")
    (io/make-parents output)
    (spit output (str (pr-str receipt) "\n"))
    receipt))
(defn verify!
  "Require an explicit expected version and unchanged reviewed JAR/POM bytes.
   Run from the same module directory as prepare!. No rebuild or remote effects."
  [{:keys [receipt version]}]
  (check-version! version)
  (let [record (edn/read-string (slurp receipt))]
    (need (= "ansatz-lean-jvm-release/1" (:schema record)) "Unknown release receipt schema")
    (need (= coordinate (:coordinate record)) "Release receipt coordinate differs")
    (need (= version (:version record)) "Expected coordinated release version differs")
    (let [jar-file (get-in record [:jar :path]) pom-file (get-in record [:pom :path])]
      (need (= record (describe! jar-file pom-file version)) "Prepared release bytes changed")
      {:jar-file jar-file :pom-file pom-file :version version
       :coordinate coordinate :receipt receipt})))
