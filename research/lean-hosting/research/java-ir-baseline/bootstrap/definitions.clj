(ns ansatz.research.ir.bootstrap.definitions
  "Pinned explicit definition loading. No selected-form reader/eval, user Vars,
   runtime/catalogue/store creation, tests or guest execution."
  (:require [ansatz.research.ir.bootstrap.artifacts :as artifacts]
            [clojure.java.io :as io])
  (:import [java.net URLClassLoader] [java.nio.file LinkOption]))
(defn- need [ok message] (when-not ok (throw (ex-info message {:component :source4-definitions}))))
(defn- entries! [profile key]
  (let [entries (get (artifacts/description profile) key)]
    (need (and (vector? entries) (<= 1 (count entries) 256)) "Explicit bounded ordered definition entries required")
    (doseq [entry entries]
      (need (and (vector? entry) (= 2 (count entry)) (every? string? entry)
                 (re-matches #"[A-Za-z][A-Za-z0-9_.-]{0,255}" (second entry)))
            "Definition entry must name an artifact ID and exact namespace"))
    (need (and (= (count entries) (count (set (map first entries))))
               (= (count entries) (count (set (map second entries))))) "Duplicate definition artifact/namespace")
    entries))
(defn preflight!
  "Preflight the entire source list before loading its first namespace. Models
   are separate and optional. Existing opaque namespaces are never replaced."
  [profile key]
  (let [entries (entries! profile key)]
    (doseq [[id namespace] entries]
      (need (nil? (find-ns (symbol namespace))) "Definition namespace already loaded; registry replacement is forbidden")
      (let [file (artifacts/file! profile id)
            _ (need (<= (.length file) (* 2 1024 1024)) "Definition file exceeds bound")
            text (artifacts/text! profile id (* 2 1024 1024))
            actual (second (re-find #"(?s)\A\s*\(ns\s+([^\s()]+)" text))]
        (need (= namespace actual) "Definition artifact has another namespace")))
    entries))
(defn- load-list! [profile key]
  (let [entries (preflight! profile key) journal (atom {:stage :definition-preflight :loaded []})]
    (try
      (doseq [[id namespace] entries]
        (artifacts/guard! profile)
        (swap! journal assoc :stage :definition-load :pending namespace)
        (load-file (.getPath (artifacts/file! profile id)))
        (need (some? (find-ns (symbol namespace))) "Declared namespace was not loaded")
        (swap! journal #(-> % (update :loaded conj namespace) (dissoc :pending))))
      (artifacts/guard! profile)
      (assoc @journal :stage :definitions-loaded :runtime-opened false :guest-calls 0)
      (catch Throwable cause
        (throw (ex-info "Definition load failed; do not retry partially loaded registry namespaces"
                        {:journal @journal :key key} cause))))))
(defn load-definitions! [profile] (load-list! profile "definitions"))
(defn load-models!
  "Define only the explicitly pinned model list. Caller runs tests separately."
  [profile] (load-list! profile "models"))
(defn assert-basis!
  "After loading the actual pinned jar basis, before any engine/image, reject
   parent delegation and mixed nested class identity. Does not replace jar hash."
  [basis jar-file]
  (let [loader (:loader basis)
        expected (.toRealPath (.toPath (io/file jar-file)) (make-array LinkOption 0))]
    (need (instance? URLClassLoader loader) "Owned URLClassLoader basis required")
    (doseq [suffix ["" "$Program" "$Node" "$SourceBinding" "$Header" "$PreparedGraph"]]
      (let [cls (Class/forName (str "ansatz.lean.jvm.internal.exec.Interpreter" suffix) false loader)
            location (some-> cls .getProtectionDomain .getCodeSource .getLocation .toURI io/file .toPath
                             (.toRealPath (make-array LinkOption 0)))]
        (need (and (identical? loader (.getClassLoader cls)) (= expected location))
              "Interpreter class delegated or came from another jar")))
    (need (identical? (:class basis) (Class/forName "ansatz.lean.jvm.internal.exec.Interpreter" false loader))
          "Mixed Interpreter basis class")
    (need (identical? (:node-class basis) (Class/forName "ansatz.lean.jvm.internal.exec.Interpreter$Node" false loader))
          "Mixed Node basis class")
    (doseq [key [:tag :rc :fields :scalars]]
      (need (and (instance? java.lang.reflect.Field (get basis key))
                 (identical? (:node-class basis) (.getDeclaringClass ^java.lang.reflect.Field (get basis key))))
            "Mixed Node reflection fields"))
    {:status :same-pinned-jar-classloader :classes 6 :runtime-opened false}))
