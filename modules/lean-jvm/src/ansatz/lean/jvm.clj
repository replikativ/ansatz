(ns ansatz.lean.jvm
  "Clojure REPL interface to checked Lean project execution. Core Ansatz can be
   used alongside this optional module; kernel declaration import is separate."
  (:require [clojure.java.io :as io])
  (:import [ansatz.lean.jvm Lean LeanProject LeanFunction
            NativeCompilerOptions ProjectOptions LeanUnit IOResult]
           [java.nio.file Path] [java.util Optional]))

(defn- path [value]
  (if (instance? Path value) value (.toPath (io/file value))))

(defn open [] (Lean/open))

(defn project-options
  "Explicit compiler configuration and requested entry names. A vector of names
   uses native signature discovery; a map can request legacy checked profiles."
  [{:keys [compiler root-module source-root entries]
    :or {root-module "Main" source-root "."}}]
  (let [native (NativeCompilerOptions. (path (:sysroot compiler))
                                      (path (:producer-bundle compiler)) (path (:cache compiler)))
        builder (-> (ProjectOptions/builder native) (.rootModule root-module) (.sourceRoot source-root))]
    (when-not (<= 1 (bounded-count 17 entries) 16)
      (throw (ex-info "Request one to sixteen checked entries" {:code "EntryRejected"})))
    (doseq [[name signature] (if (map? entries) entries (map #(vector % :auto) entries))]
      (case signature
        :auto (.function builder name)
        :nat-to-nat (.natFunction builder name)
        :string-to-string (.stringFunction builder name)
        :io-unit (.main builder name)
        (throw (ex-info "No native checked export profile supports this signature yet"
                        {:code "UnsupportedSignature"}))))
    (.build builder)))

(defn load-project
  "Load trusted source using explicit compiler options, passed as a map or a
   ProjectOptions object. No native installation or download is implicit."
  [^Lean runtime directory options]
  (.loadProject runtime (path directory)
                (if (instance? ProjectOptions options) options (project-options options))))

(defn load-artifact
  "The caller owns INPUT. EXPECTED-MANIFEST-SHA comes from a trusted descriptor."
  [^Lean runtime input expected-manifest-sha]
  (.loadArtifact runtime ^java.io.InputStream input ^String expected-manifest-sha))

(defn- clojure-value [type value]
  (case (get type "kind")
    "unit" nil
    "product" [(clojure-value (get type "first") (nth value 0))
               (clojure-value (get type "second") (nth value 1))]
    "option" (when (.isPresent ^Optional value)
               {:some (clojure-value (get type "element") (.get ^Optional value))})
    "list" (mapv #(clojure-value (get type "element") %) value)
    value))

(defn function
  "Resolve an admitted checked function as an IFn bound to this Project. Exact
   integers, Boolean and strings retain ordinary Clojure carriers. Unit is nil;
   decoded products/lists are vectors, Option is nil or {:some value}. IO returns
   {:value value :stdout text :stderr text}. Unsupported codecs throw explicitly."
  [^LeanProject project name]
  (let [^LeanFunction handle (.function project name)
        arity (.arity handle) descriptor (.descriptor handle)]
    (with-meta
      (fn [& arguments]
        (when-not (= arity (bounded-count (inc arity) arguments))
          (throw (ex-info (str "Expected " arity " explicit arguments") {:code "ArityMismatch"})))
        (let [arguments (mapv (fn [type argument]
                               (if (and (= "unit" (get type "kind")) (nil? argument)) LeanUnit/INSTANCE argument))
                             (get descriptor "arguments") arguments)
              result (.invoke handle (object-array arguments))]
          (if (= "io" (get descriptor "effect"))
            (let [^IOResult result result]
              {:value (clojure-value (get descriptor "result") (.value result))
               :stdout (.stdout result) :stderr (.stderr result)})
            (clojure-value (get descriptor "result") result))))
      {:lean/name name :lean/signature descriptor :lean/type (.signature handle) :lean/arity arity})))

(defn call [project name & arguments]
  (apply (function project name) arguments))

(defn run-main [^LeanProject project] (.runMain project))
(defn close! [^java.lang.AutoCloseable value] (.close value))
