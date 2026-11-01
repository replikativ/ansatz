(ns ansatz.lean.jvm
  "Clojure REPL interface to checked Lean project execution. Core Ansatz can be
   used alongside this optional module; kernel declaration import is separate."
  (:require [clojure.java.io :as io])
  (:import [ansatz.lean.jvm Lean LeanProject LeanFunction
            NativeCompilerOptions ProjectOptions LeanUnit IOResult LeanChoice]
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
    ("list" "array") (mapv #(clojure-value (get type "element") %) value)
    ("sum" "except") (let [left? (.isLeft ^LeanChoice value)
                              sum? (= "sum" (get type "kind"))
                              key (if sum? (if left? :left :right) (if left? :error :ok))
                              child (get type (if sum? (if left? "left" "right") (if left? "error" "value")))]
                          {key (clojure-value child (.value ^LeanChoice value))})
    value))

(defn- host-arguments [descriptor arguments]
  (let [remaining (volatile! 100000)]
    (letfn [(visit [type value depth]
              (when (.isInterrupted (Thread/currentThread))
                (throw (ex-info "Argument conversion cancelled" {:code "Cancelled"})))
              (when-not (and (< depth 128) (not (neg? (vswap! remaining dec))))
                (throw (ex-info "Argument conversion exceeds budget" {:code "ResourceLimit"})))
              (case (get type "kind")
                "unit" (if (nil? value) LeanUnit/INSTANCE value)
                "option" (cond
                           (nil? value) (Optional/empty)
                           (and (map? value) (= #{:some} (set (keys value))))
                           (Optional/of (visit (get type "element") (:some value) (inc depth)))
                           (= Optional (class value))
                           (if (.isPresent ^Optional value)
                             (Optional/of (visit (get type "element") (.get ^Optional value) (inc depth))) value)
                           :else (throw (ex-info "Option expects nil or {:some value}" {:code "UnsupportedArgumentType"})))
                ("sum" "except")
                (let [[left right] (if (= "sum" (get type "kind")) [:left :right] [:error :ok])
                      [left-type right-type] (if (= "sum" (get type "kind")) ["left" "right"] ["error" "value"])]
                  (cond
                    (and (map? value) (= #{left} (set (keys value))))
                    (LeanChoice/left (visit (get type left-type) (get value left) (inc depth)))
                    (and (map? value) (= #{right} (set (keys value))))
                    (LeanChoice/right (visit (get type right-type) (get value right) (inc depth)))
                    (= LeanChoice (class value)) value
                    :else (throw (ex-info "Expected an explicitly tagged branch" {:code "UnsupportedArgumentType"}))))
                ("product" "list" "array")
                (do (when-not (and (instance? java.util.List value) (not (instance? clojure.lang.ISeq value)))
                      (throw (ex-info "Expected a bounded vector or java.util.List" {:code "UnsupportedArgumentType"})))
                    (let [size (.size ^java.util.List value) product? (= "product" (get type "kind"))]
                      (when-not (and (<= 0 size @remaining) (or (not product?) (= size 2)))
                        (throw (ex-info "Invalid container extent" {:code "InvalidArgument"})))
                      (mapv (fn [index]
                              (visit (if product? (get type (if (zero? index) "first" "second")) (get type "element"))
                                     (.get ^java.util.List value index) (inc depth))) (range size))))
                value))]
      (mapv #(visit %1 %2 0) (get descriptor "arguments") arguments))))

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
        (let [arguments (host-arguments descriptor arguments)
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
