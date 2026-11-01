(ns ansatz.lean
  "Experimental provider-first resident facade. Source resources are BORROWED.
   Every operation returns a persistent child; callers own each context close."
  (:refer-clojure :exclude [load-file load-string name])
  (:require [clojure.string :as str]
            [prototype.resident-preparation :as preparation]
            [prototype.resident-frontend :as resident]
            [prototype.typed-extern :as typed])
  (:import [ansatz.kernel Name]
           [java.nio ByteBuffer]
           [java.nio.charset StandardCharsets CodingErrorAction]
           [java.nio.file Files Path Paths]
           [java.security MessageDigest]))

(declare close!)
(deftype Context [resident scope closed]
  java.io.Closeable
  (close [this] (close! this)))
(deftype File [resident source])
(deftype Failure [operation cause scope])
(doseq [klass [Context File Failure]]
  (defmethod print-method klass [value writer]
    (.write ^java.io.Writer writer (str "#<" (.getSimpleName (class value)) ">"))))

(defn- invalid! [message]
  (throw (ex-info message {:lean/code :invalid-request})))

(defn name
  "Build a Name from a dotted string (all segments STRING), a kernel Name, or a
   vector of string/integer segments. Vector strings may contain literal dots.
   Numeric segments follow the existing guest encoder: nonnegative signed longs."
  [value]
  (cond
    (instance? Name value) value
    (string? value) (let [parts (str/split value #"\." -1)]
                      (when (some empty? parts) (invalid! "Name has an empty dotted segment"))
                      (name (vec parts)))
    (vector? value)
    (reduce (fn [^Name prefix segment]
              (cond
                (string? segment) (Name/mkStr prefix segment)
                (and (integer? segment) (<= 0 segment Long/MAX_VALUE))
                (Name/mkNum prefix (.longValue ^Number segment))
                :else (invalid! "Name segment must be a string or nonnegative signed long")))
            Name/ANONYMOUS_NAME value)
    :else (invalid! "Expected kernel Name, dotted string, or vector of segments")))

(defn- fail-operation [operation scope cause]
  ;; Exact original cause/ex-data remains reachable without printing checkpoints.
  ;; This is diagnostic evidence, never a fabricated resumable context.
  (ex-info (str "Lean " (clojure.core/name operation) " failed")
           {:lean/code (or (:lean/code (ex-data cause)) :operation-failed)
            :lean/operation operation
            :lean/failure (Failure. operation cause scope)} cause))

(defn failure-cause
  "Advanced diagnostic access to the ORIGINAL Throwable, including untouched
   checkpoint/owner evidence. Retaining it requires retaining the provider lease.
   It grants no resumption or automatic cleanup authority."
  [failure]
  (when-not (instance? Failure failure) (invalid! "Expected opaque Lean Failure"))
  (.-cause ^Failure failure))

(defn open
  "provider is a trusted function called with options, returning
   {:candidate owned-Environment-packet :configuration independent-registries
    :source-lease nonnil-borrowed-provider-scope}.
   Never closes/transfers the lease, even if adoption fails. Provider/caller MUST
   keep it open through every descendant, operation and retained failure packet.
   open-checked verifies live association; descriptive certificates grant nothing."
  [{:keys [provider options]}]
  (when-not (ifn? provider) (invalid! "Expected a trusted prepared provider"))
  (let [scope (atom {:provider provider})]
    (try
      (let [{:keys [candidate configuration source-lease] :as input} (provider options)]
        (swap! scope assoc :input input)
        (when-not (and (map? candidate) (map? configuration) (some? source-lease))
          (invalid! "Provider requires candidate, independent configuration and borrowed source-lease"))
        (Context. (preparation/open-checked candidate configuration) scope (atom false)))
      (catch Throwable cause (throw (fail-operation :open scope cause))))))

(defn- operate [context operation f]
  (when-not (instance? Context context) (invalid! "Expected Lean Context"))
  (let [^Context context context]
    (locking context
      (try
        (when @(.-closed context)
          (throw (ex-info "Lean Context is closed" {:lean/code :closed-context})))
        (f (.-resident context) (.-scope context))
        (catch Throwable cause
          (throw (fail-operation operation (.-scope context) cause)))))))

(defn- child [resident scope] (Context. resident scope (atom false)))
(defn fork [context]
  (operate context :fork (fn [r scope] (child (resident/fork r) scope))))

(defn close!
  "Idempotently release resident roots only; NEVER close borrowed source lease.
   Retained failure evidence and other contexts may still depend on that lease."
  [context]
  (when-not (instance? Context context) (invalid! "Expected Lean Context"))
  (let [^Context context context]
    (locking context
      (when-not @(.-closed context)
        (try
          (resident/close! (.-resident context))
          (reset! (.-closed context) true)
          (catch Throwable cause (throw (fail-operation :close (.-scope context) cause)))))))
  nil)

(defn- request! [{:keys [module roots initialization file-name] :as options}]
  (when-not (and (map? options) (= #{:module :roots :initialization :file-name} (set (keys options)))
                 (vector? roots) (contains? #{:defer :run} initialization)
                 (string? file-name) (seq file-name))
    (invalid! "Source requires explicit module, roots vector, initialization :defer/:run and file-name"))
  {:module-name (name module) :roots (mapv name roots)
   :initialization initialization :file-name file-name})

(defn- capture [text origin]
  (when-not (string? text) (invalid! "Source text must be a string"))
  ;; REPORT also rejects unpaired UTF-16 surrogates in load-string; digest/text
  ;; identity always corresponds to one losslessly representable UTF-8 source.
  (let [encoder (doto (.newEncoder StandardCharsets/UTF_8)
                  (.onMalformedInput CodingErrorAction/REPORT)
                  (.onUnmappableCharacter CodingErrorAction/REPORT))
        buffer (.encode encoder (java.nio.CharBuffer/wrap text))
        bytes (byte-array (.remaining buffer))
        _ (.get buffer bytes)
        digest (.digest (MessageDigest/getInstance "SHA-256") bytes)]
    {:text text :origin origin :encoding :utf-8 :byte-count (alength bytes)
     :sha256 (apply str (map #(format "%02x" (bit-and 255 %)) digest))}))

(defn- load-captured [r scope source options]
  (let [request (assoc (request! options) :text (:text source))
        source (assoc source :module (:module-name request) :file-name (:file-name request))
        result (resident/load-source r request)]
    {:context (child (:context result) scope)
     :file (when-let [file (:file result)] (File. file source))
     :success? (:success result) :diagnostics (:diagnostics result) :source source}))

(defn load-string [context text options]
  (operate context :load-string
           (fn [r scope] (load-captured r scope (capture text :string) options))))

(defn load-file
  "Read UTF-8 once, with malformed input rejected. File location is not identity.
   The immutable captured text is passed to resident, never reopened by it."
  [context path options]
  (operate context :load-file
           (fn [r scope]
             (let [^Path path (cond (instance? Path path) path
                                    (string? path) (Paths/get path (make-array String 0))
                                    :else (invalid! "Expected Path or path string"))
                   bytes (Files/readAllBytes path)
                   decoder (doto (.newDecoder StandardCharsets/UTF_8)
                             (.onMalformedInput CodingErrorAction/REPORT)
                             (.onUnmappableCharacter CodingErrorAction/REPORT))
                   text (str (.decode decoder (ByteBuffer/wrap bytes)))]
               (load-captured r scope (capture text (str path)) options)))))

(defn- file! [file]
  (when-not (instance? File file) (invalid! "Expected admitted Lean File"))
  (.-resident ^File file))

(defn initialize [context file]
  (operate context :initialize
           (fn [r scope] (child (resident/initialize r (file! file)) scope))))

(defn call
  "Forward existing explicit generic codec descriptors unchanged. Real frontend
   acceptance of the facade initially covers Nat/String. No implicit IO adapter."
  [context file target values signature]
  (operate context :call
           (fn [r scope]
             (let [result (resident/call r (file! file) (name target) values signature)]
               {:context (child (:context result) scope) :value (:value result)}))))

(defn extern
  "Exact existing synchronous Nat/String boxed ABI adapter, with declared borrow
   bits. fn receives positional immutable host values; no raw guest objects/IO."
  [{:keys [symbol] :as specification}]
  (when-not (and (string? symbol) (seq symbol)) (invalid! "Extern requires symbol string"))
  {symbol (typed/binding (dissoc specification :symbol))})

(defn with-externs [context bindings]
  (operate context :with-externs
           (fn [r scope] (child (resident/with-externs r bindings) scope))))

(defn with-compiler-options
  "Return a separately closeable child with an advanced raw compiler selection.
   Facts must describe already loaded code; {} clears selection. Provider scope
   stays borrowed. This does not discover roots or change admission/readiness."
  [context selection]
  (operate context :with-compiler-options
           (fn [r scope] (child (resident/with-compiler-options r selection) scope))))
