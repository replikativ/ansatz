(ns java-ir-baseline
  (:require [clojure.java.io :as io]
            [clojure.data.json :as json]
            [prototype.machine :as m]
            [prototype.unchanged-program-benchmark :as benchmark])
  (:import [java.net URL URLClassLoader]
           [java.lang.reflect Method Constructor Field]))

(defn rows [path]
  (with-open [reader (io/reader path)]
    (mapv json/read-str (line-seq reader))))

(defn class-basis [directory]
  (let [loader (URLClassLoader. (into-array URL [(.toURL (.toURI (io/file directory)))])
                               (clojure.lang.RT/baseLoader))
        cls (Class/forName "ansatz.research.ir.Interpreter" true loader)
        program (Class/forName "ansatz.research.ir.Interpreter$Program" true loader)
        node (Class/forName "ansatz.research.ir.Interpreter$Node" true loader)]
    {:loader loader :class cls :node-class node
     :prepare (.getMethod cls "prepare" (into-array Class [java.util.List]))
     :constructor (.getConstructor cls (into-array Class [program]))
     :constructor-explicit (.getConstructor cls (into-array Class [program Boolean/TYPE]))
     :constructor-initializing (try (.getConstructor cls (into-array Class [program Boolean/TYPE Boolean/TYPE]))
                                   (catch NoSuchMethodException _ nil))
     :function-id (.getMethod program "functionId" (into-array Class [String]))
     :invoke (.getMethod cls "invoke" (into-array Class [Integer/TYPE (class (object-array 0))]))
     :rbmap (.getMethod cls "rbmap" (into-array Class (repeat 4 Integer/TYPE)))
     :batch (.getMethod cls "rbmapBatch" (into-array Class (repeat 5 Integer/TYPE)))
     :inc (.getMethod cls "inc" (into-array Class [Object Integer/TYPE]))
     :dec (.getMethod cls "dec" (into-array Class [Object Integer/TYPE]))
     :close (.getMethod cls "close" (make-array Class 0))
     :start (.getMethod cls "start" (into-array Class [Integer/TYPE (class (object-array 0))]))
     :start-release (try (.getMethod cls "startRelease" (into-array Class [Object Integer/TYPE]))
                         (catch NoSuchMethodException _ nil))
     :advance (.getMethod cls "advance" (into-array Class [Long/TYPE]))
     :take-result (.getMethod cls "takeResult" (make-array Class 0))
     :phase (.getMethod cls "phase" (make-array Class 0))
     :depth (.getMethod cls "continuationDepth" (make-array Class 0))
     :instructions (.getMethod cls "instructionCount" (make-array Class 0))
     :active (.getMethod cls "activeFunction" (make-array Class 0))
     :tag (.getField node "tag") :rc (.getField node "rc")
     :fields (.getField node "fields") :scalars (.getField node "scalars")}))

(defn invoke-static [^Method method args] (.invoke method nil (object-array args)))
(defn open-program [basis path]
  (assoc basis :program (invoke-static (:prepare basis) [(rows path)])))
(defn machine [basis]
  (cond
    (:task-runtime basis)
    (let [cls ^Class (:class basis)
          loader (.getClassLoader cls)
          identity-class (.loadClass loader "ansatz.research.ir.Interpreter$BuildIdentity")
          runtime-class (.loadClass loader "ansatz.research.ir.Interpreter$TaskRuntime")
          policy (:profiling-policy basis)
          parameters [(class (:program basis)) Boolean/TYPE Boolean/TYPE identity-class runtime-class]
          arguments [(:program basis) (boolean (:explicit basis)) (boolean (:initializing basis))
                     (:build-identity basis) (:task-runtime basis)]]
      (if policy
        (.newInstance (.getConstructor cls (into-array Class (conj parameters (class policy))))
                      (object-array (conj arguments policy)))
        (.newInstance (.getConstructor cls (into-array Class parameters)) (object-array arguments))))
    (:build-identity basis)
    (let [cls ^Class (:class basis)
          identity-class (.loadClass (.getClassLoader cls) "ansatz.research.ir.Interpreter$BuildIdentity")
          identity (:build-identity basis)]
      (.newInstance (.getConstructor cls (into-array Class [(class (:program basis)) Boolean/TYPE Boolean/TYPE identity-class]))
                    (object-array [(:program basis) (boolean (:explicit basis)) (boolean (:initializing basis)) identity])))
    (:initializing basis)
    (if-let [constructor (:constructor-initializing basis)]
      (.newInstance ^Constructor constructor (object-array [(:program basis) (boolean (:explicit basis)) true]))
      (throw (ex-info "Engine artifact has no initialization-session API" {})))
    (:explicit basis)
    (.newInstance ^Constructor (:constructor-explicit basis) (object-array [(:program basis) true]))
    :else (.newInstance ^Constructor (:constructor basis) (object-array [(:program basis)]))))
(defn logical-sync-task-runtime [basis]
  (let [cls (.loadClass (.getClassLoader ^Class (:class basis)) "ansatz.research.ir.Interpreter$TaskRuntime")]
    (invoke-static (.getMethod cls "logicalSynchronous" (make-array Class 0)) [])))
(defn require-disabled-profiling [basis getter]
  (let [cls (.loadClass (.getClassLoader ^Class (:class basis)) "ansatz.research.ir.Interpreter$ProfilingPolicy")]
    (invoke-static (.getMethod cls "requireDisabled" (into-array Class [(class getter)])) [getter])))
(defn start-dispose! [basis engine]
  (.invoke (.getMethod ^Class (:class basis) "startDispose" (make-array Class 0)) engine (object-array 0)))
(defn supported-build-identity [basis]
  (let [cls (.loadClass (.getClassLoader ^Class (:class basis)) "ansatz.research.ir.Interpreter$BuildIdentity")]
    (invoke-static (.getMethod cls "supportedLean4331" (make-array Class 0)) [])))
(defn finish-initialization! [basis engine]
  (.invoke (.getMethod ^Class (:class basis) "finishInitialization" (make-array Class 0))
           engine (object-array 0)))
(defn initializing? [basis engine]
  (.invoke (.getMethod ^Class (:class basis) "isInitializing" (make-array Class 0))
           engine (object-array 0)))
(defn function-id [basis label]
  (.invoke ^Method (:function-id basis) (:program basis) (object-array [label])))
(defn call [basis engine label args]
  (.invoke ^Method (:invoke basis) engine
           (object-array [(int (function-id basis label)) (object-array args)])))
(defn close! [basis engine] (.invoke ^Method (:close basis) engine (object-array 0)))
(defn release! [basis engine value] (.invoke ^Method (:dec basis) engine (object-array [value (int 1)])))
(defn retain! [basis engine value] (.invoke ^Method (:inc basis) engine (object-array [value (int 1)])))
(defn start! [basis engine label args]
  (.invoke ^Method (:start basis) engine (object-array [(int (function-id basis label)) (object-array args)])))
(defn start-release! [basis engine value count]
  (when-not (and (integer? count) (<= 0 count Integer/MAX_VALUE))
    (throw (ex-info "Release count requires a nonnegative int" {})))
  (if-let [method (:start-release basis)]
    (.invoke ^Method method engine (object-array [value (int count)]))
    (throw (ex-info "Engine artifact has no root release transaction API" {}))))
(defn advance! [basis engine budget] (.invoke ^Method (:advance basis) engine (object-array [(long budget)])))
(defn take-result! [basis engine] (.invoke ^Method (:take-result basis) engine (object-array 0)))
(defn phase [basis engine] (.invoke ^Method (:phase basis) engine (object-array 0)))
(defn depth [basis engine] (.invoke ^Method (:depth basis) engine (object-array 0)))
(defn instructions [basis engine] (.invoke ^Method (:instructions basis) engine (object-array 0)))
(defn active [basis engine] (.invoke ^Method (:active basis) engine (object-array 0)))

(defn host-basis
  "Attach the opt-in host-boundary API from this exact isolated engine artifact.
   Old computational-control artifacts remain usable through class-basis."
  [basis]
  (let [loader (:loader basis)
        host (Class/forName "ansatz.research.ir.Interpreter$HostExtern" true loader)
        request (Class/forName "ansatz.research.ir.Interpreter$HostRequest" true loader)
        host-array (class (java.lang.reflect.Array/newInstance host 0))
        string-array (class (make-array String 0)) bool-array (class (boolean-array 0))
        cls ^Class (:class basis)]
    (assoc basis :host-class host
           :host-constructor (.getConstructor host (into-array Class [String string-array bool-array String]))
           :prepare-host (.getMethod cls "prepare" (into-array Class [java.util.List host-array]))
           :host-request (.getMethod cls "pendingHostRequest" (make-array Class 0))
           :resume-host (.getMethod cls "resumeHost" (into-array Class [request Object]))
           :fail-host (.getMethod cls "failHost" (into-array Class [request Throwable]))
           :host-failure (.getMethod cls "hostFailure" (make-array Class 0)))))

(defn- host-descriptor-array [basis specifications]
  (let [descriptors (mapv (fn [{:keys [symbol parameters borrowed result]}]
                            (.newInstance ^Constructor (:host-constructor basis)
                              (object-array [symbol (into-array String parameters)
                                             (boolean-array borrowed) result]))) specifications)
        array (java.lang.reflect.Array/newInstance ^Class (:host-class basis) (count descriptors))]
    (doseq [[index descriptor] (map-indexed vector descriptors)]
      (java.lang.reflect.Array/set array index descriptor))
    array))

(defn prepare-host-program
  "Prepare in-memory original IR rows with exact opt-in host ABI descriptors.
   This registers no callback or effect; only explicit execution can request one."
  [basis rows specifications]
  (let [basis (host-basis basis) array (host-descriptor-array basis specifications)]
    (assoc basis :explicit true :program (invoke-static (:prepare-host basis) [rows array]))))

(defn extend-program
  "Prepare an immutable executable descendant. No engine, code or owner executes."
  ([basis rows] (extend-program basis rows []))
  ([basis rows additional-host-specifications]
   (let [basis (host-basis basis) array (host-descriptor-array basis additional-host-specifications)
         cls ^Class (class (:program basis))
         method (.getMethod cls "extend" (into-array Class [cls java.util.List (class array)]))]
     (assoc basis :program (invoke-static method [(:program basis) rows array])))))

(defn source-binding
  "Create a binding for the trusted adapter's accepted lightweight source token.
   This is an authority boundary, not verification of supplied bytes or hashes."
  [basis accepted-source-token]
  (let [cls (Class/forName "ansatz.research.ir.Interpreter$SourceBinding" true (:loader basis))]
    (.newInstance (.getConstructor cls (into-array Class [Object]))
                  (object-array [accepted-source-token]))))

(defn declaration-header [binding original-header-row original-sha256]
  (.invoke (.getMethod (class binding) "header" (into-array Class [java.util.Map String]))
           binding (object-array [original-header-row original-sha256])))

(defn- header-array [basis headers]
  (let [cls (Class/forName "ansatz.research.ir.Interpreter$Header" true (:loader basis))
        array (java.lang.reflect.Array/newInstance cls (count headers))]
    (doseq [[index header] (map-indexed vector headers)]
      (java.lang.reflect.Array/set array index header))
    array))

(defn register-headers
  "Append authentic headers without forcing executable bodies."
  ([basis headers] (register-headers basis headers []))
  ([basis headers specifications]
   (let [basis (host-basis basis) array (header-array basis headers)
         externs (host-descriptor-array basis specifications)
         cls (class (:program basis))
         method (.getMethod cls "registerHeaders" (into-array Class [cls (class array) (class externs)]))]
     (assoc basis :program (invoke-static method [(:program basis) array externs])))))

(defn bind-guest-exports
  "Publish source-authenticated extern Header→fdecl Header pairs in a descendant.
   This does not verify source bytes or prove an upstream export association."
  [basis bindings]
  (when-not (sequential? bindings)
    (throw (ex-info "Explicit guest export pairs required" {})))
  (let [cls (Class/forName "ansatz.research.ir.Interpreter$GuestExportBinding" true (:loader basis))
        header (Class/forName "ansatz.research.ir.Interpreter$Header" true (:loader basis))
        constructor (.getConstructor cls (into-array Class [header header]))
        array (java.lang.reflect.Array/newInstance cls (count bindings))
        program (class (:program basis))
        method (.getMethod program "bindGuestExports" (into-array Class [program (class array)]))]
    (doseq [[index pair] (map-indexed vector bindings)]
      (when-not (and (sequential? pair) (= 2 (count pair)))
        (throw (ex-info "Guest export pair must contain exactly two Headers" {})))
      (java.lang.reflect.Array/set array index
        (.newInstance constructor (object-array pair))))
    (assoc basis :program (invoke-static method [(:program basis) array]))))

(defn materialize-body
  "Prepare one authenticated original body; its dependencies remain headers."
  [basis target original-row direct-headers]
  (let [array (header-array basis direct-headers) cls (class (:program basis))
        method (.getMethod cls "materialize"
                           (into-array Class [cls (class target) java.util.Map (class array)]))]
    (assoc basis :program (invoke-static method [(:program basis) target original-row array]))))

(defn install-program!
  "Install BASIS's descendant on an idle, host-paused or code-paused engine."
  [basis engine]
  (.invoke (.getMethod ^Class (:class basis) "installProgram"
                       (into-array Class [(class (:program basis))]))
           engine (object-array [(:program basis)])))

(defn make-closure!
  "Transfer owned captures into a callable without executing guest code."
  [basis engine label captures]
  (.invoke (.getMethod ^Class (:class basis) "makeClosure"
                       (into-array Class [Integer/TYPE (class (object-array 0))]))
           engine (object-array [(int (function-id basis label)) (object-array captures)])))

(defn host-request [basis engine]
  (.invoke ^Method (:host-request basis) engine (object-array 0)))
(defn request-value
  "Borrow a request accessor; arguments acquire no new guest ownership."
  [request accessor]
  (.invoke (.getMethod ^Class (class request) accessor (make-array Class 0)) request (object-array 0)))
(defn lean-name-data
  "Normalize immutable Java Name lists to nested Clojure vectors for hashed lookup.
   Preserve exact Name tags and leaves; Java and Clojure collection hashes differ."
  [value]
  (if (instance? java.util.List value) (mapv lean-name-data value) value))
(defn resume-host! [basis engine request value]
  (.invoke ^Method (:resume-host basis) engine (object-array [request value])))
(defn fail-host! [basis engine request cause]
  (.invoke ^Method (:fail-host basis) engine (object-array [request cause])))
(defn host-failure [basis engine]
  (.invoke ^Method (:host-failure basis) engine (object-array 0)))
(defn code-request [basis engine]
  (.invoke (.getMethod ^Class (:class basis) "pendingCodeRequest" (make-array Class 0))
           engine (object-array 0)))
(defn resume-code! [basis engine request]
  (.invoke (.getMethod ^Class (:class basis) "resumeCode"
                       (into-array Class [(class request) (class (:program basis))]))
           engine (object-array [request (:program basis)])))
(defn fail-code! [basis engine request cause]
  (.invoke (.getMethod ^Class (:class basis) "failCode"
                       (into-array Class [(class request) Throwable]))
           engine (object-array [request cause])))
(defn code-failure [basis engine]
  (.invoke (.getMethod ^Class (:class basis) "codeFailure" (make-array Class 0))
           engine (object-array 0)))
(defn graph-ref [basis source-id]
  (let [cls (Class/forName "ansatz.research.ir.Interpreter$GraphRef" true (:loader basis))]
    (.newInstance (.getConstructor cls (into-array Class [Long/TYPE])) (object-array [(long source-id)]))))
(defn- unsigned-graph-bytes [values]
  (when-not (and (some? values) (or (and (sequential? values) (counted? values))
                                  (instance? java.util.List values))
                 (<= (count values) (* 16 1024 1024)))
    (throw (ex-info "ByteArray requires a bounded unsigned byte collection" {})))
  (byte-array (map (fn [value]
                     (when-not (and (integer? value) (<= 0 value 255))
                       (throw (ex-info "ByteArray element outside unsigned byte domain" {:value value})))
                     (unchecked-byte (long value))) values)))
(defn graph-node [basis {:keys [kind id rc tag fields scalars target]
                         :or {rc 0 fields [] scalars []} :as descriptor}]
  (let [allowed (case kind
                  :ctor #{:kind :id :rc :tag :fields :scalars}
                  :array #{:kind :id :rc :fields}
                  :byte-array #{:kind :id :rc :bytes}
                  :ref #{:kind :id :rc :fields}
                  :closure #{:kind :id :rc :target :fields})
        _ (when (some #(not (contains? allowed %)) (keys descriptor))
            (throw (ex-info "Unexpected graph descriptor field" {:kind kind})))
        _ (when (and (= kind :ref) (not= 1 (count fields)))
            (throw (ex-info "Ref requires exactly one payload" {})))
        _ (when (and (= kind :closure) (nil? target))
            (throw (ex-info "Closure requires an actual Header" {})))
        cls (Class/forName "ansatz.research.ir.Interpreter$ImportNode" true (:loader basis))
        objects (class (object-array 0)) bytes (class (byte-array 0))
        [types arguments]
        (case kind
          :ctor [[Long/TYPE Integer/TYPE Integer/TYPE objects bytes]
                 [(long id) (int rc) (int tag) (object-array fields) (byte-array scalars)]]
          :array [[Long/TYPE Integer/TYPE objects] [(long id) (int rc) (object-array fields)]]
          :byte-array [[Long/TYPE Integer/TYPE bytes] [(long id) (int rc) (unsigned-graph-bytes (:bytes descriptor))]]
          :ref [[Long/TYPE Integer/TYPE Object] [(long id) (int rc) (first fields)]]
          :closure [[Long/TYPE Integer/TYPE (class target) objects]
                    [(long id) (int rc) target (object-array fields)]])]
    (invoke-static (.getMethod cls (if (= kind :byte-array) "byteArray" (name kind)) (into-array Class types)) arguments)))
(defn graph-int [basis value]
  (when-not (integer? value)
    (throw (ex-info "GraphInt requires an exact integer" {:value value})))
  (let [cls (Class/forName "ansatz.research.ir.Interpreter$GraphInt" true (:loader basis))]
    (.newInstance (.getConstructor cls (into-array Class [java.math.BigInteger]))
                  (object-array [(biginteger value)]))))
(defn- graph-recipe [factory basis source state-token nodes globals global-values owned-roots]
  (let [cls (Class/forName "ansatz.research.ir.Interpreter$PreparedGraph" true (:loader basis))
        node-class (Class/forName "ansatz.research.ir.Interpreter$ImportNode" true (:loader basis))
        node-array (java.lang.reflect.Array/newInstance node-class (count nodes))
        global-array (header-array basis globals) objects (class (object-array 0))]
    (doseq [[i node] (map-indexed vector nodes)] (java.lang.reflect.Array/set node-array i node))
    (let [types (into-array Class [(class source) Object (class node-array)
                                  (class global-array) objects objects])
          args [source state-token node-array global-array
                (object-array global-values) (object-array owned-roots)]]
      (if factory
        (invoke-static (.getMethod cls factory types) args)
        (.newInstance (.getConstructor cls types) (object-array args))))))
(defn prepared-graph [basis source state-token nodes globals global-values owned-roots]
  (graph-recipe nil basis source state-token nodes globals global-values owned-roots))
(defn selected-owner-graph [basis source state-token nodes globals global-values owned-roots]
  (graph-recipe "selectedOwners" basis source state-token nodes globals global-values owned-roots))
(defn selected-owner-ref-payload-mt-graph
  "Explicit target MT reconstruction for a closed positive region below persistent Refs."
  [basis source state-token nodes globals global-values owned-roots]
  (graph-recipe "selectedOwnersWithPersistentRefPayloadSharing" basis source state-token nodes globals global-values owned-roots))
(defn install-graph! [basis engine graph]
  (vec (.invoke (.getMethod ^Class (:class basis) "installGraph" (into-array Class [(class graph)]))
                engine (object-array [graph]))))
(defn fork!
  "On-demand capture. ROOTS must account for the external owner/alias contract."
  [basis engine roots]
  (let [packet (.invoke (.getMethod ^Class (:class basis) "eagerFork"
                                  (into-array Class [(class (object-array 0))]))
                        engine (object-array [(object-array roots)]))
        cls ^Class (class packet)]
    {:engine (.get (.getField cls "engine") packet)
     :roots (vec (.get (.getField cls "roots") packet))}))

(defn rbmap-runner [basis engine]
  (let [ids (mapv #(int (function-id basis %)) ["mkMap" "fold._redArg" "main._closed_0"])]
    (fn [n]
      (.invoke ^Method (:rbmap basis) engine (object-array (conj ids (int n)))))))

(defn java-value [basis value]
  (if (.isInstance ^Class (:node-class basis) value)
    {:tag (.getInt ^Field (:tag basis) value)
     :fields (mapv #(java-value basis %) (.get ^Field (:fields basis) value))
     :scalar-bytes (mapv #(bit-and 255 %) (.get ^Field (:scalars basis) value))}
    value))

(defn reference-value [world value]
  (cond
    (m/ref? value)
    (let [n (m/node world value) layout (:layout n)
          count (+ (* 8 (or (:usize layout) 0)) (or (:ssize layout) 0))]
      {:tag (:tag n) :fields (mapv #(reference-value world %) (:fields n))
       :scalar-bytes (mapv #(get (:scalar-bytes n) (+ (* 8 (or (:objects layout) 0)) %) 0) (range count))})
    (instance? prototype.machine.Tag value) (:tag value)
    :else value))

(defn measure-rbmap [basis sizes]
  (let [engine (machine basis) run (rbmap-runner basis engine)]
    (try
      (doseq [n [0 1 11 100 300 1000]] (assert (= (quot (+ n 9) 10) (run n))))
      (doseq [_ (range 100)] (run 300))
      (doseq [_ (range 30)] (run 1000))
      {:scope "Original typed exported RBMap on recursive Java IR port. One retained engine, reusable stacks, final result only; no World materialization, no fork/hosted frontend."
       :runs (vec (for [n sizes trial (range 7)]
                    (let [[answer metrics] (benchmark/measure #(run n))]
                      (assert (= (quot (+ n 9) 10) answer))
                      (assoc metrics :n n :trial trial))))}
      (finally (close! basis engine)))))

(defn measure-batch [basis sizes repetitions]
  (let [engine (machine basis)
        ids (mapv #(int (function-id basis %)) ["mkMap" "fold._redArg" "main._closed_0"])
        run (fn [n]
              (.invoke ^Method (:batch basis) engine (object-array (into ids [(int n) (int repetitions)]))))]
    (try
      (doseq [_ (range 5)] (run 300) (run 1000))
      {:scope "Original raw typed IR; adjacent n/n+1 batch matching Lean harness. One engine with warm constants, recursive interpreter, no final World. Preparation excluded."
       :repetitions repetitions
       :runs (vec (for [n sizes trial (range 7)]
                    (let [[checksum metrics] (benchmark/measure #(run n))
                          expected (* (quot repetitions 2)
                                      (+ (quot (+ n 9) 10) (quot (+ (inc n) 9) 10)))]
                      (assert (= expected checksum))
                      (assoc metrics :n n :trial trial :checksum checksum))))}
      (finally (close! basis engine)))))

(defn measure-modes [basis sizes repetitions]
  (let [contexts {:recursive (dissoc basis :explicit) :explicit (assoc basis :explicit true)}
        engines (into {} (map (fn [[mode ctx]] [mode (machine ctx)])) contexts)
        ids (mapv #(int (function-id basis %)) ["mkMap" "fold._redArg" "main._closed_0"])
        run (fn [mode n]
              (.invoke ^Method (:batch basis) (engines mode)
                       (object-array (into ids [(int n) (int repetitions)]))))]
    (try
      (doseq [_ (range 5) n [300 1000] mode [:recursive :explicit]] (run mode n))
      {:scope "Paired recursive and explicit drivers, same prepared Program/heap semantics; adjacent inputs and reusable engine per mode; preparation/capture excluded."
       :repetitions repetitions
       :runs (vec (for [n sizes trial (range 7)
                        mode (if (even? trial) [:recursive :explicit] [:explicit :recursive])]
                    (let [[checksum metrics] (benchmark/measure #(run mode n))]
                      (assert (= checksum (* (quot repetitions 2)
                                             (+ (quot (+ n 9) 10) (quot (+ (inc n) 9) 10)))))
                      (assoc metrics :mode mode :n n :trial trial :checksum checksum))))}
      (finally (doseq [[mode engine] engines] (close! (contexts mode) engine))))))

(defn host-guest-policy
  "Capture independently selected exact Headers; this does not authenticate source bytes."
  [basis outer-headers helper-headers]
  (let [cls (Class/forName "ansatz.research.ir.Interpreter$HostGuestPolicy" true (:loader basis))
        outers (header-array basis outer-headers) helpers (header-array basis helper-headers)]
    (invoke-static (.getMethod cls "of" (into-array Class [(class outers) (class helpers)])) [outers helpers])))
(defn configure-host-guest! [basis engine policy]
  (.invoke (.getMethod ^Class (:class basis) "configureHostGuestCalls" (into-array Class [(class policy)]))
           engine (object-array [policy])))
(defn host-owned-argument [basis value]
  (let [cls (Class/forName "ansatz.research.ir.Interpreter$HostGuestArgument" true (:loader basis))]
    (invoke-static (.getMethod cls "owned" (into-array Class [Object])) [value])))
(defn host-transferred-argument [basis request index]
  (let [cls (Class/forName "ansatz.research.ir.Interpreter$HostGuestArgument" true (:loader basis))]
    (invoke-static (.getMethod cls "fromHostArgument" (into-array Class [(class request) Integer/TYPE]))
                   [request (int index)])))
(defn start-host-guest! [basis engine request header arguments]
  (let [cls (Class/forName "ansatz.research.ir.Interpreter$HostGuestArgument" true (:loader basis))
        array (java.lang.reflect.Array/newInstance cls (count arguments))]
    (doseq [[index argument] (map-indexed vector arguments)] (java.lang.reflect.Array/set array index argument))
    (.invoke (.getMethod ^Class (:class basis) "startHostGuestCall"
                        (into-array Class [(class request) (class header) (class array)]))
             engine (object-array [request header array]))))
(defn start-host-release! [basis engine request argument count]
  (.invoke (.getMethod ^Class (:class basis) "startHostRelease"
                      (into-array Class [(class request) (class argument) Integer/TYPE]))
           engine (object-array [request argument (int count)])))
(defn host-guest-operation [basis engine]
  (.invoke (.getMethod ^Class (:class basis) "currentHostGuestOperation" (make-array Class 0)) engine (object-array 0)))
(defn host-guest-result [basis engine]
  (.invoke (.getMethod ^Class (:class basis) "pendingHostGuestResult" (make-array Class 0)) engine (object-array 0)))
(defn take-host-guest-result! [basis engine request operation]
  (.invoke (.getMethod ^Class (:class basis) "takeHostGuestResult" (into-array Class [(class request) (class operation)]))
           engine (object-array [request operation])))
