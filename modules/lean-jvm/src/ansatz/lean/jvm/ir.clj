(ns ansatz.lean.jvm.ir
  "Internal adapter for the packaged canonical Java interpreter. These wrappers
   prepare trusted original rows and drive its existing ownership protocol; they
   do not authenticate source bytes, infer Lean types or establish Init startup.
   No research interpreter, benchmark, runtime javac or source checkout is used."
  (:import [java.lang.reflect Method Constructor Field]))

(defn basis-for-class
  "Internal adapter/test seam for one already-linked engine Class. Creates no
   classloader and compiles no code. Production normally uses linked-basis."
  [^Class cls]
  (when-not (= "ansatz.research.ir.Interpreter" (.getName cls))
    (throw (ex-info "Expected the canonical Interpreter class" {})))
  (let [loader (.getClassLoader cls)
        program (Class/forName "ansatz.research.ir.Interpreter$Program" true loader)
        node (Class/forName "ansatz.research.ir.Interpreter$Node" true loader)]
    {:loader loader :class cls :node-class node
     :prepare (.getMethod cls "prepare" (into-array Class [java.util.List]))
     :constructor (.getConstructor cls (into-array Class [program]))
     :constructor-explicit (.getConstructor cls (into-array Class [program Boolean/TYPE]))
     :constructor-initializing (.getConstructor cls (into-array Class [program Boolean/TYPE Boolean/TYPE]))
     :function-id (.getMethod program "functionId" (into-array Class [String]))
     :invoke (.getMethod cls "invoke" (into-array Class [Integer/TYPE (class (object-array 0))]))
     :inc (.getMethod cls "inc" (into-array Class [Object Integer/TYPE]))
     :dec (.getMethod cls "dec" (into-array Class [Object Integer/TYPE]))
     :close (.getMethod cls "close" (make-array Class 0))
     :start (.getMethod cls "start" (into-array Class [Integer/TYPE (class (object-array 0))]))
     :start-release (.getMethod cls "startRelease" (into-array Class [Object Integer/TYPE]))
     :advance (.getMethod cls "advance" (into-array Class [Long/TYPE]))
     :take-result (.getMethod cls "takeResult" (make-array Class 0))
     :phase (.getMethod cls "phase" (make-array Class 0))
     :depth (.getMethod cls "continuationDepth" (make-array Class 0))
     :instructions (.getMethod cls "instructionCount" (make-array Class 0))
     :active (.getMethod cls "activeFunction" (make-array Class 0))
     :tag (.getField node "tag") :rc (.getField node "rc")
     :fields (.getField node "fields") :scalars (.getField node "scalars")}))

(defn linked-basis
  "Resolve the already-compiled engine on the application classpath. The caller
   never supplies a class directory, compiler, jar path or research source root."
  []
  (basis-for-class (Class/forName "ansatz.research.ir.Interpreter" true
                                (clojure.lang.RT/baseLoader))))

(defn invoke-static [^Method method args] (.invoke method nil (object-array args)))

(defn machine
  "Create a task-free engine; execution and initialization remain explicit.
   Extended task/build/profiling policies are outside this initial adapter."
  [basis]
  (when (some #(get basis %) [:task-runtime :build-identity :profiling-policy])
    (throw (ex-info "Extended runtime policies are outside this adapter" {})))
  (.newInstance ^Constructor (:constructor-initializing basis)
                (object-array [(:program basis) (boolean (:explicit basis))
                               (boolean (:initializing basis))])))

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
  "Attach the opt-in host-boundary API from this exact already-linked engine."
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

(defn host-request [basis engine]
  (.invoke ^Method (:host-request basis) engine (object-array 0)))

(defn request-value
  "Borrow a request accessor; arguments acquire no new guest ownership."
  [request accessor]
  (.invoke (.getMethod ^Class (class request) accessor (make-array Class 0)) request (object-array 0)))

(defn resume-host! [basis engine request value]
  (.invoke ^Method (:resume-host basis) engine (object-array [request value])))

(defn fail-host! [basis engine request cause]
  (.invoke ^Method (:fail-host basis) engine (object-array [request cause])))

(defn start-initializer! [basis engine global action]
  (.invoke (.getMethod ^Class (:class basis) "startInitializer"
                       (into-array Class [(class global) (class action)]))
           engine (object-array [global action])))
(defn complete-initializer! [basis engine]
  (.invoke (.getMethod ^Class (:class basis) "completeInitializer" (make-array Class 0))
           engine (object-array 0)))
