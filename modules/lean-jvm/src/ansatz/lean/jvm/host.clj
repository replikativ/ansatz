(ns ansatz.lean.jvm.host
  "Private typed host adapters. Does not admit imports or register Project code."
  (:require [ansatz.lean.jvm.typed-value :as typed]
            [ansatz.lean.jvm.ir :as ir]
            [clojure.string :as str])
  (:import [java.util.function Function]
           [java.util Map List]
           [ansatz.lean.jvm HostBindings LeanType]))

(defn- need [ok message]
  (when-not ok (throw (ex-info message {:code "BindingRejected"}))))

(defn- metadata [value]
  (cond
    (map? value) (let [out (java.util.HashMap.)]
                   (doseq [[k v] value] (.put out k (metadata v))) out)
    (vector? value) (java.util.ArrayList. ^java.util.Collection (mapv metadata value))
    :else value))

(defn compile-types [ctx groups]
  (if (empty? groups) []
   (let [bridge (.loadClass ^ClassLoader (:loader ctx) "ansatz.lean.jvm.ValueBridge")
        method (doto (.getDeclaredMethod bridge "compileRoots" (into-array Class [Class Map Map])) (.setAccessible true))]
    (mapv (fn [{:keys [logical normalized]}]
            (ir/invoke-static method [(:class ctx) (metadata logical) (metadata normalized)])) groups))))

(defn binding-names [^HostBindings bindings]
  (need (= HostBindings (class bindings)) "Actual immutable HostBindings required")
  (mapv (fn [entry]
          (let [name (.name ^ansatz.lean.jvm.HostBindings$Entry entry)
                parts (str/split name #"\." -1)]
            (need (and (<= 1 (count parts) 64) (every? #(<= 1 (count %) 1024) parts)) "Bounded dotted declaration name required")
            (reduce (fn [parent part] ["str" parent part]) ["anonymous"] parts))) (.entries bindings)))

(defn clojure-implementation
  "Capture one IFn target; authenticated import admission supplies the types.
   Capturing a Var's current value does not freeze dependencies or captures."
  [argument-types result-type implementation]
  (let [target (if (instance? clojure.lang.Var implementation) @implementation implementation)
        types (vec argument-types)]
    (when-not (instance? clojure.lang.IFn target)
      (throw (IllegalArgumentException. "Expected an actual Clojure function")))
    (reify Function
      (apply [_ arguments]
        (when-not (= (count types) (count arguments))
          (throw (IllegalArgumentException. "Host argument count differs from admitted signature")))
        (typed/host-value result-type
                          (apply target (mapv typed/view types arguments)))))))

(defn admit-bindings
  "Internal publisher only: ENTRIES/HEADERS/GROUPS must already be authenticated.
   A registry selects implementations; it never authenticates these inputs."
  [ctx ^HostBindings bindings entries headers groups]
  (let [names (binding-names bindings)
        types (compile-types ctx groups)
        loader ^ClassLoader (:loader ctx)
        binding-class (.loadClass loader "ansatz.lean.jvm.internal.exec.Interpreter$PureBinding")
        header-class (.loadClass loader "ansatz.lean.jvm.internal.exec.Interpreter$Header")
        extern-class (.loadClass loader "ansatz.lean.jvm.internal.exec.Interpreter$HostExtern")
        call-class (when (seq names) (.loadClass loader "ansatz.lean.jvm.PureHostCall"))
        ctor (.getConstructor binding-class (into-array Class [header-class]))
        call-ctor (when call-class
                    (doto (.getDeclaredConstructor call-class (into-array Class [extern-class List LeanType Function])) (.setAccessible true)))
        index (into {} (map #(vector (get % "name") %) entries))
        array (java.lang.reflect.Array/newInstance binding-class (count names))
        plans
        (mapv (fn [i name registration]
                (let [entry (get index name) header (get headers (get-in entry ["raw" "name"]))
                      storage (get entry "typedStorage")
                      _ (need (and (true? (get entry "pureBinding")) storage header
                                   (= "definition" (get entry "kind")) (= "pure" (get storage "effect")))
                              "Binding requires selected v4 noinline pure reference definition")
                      roots (nth types (get storage "group"))
                      argument-types (mapv #(nth roots %) (get storage "arguments"))
                      result-type (nth roots (get storage "result"))
                      definition (.newInstance ctor (object-array [header]))
                      descriptor (.invoke (.getMethod binding-class "descriptor" (make-array Class 0)) definition (object-array 0))]
                  (java.lang.reflect.Array/set array i definition)
                  {:header header :descriptor descriptor :registration registration
                   :argument-types argument-types :result-type result-type}))
              (range) names (.entries bindings))
        ;; Validate the entire selection before invoking any user factory.
        selected
        (mapv (fn [{:keys [header descriptor registration argument-types result-type]}]
                (let [implementation (.implementation ^ansatz.lean.jvm.HostBindings$Entry registration)
                      implementation (if-not (.isFactory ^ansatz.lean.jvm.HostBindings$Entry registration) implementation
                                       (if (.isClojure ^ansatz.lean.jvm.HostBindings$Entry registration)
                                         (implementation {:argument-types argument-types :result-type result-type})
                                         (.apply ^Function implementation (ansatz.lean.jvm.HostBindings$Signature. argument-types result-type))))
                      _ (need (if (.isClojure ^ansatz.lean.jvm.HostBindings$Entry registration)
                                (instance? clojure.lang.IFn implementation) (instance? Function implementation))
                              "Host factory must return an implementation function")
                      implementation (if (.isClojure ^ansatz.lean.jvm.HostBindings$Entry registration)
                                       (clojure-implementation argument-types result-type implementation) implementation)
                      _ (need (instance? Function implementation) "Host factory must return an implementation function")
                      call (.newInstance call-ctor (object-array [descriptor argument-types result-type implementation]))]
                  {:header header :descriptor descriptor :call call}))
              plans)]
    {:types types :definitions array
     :headers (into {} (map #(vector (:header %) (:descriptor %)) selected))
     :calls (into {} (map #(vector (:descriptor %) (:call %)) selected))}))

(defn bind-program [ctx definitions]
  (let [program (:program ctx) klass (class program)
        method (.getMethod klass "bindPureDefinitions" (into-array Class [klass (class definitions)]))]
    (assoc ctx :program (ir/invoke-static method [program definitions]))))

(defn complete! [ctx engine calls]
  (let [request (.invoke (.getMethod ^Class (:class ctx) "pendingHostRequest" (make-array Class 0)) engine (object-array 0))
        descriptor (when request (.invoke (.getMethod (class request) "descriptor" (make-array Class 0)) request (object-array 0)))
        call (get calls descriptor)]
    (need (and request call) "Runtime host request has no admitted implementation")
    (let [method (doto (.getDeclaredMethod (class call) "complete" (into-array Class [(:class ctx) (class request)])) (.setAccessible true))]
      (try (.invoke method call (object-array [engine request]))
           (catch java.lang.reflect.InvocationTargetException failure (throw (.getCause failure)))))))
