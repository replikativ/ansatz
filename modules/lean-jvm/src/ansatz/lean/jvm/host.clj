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

(defn required-imports!
  "Only authenticated selected foreign entries may bypass intrinsic admission.
   Require every such entry's implementation before any initialization or factory."
  [bindings entries]
  (let [registered (set (binding-names bindings))
        imports (set (map #(get % "name") (filter #(= "foreign" (get % "hostBinding")) entries)))]
    (need (every? registered imports) "Required foreign implementation is missing")
    imports))

(defn admit-bindings
  "Internal publisher only: entries, headers and groups are authenticated first."
  [ctx ^HostBindings bindings entries headers groups]
  (let [names (binding-names bindings)
        types (compile-types ctx groups)
        loader ^ClassLoader (:loader ctx)
        binding-class (.loadClass loader "ansatz.lean.jvm.internal.exec.Interpreter$HostBinding")
        header-class (.loadClass loader "ansatz.lean.jvm.internal.exec.Interpreter$Header")
        extern-class (.loadClass loader "ansatz.lean.jvm.internal.exec.Interpreter$HostExtern")
        request-class (.loadClass loader "ansatz.lean.jvm.internal.exec.Interpreter$HostRequest")
        call-class (.loadClass loader "ansatz.lean.jvm.HostCall")
        ctor (.getConstructor binding-class (into-array Class [header-class]))
        call-ctor (doto (.getDeclaredConstructor call-class (into-array Class [extern-class List LeanType Function Object])) (.setAccessible true))
        complete (doto (.getDeclaredMethod call-class "complete" (into-array Class [(:class ctx) request-class])) (.setAccessible true))
        pending (.getMethod ^Class (:class ctx) "pendingHostRequest" (make-array Class 0))
        descriptor-method (.getMethod request-class "descriptor" (make-array Class 0))
        bridge (.loadClass loader "ansatz.lean.jvm.ValueBridge")
        compile-io (doto (.getDeclaredMethod bridge "compileIOLayouts" (into-array Class [Class Map])) (.setAccessible true))
        index (into {} (map #(vector (get % "name") %) entries))
        array (java.lang.reflect.Array/newInstance binding-class (count names))
        plans
        (mapv (fn [i name registration]
                (let [entry (get index name) header (get headers (get-in entry ["raw" "name"]))
                      storage (get entry "typedStorage") io? (.isIO ^ansatz.lean.jvm.HostBindings$Entry registration)
                      _ (need (and (#{"reference" "foreign"} (get entry "hostBinding")) storage header
                                   (= (if io? "io" "pure") (get storage "effect")))
                              "Binding requires an eligible declaration with matching effect")
                      group (get storage "group") roots (nth types group)
                      argument-types (mapv #(nth roots %) (get storage "arguments"))
                      result-type (nth roots (get storage "result"))
                      io-layouts (when io? (ir/invoke-static compile-io [(:class ctx) (metadata (:runtime-witnesses (nth groups group)))]))
                      definition (.newInstance ctor (object-array [header]))
                      descriptor (.invoke (.getMethod binding-class "descriptor" (make-array Class 0)) definition (object-array 0))
                      ;; Check the adapter ABI now, without executing user factories.
                      _ (.newInstance call-ctor (object-array [descriptor argument-types result-type
                                                              (reify Function (apply [_ _] (throw (IllegalStateException. "Validation only")))) io-layouts]))]
                  (java.lang.reflect.Array/set array i definition)
                  {:header header :descriptor descriptor :registration registration :io-layouts io-layouts
                   :argument-types argument-types :result-type result-type}))
              (range) names (.entries bindings))
        ;; Validate every declaration/effect before invoking any user factory.
        realize
        (fn []
          (let [selected (mapv (fn [{:keys [header descriptor registration argument-types result-type io-layouts]}]
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
                      call (.newInstance call-ctor (object-array [descriptor argument-types result-type implementation io-layouts]))]
                  {:header header :descriptor descriptor :call call})) plans)]
            (if (empty? selected) {}
              {:pending pending :descriptor descriptor-method :complete complete
               :implementations (into {} (map #(vector (:descriptor %) (:call %)) selected))})))]
    {:types types :definitions array
     :headers (into {} (map #(vector (:header %) (:descriptor %)) plans))
     :realize realize}))

(defn bind-program [ctx definitions]
  (let [program (:program ctx) klass (class program)
        method (.getMethod klass "bindHostDefinitions" (into-array Class [klass (class definitions)]))]
    (assoc ctx :program (ir/invoke-static method [program definitions]))))

(defn complete! [ctx engine {:keys [pending descriptor complete implementations]}]
  (let [request (.invoke ^java.lang.reflect.Method pending engine (object-array 0))
        key (when request (.invoke ^java.lang.reflect.Method descriptor request (object-array 0)))
        call (get implementations key)]
    (need (and request call) "Runtime host request has no admitted implementation")
    (try (.invoke ^java.lang.reflect.Method complete call (object-array [engine request]))
         (catch java.lang.reflect.InvocationTargetException failure (throw (.getCause failure))))))
