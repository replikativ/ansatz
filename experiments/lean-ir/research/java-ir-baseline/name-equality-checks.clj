(ns java-ir-name-equality-checks
  "Pinned borrowed Name equality and genuine constructor/wrapper ownership."
  (:require [clojure.test :refer [deftest is run-tests]]
            [clojure.data.json :as json] [clojure.edn :as edn]
            [java-ir-baseline :as j] [java-ir-baseline-checks :as c]
            [java-ir-extern-checks :as x] [java-ir-generation-checks :as g]
            [java-ir-host-checks :as host] [java-ir-header-checks :as header]
            [java-ir-pointer-checks :as pointer] [lean-compatibility-corpus :as corpus]))
(def ^:dynamic *basis* nil)
(def fixture "test/fixtures/java-name-equality-runtime/original-rows.json")
(defn rows [path] (mapv #(get % "row") (json/read-str (slurp path))))
(def originals (rows fixture))
(def primitive (first originals))
(defn context
  ([] (context []))
  ([extra]
   (assoc *basis* :program (j/invoke-static (:prepare *basis*)
     [(x/raw (concat originals (rows "test/fixtures/java-u64-runtime/name-rows.json") extra))]))))
(defn str-name [ctx engine parent value] (j/call ctx engine "Lean.Name.str._override" [parent value]))
(defn num-name [ctx engine parent value] (j/call ctx engine "Lean.Name.num._override" [parent value]))
(defn eq [ctx engine a b]
  (j/retain! ctx engine a) (j/retain! ctx engine b)
  (j/call ctx engine "Lean.Name.beq._boxed" [a b]))
(defn fields [ctx value] (.get ^java.lang.reflect.Field (:fields ctx) value))
(defn scalars [ctx value] (.get ^java.lang.reflect.Field (:scalars ctx) value))
(defn copy-hash! [ctx target source] (System/arraycopy (scalars ctx source) 0 (scalars ctx target) 0 8))
(defn flip-hash! [ctx value]
  (let [bytes ^bytes (scalars ctx value)] (aset-byte bytes 0 (unchecked-byte (bit-xor 1 (aget bytes 0))))))

(deftest exact-original-abi-and-genuine-owned-wrapper
  (let [manifest (edn/read-string (slurp "test/fixtures/java-name-equality-runtime/provenance.edn"))
        ctx (context) engine (j/machine ctx)]
    (try
      (is (= 2 (count originals)))
      (is (= (:fixture-sha256 manifest) (corpus/sha256 fixture)))
      (is (= "lean_name_eq" (j/invoke-static (.getMethod ^Class (:class ctx) "validateExternAbi"
                  (into-array Class [java.util.Map])) [primitive])))
      (is (= [true true] (mapv #(get % "borrow") (get-in primitive ["ir" "extern" "xs"]))))
      (let [a (str-name ctx engine 0 "same") b (str-name ctx engine 0 "same")]
        (is (= 1 (j/call ctx engine "Lean.Name.beq._boxed" [a b])))
        (is (= 0 (c/rc ctx a) (c/rc ctx b))))
      (finally (j/close! ctx engine)))))

(deftest anonymous-alias-distinct-and-large-natural-components
  (let [ctx (context) engine (j/machine ctx)
        large (.shiftLeft java.math.BigInteger/ONE 64)
        a (str-name ctx engine 0 "a\u0000é😀") b (str-name ctx engine 0 "a\u0000é😀")
        n (num-name ctx engine 0 large) same-number (num-name ctx engine 0 large)
        different (num-name ctx engine 0 (.add large java.math.BigInteger/ONE))
        mixed (num-name ctx engine 0 7)]
    (try
      (is (= 1 (eq ctx engine 0 (Long. "0"))))
      (is (= 1 (eq ctx engine a a) (eq ctx engine a b)))
      (is (nil? (host/private-value a "metadata")))
      (is (= 0 (eq ctx engine 0 a) (eq ctx engine a mixed)))
      (is (= 1 (eq ctx engine n same-number)))
      (is (java.util.Arrays/equals ^bytes (scalars ctx n) ^bytes (scalars ctx different)))
      (is (= 0 (eq ctx engine n different)))
      (is (= 1 (c/rc ctx a) (c/rc ctx b) (c/rc ctx n)))
      (finally
        (doseq [value [a b n same-number different mixed]] (j/release! ctx engine value))
        (j/close! ctx engine)))))

(deftest top-cached-hash-is-trusted-but-parent-hashes-are-not-rechecked
  (let [ctx (context) engine (j/machine ctx)
        p (str-name ctx engine 0 "parent") q (str-name ctx engine 0 "parent")
        a (str-name ctx engine p "leaf") b (str-name ctx engine q "leaf")
        mixed (num-name ctx engine 0 1)]
    (try
      ;; Deliberate cache corruption probes the exact native algorithm.
      (flip-hash! ctx q)
      (is (= 0 (eq ctx engine p q)))
      (is (= 1 (eq ctx engine a b)))
      (flip-hash! ctx b)
      (is (= 0 (eq ctx engine a b)))
      (copy-hash! ctx mixed a)
      (is (= 0 (eq ctx engine a mixed)))
      (finally
        (doseq [value [a b mixed]] (j/release! ctx engine value))
        (j/close! ctx engine)))))

(deftest shared-prefixes-and-pointer-metadata-forks-remain-valid-names
  (let [ctx (context (pointer/common)) engine (j/machine ctx)
        prefix (str-name ctx engine 0 "prefix")
        _ (j/retain! ctx engine prefix)
        a (str-name ctx engine prefix "leaf") b (str-name ctx engine prefix "leaf")]
    (try
      (is (= 1 (eq ctx engine a b))) (is (= 2 (c/rc ctx prefix)))
      (is (= 1 (pointer/same ctx engine a a)))
      (let [{child :engine [ca cb] :roots} (j/fork! ctx engine [a b])]
        (try
          (is (= 1 (eq ctx child ca cb)))
          (is (= (pointer/word a) (pointer/word ca)))
          (is (g/bad? #(j/call ctx child "Lean.Name.beq._boxed" [a cb])))
          (is (= "idle" (j/phase ctx child)))
          (is (= 1 (c/rc ctx a) (c/rc ctx cb)))
          (finally (j/release! ctx child ca) (j/release! ctx child cb) (j/close! ctx child))))
      (finally (j/release! ctx engine a) (j/release! ctx engine b) (j/close! ctx engine)))
    (is (= 0 (c/rc ctx prefix)))))

(deftest long-parent-chains-compare-without-java-recursion
  (let [ctx (context) engine (j/machine ctx)
        chain (fn [] (loop [i 0 parent 0]
                       (if (= i 12000) parent (recur (inc i) (str-name ctx engine parent "segment")))))
        a (chain) b (chain)]
    (try
      (is (= 1 (j/call ctx engine "Lean.Name.beq._boxed" [a b])))
      (is (= 0 (c/rc ctx a) (c/rc ctx b)))
      (finally (j/close! ctx engine)))))

(deftest raw-borrowed-root-pap-makeclosure-and-import-reject-before-effects
  (let [ctx (context) engine (j/machine ctx) value (str-name ctx engine 0 "owned")]
    (try
      (is (g/bad? #(j/call ctx engine "Lean.Name.beq" [value value])))
      (is (= "idle" (j/phase ctx engine))) (is (= 1 (c/rc ctx value)))
      (is (g/bad? #(j/make-closure! ctx engine "Lean.Name.beq" [])))
      (is (g/bad? #(context [(c/decl "partial" [] "object"
                   (c/let-ir 1 "object" {:pap {:c (get primitive "name") :ys []}} (c/ret 1)))])))
      (let [base (j/prepare-host-program *basis* [] []) source (j/source-binding base (Object.))
            target (j/declaration-header source primitive header/digest)
            raw (j/register-headers base [target]) e (j/machine raw)]
        (try
          (is (g/bad? #(j/install-graph! raw e
             (j/prepared-graph raw source (Object.) [(j/graph-node raw {:kind :closure :id 1 :target target})]
                               [] [] [(j/graph-ref raw 1)]))))
          (is (false? (host/private-value e "graphInstalled")))
          (finally (j/close! raw e))))
      (finally (j/release! ctx engine value) (j/close! ctx engine)))))

(deftest malformed-current-heads-and-components-reject-without-primitive-owner-effects
  (doseq [descriptor [{:kind :ref :id 1 :fields [0]}
                      {:kind :array :id 1 :fields [0 0]}
                      {:kind :byte-array :id 1 :bytes [0]}
                      {:kind :ctor :id 1 :tag 0 :fields [0 0] :scalars (repeat 8 0)}
                      {:kind :ctor :id 1 :tag 1 :fields [0 0] :scalars (repeat 8 0)}
                      {:kind :ctor :id 1 :tag 2 :fields [0 -1] :scalars (repeat 8 0)}
                      {:kind :ctor :id 1 :tag 2 :fields [0 "bad"] :scalars (repeat 8 0)}
                      {:kind :ctor :id 1 :tag 1 :fields [0 "ok"] :scalars []}]]
    (let [ctx (context) engine (j/machine ctx) source (j/source-binding ctx (Object.))]
      (if (= -1 (second (:fields descriptor)))
        (is (g/bad? #(j/graph-node ctx descriptor)))
        (let [[value] (j/install-graph! ctx engine
                        (j/prepared-graph ctx source (Object.) [(j/graph-node ctx descriptor)]
                                          [] [] [(j/graph-ref ctx 1)]))
              before [(c/rc ctx value) (host/private-value engine "stores") (host/private-value engine "retains")]]
          (is (g/bad? #(j/call ctx engine "Lean.Name.beq._boxed" [value value])))
          (is (= before [(c/rc ctx value) (host/private-value engine "stores") (host/private-value engine "retains")]))))))
  (doseq [value [1 -1 "anonymous" (biginteger 0)]]
    (let [ctx (context) engine (j/machine ctx)]
      (is (g/bad? #(j/call ctx engine "Lean.Name.beq._boxed" [value value]))))))

(deftest logical-natural-carriers-compare-by-magnitude-and-negative-components-reject
  (let [ctx (context) engine (j/machine ctx) a (num-name ctx engine 0 7)
        b (num-name ctx engine 0 (biginteger 7))]
    (try
      (is (= 1 (eq ctx engine a b)))
      (finally (j/release! ctx engine a) (j/release! ctx engine b) (j/close! ctx engine))))
  (let [ctx (context) engine (j/machine ctx) source (j/source-binding ctx (Object.))
        descriptor (j/graph-node ctx {:kind :ctor :id 1 :tag 2
                                     :fields [0 (j/graph-int ctx -1)] :scalars (repeat 8 0)})
        [value] (j/install-graph! ctx engine
                  (j/selected-owner-graph ctx source (Object.) [descriptor] [] [] [(j/graph-ref ctx 1)]))]
    (is (re-find #"Nat component" (c/failure #(j/call ctx engine "Lean.Name.beq._boxed" [value value]))))
    (is (= 0 (c/rc ctx value) (host/private-value engine "stores"))))
  (let [ctx (context) engine (j/machine ctx) source (j/source-binding ctx (Object.))
        [a b] (j/install-graph! ctx engine
                (j/prepared-graph ctx source (Object.)
                  [(j/graph-node ctx {:kind :ctor :id 1 :tag 1 :fields ["not a parent" "leaf"] :scalars (repeat 8 0)})
                   (j/graph-node ctx {:kind :ctor :id 2 :tag 1 :fields [0 "leaf"] :scalars (repeat 8 0)})]
                  [] [] [(j/graph-ref ctx 1) (j/graph-ref ctx 2)]))]
    (is (re-find #"anonymous zero or constructor" (c/failure #(j/call ctx engine "Lean.Name.beq._boxed" [a b]))))
    (is (= 0 (c/rc ctx a) (c/rc ctx b) (host/private-value engine "stores")))))

(deftest nonterminating-nonalias-cycles-have-an-explicit-step-bound
  (let [ctx (context) engine (j/machine ctx) source (j/source-binding ctx (Object.))
        [a b] (j/install-graph! ctx engine
                (j/prepared-graph ctx source (Object.)
                  [(j/graph-node ctx {:kind :ctor :id 1 :tag 1 :fields [(j/graph-ref ctx 1) "x"] :scalars (repeat 8 0)})
                   (j/graph-node ctx {:kind :ctor :id 2 :tag 1 :fields [(j/graph-ref ctx 2) "x"] :scalars (repeat 8 0)})]
                  [] [] [(j/graph-ref ctx 1) (j/graph-ref ctx 2)]))]
    ;; General graphs can cycle; these values are deliberately outside well-founded Name.
    (is (re-find #"depth/cycle outside bounded" (c/failure #(j/call ctx engine "Lean.Name.beq._boxed" [a b]))))
    (is (= 0 (c/rc ctx a) (c/rc ctx b) (host/private-value engine "stores")))))

(defn forged-raw-closure [ctx]
  (let [cls ^Class (:node-class ctx) ctor (.getDeclaredConstructor cls (into-array Class [Integer/TYPE Integer/TYPE Integer/TYPE]))
        _ (.setAccessible ctor true) value (.newInstance ctor (object-array [(int 245) (int 0) (int 0)]))
        functions (host/private-value (:program ctx) "functions")
        function (aget ^objects functions (int (j/function-id ctx "Lean.Name.beq")))]
    (doseq [[name payload] [["closure" function] ["metadata" (host/private-value (:program ctx) "generation")]]]
      (let [field (.getDeclaredField cls name)] (.setAccessible field true) (.set field value payload)))
    value))

(deftest first-class-borrowed-closure-and-host-reply-fences-are-preclaim
  (let [spec host/owned
        rows (concat originals (rows "test/fixtures/java-u64-runtime/name-rows.json")
                     [(host/ext "host" spec) (first g/common) (second g/common)])
        ctx (j/prepare-host-program *basis* (x/raw rows) [spec]) engine (j/machine ctx)
        value (forged-raw-closure ctx)]
    (try
      (is (g/bad? #(j/call ctx engine "identity" [value])))
      (is (g/bad? #(j/call ctx engine "apply" [value 0])))
      (is (= "idle" (j/phase ctx engine))) (is (= 1 (c/rc ctx value)))
      (j/start! ctx engine "host" [0])
      (let [request (j/host-request ctx engine)]
        (is (g/bad? #(j/resume-host! ctx engine request value)))
        (is (identical? request (j/host-request ctx engine)))
        (is (= 1 (c/rc ctx value)))
        (j/resume-host! ctx engine request 0) (is (= 0 (j/take-result! ctx engine))))
      (finally (j/release! ctx engine value) (j/close! ctx engine))))
  (is (g/bad? #(j/prepare-host-program *basis* [] [(host/spec "lean_name_eq" ["tobject" "tobject"] [true true] "uint8")]))))

(deftest tagged-immediate-deletion-is-a-noop-and-heap-deletion-transfers-fields
  (let [row (c/decl "delete-shell" [(c/p 1 "object") (c/p 2 "object")] "object"
              ["del" {:idx 1} (c/ret 2)])
        ctx (context [row]) engine (j/machine ctx)]
    (try
      (doseq [value [0 1 255 Long/MAX_VALUE]]
        (let [before (host/private-value engine "shellDeletes")]
          (is (= 42 (j/call ctx engine "delete-shell" [value 42])))
          (is (= before (host/private-value engine "shellDeletes")))))
      (let [source (j/source-binding ctx (Object.))
            [parent] (j/install-graph! ctx engine
                       (j/selected-owner-graph ctx source (Object.)
                         [(j/graph-node ctx {:kind :ctor :id 1 :rc 99 :tag 1 :fields [(j/graph-ref ctx 2)]})
                          (j/graph-node ctx {:kind :ctor :id 2 :rc 99 :tag 0 :fields [7]})]
                         [] [] [(j/graph-ref ctx 1)]))
            child (aget ^objects (fields ctx parent) 0)
            before (host/private-value engine "shellDeletes")
            answer (j/call ctx engine "delete-shell" [parent child])]
        (is (identical? child answer)) (is (= 1 (c/rc ctx child)))
        (is (host/private-value parent "dead"))
        (is (nil? (aget ^objects (fields ctx parent) 0)))
        (is (= (inc before) (host/private-value engine "shellDeletes")))
        (j/release! ctx engine answer))
      (finally (j/close! ctx engine)))))

(defn check! [basis] (binding [*basis* basis] (run-tests 'java-ir-name-equality-checks)))
