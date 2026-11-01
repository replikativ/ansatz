(ns java-ir-byte-array-checks
  "True raw ByteArrays: closed import, copy-on-write and forked payload/state."
  (:require [clojure.test :refer [deftest is run-tests]]
            [clojure.data.json :as json] [clojure.edn :as edn]
            [java-ir-baseline :as j] [java-ir-baseline-checks :as c]
            [java-ir-extern-checks :as x] [java-ir-generation-checks :as g]
            [java-ir-host-checks :as host] [java-ir-ref-checks :as ref]
            [java-ir-array-checks :as array] [lean-compatibility-corpus :as corpus]))
(def ^:dynamic *basis* nil)
(def fixture "test/fixtures/java-byte-array-runtime/original-rows.json")
(defn originals [] (json/read-str (slurp fixture)))
(defn context []
  (let [rows (mapv #(get % "row") (concat (originals) (ref/originals)))
        helpers [(c/decl "ordinary8" [(c/p 1 "object")] "object"
                   (c/let-ir 2 "object" (c/ctor 0 [] 8) (c/ret 2)))
                 (c/decl "unbox-word" [(c/p 1 "object")] "usize"
                   (c/let-ir 2 "usize" {:unbox {:x {:idx 1}}} (c/ret 2)))
                 (c/decl "project" [(c/p 1 "object")] "object"
                   (c/let-ir 2 "object" {:proj {:x {:idx 1} :i 0}} (c/ret 2)))]]
    (assoc *basis* :program (j/invoke-static (:prepare *basis*) [(into rows (x/raw helpers))]))))
(defn payload [ctx node]
  (let [length (.invoke (.getMethod (class node) "byteArraySize" (make-array Class 0)) node (object-array 0))
        bytes ^bytes (.get ^java.lang.reflect.Field (:scalars ctx) node)]
    (mapv #(Byte/toUnsignedInt (aget bytes %)) (range length))))
(defn raw-descriptor [ctx id rc data]
  (let [cls (Class/forName "ansatz.research.ir.Interpreter$ImportNode" true (:loader ctx))]
    (j/invoke-static (.getMethod cls "byteArray" (into-array Class [Long/TYPE Integer/TYPE (class (byte-array 0))]))
                     [(long id) (int rc) data])))
(defn install [ctx engine nodes roots selected?]
  (let [source (j/source-binding ctx (Object.))]
    (j/install-graph! ctx engine
      ((if selected? j/selected-owner-graph j/prepared-graph) ctx source (Object.) nodes [] [] roots))))
(defn push! [ctx engine value byte] (j/call ctx engine "ByteArray.push._boxed" [value byte]))
(defn read! [ctx engine value index]
  (j/retain! ctx engine value)
  (j/call ctx engine "ByteArray.get._boxed" [value index 0]))
(defn counters [engine] (mapv #(host/private-value engine %) ["allocations" "stores" "retains" "releases"]))

(deftest original-fixture-and-borrowed-entry-guards
  (let [ctx (context) manifest (edn/read-string (slurp "test/fixtures/java-byte-array-runtime/provenance.edn"))]
    (is (= 8 (count (originals))))
    (is (= (:fixture-sha256 manifest) (corpus/sha256 fixture)))
    (doseq [r (originals) :when (get-in r ["row" "ir" "extern"])]
      (is (string? (j/invoke-static (.getMethod ^Class (:class *basis*) "validateExternAbi"
                                                (into-array Class [java.util.Map])) [(get r "row")]))))
    (doseq [name ["ByteArray.get" "ByteArray.size"] :let [engine (j/machine ctx)]]
      (try
        (is (re-find #"Borrowed ByteArray primitive" (c/failure #(j/call ctx engine name []))))
        (is (g/bad? #(j/make-closure! ctx engine name [])))
        (finally (j/close! ctx engine))))))

(deftest raw-import-clones-live-bytes-and-is-not-subject-to-ctor1024-byte-cap
  (let [ctx (context) engine (j/machine ctx) input (byte-array (repeat 2049 (unchecked-byte 255)))
        descriptor (raw-descriptor ctx 1 0 input)]
    (aset-byte input 0 0)
    (let [[value] (install ctx engine [descriptor] [(j/graph-ref ctx 1)] false)]
      (try
        (is (= 2049 (count (payload ctx value))))
        (is (= 255 (first (payload ctx value))))
        (is (= 0 (c/rc ctx value)))
        (is (= 255 (read! ctx engine value 2048)))
        (is (= 0 (alength ^objects (.get ^java.lang.reflect.Field (:fields ctx) value))))
        (finally (j/close! ctx engine))))))

(deftest selected-byte-owner-counts-include-persistent-parent-and-root-aliases
  (let [ctx (context) engine (j/machine ctx) r #(j/graph-ref ctx %)
        [parent a b] (install ctx engine
                       [(raw-descriptor ctx 1 99 (byte-array [1 2]))
                        (j/graph-node ctx {:kind :array :id 2 :fields [(r 1) (r 1)]})]
                       [(r 2) (r 1) (r 1)] true)]
    (try
      (is (identical? a b)) (is (= 4 (c/rc ctx a)))
      (is (= 0 (c/rc ctx parent)))
      (j/release! ctx engine a) (j/release! ctx engine b)
      (is (= 2 (c/rc ctx a)))
      (finally (j/close! ctx engine)))))

(deftest object-array-mk-transfers-container-once-and-copies-exact-bytes
  (let [rows (mapv #(get % "row") (concat (originals) (json/read-str (slurp "test/fixtures/java-array-runtime/original-rows.json"))))
        ctx (assoc *basis* :program (j/invoke-static (:prepare *basis*) [rows])) engine (j/machine ctx)
        [input] (install ctx engine [(j/graph-node ctx {:kind :array :id 1 :rc 99 :fields [0 127 128 255]})]
                         [(j/graph-ref ctx 1)] true)
        before (counters engine) value (j/call ctx engine "ByteArray.mk._boxed" [input])]
    (try
      (is (= [1 0 0 1] (mapv - (counters engine) before)))
      (is (host/private-value input "dead"))
      (is (= [0 127 128 255] (payload ctx value)))
      (is (= 1 (c/rc ctx value)))
      (j/retain! ctx engine value)
      (is (= 4 (j/call ctx engine "ByteArray.size._boxed" [value])))
      (is (= 255 (read! ctx engine value 3)))
      (finally (j/release! ctx engine value) (j/close! ctx engine)))))

(deftest push-unique-growth-reuse-and-shared-persistent-copies
  (doseq [rc [0 99] shared? [false true]]
    (let [ctx (context) engine (j/machine ctx)
          [a] (install ctx engine [(raw-descriptor ctx 1 rc (byte-array [7]))] [(j/graph-ref ctx 1)] true)
          _ (when shared? (j/retain! ctx engine a)) before (counters engine)
          b (push! ctx engine a 128)]
      (try
        (is (not (identical? a b)))
        (is (= [1 1 0 (if (zero? rc) 0 1)] (mapv - (counters engine) before)))
        (is (= [7 128] (payload ctx b)))
        (is (= 4 (alength ^bytes (.get ^java.lang.reflect.Field (:scalars ctx) b))))
        (let [before (counters engine) c (push! ctx engine b 255)]
          (is (identical? b c))
          (is (= [0 1 0 0] (mapv - (counters engine) before)))
          (is (= [7 128 255] (payload ctx c))))
        (when (or shared? (zero? rc)) (is (= [7] (payload ctx a))))
        (finally
          (j/release! ctx engine b)
          (when shared? (j/release! ctx engine a))
          (j/close! ctx engine))))))

(deftest fork-copies-state-and-capacity-bytes-preserving-aliases
  (let [ctx (context) engine (j/machine ctx)
        [a] (install ctx engine [(raw-descriptor ctx 1 99 (byte-array [0]))] [(j/graph-ref ctx 1)] true)
        a (push! ctx engine a 1)
        child (j/fork! ctx engine [a a]) child-engine (:engine child) [b again] (:roots child)]
    (try
      (is (identical? b again)) (is (not (identical? a b)))
      (is (= 1 (c/rc ctx a) (c/rc ctx b)))
      (is (identical? b (push! ctx child-engine b 255)))
      (is (= [0 1] (payload ctx a))) (is (= [0 1 255] (payload ctx b)))
      (is (not (identical? (.get ^java.lang.reflect.Field (:scalars ctx) a)
                           (.get ^java.lang.reflect.Field (:scalars ctx) b))))
      (is (identical? a (push! ctx engine a 128)))
      (is (= [0 1 128] (payload ctx a))) (is (= [0 1 255] (payload ctx b)))
      (is (= 4 (alength ^bytes (.get ^java.lang.reflect.Field (:scalars ctx) b))))
      (finally (j/release! ctx engine a) (j/release! ctx child-engine b)
               (j/close! ctx engine) (j/close! ctx child-engine)))))

(deftest metadata-kind-fences-prevent-byte-array-ctor-box-and-array-confusion
  (let [ctx (context)]
    (doseq [name ["unbox-word" "project"]]
      (let [engine (j/machine ctx)
            [value] (install ctx engine [(raw-descriptor ctx 1 99 (byte-array 8))] [(j/graph-ref ctx 1)] true)]
        (.setInt ^java.lang.reflect.Field (:tag ctx) value 0)
        (is (re-find #"not a constructor" (c/failure #(j/call ctx engine name [value]))))
        (is (= 1 (c/rc ctx value))) (j/release! ctx engine value)))
    (let [engine (j/machine ctx) value (j/call ctx engine "ordinary8" [0])]
      (.setInt ^java.lang.reflect.Field (:tag ctx) value 248)
      (is (re-find #"Expected ByteArray" (c/failure #(j/call ctx engine "ByteArray.get._boxed" [value 0 0]))))
      (is (= 1 (c/rc ctx value))) (j/release! ctx engine value))))

(deftest malformed-numeric-bytes-and-aggregate-budget-do-not-consume-import
  (let [ctx (context) engine (j/machine ctx) source (j/source-binding ctx (Object.))]
    (try
      (doseq [bytes [nil [-1] [256] [1.5] [true] #{0 1}]]
        (is (g/bad? #(j/graph-node ctx {:kind :byte-array :id 1 :bytes bytes}))))
      (is (g/bad? #(j/graph-node ctx {:kind :byte-array :id 1 :bytes [] :fields []})))
      (let [data (byte-array (inc (* 8 1024 1024)))
            nodes [(raw-descriptor ctx 1 0 data) (raw-descriptor ctx 2 0 data)]]
        (is (re-find #"scalar byte" (c/failure #(j/prepared-graph ctx source (Object.) nodes [] [] [])))))
      (is (false? (host/private-value engine "graphInstalled")))
      (is (= [] (install ctx engine [] [] false)))
      (finally (j/close! ctx engine)))))
(deftest mk-rejects-invalid-element-before-allocation-or-consumption
  (let [ctx (context) engine (j/machine ctx) r #(j/graph-ref ctx %)
        [input] (install ctx engine
                  [(j/graph-node ctx {:kind :array :id 1 :rc 99 :fields [7 (r 2)]})
                   (j/graph-node ctx {:kind :ctor :id 2 :rc 99 :tag 0 :fields [0]})]
                  [(r 1)] true)
        element (aget ^objects (.get ^java.lang.reflect.Field (:fields ctx) input) 1)
        before (counters engine)]
    (try
      (is (not= "NO ERROR" (c/failure #(j/call ctx engine "ByteArray.mk._boxed" [input]))))
      (is (= before (counters engine)))
      (is (= 1 (c/rc ctx input) (c/rc ctx element)))
      (is (false? (host/private-value input "dead")))
      (finally
        (if (:explicit ctx) (is (g/bad? #(j/close! ctx engine)))
            (do (j/release! ctx engine input) (j/close! ctx engine)))))))

(deftest proof-backed-get-rejects-spare-capacity-and-huge-index-without-effects
  (doseq [index [2 (java.math.BigInteger. "18446744073709551616")]]
    (let [ctx (context) engine (j/machine ctx)
          [a] (install ctx engine [(raw-descriptor ctx 1 99 (byte-array [7]))]
                       [(j/graph-ref ctx 1)] true)
          a (push! ctx engine a 8) before (counters engine)]
      (try
        (is (= 4 (alength ^bytes (.get ^java.lang.reflect.Field (:scalars ctx) a))))
        (is (re-find #"index outside live size"
                     (c/failure #(j/call ctx engine "ByteArray.get._boxed" [a index 0]))))
        (is (= before (counters engine)))
        (is (= 1 (c/rc ctx a)))
        (is (= [7 8] (payload ctx a)))
        (finally
          (if (:explicit ctx) (is (g/bad? #(j/close! ctx engine)))
              (do (j/release! ctx engine a) (j/close! ctx engine))))))))

(deftest raw-borrowed-byte-closures-are-rejected-before-import-publication
  (doseq [name ["ByteArray.get" "ByteArray.size"]]
    (let [base (j/prepare-host-program *basis* [] []) source (j/source-binding base (Object.))
          row (first (filter #(and (get-in % ["row" "ir" "extern"])
                                   (= (last (get-in % ["row" "name"]))
                                      (last (clojure.string/split name #"\.")))) (originals)))
          header (j/declaration-header source (get row "row") (apply str (repeat 64 "a")))
          ctx (j/register-headers base [header]) engine (j/machine ctx)]
      (try
        (is (g/bad? #(j/install-graph! ctx engine
                       (j/prepared-graph ctx source (Object.)
                         [(j/graph-node ctx {:kind :closure :id 1 :target header :fields []})]
                         [] [] [(j/graph-ref ctx 1)]))))
        (is (false? (host/private-value engine "graphInstalled")))
        (is (= [] (install ctx engine [] [] false)))
        (finally (j/close! ctx engine))))))

(deftest shared-and-persistent-byte-arrays-copy-with-spare-capacity
  (doseq [persistent? [false true]]
    (let [ctx (context) engine (j/machine ctx)
          [a] (install ctx engine [(raw-descriptor ctx 1 99 (byte-array [1]))]
                       [(j/graph-ref ctx 1)] true)
          a (push! ctx engine a 2)
          _ (if persistent? (.setInt ^java.lang.reflect.Field (:rc ctx) a 0)
                           (j/retain! ctx engine a))
          before (counters engine) b (push! ctx engine a 3)]
      (try
        (is (not (identical? a b)))
        (is (= [1 2] (payload ctx a))) (is (= [1 2 3] (payload ctx b)))
        (is (= 4 (alength ^bytes (.get ^java.lang.reflect.Field (:scalars ctx) b))))
        (is (= [1 1 0 (if persistent? 0 1)] (mapv - (counters engine) before)))
        (finally (j/release! ctx engine a) (j/release! ctx engine b) (j/close! ctx engine))))))

(deftest borrowed-size-pap-is-rejected-and-fget-checks-its-erased-proof
  (let [rows (mapv #(get % "row") (originals))
        raw-name (fn [suffix] (get (first (filter #(and (get-in % ["ir" "extern"])
                                                       (= suffix (last (get % "name")))) rows)) "name"))
        pap (c/decl "bad-pap" [] "object"
              (c/let-ir 1 "object" {:pap {:c (raw-name "size") :ys []}} (c/ret 1)))
        bad-proof (c/decl "bad-proof" [(c/p 1 "object") (c/p 2 "object")] "uint8"
                    (c/let-ir 3 "uint8" {:fap {:c (raw-name "get") :ys [(c/v 1) (c/v 2) (c/v 2)]}}
                              (c/ret 3)))]
    (is (re-find #"Borrowed ByteArray primitive"
                 (c/failure #(j/invoke-static (:prepare *basis*) [(into rows (x/raw [pap]))]))))
    (let [ctx (assoc *basis* :program (j/invoke-static (:prepare *basis*) [(into rows (x/raw [bad-proof]))]))
          engine (j/machine ctx)
          [a] (install ctx engine [(raw-descriptor ctx 1 99 (byte-array [7 8]))]
                       [(j/graph-ref ctx 1)] true)
          before (counters engine)]
      (try
        (is (re-find #"proof requires erased" (c/failure #(j/call ctx engine "bad-proof" [a 1]))))
        (is (= before (counters engine))) (is (= 1 (c/rc ctx a)))
        (is (= [7 8] (payload ctx a)))
        (finally
          (if (:explicit ctx) (is (g/bad? #(j/close! ctx engine)))
              (do (j/release! ctx engine a) (j/close! ctx engine))))))))

(defn check! [basis] (binding [*basis* basis] (run-tests 'java-ir-byte-array-checks)))
