(ns ansatz-lean-jvm-boundary-checks
  "Actual Java construction/decoding checks using captured native layouts.
   These exercise mechanical ownership, not a source/artifact admission issuer."
  (:require [clojure.test :refer [deftest is run-tests]]
            [clojure.java.io :as io] [clojure.data.json :as json]
            [ansatz.lean.jvm.argument :as argument] [ansatz.lean.jvm.construction :as construction]
            [ansatz.lean.jvm.value :as value] [ansatz.lean.jvm.scalar-buffer :as scalar] [ansatz.lean.jvm.ir :as ir]
            [ansatz.lean.jvm :as lean])
  (:import [java.math BigInteger] [java.util List Optional] [ansatz.lean.jvm LeanUnit LeanChoice]))
(def ^:dynamic *root* ".")
(defn- leaf [kind] {"kind" kind})
(defn- witnesses []
  (let [documents (map #(json/read-str (slurp (io/file *root* "test/fixtures" %)))
                       ["general-entry-v2.json" "extended-entry-v2.json"])
        families (distinct (mapcat #(mapcat (fn [entry] (get-in entry ["codecWitnesses" "families"]))
                                           (get % "entries")) documents))]
    {"algorithm" "Lean.Compiler.LCNF.getCtorLayout"
     "scope" "actual-persisted-native-compiler-layout-not-host-allocation-authority" "families" (vec families)}))
(defn- roundtrip [type input]
  (let [basis (ir/linked-basis)
        program (ir/invoke-static (:prepare basis) [(List/of)])
        ctx (assoc basis :program program :explicit true :initializing false)
        engine (ir/machine ctx) layouts (witnesses)
        descriptor {"arguments" [type] "result" type "effect" "pure"}]
    (try
      (let [plan (argument/plan descriptor layouts (object-array [input]))
            roots (construction/materialize! ctx engine plan) raw (aget ^objects roots 0)]
        (try (value/decode ctx type layouts raw) (finally (ir/release! ctx engine raw))))
      (finally (ir/close! ctx engine)))))
(deftest constructed-values-use-real-managed-ownership
  (let [type {"kind" "product" "first" (leaf "bool") "second" {"kind" "list" "element" (leaf "nat")}}]
    (is (= [true [(BigInteger/valueOf 2) (BigInteger/valueOf 3)]]
           (vec (roundtrip type [true [2 3]])))))
  (is (= (Optional/of LeanUnit/INSTANCE) (roundtrip {"kind" "option" "element" (leaf "unit")} (Optional/of LeanUnit/INSTANCE))))
  (is (= [(BigInteger/valueOf 2) (BigInteger/valueOf 3)]
         (vec (roundtrip {"kind" "array" "element" (leaf "nat")} [2 3]))))
  (is (= [] (vec (roundtrip {"kind" "array" "element" (leaf "nat")} [])))))
(deftest numeric-widths-buffers-and-both-choice-branches
  (doseq [bits [8 16 32 64] signed [false true]]
    (let [type {"kind" "machine-int" "bits" bits "signed" signed}
          n (if signed (BigInteger/valueOf -1) (.subtract (.shiftLeft BigInteger/ONE bits) BigInteger/ONE))]
      (is (= n (roundtrip type n)))))
  (is (= (BigInteger/valueOf -1) (roundtrip {"kind" "word" "signed" true} -1)))
  (is (= Double/NEGATIVE_INFINITY (roundtrip {"kind" "float" "bits" 64} Double/NEGATIVE_INFINITY)))
  (is (= Integer/MIN_VALUE (Float/floatToRawIntBits (roundtrip {"kind" "float" "bits" 32} (float -0.0)))))
  (is (= 0x1f600 (roundtrip (leaf "char") 0x1f600)))
  (is (= [0 -1 42] (vec (roundtrip (leaf "bytes") (byte-array [0 -1 42])))))
  (doseq [[kind left-key right-key] [["sum" "left" "right"] ["except" "error" "value"]]]
    (let [type {"kind" kind left-key (leaf "unit") right-key (leaf "bool")}
          left (roundtrip type (LeanChoice/left LeanUnit/INSTANCE)) right (roundtrip type (LeanChoice/right false))]
      (is (.isLeft ^LeanChoice left))
      (is (identical? LeanUnit/INSTANCE (.value ^LeanChoice left)))
      (is (not (.isLeft ^LeanChoice right)))
      (is (false? (.value ^LeanChoice right))))))
(deftest clojure-conversion-is-recursive-and-bounded
  (let [type {"kind" "option" "element" (leaf "unit")}
        descriptor {"arguments" [type] "result" type "effect" "pure"}]
    (is (= [(Optional/empty)] (#'lean/host-arguments descriptor [nil])))
    (is (= [(Optional/of LeanUnit/INSTANCE)] (#'lean/host-arguments descriptor [{:some nil}])))
    (is (thrown? clojure.lang.ExceptionInfo (#'lean/host-arguments descriptor [{:some nil :extra 1}]))))
  (let [type {"kind" "sum" "left" (leaf "unit") "right" (leaf "bool")}
        converted (first (#'lean/host-arguments {"arguments" [type]} [{:left nil}]))]
    (is (.isLeft ^LeanChoice converted))
    (is (identical? LeanUnit/INSTANCE (.value ^LeanChoice converted)))))
(deftest scalar-results-use-the-engine-external-carrier-contract
  (is (= 1.5 (scalar/decode-external-scalar {"kind" "float" "bits" 64} 1.5)))
  (is (= (float -0.0) (scalar/decode-external-scalar {"kind" "float" "bits" 32} (float -0.0))))
  (is (= (BigInteger/valueOf -1)
         (scalar/decode-external-scalar {"kind" "machine-int" "bits" 64 "signed" true}
                                      (.subtract (.shiftLeft BigInteger/ONE 64) BigInteger/ONE))))
  (is (thrown? clojure.lang.ExceptionInfo
               (scalar/decode-external-scalar {"kind" "float" "bits" 32} 1.5))))
(deftest io-world-is-budgeted-before-guest-construction
  (let [type {"kind" "array" "element" (leaf "nat")}
        descriptor {"arguments" [type] "result" (leaf "unit") "effect" "pure"}
        inputs (object-array [(vec (repeat 65536 0))])]
    (is (= 65536 (count (:fields (first (:constructors (argument/plan descriptor nil inputs)))))))
    (is (thrown? clojure.lang.ExceptionInfo (argument/plan (assoc descriptor "effect" "io") nil inputs)))))
(defn check! [root] (binding [*root* root] (run-tests 'ansatz-lean-jvm-boundary-checks)))
