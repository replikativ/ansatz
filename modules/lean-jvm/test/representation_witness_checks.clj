(ns ansatz-lean-jvm-representation-witness-checks
  "Actual compiler-only observations/2 checks. No callable-entry authority."
  (:require [clojure.test :refer [deftest is run-tests]]
            [clojure.data.json :as json]
            [ansatz.lean.jvm.representation :as representation]))

(def ^:dynamic *observation* nil)
(defn- normalized [observation] (representation/normalize-observation! observation))
(defn- same [expected actual] (is (= expected actual)))
(defn- reason [f]
  (try (f) nil (catch clojure.lang.ExceptionInfo error
                 (same "InvalidRepresentation" (:code (ex-data error)))
                 (:reason (ex-data error)))))
(defn- rejected [expected observation] (same expected (reason #(normalized observation))))
(defn- builtin-index [predicate]
  (first (keep-indexed #(when (predicate (get %2 "type")) %1)
                      (get-in *observation* ["runtimeWitnesses" "closedBuiltins"]))))
(defn- nominal-row [out suffix]
  (let [id (get (first (filter #(= suffix (last (get % "name"))) (get-in out [:logical "definitions"]))) "id")]
    (first (filter #(= {"kind" "nominal" "id" id} (get % "type")) (get-in out [:normalized "plans"])))))

(deftest complete-genuine-type-closure
  (same "lean-jvm-private-nominal-observations/2" (get *observation* "schema"))
  (same 12 (count (get-in *observation* ["typeGraph" "definitions"])))
  (same 11 (count (get-in *observation* ["typeGraph" "roots"])))
  (same 7 (count (get-in *observation* ["runtimeWitnesses" "closedBuiltins"])))
  (same 14 (count (get-in *observation* ["runtimeWitnesses" "specialTypes"])))
  (let [out (normalized *observation*) rows (get-in out [:normalized "plans"])
        kinds (set (map #(get-in % ["type" "kind"]) rows))]
    (same 33 (count rows))
    (doseq [kind ["nominal" "option" "list" "product" "sum" "except" "array" "word" "unit" "float" "bytes"]] (is (kinds kind)))
    (same [0 1 2 3] (mapv #(get % "index") (get-in (nominal-row out "AST") ["encoding" "constructors"])))
    (same {"kind" "scalar" "offset" 0 "lane" "uint8"}
          (get-in (nominal-row out "AST") ["encoding" "constructors" 1 "fields" 0 "location"]))
    (same {"kind" "object" "slot" 0}
          (get-in (nominal-row out "AST") ["encoding" "constructors" 1 "fields" 1 "location"]))
    (same {"wordBits" 64 "byteOrder" "little" "storageAbi" "node-pure-data/1"} (get-in out [:normalized "target"]))))

(deftest closed-generic-storage-is-not-specialized-to-scalar-slots
  (let [out (normalized *observation*) rows (get-in out [:normalized "plans"])
        pair (first (filter #(and (= "product" (get-in % ["type" "kind"])) (= "nominal" (get-in % ["type" "first" "kind"]))) rows))
        locations (mapv #(get % "location") (get-in pair ["encoding" "constructors" 0 "fields"]))
        source-index (builtin-index #(and (= "product" (get % "kind")) (= "nominal" (get-in % ["first" "kind"]))))
        source (get-in *observation* ["runtimeWitnesses" "closedBuiltins" source-index])]
    (same [{"kind" "object" "slot" 0} {"kind" "object" "slot" 1}] locations)
    (same "uint32" (get-in source ["constructors" 0 "fields" 0 "closedIRType"]))
    (same "tobject" (get-in source ["constructors" 0 "fields" 0 "genericFieldInfo" "irType"]))
    (is (not= (get-in source ["constructors" 0 "fields" 1 "typeCheck" "actualType"])
              (get-in source ["constructors" 0 "fields" 1 "typeCheck" "expectedType"])))
    (same "box64" (get-in (first (filter #(= "word" (get-in % ["type" "kind"])) rows)) ["encoding" "boxed"]))
    (let [fields (get-in (nominal-row out "Mixed") ["encoding" "constructors" 0 "fields"])]
      (same {"kind" "usize" "nativeIndex" 5} (get-in fields [3 "location"]))
      (same {"kind" "object" "slot" 1} (get-in fields [8 "location"]))
      (same {"kind" "scalar" "offset" 28 "lane" "uint32"} (get-in fields [9 "location"])))))

(deftest embedded-witnesses-target-and-closure-are-strict
  (rejected :keys (assoc *observation* "schema" "lean-jvm-private-nominal-observations/1"))
  (rejected :keys (dissoc *observation* "runtimeWitnesses"))
  (rejected :native-target-width (assoc-in *observation* ["runtimeWitnesses" "target" "wordBits"] 32))
  (rejected :native-target-width (assoc-in *observation* ["runtimeWitnesses" "target" "wordBitsSource"] "caller-claim"))
  (rejected :special-witness-closure (update-in *observation* ["runtimeWitnesses" "specialTypes"] pop))
  (rejected :closed-builtin-closure (update-in *observation* ["runtimeWitnesses" "closedBuiltins"] pop))
  (rejected :duplicate-row (update-in *observation* ["runtimeWitnesses" "closedBuiltins"] conj
                                       (first (get-in *observation* ["runtimeWitnesses" "closedBuiltins"]))))
  (same :embedded-runtime-witnesses
        (reason #(representation/normalize-observation! *observation* {:roots [0] :runtime-witnesses {} :io? false}))))

(deftest closed-native-builtin-telescope-cannot-be-replaced-by-layout-guesses
  (let [i (builtin-index #(= "list" (get % "kind"))) prefix ["runtimeWitnesses" "closedBuiltins" i "constructors" 1 "fields"]]
    (rejected :generic-closed-field-binding (assoc-in *observation* (into prefix [0 "genericFieldIndex"]) 1))
    (rejected :generic-closed-field-binding (assoc-in *observation* (into prefix [0 "genericFieldInfo"])
                                                   {"kind" "scalar" "bytes" 4 "offset" 0 "irType" "uint32"}))
    (rejected :native-defeq (assoc-in *observation* (into prefix [0 "typeCheck" "algorithm"]) "host.inference"))
    (rejected :native-defeq (assoc-in *observation* (into prefix [0 "typeCheck" "transparency"]) "all"))
    (rejected :open-or-unsupported-native-type (assoc-in *observation* (into prefix [0 "typeCheck" "actualType"]) ["fvar" 0]))
    (rejected :field-closure (update-in *observation* prefix pop)))
  (let [i (builtin-index #(and (= "product" (get % "kind")) (= "nominal" (get-in % ["first" "kind"]))))]
    (rejected :closed-builtin-family (assoc-in *observation* ["runtimeWitnesses" "closedBuiltins" i "family"] ["str" ["anonymous"] "List"]))
    (rejected :inconsistent-closed-lowering
              (assoc-in *observation* ["runtimeWitnesses" "closedBuiltins" i "constructors" 0 "fields" 0 "closedIRType"] "uint64"))))

(deftest compiler-observation-is-not-io-or-callable-entry-proof
  (is (nil? (get-in *observation* ["runtimeWitnesses" "world"])))
  (same [] (get-in *observation* ["runtimeWitnesses" "ioFamilies"]))
  (same :missing-io-world
        (reason #(representation/normalize-observation! *observation* {:roots [0] :runtime-witnesses nil :io? true})))
  (rejected :unexpected-io-witness (assoc-in *observation* ["runtimeWitnesses" "world"] "canonical-erased-zero")))

(defn check! [actual-observation-path]
  (binding [*observation* (json/read-str (slurp actual-observation-path))]
    (run-tests 'ansatz-lean-jvm-representation-witness-checks)))
