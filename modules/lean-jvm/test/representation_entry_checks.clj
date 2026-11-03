(ns ansatz-lean-jvm-representation-entry-checks
  "Actual CLI type/layout slice checks; full callable validation is entry-v3's job."
  (:require [clojure.test :refer [deftest is run-tests]]
            [clojure.data.json :as json]
            [ansatz.lean.jvm.representation :as representation]))

(def ^:dynamic *document* nil)
(defn- same [expected actual] (is (= expected actual)))
(defn- normalize [document] (representation/normalize-entry-types! document true))
(defn- reason [f]
  (try (f) nil (catch clojure.lang.ExceptionInfo error
                 (same "InvalidRepresentation" (:code (ex-data error)))
                 (:reason (ex-data error)))))
(defn- rejected [expected document] (same expected (reason #(normalize document))))

(deftest actual-cli-catalog-and-higher-universe-builtin-normalize
  (same "lean-native-entry-evidence/3" (get *document* "schema"))
  (same 10 (count (get *document* "entries")))
  (same 10 (count (get *document* "rootTypes")))
  (let [out (normalize *document*) g (:logical out) rows (get-in out [:normalized "plans"])
        higher (first (filter #(= "Higher" (last (get % "name"))) (get g "definitions")))
        list-type {"kind" "list" "element" {"kind" "nominal" "id" (get higher "id")}}
        row (first (filter #(= list-type (get % "type")) rows))]
    (same 8 (count (get g "definitions")))
    (same 25 (count rows))
    (same "tobject" (get row "closedIR"))
    (same "family" (get-in row ["encoding" "kind"]))
    ;; This is an actual List.{1} Higher native expression, not a guessed zero universe.
    (same [["succ" ["zero"]]] (get-in *document* ["rootTypes" 6 1 2]))
    (is (not-any? #(= ["str" ["str" ["anonymous"] "IO"] "Error"] (get % "name")) (get g "definitions")))))

(deftest cli-root-ast-binding-is-direct-not-a-fabricated-defeq-row
  (rejected :entry-root-native-binding
            (assoc-in *document* ["rootTypes" 0] ["const" ["str" ["anonymous"] "Fake"] []]))
  (rejected :observation-closure (update *document* "rootTypes" pop))
  (let [fake ["const" ["str" ["anonymous"] "Fake"] []]]
    (rejected :native-logical-correspondence
              (-> *document* (assoc-in ["rootTypes" 0] fake)
                  (assoc-in ["representation" "rootTypes" 0 "nativeType"] fake))))
  (rejected :entry-schema (assoc *document* "schema" "lean-jvm-private-nominal-observations/2")))

(deftest actual-io-envelope-and-world-layout-are-required
  (same "canonical-erased-zero" (get-in *document* ["runtimeWitnesses" "world"]))
  (same ["ok" "error"] (mapv #(last (get % "constructor")) (get-in *document* ["runtimeWitnesses" "ioFamilies" 0 "constructors"])))
  (rejected :missing-io-world (assoc-in *document* ["runtimeWitnesses" "world"] nil))
  (rejected :io-family-closure (update-in *document* ["runtimeWitnesses" "ioFamilies"] pop))
  (rejected :io-envelope-layout
            (assoc-in *document* ["runtimeWitnesses" "ioFamilies" 0 "constructors" 0 "fields" 1] {"kind" "erased"}))
  (rejected :object-slot-order
            (assoc-in *document* ["runtimeWitnesses" "ioFamilies" 0 "constructors" 0 "fields" 0 "index"] 1))
  (same :unexpected-io-witness (reason #(representation/normalize-entry-types! *document* false))))

(deftest standard-io-error-witness-is-checked-but-not-admitted-as-data
  (let [fake ["str" ["str" ["str" ["anonymous"] "IO"] "Error"] "Fake"]]
    (rejected :io-error-family
              (-> *document*
                  (assoc-in ["runtimeWitnesses" "ioFamilies" 1 "constructors" 18 "constructor"] fake)
                  (assoc-in ["runtimeWitnesses" "ioFamilies" 1 "constructors" 18 "ctorInfo" "name"] fake))))
  (rejected :constructor-identity
            (assoc-in *document* ["runtimeWitnesses" "ioFamilies" 1 "constructors" 18 "ctorInfo" "cidx"] 0)))

(defn check! [actual-entry-path]
  (binding [*document* (json/read-str (slurp actual-entry-path))]
    (run-tests 'ansatz-lean-jvm-representation-entry-checks)))
