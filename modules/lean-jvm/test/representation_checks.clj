(ns ansatz-lean-jvm-representation-checks
  "Private genuine-observation normalization checks, not a native authority issuer.
   check! requires the actual native005 capture path; no origin/layout is invented."
  (:require [clojure.test :refer [deftest is run-tests]]
            [clojure.data.json :as json]
            [ansatz.lean.jvm.representation :as representation]))

(def ^:dynamic *observation* nil)
(defn- opts [roots] {:roots roots :runtime-witnesses nil :io? false})
(defn- normalize [x] (representation/normalize-observation! x (opts [3 4])))
(defn- refusal [f]
  (try (f) nil (catch clojure.lang.ExceptionInfo error
                 (is (#{"InvalidRepresentation" "InvalidTypeGraph"} (:code (ex-data error))))
                 (:reason (ex-data error)))))
(defn- family-index [suffix]
  (first (keep-indexed #(when (= suffix (last (get %2 "typeName"))) %1)
                      (get-in *observation* ["representation" "families"]))))

(deftest actual005-positive-nominal-only-selected-closure
  (is (= 11 (count (get-in *observation* ["typeGraph" "definitions"]))))
  (is (= 10 (count (get-in *observation* ["typeGraph" "roots"]))))
  (let [{:keys [logical normalized]} (normalize *observation*)]
    (is (= [{"kind" "nominal" "id" 0} {"kind" "nominal" "id" 1}] (get logical "roots")))
    (is (= ["Empty" "Singleton"] (mapv #(last (get % "name")) (get logical "definitions"))))
    (is (every? #(not= (apply str (repeat 64 "0")) (get-in % ["origin" "productSha256"])) (get logical "definitions")))
    (is (= "lean-jvm-typed-storage/1" (get normalized "schema"))))
  (doseq [i [3 4 5]]
    (let [out (representation/normalize-observation! *observation* (opts [i])) row (first (get-in out [:normalized "plans"]))]
      (is (= "family" (get-in row ["encoding" "kind"])))
      (is (every? #(= "immediate" (get-in % ["representation" "kind"])) (get-in row ["encoding" "constructors"]))))))

(defn- rejected [reason input] (is (= reason (refusal #(normalize input)))))

(deftest missing-witnesses-do-not-become-guessed-builtin-layouts
  (is (= :missing-closed-builtin-witness (refusal #(representation/normalize-observation! *observation*))))
  (is (= :missing-special-witness (refusal #(representation/normalize-observation! *observation* (opts [6])))))
  (is (= :missing-io-world (refusal #(representation/normalize-observation! *observation* (assoc (opts [3]) :io? true))))))

(deftest native-defeq-and-original-id-links-are-checked-even-outside-subset
  (rejected :native-defeq (assoc-in *observation* ["rootTypeChecks" 0 "algorithm"] "host.guess"))
  (rejected :native-defeq (assoc-in *observation* ["rootTypeChecks" 1 "transparency"] "all"))
  (rejected :root-native-binding (assoc-in *observation* ["rootTypeChecks" 3 "expectedType"] ["const" ["str" ["anonymous"] "Fake"] []]))
  (rejected :observation-closure (update-in *observation* ["representation" "applications"] pop))
  (rejected :duplicate-row (update-in *observation* ["representation" "closedFields"] conj (first (get-in *observation* ["representation" "closedFields"]))))
  ;; Real producer DefEq allows Unit actual PUnit to differ from canonical Unit.
  (let [field (get-in *observation* ["representation" "closedFields" 1 "constructors" 0 "fields" 8])]
    (is (not= (get-in field ["typeCheck" "actualType"]) (get-in field ["typeCheck" "expectedType"])))
    (is (map? (normalize *observation*)))))

(deftest generic-and-closed-field-and-layout-correspondence
  (rejected :generic-closed-field-binding
            (assoc-in *observation* ["representation" "closedFields" 1 "constructors" 0 "fields" 1 "genericFieldIndex"] 2))
  (rejected :generic-closed-field-binding
            (assoc-in *observation* ["representation" "closedFields" 1 "constructors" 0 "fields" 1 "genericFieldInfo"] {"kind" "object" "index" 0 "irType" "tobject"}))
  (rejected :grouped-scalar-offset
            (assoc-in *observation* ["representation" "families" (family-index "Mixed") "constructors" 0 "fields" 2 "offset"] 8))
  (rejected :constructor-closure (update-in *observation* ["representation" "closedFields" 0 "constructors"] pop))
  (rejected :inconsistent-closed-lowering
            (assoc-in *observation* ["representation" "closedFields" 1 "constructors" 0 "fields" 1 "closedIRType"] "uint64")))

(deftest strict-shape-and-bounded-failure
  (rejected :keys (assoc *observation* "admitted" true))
  (rejected :scalar-width (-> *observation*
                             (assoc-in ["representation" "families" (family-index "Mixed") "constructors" 0 "fields" 2 "bytes"] nil)
                             (assoc-in ["representation" "families" (family-index "Mixed") "constructors" 0 "fields" 2 "irType"] nil)))
  (rejected :trivial-structure (assoc-in *observation* ["representation" "families" (family-index "Empty") "trivialStructure"] false))
  (is (= :runtime-witnesses (refusal #(representation/normalize-observation! *observation* (assoc (opts [3]) :runtime-witnesses false)))))
  (is (= :selected-roots (refusal #(representation/normalize-observation! *observation* (opts [])))))
  (is (= :selected-roots (refusal #(representation/normalize-observation! *observation* (opts [3 3])))))
  (is (= :integer (refusal #(representation/normalize-observation! *observation* (opts [99])))))
  (rejected :document-vector (assoc *observation* "rootTypeChecks" (vec (repeat 32769 nil))))
  (try
    (.interrupt (Thread/currentThread))
    (let [result (try (normalize *observation*) nil (catch clojure.lang.ExceptionInfo error (:reason (ex-data error))))
          interrupted (.isInterrupted (Thread/currentThread))]
      (Thread/interrupted) (is (= :cancelled result)) (is interrupted))
    (finally (Thread/interrupted))))

(deftest numeric-metadata-is-bounded-before-json-or-virtual-methods
  ;; 4,097 bits costs only about 512 bytes; repeated refs do not allocate large
  ;; integer payloads. Decimal encoding must never see the malformed value.
  (let [huge (.shiftLeft java.math.BigInteger/ONE 4096)
        overflow (.shiftLeft java.math.BigInteger/ONE 64)
        hostile (proxy [java.math.BigInteger] ["1"]
                  (bitLength [] (throw (AssertionError. "virtual bitLength")))
                  (signum [] (throw (AssertionError. "virtual signum")))
                  (toString [] (throw (AssertionError. "decimal encoding"))))]
    (doseq [input [(assoc *observation* "rootTypeChecks" (vec (repeat 1000 huge)))
                   (assoc-in *observation* ["rootTypeChecks" 0 "root"] -1)
                   (assoc-in *observation* ["rootTypeChecks" 0 "root"] overflow)
                   (assoc-in *observation* ["rootTypeChecks" 0 "root"] hostile)]]
      (let [encoded? (atom false)]
        (with-redefs [json/write-str (fn [& _]
                                      (reset! encoded? true)
                                      (throw (AssertionError. "Malformed metadata reached JSON writer")))]
          (rejected :metadata-integer input))
        (is (false? @encoded?))))
    ;; UInt64's maximum fits the generic metadata gate; the tighter original
    ;; catalog-index check then refuses it at its actual field boundary.
    (rejected :root-native-binding
              (assoc-in *observation* ["representation" "rootTypes" 0 "root"]
                        (.subtract overflow java.math.BigInteger/ONE)))))

(defn check! [actual-observation-path]
  (binding [*observation* (json/read-str (slurp actual-observation-path))]
    (run-tests 'ansatz-lean-jvm-representation-checks)))
