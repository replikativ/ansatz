(ns typed-ir-pattern-design-example
  "One instruction fragment, not a complete IR grammar or general JVM backend.
   Requires Pattern on the classpath. Loading defines rules; verify! runs tiny checks."
  (:require [pattern.nanopass.dialect :refer [def-dialect => valid?]]
            [pattern.nanopass.pass :refer [defpass]]
            [pattern.r3.core :refer [rule]]
            [prototype.runtime-prim :as runtime]))

(def-dialect TypedScalar
  (terminals [i nat-int?])
  (Arg [a :enforce] [:var ?i])
  (Expr [e :enforce] [:intrinsic :uint64/add [?a0 ?a1]])
  (Instr [s :enforce] [:bind ?i :uint64 ?e])
  (entry Instr))

(def-dialect JvmScalar
  (terminals [i nat-int?])
  (Arg [a :enforce] [:var ?i])
  (Expr [e :enforce] [:jvm-op :ladd-wrap [?a0 ?a1]])
  (Instr [s :enforce] [:bind ?i [:repr :uint64 :long-bits] ?e])
  (entry Instr))

(defpass lower-uint64-add (=> TypedScalar JvmScalar)
  (rule '[:bind ?i :uint64 [:intrinsic :uint64/add [?a0 ?a1]]]
        [:bind i [:repr :uint64 :long-bits] [:jvm-op :ladd-wrap [a0 a1]]]))

(defn require! [ok message data]
  (when-not ok (throw (ex-info message data))))

(defn typecheck!
  "Separate use-def/logical-type check. ENV maps existing SSA IDs to logical types.
   Grammar membership alone cannot establish either property."
  [instruction env]
  (let [jvm? (valid? JvmScalar instruction)
        _ (require! (or jvm? (valid? TypedScalar instruction)) "Outside this instruction grammar" {})
        [_ destination annotation expression] instruction
        logical-type (if jvm? (second annotation) annotation)
        arguments (nth expression 2)]
    (require! (not (contains? env destination)) "SSA destination already defined" {:id destination})
    (doseq [[_ id] arguments]
      (require! (contains? env id) "Undefined SSA input" {:id id})
      (require! (= :uint64 (get env id)) "Expected logical uint64 input" {:id id :actual (get env id)}))
    (assoc env destination logical-type)))

(defn check-representations!
  "Target check, separate from logical typing. REPS maps existing SSA IDs to
   storage lanes. This fragment rejects mismatches; it inserts no conversions."
  [instruction reps]
  (require! (valid? JvmScalar instruction) "Expected JvmScalar instruction" {})
  (let [[_ destination _ expression] instruction]
    (require! (not (contains? reps destination)) "SSA representation already defined" {:id destination})
    (doseq [[_ id] (nth expression 2)]
      (require! (contains? reps id) "Missing input representation" {:id id})
      (require! (= :long-bits (get reps id)) "Expected long-bits input lane" {:id id :actual (get reps id)}))
    (assoc reps destination :long-bits)))

(defn lower! [instruction env reps]
  (require! (valid? TypedScalar instruction) "Expected TypedScalar input stage" {})
  (typecheck! instruction env)
  (let [out (lower-uint64-add instruction)]
    (require! (valid? JvmScalar out) "Pass produced invalid output grammar" {})
    (require! (= (typecheck! instruction env) (typecheck! out env)) "Pass changed logical types" {})
    (check-representations! out reps)
    out))

(def input [:bind 3 :uint64 [:intrinsic :uint64/add [[:var 0] [:var 1]]]])
(def expected [:bind 3 [:repr :uint64 :long-bits] [:jvm-op :ladd-wrap [[:var 0] [:var 1]]]])
(def environment {0 :uint64 1 :uint64})
(def representations {0 :long-bits 1 :long-bits})
(defn rejected? [f]
  (try (f) false (catch clojure.lang.ExceptionInfo _ true)))
(defn unsigned [bits] (bigint (Long/toUnsignedString (long bits))))
(defn bits [unsigned-value] (.longValue (biginteger unsigned-value)))

(defn verify!
  "No benchmark, Source, guest heap, compiler code generation or admission."
  []
  (let [out (lower! input environment representations)
        shape-rejections (mapv #(not (valid? TypedScalar %))
                           [(assoc-in input [3 2 0] [:var -1])
                            (assoc-in input [3 2 1] [:var "1"])
                            (assoc-in input [3 2] [[:var 0]])
                            (assoc-in input [3 1] :uint64/sub)])
        semantic-rejections [(rejected? #(lower! input {0 :uint64} representations))
                             (rejected? #(lower! input {0 :uint64 1 :nat} representations))
                             (rejected? #(lower! input (assoc environment 3 :uint64) representations))]
        representation-rejections [(rejected? #(lower! input environment {0 :long-bits}))
                                   (rejected? #(lower! input environment {0 :long-bits 1 :boxed-object}))]
        boundaries [0N 1N 127N 128N 9223372036854775807N 9223372036854775808N
                    18446744073709551614N 18446744073709551615N]
        stage-rejection (rejected? #(lower! expected environment representations))
        world (Object.)]
    (require! (= expected out) "Unexpected lowering" {})
    (require! (every? true? (concat shape-rejections semantic-rejections representation-rejections)) "A negative check was accepted" {})
    (require! stage-rejection "Lowering accepted the wrong input stage" {})
    (doseq [a boundaries b boundaries]
      (let [[same-world oracle] (runtime/evaluate {} world "lean_uint64_add" [a b])
            jvm-result (unsigned (unchecked-add (bits a) (bits b)))]
        (require! (identical? world same-world) "Numeric oracle changed its world" {})
        (require! (= oracle jvm-result) "UInt64 wrap semantics differ" {:a a :b b})))
    {:input input :output out :input-grammar-valid (valid? TypedScalar input)
     :output-grammar-valid (valid? JvmScalar out) :logical-result-type (get (typecheck! out environment) 3)
     :shape-rejections (count shape-rejections) :semantic-rejections (count semantic-rejections)
     :representation-rejections (count representation-rejections)
     :result-representation (get (check-representations! out representations) 3)
     :wrong-input-stage-rejected stage-rejection
     :uint64-boundary-pairs (* (count boundaries) (count boundaries))
     :negative-long-carrier-preserves-unsigned-type (= 18446744073709551615N (unsigned -1))
     :passed true}))
