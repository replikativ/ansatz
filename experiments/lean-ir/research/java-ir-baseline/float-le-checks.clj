(ns java-ir-float-le-checks
  "Original Float.decLe, IEEE ordered comparison and exact binary64 lane guards."
  (:require [clojure.test :refer [deftest is run-tests]] [clojure.data.json :as json]
            [java-ir-baseline :as j] [java-ir-baseline-checks :as c]
            [java-ir-extern-checks :as x] [java-ir-generation-checks :as g]
            [java-ir-host-checks :as host] [java-ir-f64-checks :as f64]
            [lean-compatibility-corpus :as corpus]))
(def ^:dynamic *basis* nil)
(def directory "test/fixtures/java-float-le-runtime/")
(defn records []
  (mapv (fn [r] (assoc r "row" (json/read-str (slurp (str directory (get r "file"))))))
        (get (json/read-str (slurp (str directory "provenance.json"))) "rows")))
(defn originals [] (mapv #(get % "row") (records)))
(defn raw-name [] (get (first (originals)) "name"))
(defn fap [args] {:fap {:c (raw-name) :ys args}})
(defn literal-row [label a b]
  (c/decl label [] "uint8"
    (c/let-ir 1 "float" (c/lit a) (c/let-ir 2 "float" (c/lit b)
      (c/let-ir 3 "uint8" (fap [(c/v 1) (c/v 2)]) (c/ret 3))))))
(defn helpers []
  [(c/decl "float-le-fap" [(c/p 1 "float") (c/p 2 "float")] "uint8"
     (c/let-ir 3 "uint8" (fap [(c/v 1) (c/v 2)]) (c/ret 3)))
   (c/decl "float-le-pap" [(c/p 1 "object")] "object"
     (c/let-ir 2 "object" {:pap {:c (get (second (originals)) "name") :ys [(c/v 1)]}} (c/ret 2)))
   (c/decl "float-le-ap" [(c/p 1 "object") (c/p 2 "object")] "object"
     (c/let-ir 3 "object" {:ap {:x {:idx 1} :ys [(c/v 2)]}} (c/ret 3)))
   ;; UInt64 box -> Float unbox preserves signaling payloads on the IR scalar
   ;; stack, using the established raw-word fixture transport (not Float.ofBits,
   ;; whose native implementation canonicalizes NaNs).
   (c/decl "float-le-words" [(c/p 1 "uint64") (c/p 2 "uint64")] "uint8"
     (c/let-ir 3 "object" (f64/box-expr "uint64" 1)
       (c/let-ir 4 "float" (f64/unbox-expr 3) ["dec" {:idx 3} 1 true false
         (c/let-ir 5 "object" (f64/box-expr "uint64" 2)
           (c/let-ir 6 "float" (f64/unbox-expr 5) ["dec" {:idx 5} 1 true false
             (c/let-ir 7 "uint8" (fap [(c/v 4) (c/v 6)]) (c/ret 7))]))])))
   (literal-row "float-le-literal" 1 2)
   (literal-row "float-le-literal-nat" (biginteger "9218868437227405313") (biginteger "9221120237041090561"))])
(defn context
  ([] (context []))
  ([extra] (binding [f64/*basis* *basis*]
             (f64/context (concat (originals) (helpers) extra)))))
(def words (mapv biginteger ["0" "9223372036854775808" "4607182418800017408" "13830554455654793216"
                             "9218868437227405312" "18442240474082181120" "9221120237041090561"
                             "9218868437227405313" "18444492273895866369"]))
(defn nan-word? [^java.math.BigInteger n]
  (and (= (.and n (biginteger "9218868437227405312")) (biginteger "9218868437227405312"))
       (pos? (.signum (.and n (biginteger "4503599627370495"))))))
(defn ordered-le [^java.math.BigInteger a ^java.math.BigInteger b]
  ;; Independent integer encoding oracle: monotone positive words, reversed
  ;; negative words, equal signed zeros and unordered NaNs. No Java Float <=.
  (let [sa (.testBit a 63) sb (.testBit b 63)
        magnitude (biginteger "9223372036854775807")]
    (if (or (nan-word? a) (nan-word? b)) 0
      (if (and (zero? (.signum (.and a magnitude))) (zero? (.signum (.and b magnitude)))) 1
        (if (not= sa sb) (if sa 1 0) (if (if sa (>= a b) (<= a b)) 1 0))))))
(defn counters [e] (mapv #(host/private-value e %) ["allocations" "stores" "retains" "releases" "shellDeletes"]))

(deftest exact-original-source-row-digests-and-captured-abis
  (let [raw (first (originals))
        method (.getMethod ^Class (:class *basis*) "validateExternAbi" (into-array Class [java.util.Map]))]
    (doseq [r (records)] (is (= (get r "sha256") (corpus/sha256 (str directory (get r "file"))))))
    (is (= "lean_float_decLe" (j/invoke-static method [raw])))
    (doseq [i [0 1]]
      (is (g/bad? #(j/invoke-static method [(assoc-in raw ["ir" "extern" "xs" i "borrow"] true)])))
      (is (g/bad? #(j/invoke-static method [(assoc-in raw ["ir" "extern" "xs" i "ty"] "uint64")]))))
    (is (g/bad? #(j/invoke-static method [(assoc-in raw ["ir" "extern" "type"] "object")])))))

(deftest signed-zero-nan-payloads-infinities-and-ordered-finite-values
  (let [ctx (context) e (j/machine ctx)]
    (try
      (doseq [a words b words :let [expected (ordered-le a b) x (f64/double-word a) y (f64/double-word b)]]
        (is (= expected (j/call ctx e "Float.decLe" [x y])) (str "raw " a " " b))
        (is (= expected (j/call ctx e "float-le-fap" [x y])) (str "FAP " a " " b))
        (is (= expected (j/call ctx e "float-le-words" [a b])) (str "raw bits " a " " b))
        (is (= expected (j/call ctx e "Float.decLe._boxed" [(f64/box ctx e x) (f64/box ctx e y)])))
        (let [closure (j/call ctx e "float-le-pap" [(f64/box ctx e x)])]
          (is (= expected (j/call ctx e "float-le-ap" [closure (f64/box ctx e y)])))))
      (finally (j/close! ctx e)))))

(deftest boxed-comparison-consumes-only-transferred-owner-credits
  (let [ctx (context) e (j/machine ctx)
        a (j/call ctx e "word-box" [(biginteger "9218868437227405313")])
        b (j/call ctx e "word-box" [(biginteger "9223372036854775808")])
        a-bytes (vec (.get ^java.lang.reflect.Field (:scalars ctx) a))
        b-bytes (vec (.get ^java.lang.reflect.Field (:scalars ctx) b))]
    (try
      (j/retain! ctx e a) (j/retain! ctx e b)
      (is (= 0 (j/call ctx e "Float.decLe._boxed" [a b])))
      (is (= [1 1] [(c/rc ctx a) (c/rc ctx b)]))
      (is (= a-bytes (vec (.get ^java.lang.reflect.Field (:scalars ctx) a))))
      (is (= b-bytes (vec (.get ^java.lang.reflect.Field (:scalars ctx) b))))
      (is (= (biginteger "9218868437227405313") (j/call ctx e "word-unbox" [a])))
      (is (= (biginteger "9223372036854775808") (j/call ctx e "word-unbox" [b])))
      (finally (j/close! ctx e)))))

(deftest literal-float-is-numeric-conversion-and-not-raw-bit-reinterpretation
  (let [ctx (context) e (j/machine ctx)]
    (try
      (is (= 1 (j/call ctx e "float-le-literal" [])))
      (is (= 1 (j/call ctx e "float-le-literal-nat" [])))
      (is (= 0 (j/call ctx e "float-le-words"
                 [(biginteger "9218868437227405313") (biginteger "9221120237041090561")])))
      (finally (j/close! ctx e)))))

(deftest binary64-host-and-ir-lane-guards-remain-distinct-from-uint64-and-float32
  (let [ctx (context) e (j/machine ctx)]
    (try
      (let [before (counters e)]
        (doseq [invalid [0 1 (biginteger 0) (float 0) "0" nil]]
          (is (g/bad? #(j/call ctx e "Float.decLe" [invalid 0.0])))
          (is (g/bad? #(j/call ctx e "Float.decLe" [0.0 invalid]))))
        (is (g/bad? #(j/make-closure! ctx e "Float.decLe" [])))
        (is (= before (counters e))))
      (is (= 1 (j/call ctx e "Float.decLe" [1.0 2.0])))
      (is (g/bad? #(context [(literal-row "float-le-negative-literal" -1 2)])))
      (is (g/bad? #(context [(c/decl "float-le-u64-mismatch" [(c/p 1 "uint64") (c/p 2 "float")] "uint8"
                               (c/let-ir 3 "uint8" (fap [(c/v 1) (c/v 2)]) (c/ret 3)))])))
      (is (g/bad? #(context [(c/decl "float-le-f32-mismatch" [(c/p 1 "float32") (c/p 2 "float")] "uint8"
                             (c/let-ir 3 "uint8" (fap [(c/v 1) (c/v 2)]) (c/ret 3)))])))
      (finally (j/close! ctx e)))))

(defn check! [basis] (binding [*basis* basis] (run-tests 'java-ir-float-le-checks)))
