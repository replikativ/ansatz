(ns java-ir-f64-checks
  "Distinct raw binary64 transport and matching-native original Float family."
  (:require [clojure.test :refer [deftest is run-tests]]
            [clojure.data.json :as json]
            [java-ir-baseline :as j] [java-ir-baseline-checks :as c]
            [java-ir-extern-checks :as x] [java-ir-generation-checks :as g]
            [java-ir-host-checks :as host] [java-ir-header-checks :as h]
            [java-ir-code-checks :as code] [lean-compatibility-corpus :as corpus]))
(def ^:dynamic *basis* nil)
(def fixture "test/fixtures/java-f64-runtime/original-rows.json")
(def originals (mapv #(get % "row") (json/read-str (slurp fixture))))
(def vectors (json/read-str (slurp "test/fixtures/java-f64-runtime/native-vectors.json")))
(defn uint [s] (biginteger s))
(defn double-word [n] (Double/longBitsToDouble (.longValue (biginteger n))))
(defn word [x] (let [n (Double/doubleToRawLongBits (double x))] (if (neg? n) (.setBit (biginteger (bit-and n Long/MAX_VALUE)) 63) (biginteger n))))
(defn canonical-word [x] (if (Double/isNaN (double x)) (uint "9221120237041090560") (word x)))
(defn box-expr [ty n] {:box {:ty ty :x {:idx n}}})
(defn unbox-expr [n] {:unbox {:x {:idx n}}})
(defn helpers []
  [(c/decl "float-id" [(c/p 1 "float")] "float" (c/ret 1))
   (c/decl "float-join" [(c/p 1 "float")] "float" ["jdecl" {:idx 2} [(c/p 3 "float")] (c/ret 3) ["jmp" {:idx 2} [(c/v 1)]]])
   (c/decl "float-box" [(c/p 1 "float")] "object" (c/let-ir 2 "object" (box-expr "float" 1) (c/ret 2)))
   (c/decl "float-unbox" [(c/p 1 "object")] "float" (c/let-ir 2 "float" (unbox-expr 1) ["dec" {:idx 1} 1 true false (c/ret 2)]))
   (c/decl "word-box" [(c/p 1 "uint64")] "object" (c/let-ir 2 "object" (box-expr "uint64" 1) (c/ret 2)))
   (c/decl "word-unbox" [(c/p 1 "object")] "uint64" (c/let-ir 2 "uint64" (unbox-expr 1) ["dec" {:idx 1} 1 true false (c/ret 2)]))
   (c/decl "float-scalar-result" [(c/p 1 "object")] "float" (c/let-ir 2 "float" (c/lit 1) (c/ret 2)))
   (c/decl "float-cache" [] "float" (c/let-ir 1 "float" (c/lit 1) (c/ret 1)))
   (c/decl "float-tail" [(c/p 1 "float") (c/p 2 "uint8")] "float"
     ["case" (c/name-ir "Bool") {:idx 2} "uint8"
      [["ctor" {:cidx 0} (c/ret 1)]
       ["default" (c/let-ir 3 "uint8" (c/lit 0)
                    (c/let-ir 4 "float" (c/fap "float-tail" [(c/v 1) (c/v 3)]) (c/ret 4)))]]])
   (second g/common)
   (c/decl "float-pack" [(c/p 1 "float") (c/p 2 "float")] "object"
     (c/let-ir 3 "object" (c/ctor 7 ["erased" "erased" "erased"] 17)
       ["sset" {:idx 3} 3 0 {:idx 1} "float" ["sset" {:idx 3} 3 8 {:idx 2} "float" (c/ret 3)]]))
   (c/decl "float-read" [(c/p 1 "object")] "float" (c/let-ir 2 "float" {:sproj {:x {:idx 1} :n 3 :offset 8}}
                                                                  ["dec" {:idx 1} 1 true false (c/ret 2)]))])
(defn context
  ([] (context []))
  ([extra] (assoc *basis* :program (j/invoke-static (:prepare *basis*) [(x/raw (concat originals (helpers) extra))]))))
(defn box [ctx engine x] (j/call ctx engine "float-box" [x]))
(defn unbox [ctx engine x] (j/call ctx engine "float-unbox" [x]))
(defn through [target]
  (c/decl "raw-through" [(c/p 1 "uint64")] "uint64"
    (c/let-ir 2 "object" (box-expr "uint64" 1)
      (c/let-ir 3 "float" (unbox-expr 2)
        ["dec" {:idx 2} 1 true false
         (c/let-ir 4 "float" (c/fap target [(c/v 3)])
           (c/let-ir 5 "object" (box-expr "float" 4)
             (c/let-ir 6 "uint64" (unbox-expr 5) ["dec" {:idx 5} 1 true false (c/ret 6)])))]))))

(deftest original-abis-fixture-and-native-receipt
  (let [p (json/read-str (slurp "test/fixtures/java-f64-runtime/provenance.json"))
        receipt (json/read-str (slurp "test/fixtures/java-f64-runtime/native-receipt.json"))]
    (is (= 18 (count originals))) (is (= (get p "fixture-sha256") (corpus/sha256 fixture)))
    (is (= 278 (count vectors) (get receipt "rows")))
    (is (true? (get-in receipt ["same-process-profile" "FE_TONEAREST"])))
    (is (= "C" (get-in receipt ["same-process-profile" "LC_NUMERIC"])))
    (is (= "7ff8000000000000" (get-in receipt ["same-process-profile" "native-ofBits-quietNaN-word"])))
    (is (= (get receipt "vectors-sha256") (corpus/sha256 "test/fixtures/java-f64-runtime/native-vectors.json")))
    (doseq [row (take-nth 2 originals)]
      (is (every? false? (map #(get % "borrow") (get-in row ["ir" "extern" "xs"]))))
      (is (string? (j/invoke-static (.getMethod ^Class (:class *basis*) "validateExternAbi" (into-array Class [java.util.Map])) [row]))))))

(deftest all-native-runtime-vectors-and-formatting
  (let [literal-rows (map-indexed (fn [i r] (c/decl (str "literal" i) [] "float" (c/let-ir 1 "float" (c/lit (uint (get r "a"))) (c/ret 1))))
                                 (filter #(= "nat" (get % "op")) vectors))
        ctx (context literal-rows) engine (j/machine ctx) literal-index (atom -1)]
    (try
      (doseq [r vectors :let [op (get r "op") a (uint (get r "a")) b (uint (get r "b"))
                             x (double-word a) y (double-word b)
                             label ({"bits" "Float.ofBits" "u64" "UInt64.toFloat" "sub" "Float.sub" "mul" "Float.mul" "div" "Float.div" "eq" "Float.beq" "lt" "Float.decLt"} op)
                             answer (if (= op "nat") (j/call ctx engine (str "literal" (swap! literal-index inc)) [])
                                      (j/call ctx engine label (if (#{"bits" "u64"} op) [a] [x y])))]]
        (if (#{"eq" "lt"} op)
          (is (= (get r "comparison") answer) (str op " " a " " b))
          (do (is (= (uint (get r "bits")) (if (= op "bits") (word answer) (canonical-word answer))) (str op " " a " " b))
              (is (= (get r "text") (j/call ctx engine "Float.toString" [answer])) (str "format " op " " a)))))
      (finally (j/close! ctx engine)))))

(deftest genuine-boxed-wrappers-and-ofmodel-identity
  (let [ctx (context) engine (j/machine ctx)]
    (try
      (doseq [n [0 1 (uint "9223372036854775808") (uint "18446744073709551615")]]
        (doseq [label ["Float.ofBits" "Float.ofModel" "UInt64.toFloat"]]
          (let [raw (j/call ctx engine label [n]) input (j/call ctx engine "word-box" [n])
                answer (unbox ctx engine (j/call ctx engine (str label "._boxed") [input]))]
            (is (= (canonical-word raw) (canonical-word answer))) (is (= 0 (c/rc ctx input))))))
      (doseq [label ["Float.sub" "Float.mul" "Float.div" "Float.beq" "Float.decLt"]]
        (let [answer (j/call ctx engine (str label "._boxed") [(box ctx engine 1.5) (box ctx engine -0.0)])
              expected (j/call ctx engine label [1.5 -0.0])]
          (if (#{"Float.beq" "Float.decLt"} label) (is (= expected answer))
            (is (= (canonical-word expected) (canonical-word (unbox ctx engine answer)))))))
      (is (= "-0.000000" (j/call ctx engine "Float.toString._boxed" [(box ctx engine -0.0)])))
      (finally (j/close! ctx engine)))))

(deftest raw-bits-joins-self-tail-cache-and-scalar-ap
  (let [ctx (context [(through "float-id")]) engine (j/machine ctx)]
    (try
      (doseq [n [0 (uint "9223372036854775808") (uint "9221120237041090626") (uint "9218868437227405313")]]
        (is (= n (j/call ctx engine "raw-through" [n]))))
      (doseq [x [0.0 -0.0 Double/POSITIVE_INFINITY (double-word "9221120237041090626")]]
        (is (= (word x) (word (j/call ctx engine "float-join" [x]))))
        (is (= (word x) (word (j/call ctx engine "float-tail" [x 1])))))
      (is (= 1.0 (j/call ctx engine "float-cache" []) (j/call ctx engine "float-cache" [])))
      (is (instance? Long (aget ^objects (host/private-value engine "constants") (int (j/function-id ctx "float-cache")))))
      (let [closure (j/make-closure! ctx engine "float-scalar-result" [])]
        (is (= 1.0 (unbox ctx engine (j/call ctx engine "apply" [closure 0])))))
      (finally (j/close! ctx engine)))))

(deftest packed-float-fields-and-fork-use-exact-bytes
  (let [ctx (context) engine (j/machine ctx) value (j/call ctx engine "float-pack" [-0.0 0.1])
        child-result (j/fork! ctx engine [value]) child (:engine child-result) copied (first (:roots child-result))]
    (try
      (is (= (vec (.get ^java.lang.reflect.Field (:scalars ctx) value)) (vec (.get ^java.lang.reflect.Field (:scalars ctx) copied))))
      (is (= 0.1 (j/call ctx engine "float-read" [value]) (j/call ctx child "float-read" [copied])))
      (finally (j/close! ctx engine) (j/close! ctx child)))))

(deftest float-lane-domain-and-preparation-rejections
  (let [ctx (context) engine (j/machine ctx)]
    (try
      (doseq [x [0 1 (biginteger 1) (float 1) "0" nil]] (is (g/bad? #(j/call ctx engine "float-id" [x]))))
      (is (= 1.0 (j/call ctx engine "float-id" [1.0])))
      (is (g/bad? #(j/make-closure! ctx engine "float-id" [])))
      (is (g/bad? #(j/call ctx engine "word-box" [1.0])))
      (is (g/bad? #(j/call ctx engine "float-scalar-result" [1.0])))
      (doseq [ty ["float32"]]
        (is (g/bad? #(context [(c/decl "unsupported" [(c/p 1 ty)] ty (c/ret 1))]))))
      (is (g/bad? #(context [(c/decl "float-case" [(c/p 1 "float")] "float" ["case" (c/name-ir "Float") {:idx 1} "float" [["default" (c/ret 1)]]])])))
      (is (g/bad? #(context [(c/decl "mismatch" [(c/p 1 "uint64")] "float" (c/let-ir 2 "float" (c/fap "float-id" [(c/v 1)]) (c/ret 2)))])))
      (finally (j/close! ctx engine)))))

(deftest code-pause-inspection-and-fork-preserve-signaling-word
  (when (:explicit *basis*)
    (let [callee (first (helpers)) caller (through "float-id")
          base (j/prepare-host-program *basis* [] []) binding (j/source-binding base (Object.))
          ch (h/header binding callee) rh (h/header binding caller) ctx (j/register-headers base [ch rh])
          linked (code/materialize ctx rh caller [ch]) ready (code/materialize linked ch callee [])
          engine (j/machine linked) n (uint "9218868437227405313")]
      (try
        (j/start! linked engine "raw-through" [n])
        (let [request (code/request! linked engine) activation (host/private-value request "activation")
              saved (aget ^objects (host/private-value activation "arguments") 0)
              child (:engine (j/fork! linked engine []))]
          (try
            (is (= (.longValue n) (host/private-value saved "bits")))
            (is (instance? Double (first (vec (j/request-value request "arguments")))))
            (is (identical? saved (aget ^objects (host/private-value activation "arguments") 0)))
            (let [objects (context) other (j/machine objects)]
              (try
                (is (g/bad? #(j/call objects other "float-id" [saved])))
                (is (g/bad? #(j/call objects other "float-scalar-result" [saved])))
                (is (g/bad? #(j/graph-node objects {:kind :array :id 1 :fields [saved]})))
                (finally (j/close! objects other))))
            (j/resume-code! ready engine request) (j/resume-code! ready child (j/code-request ready child))
            (is (= n (code/finish! ready engine) (code/finish! ready child)))
            (finally (j/close! ready child))))
        (finally (j/close! ready engine))))))

(deftest host-typed-float-views-invalid-replies-and-fork
  (when (:explicit *basis*)
    (let [spec (host/spec "research_float" ["float"] [false] "float")
          ctx (j/prepare-host-program *basis* (x/raw [(host/ext "host-float" spec) (through "host-float")]) [spec])
          engine (j/machine ctx) n (uint "9218868437227405313")]
      (try
        (j/start! ctx engine "raw-through" [n])
        (let [request (host/request! ctx engine) call (host/private-value request "call")
              saved (aget ^objects (host/private-value call "arguments") 0)
              child (:engine (j/fork! ctx engine []))]
          (try
            (is (= (.longValue n) (host/private-value saved "bits")))
            (is (Double/isNaN (double (first (host/args request)))))
            (is (= (.longValue n) (host/private-value saved "bits")))
            (doseq [invalid [0 (biginteger 1) (float 1) "bad" nil]]
              (is (g/bad? #(j/resume-host! ctx engine request invalid)))
              (is (identical? request (j/host-request ctx engine))))
            (j/resume-host! ctx engine request -0.0)
            (j/resume-host! ctx child (j/host-request ctx child) 0.1)
            (is (= (word -0.0) (host/finish! ctx engine))) (is (= (word 0.1) (host/finish! ctx child)))
            (finally (j/close! ctx child))))
        (finally (j/close! ctx engine))))))

(deftest unaligned-payload-and-original-boxed-closure-application
  (let [pack (c/decl "float-unaligned" [(c/p 1 "float")] "float"
               (c/let-ir 2 "object" (c/ctor 0 [] 9)
                 ["sset" {:idx 2} 0 1 {:idx 1} "float"
                  (c/let-ir 3 "float" {:sproj {:x {:idx 2} :n 0 :offset 1}}
                    ["dec" {:idx 2} 1 true false (c/ret 3)])]))
        ctx (context [pack]) engine (j/machine ctx)]
    (try
      (is (= (word -0.0) (word (j/call ctx engine "float-unaligned" [-0.0]))))
      (let [capture (box ctx engine 1.5) closure (j/make-closure! ctx engine "Float.sub._boxed" [capture])]
        (is (= 1.5 (unbox ctx engine (j/call ctx engine "apply" [closure (box ctx engine -0.0)]))))
        (is (= 0 (c/rc ctx capture))))
      (finally (j/close! ctx engine)))))

(deftest forked-double-view-confers-no-object-admission
  (let [ctx (context) parent (j/machine ctx) fork (j/fork! ctx parent [-0.0])
        child (:engine fork) view (first (:roots fork))]
    (try
      (is (instance? Double view)) (is (= (word -0.0) (word view)))
      (is (g/bad? #(j/call ctx child "float-scalar-result" [view])))
      (is (g/bad? #(j/graph-node ctx {:kind :array :id 1 :fields [view]})))
      (is (= (word view) (word (j/call ctx child "float-id" [view]))))
      (finally (j/close! ctx parent) (j/close! ctx child)))))

(deftest host-overapplication-retains-float-box-after-claim-failure
  (when (:explicit *basis*)
    (let [spec (host/spec "research_float_result" ["object"] [false] "float")
          apply-row (c/decl "apply-many" [(c/p 1 "object") (c/p 2 "object") (c/p 3 "object")] "object"
                      (c/let-ir 4 "object" {:ap {:x {:idx 1} :ys [(c/v 2) (c/v 3)]}} (c/ret 4)))
          ctx (j/prepare-host-program *basis* (x/raw [(host/ext "float-host" spec) apply-row]) [spec])
          engine (j/machine ctx) closure (j/make-closure! ctx engine "float-host" [])]
      (j/start! ctx engine "apply-many" [closure 0 0])
      (let [request (host/request! ctx engine)]
        (is (g/bad? #(j/resume-host! ctx engine request -0.0)))
        (is (= "failed" (j/phase ctx engine)))
        (let [completion (host/private-value engine "hostCompletion")
              value (host/private-value completion "completionResult")]
          (is (= Long/MIN_VALUE (host/private-value completion "completionScalar")))
          (is (true? (host/private-value completion "resultOwned")))
          (is (false? (host/private-value completion "resultTransferStarted")))
          (is (= 1 (c/rc ctx value)))
          (let [bytes ^bytes (.get ^java.lang.reflect.Field (:scalars ctx) value)]
            (is (= [0 0 0 0 0 0 0 -128] (vec bytes))))
          (j/release! ctx engine value) (is (= 0 (c/rc ctx value))))
        (is (g/bad? #(j/close! ctx engine)))))))

(defn check! [basis] (binding [*basis* basis] (run-tests 'java-ir-f64-checks)))
