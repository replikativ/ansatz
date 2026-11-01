(ns java-ir-layout-scalar-checks
  "Pinned layout/scalar fixture; final UInt16 records are metadata here."
  (:require [clojure.test :refer [deftest is run-tests]] [clojure.data.json :as json]
            [java-ir-baseline :as j] [java-ir-baseline-checks :as c]
            [java-ir-extern-checks :as x] [java-ir-generation-checks :as g]
            [java-ir-host-checks :as host] [java-ir-header-checks :as h]
            [java-ir-code-checks :as code] [lean-compatibility-corpus :as corpus]))
(def ^:dynamic *basis* nil)
(def directory "test/fixtures/java-layout-scalar-runtime/")
(def high (.shiftLeft java.math.BigInteger/ONE 63))
(def max64 (.subtract (.shiftLeft java.math.BigInteger/ONE 64) java.math.BigInteger/ONE))
(def layouts {"Lean.IR.Checker.getMaxCtorFields" 256 "Lean.IR.Checker.getMaxCtorScalarsSize" 1024
              "Lean.IR.Checker.getMaxCtorTag" 243 "Lean.IR.Checker.getUSizeSize" 8})
(defn records [] (json/read-str (slurp (str directory "original-rows.json"))))
(defn originals [] (mapv #(get % "row") (take 12 (records))))
(def helpers
  [(c/decl "layout-apply" [(c/p 1 "object") (c/p 2 "object")] "object"
     (c/let-ir 3 "object" {:ap {:x {:idx 1} :ys [(c/v 2)]}} (c/ret 3)))
   (c/decl "scalar-box64" [(c/p 1 "uint64")] "object"
     (c/let-ir 2 "object" {:box {:ty "uint64" :x {:idx 1}}} (c/ret 2)))
   (c/decl "scalar-box32" [(c/p 1 "uint32")] "object"
     (c/let-ir 2 "object" {:box {:ty "uint32" :x {:idx 1}}} (c/ret 2)))
   (c/decl "layout-payload" [(c/p 1 "object")] "object"
     (c/let-ir 2 "object" (c/ctor 7 [(c/v 1)] 0) (c/ret 2)))])
(defn context [] (assoc *basis* :program (j/invoke-static (:prepare *basis*) [(x/raw (concat (originals) helpers))])))
(defn counters [engine] (mapv #(host/private-value engine %) ["allocations" "stores" "retains" "releases" "shellDeletes"]))

(deftest authentic-fixture-and-exact-abi-fences
  (let [p (json/read-str (slurp (str directory "provenance.json")))
        method (.getMethod ^Class (:class *basis*) "validateExternAbi" (into-array Class [java.util.Map]))]
    (is (= 16 (count (records))))
    (is (= (get p "fixture-sha256") (corpus/sha256 (str directory "original-rows.json"))))
    (doseq [row (take-nth 2 (originals))]
      (is (string? (j/invoke-static method [row])))
      (is (g/bad? #(j/invoke-static method [(assoc-in row ["ir" "extern" "xs" 0 "borrow"] true)])))
      (is (g/bad? #(j/invoke-static method [(assoc-in row ["ir" "extern" "type"] "float")])))
      (is (g/bad? #(j/invoke-static method [(assoc-in row ["ir" "extern" "xs" 0 "ty"] "object")]))))
    ;; Metadata identity remains stable after a separate UInt16 lane extension.
    (doseq [row (map #(get % "row") (drop 12 (records)))]
      (is (= (get row "name") (get (first (vals (get row "ir"))) "f"))))))

(deftest raw-original-wrapper-and-ap-layout-results
  (let [ctx (context) engine (j/machine ctx)]
    (try
      (doseq [[label value] layouts]
        (is (= value (j/call ctx engine label [0])))
        (is (= value (j/call ctx engine (str label "._boxed") [0])))
        (doseq [target [label (str label "._boxed")]]
          (let [closure (j/make-closure! ctx engine target [])]
            (is (= value (j/call ctx engine "layout-apply" [closure 0])))
            (is (host/private-value closure "dead")))))
      (finally (j/close! ctx engine)))))

(deftest malformed-layout-unit-is-before-root-claim
  (let [ctx (context) engine (j/machine ctx) payload (j/call ctx engine "layout-payload" [7])]
    (try
      (doseq [label (keys layouts) unit [1 -1 "unit" nil java.math.BigInteger/ZERO payload]]
        (let [before (counters engine)]
          (is (g/bad? #(j/call ctx engine label [unit])))
          (is (= before (counters engine)))
          (is (= 1 (c/rc ctx payload))) (is (= "idle" (j/phase ctx engine)))))
      (finally (j/release! ctx engine payload) (j/close! ctx engine)))))

(deftest malformed-layout-ap-preserves-closure-before-retirement
  (doseq [label (keys layouts)]
    (let [ctx (context) engine (j/machine ctx) closure (j/make-closure! ctx engine label [])
          before (counters engine)]
      (is (g/bad? #(j/call ctx engine "layout-apply" [closure 1])))
      (is (= before (counters engine))) (is (= 1 (c/rc ctx closure)))
      (is (false? (host/private-value closure "dead")))
      (j/release! ctx engine closure)
      (if (:explicit ctx) (is (g/bad? #(j/close! ctx engine))) (j/close! ctx engine)))))

(deftest u32-less-than-uses-zero-extended-sign-boundaries
  (let [ctx (context) engine (j/machine ctx)]
    (try
      (doseq [a [0 2147483647 2147483648 4294967295] b [0 2147483647 2147483648 4294967295]]
        (let [expected (if (< a b) 1 0)
              boxed-a (j/call ctx engine "scalar-box32" [a]) boxed-b (j/call ctx engine "scalar-box32" [b])]
          (is (= expected (j/call ctx engine "UInt32.decLt" [a b])))
          (is (= expected (j/call ctx engine "UInt32.decLt._boxed" [boxed-a boxed-b])))))
      (doseq [bad [-1 4294967296 1.5]]
        (is (g/bad? #(j/call ctx engine "UInt32.decLt" [bad 0]))))
      (finally (j/close! ctx engine)))))

(deftest u64-nat-canonical-results-and-owned-boxed-ap
  (let [ctx (context) engine (j/machine ctx)]
    (try
      (doseq [value [0 Long/MAX_VALUE high max64]]
        (let [actual (j/call ctx engine "UInt64.toNat" [value])
              boxed (j/call ctx engine "scalar-box64" [value])
              closure (j/make-closure! ctx engine "UInt64.toNat._boxed" [])]
          (is (= value actual))
          (is (= (if (<= value Long/MAX_VALUE) Long java.math.BigInteger) (class actual)))
          (is (= value (j/call ctx engine "layout-apply" [closure boxed])))
          (is (= 0 (c/rc ctx boxed))) (is (host/private-value closure "dead"))))
      (doseq [bad [-1 (.add max64 java.math.BigInteger/ONE) 1.5]]
        (is (g/bad? #(j/call ctx engine "UInt64.toNat" [bad]))))
      (finally (j/close! ctx engine)))))

(deftest code-saved-high-word-fork-and-original-conversion
  (if-not (:explicit *basis*) (is true)
    (let [raw (nth (originals) 10)
          model (c/decl "demand-to-nat" [(c/p 1 "uint64")] "object"
                  (c/let-ir 2 "object" {:fap {:c (get raw "name") :ys [(c/v 1)]}} (c/ret 2)))
          base (j/prepare-host-program *basis* [] []) source (j/source-binding base (Object.))
          native (h/header source raw) target (h/header source model)
          ctx (j/register-headers base [native target]) ready (code/materialize ctx target model [native])
          parent (j/machine ctx)]
      (try
        (j/start! ctx parent "demand-to-nat" [max64])
        (let [request (code/request! ctx parent) child (:engine (j/fork! ctx parent []))]
          (try
            (is (= [max64] (code/args request)))
            (j/resume-code! ready parent request)
            (j/resume-code! ready child (j/code-request ctx child))
            (is (= max64 (code/finish! ready parent) (code/finish! ready child)))
            (finally (j/close! ready child))))
        (finally (j/close! ready parent))))))

(deftest host-high-word-reply-preclaim-fork-and-original-conversion
  (if-not (:explicit *basis*) (is true)
    (let [spec (host/spec "research_layout_word" ["uint64"] [false] "uint64")
          model (c/decl "host-to-nat" [(c/p 1 "uint64")] "object"
                  (c/let-ir 2 "uint64" (c/fap "word-host" [(c/v 1)])
                    (c/let-ir 3 "object" {:fap {:c (get (nth (originals) 10) "name") :ys [(c/v 2)]}} (c/ret 3))))
          ctx (j/prepare-host-program *basis* (x/raw (concat (originals) [(host/ext "word-host" spec) model])) [spec])
          parent (j/machine ctx)]
      (try
        (j/start! ctx parent "host-to-nat" [max64])
        (let [request (host/request! ctx parent) child (:engine (j/fork! ctx parent []))]
          (try
            (is (= [max64] (host/args request)))
            (is (g/bad? #(j/resume-host! ctx parent request -1)))
            (is (identical? request (j/host-request ctx parent)))
            (j/resume-host! ctx parent request high)
            (j/resume-host! ctx child (j/host-request ctx child) max64)
            (is (= high (host/finish! ctx parent))) (is (= max64 (host/finish! ctx child)))
            (finally (j/close! ctx child))))
        (finally (j/close! ctx parent))))))
(defn check! [basis] (binding [*basis* basis] (run-tests 'java-ir-layout-scalar-checks)))
