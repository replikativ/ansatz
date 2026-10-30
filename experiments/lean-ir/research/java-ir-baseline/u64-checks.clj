(ns java-ir-u64-checks
  "Distinct UInt64 transport, original hash primitives and Name cache packing."
  (:require [clojure.test :refer [deftest is run-tests]]
            [clojure.data.json :as json] [clojure.edn :as edn]
            [java-ir-baseline :as j] [java-ir-baseline-checks :as c]
            [java-ir-extern-checks :as x] [java-ir-generation-checks :as g]
            [java-ir-host-checks :as host] [java-ir-header-checks :as header]
            [java-ir-code-checks :as code] [lean-compatibility-corpus :as corpus]))
(def ^:dynamic *basis* nil)
(def fixture "test/fixtures/java-u64-runtime/original-rows.json")
(def max64 (.subtract (.shiftLeft java.math.BigInteger/ONE 64) java.math.BigInteger/ONE))
(def high (.shiftLeft java.math.BigInteger/ONE 63))
(def wide (.add max64 (biginteger 8)))
(def supported-symbols #{"lean_string_hash" "lean_uint64_mix_hash" "lean_uint64_of_nat"
                         "lean_uint64_shift_right" "lean_uint64_xor" "lean_uint64_to_usize"
                         "lean_uint64_dec_lt" "lean_uint64_dec_eq" "lean_uint64_of_nat_mk"})
(defn originals [] (json/read-str (slurp fixture)))
(defn selected-rows []
  (let [rows (mapv #(get % "row") (originals))
        names (set (for [r rows :when (contains? supported-symbols
                                       (get-in r ["ir" "extern" "ext" "entries" 0 "standard" "fn"]))]
                     (get r "name")))]
    (filterv (fn [r] (let [n (get r "name")]
                      (or (contains? names n) (and (= "_boxed" (last n)) (contains? names (second n)))))) rows)))
(defn helpers []
  [(c/decl "u64-id" [(c/p 1 "uint64")] "uint64" (c/ret 1))
   (c/decl "u64-const" [] "uint64" (c/let-ir 1 "uint64" (c/lit max64) (c/ret 1)))
   (c/decl "u64-wide-literal" [] "uint64" (c/let-ir 1 "uint64" (c/lit wide) (c/ret 1)))
   (c/decl "u64-box" [(c/p 1 "uint64")] "object"
     (c/let-ir 2 "object" {:box {:ty "uint64" :x {:idx 1}}} (c/ret 2)))
   (c/decl "u64-unbox" [(c/p 1 "object")] "uint64"
     (c/let-ir 2 "uint64" {:unbox {:x {:idx 1}}} ["dec" {:idx 1} 1 true false (c/ret 2)]))
   (c/decl "usize-unbox" [(c/p 1 "object")] "usize"
     (c/let-ir 2 "usize" {:unbox {:x {:idx 1}}} ["dec" {:idx 1} 1 true false (c/ret 2)]))
   (c/decl "u64-join" [(c/p 1 "uint64")] "uint64"
     ["jdecl" {:idx 2} [(c/p 3 "uint64")] (c/ret 3) ["jmp" {:idx 2} [(c/v 1)]]])
   (c/decl "u64-result" [(c/p 1 "object")] "uint64"
     (c/let-ir 2 "uint64" (c/lit max64) (c/ret 2)))
   (second g/common)
   (c/decl "u64-pack" [(c/p 1 "object") (c/p 2 "uint8") (c/p 3 "uint32") (c/p 4 "uint64")] "object"
     (c/let-ir 5 "object" (c/ctor 3 [(c/v 1)] 16)
       ["sset" {:idx 5} 1 0 {:idx 2} "uint8"
        ["sset" {:idx 5} 1 4 {:idx 3} "uint32"
         ["sset" {:idx 5} 2 0 {:idx 4} "uint64" (c/ret 5)]]]))
   (c/decl "u64-read" [(c/p 1 "object")] "uint64"
     (c/let-ir 2 "uint64" {:sproj {:x {:idx 1} :n 2 :offset 0}}
       ["dec" {:idx 1} 1 false false (c/ret 2)]))
   (c/decl "u64-write" [(c/p 1 "object") (c/p 2 "uint64")] "object"
     ["sset" {:idx 1} 2 0 {:idx 2} "uint64" (c/ret 1)])
   (c/decl "u64-case" [(c/p 1 "uint64")] "object"
     ["case" (c/name-ir "UInt64") {:idx 1} "uint64" [["ctor" {:cidx 0} (c/let-ir 2 "object" (c/lit 7) (c/ret 2))]
                                           ["default" (c/let-ir 3 "object" (c/lit 9) (c/ret 3))]]])])
(defn prepare [rows] (assoc *basis* :program (j/invoke-static (:prepare *basis*) [(x/raw rows)])))
(defn context [] (prepare (concat (selected-rows) (helpers))))
(defn box [ctx engine value] (j/call ctx engine "u64-box" [value]))
(defn unbox [ctx engine value] (j/call ctx engine "u64-unbox" [value]))
(defn call-boxed [ctx engine name values output-u64?]
  (let [result (j/call ctx engine (str name "._boxed") (mapv #(box ctx engine %) values))]
    (if output-u64? (unbox ctx engine result) result)))

(defn checked-oracle []
  (let [manifest (edn/read-string (slurp "test/fixtures/java-u64-runtime/provenance.edn"))
        file "test/fixtures/java-u64-runtime/native-hash-oracle.json"]
    (assert (= (get-in manifest [:compiled-hash-source-oracle :results-sha256]) (corpus/sha256 file))
            "Compiled hash-source oracle digest differs from provenance")
    (let [oracle (json/read-str (slurp file))]
      (assert (= (:lean-commit manifest) (get oracle "lean-commit")))
      (doseq [path ["src/runtime/hash.cpp" "src/runtime/hash.h"]]
        (assert (= (get-in manifest [:upstream-source-sha256 path])
                   (get-in oracle ["upstream-source-sha256" path]))))
      oracle)))

(deftest authentic-fixture-subset-and-compiled-hash-source-oracle
  (let [manifest (edn/read-string (slurp "test/fixtures/java-u64-runtime/provenance.edn"))
        oracle (checked-oracle)]
    (is (= (:fixture-sha256 manifest) (corpus/sha256 fixture)))
    (is (= 28 (count (originals)))) (is (= 20 (count (selected-rows))))
    (is (= 0 (get oracle "compiler-exit") (get oracle "oracle-exit")))
    (is (= "little" (get-in oracle ["profile" "byte-order"])))
    (doseq [row (selected-rows) :when (get-in row ["ir" "extern"])]
      (is (string? (j/invoke-static (.getMethod ^Class (:class *basis*) "validateExternAbi"
                                                (into-array Class [java.util.Map])) [row]))))))

(deftest high-bits-literal-modulo-joins-cache-and-ap-boxing
  (let [ctx (context) engine (j/machine ctx)]
    (try
      (doseq [v [0 1 Long/MAX_VALUE high max64]]
        (is (= v (j/call ctx engine "u64-id" [v])))
        (is (= v (j/call ctx engine "u64-join" [v])))
        (let [boxed (box ctx engine v)]
          (is (= 1 (c/rc ctx boxed)))
          (is (= 0 (alength ^objects (.get ^java.lang.reflect.Field (:fields ctx) boxed))))
          (is (= 8 (alength ^bytes (.get ^java.lang.reflect.Field (:scalars ctx) boxed))))
          (is (= v (unbox ctx engine boxed)))))
      (is (= max64 (j/call ctx engine "u64-const" [])))
      (is (= max64 (j/call ctx engine "u64-const" [])))
      (is (= 7 (j/call ctx engine "u64-wide-literal" [])))
      (is (g/bad? #(j/make-closure! ctx engine "u64-id" [])))
      (let [closure (j/make-closure! ctx engine "u64-result" [])
            boxed (j/call ctx engine "apply" [closure 0])]
        (is (= max64 (unbox ctx engine boxed))))
      (finally (j/close! ctx engine)))))

(deftest original-u64-operations-and-explicit-usize-conversion
  (let [ctx (context) engine (j/machine ctx)]
    (try
      (doseq [a [0 1 high max64] b [0 1 63 64 max64]]
        (is (= (.shiftRight (biginteger a) (.intValue (.and (biginteger b) (biginteger 63))))
               (j/call ctx engine "UInt64.shiftRight" [a b])
               (call-boxed ctx engine "UInt64.shiftRight" [a b] true)))
        (is (= (.xor (biginteger a) (biginteger b)) (j/call ctx engine "UInt64.xor" [a b])
               (call-boxed ctx engine "UInt64.xor" [a b] true)))
        (is (= (if (< a b) 1 0) (call-boxed ctx engine "UInt64.decLt" [a b] false)))
        (is (= (if (= a b) 1 0) (call-boxed ctx engine "UInt64.decEq" [a b] false))))
      (doseq [v [0 1 high max64 wide (.shiftLeft java.math.BigInteger/ONE 100)]]
        (let [expected (.and (biginteger v) max64)]
          (is (= expected (j/call ctx engine "UInt64.ofNat" [v])))
          (is (= expected (j/call ctx engine "UInt64.ofNatLT" [v 0])))
          (is (= expected (j/call ctx engine "UInt64.ofBitVec" [v])))
          (is (= expected (unbox ctx engine (j/call ctx engine "UInt64.ofNat._boxed" [v]))))))
      (doseq [v [0 high max64]]
        (is (= v (j/call ctx engine "UInt64.toUSize" [v])))
        (is (= v (j/call ctx engine "usize-unbox" [(call-boxed ctx engine "UInt64.toUSize" [v] false)]))))
      (finally (j/close! ctx engine)))))

(deftest packed-scalar-word-offset-and-forked-exclusive-update
  (let [ctx (context) engine (j/machine ctx)
        value (j/call ctx engine "u64-pack" [42 255 4294967295 max64])
        child (j/fork! ctx engine [value]) child-engine (:engine child) child-value (first (:roots child))]
    (try
      (is (identical? child-value (j/call ctx child-engine "u64-write" [child-value high])))
      (is (= high (j/call ctx child-engine "u64-read" [child-value])))
      (is (= max64 (j/call ctx engine "u64-read" [value])))
      (finally (j/close! ctx engine) (j/close! ctx child-engine)))))

(deftest public-domain-lane-and-wide-case-boundaries-are-explicit
  (doseq [value [-1 wide 1.5]]
    (let [ctx (context) engine (j/machine ctx)]
      (is (re-find #"unsigned scalar|Unsigned scalar" (c/failure #(j/call ctx engine "u64-id" [value]))))))
  (doseq [row [(c/decl "wrong-return" [(c/p 1 "usize")] "uint64" (c/ret 1))
               (c/decl "wrong-join" [(c/p 1 "usize")] "uint64"
                 ["jdecl" {:idx 2} [(c/p 3 "uint64")] (c/ret 3) ["jmp" {:idx 2} [(c/v 1)]]])]]
    (is (g/bad? #(prepare [row]))))
  (let [ctx (context) engine (j/machine ctx)]
    (is (= 7 (j/call ctx engine "u64-case" [0])))
    (is (= 9 (j/call ctx engine "u64-case" [1])))
    (is (re-find #"Wide UInt64 case outside execution profile"
                 (c/failure #(j/call ctx engine "u64-case" [high]))))))

(deftest host-u64-arguments-replies-and-fork-retain-exact-bits
  (let [spec (host/spec "research_u64" ["uint64"] [false] "uint64")
        ctx (j/prepare-host-program *basis* (x/raw [(host/ext "host-u64" spec)]) [spec]) engine (j/machine ctx)]
    (try
      (j/start! ctx engine "host-u64" [max64])
      (let [request (j/host-request ctx engine) child (:engine (j/fork! ctx engine []))]
        (try
          (is (= [max64] (vec (j/request-value request "arguments"))))
          (doseq [invalid [-1 wide 1.5]]
            (is (g/bad? #(j/resume-host! ctx engine request invalid)))
            (is (identical? request (j/host-request ctx engine))))
          (j/resume-host! ctx engine request high)
          (j/resume-host! ctx child (j/host-request ctx child) max64)
          (is (= high (j/take-result! ctx engine)))
          (is (= max64 (j/take-result! ctx child)))
          (finally (j/close! ctx child))))
      (finally (j/close! ctx engine)))))

(deftest code-u64-arguments-and-descendant-body-resume-preserve-bits
  (let [row (first (helpers)) base (j/prepare-host-program *basis* [] [])
        source (j/source-binding base (Object.)) target (header/header source row)
        ctx (j/register-headers base [target]) engine (j/machine ctx)
        ready (code/materialize ctx target row [])]
    (try
      (j/start! ctx engine "u64-id" [max64])
      (let [request (code/request! ctx engine) child (:engine (j/fork! ctx engine []))]
        (try
          (is (= [max64] (vec (j/request-value request "arguments"))))
          (j/resume-code! ready engine request)
          (j/resume-code! ready child (j/code-request ctx child))
          (is (= max64 (code/finish! ready engine) (code/finish! ready child)))
          (finally (j/close! ready child))))
      (finally (j/close! ready engine)))))

(deftest string-and-mix-hashes-match-compiled-pinned-source
  (let [ctx (context) engine (j/machine ctx)
        oracle (checked-oracle)]
    (try
      (doseq [v (get oracle "string") :let [expected (java.math.BigInteger. ^String (get v "hash"))]]
        (is (= expected (j/call ctx engine "String.hash" [(get v "text")])))
        (is (= expected (unbox ctx engine (j/call ctx engine "String.hash._boxed" [(get v "text")])))))
      (doseq [v (get oracle "mix") :let [a (java.math.BigInteger. ^String (get v "h"))
                                         b (java.math.BigInteger. ^String (get v "k"))
                                         expected (java.math.BigInteger. ^String (get v "hash"))]]
        (is (= expected (j/call ctx engine "mixHash" [a b])))
        (is (= expected (call-boxed ctx engine "mixHash" [a b] true))))
      (finally (j/close! ctx engine)))))
(deftest genuine-name-constructors-pack-and-project-the-native-hash
  (let [name-file "test/fixtures/java-u64-runtime/name-rows.json"
        manifest (edn/read-string (slurp "test/fixtures/java-u64-runtime/name-provenance.edn"))
        rows (mapv #(get % "row") (json/read-str (slurp name-file)))
        ctx (prepare (concat rows (helpers))) engine (j/machine ctx)
        oracle (checked-oracle)
        expected (into {} (for [v (get oracle "name")] [(get v "kind") (java.math.BigInteger. ^String (get v "hash"))]))
        hash-name (fn [value]
                    (j/retain! ctx engine value)
                    (unbox ctx engine (j/call ctx engine "Lean.Name.hash._override._boxed" [value])))]
    (try
      (is (= (:fixture-sha256 manifest) (corpus/sha256 name-file)))
      (is (= 11 (count rows)))
      (is (= (expected "anonymous") (hash-name 0)))
      (doseq [[name args] [["str-foo" [0 "foo"]] ["num-max64" [0 max64]]
                          ["num-2^64-sentinel17" [0 (.add max64 java.math.BigInteger/ONE)]]]
              :let [target (if (= name "str-foo") "Lean.Name.str._override" "Lean.Name.num._override")
                    value (j/call ctx engine target args)]]
        (is (= 1 (c/rc ctx value)))
        (is (= (expected name) (hash-name value)))
        (is (= 1 (c/rc ctx value)))
        (j/release! ctx engine value))
      (finally (j/close! ctx engine)))))

(deftest self-tail-call-preserves-u64-through-object-and-boolean-work
  (let [nat-rows (x/originals)
        eq-name (get (nat-rows "Nat.decEq") "name")
        sub-name (get (nat-rows "Nat.sub") "name")
        recur-body (c/let-ir 5 "object" (c/lit 1)
                     (c/let-ir 6 "object" {:fap {:c sub-name :ys [(c/v 2) (c/v 5)]}}
                       (c/let-ir 7 "uint64" (c/fap "tail-u64" [(c/v 1) (c/v 6)]) (c/ret 7))))
        row (c/decl "tail-u64" [(c/p 1 "uint64") (c/p 2 "object")] "uint64"
              (c/let-ir 3 "object" (c/lit 0)
                (c/let-ir 4 "uint8" {:fap {:c eq-name :ys [(c/v 2) (c/v 3)]}}
                  ["case" (c/name-ir "Bool") {:idx 4} "uint8"
                   [["ctor" {:cidx 0} recur-body] ["ctor" {:cidx 1} (c/ret 1)]]])))
        ctx (prepare [(nat-rows "Nat.decEq") (nat-rows "Nat.sub") row]) engine (j/machine ctx)]
    (try
      (is (= max64 (j/call ctx engine "tail-u64" [max64 1000])))
      (is (= high (j/call ctx engine "tail-u64" [high 0])))
      (finally (j/close! ctx engine)))))
(defn check! [basis] (binding [*basis* basis] (run-tests 'java-ir-u64-checks)))
