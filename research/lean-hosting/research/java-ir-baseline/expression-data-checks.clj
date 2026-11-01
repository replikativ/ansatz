(ns java-ir-expression-data-checks
  "Native scalar Expr/Level cached-data words; no AST object representation."
  (:require [clojure.test :refer [deftest is run-tests]]
            [clojure.data.json :as json] [clojure.edn :as edn]
            [java-ir-baseline :as j] [java-ir-baseline-checks :as c]
            [java-ir-extern-checks :as x] [java-ir-generation-checks :as g]
            [java-ir-host-checks :as host] [java-ir-continuation-checks :as k]
            [lean-compatibility-corpus :as corpus]))
(def ^:dynamic *basis* nil)
(def directory "test/fixtures/java-expression-data-runtime/")
(defn originals [] (json/read-str (slurp (str directory "original-rows.json"))))
(defn rows [] (mapv #(get % "row") (originals)))
(def labels {"expr" "Lean.Expr.mkData" "app" "Lean.Expr.mkAppData" "level" "Lean.Level.mkData"})
(def max64 (biginteger "18446744073709551615"))
(def high64 (biginteger "9223372036854775808"))
(def helpers
  [(second g/common)
   (c/decl "data-box" [(c/p 1 "uint64")] "object"
     (c/let-ir 2 "object" {:box {:ty "uint64" :x {:idx 1}}} (c/ret 2)))
   (c/decl "data-unbox" [(c/p 1 "object")] "uint64"
     (c/let-ir 2 "uint64" {:unbox {:x {:idx 1}}}
       ["dec" {:idx 1} 1 false false (c/ret 2)]))])
(defn context [] (assoc *basis* :program (j/invoke-static (:prepare *basis*) [(into (rows) (x/raw helpers))])))
(defn box [ctx engine word] (j/call ctx engine "data-box" [word]))
(defn unbox [ctx engine word] (j/call ctx engine "data-unbox" [word]))
(defn boxed-args [ctx engine op args]
  (if (= op "app") (mapv #(box ctx engine %) args)
    (assoc (vec args) 0 (box ctx engine (first args)))))
(defn boxed-call [ctx engine op args]
  (unbox ctx engine (j/call ctx engine (str (labels op) "._boxed") (boxed-args ctx engine op args))))

(deftest pinned-original-rows-and-exact-owned-abis
  (let [manifest (edn/read-string (slurp (str directory "provenance.edn")))
        validate (.getMethod ^Class (:class *basis*) "validateExternAbi" (into-array Class [java.util.Map]))]
    (is (= 6 (count (originals))))
    (is (= (:fixture-sha256 manifest) (corpus/sha256 (str directory "original-rows.json"))))
    (is (= "819816b2e0a3bf405af45ae5c7af2491d8f5bee6" (:lean-commit manifest)))
    (doseq [row (rows) :when (get-in row ["ir" "extern"])]
      (is (string? (j/invoke-static validate [row])))
      (doseq [i (range (count (get-in row ["ir" "extern" "xs"])))]
        (is (g/bad? #(j/invoke-static validate [(assoc-in row ["ir" "extern" "xs" i "borrow"] true)])))
        (is (g/bad? #(j/invoke-static validate [(assoc-in row ["ir" "extern" "xs" i "ty"] "usize")]))))
      (is (g/bad? #(j/invoke-static validate [(assoc-in row ["ir" "extern" "type"] "usize")]))))))

(deftest native-runtime-vectors-through-raw-roots-and-authentic-boxed-faps
  (let [receipt (json/read-str (slurp (str directory "native-receipt.json")))
        vectors (json/read-str (slurp (str directory "native-vectors.json")))
        ctx (context) engine (j/machine ctx)]
    (try
      (is (= 160 (count vectors) (get receipt "vector-count")))
      (is (= ["--run" "C/native"] (get receipt "modes")))
      (is (= 0 (get receipt "exit"))) (is (= "" (get receipt "stderr")))
      (is (= (get receipt "source-sha256") (corpus/sha256 (str directory "DataOracle.lean"))))
      (is (= (get receipt "vectors-sha256") (corpus/sha256 (str directory "native-vectors.json"))))
      (doseq [{:strs [op args result]} vectors
              :let [args (mapv x/nat args) expected (biginteger result)]]
        (is (= expected (j/call ctx engine (labels op) args)))
        (is (= expected (boxed-call ctx engine op args))))
      (finally (j/close! ctx engine)))))

(deftest nat-carriers-and-depth-saturation-preserve-native-bounds
  (let [ctx (context) engine (j/machine ctx)]
    (try
      (doseq [range [0 (biginteger 0) 1048575 (biginteger 1048575)] depth [0 254 255 256 4294967295]]
        (let [v (biginteger (j/call ctx engine "Lean.Expr.mkData" [max64 range depth 1 0 1 0]))]
          (is (= 4294967295 (.longValue (.and v (biginteger 4294967295)))))
          (is (= (min depth 255) (.longValue (.and (.shiftRight v 32) (biginteger 255)))))
          (is (= (biginteger range) (.shiftRight v 44)))))
      (doseq [depth [0 (biginteger 0) 16777215 (biginteger 16777215)]]
        (is (= (biginteger depth) (.shiftRight (biginteger (j/call ctx engine "Lean.Level.mkData" [high64 depth 0 1])) 40))))
      (finally (j/close! ctx engine)))))

(deftest all-raw-invalid-domains-reject-without-primitive-effects
  (doseq [[label args] (concat
           (for [v [-1 (biginteger -1) 1048576 (.shiftLeft java.math.BigInteger/ONE 100) "bad"]]
             ["Lean.Expr.mkData" [max64 v 0 0 0 0 0]])
           (for [v [-1 16777216 (.shiftLeft java.math.BigInteger/ONE 100) "bad"]]
             ["Lean.Level.mkData" [max64 v 0 0]])
           (for [index [3 4 5 6] v [2 255]] ["Lean.Expr.mkData" (assoc [max64 0 0 0 0 0 0] index v)])
           (for [index [2 3] v [2 255]] ["Lean.Level.mkData" (assoc [max64 0 0 0] index v)])
           (for [v [-1 4294967296 1.5]] ["Lean.Expr.mkData" [max64 0 v 0 0 0 0]])
           (for [label (vals labels) v [-1 (.shiftLeft java.math.BigInteger/ONE 64) 1.5]]
             [label (case label "Lean.Expr.mkData" [v 0 0 0 0 0 0] "Lean.Level.mkData" [v 0 0 0] [v 0])]))]
    (let [ctx (context) engine (j/machine ctx) before (k/counters ctx engine)]
      (is (g/bad? #(j/call ctx engine label args)))
      (is (= before (k/counters ctx engine)))
      ;; Domain errors inside explicit execution leave the known failed profile;
      ;; public-entry lane errors are rejected while still idle.
      (when (= "idle" (j/phase ctx engine)) (j/close! ctx engine)))))

(deftest direct-seven-argument-fap-validates-final-flags-before-publishing
  (let [target (get-in (first (originals)) ["row" "name"])
        forward (c/decl "forward-data" [(c/p 1 "uint64") (c/p 2 "tobject") (c/p 3 "uint32")
                                        (c/p 4 "uint8") (c/p 5 "uint8") (c/p 6 "uint8") (c/p 7 "uint8")] "uint64"
                  (c/let-ir 8 "uint64" {:fap {:c target :ys (mapv c/v (range 1 8))}} (c/ret 8)))
        ctx (assoc *basis* :program (j/invoke-static (:prepare *basis*) [(conj (rows) (first (x/raw [forward])))]))]
    (let [engine (j/machine ctx)]
      (try
        (is (= max64 (j/call ctx engine "forward-data" [max64 1048575 4294967295 1 1 1 1])))
        (finally (j/close! ctx engine))))
    (let [engine (j/machine ctx) before (k/counters ctx engine)]
      (is (re-find #"Expr.mkData flags require Bool" (c/failure #(j/call ctx engine "forward-data" [0 0 0 0 0 0 2]))))
      (is (= before (k/counters ctx engine))))))

(deftest malformed-owned-nat-node-retains-owner-before-rejection
  (doseq [[label args] [["Lean.Expr.mkData" [0 :node 0 0 0 0 0]] ["Lean.Level.mkData" [0 :node 0 0]]]]
    (let [ctx (context) engine (j/machine ctx) source (j/source-binding ctx (Object.))
          [node] (j/install-graph! ctx engine
                   (j/selected-owner-graph ctx source (Object.)
                     [(j/graph-node ctx {:kind :ctor :id 1 :rc 77 :tag 0 :fields [0]})]
                     [] [] [(j/graph-ref ctx 1)])) before (k/counters ctx engine)]
      (is (g/bad? #(j/call ctx engine label (mapv (fn [v] (if (= v :node) node v)) args))))
      (is (= before (k/counters ctx engine)))
      (is (= 1 (c/rc ctx node))) (is (false? (host/private-value node "dead")))
      (when-not (:explicit ctx) (j/release! ctx engine node) (j/close! ctx engine)))))

(deftest boxed-partial-application-captures-survive-independent-forks
  (doseq [[op args expected] [["expr" [max64 1048575 4294967295 1 1 1 1] max64]
                            ["level" [max64 16777215 1 1] (biginteger "18446742991377793023")]
                            ["app" [max64 high64] nil]]]
    (let [ctx (context) engine (j/machine ctx)
          expected (or expected (j/call ctx engine (labels op) args))
          captures (boxed-args ctx engine op (pop args))
          closure (j/make-closure! ctx engine (str (labels op) "._boxed") captures)
          ;; app's final argument must also be an actual boxed UInt64.
          last-arg (if (= op "app") (box ctx engine (peek args)) (peek args))
          fork (j/fork! ctx engine [closure last-arg]) child (:engine fork)]
      (try
        (is (= expected (unbox ctx engine (j/call ctx engine "apply" [closure last-arg]))))
        (is (= expected (unbox ctx child (j/call ctx child "apply" (:roots fork)))))
        (finally (j/close! ctx engine) (j/close! ctx child))))))

(deftest high-data-words-cross-host-suspension-and-fork-without-sign-loss
  (let [spec (host/spec "research_data_word" ["uint64"] [false] "uint64")
        caller (c/decl "data-host-caller" [(c/p 1 "uint64") (c/p 2 "uint64")] "uint64"
                 (c/let-ir 3 "uint64" {:fap {:c (get-in (first (filter #(= "Lean.Expr.mkAppData" (get % "label")) (originals))) ["row" "name"]) :ys [(c/v 1) (c/v 2)]}}
                   (c/let-ir 4 "uint64" (c/fap "data-host" [(c/v 3)]) (c/ret 4))))
        ctx (j/prepare-host-program *basis* (into (rows) (x/raw [(host/ext "data-host" spec) caller])) [spec])
        parent (j/machine ctx) expected (j/call ctx parent "Lean.Expr.mkAppData" [max64 high64])]
    (j/start! ctx parent "data-host-caller" [max64 high64])
    (let [request (host/request! ctx parent) child (:engine (j/fork! ctx parent []))
          child-request (j/host-request ctx child)]
      (try
        (is (= [expected] (host/args request) (host/args child-request)))
        (is (>= expected high64))
        (is (g/bad? #(j/resume-host! ctx child request expected)))
        (j/resume-host! ctx parent request max64) (j/resume-host! ctx child child-request high64)
        (is (= max64 (host/finish! ctx parent))) (is (= high64 (host/finish! ctx child)))
        (finally (j/close! ctx parent) (j/close! ctx child))))))

(deftest original-wrapper-code-request-preserves-boxed-words-and-header-pin
  (let [records (into {} (map (juxt #(get % "label") identity) (originals)))
        base (j/prepare-host-program *basis* (x/raw helpers) []) source (j/source-binding base (Object.))
        headers (into {} (for [[label record] records]
                          [label (j/declaration-header source (get record "row") (get record "sha256"))]))
        target (headers "Lean.Expr.mkData._boxed") dependency (headers "Lean.Expr.mkData")
        ctx (j/register-headers base [target dependency])
        ready (j/materialize-body ctx target (get-in records ["Lean.Expr.mkData._boxed" "row"]) [dependency])
        parent (j/machine ctx) args [(box ctx parent max64) 1048575 4294967295 1 1 1 1]]
    (j/start! ctx parent "Lean.Expr.mkData._boxed" args)
    (let [request (j/code-request ctx parent) fork (j/fork! ctx parent []) child (:engine fork)
          child-request (j/code-request ctx child)]
      (try
        (is (identical? target (j/request-value request "header")))
        (is (= (get-in records ["Lean.Expr.mkData._boxed" "sha256"]) (.originalSha256 target)))
        (is (= (repeat 8 -1) (seq (.get ^java.lang.reflect.Field (:scalars ctx)
                                                (first (vec (j/request-value request "arguments")))))))
        (j/resume-code! ready parent request) (j/resume-code! ready child child-request)
        (let [a (k/finish! ready parent [1 2 3]) b (k/finish! ready child [1 2 3])]
          (is (= max64 (unbox ready parent a) (unbox ready child b))))
        (finally (j/close! ready parent) (j/close! ready child))))))

(defn check! [basis] (binding [*basis* basis] (run-tests 'java-ir-expression-data-checks)))
