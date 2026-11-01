(ns java-ir-u64-scalars-checks
  "Pinned UInt64 arithmetic/logical family, genuine wrappers and reached Config body."
  (:require [clojure.test :refer [deftest is run-tests]] [clojure.data.json :as json]
            [java-ir-baseline :as j] [java-ir-baseline-checks :as c]
            [java-ir-u64-checks :as u] [java-ir-extern-checks :as x]
            [java-ir-host-checks :as host] [java-ir-header-checks :as header]
            [java-ir-code-checks :as code] [java-ir-generation-checks :as g]
            [lean-compatibility-corpus :as corpus]))
(def ^:dynamic *basis* nil)
(def directory "test/fixtures/java-u64-scalars-runtime/")
(defn originals [] (json/read-str (slurp (str directory "original-rows.json"))))
(defn original-name [label]
  (get-in (first (filter #(= label (get % "label")) (originals))) ["row" "name"]))
(defn native-fap [label args] {:fap {:c (original-name label) :ys args}})
(defn config-rows [] (json/read-str (slurp (str directory "config-rows.json"))))
(defn carrier [value] (if (<= value Long/MAX_VALUE) (long value) (biginteger value)))
(defn number-string [value] (carrier (java.math.BigInteger. ^String value)))
(defn helpers []
  (concat (u/helpers)
    [(c/decl "apply-one" [(c/p 1 "object") (c/p 2 "object")] "object"
       (c/let-ir 3 "object" {:ap {:x {:idx 1} :ys [(c/v 2)]}} (c/ret 3)))
     (c/decl "config-new" (mapv #(c/p (inc %) "uint8") (range 19)) "object"
       (c/let-ir 20 "object" (c/ctor 0 [] 19)
         (reduce (fn [next i] ["sset" {:idx 20} 0 i {:idx (inc i)} "uint8" next])
                 (c/ret 20) (reverse (range 19)))))]))
(defn context []
  (assoc *basis* :program (j/invoke-static (:prepare *basis*)
    [(into (mapv #(get % "row") (concat (originals) (config-rows))) (x/raw (helpers)))])))
(defn boxed [ctx engine label args]
  (let [result (j/call ctx engine (str label "._boxed")
                      (if (= label "Bool.toUInt64") args (mapv #(u/box ctx engine %) args)))]
    (if (= label "UInt64.decLe") result (u/unbox ctx engine result))))
(defn arguments [label vector]
  (cond (= label "Bool.toUInt64") [(number-string (get vector "flag"))]
        (contains? #{"UInt64.complement" "UInt64.neg" "UInt64.log2"} label)
        [(number-string (get vector "a"))]
        :else [(number-string (get vector "a")) (number-string (get vector "b"))]))

(deftest exact-source-fixture-abis-and-verbatim-native-inline-oracle
  (let [manifest (json/read-str (slurp (str directory "provenance.json")))
        receipt (json/read-str (slurp (str directory "native-receipt.json")))]
    (is (= 26 (count (originals))))
    (is (= 5 (count (config-rows))))
    (is (= (get manifest "fixture-sha256")
           (corpus/sha256 (str directory "original-rows.json"))))
    (is (= (get manifest "config-rows-sha256")
           (corpus/sha256 (str directory "config-rows.json"))))
    (is (= "819816b2e0a3bf405af45ae5c7af2491d8f5bee6" (get receipt "lean-commit")))
    (is (= [0 0 40 13] (mapv #(get receipt %) ["exit" "stderr-bytes" "vectors" "functions"])))
    (doseq [[file digest] (get manifest "compiled-inline-oracle")]
      (is (= digest (corpus/sha256 (str directory file)))))
    (is (= (get receipt "vectors-sha256")
           (corpus/sha256 (str directory "native-vectors.json"))))
    (doseq [entry (originals) :let [row (get entry "row")] :when (get-in row ["ir" "extern"])]
      (is (string? (j/invoke-static (.getMethod ^Class (:class *basis*) "validateExternAbi"
                                  (into-array Class [java.util.Map])) [row]))))))

(deftest direct-and-original-boxed-family-match-compiled-native-arithmetic
  (let [ctx (context) engine (j/machine ctx)
        vectors (json/read-str (slurp (str directory "native-vectors.json")))]
    (try
      (doseq [vector vectors [label value] (get vector "results")]
        (let [args (arguments label vector) expected (number-string value)
              allocations (host/private-value engine "allocations")]
          (is (= expected (j/call ctx engine label args)) label)
          (is (= allocations (host/private-value engine "allocations")) "Raw scalar call allocates no Node")
          (is (= expected (boxed ctx engine label args)) (str label " genuine boxed ABI"))))
      (finally (j/close! ctx engine)))))

(deftest generic-partial-application-forks-owned-boxes-without-new-value-copies
  (let [ctx (context) parent (j/machine ctx)
        first-box (u/box ctx parent u/max64) second-box (u/box ctx parent 1)
        closure (j/make-closure! ctx parent "UInt64.add._boxed" [first-box])
        {:keys [engine roots]} (j/fork! ctx parent [closure second-box]) child engine [cc cb] roots]
    (try
      (doseq [[e f b] [[parent closure second-box] [child cc cb]]]
        (let [deletes (host/private-value e "shellDeletes")]
          (is (= 0 (u/unbox ctx e (j/call ctx e "apply-one" [f b]))))
          (is (= (inc deletes) (host/private-value e "shellDeletes")))
          (is (= 0 (c/rc ctx b)))
          (is (true? (host/private-value f "dead")))))
      (finally (j/close! ctx parent) (j/close! ctx child)))))

(deftest invalid-public-lanes-and-canonical-bool-reject-before-claims
  (let [ctx (context) engine (j/machine ctx)]
    (try
      (doseq [invalid [-1 2 255 256 1.5 nil]]
        (let [before (mapv #(host/private-value engine %) ["allocations" "retains" "releases" "shellDeletes"])]
          (is (g/bad? #(j/call ctx engine "Bool.toUInt64" [invalid])))
          (is (= "idle" (j/phase ctx engine)))
          (is (= before (mapv #(host/private-value engine %) ["allocations" "retains" "releases" "shellDeletes"])))))
      (doseq [invalid [-1 u/wide 1.5]]
        (is (g/bad? #(j/call ctx engine "UInt64.add" [invalid 1])))
        (is (= "idle" (j/phase ctx engine))))
      (let [before (mapv #(host/private-value engine %) ["allocations" "retains" "releases" "shellDeletes"])]
        (is (g/bad? #(j/make-closure! ctx engine "Bool.toUInt64" [])))
        (is (= "idle" (j/phase ctx engine)))
        (is (= before (mapv #(host/private-value engine %) ["allocations" "retains" "releases" "shellDeletes"]))))
      ;; Native scalar partial targets require genuine boxed wrappers; malformed
      ;; Bool inside a boxed wrapper is a guest failure after ordinary entry.
      (finally (j/close! ctx engine)))))

(deftest genuine-meta-config-key-body-uses-source-bit-positions
  (let [ctx (context) engine (j/machine ctx)
        name (get (first (config-rows)) "label")
        shifts [3 4 5 6 7 8 9 10 11 0 17 16 12 13 19 14 15 22 21]
        patterns [(vec (repeat 19 0)) (vec (repeat 19 1))
                  (assoc (mapv #(mod % 2) (range 19)) 9 4 10 2 14 2)]]
    (try
      (doseq [values patterns]
        (let [expected (reduce bit-or 0 (map bit-shift-left values shifts))
              cfg (j/call ctx engine "config-new" values)
              result (j/call ctx engine (str name "._boxed") [cfg])]
          (is (= expected (u/unbox ctx engine result)))
          (is (true? (host/private-value cfg "dead")))))
      (finally (j/close! ctx engine)))))

(deftest new-family-composes-with-code-host-pause-and-typed-high-bit-fork
  (let [spec (host/spec "research_u64_family" ["uint64"] [false] "uint64")
        row (c/decl "caller" [(c/p 1 "uint64")] "uint64"
              (c/let-ir 2 "uint64" (c/lit 1)
                (c/let-ir 3 "uint64" (native-fap "UInt64.add" [(c/v 1) (c/v 2)])
                  (c/let-ir 4 "uint64" (c/fap "host" [(c/v 3)])
                    (c/let-ir 5 "uint64" (native-fap "UInt64.lor" [(c/v 4) (c/v 2)]) (c/ret 5))))))
        base (j/prepare-host-program *basis* [] []) source (j/source-binding base (Object.))
        raw (concat (map #(get % "row") (filter #(contains? #{"UInt64.add" "UInt64.lor"} (get % "label")) (originals)))
                    (x/raw [(host/ext "host" spec) row]))
        hs (into {} (for [r raw] [(get r "name") (j/declaration-header source r header/digest)]))
        ctx (j/register-headers base (vec (vals hs)) [spec]) parent (j/machine ctx)
        ready (j/materialize-body ctx (get hs (c/name-ir "caller")) (first (x/raw [row]))
                                  (mapv #(get hs (if (= % "host") (c/name-ir %) (original-name %))) ["UInt64.add" "UInt64.lor" "host"]))]
    (j/start! ctx parent "caller" [Long/MAX_VALUE])
    (let [request (code/request! ctx parent) child (:engine (j/fork! ctx parent []))]
      (try
        (doseq [e [parent child]]
          (j/resume-code! ready e (j/code-request ready e))
          (let [request (host/request! ready e)]
            (is (= [u/high] (host/args request)))
            (is (g/bad? #(j/resume-host! ready e request u/wide)))
            (is (identical? request (j/host-request ready e)))
            (j/resume-host! ready e request u/high)
            (is (= (.add u/high java.math.BigInteger/ONE) (code/finish! ready e)))))
        (finally (j/close! ready parent) (j/close! ready child))))))
(defn check! [basis] (binding [*basis* basis] (run-tests 'java-ir-u64-scalars-checks)))
