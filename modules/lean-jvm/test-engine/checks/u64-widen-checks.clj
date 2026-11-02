(ns java-ir-u64-widen-checks
  "Exact original supported-lane widening to UInt64; no UInt16 execution."
  (:require [clojure.test :refer [deftest is run-tests]] [clojure.data.json :as json]
            [java-ir-baseline :as j] [java-ir-baseline-checks :as c]
            [java-ir-extern-checks :as x] [java-ir-u64-checks :as u]
            [java-ir-host-checks :as host] [java-ir-header-checks :as header]
            [java-ir-code-checks :as code] [java-ir-generation-checks :as g]
            [lean-compatibility-corpus :as corpus]))
(def ^:dynamic *basis* nil)
(def directory "test/fixtures/java-u64-widen-runtime/")
(defn originals [] (json/read-str (slurp (str directory "original-rows.json"))))
(defn carrier [value] (if (<= value Long/MAX_VALUE) (long value) (biginteger value)))
(defn lane-label [lane] ({8 "UInt8.toUInt64" 32 "UInt32.toUInt64" 64 "USize.toUInt64"} lane))
(defn context []
  (let [boxes (for [type ["uint8" "uint32" "usize"]]
                (c/decl (str "box-" type) [(c/p 1 type)] "object"
                  (c/let-ir 2 "object" {:box {:ty type :x {:idx 1}}} (c/ret 2))))
        helpers (concat boxes (filter #(contains? #{"u64-box" "u64-unbox"} (last (:name %))) (u/helpers))
                  [(c/decl "apply-one" [(c/p 1 "object") (c/p 2 "object")] "object"
                     (c/let-ir 3 "object" {:ap {:x {:idx 1} :ys [(c/v 2)]}} (c/ret 3)))])]
    (assoc *basis* :program (j/invoke-static (:prepare *basis*)
      [(into (mapv #(get % "row") (originals)) (x/raw helpers))]))))
(defn boxed-input [ctx engine lane value]
  (j/call ctx engine (str "box-" ({8 "uint8" 32 "uint32" 64 "usize"} lane)) [value]))
(deftest authentic-abis-and-compiled-inline-cast-provenance
  (let [p (json/read-str (slurp (str directory "provenance.json")))
        receipt (json/read-str (slurp (str directory "native-receipt.json")))]
    (is (= 6 (count (originals))))
    (is (= (get p "fixture-sha256") (corpus/sha256 (str directory "original-rows.json"))))
    (is (= "819816b2e0a3bf405af45ae5c7af2491d8f5bee6" (get receipt "lean-commit")))
    (is (= [0 0 3 15 64] (mapv #(get receipt %) ["exit" "stderr-bytes" "functions" "vectors" "word-bits"])))
    (doseq [[file digest] (get p "compiled-inline-oracle")]
      (is (= digest (corpus/sha256 (str directory file)))))
    (doseq [entry (originals) :let [row (get entry "row")] :when (get-in row ["ir" "extern"])]
      (is (string? (j/invoke-static (.getMethod ^Class (:class *basis*) "validateExternAbi"
                                    (into-array Class [java.util.Map])) [row]))))))
(deftest zero-extension-and-fixed64-bit-identity-match-native-direct-and-boxed
  (let [ctx (context) engine (j/machine ctx)
        vectors (json/read-str (slurp (str directory "native-vectors.json")))]
    (try
      (doseq [v vectors :let [lane (get v "lane") label (lane-label lane)
                             value (carrier (biginteger (get v "input")))
                             expected (carrier (biginteger (get v "result")))
                             before (host/private-value engine "allocations")]]
        (is (= expected (j/call ctx engine label [value])))
        (is (= before (host/private-value engine "allocations")))
        (let [input (boxed-input ctx engine lane value)
              result (j/call ctx engine (str label "._boxed") [input])]
          (is (= 1 (c/rc ctx result)))
          (is (= expected (u/unbox ctx engine result)))
          (is (true? (host/private-value result "dead")))
          (when (= lane 64) (is (true? (host/private-value input "dead"))))))
      (finally (j/close! ctx engine)))))
(deftest width-domains-reject-before-root-or-unboxed-partial-claims
  (let [ctx (context) engine (j/machine ctx)]
    (try
      (doseq [[label wide] [["UInt8.toUInt64" 256] ["UInt32.toUInt64" 4294967296]
                           ["USize.toUInt64" (.shiftLeft java.math.BigInteger/ONE 64)]]]
        (doseq [value [-1 wide 1.5 nil]]
          (let [before (mapv #(host/private-value engine %) ["allocations" "retains" "releases" "shellDeletes"])]
            (is (g/bad? #(j/call ctx engine label [value])))
            (is (= "idle" (j/phase ctx engine)))
            (is (= before (mapv #(host/private-value engine %) ["allocations" "retains" "releases" "shellDeletes"])))))
        (is (g/bad? #(j/make-closure! ctx engine label []))))
      (finally (j/close! ctx engine)))))
(deftest original-boxed-ap-forks-real-owned-usize-boxes-and-preserves-high-bits
  (let [ctx (context) parent (j/machine ctx)
        input (boxed-input ctx parent 64 u/max64)
        closure (j/make-closure! ctx parent "USize.toUInt64._boxed" [])
        {:keys [engine roots]} (j/fork! ctx parent [closure input]) child engine [cc ci] roots]
    (try
      (doseq [[e f value] [[parent closure input] [child cc ci]]]
        (let [result (j/call ctx e "apply-one" [f value])]
          (is (= 1 (c/rc ctx result)))
          (is (= u/max64 (u/unbox ctx e result)))
          (is (true? (host/private-value value "dead")))
          (is (true? (host/private-value f "dead")))))
      (finally (j/close! ctx parent) (j/close! ctx child)))))
(deftest code-host-fork-crosses-explicit-usize-to-u64-boundary-without-sign-change
  (let [spec (host/spec "research_widen_u64" ["uint64"] [false] "uint64")
        original (first (filter #(= "USize.toUInt64" (get % "label")) (originals)))
        native-name (get-in original ["row" "name"])
        row (c/decl "caller" [(c/p 1 "usize")] "uint64"
              (c/let-ir 2 "uint64" {:fap {:c native-name :ys [(c/v 1)]}}
                (c/let-ir 3 "uint64" (c/fap "host" [(c/v 2)]) (c/ret 3))))
        base (j/prepare-host-program *basis* [] []) source (j/source-binding base (Object.))
        native (j/declaration-header source (get original "row") (get original "sha256"))
        outer (header/header source (host/ext "host" spec)) target (header/header source row)
        ctx (j/register-headers base [native outer target] [spec]) parent (j/machine ctx)
        ready (code/materialize ctx target row [native outer])]
    (j/start! ctx parent "caller" [u/high])
    (let [request (code/request! ctx parent) child (:engine (j/fork! ctx parent []))]
      (try
        (is (= [u/high] (vec (.arguments request))))
        (doseq [e [parent child]]
          (j/resume-code! ready e (j/code-request ready e))
          (let [request (host/request! ready e)]
            (is (= [u/high] (host/args request)))
            (j/resume-host! ready e request u/max64)
            (is (= u/max64 (code/finish! ready e)))))
        (finally (j/close! ready parent) (j/close! ready child))))))
(defn check! [basis] (binding [*basis* basis] (run-tests 'java-ir-u64-widen-checks)))
