(ns java-ir-string-completion-checks
  "Five original String helpers: byte ranges, owned Substrings and bounded output."
  (:require [clojure.test :refer [deftest is run-tests]]
            [java-ir-baseline :as j] [java-ir-baseline-checks :as c]
            [java-ir-string-checks :as s] [java-ir-extern-checks :as x]
            [java-ir-generation-checks :as g] [java-ir-host-checks :as host]))
(def ^:dynamic *basis* nil)
(def memcmp "String.Slice.Pattern.Internal.memcmpStr")
(def substring-eq "Substring.Raw.Internal.beq")
(defn record [label] (first (filter #(= label (get % "label")) (s/originals))))
(defn substring-row []
  (c/decl "substring" [(c/p 1 "object") (c/p 2 "object") (c/p 3 "object")] "object"
    (c/let-ir 4 "object" (c/ctor 0 [(c/v 1) (c/v 2) (c/v 3)] 0) (c/ret 4))))
(defn context []
  (assoc *basis* :program (j/invoke-static (:prepare *basis*)
                           [(into (s/selected-rows) (x/raw [(substring-row)
                             (c/decl "apply-range" (mapv #(c/p % "object") (range 1 7)) "object"
                               (c/let-ir 7 "object" {:ap {:x {:idx 1} :ys (mapv c/v (range 2 7))}} (c/ret 7)))]))])))
(defn substring [ctx engine text begin end] (j/call ctx engine "substring" [text begin end]))
(defn compare-substrings [ctx engine a b] (s/invoke ctx engine substring-eq [a b]))
(defn compare-ranges [ctx engine a b start other size]
  (s/invoke ctx engine memcmp [a b start other size 0 0]))
(defn counters [engine] (mapv #(host/private-value engine %) ["allocations" "stores" "retains" "releases"]))
(defn close-after-failure [ctx engine]
  ;; The existing explicit driver retains failure owner obligations; blanket
  ;; cleanup is intentionally unavailable. These fixtures contain no resources.
  (if (:explicit ctx) (is (g/bad? #(j/close! ctx engine))) (j/close! ctx engine)))

(deftest original-five-abis-and-boxed-wrappers-prepare-unchanged
  (let [ctx (context)]
    (doseq [label [memcmp substring-eq "String.Internal.posOf" "String.Internal.offsetOfPos" "String.Internal.pushn"]]
      (is (some? (record (str label "._boxed"))))
      (is (string? (j/invoke-static (.getMethod ^Class (:class ctx) "validateExternAbi"
                                                (into-array Class [java.util.Map])) [(get (record label) "row")]))))))

(deftest memcmp-is-seven-argument-byte-equality-including-continuation-bytes
  (let [ctx (context) engine (j/machine ctx)]
    (try
      (doseq [[a b] [["aé😀\u0000z" "xé😀\u0000y"] ["é" "ê"] ["" ""]]
              :let [x (mapv #(Byte/toUnsignedInt %) (s/utf8 a))
                    y (mapv #(Byte/toUnsignedInt %) (s/utf8 b))]
              i (range (inc (count x))) k (range (inc (count y)))
              n (range (inc (min (- (count x) i) (- (count y) k))))]
        (is (= (if (= (subvec x i (+ i n)) (subvec y k (+ k n))) 1 0)
               (compare-ranges ctx engine a b i k n))))
      (finally (j/close! ctx engine)))))

(deftest raw-borrowed-range-entry-pap-and-import-reject
  (let [ctx (context) engine (j/machine ctx) row (get (record memcmp) "row")]
    (try
      (is (re-find #"Borrowed String range primitive" (c/failure #(j/call ctx engine memcmp []))))
      (is (g/bad? #(j/make-closure! ctx engine memcmp [])))
      (let [pap (c/decl "raw-range-pap" [] "object"
                  (c/let-ir 1 "object" {:pap {:c (get row "name") :ys []}} (c/ret 1)))]
        (is (re-find #"Borrowed String range primitive"
                     (c/failure #(j/invoke-static (:prepare *basis*) [(into (s/selected-rows) (x/raw [pap]))])))))
      (let [source (j/source-binding ctx (Object.))
            h (j/declaration-header source row (get (record memcmp) "sha256"))
            imported (j/register-headers (j/prepare-host-program *basis* [] []) [h])
            imported-engine (j/machine imported)]
        (try
          (is (g/bad? #(j/install-graph! imported imported-engine
                         (j/prepared-graph imported source (Object.)
                           [(j/graph-node imported {:kind :closure :id 1 :target h :fields []})]
                           [] [] [(j/graph-ref imported 1)]))))
          (is (false? (host/private-value imported-engine "graphInstalled")))
          (is (= [] (j/install-graph! imported imported-engine
                       (j/prepared-graph imported source (Object.) [] [] [] []))))
          (finally (j/close! imported imported-engine))))
      (is (= 1 (compare-ranges ctx engine "é" "ê" 0 0 1)))
      (is (= 1 (j/call ctx engine "apply-range"
                 [(j/make-closure! ctx engine (str memcmp "._boxed") ["é" "ê"]) 0 0 1 0 0])))
      (finally (j/close! ctx engine)))))

(deftest invalid-range-and-proof-fail-before-any-guest-owner-effects
  (doseq [args [["x" "x" 0 0 1 1 0] ["x" "x" 0 0 1 0 1]
                ["x" "x" 1 0 1 0 0] ["x" "x" 0 2 0 0 0]
                ["x" "x" s/huge 0 0 0 0] ["x" "x" 0 0 s/huge 0 0]
                ["x" "x" -1 0 0 0 0]]]
    (let [ctx (context) engine (j/machine ctx) before (counters engine)]
      (is (not= "NO ERROR" (c/failure #(s/invoke ctx engine memcmp args))))
      (is (= before (counters engine)))
      (close-after-failure ctx engine))))

(deftest substring-repairs-endpoints-and-compares-content-not-position
  (let [ctx (context) engine (j/machine ctx)]
    (try
      (doseq [[a begin end b start stop expected]
              [["aé😀z" 1 3 "é" 0 2 1]
               ["aé😀z" 3 7 "x😀y" 1 5 1]
               ["é" 0 2 "ê" 0 2 0]
               ["aé😀z" 2 8 "" 0 0 1] ; invalid begin repairs to end
               ["aé😀z" 1 2 "é😀z" 0 7 1] ; invalid stop repairs to end
               ["abc" 2 1 "" 0 0 1] ; inverted ranges have zero Nat byte size
               ["abc" s/huge s/huge "" 0 0 1]
               ["aé" 1 s/huge "é" 0 2 1] ; repair huge end, unlike legacy extract
               ["aé" s/huge 0 "" 0 0 1]
               ["a\u0000b" 1 2 "\u0000" 0 1 1]
               ["😀" 1 3 "" 0 0 1]]]
        (let [x (substring ctx engine a begin end) y (substring ctx engine b start stop)
              before (counters engine)]
          (is (= expected (compare-substrings ctx engine x y)))
          (is (= [0 0 0 2] (mapv - (counters engine) before)))
          (is (host/private-value x "dead")) (is (host/private-value y "dead"))))
      (finally (j/close! ctx engine)))))

(deftest substring-sharing-persistence-aliases-and-fork-obey-owned-container-credits
  (let [ctx (context) engine (j/machine ctx) x (substring ctx engine "é" 0 2)]
    (j/retain! ctx engine x)
    (let [fork (j/fork! ctx engine [x x]) child (:engine fork) [a b] (:roots fork)]
      (try
        (is (identical? a b)) (is (not (identical? x a)))
        (is (= 2 (c/rc ctx x) (c/rc ctx a)))
        (is (= 1 (compare-substrings ctx engine x x)))
        (is (= 1 (compare-substrings ctx child a b)))
        (is (host/private-value x "dead")) (is (host/private-value a "dead"))
        (finally (j/close! ctx engine) (j/close! ctx child)))))
  (doseq [persistent? [false true]]
    (let [ctx (context) engine (j/machine ctx)
          x (substring ctx engine "aé" 1 3) y (substring ctx engine "é" 0 2)]
      (if persistent? (.setInt ^java.lang.reflect.Field (:rc ctx) x 0) (j/retain! ctx engine x))
      (try
        (is (= 1 (compare-substrings ctx engine x y)))
        (is (= (if persistent? 0 1) (c/rc ctx x)))
        (is (false? (host/private-value x "dead")))
        (when-not persistent? (j/release! ctx engine x))
        (finally (j/close! ctx engine))))))

(deftest malformed-second-substring-does-not-consume-valid-first-owner
  (doseq [fields [["x" -1 1] ["x" 0 "bad"] [0 0 0]]]
    (let [ctx (context) engine (j/machine ctx)
          x (substring ctx engine "é" 0 2)
          y (apply substring ctx engine fields) before (counters engine)]
      (is (not= "NO ERROR" (c/failure #(compare-substrings ctx engine x y))))
      (is (= before (counters engine)))
      (is (= 1 (c/rc ctx x) (c/rc ctx y)))
      (is (false? (host/private-value x "dead")))
      (is (false? (host/private-value y "dead")))
      (close-after-failure ctx engine))))

(deftest posof-and-offsetofpos-follow-utf8-not-utf16
  (let [ctx (context) engine (j/machine ctx)]
    (try
      (doseq [[text cp expected] [["aé😀\u0000é" 233 1] ["aé😀" 128512 3]
                                  ["a\u0000b" 0 1] ["é" 65 2] ["" 65 0]]]
        (is (= expected (s/invoke ctx engine "String.Internal.posOf" [text cp]))))
      (doseq [[position expected] [[0 0] [1 1] [2 2] [3 2] [4 3] [5 3] [6 3] [7 3] [8 4] [99 4] [s/huge 4]]]
        (is (= expected (s/invoke ctx engine "String.Internal.offsetOfPos" ["aé😀z" position]))))
      (is (= 0 (s/invoke ctx engine "String.Internal.offsetOfPos" ["" s/huge])))
      (finally (j/close! ctx engine)))))

(deftest pushn-preserves-scalars-zero-transfer-and-bounded-allocation
  (let [ctx (context) engine (j/machine ctx) original (String. "é😀")]
    (try
      (is (identical? original (s/invoke ctx engine "String.Internal.pushn" [original 65 0])))
      (doseq [[text cp n expected] [["a" 233 3 "aééé"] ["" 128512 2 "😀😀"] ["x" 0 2 "x\u0000\u0000"]]]
        (is (= expected (s/invoke ctx engine "String.Internal.pushn" [text cp n]))))
      (finally (j/close! ctx engine))))
  (doseq [[label args] [["String.Internal.pushn" ["x" 65 s/huge]]
                        ["String.Internal.pushn" ["" 65 16777217]]
                        ["String.Internal.pushn" ["" 128512 4194305]]
                        ["String.Internal.pushn" ["" 0xd800 0]]
                        ["String.Internal.pushn" ["" 65 -1]]
                        ["String.Internal.posOf" ["x" 0x110000]]
                        ["String.Internal.offsetOfPos" ["x" -1]]]]
    (let [ctx (context) engine (j/machine ctx) before (counters engine)]
      (is (not= "NO ERROR" (c/failure #(s/invoke ctx engine label args))))
      (is (= before (counters engine)))
      (close-after-failure ctx engine))))

(defn check! [basis] (binding [*basis* basis] (run-tests 'java-ir-string-completion-checks)))
