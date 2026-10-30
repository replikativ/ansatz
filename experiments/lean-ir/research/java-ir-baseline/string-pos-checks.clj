(ns java-ir-string-pos-checks
  "Original proof-carrying String positions, distinct from legacy Raw.set ABI."
  (:require [clojure.test :refer [deftest is run-tests]]
            [clojure.data.json :as json] [clojure.edn :as edn]
            [java-ir-baseline :as j] [java-ir-baseline-checks :as c]
            [java-ir-extern-checks :as x] [java-ir-generation-checks :as g]
            [java-ir-host-checks :as host] [java-ir-string-checks :as s]
            [lean-compatibility-corpus :as corpus]))
(def ^:dynamic *basis* nil)
(def fixture "test/fixtures/java-string-pos-runtime/original-rows.json")
(defn originals [] (json/read-str (slurp fixture)))
(defn rows [] (mapv #(get % "row") (originals)))
(defn record [label] (first (filter #(= label (get % "label")) (originals))))
(defn target [label] (get-in (record label) ["row" "name"]))
(defn context []
  (assoc *basis* :program
    (j/invoke-static (:prepare *basis*)
      [(into (rows) (x/raw
        [(c/decl "apply-two" (mapv #(c/p % "object") [1 2 3]) "object"
           (c/let-ir 4 "object" {:ap {:x {:idx 1} :ys [(c/v 2) (c/v 3)]}} (c/ret 4)))
         (c/decl "set-proof-probe" [(c/p 1 "object") (c/p 2 "object")
                                     (c/p 3 "uint32") (c/p 4 "object")] "object"
           (c/let-ir 5 "object" {:fap {:c (target "String.Pos.set")
                                      :ys (mapv c/v [1 2 3 4])}} (c/ret 5)))]))])))
(defn call [ctx engine label args] (j/call ctx engine (str label "._boxed") args))
(defn counters [engine] (mapv #(host/private-value engine %) ["allocations" "stores" "retains" "releases"]))
(defn close-after-failure [ctx engine]
  (if (= "failed" (j/phase ctx engine))
    (is (re-find #"requires ownership cleanup" (c/failure #(j/close! ctx engine))))
    (j/close! ctx engine)))

(deftest original-position-abis-and-legacy-set-remain-distinct
  (let [manifest (edn/read-string (slurp "test/fixtures/java-string-pos-runtime/provenance.edn"))
        abi (.getMethod ^Class (:class *basis*) "validateExternAbi" (into-array Class [java.util.Map]))]
    (is (= 8 (count (originals))))
    (is (= (:fixture-sha256 manifest) (corpus/sha256 fixture)))
    (doseq [r (originals) :when (get-in r ["row" "ir" "extern"])]
      (is (string? (j/invoke-static abi [(get r "row")]))))
    (let [modern (get (record "String.Pos.set") "row")
          legacy (get (first (filter #(= "String.Pos.Raw.set" (get % "label")) (s/originals))) "row")]
      (is (= "lean_string_utf8_set" (j/invoke-static abi [modern]) (j/invoke-static abi [legacy])))
      (doseq [bad [(assoc-in modern ["ir" "extern" "xs" 1 "borrow"] true)
                   (assoc-in modern ["ir" "extern" "xs" 1 "ty"] "usize")
                   (assoc-in modern ["ir" "extern" "xs" 3 "ty"] "void")]]
        (is (re-find #"Captured extern ABI mismatch" (c/failure #(j/invoke-static abi [bad]))))))))

(deftest real-wrappers-observe-byte-offsets-and-valid-unicode-replacements
  (let [ctx (context) engine (j/machine ctx)]
    (try
      (doseq [text ["ascii" "a\u0000b" "éλ" "aé😀z" "\uE000𐀀😀"]
              :let [chars (vec (.toArray (.codePoints ^String text)))
                    positions (vec (reductions + 0 (map #(alength ^bytes (s/utf8 (String. (Character/toChars (int %))))) chars)))]
              i (range (count chars))
              :let [p (positions i) next (positions (inc i))]]
        (is (= (chars i) (call ctx engine "String.decodeChar" [text p 0])))
        (is (= next (call ctx engine "String.Pos.next" [text p 0])))
        (is (= (String. (Character/toChars (int (chars i))))
               (call ctx engine "String.extract" [text p next])))
        (doseq [cp [0 65 233 0x10000 0x1f600 0x10ffff]
                :let [utf16 (.offsetByCodePoints ^String text 0 i)
                      stop (.offsetByCodePoints ^String text 0 (inc i))
                      expected (str (.substring ^String text 0 utf16)
                                    (String. (Character/toChars (int cp)))
                                    (.substring ^String text stop))]]
          (is (= expected (call ctx engine "String.Pos.set" [text p cp 0])))))
      (is (= "" (call ctx engine "String.extract" ["é😀" 2 2])))
      (is (= "" (call ctx engine "String.extract" ["é😀" 6 0])))
      (finally (j/close! ctx engine)))))

(deftest modern-set-nonend-boundary-and-proof-reject-before-effects
  (doseq [[text p cp proof] [["" 0 65 0] ["é" 2 65 0] ["é" 1 65 0]
                              ["x" Long/MAX_VALUE 65 0] ["x" Long/MIN_VALUE 65 0]
                              ["x" s/huge 65 0] ["x" -1 65 0]
                              ["x" 0 0xd800 0] ["x" 0 0x110000 0]
                              ["x" 0 65 1] ["x" 0 65 "not-proof"]]]
    (let [ctx (context) engine (j/machine ctx) before (counters engine)]
      ;; This probe forwards all four raw lanes to the actual captured extern.
      (is (not= "NO ERROR" (c/failure #(j/call ctx engine "set-proof-probe" [text p cp proof]))))
      (is (= before (counters engine)))
      (close-after-failure ctx engine))))

(deftest fast-get-and-next-validate-erased-proof-and-boundary
  (doseq [label ["String.decodeChar" "String.Pos.next"]
          [text p proof] [["é" 0 1] ["é" 1 0] ["é" 2 0] ["x" Long/MIN_VALUE 0]
                          ["x" s/huge 0]]]
    (let [ctx (context) engine (j/machine ctx) before (counters engine)]
      (is (not= "NO ERROR" (c/failure #(call ctx engine label [text p proof]))))
      (is (= before (counters engine)))
      (close-after-failure ctx engine))))

(deftest modern-set-does-not-consume-invalid-owned-node-positions
  (let [ctx (context) engine (j/machine ctx) source (j/source-binding ctx (Object.))
        [node] (j/install-graph! ctx engine
                 (j/selected-owner-graph ctx source (Object.)
                   [(j/graph-node ctx {:kind :ctor :id 1 :rc 999 :tag 0 :fields [0]})]
                   [] [] [(j/graph-ref ctx 1)])) before (counters engine)]
    (is (not= "NO ERROR" (c/failure #(j/call ctx engine "String.Pos.set" ["x" node 65 0]))))
    (is (= before (counters engine))) (is (= 1 (c/rc ctx node)))
    (is (false? (host/private-value node "dead")))
    (if (= "failed" (j/phase ctx engine)) (close-after-failure ctx engine)
        (do (j/release! ctx engine node) (j/close! ctx engine)))))

(deftest borrowed-fast-position-targets-require-original-owned-wrappers
  (let [ctx (context)]
    (doseq [label ["String.decodeChar" "String.Pos.next" "String.extract"]]
      (let [engine (j/machine ctx)
            pap (c/decl "bad-pap" [] "object"
                  (c/let-ir 1 "object" {:pap {:c (target label) :ys []}} (c/ret 1)))]
        (try
          (is (re-find #"Borrowed String position primitive" (c/failure #(j/call ctx engine label []))))
          (is (re-find #"Borrowed String position primitive" (c/failure #(j/make-closure! ctx engine label []))))
          (is (re-find #"Borrowed String position primitive"
                       (c/failure #(j/invoke-static (:prepare *basis*) [(into (rows) (x/raw [pap]))]))))
          (finally (j/close! ctx engine)))))))

(deftest imported-borrowed-position-closures-reject-before-publication
  (doseq [label ["String.decodeChar" "String.Pos.next" "String.extract"]]
    (let [base (j/prepare-host-program *basis* [] []) source (j/source-binding base (Object.))
          r (record label) h (j/declaration-header source (get r "row") (get r "sha256"))
          ctx (j/register-headers base [h]) engine (j/machine ctx)]
      (try
        (is (re-find #"Borrowed String position primitive|Prepared closure requires boxed result"
                     (c/failure #(j/install-graph! ctx engine
                       (j/prepared-graph ctx source (Object.)
                         [(j/graph-node ctx {:kind :closure :id 1 :target h :fields []})]
                         [] [] [(j/graph-ref ctx 1)])))))
        (is (false? (host/private-value engine "graphInstalled")))
        (is (= [] (j/install-graph! ctx engine (j/prepared-graph ctx source (Object.) [] [] [] []))))
        (finally (j/close! ctx engine))))))

(deftest owning-modern-boxed-pap-forks-with-independent-result-values
  (let [ctx (context) engine (j/machine ctx) text (String. "aé😀z")
        closure (j/make-closure! ctx engine "String.Pos.set._boxed" [text 1])]
    (j/retain! ctx engine closure)
    (let [fork (j/fork! ctx engine [closure closure]) child (:engine fork) [a b] (:roots fork)]
      (try
        (is (identical? a b)) (is (not (identical? closure a)))
        (is (= 2 (c/rc ctx closure) (c/rc ctx a)))
        (is (= "aλ😀z" (j/call ctx engine "apply-two" [closure 955 0])))
        (is (= "aX😀z" (j/call ctx child "apply-two" [a 88 0])))
        (is (= "a😀😀z" (j/call ctx engine "apply-two" [closure 0x1f600 0])))
        (is (= "a\u0000😀z" (j/call ctx child "apply-two" [b 0 0])))
        (is (= "aé😀z" text))
        (is (host/private-value closure "dead")) (is (host/private-value a "dead"))
        (finally (j/close! ctx engine) (j/close! ctx child))))))

(deftest owned-raw-set-entry-is-valid-but-unboxed-closures-are-rejected
  (let [ctx (context) engine (j/machine ctx)
        pap (c/decl "bad-owned-pap" [] "object"
              (c/let-ir 1 "object" {:pap {:c (target "String.Pos.set") :ys []}} (c/ret 1)))]
    (try
      (is (= "aX" (j/call ctx engine "String.Pos.set" ["aé" 1 88 0])))
      (is (re-find #"Unboxed partial target" (c/failure #(j/make-closure! ctx engine "String.Pos.set" []))))
      (is (re-find #"Unboxed partial target" (c/failure #(j/invoke-static (:prepare *basis*) [(into (rows) (x/raw [pap]))]))))
      (finally (j/close! ctx engine))))
  (let [base (j/prepare-host-program *basis* [] []) source (j/source-binding base (Object.))
        r (record "String.Pos.set") h (j/declaration-header source (get r "row") (get r "sha256"))
        ctx (j/register-headers base [h]) engine (j/machine ctx)]
    (try
      (is (re-find #"Prepared closure requires boxed parameters"
                   (c/failure #(j/install-graph! ctx engine
                     (j/prepared-graph ctx source (Object.)
                       [(j/graph-node ctx {:kind :closure :id 1 :target h :fields []})]
                       [] [] [(j/graph-ref ctx 1)])))))
      (is (false? (host/private-value engine "graphInstalled")))
      (finally (j/close! ctx engine)))))

(deftest modern-set-output-cap-rejects-before-runtime-mutation
  (let [ctx (context) engine (j/machine ctx)
        text (String. (char-array 16777216 \a)) before (counters engine)]
    (is (re-find #"String.Pos.set output outside bounded runtime profile"
                 (c/failure #(j/call ctx engine "String.Pos.set" [text 0 0x1f600 0]))))
    (is (= before (counters engine)))
    (is (= 16777216 (.length text))) (is (= \a (.charAt text 0)))
    (close-after-failure ctx engine)))

(defn check! [basis] (binding [*basis* basis] (run-tests 'java-ir-string-pos-checks)))
