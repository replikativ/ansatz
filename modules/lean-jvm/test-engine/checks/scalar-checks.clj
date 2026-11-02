(ns java-ir-scalar-checks
  (:require [clojure.test :refer [deftest is run-tests]]
            [clojure.edn :as edn]
            [java-ir-baseline :as j]
            [java-ir-baseline-checks :as c]
            [java-ir-extern-checks :as x]
            [lean-compatibility-corpus :as corpus]))

(def ^:dynamic *basis* nil)
(defn prepare [rows] (binding [x/*basis* *basis*] (x/prepare rows)))
(def max-word (biginteger "18446744073709551615"))
(def high-word (biginteger "9223372036854775808"))
(defn scalar-rows []
  (mapv (x/originals) ["USize.ofNat" "USize.ofNatLT" "USize.repr"
                      "UInt32.toNat" "UInt32.decEq" "UInt32.decLe" "System.Platform.getNumBits"]))

(defn wrapped-scalar-rows []
  (let [rows (scalar-rows) originals (x/originals)]
    (into rows
          (concat
            (for [row rows :let [d (get-in row ["ir" "extern"])
                                 label (engine-support.names/name-label (get row "name"))
                                 params (mapv (fn [i p] (c/p (inc i) (get p "ty")))
                                              (range) (get d "xs"))
                                 dest (inc (count params))]]
              (c/decl (str "wrapped-" label) params (get d "type")
                      (c/let-ir dest (get d "type")
                        {:fap {:c (get row "name") :ys (mapv c/v (range 1 dest))}} (c/ret dest))))
            [(c/decl "word-pipeline" [(c/p 1 "object")] "object"
                     (c/let-ir 2 "usize" {:fap {:c (get (originals "USize.ofNat") "name") :ys [(c/v 1)]}}
                       (c/let-ir 3 "object" {:fap {:c (get (originals "USize.repr") "name") :ys [(c/v 2)]}}
                         (c/ret 3))))]))))

(deftest captured-scalar-externs-match-native
  (let [receipt (edn/read-string (slurp "measurements/java-ir-scalar-oracle.edn"))
        ctx (prepare (wrapped-scalar-rows)) engine (j/machine ctx)]
    (try
      (is (= 1 (:schema receipt)))
      (is (zero? (:exit receipt)))
      (is (= "819816b2e0a3bf405af45ae5c7af2491d8f5bee6" (:producer receipt)))
      (is (= (:source-sha256 receipt) (corpus/sha256 (:source receipt))))
      (is (= 64 (j/call ctx engine "System.Platform.getNumBits" [0])))
      (is (= 64 (j/call ctx engine "wrapped-System.Platform.getNumBits" [0])))
      (is (= 11 (count (:usize receipt))))
      (is (= 64 (count (:u32 receipt))))
      (doseq [{:keys [input value repr]} (:usize receipt)]
        (is (= repr (j/call ctx engine "word-pipeline" [(x/nat input)]))))
      (doseq [{:keys [input value repr]} (:usize receipt) prefix ["" "wrapped-"]]
        (let [word (j/call ctx engine (str prefix "USize.ofNat") [(x/nat input)])]
          (is (= (biginteger value) word))
          (is (= repr (j/call ctx engine (str prefix "USize.repr") [word])))
          (when (< (biginteger input) (inc max-word))
            (is (= word (j/call ctx engine (str prefix "USize.ofNatLT") [(x/nat input) 0]))))))
      (doseq [{:keys [x y eq le]} (:u32 receipt) prefix ["" "wrapped-"]]
        (let [x (Long/parseLong x) y (Long/parseLong y)]
          (is (= x (j/call ctx engine (str prefix "UInt32.toNat") [x])))
          (is (= eq (j/call ctx engine (str prefix "UInt32.decEq") [x y])))
          (is (= le (j/call ctx engine (str prefix "UInt32.decLe") [x y])))))
      (finally (j/close! ctx engine)))))

(defn packed-program []
  [(c/object-constant "child")
   (c/decl "pack" [(c/p 1 "object") (c/p 2 "usize") (c/p 3 "usize")
                    (c/p 4 "uint32") (c/p 5 "uint8")] "object"
           (c/let-ir 6 "object" {:ctor {:i {:name (c/name-ir "Mixed") :cidx 7 :size 1 :usize 2 :ssize 12}
                                           :ys [(c/v 1)]}}
             ["uset" {:idx 6} 1 {:idx 2}
              ["uset" {:idx 6} 2 {:idx 3}
               ["sset" {:idx 6} 3 1 {:idx 4} "uint32"
                ["sset" {:idx 6} 4 3 {:idx 5} "uint8" (c/ret 6)]]]]))
   (c/decl "first-word" [(c/p 1 "object")] "usize"
           (c/let-ir 2 "usize" {:uproj {:x {:idx 1} :i 1}}
             ["dec" {:idx 1} 1 true false (c/ret 2)]))
   (c/decl "second-word" [(c/p 1 "object")] "usize"
           (c/let-ir 2 "usize" {:uproj {:x {:idx 1} :i 2}}
             ["dec" {:idx 1} 1 true false (c/ret 2)]))
   (c/decl "u32-field" [(c/p 1 "object")] "uint32"
           (c/let-ir 2 "uint32" {:sproj {:x {:idx 1} :n 3 :offset 1}}
             ["dec" {:idx 1} 1 true false (c/ret 2)]))
   (c/decl "byte-field" [(c/p 1 "object")] "uint8"
           (c/let-ir 2 "uint8" {:sproj {:x {:idx 1} :n 4 :offset 3}}
             ["dec" {:idx 1} 1 true false (c/ret 2)]))])

(deftest mixed-packed-fields-preserve-word-offsets-and-ownership
  (let [ctx (prepare (packed-program)) engine (j/machine ctx)]
    (try
      (let [child (j/call ctx engine "child" [])
            value (j/call ctx engine "pack" [child high-word max-word 4294967295 255])
            view (j/java-value ctx value)]
        (is (= 7 (:tag view)))
        (is (= 28 (count (:scalar-bytes view))))
        (is (= (vec (concat (repeat 7 0) [128] (repeat 8 255) [0]
                           (repeat 4 255) (repeat 6 0) [255])) (:scalar-bytes view)))
        (doseq [[label expected] [["first-word" high-word] ["second-word" max-word]
                                  ["u32-field" 4294967295] ["byte-field" 255]]]
          (j/retain! ctx engine value)
          (is (= expected (j/call ctx engine label [value])))
          (is (= 1 (c/rc ctx value))))
        (j/release! ctx engine value)
        (is (= 1 (c/rc ctx child))))
      (finally (j/close! ctx engine)))))

(defn box-program []
  [(c/decl "box-word" [(c/p 1 "usize")] "object"
           (c/let-ir 2 "object" {:box {:ty "usize" :x {:idx 1}}} (c/ret 2)))
   (c/decl "box-u32" [(c/p 1 "uint32")] "object"
           (c/let-ir 2 "object" {:box {:ty "uint32" :x {:idx 1}}} (c/ret 2)))
   (c/decl "unbox-word" [(c/p 1 "object")] "usize"
           (c/let-ir 2 "usize" {:unbox {:x {:idx 1}}}
             ["dec" {:idx 1} 1 true false (c/ret 2)]))
   (c/decl "word-constant" [] "usize" (c/let-ir 1 "usize" (c/lit max-word) (c/ret 1)))
   (c/decl "word-result" [(c/p 1 "object")] "usize"
           (c/let-ir 2 "usize" (c/fap "word-constant" []) (c/ret 2)))
   (c/decl "word-apply" [] "object"
           (c/let-ir 1 "object" {:pap {:c (c/name-ir "word-result") :ys []}}
             (c/let-ir 2 "object" {:ap {:x {:idx 1} :ys ["erased"]}} (c/ret 2))))])

(deftest boxed-word-shape-and-scalar-constant-caches
  (let [ctx (prepare (box-program)) engine (j/machine ctx)]
    (try
      (doseq [word [0 1 high-word max-word]]
        (let [boxed (j/call ctx engine "box-word" [word]) view (j/java-value ctx boxed)]
          (is (= 0 (:tag view)))
          (is (= [] (:fields view)))
          (is (= 8 (count (:scalar-bytes view))))
          (is (= word (j/call ctx engine "unbox-word" [boxed])))))
      (is (= 4294967295 (j/call ctx engine "box-u32" [4294967295])))
      (dotimes [_ 3]
        (is (= max-word (j/call ctx engine "word-constant" [])))
        (let [boxed (j/call ctx engine "word-apply" [])]
          ;; The nullary object result is cache-owned as well as caller-owned.
          (is (= 2 (c/rc ctx boxed)))
          (is (= max-word (j/call ctx engine "unbox-word" [boxed])))))
      (finally (j/close! ctx engine)))))

(deftest scalar-input-admission-is-unsigned-and-atomic
  (let [ctx (prepare (concat (scalar-rows) (box-program)))]
    (doseq [[label invalid] [["box-word" -1] ["box-word" (inc max-word)]
                             ["box-word" 1.0] ["box-u32" -1] ["box-u32" 4294967296]
                             ["USize.repr" -1] ["UInt32.toNat" 4294967296]]]
      (let [engine (j/machine ctx)]
        (try
          (is (not= "NO ERROR" (c/failure #(j/call ctx engine label [invalid]))))
          (is (= "idle" (j/phase ctx engine)))
          (is (= 17 (j/call ctx engine "UInt32.toNat" [17])))
          (finally (j/close! ctx engine)))))
    (doseq [[type literal] [["uint32" 4294967296] ["usize" (inc max-word)]]]
      (is (not= "NO ERROR"
                (c/failure #(prepare [(c/decl "bad" [] type
                                             (c/let-ir 1 type (c/lit literal) (c/ret 1)))])))))))

(deftest word-lanes-survive-self-tail-calls-and-joins
  (let [originals (x/originals)
        sub-name (get (originals "Nat.sub") "name")
        eq-name (get (originals "Nat.decEq") "name")
        rows [(originals "Nat.sub") (originals "Nat.decEq")
              (c/decl "rotate" [(c/p 1 "object") (c/p 2 "usize") (c/p 3 "usize")] "usize"
                      (c/let-ir 4 "object" (c/lit 0)
                        (c/let-ir 5 "uint8" {:fap {:c eq-name :ys [(c/v 1) (c/v 4)]}}
                          ["case" (c/name-ir "Bool") {:idx 5} "uint8"
                           [["ctor" {:cidx 1} (c/ret 2)]
                            ["ctor" {:cidx 0}
                             (c/let-ir 6 "object" (c/lit 1)
                               (c/let-ir 7 "object" {:fap {:c sub-name :ys [(c/v 1) (c/v 6)]}}
                                 (c/let-ir 8 "usize" (c/fap "rotate" [(c/v 7) (c/v 3) (c/v 2)])
                                   (c/ret 8))))]]])))
              (c/decl "join" [(c/p 1 "usize") (c/p 2 "uint32")] "usize"
                      ["jdecl" {:idx 20} [(c/p 3 "uint32") (c/p 4 "usize")]
                       (c/ret 4) ["jmp" {:idx 20} [(c/v 2) (c/v 1)]]])]
        ctx (prepare rows) engine (j/machine ctx)]
    (try
      (is (= max-word (j/call ctx engine "rotate" [10001 high-word max-word])))
      (is (= high-word (j/call ctx engine "rotate" [10000 high-word max-word])))
      (is (= max-word (j/call ctx engine "join" [max-word 4294967295])))
      (finally (j/close! ctx engine)))))

(deftest scalar-case-and-payload-boundaries-are-explicit
  (let [case-fn (fn [label type]
                  (c/decl label [(c/p 1 type)] "uint8"
                          ["case" (c/name-ir "Case") {:idx 1} type
                           [["ctor" {:cidx 3} (c/let-ir 2 "uint8" (c/lit 1) (c/ret 2))]
                            ["default" (c/let-ir 3 "uint8" (c/lit 0) (c/ret 3))]]]))
        ctx (prepare [(case-fn "case-u32" "uint32") (case-fn "case-word" "usize")
                      (c/decl "bad-word-field" [] "usize"
                              (c/let-ir 1 "object" (c/ctor 0 ["erased"] 8)
                                (c/let-ir 2 "usize" {:uproj {:x {:idx 1} :i 0}} (c/ret 2))))
                      (c/decl "bad-u32-field" [] "uint32"
                              (c/let-ir 1 "object" (c/ctor 0 [] 3)
                                (c/let-ir 2 "uint32" {:sproj {:x {:idx 1} :n 0 :offset 0}} (c/ret 2))))])
        engine (j/machine ctx)]
    (try
      (is (= 1 (j/call ctx engine "case-u32" [3])))
      (is (= 0 (j/call ctx engine "case-u32" [4294967295])))
      (is (= 1 (j/call ctx engine "case-word" [3])))
      (finally (j/close! ctx engine)))
    (doseq [[label args pattern] [["case-word" [4294967299] #"Wide USize case outside execution profile"]
                                  ["bad-word-field" [] #"Scalar field outside payload"]
                                  ["bad-u32-field" [] #"Scalar field outside payload"]]]
      (x/probe-failure! ctx label args pattern))))

(defn check! [basis]
  (binding [*basis* basis] (run-tests 'java-ir-scalar-checks)))
