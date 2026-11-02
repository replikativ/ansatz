(ns java-ir-f32-checks
  "Binary32 transport/layout only; does not implement the Float32 extern family."
  (:require [clojure.test :refer [deftest is run-tests]]
            [java-ir-baseline :as j] [java-ir-baseline-checks :as c]
            [java-ir-extern-checks :as x] [java-ir-generation-checks :as g]
            [java-ir-host-checks :as host] [java-ir-header-checks :as h]
            [java-ir-code-checks :as code]))
(def ^:dynamic *basis* nil)
(def words [0 2147483648 1 8388607 8388608 1065353216 2139095039
            2139095040 4286578688 2143289345 2139095041 4290772993])
(defn as-float [n] (Float/intBitsToFloat (unchecked-int n)))
(defn word [x] (Integer/toUnsignedLong (Float/floatToRawIntBits x)))
(defn raw-through [target]
  (c/decl "raw32" [(c/p 1 "uint32")] "uint32"
    (c/let-ir 2 "object" (c/ctor 0 [] 4)
      ["sset" {:idx 2} 0 0 {:idx 1} "uint32"
       (c/let-ir 3 "float32" {:unbox {:x {:idx 2}}}
         ["dec" {:idx 2} 1 true false
          (c/let-ir 4 "float32" (c/fap target [(c/v 3)])
            (c/let-ir 5 "object" {:box {:ty "float32" :x {:idx 4}}}
              (c/let-ir 6 "uint32" {:sproj {:x {:idx 5} :n 0 :offset 0}}
                ["dec" {:idx 5} 1 true false (c/ret 6)])))])])))
(def identity-row (c/decl "f32-id" [(c/p 1 "float32")] "float32" (c/ret 1)))
(defn context [rows] (j/prepare-host-program *basis* (x/raw rows) []))
(deftest raw-words-boxing-and-static-calls-preserve-all-bits
  (let [ctx (context [identity-row (raw-through "f32-id")]) e (j/machine ctx)]
    (try
      (doseq [n words] (is (= n (j/call ctx e "raw32" [n]))))
      (doseq [n words] (is (= n (word (j/call ctx e "f32-id" [(as-float n)])))))
      (finally (j/close! ctx e)))))
(deftest float32-is-distinct-from-binary64-integer-and-object-lanes
  (let [ctx (context [identity-row (c/decl "obj" [(c/p 1 "object")] "object" (c/ret 1))]) e (j/machine ctx)]
    (try
      (doseq [x [0 1.0 nil (biginteger 1)]] (is (g/bad? #(j/call ctx e "f32-id" [x]))))
      (is (g/bad? #(j/call ctx e "obj" [(as-float 0)])))
      (is (g/bad? #(context [identity-row (c/decl "mixed" [(c/p 1 "float")] "float32"
                                           (c/let-ir 2 "float32" (c/fap "f32-id" [(c/v 1)]) (c/ret 2)))])))
      (is (g/bad? #(context [(c/decl "switch" [(c/p 1 "float32")] "float32"
                              ["case" (c/name-ir "Float32") {:idx 1} "float32" [["default" (c/ret 1)]]])])))
      (finally (j/close! ctx e)))))
(deftest joins-literals-and-pure-nullary-cache-use-binary32
  (let [join (c/decl "join32" [(c/p 1 "float32")] "float32"
               ["jdecl" {:idx 2} [(c/p 3 "float32")] (c/ret 3) ["jmp" {:idx 2} [(c/v 1)]]])
        literal (c/decl "literal32" [] "float32" (c/let-ir 1 "float32" (c/lit 16777217) (c/ret 1)))
        ctx (context [join literal]) e (j/machine ctx)]
    (try
      (doseq [n words] (is (= n (word (j/call ctx e "join32" [(as-float n)])))))
      (is (= (float 16777216) (j/call ctx e "literal32" []) (j/call ctx e "literal32" [])))
      (finally (j/close! ctx e)))))
(deftest scalar-payload-uses-four-bytes-at-byte-offset
  (let [row (c/decl "packed32" [(c/p 1 "float32")] "float32"
              (c/let-ir 2 "object" (c/ctor 0 ["erased"] 5)
                ["sset" {:idx 2} 1 1 {:idx 1} "float32"
                 (c/let-ir 3 "float32" {:sproj {:x {:idx 2} :n 1 :offset 1}}
                   ["dec" {:idx 2} 1 true false (c/ret 3)])]))
        ctx (context [row]) e (j/machine ctx)]
    (try (doseq [n words] (is (= n (word (j/call ctx e "packed32" [(as-float n)])))))
         (finally (j/close! ctx e)))))
(deftest deferred-code-and-fork-preserve-signaling-payload
  (let [base (j/prepare-host-program (assoc *basis* :explicit true) [] [])
        binding (j/source-binding base (Object.)) caller (raw-through "f32-id")
        ch (h/header binding identity-row) rh (h/header binding caller)
        ctx (code/materialize (j/register-headers base [ch rh]) rh caller [ch])
        ready (code/materialize ctx ch identity-row []) e (j/machine ctx)]
    (try
      (j/start! ctx e "raw32" [2139095041])
      (let [request (code/request! ctx e) child (:engine (j/fork! ctx e []))]
        (try
          (is (instance? Float (first (vec (j/request-value request "arguments")))))
          (j/resume-code! ready e request)
          (j/resume-code! ready child (j/code-request ready child))
          (is (= 2139095041 (code/finish! ready e) (code/finish! ready child)))
          (finally (j/close! ready child))))
      (finally (j/close! ready e)))))
(deftest host-views-replies-and-fork-keep-the-float32-lane
  (let [spec (host/spec "research_f32" ["float32"] [false] "float32")
        ctx (j/prepare-host-program (assoc *basis* :explicit true)
              (x/raw [(host/ext "host32" spec) (raw-through "host32")]) [spec]) e (j/machine ctx)]
    (try
      (j/start! ctx e "raw32" [2139095041])
      (let [request (host/request! ctx e) child (:engine (j/fork! ctx e []))]
        (try
          (is (instance? Float (first (host/args request))))
          (doseq [bad [0 1.0 nil]] (is (g/bad? #(j/resume-host! ctx e request bad))))
          (j/resume-host! ctx e request (as-float 2147483648))
          (j/resume-host! ctx child (j/host-request ctx child) (as-float 1))
          (is (= 2147483648 (host/finish! ctx e)))
          (is (= 1 (host/finish! ctx child)))
          (finally (j/close! ctx child))))
      (finally (j/close! ctx e)))))
(defn check! [basis] (binding [*basis* basis] (run-tests 'java-ir-f32-checks)))
