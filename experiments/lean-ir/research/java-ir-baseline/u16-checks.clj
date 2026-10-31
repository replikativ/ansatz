(ns java-ir-u16-checks
  "Distinct canonical UInt16 lane; original equality/Nat wrappers and typed transport."
  (:require [clojure.test :refer [deftest is run-tests]] [clojure.data.json :as json]
            [java-ir-baseline :as j] [java-ir-baseline-checks :as c]
            [java-ir-extern-checks :as x] [java-ir-generation-checks :as g]
            [java-ir-host-checks :as host] [java-ir-header-checks :as h]
            [java-ir-code-checks :as code] [java-ir-sync-task-checks :as sync]
            [lean-compatibility-corpus :as corpus]))
(def ^:dynamic *basis* nil)
(def directory "test/fixtures/java-u16-runtime/")
(def values [0 255 256 32767 32768 65535])
(defn originals [] (mapv #(get % "row") (json/read-str (slurp (str directory "original-rows.json")))))
(def helpers
  [(c/decl "u16-id" [(c/p 1 "uint16")] "uint16" (c/ret 1))
   (c/decl "u16-join" [(c/p 1 "uint16")] "uint16"
     ["jdecl" {:idx 2} [(c/p 3 "uint16")] (c/ret 3) ["jmp" {:idx 2} [(c/v 1)]]])
   (c/decl "u16-box" [(c/p 1 "uint16")] "tagged"
     (c/let-ir 2 "tagged" {:box {:ty "uint16" :x {:idx 1}}} (c/ret 2)))
   (c/decl "u16-unbox" [(c/p 1 "object")] "uint16"
     (c/let-ir 2 "uint16" {:unbox {:x {:idx 1}}} (c/ret 2)))
   (c/decl "u16-literal" [] "uint16" (c/let-ir 1 "uint16" (c/lit 65535) (c/ret 1)))
   (c/decl "u16-result" [(c/p 1 "object")] "uint16" (c/let-ir 2 "uint16" (c/lit 65535) (c/ret 2)))
   (c/decl "u16-apply" [(c/p 1 "object") (c/p 2 "object")] "object"
     (c/let-ir 3 "object" {:ap {:x {:idx 1} :ys [(c/v 2)]}} (c/ret 3)))
   (c/decl "u16-partial-eq" [(c/p 1 "object")] "object"
     (c/let-ir 2 "object" {:pap {:c ["str" ["str" ["str" ["anonymous"] "UInt16"] "decEq"] "_boxed"] :ys [(c/v 1)]}} (c/ret 2)))
   (c/decl "u16-case" [(c/p 1 "uint16")] "object"
     ["case" (c/name-ir "UInt16") {:idx 1} "uint16"
      [["ctor" {:cidx 65535} (c/let-ir 2 "object" (c/lit 7) (c/ret 2))]
       ["default" (c/let-ir 3 "object" (c/lit 9) (c/ret 3))]]])
   (c/decl "u16-pack" [(c/p 1 "object") (c/p 2 "uint16") (c/p 3 "uint32")] "object"
     (c/let-ir 4 "object" (c/ctor 3 [(c/v 1)] 8)
       ["sset" {:idx 4} 1 1 {:idx 2} "uint16"
        ["sset" {:idx 4} 1 4 {:idx 3} "uint32" (c/ret 4)]]))
   (c/decl "u16-read" [(c/p 1 "object")] "uint16"
     (c/let-ir 2 "uint16" {:sproj {:x {:idx 1} :n 1 :offset 1}}
       ["dec" {:idx 1} 1 false false (c/ret 2)]))
   (c/decl "u16-write" [(c/p 1 "object") (c/p 2 "uint16")] "object"
     ["sset" {:idx 1} 1 1 {:idx 2} "uint16" (c/ret 1)])])
(defn prepare [rows] (assoc *basis* :program (j/invoke-static (:prepare *basis*) [(x/raw rows)])))
(defn context [] (prepare (concat (originals) helpers)))
(defn counters [e] (mapv #(host/private-value e %) ["allocations" "stores" "retains" "releases" "shellDeletes"]))

(deftest exact-original-fixture-and-native-abis
  (let [p (json/read-str (slurp (str directory "provenance.json")))
        method (.getMethod ^Class (:class *basis*) "validateExternAbi" (into-array Class [java.util.Map]))]
    (is (= 4 (count (originals))))
    (is (= (get p "fixture-sha256") (corpus/sha256 (str directory "original-rows.json"))))
    (doseq [row (take-nth 2 (originals))]
      (is (string? (j/invoke-static method [row])))
      (is (g/bad? #(j/invoke-static method [(assoc-in row ["ir" "extern" "xs" 0 "ty"] "uint32")])))
      (is (g/bad? #(j/invoke-static method [(assoc-in row ["ir" "extern" "xs" 0 "borrow"] true)]))))))

(deftest boundary-raw-boxed-fap-join-case-and-return
  (let [ctx (context) e (j/machine ctx)]
    (try
      (doseq [v values]
        (is (= v (j/call ctx e "u16-id" [v]) (j/call ctx e "u16-join" [v])))
        (is (= v (j/call ctx e "u16-box" [v]) (j/call ctx e "u16-unbox" [v])))
        (is (= v (j/call ctx e "UInt16.toNat" [v]) (j/call ctx e "UInt16.toNat._boxed" [v])))
        (is (= (if (= v 65535) 7 9) (j/call ctx e "u16-case" [v]))))
      (doseq [a values b values]
        (is (= (if (= a b) 1 0) (j/call ctx e "UInt16.decEq" [a b])
               (j/call ctx e "UInt16.decEq._boxed" [a b]))))
      (is (= 65535 (j/call ctx e "u16-literal" []) (j/call ctx e "u16-literal" [])))
      (finally (j/close! ctx e)))))

(deftest genuine-boxed-pap-ap-and-scalar-result-boxing
  (let [ctx (context) e (j/machine ctx)]
    (try
      (doseq [v values]
        (let [partial (j/call ctx e "u16-partial-eq" [v])
              nat (j/make-closure! ctx e "UInt16.toNat._boxed" [])]
          (is (= 1 (j/call ctx e "u16-apply" [partial v])))
          (is (= v (j/call ctx e "u16-apply" [nat v])))))
      (is (= 65535 (j/call ctx e "u16-apply" [(j/make-closure! ctx e "u16-result" []) 0])))
      (is (g/bad? #(j/make-closure! ctx e "UInt16.toNat" [])))
      (finally (j/close! ctx e)))))

(deftest canonical-range-root-and-unbox-reject-without-effects
  (let [ctx (context) e (j/machine ctx)]
    (try
      (doseq [label ["u16-id" "UInt16.toNat"] bad [-1 65536 1.5 nil]]
        (let [before (counters e)]
          (is (g/bad? #(j/call ctx e label [bad])))
          (is (= before (counters e))) (is (= "idle" (j/phase ctx e)))))
      (finally (j/close! ctx e))))
  ;; Unboxing is a guest instruction, so a failure is terminal in explicit mode.
  (doseq [bad [-1 65536]]
    (let [ctx (context) e (j/machine ctx) before (counters e)]
      (is (g/bad? #(j/call ctx e "u16-unbox" [bad]))) (is (= before (counters e)))
      (if (:explicit ctx) (is (g/bad? #(j/close! ctx e))) (j/close! ctx e)))))

(deftest preparation-rejects-wide-literals-float32-and-cross-lane-ir
  (doseq [row [(c/decl "wide16" [] "uint16" (c/let-ir 1 "uint16" (c/lit 65536) (c/ret 1)))
               (c/decl "negative16" [] "uint16" (c/let-ir 1 "uint16" (c/lit -1) (c/ret 1)))
               (c/decl "cross-return" [(c/p 1 "uint32")] "uint16" (c/ret 1))
               (c/decl "f32" [(c/p 1 "float32")] "float32" (c/ret 1))
               (c/decl "cross-call" [(c/p 1 "uint32")] "object"
                 (c/let-ir 2 "object" {:fap {:c (get (nth (originals) 2) "name") :ys [(c/v 1)]}} (c/ret 2)))
               (c/decl "raw-partial" [] "object"
                 (c/let-ir 1 "object" {:pap {:c ["str" ["str" ["anonymous"] "UInt16"] "decEq"] :ys []}} (c/ret 1)))]]
    (is (g/bad? #(prepare (concat (originals) [row]))))))

(deftest two-byte-packed-adjacency-and-exclusive-fork-mutation
  (let [ctx (context) p (j/machine ctx) value (j/call ctx p "u16-pack" [42 65535 4294967295])
        {:keys [engine roots]} (j/fork! ctx p [value]) child engine cv (first roots)]
    (try
      (is (= [0 255 255 0 255 255 255 255]
             (mapv #(bit-and 255 %) (.get ^java.lang.reflect.Field (:scalars ctx) value))))
      (is (identical? cv (j/call ctx child "u16-write" [cv 256])))
      (is (= [0 0 1 0 255 255 255 255]
             (mapv #(bit-and 255 %) (.get ^java.lang.reflect.Field (:scalars ctx) cv))))
      (is (= 65535 (j/call ctx p "u16-read" [value])))
      (is (= 256 (j/call ctx child "u16-read" [cv])))
      (finally (j/close! ctx p) (j/close! ctx child)))))

(deftest two-byte-storage-bounds-do-not-touch-adjacent-memory
  (doseq [[size offset] [[1 0] [2 1] [2 -1]]]
    (let [maker (c/decl "tiny" [(c/p 1 "object")] "object"
                  (c/let-ir 2 "object" (c/ctor 3 [(c/v 1)] size) (c/ret 2)))
          writer (c/decl "bad-write" [(c/p 1 "object") (c/p 2 "uint16")] "object"
                   ["sset" {:idx 1} 1 offset {:idx 2} "uint16" (c/ret 1)])]
      ;; Negative raw offsets may be rejected at preparation; both are fail-closed.
      (if (neg? offset)
        (is (g/bad? #(prepare [maker writer])))
        (let [ctx (prepare [maker writer]) e (j/machine ctx) value (j/call ctx e "tiny" [0]) before (counters e)]
          (is (g/bad? #(j/call ctx e "bad-write" [value 65535])))
          (is (= before (counters e))) (is (= 1 (c/rc ctx value)))
          (is (every? zero? (.get ^java.lang.reflect.Field (:scalars ctx) value)))
          (j/release! ctx e value)
          (if (:explicit ctx) (is (g/bad? #(j/close! ctx e))) (j/close! ctx e)))))))

(deftest metadata-code-request-and-fork-preserve-distinct-u16
  (if-not (:explicit *basis*) (is true)
    (let [row (first helpers) base (j/prepare-host-program *basis* [] [])
          source (j/source-binding base (Object.)) target (h/header source row)
          ctx (j/register-headers base [target]) ready (code/materialize ctx target row []) p (j/machine ctx)]
      (try
        (is (= ["uint16"] (vec (j/request-value target "paramTypes"))))
        (j/start! ctx p "u16-id" [65535])
        (let [request (code/request! ctx p) child (:engine (j/fork! ctx p []))]
          (try
            (is (= [65535] (code/args request)))
            (j/resume-code! ready p request) (j/resume-code! ready child (j/code-request ctx child))
            (is (= 65535 (code/finish! ready p) (code/finish! ready child)))
            (finally (j/close! ready child))))
        (finally (j/close! ready p))))))

(deftest host-u16-preclaim-and-divergent-fork-results
  (if-not (:explicit *basis*) (is true)
    (let [spec (host/spec "research_u16" ["uint16"] [false] "uint16")
          ctx (j/prepare-host-program *basis* (x/raw [(host/ext "u16-host" spec)]) [spec]) p (j/machine ctx)]
      (try
        (j/start! ctx p "u16-host" [65535])
        (let [request (j/host-request ctx p) child (:engine (j/fork! ctx p []))]
          (try
            (is (= [65535] (host/args request)))
            (is (= ["uint16"] (vec (j/request-value request "paramTypes"))))
            (doseq [bad [-1 65536 1.5]]
              (is (g/bad? #(j/resume-host! ctx p request bad)))
              (is (identical? request (j/host-request ctx p))))
            (j/resume-host! ctx p request 32768)
            (j/resume-host! ctx child (j/host-request ctx child) 65535)
            (is (= 32768 (j/take-result! ctx p))) (is (= 65535 (j/take-result! ctx child)))
            (finally (j/close! ctx child))))
        (finally (j/close! ctx p))))))

(deftest active-claimed-host-completion-drains-before-u16-publication-and-forks
  (if-not (:explicit *basis*) (is true)
    (let [spec (host/spec "research_u16_cleanup" ["object"] [true] "uint16")
          maker (c/decl "cons" [(c/p 1 "object")] "object"
                  (c/let-ir 2 "object" (c/ctor 1 [(c/v 1)] 0) (c/ret 2)))
          ctx (sync/active (j/prepare-host-program *basis* (x/raw [(host/ext "u16-cleanup" spec) maker]) [spec]))
          p (j/machine ctx) value (j/call ctx p "cons" [7])]
      (j/start! ctx p "u16-cleanup" [value])
      (j/resume-host! ctx p (j/host-request ctx p) 65535)
      (is (= "running" (j/phase ctx p))) (is (= 1 (c/rc ctx value)))
      (is (true? (host/private-value (host/private-value p "hostCompletion") "replyClaimed")))
      (is (= 65535 (host/private-value (host/private-value p "hostCompletion") "completionScalar")))
      (is (g/bad? #(j/take-result! ctx p)))
      (let [{:keys [engine roots]} (j/fork! ctx p [value]) child engine cv (first roots)]
        (is (= 65535 (sync/finish! ctx p) (sync/finish! ctx child)))
        (is (host/private-value value "dead")) (is (host/private-value cv "dead"))
        (is (nil? (host/private-value p "hostCompletion")))
        (sync/close! ctx p) (sync/close! ctx child)))))
(defn check! [basis] (binding [*basis* basis] (run-tests 'java-ir-u16-checks)))
