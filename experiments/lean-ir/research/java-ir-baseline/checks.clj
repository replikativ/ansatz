(ns java-ir-baseline-checks
  (:require [clojure.test :refer [deftest is run-tests]]
            [clojure.data.json :as json]
            [java-ir-baseline :as j]
            [prototype.import-ir :as ir]
            [prototype.machine :as m]
            [prototype.unchanged-program-benchmark :as benchmark])
  (:import [java.lang.reflect Method Field]))

(def ^:dynamic *basis* nil)
(defn name-ir [s] ["str" ["anonymous"] s])
(defn v [id] {:var {:id {:idx id}}})
(defn p [id ty] {:x {:idx id} :ty ty :borrow false})
(defn decl [label params type body]
  {:kind "decl" :name (name-ir label)
   :ir {:fdecl {:f (name-ir label) :xs params :type type :body body}}})
(defn let-ir [id type expr cont] ["vdecl" {:idx id} type expr cont])
(defn ret [id] ["ret" (v id)])
(defn fap [s args] {:fap {:c (name-ir s) :ys args}})
(defn lit [n] {:lit {:v {:num {:v n}}}})
(defn ctor [tag fields scalar-bytes]
  {:ctor {:i {:name (name-ir "C") :cidx tag :size (count fields) :usize 0 :ssize scalar-bytes} :ys fields}})
(defn prepare [rows]
  (assoc *basis* :program (j/invoke-static (:prepare *basis*) [(json/read-str (json/write-str rows))])))
(defn rc [basis value] (.getInt ^Field (:rc basis) value))
(defn failure [f]
  (try (f) "NO ERROR"
       (catch Throwable t
         (loop [t t] (if-let [cause (ex-cause t)] (recur cause) (ex-message t))))))
(defn object-constant [label]
  (decl label [] "object" (let-ir 1 "object" (ctor 7 [] 1) (ret 1))))

(deftest constant-ownership-is-borrowed-internally
  (let [ctx (prepare [(object-constant "constant")
                      (decl "shared" [(p 1 "uint8")] "uint8"
                            (let-ir 2 "object" (fap "constant" [])
                              (let-ir 3 "uint8" {:isShared {:x {:idx 2}}} (ret 3))))])
        engine (j/machine ctx)]
    (try
      ;; The cache owns one reference; the internal IR read acquires none.
      (is (= 0 (j/call ctx engine "shared" [0])))
      (let [root (j/call ctx engine "constant" [])]
        (is (= 2 (rc ctx root)))
        (is (= 1 (j/call ctx engine "shared" [0])))
        (j/release! ctx engine root)
        (is (= 1 (rc ctx root)))
        (dotimes [_ 20] (is (= 0 (j/call ctx engine "shared" [0]))))
        (j/close! ctx engine)
        (is (= 0 (rc ctx root)))
        (is (re-find #"live object" (failure #(j/retain! ctx engine root)))))
      (finally (j/close! ctx engine)))))

(deftest packed-scalar-addresses-retain-word-index
  (let [ctx (prepare [(decl "byte" [] "uint8"
                           (let-ir 1 "object" (ctor 4 ["erased"] 12)
                             (let-ir 2 "uint8" (lit 255)
                               ["sset" {:idx 1} 2 1 {:idx 2} "uint8"
                                (let-ir 3 "uint8" {:sproj {:x {:idx 1} :n 2 :offset 1}}
                                  ["dec" {:idx 1} 1 true false (ret 3)])])))])
        engine (j/machine ctx)]
    (try (is (= 255 (j/call ctx engine "byte" [])))
         (is (= 255 (j/call ctx engine "byte" [])))
         (finally (j/close! ctx engine)))))

(deftest shell-delete-transfers-children-without-releasing
  (let [ctx (prepare [(object-constant "child")
                      (decl "parent" [(p 1 "object")] "object"
                            (let-ir 2 "object" (ctor 8 [(v 1)] 0) (ret 2)))
                      (decl "unpack" [(p 1 "object")] "object"
                            (let-ir 2 "object" {:proj {:x {:idx 1} :i 0}}
                              ["del" {:idx 1} (ret 2)]))])
        engine (j/machine ctx)]
    (try
      (let [child (j/call ctx engine "child" [])
            parent (j/call ctx engine "parent" [child])
            restored (j/call ctx engine "unpack" [parent])]
        (is (identical? child restored))
        (is (= 2 (rc ctx child)))
        (is (re-find #"live object" (failure #(j/retain! ctx engine parent))))
        (j/release! ctx engine restored)
        (is (= 1 (rc ctx child))))
      (finally (j/close! ctx engine)))))

(deftest partial-shared-and-overapplication
  (let [ctx (prepare [(decl "id" [(p 1 "object")] "object" (ret 1))
                      (decl "second" [(p 1 "object") (p 2 "object")] "object"
                            ["dec" {:idx 1} 1 true false (ret 2)])
                      (decl "closure" [(p 1 "object")] "object"
                            (let-ir 2 "object" {:pap {:c (name-ir "second") :ys [(v 1)]}} (ret 2)))
                      (decl "apply" [(p 1 "object") (p 2 "object")] "object"
                            (let-ir 3 "object" {:ap {:x {:idx 1} :ys [(v 2)]}} (ret 3)))
                      (decl "return-id" [(p 1 "object")] "object"
                            ["dec" {:idx 1} 1 true false
                             (let-ir 2 "object" {:pap {:c (name-ir "id") :ys []}} (ret 2))])
                      (decl "over" [(p 1 "object") (p 2 "object")] "object"
                            (let-ir 3 "object" {:pap {:c (name-ir "return-id") :ys []}}
                              (let-ir 4 "object" {:ap {:x {:idx 3} :ys [(v 1) (v 2)]}} (ret 4))))
                      (object-constant "value")])
        engine (j/machine ctx)]
    (try
      (let [value (j/call ctx engine "value" [])
            closure (j/call ctx engine "closure" [value])]
        (j/retain! ctx engine closure)
        (is (= 42 (j/call ctx engine "apply" [closure 42])))
        (is (= 1 (rc ctx closure)))
        (is (= 2 (rc ctx value)))
        (is (= 43 (j/call ctx engine "apply" [closure 43])))
        (is (= 1 (rc ctx value))))
      (is (= 99 (j/call ctx engine "over" [10 99])))
      (let [foreign (prepare [(decl "apply" [(p 1 "object") (p 2 "object")] "object"
                                   (let-ir 3 "object" {:ap {:x {:idx 1} :ys [(v 2)]}} (ret 3)))])
            other (j/machine foreign) closure (j/call ctx engine "closure" [10])]
        (try
          (is (re-find #"another code image" (failure #(j/call foreign other "apply" [closure 42]))))
          (finally (j/release! ctx engine closure) (j/close! foreign other))))
      (finally (j/close! ctx engine)))))

(deftest nat-intrinsics-promote-and-preserve-zero-rules
  (let [ctx (j/open-program *basis* "test/fixtures/unchanged-programs/rbmap.jsonl")
        engine (j/machine ctx)]
    (try
      (doseq [[label a b answer] [["Nat.add" Long/MAX_VALUE 1 9223372036854775808N]
                                ["Nat.add" 9223372036854775808N 2 9223372036854775810N]
                                ["Nat.sub" 1 2 0] ["Nat.mod" 23 0 23]
                                ["Nat.mod" 9223372036854775808N 0 9223372036854775808N]
                                ["Nat.decEq" 20 20 1] ["Nat.decLt" 20 22 1]]]
        (let [args (mapv #(if (instance? clojure.lang.BigInt %) (.toBigInteger ^clojure.lang.BigInt %) %) [a b])]
          (is (= answer (j/call ctx engine label args)))))
      (is (re-find #"Invalid Nat" (failure #(j/call ctx engine "Nat.add" [-1 2]))))
      (finally (j/close! ctx engine)))))

(deftest preparation-rejects-unsupported-and-invalid-lanes
  (doseq [rows [[(decl "bad" [(p 0 "object")] "object" (ret 0))]
                [(decl "bad" [(p 1 "object") (p 1 "object")] "object" (ret 1))]
                [(decl "bad" [(p 1.5 "object")] "object" (ret 1))]
                [(decl "bad" [(p 18446744073709551617N "object")] "object" (ret 1))]
                [(decl "bad" [(p 1 "float32")] "float" (ret 1))]
                [(decl "bad" [] "object" (let-ir 1 "uint8" (ctor 0 [] 0) (ret 1)))]
                [(decl "bad" [] "object" (let-ir 1 "object" (lit 1) (ret 2)))]
                [(decl "bad" [] "uint8" (let-ir 1 "uint8" (lit 256) (ret 1)))]
                [(decl "bad" [(p 1 "object")] "object" (let-ir 2 "object" (fap "bad" []) (ret 2)))]
                [(decl "bad" [(p 1 "float")] "float32"
                       ["jdecl" {:idx 3} [(p 2 "float32")] (ret 2) ["jmp" {:idx 3} [(v 1)]]])]]]
    (is (not= "NO ERROR" (failure #(prepare rows)))))
  (let [ctx (prepare [(object-constant "value")]) engine (j/machine ctx)]
    (try (is (re-find #"Arity" (failure #(j/call ctx engine "value" [1]))))
         (finally (j/close! ctx engine)))
    (is (re-find #"closed" (failure #(j/call ctx engine "value" []))))))

(deftest self-tail-permutation-and-stack-growth
  (let [externs (filter #(and (= "decl" (get % "kind"))
                             (contains? #{"Nat.sub" "Nat.decEq"} (ir/name-label (get % "name"))))
                       (j/rows "test/fixtures/unchanged-programs/rbmap.jsonl"))
        definitions [(decl "rotate" [(p 1025 "object") (p 1026 "uint8") (p 1027 "uint8")] "uint8"
                           (let-ir 1028 "object" (lit 0)
                             (let-ir 1029 "uint8" {:fap {:c ["str" (name-ir "Nat") "decEq"] :ys [(v 1025) (v 1028)]}}
                               ["case" (name-ir "Bool") {:idx 1029} "uint8"
                                [["ctor" {:cidx 1} (ret 1026)]
                                 ["ctor" {:cidx 0}
                                  (let-ir 1030 "object" (lit 1)
                                    (let-ir 1031 "object" {:fap {:c ["str" (name-ir "Nat") "sub"] :ys [(v 1025) (v 1030)]}}
                                      (let-ir 1032 "uint8" (fap "rotate" [(v 1031) (v 1027) (v 1026)]) (ret 1032))))]]])))
                     (decl "wide-join" [(p 1 "uint8")] "uint8"
                           ["jdecl" {:idx 300} [(p 1025 "uint8")] (ret 1025) ["jmp" {:idx 300} [(v 1)]]])]
        ctx (prepare (into (vec externs) definitions)) engine (j/machine ctx)]
    (try
      (doseq [n [0 1 2 3 1000 1001]]
        (is (= (if (even? n) 7 9) (j/call ctx engine "rotate" [n 7 9]))))
      (is (= 17 (j/call ctx engine "wide-join" [17])))
      (doseq [bad [-1 256 1.5 18446744073709551617N]]
        (is (not= "NO ERROR" (failure #(j/call ctx engine "wide-join" [bad])))))
      ;; Failed external argument validation must not publish a stack frame.
      (is (= 19 (j/call ctx engine "wide-join" [19])))
      (finally (j/close! ctx engine)))))

(deftest rbmap-intermediate-tree-and-completed-results
  (let [ctx (j/open-program *basis* "test/fixtures/unchanged-programs/rbmap.jsonl")
        reference (benchmark/setup "test/fixtures/unchanged-programs/rbmap.jsonl"
                                   ["mkMap" "fold._redArg" "main._closed_0"])
        [make fold callback] (:names reference)
        seed (m/run (m/start (m/world (:functions reference)) callback []) 10000)]
    (doseq [n [0 1 11 100 300 1000]
            :let [engine (j/machine ctx)]]
      (try
        (let [tree-world (m/run (m/start seed make [n]) 2000000)
              completed (m/run (m/start tree-world fold [(:result seed) (:result tree-world) 0]) 2000000)
              tree (j/call ctx engine "mkMap" [n])
              cb (j/call ctx engine "main._closed_0" [])]
          (is (= (j/reference-value tree-world (:result tree-world)) (j/java-value ctx tree)))
          (is (= (quot (+ n 9) 10) (j/call ctx engine "fold._redArg" [cb tree 0])))
          (is (= (get-in completed [:stats :allocations])
                 (.getLong (.getField ^Class (:class ctx) "allocations") engine)))
          (is (= (get-in completed [:stats :field-stores])
                 (.getLong (.getField ^Class (:class ctx) "stores") engine))))
        (finally (j/close! ctx engine))))))

(deftest mcmc-constant-data-all-declarations
  (let [path "test/fixtures/unchanged-programs/compiler-ir.jsonl"
        ctx (j/open-program *basis* path)
        labels (mapv #(get % "name") (filter #(= "decl" (get % "kind")) (j/rows path)))
        reference (benchmark/setup path (mapv ir/name-label labels))
        engine (j/machine ctx)]
    (try
      (is (= 81 (count labels)))
      (doseq [entry labels]
        (let [world (m/run (m/start (m/world (:functions reference)) entry []) 100000)
              expected (j/reference-value world (:result world))]
          (doseq [_ (range 2)]
            (let [value (j/call ctx engine (ir/name-label entry) [])]
              (is (= expected (j/java-value ctx value)) (ir/name-label entry))
              (j/release! ctx engine value)))))
      (finally (j/close! ctx engine)))))

(defn check! [basis]
  (binding [*basis* basis] (run-tests 'java-ir-baseline-checks)))
