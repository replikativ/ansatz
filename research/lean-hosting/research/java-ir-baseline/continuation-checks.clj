(ns java-ir-continuation-checks
  (:require [clojure.test :refer [deftest is run-tests]]
            [java-ir-baseline :as j]
            [java-ir-baseline-checks :as c])
  (:import [java.lang.reflect Field]))

(def ^:dynamic *basis* nil)
(defn prepare [rows]
  (binding [c/*basis* (assoc *basis* :explicit true)] (c/prepare rows)))
(defn counters [ctx engine]
  (into {} (for [field ["allocations" "stores" "retains" "releases" "shellDeletes"]]
             [field (.getLong (.getField ^Class (:class ctx) field) engine)])))
(defn finish! [ctx engine slices]
  (loop [budgets (cycle slices) attempts 0]
    (assert (< attempts 1000000) "Continuation test did not terminate")
    (if (j/advance! ctx engine (first budgets))
      (j/take-result! ctx engine)
      (recur (rest budgets) (inc attempts)))))
(defn bind-ir [id type expr] ["vdecl" {:idx id} type expr])
(defn linear [prefix terminal] (reduce (fn [tail form] (conj form tail)) terminal (reverse prefix)))

(defn mixed-program []
  [(c/object-constant "child")
   (c/object-constant "object-leaf")
   (c/decl "object-constant" [] "object"
           (c/let-ir 1 "object" (c/fap "object-leaf" [])
             ["inc" {:idx 1} 1 true true (c/ret 1)]))
   (c/decl "byte-leaf" [] "uint8" (c/let-ir 1 "uint8" (c/lit 13) (c/ret 1)))
   (c/decl "byte-constant" [] "uint8" (c/let-ir 1 "uint8" (c/fap "byte-leaf" []) (c/ret 1)))
   (c/decl "third" [(c/p 1 "object") (c/p 2 "object") (c/p 3 "object")] "object"
           ["dec" {:idx 1} 1 true false ["dec" {:idx 2} 1 true false (c/ret 3)]])
   (c/decl "scalar" [(c/p 1 "object")] "uint8"
           ["dec" {:idx 1} 1 true false (c/let-ir 2 "uint8" (c/lit 21) (c/ret 2))])
   (c/decl "id" [(c/p 1 "object")] "object" (c/ret 1))
   (c/decl "return-id" [(c/p 1 "object")] "object"
           ["dec" {:idx 1} 1 true false
            (c/let-ir 2 "object" {:pap {:c (c/name-ir "id") :ys []}} (c/ret 2))])
   (c/decl "return-curried" [(c/p 1 "object")] "object"
           ["dec" {:idx 1} 1 true false
            (c/let-ir 2 "object" {:pap {:c (c/name-ir "return-id") :ys []}} (c/ret 2))])
   (c/decl "bridge" [(c/p 1 "object")] "object"
           (linear [(bind-ir 2 "object" (c/fap "object-constant" []))
                    ["inc" {:idx 2} 1 true false]
                    (bind-ir 3 "uint8" (c/fap "byte-constant" []))
                    (bind-ir 4 "object" {:box {:ty "uint8" :x {:idx 3}}})
                    (bind-ir 5 "object" {:pap {:c (c/name-ir "third") :ys []}})
                    (bind-ir 6 "object" {:ap {:x {:idx 5} :ys [(c/v 2)]}})
                    (bind-ir 7 "object" {:ap {:x {:idx 6} :ys [(c/v 4)]}})
                    (bind-ir 8 "object" {:ap {:x {:idx 7} :ys [(c/v 1)]}})
                    (bind-ir 9 "object" {:pap {:c (c/name-ir "scalar") :ys []}})
                    (bind-ir 10 "object" {:ap {:x {:idx 9} :ys [(c/v 4)]}})
                    (bind-ir 11 "object" {:pap {:c (c/name-ir "return-curried") :ys []}})
                    (bind-ir 12 "object" (c/lit 42))
                    (bind-ir 13 "object" {:ap {:x {:idx 11} :ys [(c/v 10) (c/v 8) (c/v 12)]}})]
                   (c/ret 13)))])

(defn warm! [ctx engine warm?]
  (when warm?
    (let [child (j/call ctx engine "child" [])]
      (assert (= 42 (j/call ctx engine "bridge" [child]))))))

(deftest every-prefix-through-constants-and-application-actions
  (let [ctx (prepare (mixed-program))]
    (doseq [warm? [false true]
            :let [reference (j/machine (dissoc ctx :explicit))
                  _ (warm! ctx reference warm?)
                  reference-child (j/call ctx reference "child" [])
                  answer (j/call ctx reference "bridge" [reference-child])
                  expected (counters ctx reference)
                  probe (j/machine ctx)
                  _ (warm! ctx probe warm?)
                  child (j/call ctx probe "child" [])
                  _ (j/start! ctx probe "bridge" [child])
                  _ (finish! ctx probe [1])
                  total (j/instructions ctx probe)]]
      (try
        (is (= 42 answer))
        (doseq [prefix (range (+ total 2))
                :let [engine (j/machine ctx) _ (warm! ctx engine warm?)
                      child (j/call ctx engine "child" [])]]
          (try
            (j/start! ctx engine "bridge" [child])
            (let [complete? (j/advance! ctx engine prefix)
                  charged (j/instructions ctx engine)]
              (is (= (min prefix total) charged))
              (is (= complete? (>= prefix total)))
              (when-not complete?
                (let [before [(j/phase ctx engine) (j/depth ctx engine) (counters ctx engine)]]
                  (is (false? (j/advance! ctx engine 0)))
                  (is (= charged (j/instructions ctx engine)))
                  (is (= before [(j/phase ctx engine) (j/depth ctx engine) (counters ctx engine)]))))
              (is (= answer (if complete? (j/take-result! ctx engine) (finish! ctx engine [1 3 7]))))
              (is (= total (j/instructions ctx engine)))
              (is (= expected (counters ctx engine))))
            (is (= 1 (c/rc ctx child)))
            (is (= "idle" (j/phase ctx engine)))
            (is (= 0 (j/depth ctx engine)))
            (finally (j/close! ctx engine))))
        (finally (j/close! ctx reference) (j/close! ctx probe))))))

(deftest result-transfer-and-paused-lifecycle
  (let [ctx (prepare [(c/object-constant "object")
                      (c/decl "id" [(c/p 1 "object")] "object" (c/ret 1))])
        engine (j/machine ctx)]
    (try
      (j/start! ctx engine "id" [42])
      (is (= "running" (j/phase ctx engine)))
      (is (= 1 (j/depth ctx engine)))
      (is (re-find #"cleanup" (c/failure #(j/close! ctx engine))))
      (is (re-find #"before start" (c/failure #(j/start! ctx engine "id" [7]))))
      (is (re-find #"Negative" (c/failure #(j/advance! ctx engine -1))))
      (is (= 0 (j/instructions ctx engine)))
      (is (true? (j/advance! ctx engine 1)))
      (is (= "complete" (j/phase ctx engine)))
      (is (re-find #"before start" (c/failure #(j/start! ctx engine "id" [7]))))
      (is (= 42 (j/take-result! ctx engine)))
      (is (re-find #"No owned" (c/failure #(j/take-result! ctx engine))))
      (is (re-find #"No resumable" (c/failure #(j/advance! ctx engine 1))))
      (j/start! ctx engine "object" [])
      (let [value (finish! ctx engine [1])]
        (is (= 2 (c/rc ctx value)))
        (j/close! ctx engine)
        (is (= 1 (c/rc ctx value)))
        (j/release! ctx engine value)
        (is (= 0 (c/rc ctx value))))
      (finally (j/close! ctx engine)))))

(deftest close-releases-unclaimed-owned-result
  (let [ctx (prepare [(c/object-constant "object")]) engine (j/machine ctx)]
    (j/start! ctx engine "object" [])
    (is (true? (j/advance! ctx engine 100)))
    (is (= 1 (get (counters ctx engine) "retains")))
    (j/close! ctx engine)
    (is (= 2 (get (counters ctx engine) "releases")))
    (j/close! ctx engine)
    (is (= 2 (get (counters ctx engine) "releases")))
    (is (re-find #"closed" (c/failure #(j/take-result! ctx engine))))))

(deftest failed-execution-cannot-replay-or-silently-close
  (let [ctx (prepare [(c/decl "trap" [(c/p 1 "object")] "object" ["unreachable"])])
        engine (j/machine ctx)]
    ;; No managed objects are supplied/allocated here. General poisoned-run
    ;; ownership cleanup is intentionally outside this experiment.
    (j/start! ctx engine "trap" [0])
    (is (re-find #"Unreachable" (c/failure #(j/advance! ctx engine 1))))
    (is (= "failed" (j/phase ctx engine)))
    (is (= 1 (j/instructions ctx engine)))
    (is (re-find #"No resumable" (c/failure #(j/advance! ctx engine 1))))
    (is (re-find #"No owned" (c/failure #(j/take-result! ctx engine))))
    (is (re-find #"before start" (c/failure #(j/start! ctx engine "trap" [0]))))
    (is (re-find #"cleanup" (c/failure #(j/close! ctx engine))))))

(deftest invalid-start-preserves-idle-state
  (let [externs (filter #(and (= "decl" (get % "kind"))
                             (= "Nat.add" (prototype.import-ir/name-label (get % "name"))))
                       (j/rows "test/fixtures/unchanged-programs/rbmap.jsonl"))
        ctx (prepare (conj (vec externs) (c/decl "byte" [(c/p 1 "uint8")] "uint8" (c/ret 1))))
        engine (j/machine ctx)]
    (try
      (is (= 21 (j/call ctx engine "byte" [21])))
      (doseq [[label args] [["byte" [-1]] ["byte" [256]] ["Nat.add" [-1 2]]]]
        (is (not= "NO ERROR" (c/failure #(j/start! ctx engine label args))))
        (is (= "idle" (j/phase ctx engine)))
        (is (= 1 (j/instructions ctx engine)))
        (is (= 0 (j/depth ctx engine))))
      (finally (j/close! ctx engine)))))

(deftest intrinsic-applications-and-warm-root-completion
  (let [externs (filter #(and (= "decl" (get % "kind"))
                             (= "Nat.add" (prototype.import-ir/name-label (get % "name"))))
                       (j/rows "test/fixtures/unchanged-programs/rbmap.jsonl"))
        defs [(c/object-constant "object")
              (c/decl "add" [(c/p 1 "object") (c/p 2 "object")] "object"
                      (linear [(bind-ir 3 "object" {:pap {:c ["str" (c/name-ir "Nat") "add"] :ys []}})
                               (bind-ir 4 "object" {:ap {:x {:idx 3} :ys [(c/v 1)]}})
                               (bind-ir 5 "object" {:ap {:x {:idx 4} :ys [(c/v 2)]}})]
                              (c/ret 5)))]
        ctx (prepare (into (vec externs) defs)) engine (j/machine ctx)]
    (try
      (j/start! ctx engine "Nat.add" [20 22])
      (is (= "complete" (j/phase ctx engine)))
      (is (= 0 (j/instructions ctx engine)))
      (is (true? (j/advance! ctx engine 0)))
      (is (= 42 (j/take-result! ctx engine)))
      (j/start! ctx engine "add" [20 22])
      (is (= 42 (finish! ctx engine [1])))
      (let [value (j/call ctx engine "object" [])]
        (j/release! ctx engine value)
        (j/start! ctx engine "object" [])
        (is (= "complete" (j/phase ctx engine)))
        (is (= 0 (j/depth ctx engine)))
        (is (= 0 (j/instructions ctx engine)))
        (is (true? (j/advance! ctx engine 0)))
        (is (identical? value (j/take-result! ctx engine)))
        (is (= 2 (c/rc ctx value)))
        (j/release! ctx engine value))
      (finally (j/close! ctx engine)))))

(defn corpus-run [ctx engine n slices]
  (let [call (fn [label args]
               (if (:explicit ctx)
                 (do (j/start! ctx engine label args) (finish! ctx engine slices))
                 (j/call ctx engine label args)))
        cb (call "main._closed_0" [])
        tree (call "mkMap" [n])
        value (j/java-value ctx tree)
        result (call "fold._redArg" [cb tree 0])]
    {:tree value :result result :counters (counters ctx engine)}))

(deftest exported-rbmap-resumes-with-varied-slices
  (let [ctx (assoc (j/open-program *basis* "test/fixtures/unchanged-programs/rbmap.jsonl") :explicit true)]
    (doseq [n [0 11 100 1000]
            :let [reference-ctx (dissoc ctx :explicit) reference (j/machine reference-ctx)
                  expected (corpus-run reference-ctx reference n nil)]]
      (try
        (doseq [slices (if (= n 1000) [[97] [4096]] [[1] [7] [1 3 97]])
                :let [engine (j/machine ctx)]]
          (try
            (is (= expected (corpus-run ctx engine n slices)))
            (is (= "idle" (j/phase ctx engine)))
            (is (= 0 (j/depth ctx engine)))
            (finally (j/close! ctx engine))))
        (finally (j/close! reference-ctx reference))))))

(deftest deep-nontail-calls-use-no-java-guest-stack
  (let [externs (filter #(and (= "decl" (get % "kind"))
                             (contains? #{"Nat.add" "Nat.sub" "Nat.decEq"}
                                        (prototype.import-ir/name-label (get % "name"))))
                       (j/rows "test/fixtures/unchanged-programs/rbmap.jsonl"))
        native-call (fn [label args] {:fap {:c ["str" (c/name-ir "Nat") label] :ys args}})
        recursive (c/decl "count" [(c/p 1 "object")] "object"
                          (c/let-ir 2 "object" (c/lit 0)
                            (c/let-ir 3 "uint8" (native-call "decEq" [(c/v 1) (c/v 2)])
                              ["case" (c/name-ir "Bool") {:idx 3} "uint8"
                               [["ctor" {:cidx 1} (c/ret 2)]
                                ["ctor" {:cidx 0}
                                 (c/let-ir 4 "object" (c/lit 1)
                                   (c/let-ir 5 "object" (native-call "sub" [(c/v 1) (c/v 4)])
                                     (c/let-ir 6 "object" (c/fap "count" [(c/v 5)])
                                       (c/let-ir 7 "object" (native-call "add" [(c/v 6) (c/v 4)]) (c/ret 7)))))]]])))
        ctx (prepare (conj (vec externs) recursive)) engine (j/machine ctx)]
    (try
      (j/start! ctx engine "count" [20000])
      (let [maximum (loop [maximum 0]
                      (if (j/advance! ctx engine 97) maximum
                        (recur (max maximum (j/depth ctx engine)))))]
        (is (> maximum 19000))
        (is (= 20000 (j/take-result! ctx engine)))
        (is (= 160004 (j/instructions ctx engine)))
        (is (= 0 (j/depth ctx engine))))
      (finally (j/close! ctx engine)))))

(defn check! [basis]
  (binding [*basis* basis] (run-tests 'java-ir-continuation-checks)))
