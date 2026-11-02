(ns java-ir-logical-sharing-checks
  "Logical MT mark/exclusivity only; no active tasks, scheduler or finalizers."
  (:require [clojure.test :refer [deftest is run-tests]]
            [java-ir-baseline :as j] [java-ir-baseline-checks :as c]
            [java-ir-extern-checks :as x] [java-ir-generation-checks :as g]
            [java-ir-host-checks :as host] [java-ir-ref-checks :as ref]
            [java-ir-array-checks :as array] [java-ir-byte-array-checks :as byte]
            [java-ir-task-map-checks :as task] [java-ir-pointer-checks :as pointer]))
(def ^:dynamic *basis* nil)
(defn private-call [ctx engine method types args]
  (let [m (.getDeclaredMethod ^Class (:class ctx) method (into-array Class types))]
    (.setAccessible m true) (.invoke m engine (object-array args))))
(defn mark! [ctx engine value] (private-call ctx engine "markLogicalMT" [Object] [value]))
(defn mt? [ctx value] (boolean (private-call ctx nil "logicalMT" [(:node-class ctx)] [value])))
(defn exclusive? [ctx value] (boolean (private-call ctx nil "exclusive" [(:node-class ctx)] [value])))
(defn fields [ctx value] (.get ^java.lang.reflect.Field (:fields ctx) value))
(defn metadata [value] (host/private-value value "metadata"))
(defn dead? [value] (host/private-value value "dead"))
(defn context []
  (let [originals (concat (map #(get % "row") (concat (ref/originals) (array/originals) (byte/originals)))
                          task/originals task/task-rows [pointer/pointer pointer/equality])
        originals (vals (into {} (map (juxt #(get % "name") identity) originals)))
        helpers (concat g/common [(pointer/compare-row)
          (c/decl "fresh" [(c/p 1 "object")] "object"
            (c/let-ir 2 "object" (c/ctor 0 [(c/v 1)] 0) (c/ret 2)))
          (c/decl "scalar-ctor" [(c/p 1 "object")] "object"
            (c/let-ir 2 "object" (c/ctor 0 [(c/v 1)] 16) (c/ret 2)))
          (c/decl "keep-first" [(c/p 1 "object") (c/p 2 "object")] "object"
            ["dec" {:idx 2} 1 true false (c/ret 1)])
          (c/decl "observe-shared" [(c/p 1 "object")] "object"
            (c/let-ir 2 "uint8" {:isShared {:x {:idx 1}}}
              (c/let-ir 3 "tobject" {:box {:ty "uint8" :x {:idx 2}}}
                (c/let-ir 4 "object" (c/ctor 0 [(c/v 1) (c/v 3)] 0) (c/ret 4)))))
          (c/decl "project" [(c/p 1 "object")] "object"
            (c/let-ir 2 "object" {:proj {:x {:idx 1} :i 0}} (c/ret 2)))
          (c/decl "set-field" [(c/p 1 "object") (c/p 2 "object")] "object"
            ["set" {:idx 1} 0 (c/v 2) (c/ret 1)])
          (c/decl "set-byte" [(c/p 1 "object") (c/p 2 "uint8")] "object"
            ["sset" {:idx 1} 1 0 {:idx 2} "uint8" (c/ret 1)])
          (c/decl "set-word" [(c/p 1 "object") (c/p 2 "usize")] "object"
            ["uset" {:idx 1} 1 {:idx 2} (c/ret 1)])
          (c/decl "set-tag" [(c/p 1 "object")] "object"
            ["setTag" {:idx 1} 2 (c/ret 1)])
          (c/decl "delete-shell" [(c/p 1 "object")] "object"
            ["del" {:idx 1} (c/let-ir 2 "object" (c/lit 0) (c/ret 2))])
          (c/decl "reset-choice" [(c/p 1 "object")] "object"
            (c/let-ir 2 "uint8" {:isShared {:x {:idx 1}}}
              ["case" (c/name-ir "Bool") {:idx 2} "uint8"
               [["ctor" {:cidx 0} ["del" {:idx 1} (c/let-ir 3 "object" (c/lit 0) (c/ret 3))]]
                ["default" ["dec" {:idx 1} 1 true false
                            (c/let-ir 4 "object" (c/lit 1) (c/ret 4))]]]]))])]
    (assoc *basis* :program (j/invoke-static (:prepare *basis*) [(x/raw (concat originals helpers))]))))
(defn fresh [ctx engine] (j/call ctx engine "fresh" [0]))
(defn shared! [ctx engine value]
  ;; Transfer into an owning result packet, then recover that same credit.
  ;; The isShared instruction observes the original count, before any retain.
  (let [packet (j/call ctx engine "observe-shared" [value])
        result (aget ^objects (fields ctx packet) 1)]
    (j/retain! ctx engine value) (j/release! ctx engine packet) result))
(defn counters [engine] (mapv #(host/private-value engine %) ["allocations" "stores" "retains" "releases" "shellDeletes"]))
(defn close-after-failure [ctx engine]
  (if (= "failed" (j/phase ctx engine)) (is (g/bad? #(j/close! ctx engine)))
      (j/close! ctx engine)))

(deftest private-mark-is-monotone-transitive-and-independent-of-owner-counts
  (let [ctx (context) engine (j/machine ctx) leaf (fresh ctx engine)
        root (j/call ctx engine "fresh" [leaf])]
    (try
      (is (nil? (metadata root))) (is (exclusive? ctx root))
      (is (= 0 (shared! ctx engine root)))
      (let [before (counters engine)]
        (mark! ctx engine root)
        (is (= before (counters engine))))
      (is (mt? ctx root)) (is (mt? ctx leaf))
      (is (= 1 (c/rc ctx root) (c/rc ctx leaf)))
      (is (false? (exclusive? ctx root))) (is (= 1 (shared! ctx engine root)))
      (let [state (metadata root)] (mark! ctx engine root) (is (identical? state (metadata root))))
      (j/retain! ctx engine root) (j/release! ctx engine root)
      (is (= 1 (c/rc ctx root))) (is (= 1 (shared! ctx engine root)))
      (finally (j/release! ctx engine root) (j/close! ctx engine)))
    (is (dead? leaf))))

(deftest persistent-and-already-marked-stops-do-not-infer-sharing-from-source-counts
  (let [ctx (context) engine (j/machine ctx) source (j/source-binding ctx (Object.))
        [cell child] (j/install-graph! ctx engine
                       (j/selected-owner-graph ctx source (Object.)
                         [(j/graph-node ctx {:kind :ref :id 1 :rc 0 :fields [(j/graph-ref ctx 2)]})
                          (j/graph-node ctx {:kind :ctor :id 2 :rc 999 :tag 0 :fields [0]})]
                         [] [] [(j/graph-ref ctx 1) (j/graph-ref ctx 2)]))]
    (try
      (is (= 0 (c/rc ctx cell))) (is (= 2 (c/rc ctx child)))
      (is (false? (mt? ctx child)))
      (mark! ctx engine cell)
      (is (nil? (metadata cell))) (is (false? (mt? ctx child)))
      (is (= 1 (shared! ctx engine cell)))
      (ref/ref-set! ctx engine cell 0)
      (is (= 1 (c/rc ctx child))) (is (exclusive? ctx child))
      (j/release! ctx engine child) (is (dead? child))
      (finally (j/close! ctx engine)))))

(deftest cyclic-owning-graphs-mark-once-and-retain-their-selected-owner-ledger
  (let [ctx (context) engine (j/machine ctx) source (j/source-binding ctx (Object.))
        [root] (j/install-graph! ctx engine
                 (j/selected-owner-graph ctx source (Object.)
                   [(j/graph-node ctx {:kind :ctor :id 1 :rc 99 :tag 0 :fields [(j/graph-ref ctx 2)]})
                    (j/graph-node ctx {:kind :ref :id 2 :rc 99 :fields [(j/graph-ref ctx 1)]})]
                   [] [] [(j/graph-ref ctx 1)])) cell (aget ^objects (fields ctx root) 0)]
    (try
      (is (= [2 1] [(c/rc ctx root) (c/rc ctx cell)]))
      (mark! ctx engine root)
      (is (mt? ctx root)) (is (mt? ctx cell))
      (is (= [2 1] [(c/rc ctx root) (c/rc ctx cell)]))
      (is (false? (exclusive? ctx cell)))
      ;; Break the cycle through the original Ref primitive; no cycle collector.
      (ref/ref-set! ctx engine cell 0)
      (j/release! ctx engine root)
      (is (dead? root)) (is (dead? cell))
      (finally (j/close! ctx engine)))))

(deftest deep-marking-and-release-use-no-java-recursion
  (let [ctx (context) engine (j/machine ctx) leaf (fresh ctx engine)
        root (loop [n 4000 value leaf]
               (if (zero? n) value (recur (dec n) (j/call ctx engine "fresh" [value]))))]
    (try
      (mark! ctx engine root)
      (is (mt? ctx root)) (is (mt? ctx leaf))
      (is (= 1 (c/rc ctx root) (c/rc ctx leaf)))
      (j/release! ctx engine root) (is (dead? leaf))
      (finally (j/close! ctx engine)))))

(deftest persistent-ref-publication-marks-all-supported-owned-node-kinds
  (let [ctx (context) engine (j/machine ctx) source (j/source-binding ctx (Object.))
        [cell] (j/install-graph! ctx engine (j/prepared-graph ctx source (Object.)
                  [(j/graph-node ctx {:kind :ref :id 1 :fields [0]})] [] [] [(j/graph-ref ctx 1)]))
        leaf (fresh ctx engine) closure (j/make-closure! ctx engine "keep-first" [leaf])
        bytes (byte/push! ctx engine (j/call ctx engine "ByteArray.mk._boxed"
                     [(array/push! ctx engine (array/empty! ctx engine 3) 10)]) 20)
        a (array/push! ctx engine (array/push! ctx engine (array/empty! ctx engine 4) closure) bytes)
        ready (task/pure ctx engine a) inner (ref/make-ref! ctx engine ready)
        payload (j/call ctx engine "fresh" [inner]) nodes [payload inner ready a closure bytes leaf]]
    (try
      (is (every? #(not (mt? ctx %)) nodes))
      (is (= 0 (ref/ref-set! ctx engine cell payload)))
      (is (every? #(mt? ctx %) nodes)) (is (every? #(= 1 (c/rc ctx %)) nodes))
      (is (= 2 (array/size a))) (is (= [10 20] (byte/payload ctx bytes)))
      (is (= 1 (shared! ctx engine payload)))
      (let [old (ref/ref-swap! ctx engine cell 0)]
        (is (identical? payload old)) (is (= 1 (c/rc ctx old)))
        (j/release! ctx engine old))
      (is (every? dead? nodes))
      (finally (j/close! ctx engine)))))

(deftest fresh-st-ref-and-shared-st-ref-stores-do-not-mark-incoming-values
  (let [ctx (context) engine (j/machine ctx) cell (ref/make-ref! ctx engine 0)
        payload (fresh ctx engine)]
    (try
      ;; The original owning facade temporarily gives this ST ref two owners.
      (ref/ref-set! ctx engine cell payload)
      (is (false? (mt? ctx cell))) (is (false? (mt? ctx payload)))
      (is (exclusive? ctx payload))
      (let [replacement (fresh ctx engine) old (ref/ref-swap! ctx engine cell replacement)]
        (is (identical? payload old)) (is (false? (mt? ctx replacement)))
        (j/release! ctx engine old))
      (finally (j/release! ctx engine cell) (j/close! ctx engine)))))

(deftest logical-mt-ref-set-and-swap-mark-before-publishing-without-changing-old-owner-transfer
  (let [ctx (context) engine (j/machine ctx) cell (ref/make-ref! ctx engine 0)]
    (try
      (mark! ctx engine cell)
      (let [a (fresh ctx engine) b (fresh ctx engine)]
        (is (= 0 (ref/ref-swap! ctx engine cell a))) (is (mt? ctx a))
        (is (identical? a (ref/ref-swap! ctx engine cell b)))
        (is (= 1 (c/rc ctx a) (c/rc ctx b))) (is (mt? ctx b))
        (j/release! ctx engine a)
        (is (= 0 (ref/ref-set! ctx engine cell 0))) (is (dead? b)))
      (finally (j/release! ctx engine cell) (j/close! ctx engine)))))

(deftest marked-count-one-constructors-refuse-every-unique-mutation-and-del
  (doseq [[label args] [["set-field" [7]] ["set-byte" [8]] ["set-word" [9]]
                         ["set-tag" []] ["delete-shell" []]]]
    (let [ctx (context) engine (j/machine ctx) value (j/call ctx engine "scalar-ctor" [0])]
      (mark! ctx engine value)
      (let [before (counters engine) data (vec (.get ^java.lang.reflect.Field (:scalars ctx) value))]
        (is (re-find #"Expected exclusive object" (c/failure #(j/call ctx engine label (into [value] args)))))
        (is (= before (counters engine))) (is (= 1 (c/rc ctx value)))
        (is (= 0 (.getInt ^java.lang.reflect.Field (:tag ctx) value)))
        (is (= data (vec (.get ^java.lang.reflect.Field (:scalars ctx) value))))
        (is (false? (dead? value))))
      (when-not (:explicit ctx) (j/release! ctx engine value))
      (close-after-failure ctx engine))))

(deftest reset-sharing-branch-selects-dec-instead-of-unique-shell-transfer
  (doseq [marked? [false true]]
    (let [ctx (context) engine (j/machine ctx) value (fresh ctx engine)]
      (try
        (when marked? (mark! ctx engine value))
        (is (= (if marked? 1 0) (j/call ctx engine "reset-choice" [value])))
        (is (dead? value))
        (finally (j/close! ctx engine))))))

(deftest marked-count-one-array-copies-live-owners-even-with-spare-capacity
  (let [ctx (context) engine (j/machine ctx) value (fresh ctx engine)
        a (array/push! ctx engine (array/empty! ctx engine 4) value)]
    (try
      (mark! ctx engine a)
      (let [before (counters engine) b (array/push! ctx engine a 42)]
        (is (not (identical? a b))) (is (dead? a))
        (is (= [value 42] (array/elements ctx b)))
        (is (= 1 (c/rc ctx value))) (is (mt? ctx value))
        (is (false? (mt? ctx b))) (is (exclusive? ctx b))
        (is (= 1 (- (host/private-value engine "retains") (nth before 2))))
        (j/release! ctx engine b) (is (dead? value)))
      (finally (j/close! ctx engine)))))

(deftest marked-array-pop-set-and-swap-all-copy-before-mutation
  (doseq [[operation expected] [["pop" [10]] ["set" [99 20]] ["swap" [20 10]]]]
    (let [ctx (context) engine (j/machine ctx)
          a (reduce #(array/push! ctx engine %1 %2) (array/empty! ctx engine 4) [10 20])]
      (try
        (mark! ctx engine a)
        (let [out (case operation
                    "pop" (array/pop! ctx engine a)
                    "set" (j/call ctx engine "Array.set._boxed" [0 a 0 99 0])
                    "swap" (j/call ctx engine "Array.swap._boxed" [0 a 0 1 0 0]))]
          (is (not (identical? a out))) (is (dead? a))
          (is (= expected (array/elements ctx out)))
          (is (false? (mt? ctx out))) (is (exclusive? ctx out))
          (j/release! ctx engine out))
        (finally (j/close! ctx engine))))))

(deftest array-marking-traverses-live-prefix-only
  (let [ctx (context) engine (j/machine ctx) live (fresh ctx engine) spare (fresh ctx engine)
        a (array/push! ctx engine (array/empty! ctx engine 4) live)]
    (try
      ;; A private diagnostic sentinel in spare storage has no guest ownership.
      ;; Restore it before any mutation/fork; marking must never traverse it.
      (aset ^objects (fields ctx a) 3 spare)
      (try (mark! ctx engine a) (finally (aset ^objects (fields ctx a) 3 nil)))
      (is (mt? ctx a)) (is (mt? ctx live)) (is (false? (mt? ctx spare)))
      (is (= 1 (array/size a)))
      (finally (j/release! ctx engine a) (j/release! ctx engine spare) (j/close! ctx engine)))))

(deftest marked-byte-array-fork-preserves-kind-state-and-pointer-owners-before-cow
  (let [ctx (context) engine (j/machine ctx)
        a (j/call ctx engine "ByteArray.mk._boxed" [(array/empty! ctx engine 0)])
        a (reduce #(byte/push! ctx engine %1 %2) a [1 2 3])]
    (pointer/same ctx engine a a)
    (let [word (pointer/word a)]
      (mark! ctx engine a)
      (is (= word (pointer/word a)))
      (let [fork (j/fork! ctx engine [a]) child (:engine fork) b (first (:roots fork))]
        (try
          (is (= word (pointer/word b))) (is (mt? ctx a)) (is (mt? ctx b))
          (is (= 1 (c/rc ctx a) (c/rc ctx b)))
          (is (not (identical? (private-call ctx nil "kindMetadata" [(:node-class ctx)] [a])
                              (private-call ctx nil "kindMetadata" [(:node-class ctx)] [b]))))
          (let [x (byte/push! ctx engine a 4) y (byte/push! ctx child b 9)]
            (is (not (identical? a x))) (is (not (identical? b y)))
            (is (dead? a)) (is (dead? b))
            (is (= [1 2 3 4] (byte/payload ctx x))) (is (= [1 2 3 9] (byte/payload ctx y)))
            (is (false? (mt? ctx x))) (is (false? (mt? ctx y)))
            (j/release! ctx engine x) (j/release! ctx child y))
          (finally (j/close! ctx engine) (j/close! ctx child)))))))

(deftest marked-byte-array-kind-cannot-be-reinterpreted-through-metadata-wrappers
  (doseq [[label args pattern] [["project" [] #"not a constructor"]
                                 ["Array.usize._boxed" [0] #"Expected Array"]
                                 ["ST.Prim.Ref.get._boxed" [0 0] #"Expected ST.Ref cell"]
                                 ["Task.get" [0] #"Expected engine ready Task"]
                                 ["apply" [] #"Expected closure"]]]
    (let [ctx (context) engine (j/machine ctx)
          a (j/call ctx engine "ByteArray.mk._boxed" [(array/empty! ctx engine 0)])]
      (mark! ctx engine a) (pointer/same ctx engine a a)
      (let [before (counters engine)
            arguments (case label
                        "project" [a] "Array.usize._boxed" [0 a]
                        "ST.Prim.Ref.get._boxed" [0 0 a 0]
                        "Task.get" [0 a] "apply" [a 0])]
        (is (re-find pattern (c/failure #(j/call ctx engine label arguments))))
        (is (= before (counters engine)))
        (is (= 1 (c/rc ctx a))) (is (false? (dead? a))))
      (when-not (:explicit ctx) (j/release! ctx engine a))
      (close-after-failure ctx engine))))

(deftest observed-marked-closure-generation-and-capture-state-survive-fork
  (let [ctx (context) engine (j/machine ctx) payload (fresh ctx engine)
        closure (j/make-closure! ctx engine "keep-first" [payload])]
    (pointer/same ctx engine closure closure)
    (let [word (pointer/word closure)]
      (mark! ctx engine closure)
      (let [fork (j/fork! ctx engine [closure]) child (:engine fork) copied (first (:roots fork))
            copied-payload (aget ^objects (fields ctx copied) 0)]
        (try
          (is (= word (pointer/word copied))) (is (mt? ctx copied))
          (is (mt? ctx copied-payload)) (is (= 1 (c/rc ctx copied-payload)))
          (is (identical? payload (j/call ctx engine "apply" [closure 0])))
          (is (identical? copied-payload (j/call ctx child "apply" [copied 0])))
          (is (dead? closure)) (is (dead? copied))
          (is (= 1 (c/rc ctx payload) (c/rc ctx copied-payload)))
          (j/release! ctx engine payload) (j/release! ctx child copied-payload)
          (finally (j/close! ctx engine) (j/close! ctx child)))))))

(deftest marked-count-one-closure-retains-captures-before-consuming-its-shell
  (doseq [marked? [false true]]
    (let [ctx (context) engine (j/machine ctx) value (fresh ctx engine)
          closure (j/make-closure! ctx engine "keep-first" [value])]
      (try
        (when marked? (mark! ctx engine closure))
        (let [before (counters engine) result (j/call ctx engine "apply" [closure 0])]
          (is (identical? value result)) (is (dead? closure))
          (is (= 1 (c/rc ctx value))) (is (= marked? (mt? ctx value)))
          (is (= (if marked? 1 0) (- (host/private-value engine "retains") (nth before 2))))
          (is (= (if marked? 0 1) (- (host/private-value engine "shellDeletes") (nth before 4))))
          (j/release! ctx engine value))
        (finally (j/close! ctx engine))))))

(deftest pointer-wrapper-order-and-forked-marking-never-hide-owner-guards
  (let [ctx (context) engine (j/machine ctx) a (fresh ctx engine) b (fresh ctx engine)]
    (try
      (mark! ctx engine a) (pointer/same ctx engine a a)
      (pointer/same ctx engine b b)
      (let [word (pointer/word b)] (mark! ctx engine b) (is (= word (pointer/word b))))
      (let [fork (j/fork! ctx engine [a b]) child (:engine fork) [x y] (:roots fork)]
        (try
          (is (= (pointer/word a) (pointer/word x))) (is (= (pointer/word b) (pointer/word y)))
          (is (mt? ctx x)) (is (mt? ctx y))
          (is (re-find #"belongs to another interpreter" (c/failure #(mark! ctx child a))))
          (is (re-find #"belongs to another interpreter" (c/failure #(j/retain! ctx child b))))
          (is (= 1 (shared! ctx engine a)))
          (is (= 1 (pointer/same ctx child x x)))
          (j/release! ctx child x) (j/release! ctx child y)
          (finally (j/close! ctx child))))
      (finally (j/release! ctx engine a) (j/release! ctx engine b) (j/close! ctx engine)))))

(deftest post-fork-marking-is-branch-local-even-with-shared-pointer-word
  (let [ctx (context) engine (j/machine ctx) value (fresh ctx engine)]
    (pointer/same ctx engine value value)
    (let [fork (j/fork! ctx engine [value]) child (:engine fork) copied (first (:roots fork))]
      (try
        (is (= (pointer/word value) (pointer/word copied)))
        (mark! ctx child copied)
        (is (false? (mt? ctx value))) (is (mt? ctx copied))
        (is (= 0 (shared! ctx engine value))) (is (= 1 (shared! ctx child copied)))
        (is (= 1 (c/rc ctx value) (c/rc ctx copied)))
        (finally (j/release! ctx engine value) (j/release! ctx child copied)
                 (j/close! ctx engine) (j/close! ctx child))))))

(deftest marking-rejects-impossible-st-pending-task-before-attaching-metadata
  (let [ctx (context) engine (j/machine ctx) value (fresh ctx engine)
        ready (task/pure ctx engine value)]
    (try
      ;; Diagnostic corruption only: restore before any runtime get/release.
      (aset ^objects (fields ctx ready) 0 nil)
      (try
        (is (re-find #"Pending Task outside ready-only" (c/failure #(mark! ctx engine ready))))
        (is (false? (mt? ctx ready))) (is (false? (mt? ctx value)))
        (finally (aset ^objects (fields ctx ready) 0 value)))
      (is (identical? value (task/get-task ctx engine ready)))
      (j/release! ctx engine value)
      (finally (j/close! ctx engine)))))

(deftest fresh-ref-task-pure-and-ready-map-remain-st-without-implicit-marking
  (let [ctx (context) engine (j/machine ctx) value (fresh ctx engine)
        callback (j/make-closure! ctx engine "keep-first" [value])
        ready (task/pure ctx engine 0)]
    (try
      (let [mapped (task/map-task ctx engine callback ready)]
        (is (false? (mt? ctx mapped))) (is (false? (mt? ctx value)))
        (is (dead? callback))
        (is (identical? value (task/get-task ctx engine mapped)))
        (is (= 1 (c/rc ctx value)))
        (j/release! ctx engine value))
      (let [marked (fresh ctx engine)]
        (mark! ctx engine marked)
        (let [pure (task/pure ctx engine marked)]
          (is (false? (mt? ctx pure))) (is (mt? ctx marked))
          (is (identical? marked (task/get-task ctx engine pure)))
          (is (= 1 (shared! ctx engine marked)))
          (j/release! ctx engine marked)))
      (finally (j/close! ctx engine)))))

(deftest st-ready-task-marking-visits-value-and-refill-of-empty-mt-ref-marks-payload
  (let [ctx (context) engine (j/machine ctx) value (fresh ctx engine)
        ready (task/pure ctx engine value) cell (ref/make-ref! ctx engine 0)]
    (try
      (mark! ctx engine ready) (is (mt? ctx ready)) (is (mt? ctx value))
      (is (identical? value (task/get-task ctx engine ready))) (j/release! ctx engine value)
      (mark! ctx engine cell) (is (= 0 (ref/ref-take! ctx engine cell)))
      (mark! ctx engine cell)
      (let [incoming (fresh ctx engine)]
        (ref/ref-set! ctx engine cell incoming) (is (mt? ctx incoming)))
      (finally (j/release! ctx engine cell) (j/close! ctx engine)))))

(defn check! [basis] (binding [*basis* basis] (run-tests 'java-ir-logical-sharing-checks)))
