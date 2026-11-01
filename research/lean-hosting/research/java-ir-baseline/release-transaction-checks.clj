(ns java-ir-release-transaction-checks
  "Budgeted explicit finalizer-free root release; no guest callback dispatch."
  (:require [clojure.test :refer [deftest is run-tests]] [clojure.data.json :as json]
            [java-ir-baseline :as j] [java-ir-baseline-checks :as c]
            [java-ir-release-order-checks :as order] [java-ir-host-checks :as host]
            [java-ir-generation-checks :as g] [java-ir-extern-checks :as x]
            [java-ir-array-checks :as array] [java-ir-pointer-checks :as pointer]))
(def ^:dynamic *basis* nil)
(defn context [] (binding [order/*basis* (assoc *basis* :explicit true)] (order/context)))
(defn fields [ctx node] (order/fields ctx node))
(defn dead? [node] (order/dead? node))
(defn cons! [ctx engine value] (order/cons! ctx engine value))
(defn pair! [ctx engine a b] (order/pair! ctx engine a b))
(defn tx [engine] (host/private-value engine "releaseTransaction"))
(defn state [engine field] (host/private-value (tx engine) field))
(defn counters [engine] (mapv #(host/private-value engine %) ["allocations" "retains" "releases" "shellDeletes"]))
(defn finish! [ctx engine]
  (loop [left 100000]
    (when (zero? left) (throw (ex-info "Release failed to finish" {})))
    (if (j/advance! ctx engine 3) (j/take-result! ctx engine) (recur (dec left)))))

(deftest root-claim-zero-budget-and-native-midbatch-state
  (let [ctx (context) engine (j/machine ctx) a (cons! ctx engine 11) b (cons! ctx engine 22) root (pair! ctx engine a b)]
    (try
      (j/start-release! ctx engine root 1)
      (is (= "running" (j/phase ctx engine))) (is (nil? (j/active ctx engine)))
      (is (nil? (host/private-value engine "pc"))) (is (nil? (host/private-value engine "entry")))
      (is (true? (state engine "claimed"))) (is (= 1 (state engine "count")))
      (is (identical? root (state engine "origin"))) (is (dead? root))
      (is (= 1 (c/rc ctx a) (c/rc ctx b)))
      (let [before (counters engine)]
        (is (false? (j/advance! ctx engine 0))) (is (= before (counters engine))) (is (= 0 (j/instructions ctx engine))))
      (is (false? (j/advance! ctx engine 1)))
      (is (= 1 (state engine "fieldCursor"))) (is (= 0 (c/rc ctx a))) (is (= 1 (c/rc ctx b)))
      (is (= [nil b] (vec (fields ctx root))))
      (is (= [a] (order/queue engine))) (is (= [11] (vec (fields ctx a))))
      (is (false? (j/advance! ctx engine 1)))
      (is (= [a b] (order/queue engine))) (is (= 2 (state engine "fieldCursor")))
      (is (= [22] (vec (fields ctx b))))
      (is (false? (j/advance! ctx engine 1))) (is (identical? b (state engine "current")))
      (is (= 0 (state engine "fieldCursor"))) (is (= [a] (order/queue engine)))
      (is (= 0 (finish! ctx engine))) (is (= 3 (host/private-value engine "releases")))
      (is (nil? (tx engine))) (is (= 0 (order/pending engine)))
      (is (every? nil? (host/private-value engine "releaseWork")))
      (is (g/bad? #(j/take-result! ctx engine)))
      (is (every? #(every? nil? (fields ctx %)) [root a b]))
      (finally (j/close! ctx engine)))))

(deftest quiet-immediate-shared-persistent-and-zero-count-need-no-transaction
  (let [ctx (context) engine (j/machine ctx)]
    (try
      (doseq [value [0 -1 "text" (biginteger (.shiftLeft java.math.BigInteger/ONE 100))]]
        (j/start-release! ctx engine value 1)
        (is (= "complete" (j/phase ctx engine))) (is (nil? (tx engine)))
        (is (true? (j/advance! ctx engine 0))) (is (= 0 (j/take-result! ctx engine))))
      (let [value (cons! ctx engine 7)]
        (j/start-release! ctx engine value 0) (is (= 1 (c/rc ctx value))) (is (nil? (tx engine)))
        (is (= 0 (j/take-result! ctx engine)))
        (j/retain! ctx engine value)
        (j/start-release! ctx engine value 1) (is (= 1 (c/rc ctx value))) (is (nil? (tx engine)))
        (is (= 0 (j/take-result! ctx engine)))
        (.setInt ^java.lang.reflect.Field (:rc ctx) value 0)
        (j/start-release! ctx engine value Integer/MAX_VALUE)
        (is (nil? (tx engine))) (is (false? (dead? value))) (is (= [7] (vec (fields ctx value))))
        (is (= 0 (j/take-result! ctx engine))))
      (finally (j/close! ctx engine)))))

(deftest invalid-carriers-counts-and-recursive-entry-are-pure-preflight
  (let [ctx (context) engine (j/machine ctx) value (cons! ctx engine 7)
        bits-class (.loadClass (:loader ctx) "ansatz.research.ir.Interpreter$F64Bits")
        ctor (.getDeclaredConstructor bits-class (into-array Class [Long/TYPE]))
        _ (.setAccessible ctor true) bits (.newInstance ctor (object-array [(long 0)]))]
    (try
      (doseq [invalid [nil (Object.) (object-array 0) 0.0 bits]]
        (let [before [(counters engine) (j/instructions ctx engine)]]
          (is (g/bad? #(j/start-release! ctx engine invalid 0)))
          (is (= before [(counters engine) (j/instructions ctx engine)]))
          (is (= "idle" (j/phase ctx engine))) (is (nil? (tx engine)))))
      (doseq [count [-1 1.5 "1" (inc (bigint Integer/MAX_VALUE)) 2 Integer/MAX_VALUE]]
        (let [before (counters engine)]
          (is (g/bad? #(j/start-release! ctx engine value count))) (is (= before (counters engine)))
          (is (= 1 (c/rc ctx value)))))
      (is (g/bad? #(.invoke ^java.lang.reflect.Method (:start-release ctx) engine (object-array [value (int -1)]))))
      (is (false? (host/private-value engine "releaseRoot")))
      (j/release! ctx engine value)
      (is (g/bad? #(j/start-release! ctx engine value 0)))
      (finally (j/close! ctx engine)))
    (let [recursive (assoc ctx :explicit false) engine (j/machine recursive) value (cons! recursive engine 9)]
      (is (g/bad? #(j/start-release! recursive engine value 1))) (is (= 1 (c/rc recursive value)))
      (j/release! recursive engine value) (j/close! recursive engine))))

(deftest pending-and-completed-release-reject-illegal-entry-without-corrupting-work
  (let [ctx (context) engine (j/machine ctx) root (cons! ctx engine 7) other (cons! ctx engine 8)]
    (try
      (j/start-release! ctx engine root 1)
      (doseq [operation [#(j/start-release! ctx engine other 1) #(j/release! ctx engine other)
                         #(j/start! ctx engine "cons" [0]) #(j/take-result! ctx engine)
                         #(j/install-program! ctx engine) #(j/make-closure! ctx engine "three" [])
                         #(j/finish-initialization! ctx engine) #(j/close! ctx engine)]]
        (let [before [(counters engine) (order/queue engine) (state engine "fieldCursor")]]
          (is (g/bad? operation)) (is (= before [(counters engine) (order/queue engine) (state engine "fieldCursor")]))
          (is (= 1 (c/rc ctx other)))))
      (while (not (j/advance! ctx engine 1)))
      (is (= "complete" (j/phase ctx engine)))
      (is (g/bad? #(j/release! ctx engine other)))
      (is (g/bad? #(j/start-release! ctx engine other 1)))
      (is (= 0 (j/take-result! ctx engine)))
      (j/release! ctx engine other)
      (is (dead? other))
      (finally (j/close! ctx engine)))))

(deftest partial-count-and-duplicate-fields-consume-each-credit-once
  (let [ctx (context) engine (j/machine ctx) value (cons! ctx engine 7)]
    (try
      (j/retain! ctx engine value) (j/retain! ctx engine value)
      (j/start-release! ctx engine value 2) (is (= 1 (c/rc ctx value))) (is (= 0 (j/take-result! ctx engine)))
      (j/retain! ctx engine value)
      (let [root (pair! ctx engine value value)]
        (j/start-release! ctx engine root 1)
        (is (false? (j/advance! ctx engine 1))) (is (= 1 (c/rc ctx value))) (is (empty? (order/queue engine)))
        (is (false? (j/advance! ctx engine 1))) (is (= 0 (c/rc ctx value))) (is (= [value] (order/queue engine)))
        (is (= 0 (finish! ctx engine))) (is (dead? value)))
      (is (= 5 (host/private-value engine "releases")))
      (finally (j/close! ctx engine)))))

(deftest wide-and-deep-release-honor-single-step-budgets
  (let [ctx (context) engine (j/machine ctx) leaves (mapv #(cons! ctx engine %) (range 40))
        root (reduce #(array/push! ctx engine %1 %2) (array/empty! ctx engine 40) leaves)]
    (try
      (j/start-release! ctx engine root 1)
      (dotimes [i 40]
        (is (false? (j/advance! ctx engine 1)))
        (is (= (inc i) (state engine "fieldCursor")))
        (is (every? #(some? (aget ^objects (fields ctx %) 0)) leaves)))
      (is (= 40 (order/pending engine)))
      (is (= 0 (finish! ctx engine)))
      (let [nodes (loop [left 5000 value 0 nodes []]
                    (if (zero? left) nodes
                      (let [next (cons! ctx engine value)] (recur (dec left) next (conj nodes next)))))
            before (host/private-value engine "releases")]
        (j/start-release! ctx engine (peek nodes) 1)
        (is (= 0 (finish! ctx engine)))
        (is (= 5000 (- (host/private-value engine "releases") before)))
        (is (every? dead? nodes)))
      (finally (j/close! ctx engine)))))

(deftest midfield-fork-preserves-shared-aliases-and-independent-drain
  (let [ctx (context) parent (j/machine ctx) value (cons! ctx parent 99)
        _ (j/retain! ctx parent value) _ (j/retain! ctx parent value) root (pair! ctx parent value value)]
    (try
      (j/start-release! ctx parent root 1) (j/advance! ctx parent 1)
      (let [fork (j/fork! ctx parent [value]) child (:engine fork) copy (first (:roots fork))
            child-root (state child "origin")]
        (try
          (is (= 2 (c/rc ctx value) (c/rc ctx copy)))
          (is (not (identical? value copy)))
          (is (identical? child-root (state child "current")))
          (is (identical? copy (aget ^objects (fields ctx child-root) 1)))
          (is (= [nil value] (vec (fields ctx root))))
          (is (= 1 (state parent "fieldCursor") (state child "fieldCursor")))
          (is (= 0 (finish! ctx parent))) (is (= 1 (c/rc ctx value))) (is (= 2 (c/rc ctx copy)))
          (is (= 0 (finish! ctx child))) (is (= 1 (c/rc ctx copy)))
          (aset ^objects (fields ctx copy) 0 77)
          (is (= 99 (aget ^objects (fields ctx value) 0)))
          (is (= 77 (aget ^objects (fields ctx copy) 0)))
          (j/release! ctx parent value) (j/release! ctx child copy)
          (finally (j/close! ctx child))))
      (finally (j/close! ctx parent)))))

(deftest fork-copies-dead-queued-shells-and-their-still-owned-fields
  (let [ctx (context) parent (j/machine ctx) payload (cons! ctx parent 9) a (cons! ctx parent payload)
        b (cons! ctx parent 22) root (pair! ctx parent a b)]
    (try
      (j/start-release! ctx parent root 1) (j/advance! ctx parent 1)
      (let [fork (j/fork! ctx parent []) child (:engine fork) copied-a (first (order/queue child))
            copied-payload (aget ^objects (fields ctx copied-a) 0)]
        (try
          (is (dead? a)) (is (dead? copied-a))
          (is (not (identical? a copied-a))) (is (not (identical? payload copied-payload)))
          (is (= 1 (c/rc ctx payload) (c/rc ctx copied-payload)))
          (is (= 0 (c/rc ctx a) (c/rc ctx copied-a)))
          (is (= 0 (finish! ctx parent)))
          (is (false? (dead? copied-payload)))
          (is (= 0 (finish! ctx child)))
          (is (dead? copied-payload)) (is (dead? payload))
          (finally (j/close! ctx child))))
      (finally (j/close! ctx parent)))))

(deftest postclaim-failure-preserves-queue-cursor-and-unconsumed-edges
  (let [ctx (context) engine (j/machine ctx) a (cons! ctx engine 11) b (cons! ctx engine 22)
        bad (cons! ctx engine 0) _ (j/release! ctx engine bad)
        root (array/push! ctx engine (array/push! ctx engine (array/push! ctx engine (array/empty! ctx engine 3) a) 0) b)]
    (aset ^objects (fields ctx root) 1 bad)
    (j/start-release! ctx engine root 1) (j/advance! ctx engine 1)
    (let [before (counters engine)]
      (is (g/bad? #(j/advance! ctx engine 1)))
      (is (= "failed" (j/phase ctx engine)))
      (is (true? (state engine "claimed"))) (is (= 1 (state engine "fieldCursor")))
      (is (= [a] (order/queue engine))) (is (= [11] (vec (fields ctx a))))
      (is (= [nil bad b] (vec (fields ctx root)))) (is (= 1 (c/rc ctx b)))
      (is (= before (counters engine)))
      (is (g/bad? #(j/advance! ctx engine 1))) (is (g/bad? #(j/take-result! ctx engine)))
      (is (g/bad? #(j/release! ctx engine b))) (is (g/bad? #(j/fork! ctx engine [])))
      (is (g/bad? #(j/close! ctx engine)))
      (is (= [a] (order/queue engine))) (is (= 1 (c/rc ctx b))))))

(deftest completed-unit-forks-and-close-disposes-source-cache-without-function-dereference
  (let [base (context) ctx (j/extend-program base (x/raw [(c/object-constant "cached")]))
        parent (j/machine ctx) value (j/call ctx parent "cached" [])]
    (j/start-release! ctx parent value 1)
    (let [child (:engine (j/fork! ctx parent []))]
      (try
        (is (= "complete" (j/phase ctx parent) (j/phase ctx child)))
        (is (= 0 (j/take-result! ctx child)))
        (j/close! ctx child)
        (is (false? (dead? value)))
        (j/close! ctx parent)
        (is (dead? value))
        (is (g/bad? #(j/start-release! ctx parent 0 0)))
        (finally (j/close! ctx child) (j/close! ctx parent))))))

(deftest existing-pointer-and-closure-provenance-guards-precede-root-claim
  (let [ctx (binding [pointer/*basis* (assoc *basis* :explicit true)] (pointer/prepare []))
        parent (j/machine ctx) other (j/machine ctx) value (pointer/fresh ctx parent)]
    (try
      (is (= 1 (pointer/same ctx parent value value)))
      (let [before (counters other)]
        (is (g/bad? #(j/start-release! ctx other value 0))) (is (= before (counters other)))
        (is (= 1 (c/rc ctx value))))
      (let [word (pointer/word value)]
        (j/start-release! ctx parent value 1)
        (let [child (:engine (j/fork! ctx parent [])) copy (state child "origin")]
          (try
            (is (= word (pointer/word copy)))
            (is (identical? (host/private-value child "runtimeIdentity") (host/private-value (pointer/metadata copy) "owner")))
            (is (not (identical? (pointer/metadata value) (pointer/metadata copy))))
            (is (= 0 (finish! ctx parent) (finish! ctx child)))
            (finally (j/close! ctx child)))))
      (finally (j/close! ctx parent) (j/close! ctx other))))
  (let [base (context) a (j/extend-program base (x/raw [(g/literal "left" 1)]))
        b (j/extend-program base (x/raw [(g/literal "right" 2)]))
        left (j/machine a) right (j/machine b) f (j/make-closure! b right "right" [])]
    (try
      (let [before (counters left)]
        (is (g/bad? #(j/start-release! a left f 0))) (is (= before (counters left)))
        (is (= 1 (c/rc b f))))
      (finally (j/release! b right f) (j/close! a left) (j/close! b right)))))

(deftest field-limit-preflight-and-queued-limit-failure-retain-the-correct-claim
  (let [ctx (context) engine (j/machine ctx) value (array/empty! ctx engine 0)
        metadata (host/private-value value "metadata") size (.getDeclaredField (class metadata) "size")]
    (.setAccessible size true) (.setInt size metadata 1)
    (try
      (let [before (counters engine)]
        (is (g/bad? #(j/start-release! ctx engine value 1))) (is (= before (counters engine)))
        (is (= 1 (c/rc ctx value))) (is (nil? (tx engine))) (is (= "idle" (j/phase ctx engine))))
      (finally (.setInt size metadata 0) (j/release! ctx engine value) (j/close! ctx engine))))
  (let [ctx (context) engine (j/machine ctx) child (array/empty! ctx engine 0)
        metadata (host/private-value child "metadata") size (.getDeclaredField (class metadata) "size")
        root (cons! ctx engine child)]
    (.setAccessible size true) (.setInt size metadata 1)
    (j/start-release! ctx engine root 1)
    (is (false? (j/advance! ctx engine 1)))
    (is (= [child] (order/queue engine)))
    (is (g/bad? #(j/advance! ctx engine 1)))
    (is (= "failed" (j/phase ctx engine)))
    (is (identical? root (state engine "current")))
    (is (= [child] (order/queue engine))) (is (dead? child))
    (is (g/bad? #(j/close! ctx engine)))))

(defn check! [basis] (binding [*basis* basis] (run-tests 'java-ir-release-transaction-checks)))
