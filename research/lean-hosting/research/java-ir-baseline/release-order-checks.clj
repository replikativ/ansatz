(ns java-ir-release-order-checks
  "Native ascending credit batches and LIFO zero shells, without finalizers."
  (:require [clojure.test :refer [deftest is run-tests]]
            [java-ir-baseline :as j] [java-ir-baseline-checks :as c]
            [java-ir-extern-checks :as x] [java-ir-host-checks :as host]
            [java-ir-generation-checks :as g] [java-ir-array-checks :as array]))
(def ^:dynamic *basis* nil)
(defn context []
  (assoc *basis* :program (j/invoke-static (:prepare *basis*)
    [(x/raw (concat (mapv #(get % "row") (array/originals))
       [(c/decl "cons" [(c/p 1 "object")] "object" (c/let-ir 2 "object" (c/ctor 1 [(c/v 1)] 0) (c/ret 2)))
        (c/decl "pair" [(c/p 1 "object") (c/p 2 "object")] "object"
          (c/let-ir 3 "object" (c/ctor 2 [(c/v 1) (c/v 2)] 0) (c/ret 3)))
        (c/decl "three" [(c/p 1 "object") (c/p 2 "object") (c/p 3 "object")] "object" (c/ret 3))]))])))
(defn cons! [ctx engine value] (j/call ctx engine "cons" [value]))
(defn pair! [ctx engine left right] (j/call ctx engine "pair" [left right]))
(defn fields [ctx node] (.get ^java.lang.reflect.Field (:fields ctx) node))
(defn dead? [node] (host/private-value node "dead"))
(defn pending [engine] (host/private-value engine "releasePending"))
(defn queue [engine] (vec (take (pending engine) (host/private-value engine "releaseWork"))))
(defn batch! [ctx engine node]
  (let [method (.getDeclaredMethod ^Class (:class ctx) "releaseFields" (into-array Class [(:node-class ctx)]))]
    (.setAccessible method true) (.invoke method engine (object-array [node]))))
(defn pop-zero! [ctx engine]
  (let [method (.getDeclaredMethod ^Class (:class ctx) "takeReleased" (make-array Class 0))]
    (.setAccessible method true) (.invoke method engine (object-array 0))))
;; These private probes expose a batch boundary without registering an executable
;; destructor/finalizer hook. Test roots keep their own owner until the final DEC;
;; removed field credits have already moved to the private zero-shell queue.

(deftest siblings-lose-credits-as-one-ascending-batch-before-lifo-visits
  (let [ctx (context) engine (j/machine ctx) a (cons! ctx engine 11) b (cons! ctx engine 22)
        root (pair! ctx engine a b)]
    (try
      (batch! ctx engine root)
      (is (= 0 (c/rc ctx a) (c/rc ctx b)))
      (is (dead? a)) (is (dead? b))
      (is (= [a b] (queue engine))) (is (= [nil nil] (vec (fields ctx root))))
      (is (= 11 (aget ^objects (fields ctx a) 0))) (is (= 22 (aget ^objects (fields ctx b) 0)))
      (is (g/bad? #(j/retain! ctx engine a)))
      (let [first (pop-zero! ctx engine) second (pop-zero! ctx engine)]
        (is (identical? b first)) (is (identical? a second))
        (batch! ctx engine first) (batch! ctx engine second))
      (is (= 0 (pending engine)))
      (j/release! ctx engine root)
      (is (= 3 (host/private-value engine "releases")))
      (is (every? nil? (host/private-value engine "releaseWork")))
      (finally (j/close! ctx engine)))))

(deftest shared-grandchild-is-decremented-at-parent-scan-not-at-queue-pop
  (let [ctx (context) engine (j/machine ctx) child (cons! ctx engine 7)
        _ (j/retain! ctx engine child) a (cons! ctx engine child) b (cons! ctx engine child)
        root (pair! ctx engine a b)]
    (try
      (batch! ctx engine root)
      (is (= 2 (c/rc ctx child))) (is (= [a b] (queue engine)))
      (is (identical? b (pop-zero! ctx engine))) (batch! ctx engine b)
      (is (= 1 (c/rc ctx child))) (is (= [a] (queue engine)))
      (is (identical? a (pop-zero! ctx engine))) (batch! ctx engine a)
      (is (= 0 (c/rc ctx child))) (is (dead? child)) (is (= [child] (queue engine)))
      (is (identical? child (pop-zero! ctx engine))) (batch! ctx engine child)
      (j/release! ctx engine root)
      (is (= 5 (host/private-value engine "releases")))
      (is (= [nil] (vec (fields ctx child))))
      (finally (j/close! ctx engine)))))

(deftest duplicate-edges-enqueue-once-and-persistent-is-not-queued-zero
  (let [ctx (context) engine (j/machine ctx) a (cons! ctx engine 7)
        _ (j/retain! ctx engine a) root (pair! ctx engine a a)]
    (try
      (batch! ctx engine root)
      (is (= [a] (queue engine))) (is (= 0 (c/rc ctx a)))
      (is (= 2 (host/private-value engine "releases")))
      ;; Public destruction uses the same batch/pop helpers to drain this
      ;; privately inspected queue and the now-empty root, without callbacks.
      (j/release! ctx engine root)
      (is (dead? a)) (is (= [nil] (vec (fields ctx a)))) (is (= 0 (pending engine)))
      (let [persistent (cons! ctx engine 99) ordinary (cons! ctx engine 42)]
        (.setInt ^java.lang.reflect.Field (:rc ctx) persistent 0)
        (let [root (pair! ctx engine persistent ordinary)]
          (batch! ctx engine root)
          (is (= [ordinary] (queue engine)))
          (is (false? (dead? persistent))) (is (= 99 (aget ^objects (fields ctx persistent) 0)))
          (j/release! ctx engine root)
          (is (dead? ordinary)) (is (false? (dead? persistent)))))
      (finally (j/close! ctx engine)))))

(deftest array-scans-only-live-elements-and-closure-scans-captures-ascending
  (let [ctx (context) engine (j/machine ctx) a (cons! ctx engine 1) b (cons! ctx engine 2)
        spare (cons! ctx engine 3) values (array/push! ctx engine (array/push! ctx engine (array/empty! ctx engine 4) a) b)]
    (try
      ;; The spare is a deliberately installed nonowning diagnostic alias.
      (aset ^objects (fields ctx values) 3 spare)
      (batch! ctx engine values)
      (is (= [a b] (queue engine))) (is (= 1 (c/rc ctx spare)))
      (j/release! ctx engine values)
      (is (dead? a)) (is (dead? b)) (is (false? (dead? spare)))
      (j/release! ctx engine spare)
      (let [a (cons! ctx engine 4) b (cons! ctx engine 5)
            closure (j/make-closure! ctx engine "three" [a b])]
        (batch! ctx engine closure)
        (is (= [a b] (queue engine)))
        (j/release! ctx engine closure)
        (is (dead? a)) (is (dead? b)) (is (dead? closure)))
      (finally (j/close! ctx engine)))))

(deftest wide-zero-batch-grows-before-claims-and-visits-reverse-registration
  (let [ctx (context) engine (j/machine ctx)
        leaves (mapv #(cons! ctx engine %) (range 40))
        root (reduce #(array/push! ctx engine %1 %2) (array/empty! ctx engine 40) leaves)]
    (try
      (batch! ctx engine root)
      (is (= 40 (pending engine))) (is (= leaves (queue engine)))
      (is (every? #(and (dead? %) (zero? (c/rc ctx %))) leaves))
      (let [visited (loop [events []]
                      (if (zero? (pending engine)) events
                        (let [node (pop-zero! ctx engine) marker (aget ^objects (fields ctx node) 0)]
                          (batch! ctx engine node) (recur (conj events marker)))))]
        (is (= (vec (reverse (range 40))) visited)))
      (j/release! ctx engine root)
      (is (= 41 (host/private-value engine "releases")))
      (is (every? nil? (host/private-value engine "releaseWork")))
      (finally (j/close! ctx engine)))))

(deftest ordinary-public-dec-drains-a-deep-chain-iteratively
  (let [ctx (context) engine (j/machine ctx)
        nodes (loop [left 5000 value 0 nodes []]
                (if (zero? left) nodes
                  (let [next (cons! ctx engine value)] (recur (dec left) next (conj nodes next)))))]
    (try
      (j/release! ctx engine (peek nodes))
      (is (= 5000 (host/private-value engine "releases")))
      (is (every? dead? nodes)) (is (every? #(nil? (aget ^objects (fields ctx %) 0)) nodes))
      (is (= 0 (pending engine)))
      (finally (j/close! ctx engine)))))

(defn check! [basis] (binding [*basis* basis] (run-tests 'java-ir-release-order-checks)))
