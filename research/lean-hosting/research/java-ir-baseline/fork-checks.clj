(ns java-ir-fork-checks
  (:require [clojure.test :refer [deftest is run-tests]]
            [java-ir-baseline :as j]
            [java-ir-baseline-checks :as c]
            [java-ir-continuation-checks :as k]
            [java-ir-main-checks :as main]
            [java-ir-extern-checks :as x])
  (:import [java.lang.reflect Method Field]))

(def ^:dynamic *basis* nil)
(defn- prepare [rows explicit?]
  (binding [c/*basis* (assoc *basis* :explicit explicit?)] (c/prepare rows)))
(defn- private-field [ctx engine label]
  (let [f (.getDeclaredField ^Class (:class ctx) label)] (.setAccessible f true) (.get f engine)))
(defn- fields [ctx value] (.get ^Field (:fields ctx) value))
(defn- fork! [ctx engine roots]
  (let [method (.getMethod ^Class (:class ctx) "eagerFork" (into-array Class [(class (object-array 0))]))
        packet (.invoke method engine (object-array [(object-array roots)]))
        cls (class packet)]
    {:engine (.get (.getField cls "engine") packet)
     :roots (vec (.get (.getField cls "roots") packet))}))
(defn- counters [ctx engine] (k/counters ctx engine))

(deftest idle-cache-and-external-aliases-fork-together
  (doseq [explicit? [false true]]
    (let [ctx (prepare [(c/object-constant "child")] explicit?) parent (j/machine ctx)
          root (j/call ctx parent "child" [])
          before (counters ctx parent)
          {:keys [engine roots]} (fork! ctx parent [root root])
          branch engine copy (first roots)]
      ;; Keep parent explicitly: roots still refer to its object identity.
      (is (identical? copy (second roots)))
      (is (not (identical? copy root)))
      (is (= (c/rc ctx root) (c/rc ctx copy)))
      (is (= 2 (c/rc ctx copy)))
      (is (= before (counters ctx branch)))
      (let [again (j/call ctx branch "child" [])]
        (is (identical? copy again)) (j/release! ctx branch again))
      (aset-byte (.get ^Field (:scalars ctx) copy) 0 (byte 7))
      (is (= 0 (aget ^bytes (.get ^Field (:scalars ctx) root) 0)))
      (j/release! ctx branch copy)
      (j/release! ctx parent root)
      (j/close! ctx branch) (j/close! ctx parent))))

(deftest readiness-false-is-not-an-initialized-null-cache
  (let [ctx (prepare [(c/object-constant "child")] true) parent (j/machine ctx)
        {:keys [engine]} (fork! ctx parent [])]
    (try
      (is (false? (aget ^booleans (private-field ctx parent "constantReady") 0)))
      (is (false? (aget ^booleans (private-field ctx engine "constantReady") 0)))
      (j/release! ctx parent (j/call ctx parent "child" []))
      (is (true? (aget ^booleans (private-field ctx parent "constantReady") 0)))
      (is (false? (aget ^booleans (private-field ctx engine "constantReady") 0)))
      (j/release! ctx engine (j/call ctx engine "child" []))
      (is (true? (aget ^booleans (private-field ctx engine "constantReady") 0)))
      (finally (j/close! ctx parent) (j/close! ctx engine)))))

(deftest paused-every-prefix-copies-control-and-ownership
  (let [ctx (prepare (k/mixed-program) true)]
    (doseq [prefix (range 1 65)]
      (let [parent (j/machine ctx) child-root (j/call ctx parent "child" [])]
        (j/start! ctx parent "bridge" [child-root])
        (j/advance! ctx parent prefix)
        (let [before (counters ctx parent)
              {:keys [engine]} (fork! ctx parent [])]
          (try
            (is (= (j/phase ctx parent) (j/phase ctx engine)))
            (is (= (j/depth ctx parent) (j/depth ctx engine)))
            (is (= (j/instructions ctx parent) (j/instructions ctx engine)))
            (is (= before (counters ctx engine)))
            (doseq [field ["bp" "sp" "jbp" "jsp" "callsLeft" "scalarResult"
                           "pendingOwnedResult" "continuationDepth" "instructions"]]
              (is (= (private-field ctx parent field) (private-field ctx engine field))))
            (is (= (j/active ctx parent) (j/active ctx engine)))
            (doseq [field ["objects" "numbers" "joins" "constants" "constantReady" "continuations" "releaseWork"]]
              (is (not (identical? (private-field ctx parent field) (private-field ctx engine field)))))
            (is (= 42 (k/finish! ctx parent [1 3 2])))
            (is (= 42 (k/finish! ctx engine [2 1])))
            (is (= (counters ctx parent) (counters ctx engine)))
            (finally (j/close! ctx parent) (j/close! ctx engine))))))))

(deftest completed-pending-result-escrow-is-independent
  (let [ctx (prepare [(c/object-constant "child")] true) parent (j/machine ctx)]
    (j/start! ctx parent "child" []) (j/advance! ctx parent 100)
    (let [{:keys [engine]} (fork! ctx parent [])
          a (j/take-result! ctx parent) b (j/take-result! ctx engine)]
      (try
        (is (= 2 (c/rc ctx a) (c/rc ctx b)))
        (is (not (identical? a b)))
        (j/release! ctx parent a)
        (is (= 2 (c/rc ctx b)))
        (j/release! ctx engine b)
        (finally (j/close! ctx parent) (j/close! ctx engine))))))

(deftest cycles-and-field-array-aliases-preserve-identity
  (let [ctx (prepare [(c/decl "cell" [(c/p 1 "object")] "object"
                             (c/let-ir 2 "object" (c/ctor 1 [(c/v 1)] 1) (c/ret 2)))] false)
        parent (j/machine ctx) root (j/call ctx parent "cell" [0])
        slots (fields ctx root)]
    (aset slots 0 root) (j/retain! ctx parent root)
    (let [{:keys [engine roots]} (fork! ctx parent [slots root root])
          a (nth roots 1)]
      (is (identical? a (nth roots 2)))
      (is (identical? (first roots) (fields ctx a)))
      (is (identical? a (aget (fields ctx a) 0)))
      (is (not (identical? slots (fields ctx a))))
      ;; Break the self-edge and discharge its owner in each branch.
      (aset (fields ctx a) 0 0) (j/release! ctx engine a)
      (is (identical? root (aget slots 0)))
      (aset slots 0 0) (j/release! ctx parent root)
      (j/release! ctx engine a) (j/release! ctx parent root)
      (j/close! ctx engine) (j/close! ctx parent))))

(deftest virtual-stream-private-closures-rebind-and-output-diverges
  (let [rows (into (vec (vals (x/originals))) (main/helper-rows))
        ctx (binding [x/*basis* (assoc *basis* :explicit true)] (x/prepare rows))
        parent (j/machine ctx)]
    (j/release! ctx parent (j/call ctx parent "put" ["prefix"]))
    (let [method (j/call ctx parent "partial-put" ["-method"])
          {:keys [engine roots]} (fork! ctx parent [method])]
      (try
        (j/release! ctx parent (j/call ctx parent "put" ["parent"]))
        (j/release! ctx engine (j/call ctx engine "put" ["child"]))
        (j/release! ctx parent (j/call ctx parent "apply-zero" [method]))
        (j/release! ctx engine (j/call ctx engine "apply-zero" [(first roots)]))
        (is (= "prefixparent-method" (main/stdout ctx parent)))
        (is (= "prefixchild-method" (main/stdout ctx engine)))
        (j/close! ctx parent)
        (j/release! ctx engine (j/call ctx engine "put" ["-live"]))
        (is (= "prefixchild-method-live" (main/stdout ctx engine)))
        (finally (j/close! ctx parent) (j/close! ctx engine))))))

(deftest array-metadata-and-cache-element-alias-survive-fork
  (let [rows (into (vec (vals (x/originals))) (main/helper-rows))
        ctx (binding [x/*basis* (assoc *basis* :explicit true)] (x/prepare rows))
        parent (j/machine ctx)
        element (j/call ctx parent "child" [])
        list (j/call ctx parent "cons" [element 0])
        array (j/call ctx parent "Array.mk" [0 list])
        {:keys [engine roots]} (fork! ctx parent [array])]
    (try
      (let [answer (j/call ctx engine "owned-array-get" [(first roots) 0])
            cached (j/call ctx engine "child" [])]
        (is (identical? answer cached))
        (is (not (identical? element answer)))
        (j/release! ctx engine answer) (j/release! ctx engine cached))
      (is (= 2 (c/rc ctx element)))
      (is (= 1 (j/call ctx parent "owned-array-size" [array])))
      (is (= 1 (c/rc ctx element)))
      (finally (j/close! ctx parent) (j/close! ctx engine)))))

(deftest stale-dead-register-alias-is-copied-without-owning-it
  (let [ctx (prepare [(c/decl "stale" [] "object"
                             (c/let-ir 1 "object" (c/ctor 7 [] 1)
                               ["dec" {:idx 1} 1 true false
                                (c/let-ir 2 "object" (c/lit 9) (c/ret 2))]))] true)
        parent (j/machine ctx)]
    (j/start! ctx parent "stale" []) (j/advance! ctx parent 2)
    (let [{:keys [engine]} (fork! ctx parent [])
          a (aget ^objects (private-field ctx parent "objects") 1)
          b (aget ^objects (private-field ctx engine "objects") 1)
          dead (.getDeclaredField ^Class (:node-class ctx) "dead")]
      (.setAccessible dead true)
      (is (.getBoolean dead a)) (is (.getBoolean dead b))
      (is (not (identical? a b)))
      (is (= 0 (c/rc ctx a) (c/rc ctx b)))
      (is (= 9 (k/finish! ctx parent [1])))
      (is (= 9 (k/finish! ctx engine [1])))
      (j/close! ctx parent) (j/close! ctx engine))))

(deftest deep-graph-fork-does-not-use-java-recursion
  (let [ctx (prepare [(c/decl "wrap" [(c/p 1 "object")] "object"
                             (c/let-ir 2 "object" (c/ctor 1 [(c/v 1)] 0) (c/ret 2)))] false)
        parent (j/machine ctx)
        root (loop [n 5000 value 0]
               (if (zero? n) value (recur (dec n) (j/call ctx parent "wrap" [value]))))
        {:keys [engine roots]} (fork! ctx parent [root])]
    (loop [a root b (first roots) n 0]
      (if (= a 0) (is (= 5000 n))
        (do (is (not (identical? a b)))
            (recur (aget (fields ctx a) 0) (aget (fields ctx b) 0) (inc n)))))
    (j/release! ctx parent root) (j/release! ctx engine (first roots))
    (j/close! ctx parent) (j/close! ctx engine)))

(deftest closed-and-failed-forks-reject-without-transfer
  (let [ctx (prepare [(c/decl "trap" [(c/p 1 "object")] "object" ["unreachable"])] true)
        closed (j/machine ctx) failed (j/machine ctx)]
    (j/close! ctx closed)
    (is (re-find #"boundary" (c/failure #(fork! ctx closed []))))
    (j/start! ctx failed "trap" [0])
    (is (re-find #"Unreachable" (c/failure #(j/advance! ctx failed 1))))
    (is (re-find #"boundary" (c/failure #(fork! ctx failed [])))))
  (let [ctx (prepare [(c/decl "trap" [(c/p 1 "object")] "object" ["unreachable"])] false)
        engine (j/machine ctx)]
    (is (re-find #"Unreachable" (c/failure #(j/call ctx engine "trap" [0]))))
    (is (re-find #"boundary" (c/failure #(fork! ctx engine []))))
    (j/close! ctx engine))
  (let [ctx (binding [x/*basis* (assoc *basis* :explicit true)]
              (x/prepare [((x/originals) "Nat.pow")]))
        engine (j/machine ctx)]
    (is (re-find #"exponent" (c/failure #(j/start! ctx engine "Nat.pow" [2 4294967296]))))
    (is (re-find #"boundary" (c/failure #(fork! ctx engine []))))
    (j/close! ctx engine)))

(deftest advancing-and-recursive-stack-guards-are-conservative
  (let [ctx (prepare [(c/object-constant "child")] false) engine (j/machine ctx)
        advancing (.getDeclaredField ^Class (:class ctx) "advancing")
        sp (.getDeclaredField ^Class (:class ctx) "sp")]
    (.setAccessible advancing true) (.setAccessible sp true)
    (try
      (.setBoolean advancing engine true)
      (is (re-find #"boundary" (c/failure #(fork! ctx engine []))))
      (.setBoolean advancing engine false)
      (.setInt sp engine 1)
      (is (re-find #"boundary" (c/failure #(fork! ctx engine []))))
      (finally (.setInt sp engine 0) (.setBoolean advancing engine false) (j/close! ctx engine)))))

(deftest unsupported-primitive-array-roots-leave-parent-usable
  (let [ctx (prepare [(c/object-constant "child")] true) parent (j/machine ctx)
        root (j/call ctx parent "child" []) before (counters ctx parent)]
    (doseq [unsupported [(.get ^Field (:scalars ctx) root)
                         (private-field ctx parent "numbers")]]
      (is (re-find #"outside.*profile" (c/failure #(fork! ctx parent [unsupported]))))
      (is (= before (counters ctx parent)))
      (is (= 2 (c/rc ctx root)))
      (is (= "idle" (j/phase ctx parent))))
    (let [again (j/call ctx parent "child" [])]
      (is (identical? root again)) (j/release! ctx parent again))
    (let [{:keys [engine roots]} (fork! ctx parent [root])]
      (is (= 2 (c/rc ctx (first roots))))
      (j/release! ctx engine (first roots)) (j/close! ctx engine))
    (j/release! ctx parent root) (j/close! ctx parent)))

(deftest live-rc-zero-node-still-clones-owned-descendants
  (let [ctx (prepare [(c/object-constant "child")
                      (c/decl "wrap" [(c/p 1 "object")] "object"
                              (c/let-ir 2 "object" (c/ctor 1 [(c/v 1)] 0) (c/ret 2)))] false)
        parent (j/machine ctx) leaf (j/call ctx parent "child" [])
        root (j/call ctx parent "wrap" [leaf])]
    ;; Model a live persistent header. The child edge remains an owner; RC0
    ;; must not make the graph copier stop traversing fields.
    (.setInt ^Field (:rc ctx) root 0)
    (let [{:keys [engine roots]} (fork! ctx parent [root])
          copy (first roots) cloned-leaf (aget (fields ctx copy) 0)
          cached (j/call ctx engine "child" [])]
      (is (= 0 (c/rc ctx root) (c/rc ctx copy)))
      (is (not (identical? root copy)))
      (is (not (identical? leaf cloned-leaf)))
      (is (identical? cloned-leaf cached))
      (is (= 2 (c/rc ctx leaf)))
      (j/release! ctx engine cached)
      (is (= 2 (c/rc ctx cloned-leaf)))
      ;; Restore fixture headers solely to discharge the test's owners.
      (.setInt ^Field (:rc ctx) root 1) (.setInt ^Field (:rc ctx) copy 1)
      (j/release! ctx parent root) (j/release! ctx engine copy)
      (is (= 1 (c/rc ctx leaf) (c/rc ctx cloned-leaf)))
      (j/close! ctx parent) (j/close! ctx engine))))

(defn check! [basis] (binding [*basis* basis] (run-tests 'java-ir-fork-checks)))
