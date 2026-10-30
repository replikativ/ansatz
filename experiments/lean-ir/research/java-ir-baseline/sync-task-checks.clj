(ns java-ir-sync-task-checks
  "Logical synchronous runtime foundation; pending callbacks are not enabled yet."
  (:require [clojure.test :refer [deftest is run-tests]]
            [clojure.data.json :as json] [lean-compatibility-corpus :as corpus]
            [java-ir-baseline :as j] [java-ir-baseline-checks :as c]
            [java-ir-extern-checks :as x] [java-ir-host-checks :as host]
            [java-ir-generation-checks :as g] [java-ir-array-checks :as array]
            [java-ir-task-map-checks :as task]
            [java-ir-ref-checks :as ref] [java-ir-release-order-checks :as order]))
(def ^:dynamic *basis* nil)
(defn active [ctx] (assoc ctx :explicit true :task-runtime (j/logical-sync-task-runtime ctx)))
(defn context []
  (active (assoc *basis* :program (j/invoke-static (:prepare *basis*)
    [(vec (concat (map #(get % "row") (array/originals))
                  (map #(get % "row") (ref/originals)) task/task-rows
                  (x/raw [(c/decl "cons" [(c/p 1 "object")] "object"
                             (c/let-ir 2 "object" (c/ctor 1 [(c/v 1)] 0) (c/ret 2)))
                          (c/decl "pair" [(c/p 1 "object") (c/p 2 "object")] "object"
                             (c/let-ir 3 "object" (c/ctor 2 [(c/v 1) (c/v 2)] 0) (c/ret 3)))
                          (c/decl "drop" [(c/p 1 "object") (c/p 2 "object")] "object"
                             ["dec" {:idx 1} 1 true false (c/ret 2)])
                          (c/object-constant "cached")])))]))))
(defn finish! [ctx engine]
  (loop [left 100000]
    (when (zero? left) (throw (ex-info "Action did not finish" {})))
    (if (j/advance! ctx engine 1) (j/take-result! ctx engine) (recur (dec left)))))
(defn release! [ctx engine value]
  (j/start-release! ctx engine value 1) (finish! ctx engine))
(defn close! [ctx engine]
  (j/start-dispose! ctx engine) (finish! ctx engine) (j/close! ctx engine))
(defn action [engine] (host/private-value engine "runtimeAction"))

(deftest activation-is-explicit-and-dec-close-never-start-effects
  (let [ctx (context) engine (j/machine ctx) value (order/cons! ctx engine 42)]
    (is (g/bad? #(j/machine (assoc ctx :explicit false))))
    (is (g/bad? #(j/release! ctx engine value))) (is (= 1 (c/rc ctx value)))
    (is (g/bad? #(j/close! ctx engine))) (is (= "idle" (j/phase ctx engine)))
    (is (= 0 (release! ctx engine value))) (is (order/dead? value))
    (close! ctx engine)))

(deftest root-release-action-batches-forks-and-resumes-without-source-function-invention
  (let [ctx (context) parent (j/machine ctx)
        a (order/cons! ctx parent 1) b (order/cons! ctx parent 2) root (order/pair! ctx parent a b)]
    (j/start-release! ctx parent root 1)
    (is (order/dead? root)) (is (= 1 (c/rc ctx a) (c/rc ctx b)))
    (is (false? (j/advance! ctx parent 0)))
    (j/advance! ctx parent 1) (is (= 0 (c/rc ctx a))) (is (= 1 (c/rc ctx b)))
    (let [{:keys [engine roots]} (j/fork! ctx parent [root a b]) child engine [cr ca cb] roots]
      (is (not (identical? cr root))) (is (= 0 (c/rc ctx ca))) (is (= 1 (c/rc ctx cb)))
      (is (= 0 (finish! ctx parent) (finish! ctx child)))
      (is (every? order/dead? [root a b cr ca cb]))
      (is (nil? (action parent))) (is (nil? (action child)))
      (close! ctx parent) (close! ctx child))))

(deftest quiet-native-helper-release-finishes-inline-with-no-release-action
  (let [ctx (context) engine (j/machine ctx) value (order/cons! ctx engine 7)
        array (array/push! ctx engine (array/empty! ctx engine 1) value)
        old (order/cons! ctx engine 8) new (order/cons! ctx engine 9)
        cell (ref/make-ref! ctx engine old)]
    (is (identical? array (array/pop! ctx engine array)))
    (is (order/dead? value)) (is (= 0 (array/size array)))
    (is (nil? (action engine))) (is (nil? (host/private-value engine "quietCurrent")))
    (is (= 0 (ref/ref-set! ctx engine cell new)))
    (is (order/dead? old)) (is (identical? new (first (ref/fields ctx cell))))
    (release! ctx engine cell) (release! ctx engine array)
    (is (order/dead? new)) (close! ctx engine)))

(deftest claimed-host-reply-keeps-borrowed-credit-until-action-drains
  (let [ctx (active (binding [host/*basis* *basis*]
                      (host/prepare [(host/ext "host" host/borrowed)
                                     (c/decl "cons" [(c/p 1 "object")] "object"
                                       (c/let-ir 2 "object" (c/ctor 1 [(c/v 1)] 0) (c/ret 2)))] [host/borrowed])))
        parent (j/machine ctx) value (order/cons! ctx parent 7)]
    (j/start! ctx parent "host" [value])
    (let [request (j/host-request ctx parent)]
      (is (g/bad? #(j/resume-host! ctx parent request nil))) (is (= 1 (c/rc ctx value)))
      (j/resume-host! ctx parent request 41)
      (is (= "running" (j/phase ctx parent))) (is (= 1 (c/rc ctx value)))
      (is (true? (host/private-value (host/private-value parent "hostCompletion") "replyClaimed")))
      (j/advance! ctx parent 1) (is (= 0 (c/rc ctx value)))
      (let [{:keys [engine roots]} (j/fork! ctx parent [value]) child engine [copy] roots]
        (is (= 41 (finish! ctx parent) (finish! ctx child)))
        (is (order/dead? value)) (is (order/dead? copy))
        (is (nil? (host/private-value parent "hostCompletion")))
        (close! ctx parent) (close! ctx child)))))

(deftest cache-disposal-is-explicit-and-retired-entry-cannot-replay
  (let [ctx (context) parent (j/machine ctx) value (j/call ctx parent "cached" [])]
    (is (= 2 (c/rc ctx value))) (release! ctx parent value) (is (= 1 (c/rc ctx value)))
    (j/start-dispose! ctx parent)
    (let [{:keys [engine roots]} (j/fork! ctx parent [value]) child engine [copy] roots]
      (is (= 0 (finish! ctx parent) (finish! ctx child)))
      (is (order/dead? value)) (is (order/dead? copy))
      (is (g/bad? #(j/start! ctx parent "cached" [])))
      (is (g/bad? #(j/start-dispose! ctx parent)))
      (j/close! ctx parent) (j/close! ctx child))))

(deftest disposal-rejects-untracked-terminal-failure-before-moving-any-owner
  (let [ctx (context) engine (j/machine ctx) value (order/cons! ctx engine 7)]
    (is (g/bad? #(j/call ctx engine "ST.Prim.mkRef" [0 0 nil 0])))
    (is (true? (host/private-value engine "untrackedFailure")))
    (is (= "idle" (j/phase ctx engine)))
    (let [before (mapv #(host/private-value engine %) ["allocations" "releases" "retains"])]
      (is (g/bad? #(j/start-dispose! ctx engine)))
      (is (= before (mapv #(host/private-value engine %) ["allocations" "releases" "retains"])))
      (is (= 1 (c/rc ctx value))) (is (nil? (action engine))))))

(deftest deeply-nested-ready-release-is-iterative-quiet-and-budget-fork-safe
  (let [ctx (context) parent (j/machine ctx)
        deep (loop [i 0 value 7]
               (if (= i 6000) value (recur (inc i) (task/pure ctx parent value))))]
    (j/start-release! ctx parent deep 1)
    (is (false? (j/advance! ctx parent 4000)))
    (is (= 0 (j/depth ctx parent)))
    (let [{:keys [engine]} (j/fork! ctx parent [deep]) child engine]
      (is (= 0 (finish! ctx parent) (finish! ctx child)))
      (let [quiet (loop [i 0 value 8]
                    (if (= i 6000) value (recur (inc i) (task/pure ctx parent value))))]
        (is (= 42 (j/call ctx parent "drop" [quiet 42])))
        (is (nil? (action parent))) (is (order/dead? quiet)))
      (close! ctx parent) (close! ctx child))))

(defn private-set! [target label value]
  (let [f (.getDeclaredField (class target) label)] (.setAccessible f true) (.set f target value)))
(defn record-chain [ctx class-name field n]
  (let [cls (.loadClass (:loader ctx) (str "ansatz.research.ir.Interpreter$" class-name))
        ctor (.getDeclaredConstructor cls (make-array Class 0))]
    (.setAccessible ctor true)
    (loop [i 0 head nil]
      (if (= i n) head
        (let [next (.newInstance ctor (object-array 0))]
          (private-set! next field head) (recur (inc i) next))))))
(defn chain-count [head field]
  (loop [node head n 0]
    (if node (recur (host/private-value node field) (inc n)) n)))
(deftest model-deep-action-and-completion-records-copy-without-recursive-java-frames
  ;; Structural private-state model only; no synthetic guest finalizers or host
  ;; effects. The public ready-chain test above exercises reachable execution.
  (let [ctx (context) parent (j/machine ctx)
        actions (record-chain ctx "RuntimeAction" "parent" 12000)
        completions (record-chain ctx "HostCall" "previousCompletion" 12000)]
    (private-set! parent "runtimeAction" actions) (private-set! parent "hostCompletion" completions)
    (let [{:keys [engine]} (j/fork! ctx parent []) child engine]
      (is (= 12000 (chain-count (action child) "parent")))
      (is (= 12000 (chain-count (host/private-value child "hostCompletion") "previousCompletion")))
      (is (not (identical? actions (action child))))
      (doseq [e [parent child]]
        (private-set! e "runtimeAction" nil) (private-set! e "hostCompletion" nil) (close! ctx e)))))

(deftest exact-original-task-closure-provenance-does-not-imply-execution-support
  (let [path "test/fixtures/java-task-sync-runtime/"
        rows (json/read-str (slurp (str path "original-rows.json")))
        roots (json/read-str (slurp (str path "root-names.json")))
        provenance (json/read-str (slurp (str path "provenance.json")))
        names (set (map #(get-in % ["row" "name"]) rows))]
    (is (= 60 (count rows) (count names))) (is (= 50 (count roots)))
    (is (= "5f80a94832d953b1eb00820991a56fb6acedcaf68134ae8f10b28e5726a6d950"
           (corpus/sha256 (str path "original-rows.json")))
        "Original closure has one separately pinned derived fixture hash")
    (is (= "819816b2e0a3bf405af45ae5c7af2491d8f5bee6" (get provenance "lean-commit")))
    (is (every? names roots))
    (is (every? names (mapcat #(get-in % ["row" "dependencies"]) rows)))
    (is (re-find #"Unsupported baseline extern: lean_io_promise_new"
                 (c/failure #(j/invoke-static (:prepare *basis*) [(mapv (fn [r] (get r "row")) rows)]))))))

(deftest failed-release-keeps-current-cursor-queued-shell-and-owner-fields
  (let [ctx (context) engine (j/machine ctx) a (order/cons! ctx engine 7)
        bad (order/cons! ctx engine 8) root (order/pair! ctx engine a bad)]
    ;; Deliberately malformed borrowed alias, as in the existing terminal tests.
    (release! ctx engine bad)
    (j/start-release! ctx engine root 1) (j/advance! ctx engine 1)
    (is (g/bad? #(j/advance! ctx engine 1)))
    (is (= "failed" (j/phase ctx engine)))
    (let [record (action engine)]
      (is (identical? root (host/private-value record "current")))
      (is (= 1 (host/private-value record "cursor")))
      (is (= [a] (vec (take (host/private-value record "pending") (host/private-value record "work")))))
      (is (= [7] (vec (order/fields ctx a)))) (is (order/dead? a))
      (is (g/bad? #(j/fork! ctx engine []))) (is (g/bad? #(j/start-dispose! ctx engine)))
      (is (g/bad? #(j/close! ctx engine)))
      (is (identical? record (action engine))))))

(deftest disposal-closes-all-owner-creating-entry-points-before-claims
  (let [ctx (context) engine (j/machine ctx)
        graph (j/selected-owner-graph ctx (j/source-binding ctx (Object.)) (Object.) [] [] [] [])]
    (j/start-dispose! ctx engine) (is (= 0 (finish! ctx engine)))
    (let [before (mapv #(host/private-value engine %) ["allocations" "retains" "releases"])]
      (doseq [operation [#(j/start-release! ctx engine 0 0)
                         #(j/start! ctx engine "cons" [1])
                         #(j/retain! ctx engine 0)
                         #(j/make-closure! ctx engine "cons" [])
                         #(j/install-program! ctx engine)
                         #(j/install-graph! ctx engine graph)
                         #(j/finish-initialization! ctx engine)
                         #(j/fork! ctx engine [])]]
        (is (g/bad? operation)))
      (is (= before (mapv #(host/private-value engine %) ["allocations" "retains" "releases"])))
      (is (= "idle" (j/phase ctx engine))))
    (j/close! ctx engine) (j/close! ctx engine)))

(defn check! [basis] (binding [*basis* basis] (run-tests 'java-ir-sync-task-checks)))
