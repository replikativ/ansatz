(ns java-ir-sync-task-checks
  "Explicit logical synchronous tasks, native release boundaries and request/fork control."
  (:require [clojure.test :refer [deftest is run-tests]]
            [clojure.data.json :as json] [lean-compatibility-corpus :as corpus]
            [java-ir-baseline :as j] [java-ir-baseline-checks :as c]
            [java-ir-extern-checks :as x] [java-ir-host-checks :as host]
            [java-ir-generation-checks :as g] [java-ir-array-checks :as array]
            [java-ir-header-checks :as headers] [java-ir-code-checks :as code]
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
    (is (some? (j/invoke-static (:prepare *basis*) [(mapv #(get % "row") rows)])))))

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

(defn task-context
  ([] (task-context [] []))
  ([extra descriptors]
   (let [rows (concat (map #(get % "row") (json/read-str (slurp "test/fixtures/java-task-sync-runtime/original-rows.json")))
                      (map #(get % "row") (ref/originals)) (map #(get % "row") (array/originals))
                      (x/raw (concat [(c/decl "cons" [(c/p 1 "object")] "object"
                                        (c/let-ir 2 "object" (c/ctor 1 [(c/v 1)] 0) (c/ret 2)))
                                     (c/decl "identity" [(c/p 1 "object")] "object" (c/ret 1))
                                     (c/decl "keepIO" [(c/p 1 "object") (c/p 2 "object")] "object" (c/ret 1))]
                                    extra)))
         table (java.util.LinkedHashMap.)]
     (doseq [row rows] (.putIfAbsent table (get row "name") row))
     (active (j/prepare-host-program *basis* (vec (.values table)) descriptors)))))
(defn promise! [ctx engine] (j/call ctx engine "IO.Promise.new._boxed" [0 0 0]))
(defn result-task! [ctx engine promise]
  (j/retain! ctx engine promise) (j/call ctx engine "IO.Promise.result?._boxed" [0 promise]))
(defn resolve! [ctx engine promise value]
  (j/retain! ctx engine promise) (j/call ctx engine "IO.Promise.resolve._boxed" [0 value promise 0]))
(defn task-state [ctx engine task]
  (j/retain! ctx engine task) (j/call ctx engine "IO.getTaskState._boxed" [0 task 0]))
(defn get! [ctx engine task] (j/call ctx engine "Task.get" [0 task]))
(defn map! [ctx engine callback source]
  (j/call ctx engine "Task.map" [0 0 callback source 0 1]))
(defn io-map! [ctx engine callback source]
  (j/call ctx engine "BaseIO.mapTask" [0 0 callback source 0 1 0]))

(deftest original-promise-alias-first-write-losing-payload-and-drop-none
  (let [ctx (task-context) engine (j/machine ctx) p (promise! ctx engine)
        a (result-task! ctx engine p) b (result-task! ctx engine p)]
    (is (identical? a b)) (is (= 3 (c/rc ctx a))) (is (= 1 (task-state ctx engine a)))
    (is (= 0 (resolve! ctx engine p 7))) (is (= 2 (task-state ctx engine a)))
    (let [loser (order/cons! ctx engine 8)]
      (is (= 0 (resolve! ctx engine p loser))) (is (order/dead? loser)))
    (let [some (get! ctx engine a)]
      (is (= 1 (.getInt ^java.lang.reflect.Field (:tag ctx) some)))
      (is (= [7] (vec (order/fields ctx some)))) (release! ctx engine some))
    (release! ctx engine b) (release! ctx engine p)
    (let [p (promise! ctx engine) task (result-task! ctx engine p)]
      (release! ctx engine p) (is (= 2 (task-state ctx engine task)))
      (is (= 0 (get! ctx engine task))))
    (close! ctx engine)))

(deftest pure-pending-map-last-owner-unlinks-without-running-callback
  (let [spec (host/spec "record" ["object"] [false] "object")
        ctx (task-context [(host/ext "record" spec)] [spec]) engine (j/machine ctx)
        p (promise! ctx engine) source (result-task! ctx engine p)
        callback (j/make-closure! ctx engine "record" []) dependent (map! ctx engine callback source)]
    (is (= 0 (task-state ctx engine dependent))) (is (= 1 (c/rc ctx dependent)))
    (release! ctx engine dependent) (is (order/dead? dependent)) (is (order/dead? callback))
    (is (= 0 (resolve! ctx engine p 7))) (is (nil? (j/host-request ctx engine)))
    (release! ctx engine p) (close! ctx engine)))

(deftest pending-baseio-keepalive-host-callback-pauses-and-forks-at-action-receiver
  (let [spec (host/spec "record_io" ["object" "object"] [false false] "object")
        ctx (task-context [(host/ext "recordIO" spec)] [spec]) parent (j/machine ctx)
        p (promise! ctx parent) source (result-task! ctx parent p)
        callback (j/make-closure! ctx parent "recordIO" []) dependent (io-map! ctx parent callback source)]
    (is (= 2 (c/rc ctx dependent))) (release! ctx parent dependent) (is (= 1 (c/rc ctx dependent)))
    (j/retain! ctx parent p) (j/start! ctx parent "IO.Promise.resolve._boxed" [0 7 p 0])
    (let [request (host/request! ctx parent) args (host/args request)
          {:keys [engine roots]} (j/fork! ctx parent [p dependent]) child engine [cp cd] roots]
      (is (= 0 (second args))) (is (= [7] (vec (order/fields ctx (first args)))))
      (is (g/bad? #(j/resume-host! ctx child request 0)))
      ;; Handler consumes its owned Some input; release itself is a serialized
      ;; guest operation, so this fixture transfers that Some back as the reply.
      (j/resume-host! ctx parent request (first args))
      (let [cr (j/host-request ctx child)] (j/resume-host! ctx child cr (first (host/args cr))))
      (is (= 0 (finish! ctx parent) (finish! ctx child)))
      (is (order/dead? dependent)) (is (order/dead? cd))
      (is (= 1 (c/rc ctx p) (c/rc ctx cp)))
      (release! ctx parent p) (release! ctx child cp) (close! ctx parent) (close! ctx child))))

(deftest ready-map-and-bind-use-original-wrappers-and-bind-preserves-identity
  (let [ctx (task-context) engine (j/machine ctx)
        p (promise! ctx engine) pending (result-task! ctx engine p)
        source (task/pure ctx engine pending)
        callback (j/make-closure! ctx engine "identity" [])
        result (j/call ctx engine "Task.bind" [0 0 source callback 0 1])]
    (is (identical? pending result)) (is (= 1 (task-state ctx engine result)))
    (release! ctx engine result) (release! ctx engine p)
    (let [value (order/cons! ctx engine 7) source (task/pure ctx engine value)
          mapped (j/call ctx engine "Task.map._boxed" [0 0 (j/make-closure! ctx engine "identity" []) source 0 1])]
      (is (identical? value (get! ctx engine mapped))) (release! ctx engine value))
    (close! ctx engine)))

(def task-names (into {} (map (fn [r] [(get r "label") (get-in r ["row" "name"])])
                            (json/read-str (slurp "test/fixtures/java-task-sync-runtime/original-rows.json")))))
(defn sfap [label args] {:fap {:c (or (task-names label) (throw (ex-info "Missing genuine Name" {:label label}))) :ys args}})
(defn drive-host! [ctx engine handler]
  (loop [left 100000]
    (when (zero? left) (throw (ex-info "Host drive exhausted" {})))
    (if-let [request (j/host-request ctx engine)]
      (do (j/resume-host! ctx engine request (handler request)) (recur (dec left)))
      (if (j/advance! ctx engine 3) (j/take-result! ctx engine) (recur (dec left))))))
(defn quiescent? [ctx engine]
  (.invoke (.getMethod ^Class (:class ctx) "taskRuntimeQuiescent" (make-array Class 0)) engine (object-array 0)))

(deftest original-cancel-token-set-runs-onset-before-ref-flag-write
  (let [spec (host/spec "observe" ["object"] [false] "object")
        observe (c/decl "observe-token" [(c/p 1 "object") (c/p 2 "object")] "object"
                  (c/let-ir 3 "uint8" (sfap "IO.CancelToken.isSet" [(c/v 1) (c/v 2)])
                    ["dec" {:idx 1} 1 true false
                     (c/let-ir 4 "object" {:box {:ty "uint8" :x {:idx 3}}}
                       (c/let-ir 5 "object" (c/fap "observe" [(c/v 4)]) (c/ret 5)))]))
        ctx (task-context [(host/ext "observe" spec) observe] [spec]) engine (j/machine ctx)
        token (j/call ctx engine "IO.CancelToken.new._boxed" [0])]
    (j/retain! ctx engine token)
    (let [callback (j/make-closure! ctx engine "observe-token" [token])]
      (j/retain! ctx engine token)
      (is (= 0 (j/call ctx engine "IO.CancelToken.onSet._boxed" [token callback 0])))
      (is (false? (quiescent? ctx engine)))
      (j/retain! ctx engine token) (j/start! ctx engine "IO.CancelToken.set._boxed" [token 0])
      (let [observed (atom [])]
        (is (= 0 (drive-host! ctx engine #(do (swap! observed conj (first (host/args %))) 0))))
        (is (= [0] @observed))))
    (j/retain! ctx engine token) (is (= 1 (j/call ctx engine "IO.CancelToken.isSet._boxed" [token 0])))
    (is (quiescent? ctx engine)) (release! ctx engine token) (close! ctx engine)))

(deftest detached-registration-batch-is-lifo-and-later-entry-can-be-deleted
  (let [spec (host/spec "record_label" ["object" "object"] [false false] "object")
        ctx (task-context [(host/ext "record-label" spec)] [spec]) engine (j/machine ctx)
        p (promise! ctx engine)
        dependencies (mapv (fn [n] (map! ctx engine (j/make-closure! ctx engine "record-label" [n])
                                          (result-task! ctx engine p))) [1 2 3])
        log (atom [])]
    (j/retain! ctx engine p) (j/start! ctx engine "IO.Promise.resolve._boxed" [0 7 p 0])
    (is (= 0 (drive-host! ctx engine #(let [[label value] (host/args %)] (swap! log conj label) value))))
    (is (= [3 2 1] @log))
    (doseq [d dependencies] (release! ctx engine d)) (release! ctx engine p) (close! ctx engine))
  (let [spec (host/spec "later" ["object"] [false] "object")
        killer (c/decl "kill-later" [(c/p 1 "object") (c/p 2 "object")] "object"
                 ["dec" {:idx 1} 1 true false (c/ret 2)])
        ctx (task-context [(host/ext "later" spec) killer] [spec]) engine (j/machine ctx)
        p (promise! ctx engine)
        later (map! ctx engine (j/make-closure! ctx engine "later" []) (result-task! ctx engine p))
        first (map! ctx engine (j/make-closure! ctx engine "kill-later" [later]) (result-task! ctx engine p))]
    (is (= 0 (resolve! ctx engine p 7))) (is (order/dead? later))
    (is (nil? (j/host-request ctx engine)))
    (release! ctx engine first) (release! ctx engine p) (close! ctx engine)))

(deftest sibling-promise-finalizers-run-after-entire-native-field-batch-and-fork
  (let [spec (host/spec "sibling" ["object" "object" "object"] [false false false] "object")
        pair (c/decl "pair" [(c/p 1 "object") (c/p 2 "object")] "object"
                    (c/let-ir 3 "object" (c/ctor 2 [(c/v 1) (c/v 2)] 0) (c/ret 3)))
        ctx (task-context [(host/ext "sibling" spec) pair] [spec]) parent (j/machine ctx)
        p1 (promise! ctx parent) p2 (promise! ctx parent)
        a (io-map! ctx parent (j/make-closure! ctx parent "sibling" [1]) (result-task! ctx parent p1))
        b (io-map! ctx parent (j/make-closure! ctx parent "sibling" [2]) (result-task! ctx parent p2))
        root (order/pair! ctx parent p1 p2)]
    (release! ctx parent a) (release! ctx parent b)
    (j/start-release! ctx parent root 1)
    (let [request (host/request! ctx parent)
          {:keys [engine]} (j/fork! ctx parent []) child engine]
      (is (= [2 0 0] (host/args request)))
      (is (order/dead? p1)) (is (order/dead? p2))
      (is (= [nil nil] (vec (order/fields ctx root))))
      (doseq [e [parent child]]
        (let [log (atom [])]
          (is (= 0 (drive-host! ctx e #(let [[label value] (host/args %)] (swap! log conj label) value))))
          (is (= [2 1] @log)))
        (is (quiescent? ctx e)) (close! ctx e)))))

(deftest pending-bind-keeps-outer-identity-and-baseio-credit-until-forwarding-finishes
  (doseq [io? [false true]]
    (let [callback (c/decl "return-task" (mapv #(c/p % "object") (if io? [1 2 3] [1 2])) "object"
                             ["dec" {:idx 2} 1 true false (c/ret 1)])
          ctx (task-context [callback] []) engine (j/machine ctx)
          p (promise! ctx engine) q (promise! ctx engine) nested (result-task! ctx engine q)
          cb (j/make-closure! ctx engine "return-task" [nested])
          outer (j/call ctx engine (if io? "BaseIO.bindTask" "Task.bind")
                        (cond-> [0 0 (result-task! ctx engine p) cb 0 1] io? (conj 0)))]
      (when io? (release! ctx engine outer))
      (is (= 0 (resolve! ctx engine p 1)))
      (if io? (is (true? (host/private-value (get (host/private-value engine "taskRecords") outer) "keepalive")))
          (is (= 0 (task-state ctx engine outer))))
      (when io? (is (false? (quiescent? ctx engine))))
      (is (= 0 (resolve! ctx engine q 9)))
      (if io? (is (order/dead? outer))
        (let [value (get! ctx engine outer)] (is (= [9] (vec (order/fields ctx value)))) (release! ctx engine value)))
      (release! ctx engine p) (release! ctx engine q) (close! ctx engine))))

(deftest promise-callback-code-activation-is-claimed-once-and-forks-before-materialization
  (let [base (task-context) binding (j/source-binding base (Object.))
        row (c/decl "demanded-callback" [(c/p 1 "object")] "object" (c/ret 1))
        header (headers/header binding row) ctx (j/register-headers base [header])
        ready (code/materialize ctx header row []) parent (j/machine ctx)
        p (promise! ctx parent)
        mapped (map! ctx parent (j/make-closure! ctx parent "demanded-callback" []) (result-task! ctx parent p))]
    (j/retain! ctx parent p) (j/start! ctx parent "IO.Promise.resolve._boxed" [0 7 p 0])
    (let [request (code/request! ctx parent) arguments (code/args request)
          {:keys [engine roots]} (j/fork! ctx parent [p mapped]) child engine [cp cm] roots
          child-request (j/code-request ctx child)]
      (is (= [[7]] (mapv #(vec (order/fields ctx %)) arguments)))
      (is (g/bad? #(j/resume-code! ctx parent request)))
      (is (identical? request (j/code-request ctx parent)))
      (is (g/bad? #(j/resume-code! ready child request)))
      (j/resume-code! ready parent request) (j/resume-code! ready child child-request)
      (is (= 0 (finish! ready parent) (finish! ready child)))
      (doseq [[e promise dep] [[parent p mapped] [child cp cm]]]
        (let [value (get! ready e dep)] (is (= [7] (vec (order/fields ready value)))) (release! ready e value))
        (release! ready e promise) (is (quiescent? ready e)) (close! ready e)))))

(deftest outer-claimed-host-scalar-survives-promise-cleanup-inner-request-fork-and-failure
  (let [outer (host/spec "outer_cleanup" ["object" "object"] [true true] "float")
        inner (host/spec "inner_cleanup" ["object" "object"] [false false] "object")
        ctx (task-context [(host/ext "outer" outer) (host/ext "inner" inner)] [outer inner])
        parent (j/machine ctx) p (promise! ctx parent) later (order/cons! ctx parent 7)
        dependent (io-map! ctx parent (j/make-closure! ctx parent "inner" []) (result-task! ctx parent p))
        bits (long 0x7ff8000000001234) reply (Double/longBitsToDouble bits)]
    (release! ctx parent dependent)
    (j/start! ctx parent "outer" [p later])
    (let [a (j/host-request ctx parent)]
      (j/resume-host! ctx parent a reply)
      (let [b (host/request! ctx parent) outer-call (host/private-value parent "hostCompletion")
            {:keys [engine roots]} (j/fork! ctx parent [later]) child engine [child-later] roots
            failed (:engine (j/fork! ctx parent []))]
        (is (= "inner_cleanup" (j/request-value b "symbol")))
        (is (= 0 (host/private-value outer-call "borrowedCursor")))
        (is (true? (host/private-value outer-call "adapterReleaseStarted")))
        (is (= bits (host/private-value outer-call "completionScalar")))
        (is (= 1 (c/rc ctx later) (c/rc ctx child-later)))
        (is (g/bad? #(j/resume-host! ctx parent b nil))) (is (identical? b (j/host-request ctx parent)))
        (let [f (j/host-request ctx failed)]
          (j/fail-host! ctx failed f (ex-info "deliberate nested failure" {}))
          (is (= "failed" (j/phase ctx failed)))
          (is (some? (host/private-value (host/private-value failed "hostCompletion") "previousCompletion")))
          (is (g/bad? #(j/start-dispose! ctx failed))) (is (g/bad? #(j/close! ctx failed))))
        (doseq [e [parent child]]
          (j/resume-host! ctx e (j/host-request ctx e) 0)
          (is (= bits (Double/doubleToRawLongBits (double (finish! ctx e)))))
          (is (quiescent? ctx e)) (close! ctx e))
        (is (order/dead? later)) (is (order/dead? child-later))))))

(deftest pending-map-callback-intrinsic-partial-and-io-overapplication-share-action-receiver
  (let [world-reply (c/decl "world-reply" [(c/p 1 "object") (c/p 2 "object")] "object" (c/ret 1))
        curried (c/decl "curried-io" [(c/p 1 "object")] "object"
                       (c/let-ir 2 "object" {:pap {:c (c/name-ir "world-reply") :ys [(c/v 1)]}} (c/ret 2)))
        ctx (task-context [world-reply curried] []) engine (j/machine ctx)]
    (doseq [[label captures io?] [["Task.pure" [0] false] ["world-reply" [] false] ["curried-io" [] true]]]
      (let [p (promise! ctx engine) cb (j/make-closure! ctx engine label captures)
            dep ((if io? io-map! map!) ctx engine cb (result-task! ctx engine p))]
        (is (= 0 (resolve! ctx engine p 7)))
        (let [value (get! ctx engine dep)]
          (is (instance? (:node-class ctx) value))
          (release! ctx engine value))
        (release! ctx engine p)))
    (close! ctx engine)))

(defn cancel! [ctx engine task]
  (j/retain! ctx engine task) (j/call ctx engine "IO.cancel._boxed" [0 task 0]))
(defn scope-probe-row []
  (c/decl "scope-probe" [(c/p 1 "object")] "object"
    (c/let-ir 2 "uint8" (sfap "IO.checkCanceled" ["erased"])
      ["dec" {:idx 1} 1 true false
       (c/let-ir 3 "object" {:box {:ty "uint8" :x {:idx 2}}}
         (c/let-ir 4 "object" (c/fap "scope-host" [(c/v 3)]) (c/ret 4)))])))

(deftest cancellation-is-flag-only-propagates-on-finish-and-inline-scope-is-inherited
  (let [spec (host/spec "scope_host" ["object"] [false] "object")
        ctx (task-context [(host/ext "scope-host" spec) (scope-probe-row)] [spec]) engine (j/machine ctx)]
    (doseq [cancel-source? [true false]]
      (let [p (promise! ctx engine) source (result-task! ctx engine p)
            _ (j/retain! ctx engine source)
            dependent (map! ctx engine (j/make-closure! ctx engine "scope-probe" []) source)]
        (is (= 0 (cancel! ctx engine (if cancel-source? source dependent))))
        (is (= 1 (task-state ctx engine source))) (is (= 0 (task-state ctx engine dependent)))
        (is (nil? (j/host-request ctx engine)))
        (j/retain! ctx engine p) (j/start! ctx engine "IO.Promise.resolve._boxed" [0 7 p 0])
        (let [log (atom [])]
          (is (= 0 (drive-host! ctx engine #(do (swap! log conj (first (host/args %))) 0))))
          (is (= [1] @log)))
        (release! ctx engine source) (release! ctx engine dependent) (release! ctx engine p)))
    (let [source (task/pure ctx engine 0) log (atom [])]
      (j/start! ctx engine "Task.map" [0 0 (j/make-closure! ctx engine "scope-probe" []) source 0 1])
      (let [mapped (drive-host! ctx engine #(do (swap! log conj (first (host/args %))) 0))]
        (is (= [0] @log)) (release! ctx engine mapped)))
    (is (= 0 (j/call ctx engine "IO.checkCanceled" [0])))
    (close! ctx engine)))

(defn drop-self-row [bind?]
  (let [take-id (if bind? 4 3)
        suffix (if bind? (c/ret 2)
                 (c/let-ir 4 "uint8" (sfap "IO.checkCanceled" ["erased"])
                   (c/let-ir 5 "object" {:box {:ty "uint8" :x {:idx 4}}}
                     (c/let-ir 6 "object" (c/fap "scope-host" [(c/v 5)]) (c/ret 6)))))
        take-name (get-in (first (filter #(= "ST.Prim.Ref.take" (get % "label")) (ref/originals))) ["row" "name"])]
    (c/decl "drop-current-task" (mapv #(c/p % "object") (if bind? [1 2 3] [1 2])) "object"
      (c/let-ir take-id "tobject" {:fap {:c take-name :ys ["erased" "erased" (c/v 1) "erased"]}}
        ["dec" {:idx take-id} 1 true false
         ["dec" {:idx 1} 1 true false
          ["dec" {:idx (if bind? 3 2)} 1 true false suffix]]]))))

(deftest running-pure-map-deactivation-finishes-callback-in-scope-and-discards-result
  (let [spec (host/spec "scope_host" ["object"] [false] "object")
        ctx (task-context [(host/ext "scope-host" spec) (drop-self-row false)] [spec]) engine (j/machine ctx)
        p (promise! ctx engine) holder (ref/make-ref! ctx engine 0)
        _ (j/retain! ctx engine holder)
        dependent (map! ctx engine (j/make-closure! ctx engine "drop-current-task" [holder]) (result-task! ctx engine p))]
    (ref/ref-set! ctx engine holder dependent)
    (j/retain! ctx engine p) (j/start! ctx engine "IO.Promise.resolve._boxed" [0 7 p 0])
    (let [request (host/request! ctx engine)]
      (is (order/dead? dependent)) (is (= [1] (host/args request)))
      (is (nil? (first (ref/fields ctx holder))))
      (j/resume-host! ctx engine request 0) (is (= 0 (finish! ctx engine))))
    (is (quiescent? ctx engine))
    (release! ctx engine holder) (release! ctx engine p) (close! ctx engine)))

(deftest deactivated-running-bind-pending-return-is-a-preserved-native-leak-boundary
  (let [ctx (task-context [(drop-self-row true)] []) engine (j/machine ctx)
        p (promise! ctx engine) q (promise! ctx engine) nested (result-task! ctx engine q)
        holder (ref/make-ref! ctx engine 0) _ (j/retain! ctx engine holder)
        callback (j/make-closure! ctx engine "drop-current-task" [holder nested])
        outer (j/call ctx engine "Task.bind" [0 0 (result-task! ctx engine p) callback 0 1])]
    (ref/ref-set! ctx engine holder outer)
    (is (re-find #"native leaked-capture boundary" (c/failure #(resolve! ctx engine p 7))))
    (is (= "failed" (j/phase ctx engine))) (is (order/dead? outer))
    (is (identical? nested (host/private-value (action engine) "output")))
    (is (= 2 (c/rc ctx nested)))
    (is (nil? (host/private-value (host/private-value (action engine) "task") "waiting")))
    (is (g/bad? #(j/start-dispose! ctx engine))) (is (g/bad? #(j/close! ctx engine)))))

(deftest disposal-releases-callback-created-earlier-cache-and-recreated-stdout
  (let [spec (host/spec "dispose_observe" ["object"] [true] "object")
        stdout (host/ext "stdout" (host/spec "lean_get_stdout" ["void"] [false] "object"))
        use (c/decl "dispose-callback" [(c/p 1 "object") (c/p 2 "object")] "object"
              ["dec" {:idx 1} 1 true false
               (c/let-ir 3 "object" (c/fap "new-cache" [])
                 (c/let-ir 4 "object" (c/fap "stdout" ["erased"])
                   ["dec" {:idx 4} 1 true false
                    (c/let-ir 5 "object" (c/fap "observe-disposal" [(c/v 3)]) (c/ret 5))]))])
        old (c/decl "old-cache" [] "object"
                   (c/let-ir 1 "tobject" (sfap "IO.Promise.new" ["erased" "erased" "erased"]) (c/ret 1)))
        ctx (task-context [(c/object-constant "new-cache") old stdout (host/ext "observe-disposal" spec) use] [spec])
        parent (j/machine ctx) promise (j/call ctx parent "old-cache" [])
        dependent (io-map! ctx parent (j/make-closure! ctx parent "dispose-callback" []) (result-task! ctx parent promise))]
    (release! ctx parent dependent) (release! ctx parent promise)
    (j/start-dispose! ctx parent)
    (let [request (host/request! ctx parent) cache (first (host/args request))
          stdout-root (host/private-value parent "stdoutRoot")
          {:keys [engine roots]} (j/fork! ctx parent [cache stdout-root]) child engine [cc cs] roots]
      (is (= 1 (c/rc ctx cache) (c/rc ctx stdout-root)))
      (doseq [e [parent child]]
        (j/resume-host! ctx e (j/host-request ctx e) 0)
        (is (= 0 (finish! ctx e))) (is (quiescent? ctx e))
        (is (nil? (host/private-value e "stdoutRoot")))
        (is (not-any? true? (seq (host/private-value e "constantReady"))))
        (j/close! ctx e))
      (is (every? order/dead? [cache stdout-root cc cs])))))

(deftest unresolved-baseio-keeps-disposal-waiting-with-exact-records-and-no-close
  (let [ctx (task-context) engine (j/machine ctx)
        p (promise! ctx engine) dependent (io-map! ctx engine (j/make-closure! ctx engine "keepIO" []) (result-task! ctx engine p))]
    ;; Deliberately violate the documented external-owner-before-disposal order
    ;; to check that the implementation reports retained work rather than success.
    (release! ctx engine dependent) (is (false? (quiescent? ctx engine)))
    (j/start-dispose! ctx engine)
    (loop [left 10000]
      (when (zero? left) (throw (ex-info "No waiting boundary" {})))
      (when-not (= "waiting" (j/phase ctx engine)) (j/advance! ctx engine 10) (recur (dec left))))
    (is (false? (j/advance! ctx engine 100))) (is (false? (quiescent? ctx engine)))
    (is (false? (host/private-value engine "disposed")))
    (is (= 1 (c/rc ctx p) (c/rc ctx dependent)))
    (is (g/bad? #(j/take-result! ctx engine))) (is (g/bad? #(j/close! ctx engine)))
    (let [{:keys [engine]} (j/fork! ctx engine [])]
      (is (= "waiting" (j/phase ctx engine))) (is (false? (j/advance! ctx engine 1))))))

(defn enclosing-native [engine]
  (loop [a (action engine)]
    (when a (if (= 3 (host/private-value a "operation")) a (recur (host/private-value a "parent"))))))
(defn watching-promise! [ctx engine]
  (let [p (promise! ctx engine)
        dependent (io-map! ctx engine (j/make-closure! ctx engine "watch" []) (result-task! ctx engine p))]
    (release! ctx engine dependent) p))

(deftest zero-replicate-native-root-fap-and-owned-ap-wait-for-finalizer-before-publishing
  (let [spec (host/spec "watch" ["object" "object"] [false false] "object")
        apply-one (c/decl "apply-one" [(c/p 1 "object") (c/p 2 "object")] "object"
                            (c/let-ir 3 "object" {:ap {:x {:idx 1} :ys [(c/v 2)]}} (c/ret 3)))
        ctx (task-context [(host/ext "watch" spec) apply-one] [spec])]
    (doseq [route [:root :fap :ap]]
      (let [parent (j/machine ctx) p (watching-promise! ctx parent)]
        (case route
          :root (j/start! ctx parent "Array.replicate" [0 0 p])
          :fap (j/start! ctx parent "Array.replicate._boxed" [0 0 p])
          :ap (j/start! ctx parent "apply-one" [(j/make-closure! ctx parent "Array.replicate" [0 0]) p]))
        (let [request (host/request! ctx parent) native (enclosing-native parent)
              output (host/private-value native "output")
              {:keys [engine roots]} (j/fork! ctx parent [output]) child engine [copy] roots]
          (is (order/dead? p)) (is (= 0 (array/size output)))
          (is (true? (host/private-value native "releaseClaimed")))
          (is (false? (j/advance! ctx parent 0)))
          (doseq [[e expected] [[parent output] [child copy]]]
            (j/resume-host! ctx e (j/host-request ctx e) 0)
            (is (identical? expected (finish! ctx e)))
            (release! ctx e expected) (close! ctx e)))))))

(deftest array-pop-and-set-preserve-prefix-output-and-replacement-through-finalizer-fork
  (let [spec (host/spec "watch" ["object" "object"] [false false] "object")
        ctx (task-context [(host/ext "watch" spec)] [spec])]
    (doseq [operation [:pop :set]]
      (let [parent (j/machine ctx) p (watching-promise! ctx parent)
            source (array/push! ctx parent (array/empty! ctx parent 1) p)
            replacement (order/cons! ctx parent 8)]
        (if (= operation :pop) (j/start! ctx parent "Array.pop._boxed" [0 source])
          (j/start! ctx parent "Array.set._boxed" [0 source 0 replacement 0]))
        (let [_ (host/request! ctx parent) native (enclosing-native parent)
              {:keys [engine roots]} (j/fork! ctx parent [source replacement]) child engine [copy cr] roots]
          (is (identical? source (host/private-value native "output")))
          (is (order/dead? p)) (is (= 1 (c/rc ctx replacement)))
          (if (= operation :pop) (is (= 0 (array/size source)))
            (is (identical? p (first (array/elements ctx source)))))
          (doseq [[e out value] [[parent source replacement] [child copy cr]]]
            (j/resume-host! ctx e (j/host-request ctx e) 0)
            (is (identical? out (finish! ctx e)))
            (if (= operation :pop) (release! ctx e value)
              (is (identical? value (first (array/elements ctx out)))))
            (release! ctx e out) (close! ctx e)))))))

(deftest captured-mt-ref-sees-replacement-and-outer-set-does-not-replay-store-after-callback
  (let [spec (host/spec "read_replacement" ["object"] [true] "object")
        read-row (c/decl "read-replacement" (mapv #(c/p % "object") [1 2 3]) "object"
                   ["dec" {:idx 2} 1 true false
                    (c/let-ir 4 "tobject" (sfap "ST.Prim.Ref.get" ["erased" "erased" (c/v 1) "erased"])
                      (c/let-ir 5 "object" (c/fap "read-host" [(c/v 4)])
                        (c/let-ir 6 "object" (c/lit 99)
                          (c/let-ir 7 "tagged" (sfap "ST.Prim.Ref.set" ["erased" "erased" (c/v 1) (c/v 6) "erased"])
                            ["dec" {:idx 4} 1 true false ["dec" {:idx 1} 1 true false (c/ret 5)]]))))])
        ctx (task-context [(host/ext "read-host" spec) read-row] [spec]) parent (j/machine ctx)
        p (promise! ctx parent) holder (ref/make-ref! ctx parent p)
        _ (j/retain! ctx parent holder)
        dep (io-map! ctx parent (j/make-closure! ctx parent "read-replacement" [holder]) (result-task! ctx parent p))
        replacement (order/cons! ctx parent 7)]
    (release! ctx parent dep) (j/retain! ctx parent holder)
    (j/start! ctx parent "ST.Prim.Ref.set._boxed" [0 0 holder replacement 0])
    (let [request (host/request! ctx parent)
          {:keys [engine roots]} (j/fork! ctx parent [holder replacement]) child engine [ch cr] roots]
      (is (identical? replacement (first (host/args request))))
      (is (identical? replacement (first (ref/fields ctx holder))))
      (is (= 2 (c/rc ctx replacement)))
      (doseq [[e cell value] [[parent holder replacement] [child ch cr]]]
        (j/resume-host! ctx e (j/host-request ctx e) 0)
        (is (= 0 (finish! ctx e))) (is (= [99] (vec (ref/fields ctx cell))))
        (is (order/dead? value))
        (release! ctx e cell) (close! ctx e)))))

(deftest active-operand-and-profile-preflight-rejections-preserve-owners-and-idle-state
  (let [ctx (task-context) engine (j/machine ctx) foreign (j/machine ctx)
        p (promise! ctx engine) source (result-task! ctx engine p)
        fp (promise! ctx foreign) fs (result-task! ctx foreign fp)
        callback (j/make-closure! ctx engine "identity" [])
        invalid [[0 0 callback source 9 1] [0 0 callback source -1 1]
                 [0 0 callback source 0 0] [0 0 callback source 0 2]
                 [1 0 callback source 0 1] [0 0 "bad" source 0 1]
                 [0 0 callback fs 0 1]]]
    (doseq [args invalid]
      (let [before [(c/rc ctx callback) (c/rc ctx source) (c/rc ctx fs)]]
        (is (g/bad? #(j/start! ctx engine "Task.map" args)))
        (is (= "idle" (j/phase ctx engine)))
        (is (= before [(c/rc ctx callback) (c/rc ctx source) (c/rc ctx fs)]))))
    (is (g/bad? #(j/start! ctx engine "Task.get" [0 source]))) (is (= 2 (c/rc ctx source)))
    (doseq [[label args] [["IO.Promise.resolve" [0 7 p 0]] ["IO.Promise.result?" [0 p]]
                          ["IO.getTaskState" [0 source 0]] ["IO.cancel" [0 source 0]]]]
      (is (g/bad? #(j/start! ctx engine label args)))
      (is (g/bad? #(j/make-closure! ctx engine label []))))
    (is (g/bad? #(j/fork! ctx engine [fs])))
    (let [inactive (j/machine (dissoc ctx :task-runtime))]
      (is (g/bad? #(j/start! ctx inactive "IO.Promise.new" [0 0 0])))
      (is (= "idle" (j/phase ctx inactive))) (j/close! ctx inactive))
    (release! ctx engine callback) (release! ctx engine source) (release! ctx engine p)
    (release! ctx foreign fs) (release! ctx foreign fp) (close! ctx engine) (close! ctx foreign)))

(deftest borrowed-native-task-pap-and-prepared-import-admissions-reject
  (let [rows (mapv #(get % "row") (json/read-str (slurp "test/fixtures/java-task-sync-runtime/original-rows.json")))
        pap (c/decl "bad-pap" [] "object"
                    (c/let-ir 1 "object" {:pap {:c (task-names "IO.Promise.result?") :ys ["erased"]}} (c/ret 1)))]
    (is (re-find #"Borrowed task primitive" (c/failure #(j/invoke-static (:prepare *basis*) [(conj rows (first (x/raw [pap])))]))))
    (let [base (active (j/prepare-host-program *basis* [] []))
          source (j/source-binding base (Object.))
          row (get-in (first (filter #(= "IO.Promise.result?" (get % "label"))
                                    (json/read-str (slurp "test/fixtures/java-task-sync-runtime/original-rows.json")))) ["row"])
          header (j/declaration-header source row (apply str (repeat 64 "a")))
          ctx (j/register-headers base [header]) engine (j/machine ctx)
          graph (j/selected-owner-graph ctx source (Object.)
                  [(j/graph-node ctx {:kind :closure :id 1 :rc 1 :target header :fields []})]
                  [] [] [(j/graph-ref ctx 1)])]
      (is (g/bad? #(j/install-graph! ctx engine graph)))
      (is (false? (host/private-value engine "graphInstalled"))) (close! ctx engine))))

(deftest deep-pending-dependency-propagation-forks-entire-record-and-action-graph-iteratively
  (let [ctx (task-context) parent (j/machine ctx) p (promise! ctx parent)
        last-task (loop [i 0 source (result-task! ctx parent p)]
                    (if (= i 3000) source
                      (recur (inc i) (map! ctx parent (j/make-closure! ctx parent "identity" []) source))))]
    (j/retain! ctx parent p) (j/start! ctx parent "IO.Promise.resolve._boxed" [0 7 p 0])
    (loop [left 1000]
      (when (zero? left) (throw (ex-info "No deep propagation boundary" {})))
      (when (< (chain-count (action parent) "parent") 2000)
        (j/advance! ctx parent 500) (recur (dec left))))
    (let [{:keys [engine roots]} (j/fork! ctx parent [p last-task]) child engine [cp ct] roots]
      (is (= 0 (finish! ctx parent) (finish! ctx child)))
      (doseq [[e promise task] [[parent p last-task] [child cp ct]]]
        (let [value (get! ctx e task)] (is (= [7] (vec (order/fields ctx value)))) (release! ctx e value))
        (is (zero? (.size ^java.util.Map (host/private-value e "taskRecords"))))
        (release! ctx e promise) (is (quiescent? ctx e)) (close! ctx e)))))

(deftest claimed-owned-host-reply-keeps-alias-credit-distinct-from-later-facade-drop
  (let [outer (host/spec "outer_object" ["object" "object"] [true true] "object")
        inner (host/spec "inner_object" ["object" "object"] [false false] "object")
        ctx (task-context [(host/ext "outer" outer) (host/ext "inner" inner)] [outer inner]) parent (j/machine ctx)
        p (promise! ctx parent) value (order/cons! ctx parent 7)
        dependent (io-map! ctx parent (j/make-closure! ctx parent "inner" []) (result-task! ctx parent p))]
    (release! ctx parent dependent) (j/start! ctx parent "outer" [p value])
    (let [a (j/host-request ctx parent)]
      (is (g/bad? #(j/resume-host! ctx parent a value)))
      (is (identical? a (j/host-request ctx parent)))
      (is (= 1 (c/rc ctx value) (c/rc ctx p)))
      (j/retain! ctx parent value) (j/resume-host! ctx parent a value)
      (let [_ (host/request! ctx parent) completion (host/private-value parent "hostCompletion")
            {:keys [engine roots]} (j/fork! ctx parent [value]) child engine [copy] roots]
        (is (true? (host/private-value completion "resultOwned")))
        (is (identical? value (host/private-value completion "completionResult")))
        (is (= 2 (c/rc ctx value) (c/rc ctx copy)))
        (doseq [[e expected] [[parent value] [child copy]]]
          (j/resume-host! ctx e (j/host-request ctx e) 0)
          (is (identical? expected (finish! ctx e))) (is (= 1 (c/rc ctx expected)))
          (release! ctx e expected) (is (order/dead? expected)) (close! ctx e))))))

(deftest foreign-runtime-task-host-reply-is-rejected-before-any-claim
  (let [spec (host/spec "return_task" ["object"] [false] "object")
        ctx (task-context [(host/ext "return-task" spec)] [spec]) parent (j/machine ctx)
        p (promise! ctx parent) task (result-task! ctx parent p)]
    (j/start! ctx parent "return-task" [0])
    (let [a (j/host-request ctx parent)
          {:keys [engine roots]} (j/fork! ctx parent [p task]) child engine [cp ct] roots
          b (j/host-request ctx child)]
      (is (g/bad? #(j/resume-host! ctx child b task)))
      (is (identical? b (j/host-request ctx child)))
      (is (= 2 (c/rc ctx task) (c/rc ctx ct)))
      (j/resume-host! ctx parent a task) (j/resume-host! ctx child b ct)
      (is (identical? task (finish! ctx parent))) (is (identical? ct (finish! ctx child)))
      (doseq [[e promise value] [[parent p task] [child cp ct]]]
        (release! ctx e value) (release! ctx e promise) (close! ctx e)))))

(deftest active-task-pure-invalid-carriers-are-pure-preflight
  (let [ctx (task-context) engine (j/machine ctx)]
    (doseq [args [[1 0] [0 nil] [0 1.0] [0 (object-array 0)]]]
      (is (g/bad? #(j/start! ctx engine "Task.pure" args)))
      (is (= "idle" (j/phase ctx engine)))
      (is (false? (host/private-value engine "untrackedFailure"))))
    (close! ctx engine)))

(deftest private-quiet-proof-failure-retains-scratch-and-never-dispatches-promise
  ;; Structural proof-misuse model, not an admitted public finalizer API. Real
  ;; arbitrary drops must use beginRelease; its callback gates appear above.
  (let [ctx (task-context) engine (j/machine ctx) promise (promise! ctx engine)
        task (first (order/fields ctx promise))
        release (.getDeclaredMethod ^Class (:class ctx) "releaseQuiet" (into-array Class [Object Integer/TYPE]))]
    (.setAccessible release true)
    (is (re-find #"Quiet release proof reached Promise" (c/failure #(.invoke release engine (object-array [promise (int 1)])))))
    (is (order/dead? promise)) (is (= 1 (c/rc ctx task)))
    (is (identical? promise (host/private-value engine "quietCurrent")))
    (is (= 0 (host/private-value engine "quietFieldCursor")))
    (is (identical? task (first (order/fields ctx promise))))
    (is (nil? (first (order/fields ctx task))))
    (is (g/bad? #(j/start-dispose! ctx engine))) (is (g/bad? #(j/close! ctx engine)))))

(deftest genuine-promise-result-bang-uses-option-extraction-and-rejects-drop-none
  (let [ctx (task-context) engine (j/machine ctx) p (promise! ctx engine)]
    (j/retain! ctx engine p)
    (let [result (j/call ctx engine "IO.Promise.result!._boxed" [0 p])]
      (is (= 0 (task-state ctx engine result)))
      (is (= 0 (resolve! ctx engine p 7))) (is (= 7 (get! ctx engine result))))
    (release! ctx engine p) (close! ctx engine))
  (let [ctx (task-context) engine (j/machine ctx) p (promise! ctx engine)]
    (j/retain! ctx engine p)
    (let [result (j/call ctx engine "IO.Promise.result!._boxed" [0 p])]
      (is (re-find #"Option.getOrBlock! None" (c/failure #(release! ctx engine p))))
      (is (= "failed" (j/phase ctx engine))) (is (= 1 (c/rc ctx result)))
      (is (g/bad? #(j/take-result! ctx engine))) (is (g/bad? #(j/close! ctx engine))))))

(deftest native-first-publication-marks-values-duplicate-does-not-and-ready-map-stays-st
  (let [keep (c/decl "keep-capture" [(c/p 1 "object") (c/p 2 "object")] "object"
                       ["dec" {:idx 2} 1 true false (c/ret 1)])
        ctx (task-context [keep] []) engine (j/machine ctx)
        p (promise! ctx engine) first (order/cons! ctx engine 7) losing (order/cons! ctx engine 8)
        mt? (fn [value]
              (let [method (.getDeclaredMethod ^Class (:class ctx) "logicalMT" (into-array Class [(:node-class ctx)]))]
                (.setAccessible method true) (.invoke method nil (object-array [value]))))]
    (is (false? (mt? first))) (resolve! ctx engine p first) (is (true? (mt? first)))
    (resolve! ctx engine p losing) (is (order/dead? losing)) (is (false? (mt? losing)))
    (release! ctx engine p) (is (order/dead? first))
    (let [value (order/cons! ctx engine 9)
          callback (j/make-closure! ctx engine "keep-capture" [value])
          mapped (map! ctx engine callback (task/pure ctx engine 0))]
      (is (false? (mt? value))) (is (false? (mt? mapped)))
      (is (identical? value (get! ctx engine mapped))) (release! ctx engine value))
    (close! ctx engine)))

(deftest queued-zero-pure-task-can-run-before-its-native-lifo-deactivation-visit
  ;; A generic constructor drop claims BOTH child credits before visiting
  ;; either shell. Its later Promise is visited first and completes the still
  ;; registered Task; cancelling at the earlier credit claim would be premature.
  (let [spec (host/spec "queued_zero" ["object"] [false] "object")
        pair (c/decl "pair" [(c/p 1 "object") (c/p 2 "object")] "object"
                    (c/let-ir 3 "object" (c/ctor 2 [(c/v 1) (c/v 2)] 0) (c/ret 3)))
        ctx (task-context [(host/ext "queued-zero" spec) pair] [spec]) engine (j/machine ctx)
        p (promise! ctx engine)
        dependent (map! ctx engine (j/make-closure! ctx engine "queued-zero" []) (result-task! ctx engine p))
        root (order/pair! ctx engine dependent p)]
    (j/start-release! ctx engine root 1)
    (let [request (host/request! ctx engine)]
      (is (order/dead? dependent)) (is (order/dead? p))
      (is (= [0] (host/args request)))
      (j/resume-host! ctx engine request 0) (is (= 0 (finish! ctx engine)))
      (is (zero? (.size ^java.util.Map (host/private-value engine "taskRecords"))))
      (is (quiescent? ctx engine)) (close! ctx engine))))

(defn check! [basis] (binding [*basis* basis] (run-tests 'java-ir-sync-task-checks)))
