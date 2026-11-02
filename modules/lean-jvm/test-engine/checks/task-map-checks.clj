(ns java-ir-task-map-checks
  "Pinned no-manager Task.map, explicit runtime frames and owned ready values."
  (:require [clojure.test :refer [deftest is run-tests]] [clojure.data.json :as json]
            [java-ir-baseline :as j] [java-ir-baseline-checks :as c]
            [java-ir-extern-checks :as x] [java-ir-generation-checks :as g]
            [java-ir-header-checks :as h] [java-ir-code-checks :as code]
            [java-ir-host-checks :as host] [java-ir-ref-checks :as ref]
            [lean-compatibility-corpus :as corpus]))
(def ^:dynamic *basis* nil)
(def fixture "test/fixtures/java-task-map-runtime/original-rows.json")
(defn rows [file] (mapv #(get % "row") (json/read-str (slurp file))))
(def originals (rows fixture))
(def task-rows (rows "test/fixtures/java-task-runtime/original-rows.json"))
(def task-map-name (get (first originals) "name"))
(def task-pure-name (get (first task-rows) "name"))
(defn helpers []
  (concat g/common
    [(c/decl "fresh" [(c/p 1 "object")] "object" (c/let-ir 2 "object" (c/ctor 1 [(c/v 1)] 0) (c/ret 2)))
     (c/decl "keep-first" [(c/p 1 "object") (c/p 2 "object")] "object" ["dec" {:idx 2} 1 true false (c/ret 1)])
     (c/decl "second" [(c/p 1 "object") (c/p 2 "object")] "object" ["dec" {:idx 1} 1 true false (c/ret 2)])
     (c/decl "scalar" [(c/p 1 "object")] "float" ["dec" {:idx 1} 1 true false (c/let-ir 2 "float" (c/lit 1) (c/ret 2))])
     (c/decl "unbox-float" [(c/p 1 "object")] "float" (c/let-ir 2 "float" {:unbox {:x {:idx 1}}} ["dec" {:idx 1} 1 true false (c/ret 2)]))
     (c/decl "task-value" [(c/p 1 "object")] "object"
       (c/let-ir 2 "erased" (c/lit 0) (c/let-ir 3 "object" {:fap {:c task-pure-name :ys [(c/v 2) (c/v 1)]}} (c/ret 3))))
     (c/decl "closure-value" [(c/p 1 "object")] "object" (c/let-ir 2 "object" {:pap {:c (c/name-ir "keep-first") :ys [(c/v 1)]}} (c/ret 2)))
     (c/decl "tail" [(c/p 1 "object") (c/p 2 "object")] "object"
       ["case" (c/name-ir "Bool") {:idx 1} "object" [["ctor" {:cidx 0} (c/ret 2)]
        ["default" (c/let-ir 3 "object" (c/lit 0) (c/let-ir 4 "object" (c/fap "tail" [(c/v 3) (c/v 2)]) (c/ret 4)))]]])
     (c/decl "nested" [(c/p 1 "object") (c/p 2 "object")] "object"
       (c/let-ir 3 "erased" (c/lit 0)
         (c/let-ir 4 "uint8" (c/lit 0)
           (c/let-ir 5 "object" {:fap {:c task-pure-name :ys [(c/v 3) (c/v 2)]}}
             (c/let-ir 6 "object" {:fap {:c task-map-name :ys [(c/v 3) (c/v 3) (c/v 1) (c/v 5) (c/v 3) (c/v 4)]}} (c/ret 6))))))]))
(defn context
  ([] (context []))
  ([extra] (assoc *basis* :program (j/invoke-static (:prepare *basis*) [(x/raw (concat originals task-rows (helpers) extra))]))))
(defn closure [ctx engine label & captures] (j/make-closure! ctx engine label captures))
(defn fresh [ctx engine] (j/call ctx engine "fresh" [7]))
(defn pure [ctx engine value] (j/call ctx engine "Task.pure" [0 value]))
(defn get-task [ctx engine value] (j/call ctx engine "Task.get" [0 value]))
(defn map-task [ctx engine f task] (j/call ctx engine "Task.map" [0 0 f task 0 0]))
(defn fields [ctx value] (.get ^java.lang.reflect.Field (:fields ctx) value))
(defn dead? [value] (host/private-value value "dead"))
(defn counters [engine] (mapv #(host/private-value engine %) ["allocations" "retains" "releases" "shellDeletes"]))
(defn stop-at-wrap! [ctx engine]
  (loop [left 1000]
    (when (zero? left) (throw (ex-info "No map wrap" {})))
    (if (= 14 (host/private-value (host/private-value engine "pc") "op")) nil
      (do (j/advance! ctx engine 1) (recur (dec left))))))

(deftest exact-authentic-abi-root-and-genuine-wrapper
  (let [manifest (json/read-str (slurp "test/fixtures/java-task-map-runtime/provenance.json")) ctx (context) engine (j/machine ctx)]
    (try
      (is (= 2 (count originals))) (is (= (get manifest "fixture-sha256") (corpus/sha256 fixture)))
      (is (= ["erased" "erased" "tobject" "object" "tobject" "uint8"] (mapv #(get % "ty") (get-in (first originals) ["ir" "extern" "xs"]))))
      (is (every? false? (map #(get % "borrow") (get-in (first originals) ["ir" "extern" "xs"]))))
      (is (= "lean_task_map" (j/invoke-static (.getMethod ^Class (:class ctx) "validateExternAbi" (into-array Class [java.util.Map])) [(first originals)])))
      (doseq [label ["Task.map" "Task.map._boxed"] prio [0 8 9 Long/MAX_VALUE] sync [0 1]]
        (is (= 42 (get-task ctx engine (j/call ctx engine label [0 0 (closure ctx engine "identity") (pure ctx engine 42) prio sync])))))
      (is (g/bad? #(j/make-closure! ctx engine "Task.map" [])))
      (finally (j/close! ctx engine)))))

(deftest unique-shared-and-persistent-task-callback-ownership
  (let [ctx (context) engine (j/machine ctx)]
    (try
      (doseq [shared? [false true]]
        (let [value (fresh ctx engine) task (pure ctx engine value) f (closure ctx engine "identity")]
          (when shared? (j/retain! ctx engine task) (j/retain! ctx engine f))
          (let [answer (get-task ctx engine (map-task ctx engine f task))]
            (is (identical? value answer))
            (is (= (if shared? 2 1) (c/rc ctx value)))
            (is (= (not shared?) (dead? task) (dead? f)))
            (j/release! ctx engine answer))
          (when shared? (j/release! ctx engine task) (j/release! ctx engine f))
          (is (= 0 (c/rc ctx value)))))
      (let [task (pure ctx engine 42) f (closure ctx engine "identity")]
        (.setInt ^java.lang.reflect.Field (:rc ctx) task 0) (.setInt ^java.lang.reflect.Field (:rc ctx) f 0)
        (is (= 42 (get-task ctx engine (map-task ctx engine f task))))
        (is (= 0 (c/rc ctx task) (c/rc ctx f))) (is (false? (dead? task))) (is (false? (dead? f))))
      (finally (j/close! ctx engine)))))

(deftest payload-capture-aliases-and-known-credit-rejection
  (let [ctx (context) engine (j/machine ctx)]
    (try
      (let [value (fresh ctx engine) _ (j/retain! ctx engine value)
            f (closure ctx engine "keep-first" value) task (pure ctx engine value)
            answer (get-task ctx engine (map-task ctx engine f task))]
        (is (identical? value answer)) (is (= 1 (c/rc ctx value))) (j/release! ctx engine answer) (is (dead? value)))
      (let [value (fresh ctx engine) _ (j/retain! ctx engine value)
            f (closure ctx engine "keep-first" value) task (pure ctx engine value)]
        (.setInt ^java.lang.reflect.Field (:rc ctx) value 1)
        (let [before (counters engine)]
          (is (g/bad? #(map-task ctx engine f task))) (is (= before (counters engine)))
          (is (= 1 (c/rc ctx f) (c/rc ctx task) (c/rc ctx value))))
        (.setInt ^java.lang.reflect.Field (:rc ctx) value 2)
        (j/release! ctx engine f) (j/release! ctx engine task) (is (dead? value)))
      (finally (j/close! ctx engine)))))

(deftest callback-results-are-wrapped-without-flattening-or-extra-application
  (let [ctx (context) engine (j/machine ctx)]
    (try
      (let [answer (get-task ctx engine (map-task ctx engine (closure ctx engine "scalar") (pure ctx engine 0)))]
        (is (= 1.0 (j/call ctx engine "unbox-float" [answer]))))
      (let [inner (get-task ctx engine (map-task ctx engine (closure ctx engine "task-value") (pure ctx engine 42)))]
        (is (true? (host/private-value inner "readyTask"))) (is (= 42 (get-task ctx engine inner))))
      (let [f (get-task ctx engine (map-task ctx engine (closure ctx engine "closure-value") (pure ctx engine 42)))]
        (is (= 42 (j/call ctx engine "apply" [f 99]))))
      (finally (j/close! ctx engine)))))

(deftest partial-callback-produces-a-closure-without-forcing-code
  (let [base (context) binding (j/source-binding base (Object.))
        row (c/decl "unforced-two" [(c/p 1 "object") (c/p 2 "object")] "object" ["dec" {:idx 2} 1 true false (c/ret 1)])
        header (h/header binding row) ctx (j/register-headers base [header]) engine (j/machine ctx)]
    (try
      (let [f (get-task ctx engine (map-task ctx engine (closure ctx engine "unforced-two") (pure ctx engine 42)))]
        (is (= 1 (count (fields ctx f)))) (is (= 42 (aget ^objects (fields ctx f) 0)))
        (is (nil? (j/code-request ctx engine))) (j/release! ctx engine f))
      (finally (j/close! ctx engine)))))

(deftest nested-maps-and-callback-self-tails-use-existing-control
  (let [ctx (context) engine (j/machine ctx)]
    (try
      (is (= 42 (get-task ctx engine (map-task ctx engine (closure ctx engine "tail" 1) (pure ctx engine 42)))))
      (let [f (loop [n 64 f (closure ctx engine "identity")]
                (if (zero? n) f (recur (dec n) (closure ctx engine "nested" f))))
            task (map-task ctx engine f (pure ctx engine 42))]
        (is (= 42 (loop [n 65 value task] (if (zero? n) value (recur (dec n) (get-task ctx engine value)))))))
      (finally (j/close! ctx engine)))))

(deftest invalid-inputs-reject-before-root-transfer
  (let [ctx (context) engine (j/machine ctx) f (closure ctx engine "identity") task (pure ctx engine 42)
        normal [0 0 f task 0 0]]
    (try
      (doseq [[index value] [[0 1] [1 1] [2 task] [3 f] [4 -1] [4 (biginteger 0)] [5 2] [5 255]]]
        (let [before (counters engine)]
          (is (g/bad? #(j/call ctx engine "Task.map" (assoc normal index value))))
          (is (= before (counters engine))) (is (= 1 (c/rc ctx f) (c/rc ctx task)))))
      (let [expected (aget ^objects (fields ctx task) 0)]
        (aset ^objects (fields ctx task) 0 nil)
        (is (g/bad? #(map-task ctx engine f task)))
        (aset ^objects (fields ctx task) 0 expected))
      (is (= 42 (get-task ctx engine (map-task ctx engine f task))))
      (finally (j/close! ctx engine)))))

(deftest explicit-start-zero-budget-and-before-apply-fork
  (when (:explicit *basis*)
    (let [ctx (context) parent (j/machine ctx) task (pure ctx parent 42) f (closure ctx parent "identity")]
      (j/start! ctx parent "Task.map" [0 0 f task 0 0])
      (let [before (counters parent) child (:engine (j/fork! ctx parent []))]
        (try
          (is (= "running" (j/phase ctx parent))) (is (= 0 (j/instructions ctx parent)))
          (is (false? (j/advance! ctx parent 0))) (is (= before (counters parent)))
          (is (= 1 (c/rc ctx f) (c/rc ctx task)))
          (let [a (code/finish! ctx parent) b (code/finish! ctx child)]
            (is (= 3 (j/instructions ctx parent) (j/instructions ctx child)))
            (is (= 42 (get-task ctx parent a) (get-task ctx child b))))
          (finally (j/close! ctx parent) (j/close! ctx child)))))))

(deftest code-callback-demand-rejects-recursive-before-transfer-and-forks-explicit
  (let [base (context) binding (j/source-binding base (Object.)) row (first g/common)
        header (h/header binding (assoc row :name (c/name-ir "demanded") :ir {:fdecl (assoc (get-in row [:ir :fdecl]) :f (c/name-ir "demanded"))}))
        row (assoc row :name (c/name-ir "demanded") :ir {:fdecl (assoc (get-in row [:ir :fdecl]) :f (c/name-ir "demanded"))})
        ctx (j/register-headers base [header]) ready (code/materialize ctx header row [])
        engine (j/machine ctx) value (fresh ctx engine) task (pure ctx engine value) f (closure ctx engine "demanded")]
    (if-not (:explicit *basis*)
      (try
        (let [before (counters engine)] (is (g/bad? #(map-task ctx engine f task))) (is (= before (counters engine))))
        (is (= 1 (c/rc ctx f) (c/rc ctx task) (c/rc ctx value)))
        (finally (j/release! ctx engine f) (j/release! ctx engine task) (j/close! ctx engine)))
      (do
        (j/start! ctx engine "Task.map" [0 0 f task 0 0])
        (let [request (code/request! ctx engine) child (:engine (j/fork! ctx engine []))
              child-request (j/code-request ctx child) before (counters engine)]
          (try
            (is (dead? f)) (is (dead? task)) (is (= 1 (c/rc ctx value)))
            (is (identical? value (first (code/args request))))
            (is (g/bad? #(j/resume-code! ctx engine request)))
            (is (g/bad? #(j/resume-code! ready child request)))
            (is (identical? request (j/code-request ctx engine)))
            (is (= before (counters engine)))
            (j/install-program! ready child)
            (j/resume-code! ready child child-request) (j/resume-code! ready engine request)
            (let [a (get-task ready engine (code/finish! ready engine)) b (get-task ready child (code/finish! ready child))]
              (is (identical? value a)) (is (not (identical? a b)))
              (is (= 1 (c/rc ready a) (c/rc ready b)))
              (j/release! ready engine a) (j/release! ready child b))
            (is (g/bad? #(j/resume-code! ready engine request)))
            (finally (j/close! ready engine) (j/close! ready child))))))))

(deftest host-callback-borrowed-reply-fork-and-no-effect-replay
  (let [spec (host/spec "research_task_map" ["object"] [true] "object")
        ctx (assoc (j/prepare-host-program *basis* (x/raw (concat originals task-rows (helpers) [(host/ext "host" spec)])) [spec])
                   :explicit (boolean (:explicit *basis*)))
        engine (j/machine ctx) value (fresh ctx engine) f (closure ctx engine "host") task (pure ctx engine value)]
    (if-not (:explicit *basis*)
      (try
        (let [before (counters engine)] (is (g/bad? #(map-task ctx engine f task))) (is (= before (counters engine))))
        (is (= 1 (c/rc ctx f) (c/rc ctx task) (c/rc ctx value)))
        (finally (j/release! ctx engine f) (j/release! ctx engine task) (j/close! ctx engine)))
      (do
        (j/start! ctx engine "Task.map" [0 0 f task 0 0])
        (let [request (host/request! ctx engine) fork (j/fork! ctx engine [value]) child (:engine fork) copy (first (:roots fork))
              child-request (j/host-request ctx child) before (counters engine)]
          (try
            (is (identical? value (first (host/args request))))
            (is (identical? copy (first (host/args child-request))))
            (is (g/bad? #(j/resume-host! ctx engine request value)))
            (is (identical? request (j/host-request ctx engine)))
            (is (= before (counters engine)))
            (is (g/bad? #(j/resume-host! ctx child request copy)))
            (j/retain! ctx engine value) (j/retain! ctx child copy)
            (j/resume-host! ctx engine request value) (j/resume-host! ctx child child-request copy)
            (let [a (get-task ctx engine (host/finish! ctx engine)) b (get-task ctx child (host/finish! ctx child))]
              (is (identical? a value)) (is (identical? b copy)) (is (= 1 (c/rc ctx a) (c/rc ctx b)))
              (j/release! ctx engine a) (j/release! ctx child b))
            (is (g/bad? #(j/resume-host! ctx engine request value)))
            (finally (j/close! ctx engine) (j/close! ctx child))))))))

(deftest before-wrap-fork-remaps-ref-result-and-preserves-runtime-layout
  (when (:explicit *basis*)
    (let [ctx (context (mapv #(get % "row") (ref/originals))) engine (j/machine ctx)
          cell (ref/make-ref! ctx engine 42) _ (j/retain! ctx engine cell)
          task (pure ctx engine cell) f (closure ctx engine "identity")]
      (j/start! ctx engine "Task.map" [0 0 f task 0 0]) (stop-at-wrap! ctx engine)
      (let [prepared (host/private-value engine "activePrepared") fork (j/fork! ctx engine [cell])
            child (:engine fork) copy (first (:roots fork))]
        (try
          (is (identical? prepared (host/private-value child "activePrepared")))
          (is (not (identical? cell copy)))
          (is (= 2 (c/rc ctx cell) (c/rc ctx copy)))
          ;; Modeled host mutation of an immediate ref field, not guest reentry.
          (aset ^objects (fields ctx copy) 0 99)
          (let [a (get-task ctx engine (code/finish! ctx engine)) b (get-task ctx child (code/finish! ctx child))]
            (is (identical? cell a)) (is (identical? copy b))
            (is (= 42 (ref/ref-get! ctx engine a))) (is (= 99 (ref/ref-get! ctx child b)))
            (j/release! ctx engine a) (j/release! ctx child b))
          (j/release! ctx engine cell) (j/release! ctx child copy)
          (is (dead? cell)) (is (dead? copy))
          (finally (j/close! ctx engine) (j/close! ctx child)))))))

(deftest sibling-callback-lineage-rejects-before-map-input-consumption
  (let [base (context) a (j/extend-program base (x/raw [(g/literal "left" 1)]))
        b (j/extend-program base (x/raw [(g/literal "right" 2)]))
        engine (j/machine a) other (j/machine b) f (closure b other "right") task (pure a engine 42)]
    (try
      (let [before (counters engine)] (is (g/bad? #(map-task a engine f task))) (is (= before (counters engine))))
      (is (= 1 (c/rc b f) (c/rc a task)))
      (finally (j/release! b other f) (j/release! a engine task) (j/close! a engine) (j/close! b other)))))

(deftest failed-code-and-host-callbacks-do-not-publish-ready-tasks
  (when (:explicit *basis*)
    (doseq [kind [:code :host]]
      (let [base (context) spec (host/spec "research_task_failure" ["object"] [false] "object")
            binding (j/source-binding base (Object.)) row (g/literal "failed-callback" 0)
            header (h/header binding row)
            ctx (if (= kind :code) (j/register-headers base [header])
                  (j/extend-program base (x/raw [(host/ext "failed-callback" spec)]) [spec]))
            engine (j/machine ctx) value (fresh ctx engine) f (closure ctx engine "failed-callback") task (pure ctx engine value)]
        (j/start! ctx engine "Task.map" [0 0 f task 0 0])
        (let [request (if (= kind :code) (code/request! ctx engine) (host/request! ctx engine)) before (counters engine)]
          (if (= kind :code) (j/fail-code! ctx engine request (Exception. "deliberate"))
            (j/fail-host! ctx engine request (Exception. "deliberate")))
          (is (= "failed" (j/phase ctx engine))) (is (= before (counters engine)))
          (is (false? (host/private-value engine "pendingOwnedResult")))
          (is (g/bad? #(j/advance! ctx engine 1)))
          (is (= 1 (c/rc ctx value)))
          (j/release! ctx engine value) (is (g/bad? #(j/close! ctx engine))))))))

(deftest genuine-boxed-map-pap-and-outer-surplus-wrap-order
  (let [apply-many (c/decl "apply-many" [(c/p 1 "object") (c/p 2 "object") (c/p 3 "object")] "object"
                     (c/let-ir 4 "object" {:ap {:x {:idx 1} :ys [(c/v 2) (c/v 3)]}} (c/ret 4)))
        ctx (context [apply-many]) engine (j/machine ctx)]
    (let [f (closure ctx engine "identity") task (pure ctx engine 42)
          wrapped (closure ctx engine "Task.map._boxed" 0 0 f task 0)]
      (is (= 42 (get-task ctx engine (j/call ctx engine "apply" [wrapped 0])))))
    (let [f (closure ctx engine "closure-value") task (pure ctx engine 42)
          wrapped (closure ctx engine "Task.map._boxed" 0 0 f task 0)]
      (is (g/bad? #(j/call ctx engine "apply-many" [wrapped 0 99])))
      (let [answer (host/private-value engine "result")]
        (is (true? (host/private-value answer "readyTask")))
        (is (= 1 (c/rc ctx answer)))
        (is (some? (host/private-value (aget ^objects (fields ctx answer) 0) "closure")))
        (j/release! ctx engine answer))
      (if (:explicit *basis*) (is (g/bad? #(j/close! ctx engine))) (j/close! ctx engine)))))

(deftest host-reply-overapplication-enters-the-original-boxed-map
  (when (:explicit *basis*)
    (let [spec (host/spec "research_map_reply" ["object"] [false] "object")
          apply-many (c/decl "apply-many" [(c/p 1 "object") (c/p 2 "object") (c/p 3 "object")] "object"
                       (c/let-ir 4 "object" {:ap {:x {:idx 1} :ys [(c/v 2) (c/v 3)]}} (c/ret 4)))
          ctx (j/prepare-host-program *basis* (x/raw (concat originals task-rows (helpers) [(host/ext "host" spec) apply-many])) [spec])
          engine (j/machine ctx) reply (closure ctx engine "Task.map._boxed" 0 0 (closure ctx engine "identity") (pure ctx engine 42) 0)]
      (try
        (j/start! ctx engine "apply-many" [(closure ctx engine "host") 0 0])
        (let [request (host/request! ctx engine)] (j/resume-host! ctx engine request reply))
        (is (= 42 (get-task ctx engine (host/finish! ctx engine))))
        (is (nil? (host/private-value engine "hostCompletion")))
        (finally (j/close! ctx engine))))))

(deftest guest-static-borrowed-host-callback-keeps-its-own-input-credit
  (when (:explicit *basis*)
    (let [spec (host/spec "research_map_static" ["object"] [true] "object")
          guest (c/decl "guest-host" [(c/p 1 "object")] "object"
                  (c/let-ir 2 "object" (c/fap "host" [(c/v 1)]) ["dec" {:idx 1} 1 true false (c/ret 2)]))
          ctx (j/prepare-host-program *basis* (x/raw (concat originals task-rows (helpers) [(host/ext "host" spec) guest])) [spec])
          engine (j/machine ctx) value (fresh ctx engine)]
      (try
        (j/start! ctx engine "Task.map" [0 0 (closure ctx engine "guest-host") (pure ctx engine value) 0 0])
        (let [request (host/request! ctx engine)]
          (is (false? (host/private-value (host/private-value request "call") "facade")))
          (is (= 1 (c/rc ctx value))) (j/retain! ctx engine value)
          (j/resume-host! ctx engine request value))
        (let [answer (get-task ctx engine (host/finish! ctx engine))]
          (is (identical? value answer)) (is (= 1 (c/rc ctx answer))) (j/release! ctx engine answer))
        (finally (j/close! ctx engine))))))

(deftest callback-unreachable-and-map-budget-failure-publish-no-task
  (when (:explicit *basis*)
    (let [bad (c/decl "explode" [(c/p 1 "object")] "object" ["unreachable"])
          ctx (context [bad]) engine (j/machine ctx) value (fresh ctx engine)
          task (pure ctx engine value) f (closure ctx engine "explode")]
      (j/start! ctx engine "Task.map" [0 0 f task 0 0])
      (let [allocations (host/private-value engine "allocations")]
        (is (false? (j/advance! ctx engine 1)))
        (is (g/bad? #(j/advance! ctx engine 1)))
        (is (= "failed" (j/phase ctx engine))) (is (false? (host/private-value engine "pendingOwnedResult")))
        (is (= allocations (host/private-value engine "allocations")))
        (is (dead? task)) (is (dead? f)) (is (= 1 (c/rc ctx value)))
        (j/release! ctx engine value) (is (g/bad? #(j/close! ctx engine)))))
    (let [ctx (context) engine (j/machine ctx) task (pure ctx engine 42) f (closure ctx engine "identity")
          field (.getDeclaredField (class engine) "callsLeft")]
      (j/start! ctx engine "Task.map" [0 0 f task 0 0])
      (.setAccessible field true) (.setLong field engine 0)
      (is (g/bad? #(j/advance! ctx engine 1))) (is (= "failed" (j/phase ctx engine)))
      (is (= 1 (c/rc ctx task) (c/rc ctx f)))
      (j/release! ctx engine task) (j/release! ctx engine f)
      (is (g/bad? #(j/close! ctx engine))))))

(deftest raw-map-pap-import-and-fake-task-admission-reject-without-effects
  (let [ctx (context [(c/decl "fake-task" [(c/p 1 "object")] "object" (c/let-ir 2 "object" (c/ctor 252 [(c/v 1)] 0) (c/ret 2)))])
        engine (j/machine ctx) f (closure ctx engine "identity") fake (j/call ctx engine "fake-task" [42])]
    (try
      (let [before (counters engine)] (is (g/bad? #(map-task ctx engine f fake))) (is (= before (counters engine))))
      (is (= 1 (c/rc ctx f) (c/rc ctx fake)))
      (is (g/bad? #(context [(c/decl "raw-pap" [] "object"
                             (c/let-ir 1 "object" {:pap {:c task-map-name :ys []}} (c/ret 1)))])))
      (finally (j/release! ctx engine f) (j/release! ctx engine fake) (j/close! ctx engine))))
  (let [base (assoc *basis* :program (j/invoke-static (:prepare *basis*) [[]])) binding (j/source-binding base (Object.))
        header (h/header binding (first originals)) ctx (j/register-headers base [header]) engine (j/machine ctx)
        node (j/graph-node ctx {:kind :closure :id 1 :target header :fields []})
        graph (j/prepared-graph ctx binding (Object.) [node] [] [] [(j/graph-ref ctx 1)])]
    (try
      (is (g/bad? #(j/install-graph! ctx engine graph)))
      (is (= [0 0 0 0] (counters engine))) (is (false? (host/private-value engine "graphInstalled")))
      (finally (j/close! ctx engine)))))

(deftest nested-map-single-stepping-yields-and-does-not-publish-program-bodies
  (when (:explicit *basis*)
    (let [ctx (context) engine (j/machine ctx)
          f (loop [n 32 f (closure ctx engine "identity")] (if (zero? n) f (recur (dec n) (closure ctx engine "nested" f))))
          task (pure ctx engine 42) count-before (.functionCount (:program ctx))]
      (try
        (j/start! ctx engine "Task.map" [0 0 f task 0 0])
        (let [slot (aget ^objects (host/private-value (:program ctx) "preparedBodies") (int (j/function-id ctx "Task.map")))]
          (is (nil? (host/private-value slot "body")))
          (is (not (identical? slot (host/private-value engine "activePrepared")))))
        (let [stats (loop [left 2000 steps 0 maximum 0 max-depth 0]
                      (when (zero? left) (throw (ex-info "Map did not yield/finish" {})))
                      (when (= steps 70)
                        (let [before [(j/instructions ctx engine) (counters engine)]]
                          (is (false? (j/advance! ctx engine 0)))
                          (is (= before [(j/instructions ctx engine) (counters engine)]))))
                      (let [before (j/instructions ctx engine) complete? (j/advance! ctx engine 1)
                            delta (- (j/instructions ctx engine) before) depth (j/depth ctx engine)]
                        (if complete? [(inc steps) (max maximum delta) (max max-depth depth)]
                          (recur (dec left) (inc steps) (max maximum delta) (max max-depth depth)))))]
          (is (= 1 (second stats))) (is (> (first stats) 70)) (is (> (nth stats 2) 32)))
        (is (= 42 (loop [n 33 value (j/take-result! ctx engine)]
                    (if (zero? n) value (recur (dec n) (get-task ctx engine value))))))
        (is (= count-before (.functionCount (:program ctx))))
        (finally (j/close! ctx engine))))))

(defn check! [basis] (binding [*basis* basis] (run-tests 'java-ir-task-map-checks)))
