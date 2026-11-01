(ns java-ir-mvars-session-checks
  "Private mixed caller: one context/session/budget; no Expr native enablement."
  (:require [clojure.test :refer [deftest is run-tests]]
            [java-ir-baseline :as j] [java-ir-baseline-checks :as c]
            [java-ir-generation-checks :as g] [java-ir-host-checks :as h]
            [java-ir-sync-task-checks :as sync] [java-ir-logical-sharing-checks :as sharing]
            [java-ir-level-mvars-checks :as level] [java-ir-expr-machinery-checks :as expr]))
(def ^:dynamic *basis* nil)
(def pv expr/private-value)
(defn context
  ([] (context {}))
  ([options]
   (let [lab (binding [expr/*basis* *basis*]
               (expr/context (merge options
                  {:extra-originals (concat (level/records) (map level/setup-copy (rest level/roles)))
                   :rows (concat [(level/fresh-context-row)] (:rows options))})))
         policy (apply j/level-instantiation-policy (:ctx lab) (map (:headers lab) level/roles))]
     (assoc lab :level-policy policy))))
(defn engine [{:keys [ctx level-policy]}]
  (let [e (j/machine ctx)] (j/configure-level-instantiation! ctx e level-policy) e))
(defn batch-action [e]
  (loop [a (sync/action e)]
    (when a (if (pv a "mvarSessionResearch") a (recur (pv a "parent"))))))
(defn state [e] (some-> (batch-action e) (pv "mvarSessionResearch")))
(defn session [e] (some-> (state e) (pv "session")))
(defn budget [e] (some-> (state e) (pv "budget")))
(defn context-value [e] (some-> (state e) (pv "context") (pv "current") (pv "value")))
(defn start! [{:keys [ctx headers]} e m inputs input amount]
  (let [hs (into-array (Class/forName "ansatz.lean.jvm.internal.exec.Interpreter$Header" true (:loader ctx)) (mapv headers expr/roles))
        method (.getDeclaredMethod ^Class (:class ctx) "startMVarSessionResearch"
                 (into-array Class [(class hs) Object (class (object-array 0)) Object Long/TYPE]))]
    (.setAccessible method true)
    (.invoke method e (object-array [hs m (object-array inputs) input (long amount)]))))
(defn private-call [ctx e method types values]
  (let [m (.getDeclaredMethod ^Class (:class ctx) method (into-array Class types))]
    (.setAccessible m true) (.invoke m e (object-array values))))
(defn reject-restart-and-seal! [ctx e s]
  (is (g/bad? #(private-call ctx e "startLevelJob" [(class s) Object] [s 0])))
  (is (g/bad? #(private-call ctx e "sealLevelSession" [(class s)] [s]))))
(defn until! [ctx e predicate] (expr/until! ctx e predicate))
(defn finish! [ctx e] (expr/finish-research! ctx e))
(defn close-output! [ctx e output] (sync/release! ctx e output) (sync/close! ctx e))
(deftest mixed-batch-uses-real-context-and-no-job-input-retain
  (let [{:keys [ctx] :as lab} (context) e (engine lab) m (level/fresh! ctx e)
        l0 (level/mvar! ctx e (level/name! ctx e "first-unassigned"))
        l1 (level/succ! ctx e (level/mvar! ctx e (level/name! ctx e "second-unassigned")))
        input (expr/bvar! ctx e 0)]
    (start! lab e m [l0 l1] input 1)
    (is (= 1 (c/rc ctx l0) (c/rc ctx l1)))
    (is (identical? m (context-value e)))
    (let [output (finish! ctx e) fields (expr/fields ctx output)]
      (is (identical? m (fields 0))) (is (identical? l0 (fields 1))) (is (identical? l1 (fields 3)))
      (is (= [1] (expr/fields ctx (fields 2))))
      (is (= 1 (c/rc ctx l0) (c/rc ctx l1)))
      (is (nil? (state e))) (close-output! ctx e output))))
(deftest outstanding-result-is-owned-and-rejects-restart-or-seal
  (let [{:keys [ctx] :as lab} (context) e (engine lab) m (level/fresh! ctx e)
        l0 (level/succ! ctx e 0) l1 (level/succ! ctx e 0) input (expr/bvar! ctx e 0)]
    (start! lab e m [l0 l1] input 1)
    (until! ctx e #(= 1 (pv (state e) "stage")))
    (let [s (session e) credit (pv s "result") count (c/rc ctx l0) work (pv (budget e) "work")]
      (is (= 2 (pv s "phase"))) (is (true? (pv credit "owned")))
      (reject-restart-and-seal! ctx e s)
      (is (identical? credit (pv s "result"))) (is (= count (c/rc ctx l0)))
      (is (= work (pv (budget e) "work"))))
    (let [output (finish! ctx e)] (close-output! ctx e output))))
(deftest shared-cache-survives-expr-child-and-fork-then-hits-second-job
  (let [label (expr/roles 0) {:keys [ctx] :as lab} (context {:defer #{label}}) parent (engine lab)
        m (level/fresh! ctx parent) root (level/succ! ctx parent (level/mvar! ctx parent (level/name! ctx parent "cache")))
        input (expr/bvar! ctx parent 0)]
    (start! lab parent m [(expr/retain ctx parent root) root] input 1)
    (until! ctx parent #(= 2 (pv (state parent) "stage")))
    (let [b (state parent) borrowed-input-credit (pv b "exprInput") counter (pv b "budget")
          instructions (j/instructions ctx parent) calls (pv parent "callsLeft")]
      (expr/constructor-request! ctx parent)
      (let [worker (expr/state parent) s (session parent)
            {:keys [engine roots]} (j/fork! ctx parent [root]) child engine cr (first roots)
            ready (expr/materialize lab label)]
        (is (identical? counter (pv worker "budget")))
        (is (identical? counter (pv s "budget")))
        (is (identical? borrowed-input-credit (pv worker "input"))) (is (nil? (pv (state parent) "exprInput")))
        (is (= 1 (.size ^java.util.Map (pv s "cache"))))
        (is (not (identical? counter (budget child))))
        (is (identical? (budget child) (pv (session child) "budget")))
        (is (identical? (budget child) (pv (expr/state child) "budget")))
        (is (identical? (pv (state child) "context") (pv (session child) "context")))
        (is (> (j/instructions ctx parent) instructions)) (is (<= (pv parent "callsLeft") calls))
        (doseq [[e expected] [[parent root] [child cr]]]
          (let [old-session (session e) old-cell (pv (state e) "context") before (pv (budget e) "work")]
            (j/resume-code! ready e (j/code-request ready e))
            (is (< (pv e "callsLeft") calls))
            (until! ready e #(= 4 (pv (state e) "stage")))
            (is (> (pv (budget e) "work") before))
            (until! ready e #(let [frame (.peekLast ^java.util.Deque (pv (session e) "frames"))]
                              (and frame (true? (pv frame "cached")) (= 8 (pv frame "stage")))))
            (let [output (finish! ready e) fields (expr/fields ready output)]
              (is (identical? expected (fields 1))) (is (identical? expected (fields 3)))
              (is (= 2 (c/rc ready expected)))
              (is (= 5 (pv old-session "phase"))) (is (nil? (pv old-cell "current")))
              (is (zero? (.size ^java.util.Map (pv old-session "cache"))))
              (is (zero? (.size ^java.util.List (pv old-session "cacheValues"))))
              (reject-restart-and-seal! ready e old-session)
              (close-output! ready e output))))))))
(deftest later-worker-has-no-fresh-work-allowance-and-keeps-the-moved-input
  (let [{:keys [ctx] :as lab} (context) e (engine lab) m (level/fresh! ctx e)
        input (expr/bvar! ctx e 0)]
    (start! lab e m [0 0] input 1)
    (until! ctx e #(= 2 (pv (state e) "stage")))
    (let [counter (budget e) credit (pv (state e) "exprInput")]
      (sync/private-set! counter "work" (long 999999))
      (is (false? (j/advance! ctx e 1)))
      (is (nil? (pv (state e) "exprInput")))
      (is (identical? credit (pv (expr/state e) "input")))
      (is (identical? counter (pv (expr/state e) "budget")))
      (is (re-find #"Expr machinery work outside bounded" (c/failure #(j/advance! ctx e 1))))
      (is (= 1000000 (pv counter "work"))) (is (true? (pv credit "owned")))
      (is (= 1 (c/rc ctx input))) (is (true? (pv (pv (pv (state e) "context") "current") "owned"))))))
(deftest first-job-context-cow-is-the-exact-current-context-used-by-second-job
  (let [label (expr/roles 0) {:keys [ctx] :as lab} (context {:defer #{label}}) e (engine lab)
        m (level/fresh! ctx e) a (level/name! ctx e "ctx-a") b (level/name! ctx e "ctx-b")
        l0 (level/mvar! ctx e (expr/retain ctx e a)) l1 (level/mvar! ctx e (expr/retain ctx e a))
        bv (level/mvar! ctx e (expr/retain ctx e b))
        m (level/assign! ctx e m b 0) m (level/assign! ctx e m (expr/retain ctx e a) bv)
        outside (expr/retain ctx e m) input (expr/bvar! ctx e 0)]
    (start! lab e m [l0 l1] input 1)
    (expr/constructor-request! ctx e)
    (let [latest (context-value e) s (session e) saved (pv s "saved")
          ready (expr/materialize lab label)]
      (is (not (identical? outside latest)))
      (is (= 1 (.size ^java.util.List saved)))
      (is (identical? bv (pv (.get ^java.util.List saved 0) "value")))
      (is (true? (pv (.get ^java.util.List saved 0) "owned")))
      (j/resume-code! ready e (j/code-request ready e))
      (let [output (finish! ready e) fields (expr/fields ready output)
            old (expr/call ready e "Lean.getLevelMVarAssignmentExp" [(expr/retain ready e outside) (expr/retain ready e a)])
            current (expr/call ready e "Lean.getLevelMVarAssignmentExp" [(expr/retain ready e (fields 0)) a])]
        (is (identical? latest (fields 0))) (is (= [0 0] [(fields 1) (fields 3)]))
        (is (identical? bv (first (expr/fields ready old)))) (is (= [0] (expr/fields ready current)))
        (sync/release! ready e old) (sync/release! ready e current)
        (sync/release! ready e outside) (is (true? (pv bv "dead")))
        (close-output! ready e output)))))
(deftest level-mt-exclusivity-and-expr-replace-rc-heuristic-remain-distinct
  (let [{:keys [ctx] :as lab} (context) e (engine lab) m (level/fresh! ctx e)
        root (level/succ! ctx e (level/mvar! ctx e (level/name! ctx e "mt"))) input (expr/bvar! ctx e 0)]
    (sharing/mark! ctx e root) (sharing/mark! ctx e input)
    (start! lab e m [root 0] input 1)
    (is (= 1 (c/rc ctx root) (c/rc ctx input)))
    (until! ctx e #(let [frame (.peekFirst ^java.util.Deque (pv (session e) "frames"))]
                    (and frame (true? (pv frame "shared")))))
    (is (= 1 (c/rc ctx root)))
    (until! ctx e #(some? (expr/state e)))
    (until! ctx e #(let [job (expr/current-job e) frame (.peekLast ^java.util.Deque (pv job "frames"))]
                    (and frame (= 5 (pv frame "stage")))))
    (let [frame (.peekLast ^java.util.Deque (pv (expr/current-job e) "frames"))]
      (is (false? (pv frame "shared")))
      (is (zero? (pv (expr/state e) "liveCacheEntries")))
      (is (= 1 (.size ^java.util.Map (pv (session e) "cache")))))
    (let [output (finish! ctx e) fields (expr/fields ctx output)]
      (is (identical? root (fields 1))) (is (sharing/mt? ctx root))
      (is (false? (sharing/mt? ctx (fields 2)))) (close-output! ctx e output))))
(deftest setter-code-fork-keeps-single-cell-empty-until-the-exact-return
  (let [label (second level/roles) {:keys [ctx headers] :as lab} (context {:defer #{label}}) parent (engine lab)
        m (level/fresh! ctx parent) a (level/name! ctx parent "steal-a") b (level/name! ctx parent "steal-b")
        l0 (level/mvar! ctx parent (expr/retain ctx parent a)) l1 (level/mvar! ctx parent (expr/retain ctx parent a))
        bv (level/mvar! ctx parent (expr/retain ctx parent b))
        m (expr/call ctx parent (str "model-setup-" label) [m b 0])
        m (expr/call ctx parent (str "model-setup-" label) [m a bv]) input (expr/bvar! ctx parent 0)]
    (start! lab parent m [l0 l1] input 1)
    (expr/constructor-request! ctx parent)
    (let [s (session parent) packet (pv s "call")
          {:keys [engine roots]} (j/fork! ctx parent [m]) child engine cm (first roots)
          ready (expr/materialize lab label)]
      (is (identical? (headers label) (.header (j/code-request ctx parent))))
      (is (nil? (pv (pv s "context") "current")))
      (is (= [false false false] (vec (pv packet "owned"))))
      (reject-restart-and-seal! ctx parent s)
      (is (g/bad? #(private-call ctx parent "takeLevelJobResult" [(class s)] [s])))
      (doseq [[e expected] [[parent m] [child cm]]]
        (is (identical? (pv (state e) "context") (pv (session e) "context")))
        (is (nil? (context-value e)))
        (j/resume-code! ready e (j/code-request ready e))
        (let [output (finish! ready e) fields (expr/fields ready output)]
          (is (identical? expected (fields 0))) (is (= [0 0] [(fields 1) (fields 3)]))
          (close-output! ready e output))))))
(deftest expr-child-host-pause-fork-and-invalid-reply-preserve-input-handoff
  (let [label (expr/roles 0)
        original (get-in (first (expr/records)) ["row" "ir" "fdecl" "body"])
        spec (h/spec "research_mixed_session_event" ["object"] [true] "object")
        body (c/let-ir 100 "object" (c/fap "model-mixed-session-event" [(c/v 1)]) original)
        {:keys [ctx] :as lab} (context {:replacements {label body} :rows [(h/ext "model-mixed-session-event" spec)] :host-specs [spec]})
        parent (engine lab) m (level/fresh! ctx parent) input (expr/bvar! ctx parent 0)]
    (start! lab parent m [0 0] input 1)
    (let [request (h/request! ctx parent) worker (expr/state parent) credit (pv worker "input")
          {:keys [engine roots]} (j/fork! ctx parent [input]) child engine ci (first roots)]
      (is (= "research_mixed_session_event" (j/request-value request "symbol")))
      (is (nil? (pv (state parent) "exprInput")))
      (is (true? (pv credit "owned"))) (is (identical? input (pv credit "value")))
      (is (identical? (budget parent) (pv worker "budget")))
      (is (g/bad? #(j/resume-host! ctx parent request (Double/valueOf 0.5))))
      (is (identical? request (j/host-request ctx parent)))
      (is (= 1 (c/rc ctx input)))
      (doseq [[e old] [[parent input] [child ci]]]
        (is (identical? (budget e) (pv (expr/state e) "budget")))
        (j/resume-host! ctx e (j/host-request ctx e) 0)
        (let [output (finish! ctx e)]
          (is (= [1] (expr/fields ctx (nth (expr/fields ctx output) 2))))
          (is (true? (pv old "dead"))) (close-output! ctx e output))))))
(deftest private-batch-entry-rejects-shape-bounds-and-aliases-before-claims
  (let [{:keys [ctx] :as lab} (context) e (engine lab) m (level/fresh! ctx e)
        root (level/succ! ctx e 0) input (expr/bvar! ctx e 0)
        before (mapv #(pv e %) ["allocations" "stores" "retains" "releases"])]
    (doseq [[levels amount] [[[root root] 1] [[0 0] -1] [[0 0] 1048576] [[0] 1] [[0 0 0] 1]]]
      (is (g/bad? #(start! lab e m levels input amount)))
      (is (= "idle" (j/phase ctx e))) (is (nil? (state e)))
      (is (= before (mapv #(pv e %) ["allocations" "stores" "retains" "releases"]))))
    (doseq [value [m root input]] (sync/release! ctx e value)) (sync/close! ctx e)))

(deftest saved-assignment-stays-owned-across-expr-job-without-an-outside-context
  (let [label (expr/roles 0) {:keys [ctx] :as lab} (context {:defer #{label}}) e (engine lab)
        m (level/fresh! ctx e) a (level/name! ctx e "saved-a") b (level/name! ctx e "saved-b")
        l0 (level/mvar! ctx e (expr/retain ctx e a)) l1 (level/mvar! ctx e (expr/retain ctx e a))
        bv (level/mvar! ctx e (expr/retain ctx e b))
        m (level/assign! ctx e m b 0) m (level/assign! ctx e m a bv) input (expr/bvar! ctx e 0)]
    (start! lab e m [l0 l1] input 1)
    (expr/constructor-request! ctx e)
    (let [s (session e) saved (pv s "saved") ready (expr/materialize lab label)]
      (is (identical? m (context-value e))) (is (= 1 (c/rc ctx m)))
      (is (= 1 (.size ^java.util.List saved)))
      (is (identical? bv (pv (.get ^java.util.List saved 0) "value")))
      (is (true? (pv (.get ^java.util.List saved 0) "owned"))) (is (= 1 (c/rc ctx bv)))
      (j/resume-code! ready e (j/code-request ready e))
      (let [output (finish! ready e)]
        (is (true? (pv bv "dead"))) (is (zero? (.size ^java.util.List saved)))
        (close-output! ready e output)))))
(deftest sealed-output-escrow-forks-and-one-branch-fails-with-exact-remaining-inputs
  (let [{:keys [ctx] :as lab} (context) parent (engine lab)
        m (level/fresh! ctx parent) a (level/name! ctx parent "drain-a") b (level/name! ctx parent "drain-b")
        root (level/succ! ctx parent (level/mvar! ctx parent (expr/retain ctx parent a)))
        bv (level/mvar! ctx parent (expr/retain ctx parent b))
        m (level/assign! ctx parent m b 0) m (level/assign! ctx parent m a bv) input (expr/bvar! ctx parent 0)]
    (start! lab parent m [(expr/retain ctx parent root) root] input 1)
    (until! ctx parent #(= 8 (pv (state parent) "stage")))
    (let [s (session parent) output-credit (pv (state parent) "output")
          {:keys [engine roots]} (j/fork! ctx parent [root bv]) child engine [cr cbv] roots]
      (is (= 3 (pv s "phase"))) (is (= 4 (pv (state parent) "outputFields")))
      (is (nil? (context-value parent))) (is (true? (pv output-credit "owned")))
      (is (zero? (.size ^java.util.Map (pv s "cache"))))
      (is (= 1 (.size ^java.util.List (pv s "saved"))))
      (reject-restart-and-seal! ctx parent s)
      (sync/private-set! (budget parent) "work" (long 999999))
      (is (false? (j/advance! ctx parent 1)))
      (is (re-find #"Mixed MVar session work outside bounded" (c/failure #(j/advance! ctx parent 1))))
      (is (true? (pv output-credit "owned")))
      (is (= [false true] (mapv #(pv % "owned") (pv (state parent) "inputs"))))
      (is (= 1 (c/rc ctx root))) (is (true? (pv (.get ^java.util.List (pv s "saved") 0) "owned")))
      (let [output (finish! ctx child) fields (expr/fields ctx output)]
        (is (identical? (fields 1) (fields 3))) (is (= 2 (c/rc ctx (fields 1))))
        (is (true? (pv cr "dead"))) (is (true? (pv cbv "dead")))
        (close-output! ctx child output)))))

(defn check! [basis] (binding [*basis* basis] (run-tests 'java-ir-mvars-session-checks)))
