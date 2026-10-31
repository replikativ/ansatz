(ns java-ir-expr-delayed-control-checks
  "Private Stage4 continuation/failure models, separate from the semantic slice."
  (:refer-clojure :exclude [run!])
  (:require [clojure.test :refer [deftest is run-tests]]
            [java-ir-baseline :as j] [java-ir-baseline-checks :as c]
            [java-ir-expr-delayed-checks :as foundation]
            [java-ir-expr-direct-checks :as direct] [java-ir-expr-machinery-checks :as expr]
            [java-ir-level-mvars-checks :as level] [java-ir-sync-task-checks :as sync]
            [java-ir-host-checks :as h] [java-ir-generation-checks :as g]
            [java-ir-logical-sharing-checks :as sharing]))
(def ^:dynamic *basis* nil)
(def pv expr/private-value)
(defn context ([] (context {})) ([options] (binding [foundation/*basis* *basis*] (foundation/context options))))
(def engine foundation/engine)
(def state foundation/state)
(def session foundation/session)
(def action foundation/action)
(def start! foundation/start!)
(def run! foundation/run!)
(def close! foundation/close!)
(def array! foundation/array!)
(def named-fvar! foundation/named-fvar!)
(def delayed-with-fvars! foundation/delayed-with-fvars!)
(deftest resolver-each-helper-code-publication-forks-own-options-temporaries-and-cell
  (doseq [label (mapv direct/helpers [0 1 2 3])]
    (let [{:keys [ctx headers] :as lab} (context {:rows (direct/delayed-model-rows) :defer #{label}})
          parent (engine lab) m (level/fresh! ctx parent) n (level/name! ctx parent "code-head") pending (level/name! ctx parent "code-pending")
          input (expr/app! ctx parent (direct/mvar! ctx parent (expr/retain ctx parent n)) (expr/sort! ctx parent))
          m (direct/assign! ctx parent m (expr/retain ctx parent pending) (expr/fvar! ctx parent "assigned"))
          [m record] (delayed-with-fvars! ctx parent m n pending (array! ctx parent []))]
      (start! lab parent 1 m [input] [[4 0]]) (expr/until! ctx parent #(some? (j/code-request ctx parent)))
      (let [packet (pv (session parent) "call") request (j/code-request ctx parent)
            {:keys [engine roots]} (j/fork! ctx parent [m input record]) child engine ready (expr/materialize lab label)]
        (is (identical? (headers label) (.header request))) (is (true? (pv packet "entered")))
        (is (every? false? (vec (pv packet "owned"))))
        (when (#{(direct/helpers 2) (direct/helpers 3)} label) (is (= 4 (c/rc ctx record))))
        (doseq [e [parent child]]
          (is (identical? (pv (state e) "context") (pv (session e) "context")))
          (is (identical? (pv (state e) "budget") (pv (session e) "budget")))
          (j/resume-code! ready e (j/code-request ready e))
          (let [report (expr/finish-research! ready e)] (is (= 1 (nth (expr/fields ready report) 2))) (close! ready e report)))))))
(deftest borrowed-lift-constructor-code-fork-preserves-input-heuristic-and-shared-budget
  (let [label (expr/roles 0) {:keys [ctx] :as lab} (context {:defer #{label}}) parent (engine lab)
        m (level/fresh! ctx parent) name (level/name! ctx parent "lift-code") p (expr/bvar! ctx parent 0)
        fvars (array! ctx parent [(named-fvar! ctx parent (expr/retain ctx parent name))]) args (array! ctx parent [p])]
    (start! lab parent 2 m [fvars args name] [[5 0 1 0] [7 2 2] [6]])
    (expr/constructor-request! ctx parent)
    (let [worker (expr/state parent) lookup (pv (session parent) "lookup")
          {:keys [engine roots]} (j/fork! ctx parent [p]) child engine cp (first roots) ready (expr/materialize lab label)]
      (is (nil? (pv worker "input"))) (is (= 3 (c/rc ctx p)))
      (is (identical? p (pv (pv (pv lookup "entry") "value") "value")))
      (doseq [[e ep] [[parent p] [child cp]]]
        (is (identical? (pv (session e) "budget") (pv (expr/state e) "budget")))
        (is (identical? ep (pv (expr/current-job e) "input")))
        (j/resume-code! ready e (j/code-request ready e))
        (expr/until! ready e #(= 2 (pv (state e) "commandCursor")))
        (is (= [2] (expr/fields ready (pv (pv (state e) "lastResult") "value"))))
        (let [report (expr/finish-research! ready e)] (close! ready e report))))))
(deftest resolver-host-fork-invalid-reply-and-exit-sharing-resample
  (let [label (direct/helpers 1) entry (first (filter #(= label (get % "label")) (direct/originals)))
        body (get-in entry ["row" "ir" "fdecl" "body"])
        event (h/spec "research_resolver_event" ["object"] [true] "object")
        replacement (c/let-ir 100 "object" (c/fap "model-resolver-event" [(c/v 1)]) body)
        {:keys [ctx] :as lab} (context {:rows (concat (direct/delayed-model-rows) [(h/ext "model-resolver-event" event)])
                                      :host-specs [event] :replacements {label replacement}})
        parent (engine lab) m (level/fresh! ctx parent) n (level/name! ctx parent "host-head") pending (level/name! ctx parent "host-pending")
        input (expr/app! ctx parent (direct/mvar! ctx parent (expr/retain ctx parent n)) (expr/sort! ctx parent))
        m (direct/assign! ctx parent m (expr/retain ctx parent pending) (expr/sort! ctx parent))
        [m _] (delayed-with-fvars! ctx parent m n pending (array! ctx parent []))]
    (start! lab parent 1 m [input] [[4 0]])
    (let [request (h/request! ctx parent) root-frame (first (pv (session parent) "resolver"))]
      (is (false? (pv root-frame "entryShared")))
      (is (g/bad? #(j/resume-host! ctx parent request (Double/valueOf 0.5))))
      (is (identical? request (j/host-request ctx parent)))
      ;; Controlled private marking during a modeled Host pause changes the exit
      ;; sharing sample without inventing another guest RC owner.
      (sharing/mark! ctx parent input)
      (let [{:keys [engine roots]} (j/fork! ctx parent [input]) child engine ci (first roots)]
        (doseq [[e root] [[parent input] [child ci]]]
          (j/resume-host! ctx e (j/host-request ctx e) 0)
          (expr/until! ctx e #(= 1 (pv (state e) "commandCursor")))
          (is (= true (.get ^java.util.Map (pv (session e) "resolvableExpressions") root)))
          (let [report (expr/finish-research! ctx e)] (is (= 1 (nth (expr/fields ctx report) 2))) (close! ctx e report)))))))
(deftest cache-member-drain-demands-finalizer-code-host-and-forks-owned-disposition
  ;; Deliberately nonnominal Expr-shaped storage model: its two fields own a
  ;; genuine Promise and waiting mapped Task. Cache code is shape-only; this
  ;; verifies release control, not a source-produced Expr/MData value.
  (let [event (h/spec "research_cache_drain_event" ["object"] [true] "object")
        finalizer (c/decl "model-cache-drain-finalizer" [(c/p 1 "object")] "object"
                    (c/let-ir 2 "object" (c/fap "model-cache-drain-event" [(c/v 1)])
                      ["dec" {:idx 1} 1 false false (c/ret 2)]))
        build (c/decl "model-cache-drain-value" [(c/p 1 "object")] "object"
                (c/let-ir 10 "object" (c/lit 1)
                  (c/let-ir 3 "object" (sync/sfap "IO.Promise.new._boxed" ["erased" "erased" "erased"])
                    ["inc" {:idx 3} 1 false false
                     (c/let-ir 4 "object" (sync/sfap "IO.Promise.result?._boxed" ["erased" (c/v 3)])
                       (c/let-ir 5 "object" {:pap {:c (c/name-ir "model-cache-drain-finalizer") :ys []}}
                         (c/let-ir 6 "object" (sync/sfap "Task.map._boxed" ["erased" "erased" (c/v 5) (c/v 4) "erased" (c/v 10)])
                           ["inc" {:idx 6} 1 false false
                            (c/let-ir 7 "object" (c/ctor 10 [(c/v 3) (c/v 6)] 8)
                              (c/let-ir 8 "object" (c/ctor 0 [(c/v 6) (c/v 7)] 0)
                                ["dec" {:idx 1} 1 false false (c/ret 8)]))])))])))
        {:keys [ctx headers] :as lab} (context {:tasks true :rows [(h/ext "model-cache-drain-event" event) finalizer build]
                                               :host-specs [event] :defer #{"model-cache-drain-finalizer"}})
        parent (engine lab) key (expr/bvar! ctx parent 0) other (expr/bvar! ctx parent 1)
        built (expr/call ctx parent "model-cache-drain-value" [0])
        [task value] (expr/fields ctx built)
        ;; CACHE protocol does not inspect its opaque context. This independent
        ;; Task owner prevents pure-dependent deactivation before Promise drop.
        m (expr/retain ctx parent task) value (expr/retain ctx parent value)]
    (sync/release! ctx parent built)
    (start! lab parent 0 m [key value other] [[3 0 0 1 0] [2 2 0]])
    (expr/constructor-request! ctx parent)
    (let [cache (pv (session parent) "cache") entry (pv cache "retiringEntry")
          {:keys [engine]} (j/fork! ctx parent []) child engine ready (expr/materialize lab "model-cache-drain-finalizer")]
      (is (identical? (headers "model-cache-drain-finalizer") (.header (j/code-request ctx parent))))
      (is (= 1 (pv cache "liveEntries"))) (is (false? (pv (pv entry "result") "owned")))
      (doseq [e [parent child]]
        (is (= 1 (pv (pv (session e) "cache") "liveEntries")))
        (j/resume-code! ready e (j/code-request ready e))
        (let [r (h/request! ready e)] (is (= "research_cache_drain_event" (j/request-value r "symbol")))
          (is (= [0] (h/args r))) (j/resume-host! ready e r 0))
        (let [report (expr/finish-research! ready e)] (is (= 0 (second (expr/fields ready report))))
          (is (nil? (session e))) (close! ready e report))))))
(deftest malformed-fvars-accessor-keeps-owned-return-option-and-record-temporary
  (let [label (direct/helpers 2)
        body ["dec" {:idx 1} 1 false false
              (c/let-ir 3 "object" (c/lit 0) (c/let-ir 4 "object" (c/ctor 2 [(c/v 3)] 0) (c/ret 4)))]
        {:keys [ctx] :as lab} (context {:rows (direct/delayed-model-rows) :replacements {label body}})
        e (engine lab) m (level/fresh! ctx e) n (level/name! ctx e "invalid-fvars")
        input (expr/app! ctx e (direct/mvar! ctx e (expr/retain ctx e n)) (expr/sort! ctx e))
        [m record] (delayed-with-fvars! ctx e m n (level/name! ctx e "pending") (array! ctx e []))]
    (start! lab e 1 m [input] [[4 0]])
    (is (re-find #"fvars accessor" (c/failure #(expr/finish-research! ctx e))))
    (let [a (action e) receiver (aget ^objects (pv e "objects") (pv a "slot"))
          frame (.peekLast ^java.util.Deque (pv (session e) "resolver"))]
      (is (= 2 (.getInt ^java.lang.reflect.Field (:tag ctx) receiver))) (is (= 1 (c/rc ctx receiver)))
      (is (true? (pv (pv frame "recordTemporary") "owned"))) (is (true? (pv (pv frame "option") "owned")))
      (is (= 3 (c/rc ctx record))) (is (some? (pv (session e) "call"))))))
(deftest private-protocol-preflight-rejects-scope-commands-aliases-and-inactive-before-claims
  (let [{:keys [ctx] :as lab} (context) e (engine lab) m (level/fresh! ctx e) key (expr/bvar! ctx e 0)
        before (mapv #(pv e %) ["allocations" "stores" "retains" "releases"])]
    (doseq [[mode anchors commands] [[0 [key] [[1]]] [0 [key] [[3 0 0 0 -1]]]
                                    [0 [key key] [[2 0 0]]] [1 [key] [[4 1]]] [2 [key] [[5 0 0 0]]]]]
      (is (g/bad? #(start! lab e mode m anchors commands))) (is (= "idle" (j/phase ctx e)))
      (is (= 1 (c/rc ctx m) (c/rc ctx key))) (is (nil? (state e)))
      (is (= before (mapv #(pv e %) ["allocations" "stores" "retains" "releases"]))))
    (sync/release! ctx e m) (sync/release! ctx e key) (sync/close! ctx e))
  (let [{:keys [ctx] :as lab} (context {:inactive true}) e (j/machine ctx) key (expr/bvar! ctx e 0)]
    (is (g/bad? #(start! lab e 0 0 [key] [[2 0 0]]))) (is (= "idle" (j/phase ctx e)))
    (is (= 1 (c/rc ctx key))) (j/release! ctx e key) (j/close! ctx e)))
(deftest named-cache-cap-work-and-interruption-fail-with-explicit-owned-escrow
  (let [{:keys [ctx] :as lab} (context) e (engine lab) m (level/fresh! ctx e)
        key (expr/bvar! ctx e 0) value (expr/fvar! ctx e "capacity")]
    (start! lab e 0 m [key value] [[3 0 0 1 0]])
    (expr/until! ctx e #(let [op (pv (session e) "cacheOperation")] (and op (= 14 (pv op "stage")))))
    (let [op (pv (session e) "cacheOperation") before (c/rc ctx value)]
      ;; Forged resource-ledger boundary, not fabricated guest/source heap data.
      (sync/private-set! (pv (session e) "cache") "liveEntries" (int 100000))
      (is (re-find #"live-entry bound" (c/failure #(j/advance! ctx e 1))))
      (is (true? (pv (pv op "computed") "owned"))) (is (true? (pv (pv op "shared") "owned")))
      (is (nil? (pv op "newEntry"))) (is (= before (c/rc ctx value)))))
  (doseq [kind [:work :interrupt]]
    (let [{:keys [ctx] :as lab} (context) e (engine lab) m (level/fresh! ctx e) key (expr/bvar! ctx e 0) outcome (atom nil)]
      (start! lab e 0 m [key] [[2 0 0]])
      (sync/private-set! (pv (session e) "budget") "work" (long (if (= kind :work) 1000000 1023)))
      (if (= kind :work) (reset! outcome (c/failure #(j/advance! ctx e 1)))
        (let [worker (Thread. ^Runnable (fn [] (.interrupt (Thread/currentThread))
                                         (try (reset! outcome (c/failure #(j/advance! ctx e 1)))
                                              (finally (Thread/interrupted)))))]
          (.start worker) (.join worker 1000) (is (not (.isAlive worker)))))
      (is (re-find (if (= kind :work) #"work outside bounded" #"interrupted") (or @outcome "")))
      (is (= 1 (c/rc ctx m) (c/rc ctx key)))
      (is (true? (pv (first (pv (state e) "anchors")) "owned")))
      (is (true? (pv (pv (pv (session e) "context") "current") "owned"))))))
(deftest helper-code-reply-preclaim-and-post-frame-tick-failure-keep-their-disposition
  (let [label (direct/helpers 1) {:keys [ctx] :as lab} (context {:defer #{label}}) e (engine lab)
        m (level/fresh! ctx e) input (expr/app! ctx e (direct/mvar! ctx e (level/name! ctx e "tick")) (expr/sort! ctx e))]
    (start! lab e 1 m [input] [[4 0]]) (expr/until! ctx e #(some? (j/code-request ctx e)))
    (let [request (j/code-request ctx e) packet (pv (session e) "call") ready (expr/materialize lab label)]
      (is (g/bad? #(j/resume-code! ctx e request)))
      (is (identical? request (j/code-request ctx e))) (is (= "code-call" (j/phase ctx e)))
      (is (= 2 (c/rc ctx m))) (is (every? false? (vec (pv packet "owned"))))
      (sync/private-set! e "callsLeft" (long 0))
      (is (re-find #"Call/loop budget" (c/failure #(j/resume-code! ready e request))))
      (is (= "failed" (j/phase ready e))) (is (true? (pv packet "entered")))
      (is (every? false? (vec (pv packet "owned")))) (is (identical? request (pv e "failedCodeRequest")))
      (is (= 2 (c/rc ctx m))) (is (= 1 (c/rc ctx input)))
      (is (nil? (pv (state e) "output"))))))
(defn check! [basis] (binding [*basis* basis] (run-tests 'java-ir-expr-delayed-control-checks)))
