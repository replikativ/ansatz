(ns java-ir-host-guest-checks
  "Bounded same-engine parked host/helper/release control; no kernel association or Init."
  (:require [clojure.test :refer [deftest is run-tests]]
            [java-ir-baseline :as j] [java-ir-baseline-checks :as c]
            [java-ir-host-checks :as h] [java-ir-header-checks :as headers]
            [java-ir-code-checks :as code] [java-ir-generation-checks :as g]
            [java-ir-sync-task-checks :as sync] [java-ir-release-order-checks :as order]))
(def ^:dynamic *basis* nil)
(def inner-spec (h/spec "research_inner" ["object"] [false] "object"))
(def identity-row (c/decl "helper" [(c/p 1 "object")] "object" (c/ret 1)))
(def nested-row (c/decl "nested" [(c/p 1 "object")] "object"
                       (c/let-ir 2 "object" (c/fap "inner" [(c/v 1)]) (c/ret 2))))
(def cons-row (c/decl "cons" [(c/p 1 "object")] "object"
                     (c/let-ir 2 "object" (c/ctor 1 [(c/v 1)] 0) (c/ret 2))))
(defn context
  ([] (context h/owned))
  ([outer-spec]
   (let [base (j/prepare-host-program *basis* [] []) binding (j/source-binding base (Object.))
         rows [(h/ext "outer" outer-spec) (h/ext "inner" inner-spec) identity-row nested-row cons-row]
         hs (into {} (map (fn [row] [(last (:name row)) (headers/header binding row)]) rows))
         ctx (sync/active (j/register-headers base (vec (vals hs)) [outer-spec inner-spec]))
         ctx (code/materialize ctx (hs "cons") cons-row [])]
     {:ctx ctx :headers hs})))
(defn engine [ctx hs]
  (let [engine (j/machine ctx)]
    (j/configure-host-guest! ctx engine (j/host-guest-policy ctx [(hs "outer") (hs "inner")] [(hs "helper") (hs "nested")]))
    engine))
(defn result! [ctx engine]
  (loop [left 1000]
    (when (zero? left) (throw (ex-info "Helper result not reached" {})))
    (if-let [operation (j/host-guest-result ctx engine)] operation
      (do (assert (not (j/advance! ctx engine 1))) (recur (dec left))))))
(defn close! [ctx engine] (sync/close! ctx engine))
(defn finish-outer! [ctx engine request value]
  (j/resume-host! ctx engine request value) (sync/finish! ctx engine))

(deftest code-demand-forks-and-restores-the-exact-unclaimed-outer
  (let [{:keys [ctx headers]} (context) parent (engine ctx headers)]
    (j/start! ctx parent "outer" [41])
    (let [outer (j/host-request ctx parent) before (j/instructions ctx parent)
          op (j/start-host-guest! ctx parent outer (headers "helper") [(j/host-transferred-argument ctx outer 0)])]
      (is (= "running" (j/phase ctx parent))) (is (false? (j/advance! ctx parent 0)))
      (is (= before (j/instructions ctx parent)))
      (is (true? (.argumentTransferred outer 0)))
      (is (g/bad? #(j/resume-host! ctx parent outer 9)))
      (let [request (code/request! ctx parent) child (:engine (j/fork! ctx parent []))
            child-op (j/host-guest-operation ctx child) child-outer (.outerRequest child-op)
            ready (code/materialize ctx (headers "helper") identity-row [])]
        (is (not (identical? op child-op))) (is (not (identical? outer child-outer)))
        (is (g/bad? #(j/take-host-guest-result! ctx child outer op)))
        (j/resume-code! ready parent request)
        (j/resume-code! ready child (j/code-request ready child))
        (doseq [[e o token] [[parent outer op] [child child-outer child-op]]]
          (is (identical? token (result! ready e)))
          (is (= "host-guest-result" (j/phase ready e)))
          (is (false? (j/advance! ready e 10)))
          (is (g/bad? #(j/take-result! ready e)))
          (is (= 41 (j/take-host-guest-result! ready e o token)))
          (is (identical? o (j/host-request ready e)))
          (is (g/bad? #(j/take-host-guest-result! ready e o token)))
          (is (= 42 (finish-outer! ready e o 42)))
          (close! ready e))))))

(deftest nested-host-helpers-use-the-current-program-without-replaying-outer
  (let [{:keys [ctx headers]} (context)
        ctx (code/materialize ctx (headers "nested") nested-row [(headers "inner")])
        ctx (code/materialize ctx (headers "helper") identity-row []) e (engine ctx headers)]
    (j/start! ctx e "outer" [5])
    (let [a (j/host-request ctx e)
          a-op (j/start-host-guest! ctx e a (headers "nested") [(j/host-transferred-argument ctx a 0)])
          b (h/request! ctx e)
          b-op (j/start-host-guest! ctx e b (headers "helper") [(j/host-transferred-argument ctx b 0)])]
      (is (= "research_inner" (.symbol b)))
      (is (identical? b-op (result! ctx e)))
      (is (= 5 (j/take-host-guest-result! ctx e b b-op)))
      (j/resume-host! ctx e b 6)
      (is (identical? a-op (result! ctx e)))
      (is (= 6 (j/take-host-guest-result! ctx e a a-op)))
      (is (identical? a (j/host-request ctx e)))
      (is (= 7 (finish-outer! ctx e a 7))) (close! ctx e))))

(deftest transferred-owned-input-can-be-released-on-the-same-parked-request
  (let [{:keys [ctx headers]} (context) ctx (code/materialize ctx (headers "helper") identity-row [])
        e (engine ctx headers) value (j/call ctx e "cons" [3])]
    (j/start! ctx e "outer" [value])
    (let [outer (j/host-request ctx e)
          op (j/start-host-guest! ctx e outer (headers "helper") [(j/host-transferred-argument ctx outer 0)])]
      (result! ctx e) (is (identical? value (j/take-host-guest-result! ctx e outer op)))
      (is (g/bad? #(j/start-host-release! ctx e outer (j/host-transferred-argument ctx outer 0) 1)))
      (is (= 1 (c/rc ctx value)))
      (let [release (j/start-host-release! ctx e outer (j/host-owned-argument ctx value) 1)]
        (is (identical? release (result! ctx e)))
        (is (order/dead? value))
        (is (= 0 (j/take-host-guest-result! ctx e outer release))))
      (is (= 0 (finish-outer! ctx e outer 0))) (close! ctx e))))

(deftest borrowed-facade-credit-is-reserved-until-the-outer-completion
  (let [{:keys [ctx headers]} (context h/borrowed)
        ctx (code/materialize ctx (headers "helper") identity-row []) e (engine ctx headers)
        value (j/call ctx e "cons" [3])]
    (j/start! ctx e "outer" [value])
    (let [outer (j/host-request ctx e)]
      (is (g/bad? #(j/start-host-guest! ctx e outer (headers "helper") [(j/host-owned-argument ctx value)])))
      (is (g/bad? #(j/start-host-release! ctx e outer (j/host-transferred-argument ctx outer 0) 1)))
      (is (identical? outer (j/host-request ctx e))) (is (= 1 (c/rc ctx value)))
      (j/retain! ctx e value)
      (let [op (j/start-host-guest! ctx e outer (headers "helper") [(j/host-owned-argument ctx value)])]
        (result! ctx e) (j/take-host-guest-result! ctx e outer op))
      (let [op (j/start-host-release! ctx e outer (j/host-owned-argument ctx value) 1)]
        (result! ctx e) (j/take-host-guest-result! ctx e outer op))
      (is (= 1 (c/rc ctx value)))
      (is (= 0 (finish-outer! ctx e outer 0))) (is (order/dead? value)) (close! ctx e))))

(deftest nested-failure-keeps-all-parked-ancestors-and-rejects-cleanup
  (let [{:keys [ctx headers]} (context)
        ctx (code/materialize ctx (headers "nested") nested-row [(headers "inner")]) e (engine ctx headers)]
    (j/start! ctx e "outer" [0])
    (let [a (j/host-request ctx e)
          op (j/start-host-guest! ctx e a (headers "nested") [(j/host-transferred-argument ctx a 0)])
          b (h/request! ctx e)]
      (j/fail-host! ctx e b (ex-info "handler failed" {}))
      (is (= "failed" (j/phase ctx e)))
      (is (identical? op (j/host-guest-operation ctx e)))
      (is (identical? a (.outerRequest op)))
      (is (g/bad? #(j/resume-host! ctx e a 0)))
      (is (g/bad? #(j/fork! ctx e [])))
      (is (g/bad? #(j/close! ctx e))))))

(deftest callback-capable-host-release-can-demand-code-fork-and-start-another-helper
  (let [base (binding [sync/*basis* *basis*] (sync/task-context))
        binding (j/source-binding base (Object.))
        rows [(h/ext "outer" h/owned) (h/ext "inner" inner-spec) identity-row nested-row]
        hs (into {} (map (fn [row] [(last (:name row)) (headers/header binding row)]) rows))
        ctx (j/register-headers base (vec (vals hs)) [h/owned inner-spec])
        ctx (code/materialize ctx (hs "helper") identity-row [])
        ready (code/materialize ctx (hs "nested") nested-row [(hs "inner")])
        parent (engine ctx hs) p (sync/promise! ctx parent)
        source (sync/result-task! ctx parent p)
        callback (j/make-closure! ctx parent "nested" [])
        dependent (sync/map! ctx parent callback source)]
    (j/start! ctx parent "outer" [p])
    (let [outer (j/host-request ctx parent)
          release (j/start-host-release! ctx parent outer (j/host-transferred-argument ctx outer 0) 1)
          demand (code/request! ctx parent)
          {:keys [engine roots]} (j/fork! ctx parent [dependent]) child engine [child-dependent] roots]
      (is (identical? (hs "nested") (.header demand)))
      (is (false? (.argumentsOwned release)))
      (doseq [[e dep] [[parent dependent] [child child-dependent]]]
        (let [release (j/host-guest-operation ctx e) outer (.outerRequest release)]
          (j/resume-code! ready e (j/code-request ready e))
          (let [inner (h/request! ready e)
                helper (j/start-host-guest! ready e inner (hs "helper")
                                           [(j/host-transferred-argument ready inner 0)])]
            (is (= [0] (h/args inner)))
            (is (identical? helper (result! ready e)))
            (is (= 0 (j/take-host-guest-result! ready e inner helper)))
            (j/resume-host! ready e inner 0))
          (is (identical? release (result! ready e)))
          (is (= 0 (j/take-host-guest-result! ready e outer release)))
          (is (= 0 (finish-outer! ready e outer 0)))
          (is (= 2 (sync/task-state ready e dep)))
          (sync/release! ready e dep) (close! ready e))))))

(deftest nested-reply-cannot-consume-a-parked-borrowed-facade-credit
  (let [{:keys [ctx headers]} (context h/borrowed)
        ctx (code/materialize ctx (headers "nested") nested-row [(headers "inner")])
        e (engine ctx headers) value (j/call ctx e "cons" [3])]
    (j/start! ctx e "outer" [value])
    (let [outer (j/host-request ctx e)
          op (j/start-host-guest! ctx e outer (headers "nested") [(j/host-owned-argument ctx 0)])
          inner (h/request! ctx e)]
      (is (g/bad? #(j/resume-host! ctx e inner value)))
      (is (identical? inner (j/host-request ctx e))) (is (= 1 (c/rc ctx value)))
      (j/retain! ctx e value)
      (j/resume-host! ctx e inner value)
      (result! ctx e) (is (identical? value (j/take-host-guest-result! ctx e outer op)))
      (let [drop (j/start-host-release! ctx e outer (j/host-owned-argument ctx value) 1)]
        (result! ctx e) (j/take-host-guest-result! ctx e outer drop))
      (is (= 0 (finish-outer! ctx e outer 0))) (is (order/dead? value)) (close! ctx e))))

(deftest duplicate-nonfacade-borrowed-views-reserve-one-existing-credit
  (let [spec (h/spec "research_twice" ["object" "object"] [true true] "object")
        base (j/prepare-host-program *basis* [] []) binding (j/source-binding base (Object.))
        caller (c/decl "caller" [(c/p 1 "object")] "object"
                 (c/let-ir 2 "object" (c/fap "outer" [(c/v 1) (c/v 1)])
                   ["dec" {:idx 1} 1 true false (c/ret 2)]))
        rows [(h/ext "outer" spec) (h/ext "inner" inner-spec) identity-row nested-row cons-row caller]
        hs (into {} (map (fn [row] [(last (:name row)) (headers/header binding row)]) rows))
        ctx (sync/active (j/register-headers base (vec (vals hs)) [spec inner-spec]))
        ctx (code/materialize ctx (hs "cons") cons-row [])
        ctx (code/materialize ctx (hs "helper") identity-row [])
        ctx (code/materialize ctx (hs "caller") caller [(hs "outer")])
        e (engine ctx hs) value (j/call ctx e "cons" [3])]
    (j/start! ctx e "caller" [value])
    (let [outer (h/request! ctx e)]
      (is (= [value value] (h/args outer)))
      (is (g/bad? #(j/start-host-guest! ctx e outer (hs "helper") [(j/host-owned-argument ctx value)])))
      (j/retain! ctx e value)
      (let [op (j/start-host-guest! ctx e outer (hs "helper") [(j/host-owned-argument ctx value)])]
        (is (identical? op (result! ctx e)))
        (is (identical? value (j/take-host-guest-result! ctx e outer op))))
      (let [op (j/start-host-release! ctx e outer (j/host-owned-argument ctx value) 1)]
        (result! ctx e) (j/take-host-guest-result! ctx e outer op))
      (is (= 1 (c/rc ctx value)))
      (is (= 0 (finish-outer! ctx e outer 0))) (is (order/dead? value)) (close! ctx e))))

(deftest preflight-rejects-forged-authority-bad-carriers-and-repeated-transfers-without-effects
  (let [{:keys [ctx headers]} (context) e (engine ctx headers)
        wrong (headers/header (j/source-binding ctx (Object.)) identity-row)]
    (is (g/bad? #(j/configure-host-guest! ctx e (j/host-guest-policy ctx [(headers "outer")] [(headers "helper")]))))
    (j/start! ctx e "outer" [3])
    (let [outer (j/host-request ctx e) before (mapv #(h/private-value e %) ["allocations" "retains" "releases" "instructions"])]
      (is (g/bad? #(j/start-host-guest! ctx e outer wrong [(j/host-owned-argument ctx 0)])))
      (doseq [value [nil 1.25 (object-array [0]) (Object.)]]
        (is (g/bad? #(j/start-host-release! ctx e outer (j/host-owned-argument ctx value) 0))))
      (is (g/bad? #(j/start-host-release! ctx e outer (j/host-transferred-argument ctx outer 0) 0)))
      (is (g/bad? #(j/start-host-release! ctx e outer (j/host-owned-argument ctx 0) -1)))
      (is (false? (.argumentTransferred outer 0)))
      (is (identical? outer (j/host-request ctx e)))
      (is (= before (mapv #(h/private-value e %) ["allocations" "retains" "releases" "instructions"])))
      (let [op (j/start-host-release! ctx e outer (j/host-owned-argument ctx 0) 0)]
        (result! ctx e) (is (= 0 (j/take-host-guest-result! ctx e outer op))))
      (is (= 4 (finish-outer! ctx e outer 4))) (close! ctx e))))

(deftest completed-result-escrow-forks-the-same-owned-graph-and-dispositions
  (let [{:keys [ctx headers]} (context) ctx (code/materialize ctx (headers "helper") identity-row [])
        e (engine ctx headers) value (j/call ctx e "cons" [3])]
    (j/start! ctx e "outer" [value])
    (let [outer (j/host-request ctx e)
          op (j/start-host-guest! ctx e outer (headers "helper") [(j/host-transferred-argument ctx outer 0)])]
      (result! ctx e)
      (is (false? (.argumentsOwned op))) (is (true? (.resultOwned op)))
      (let [{:keys [engine roots]} (j/fork! ctx e [value]) child engine [copy] roots]
        (doseq [[machine expected] [[e value] [child copy]]]
          (let [token (j/host-guest-result ctx machine) request (.outerRequest token)]
            (is (identical? expected (.result token)))
            (is (identical? expected (first (h/args request))))
            (is (true? (.argumentTransferred request 0)))
            (is (identical? expected (j/take-host-guest-result! ctx machine request token)))
            (is (false? (.resultOwned token)))
            (is (= 1 (c/rc ctx expected)))
            (let [drop (j/start-host-release! ctx machine request (j/host-owned-argument ctx expected) 1)]
              (result! ctx machine) (j/take-host-guest-result! ctx machine request drop))
            (is (= 0 (finish-outer! ctx machine request 0)))
            (is (order/dead? expected)) (close! ctx machine)))))))

(deftest helper-entry-failure-distinguishes-escrow-from-published-frame-ownership
  (doseq [[field value published?] [["continuationDepth" (int 65536) false] ["callsLeft" (long 0) true]]]
    (let [{:keys [ctx headers]} (context) ctx (code/materialize ctx (headers "helper") identity-row [])
          e (engine ctx headers) payload (j/call ctx e "cons" [3])]
      (j/start! ctx e "outer" [payload])
      (let [outer (j/host-request ctx e)
            op (j/start-host-guest! ctx e outer (headers "helper") [(j/host-transferred-argument ctx outer 0)])]
        (sync/private-set! e field value)
        (is (g/bad? #(j/advance! ctx e 1)))
        (is (= "failed" (j/phase ctx e)))
        (is (= (not published?) (.argumentsOwned op)))
        (is (identical? payload (first (.arguments op))))
        (is (= 1 (c/rc ctx payload)))
        (is (identical? op (j/host-guest-operation ctx e)))
        (is (identical? outer (.outerRequest op)))
        (is (g/bad? #(j/start-dispose! ctx e)))
        (is (g/bad? #(j/close! ctx e)))))))

(deftest helper-inside-claimed-host-cleanup-reserves-the-outer-reply-and-future-facade
  (let [base (binding [sync/*basis* *basis*] (sync/task-context))
        outer-spec (h/spec "research_cleanup" ["object" "object"] [true true] "object")
        binding (j/source-binding base (Object.))
        rows [(h/ext "outer" outer-spec) (h/ext "inner" inner-spec) identity-row nested-row]
        hs (into {} (map (fn [row] [(last (:name row)) (headers/header binding row)]) rows))
        ctx (j/register-headers base (vec (vals hs)) [outer-spec inner-spec])
        ctx (code/materialize ctx (hs "helper") identity-row [])
        e (engine ctx hs) p (sync/promise! ctx e) later (j/call ctx e "cons" [3])
        reply (j/call ctx e "cons" [4])
        dependent (sync/map! ctx e (j/make-closure! ctx e "inner" []) (sync/result-task! ctx e p))]
    (j/start! ctx e "outer" [p later])
    (j/resume-host! ctx e (j/host-request ctx e) reply)
    (let [inner (h/request! ctx e)
          fork (j/fork! ctx e [later reply dependent]) child (:engine fork)
          [child-later child-reply child-dep] (:roots fork)
          failed (:engine (j/fork! ctx e []))
          failed-inner (j/host-request ctx failed)
          failed-completion (h/private-value failed "hostCompletion")
          failed-op (j/start-host-guest! ctx failed failed-inner (hs "helper") [(j/host-owned-argument ctx 0)])]
      (sync/private-set! failed "continuationDepth" (int 65536))
      (is (g/bad? #(j/advance! ctx failed 1)))
      (is (= "failed" (j/phase ctx failed)))
      (is (identical? failed-completion (h/private-value failed "hostCompletion")))
      (is (identical? failed-inner (.outerRequest failed-op)))
      (is (true? (.argumentsOwned failed-op)))
      (is (true? (h/private-value failed-completion "resultOwned")))
      (is (g/bad? #(j/close! ctx failed)))
      (doseq [[machine next-value answer dep] [[e later reply dependent] [child child-later child-reply child-dep]]]
        (let [inner (j/host-request ctx machine) completion (h/private-value machine "hostCompletion")]
          (is (true? (h/private-value completion "adapterReleaseStarted")))
          (doseq [protected [answer next-value]]
            (is (g/bad? #(j/start-host-guest! ctx machine inner (hs "helper") [(j/host-owned-argument ctx protected)]))))
          (j/retain! ctx machine answer)
          (let [op (j/start-host-guest! ctx machine inner (hs "helper") [(j/host-owned-argument ctx answer)])]
            (result! ctx machine) (is (identical? answer (j/take-host-guest-result! ctx machine inner op))))
          (let [op (j/start-host-release! ctx machine inner (j/host-owned-argument ctx answer) 1)]
            (result! ctx machine) (j/take-host-guest-result! ctx machine inner op))
          (is (identical? completion (h/private-value machine "hostCompletion")))
          (j/resume-host! ctx machine inner 0)
          (is (identical? answer (sync/finish! ctx machine)))
          (is (order/dead? next-value)) (is (= 1 (c/rc ctx answer)))
          (sync/release! ctx machine answer) (sync/release! ctx machine dep) (close! ctx machine))))))

(defn check! [basis] (binding [*basis* basis] (run-tests 'java-ir-host-guest-checks)))
