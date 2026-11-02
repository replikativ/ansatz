(ns java-ir-kernel-projection-host-guest-checks
  "Tiny real HostGuest lending boundaries; synthetic owned constructor layouts,
   not source/Base/Module provenance. No image or native tool is launched."
  (:require [clojure.test :refer [deftest is run-tests]]
            [java-ir-baseline :as j] [java-ir-baseline-checks :as c]
            [java-ir-host-checks :as h] [java-ir-host-guest-checks :as hg]
            [java-ir-header-checks :as headers] [java-ir-code-checks :as code]
            [java-ir-sync-task-checks :as sync] [java-ir-release-order-checks :as order]
            [java-ir-kernel-projection-checks :as k] [ansatz.research.ir.kernel-projection :as projection]))
(def ^:dynamic *basis* nil)
(defn fixture
  ([] (fixture h/owned))
  ([outer-spec]
   (let [base (binding [sync/*basis* *basis*] (sync/task-context))
         source (j/source-binding base (Object.))
         rows [(h/ext "outer" outer-spec) (h/ext "inner" hg/inner-spec) hg/identity-row hg/nested-row]
         hs (into {} (map (fn [row] [(last (:name row)) (headers/header source row)]) rows))
         ctx (code/materialize (j/register-headers base (vec (vals hs)) [outer-spec hg/inner-spec])
                               (hs "helper") hg/identity-row [])
         engine (hg/engine ctx hs)
         nodes (mapv (fn [n] (j/graph-node ctx
                                   (update n :fields #(mapv (fn [v] (if (map? v) (j/graph-ref ctx (:ref v)) v)) %))))
                     (k/descriptors))
         [root] (j/install-graph! ctx engine
                  (j/selected-owner-graph ctx source (Object.) nodes [] [] [(j/graph-ref ctx 6)]))]
     {:ctx ctx :engine engine :headers hs :root root})))
(defn scope [ctx engine]
  (projection/open-projector ctx engine {:max-nodes 100 :deadline-nanos (+ (System/nanoTime) 10000000000)}))
(defn finish! [ctx engine outer value]
  (j/resume-host! ctx engine outer value)
  (let [answer (sync/finish! ctx engine)]
    (sync/release! ctx engine answer)
    (sync/close! ctx engine)))
(deftest actual-helper-result-lends-readonly-and-take-invalidates-both-memo-paths
  (let [{:keys [ctx engine headers root]} (fixture)]
    (j/start! ctx engine "outer" [root])
    (let [outer (j/host-request ctx engine)
          op (j/start-host-guest! ctx engine outer (headers "helper") [(j/host-transferred-argument ctx outer 0)])]
      (is (identical? op (hg/result! ctx engine)))
      (let [counts (k/counters engine) p (scope ctx engine)]
        (try
          (is (= "host-guest-result" (j/phase ctx engine)))
          (is (identical? root (.result op)))
          (is (true? (.resultOwned op))) (is (false? (.resultTaken op)))
          (is (some? (:value (k/projected p root))))
          (is (some? (:value (k/projected p root))))
          (is (= counts (k/counters engine)))
          (is (identical? root (j/take-host-guest-result! ctx engine outer op)))
          (is (thrown? Exception (k/projected p root)))
          (is (thrown? Exception ((get-in p [:carrier-ops :check!]))))
          (finally ((:close! p)))))
      (finish! ctx engine outer root))))
(deftest paused-result-fork-has-independent-record-token-and-readonly-view
  (let [{:keys [ctx engine headers root]} (fixture)]
    (j/start! ctx engine "outer" [root])
    (let [outer (j/host-request ctx engine)
          op (j/start-host-guest! ctx engine outer (headers "helper") [(j/host-transferred-argument ctx outer 0)])]
      (hg/result! ctx engine)
      (let [child (:engine (j/fork! ctx engine [])) child-op (j/host-guest-result ctx child)]
        (is (not (identical? op child-op)))
        (is (not (identical? root (.result child-op))))
        (doseq [[e token] [[engine op] [child child-op]]]
          (let [value (.result token) p (scope ctx e) before (k/counters e) request (.outerRequest token)]
            (try (is (some? (:value (k/projected p value))))
                 (is (= before (k/counters e)))
                 (finally ((:close! p))))
            (is (identical? value (j/take-host-guest-result! ctx e request token)))
            (finish! ctx e request value)))))))
(deftest claimed-host-completion-prefix-remains-valid-through-helper-lending
  (let [outer-spec (h/spec "projection_cleanup" ["object" "object"] [true true] "object")
        {:keys [ctx engine headers root]} (fixture outer-spec)
        promise (sync/promise! ctx engine) later (j/call ctx engine "cons" [3])
        dependent (sync/map! ctx engine (j/make-closure! ctx engine "inner" []) (sync/result-task! ctx engine promise))]
    (j/start! ctx engine "outer" [promise later])
    (j/resume-host! ctx engine (j/host-request ctx engine) root)
    (let [inner (h/request! ctx engine) completion (h/private-value engine "hostCompletion")]
      (is (some? completion))
      (j/retain! ctx engine root)
      (let [op (j/start-host-guest! ctx engine inner (headers "helper") [(j/host-owned-argument ctx root)])]
        (hg/result! ctx engine)
        (let [before (k/counters engine) p (scope ctx engine)]
          (try (is (some? (:value (k/projected p root))))
               (is (identical? completion (h/private-value engine "hostCompletion")))
               (is (= before (k/counters engine)))
               (finally ((:close! p)))))
        (is (identical? root (j/take-host-guest-result! ctx engine inner op))))
      (let [release (j/start-host-release! ctx engine inner (j/host-owned-argument ctx root) 1)]
        (hg/result! ctx engine) (is (= 0 (j/take-host-guest-result! ctx engine inner release))))
      (is (identical? completion (h/private-value engine "hostCompletion")))
      (j/resume-host! ctx engine inner 0)
      (is (identical? root (sync/finish! ctx engine)))
      (is (order/dead? later))
      (sync/release! ctx engine root) (sync/release! ctx engine dependent) (sync/close! ctx engine))))
(deftest inconsistent-result-record-is-not-an-admitted-lending-phase
  (let [{:keys [ctx engine headers root]} (fixture)]
    (j/start! ctx engine "outer" [root])
    (let [outer (j/host-request ctx engine)
          op (j/start-host-guest! ctx engine outer (headers "helper") [(j/host-transferred-argument ctx outer 0)])]
      (hg/result! ctx engine)
      (let [record (h/private-value engine "hostGuestRecord") p (scope ctx engine)
            before (k/counters engine)]
        (try
          (k/projected p root)
          (doseq [[field bad good] [["complete" false true] ["resultOwned" false true]
                                    ["taken" true false] ["argumentsOwned" true false]]]
            ;; Controlled state corruption isolates the admission predicate;
            ;; restore before any interpreter operation or owner claim.
            (sync/private-set! record field bad)
            (try (is (thrown? Exception (scope ctx engine)))
                 (is (thrown? Exception (k/projected p root)))
                 (finally (sync/private-set! record field good))))
          (is (= before (k/counters engine)))
          (finally ((:close! p)))))
      (is (identical? root (j/take-host-guest-result! ctx engine outer op)))
      (finish! ctx engine outer root))))
(defn check! [basis]
  (binding [*basis* basis] (run-tests 'java-ir-kernel-projection-host-guest-checks)))
