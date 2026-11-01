(ns prototype.raw-boundary-test
  "Draft-only callback protocol tests; no native frontend compatibility claim."
  (:require [clojure.test :refer [deftest is]]
            [prototype.raw-interop :as raw]
            [prototype.raw-interop-test :as fixture]
            [prototype.machine :as m]))

(defn failure [f] (try (f) nil (catch clojure.lang.ExceptionInfo e e)))
(defn advance [session world args]
  (raw/advance-to-boundary session (m/start world fixture/root args)))
(def helper ["str" ["anonymous"] "boundary-helper"])

(deftest yield-is-unstarted-and-completion-does-not-step-the-outer-guest
  (doseq [backend fixture/backends]
    (let [effects (atom 0)
          s (fixture/session backend "yield" (fixture/binding-for [fixture/owned] "object"
                (fn [_ world [x]] (swap! effects inc) [world x])) {})
          s (assoc s :fuel 1)
          [before value] (m/resource (m/world (:functions s)) "owned")
          boundary (advance s before [value]) at (:state boundary)]
      (is (= :boundary (:status boundary)))
      (is (= 0 @effects))
      (is (= 1 (:rc (m/node at value))))
      (is (= (:heap before) (:heap at)))
      (let [completed (raw/complete-host-boundary (:token boundary) {:helper-fuel 0})
            after (:state completed)]
        (is (= 1 @effects))
        (is (= :handler-completed (:status completed)))
        (is (= :running (:status after)))
        (is (= (:stats at) (:stats after)))
        (is (= (:heap at) (:heap after)))
        (is (= 0 (:helper-steps completed)))
        (is (identical? s (:session completed)))
        (is (failure #(raw/complete-host-boundary (:token boundary) {:helper-fuel 0})))
        (is (= 1 @effects))
        (let [done (raw/advance-to-boundary (:session completed) after)]
          (is (= :done (:status done)))
          (is (= value (:value done)))
          (is (= [[:released "owned"]] (:events (m/release (:state done) value 1)))))))))

(deftest default-exact-fuel-and-cooperative-pauses-remain-distinct
  (doseq [backend fixture/backends]
    (let [effects (atom 0)
          s (fixture/session backend "default" (fixture/binding-for [] "object"
                (fn [_ world _] (swap! effects inc) [world 42])) {})
          before (m/world (:functions s))
          s (assoc s :fuel 1)
          error (failure #(raw/call s before fixture/root []))]
      ;; Existing continue still invokes the reached host handler then exhausts
      ;; before the guest return; new advance yields before that handler.
      (is (= 1 @effects))
      (is (= :paused (get-in (ex-data error) [:checkpoint :status])))
      (let [pause (advance (assoc s :fuel 0) before [])]
        (is (= :paused (:status pause)))
        (is (nil? (:token pause)))
        (is (= 1 @effects))
        (let [boundary (raw/advance-to-boundary s (:state pause))]
          (is (= :boundary (:status boundary)))
          (is (= 1 @effects)))))))

(deftest completion-transfers-owned-and-retains-borrowed-through-real-helper
  (doseq [backend fixture/backends]
    (let [escaped (atom nil)
          s (fixture/session backend "owners"
                (fixture/binding-for [fixture/owned fixture/borrowed] "object"
                  (fn [{:keys [invoke]} world [owned borrowed]]
                    (reset! escaped [invoke world])
                    (invoke (m/retain world borrowed 1) helper [owned borrowed])))
                {helper {:params [1 2] :body [:let 3 [:ctor 0 [[:var 1] [:var 2]]] [:return [:var 3]]]}})
          [before a] (m/resource (m/world (:functions s)) "a")
          [before b] (m/resource before "b")
          boundary (advance (assoc s :fuel 1) before [a b])
          completed (raw/complete-host-boundary (:token boundary) {:helper-fuel 2})
          [invoke entry] @escaped
          done (raw/advance-to-boundary (:session completed) (:state completed))
          state (:state done) value (:value done)]
      (is (= 2 (:helper-steps completed)))
      (is (= [a b] (:fields (m/node state value))))
      (is (= 1 (:rc (m/node state a))))
      (is (= 2 (:rc (m/node state b))))
      (is (= 1 (:rc (m/node before b))))
      (is (failure #(invoke entry helper [a b])))
      (let [released (m/release state value 1)]
        (is (= [[:released "a"]] (:events released)))
        (is (= 1 (:rc (m/node released b))))))))

(deftest nested-callbacks-remain-synchronous-and-share-one-helper-budget
  (doseq [backend fixture/backends]
    (let [inner ["str" ["anonymous"] "inner-boundary"]
          calls (atom [])
          bindings {"outer" (fixture/binding-for [] "object"
                               (fn [{:keys [invoke]} world _]
                                 (swap! calls conj :outer)
                                 (invoke world inner [])))
                    "inner" (fixture/binding-for [] "object"
                               (fn [{:keys [invoke]} world _]
                                 (swap! calls conj :inner)
                                 (invoke world helper [])))}
          inner-row (-> (fixture/row "inner" [] "object")
                        (assoc :name inner) (assoc-in [:ir :extern :f] inner))
          functions {fixture/root (second (raw/lower bindings (fixture/row "outer" [] "object")))
                     inner (second (raw/lower bindings inner-row))
                     helper {:params [] :body [:return [:imm 42]]}}
          s (raw/open-functions functions bindings {:backend backend :fuel 1})
          boundary (advance s (m/world functions) [])
          completed (raw/complete-host-boundary (:token boundary) {:helper-fuel 3})]
      (is (= [:outer :inner] @calls))
      (is (= 3 (:helper-steps completed))) ; inner host + helper return + inner return
      (is (= :running (get-in completed [:state :status])))
      (let [done (raw/advance-to-boundary (:session completed) (:state completed))]
        (is (= 42 (:value done)))))))

(deftest aggregate-helper-budget-cannot-reset-by-invoking-an-earlier-fork
  (doseq [backend fixture/backends]
    (let [calls (atom 0)
          s (fixture/session backend "aggregate" (fixture/binding-for [] "object"
                (fn [{:keys [invoke]} world _]
                  (swap! calls inc)
                  (invoke world helper [])
                  ;; Deliberate old-world helper branch must still be charged.
                  (invoke world helper [])))
                {helper {:params [] :body [:return [:imm 42]]}})
          boundary (advance s (m/world (:functions s)) [])
          error (failure #(raw/complete-host-boundary (:token boundary) {:helper-fuel 1}))
          data (ex-data error)]
      (is (= 1 @calls))
      (is (= :failed (:boundary-completion data)))
      (is (true? (:boundary-token-consumed? data)))
      (is (= :paused (get-in data [:checkpoint :status])))
      (is (= :host-call (get-in data [:host-boundary-checkpoint :status])))
      (is (seq (:host-boundaries data)))
      (is (failure #(raw/complete-host-boundary (:token boundary) {:helper-fuel 100})))
      (is (= 1 @calls)))))

(deftest started-nested-failure-is-terminal-not-a-continuation-or-io-retry
  (doseq [backend fixture/backends]
    (let [effects (atom 0)
          s (fixture/session backend "effect-then-fail" (fixture/binding-for [fixture/owned] "object"
                (fn [{:keys [invoke checkpoint!]} world [value]]
                  (swap! effects inc)
                  (let [world (checkpoint! (m/release world value 1))]
                    (invoke world helper []))))
                {helper {:params [] :body [:unreachable]}})
          [before value] (m/resource (m/world (:functions s)) "effect-owner")
          boundary (advance s before [value])
          error (failure #(raw/complete-host-boundary (:token boundary) {:helper-fuel 10}))
          data (ex-data error)]
      (is (= 1 @effects))
      (is (true? (:boundary-token-consumed? data)))
      (is (= [[:released "effect-owner"]] (get-in data [:checkpoint :events])))
      (is (= [] (:events (:unstarted-outer-checkpoint data))))
      (is (= 1 (:rc (m/node (:unstarted-outer-checkpoint data) value))))
      (is (identical? (:session boundary) (:unstarted-outer-session data)))
      (is (failure #(raw/complete-host-boundary (:token boundary) {:helper-fuel 10})))
      (is (= 1 @effects)))))

(deftest session-adoption-is-returned-without-an-outer-guest-step
  (doseq [backend fixture/backends]
    (let [new-backend (if (= backend :jvm) :mutable :jvm)
          s (fixture/session backend "adopt" (fixture/binding-for [] "object"
                (fn [{:keys [switch-backend! invoke]} world _]
                  (let [world (switch-backend! world new-backend)]
                    (invoke world helper []))))
                {helper {:params [] :body [:return [:imm 42]]}})
          boundary (advance s (m/world (:functions s)) [])
          completed (raw/complete-host-boundary (:token boundary) {:helper-fuel 1})]
      (is (= new-backend (get-in completed [:session :backend])))
      (is (identical? (:functions s) (get-in completed [:session :functions])))
      (is (= 1 (:helper-steps completed)))
      (is (= 42 (:value (raw/advance-to-boundary (:session completed) (:state completed))))))))

(deftest invalid-options-do-not-claim-and-racing-completers-run-once
  (let [calls (atom 0)
        s (fixture/session :reference "once" (fixture/binding-for [] "object"
              (fn [_ world _] (swap! calls inc) [world 42])) {})
        boundary (advance s (m/world (:functions s)) []) token (:token boundary)]
    (doseq [options [{} {:helper-fuel -1} {:helper-fuel 1 :other true}]]
      (is (failure #(raw/complete-host-boundary token options))))
    (is (= 0 @calls))
    (let [start (promise)
          attempt (fn [] @start (try (raw/complete-host-boundary token {:helper-fuel 0})
                                    (catch clojure.lang.ExceptionInfo _ :consumed)))
          a (future (attempt)) b (future (attempt))]
      (deliver start true)
      (is (= #{:handler-completed :consumed}
             (set (map #(if (= :consumed %) % (:status %)) [@a @b]))))
      (is (= 1 @calls)))))

(deftest reentrant-completion-cannot-reenter-the-same-handler
  (let [holder (atom nil) calls (atom 0)
        s (fixture/session :reference "reentrant" (fixture/binding-for [] "object"
              (fn [_ world _]
                (swap! calls inc)
                (is (failure #(raw/complete-host-boundary @holder {:helper-fuel 0})))
                [world 42])) {})
        boundary (advance s (m/world (:functions s)) [])]
    (reset! holder (:token boundary))
    (is (= :handler-completed
           (:status (raw/complete-host-boundary @holder {:helper-fuel 0}))))
    (is (= 1 @calls))))

(deftest compiled-installation-and-trusted-linking-return-the-new-active-session
  (let [linked ["str" ["anonymous"] "boundary-linkedSeven"]
        catalogue {:manifests [{:kind "manifest" :schema "lean-ir-probe/1" :leanVersion "4.33.1"
                               :runtimeProfile {:target "x86_64-unknown-linux-gnu" :wordBits 64}}]
                   :declarations {linked {:kind "decl" :name linked :runtime {:role "ordinary" :initializer nil}
                                          :ir {:fdecl {:f linked :xs [] :type "object"
                                                       :body ["vdecl" {:idx 1} "object" {:lit {:v {:num {:v 7}}}}
                                                              ["ret" {:var {:id {:idx 1}}}]]}}}}}
        s (fixture/session :reference "install-link" (fixture/binding-for [fixture/owned] "object"
              (fn [{:keys [install-compiled! link-trusted! invoke]} world [input]]
                (let [[world installed] (install-compiled! world (slurp "fixtures/runtime-compiled-identity.jsonl") {})
                      [world value] (invoke world (get (:boxed-entrypoints installed) ["str" ["anonymous"] "answer"])
                                           [m/erased input])
                      [world _] (link-trusted! world catalogue [linked]
                                              (fn [_ added] (is (contains? added linked))))
                      [world seven] (invoke world linked [])]
                  (is (= 7 seven))
                  [world value]))) {})
        [before value] (m/resource (m/world (:functions s)) "installed-owner")
        boundary (advance (assoc s :fuel 1) before [value])
        completed (raw/complete-host-boundary (:token boundary) {:helper-fuel 1000})
        session (:session completed) state (:state completed)]
    (is (contains? (:functions session) linked))
    (is (identical? (:functions session) (:functions state)))
    (is (identical? (get-in s [:functions fixture/root]) (get-in session [:functions fixture/root])))
    (is (not (contains? (:functions before) linked)))
    (is (= 1 (:rc (m/node state value))))
    (is (= value (:value (raw/advance-to-boundary (assoc session :fuel 1000) state))))))

(deftest caught-throwing-helper-cannot-recover-unaccounted-budget-from-old-world
  (doseq [backend fixture/backends]
    (let [good ["str" ["anonymous"] "after-failed-helper"]
          caught (atom false) retried-value (atom nil)
          s (fixture/session backend "catch-then-reinvoke"
                (fixture/binding-for [] "object"
                  (fn [{:keys [invoke]} world _]
                    ;; The backend consumes a let step, then throws before a
                    ;; frozen result can report an exact consumed-step count.
                    (is (failure #(invoke world helper [])))
                    (reset! caught true)
                    (let [[world result] (invoke world good [])]
                      (reset! retried-value result)
                      [world result])))
                {helper {:params [] :body [:let 1 [:literal 1] [:unreachable]]}
                 good {:params [] :body [:return [:imm 42]]}})
          boundary (advance s (m/world (:functions s)) [])
          error (failure #(raw/complete-host-boundary (:token boundary) {:helper-fuel 100}))
          data (ex-data error)]
      (is @caught)
      (is (nil? @retried-value))
      (is (= :failed (:boundary-completion data)))
      (is (re-find #"poisoned" (.getMessage error)))
      (is (true? (:boundary-token-consumed? data)))
      (is (failure #(raw/complete-host-boundary (:token boundary) {:helper-fuel 100}))))))


(deftest caught-backend-failure-cannot-be-turned-into-a-success-receipt
  (doseq [backend fixture/backends]
    (let [s (fixture/session backend "catch-and-return"
                (fixture/binding-for [] "object"
                  (fn [{:keys [invoke]} world _]
                    (is (failure #(invoke world helper [])))
                    [world 42]))
                {helper {:params [] :body [:let 1 [:literal 1] [:unreachable]]}})
          before (m/world (:functions s))
          ordinary (raw/call s before fixture/root [])
          boundary (advance s before [])
          error (failure #(raw/complete-host-boundary (:token boundary) {:helper-fuel 100}))
          data (ex-data error)]
      ;; Exactly the same catch-and-return handler remains supported by the
      ;; existing default driver; only explicit cooperative completion poisons.
      (is (= 42 (:value ordinary)))
      (is (= :done (get-in ordinary [:state :status])))
      (is (re-find #"poisoned" (.getMessage error)))
      (is (= :failed (:boundary-completion data)))
      (is (= 42 (:unresumed-host-result data)))
      (is (= :host-call (get-in data [:checkpoint :status])))
      (is (not (contains? data :helper-steps))))))
