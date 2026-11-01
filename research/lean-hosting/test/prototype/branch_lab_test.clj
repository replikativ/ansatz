(ns prototype.branch-lab-test
  (:require [clojure.test :refer [deftest is testing]]
            [prototype.branch-lab :as lab]
            [prototype.machine :as m]))

(def backends [:persistent :mutable :compiled])
(defn rejected? [f]
  (try (f) false (catch clojure.lang.ExceptionInfo _ true)))

(defn trial [backend]
  (let [{:keys [world cell functions]} (lab/fixture)
        basis {:version 1 :definition :old}
        s (lab/session world basis)
        original (lab/snapshot s (:initial s))
        [left right] (lab/fork! s (:initial s))
        run (lab/runner backend functions)
        left (lab/advance! s left run 10)
        right (lab/advance! s right run 20)
        l (lab/snapshot s left) r (lab/snapshot s right)]
    (is (= 0 (first (:fields (m/node (:world original) cell)))))
    (is (= [10 20] (mapv #(get-in % [:world :result]) [l r])))
    (is (= [10 20] (mapv #(first (:fields (m/node (:world %) cell))) [l r])))
    (is (= [[10] [20]] (mapv :outbox [l r])))
    (is (every? #(identical? basis (:basis %)) [original l r]))
    ;; Snapshot maps cannot be substituted for consumed or live authorities.
    (is (rejected? #(lab/fork! s (:initial s))))
    (is (rejected? #(lab/advance! s original run 99)))
    (let [effects (atom [])]
      (is (= l (lab/adopt! s left #(swap! effects conj %))))
      (is (= [10] @effects))
      (is (rejected? (fn [] (lab/adopt! s left #(swap! effects conj %)))))
      (is (rejected? (fn [] (lab/adopt! s right #(swap! effects conj %)))))
      (is (rejected? #(lab/fork! s right)))
      (is (= [10] @effects)))
    [original l r]))

(deftest actual-backends-agree-on-store-control-and-outbox
  ;; Whole snapshots, including RC, frames and stats, must agree, not just output.
  (is (apply = (mapv trial backends))))

(deftest fork-discard-and-stale-successor-cannot-recreate-authority
  (doseq [backend backends]
    (let [{:keys [world functions]} (lab/fixture)
          s (lab/session world {})
          [left right] (lab/fork! s (:initial s))
          [a b] (lab/fork! s left)
          run (lab/runner backend functions)
          done (lab/advance! s b run 30)
          output (atom [])]
      (lab/discard! s a)
      (lab/discard! s right)
      (is (rejected? #(lab/advance! s a run 0)))
      (is (rejected? #(lab/advance! s b run 0)))
      (lab/adopt! s done #(swap! output conj %))
      (is (= [30] @output)))))

(deftest incomplete-commit-never-replays-an-effect
  (doseq [backend backends]
    (let [{:keys [world functions]} (lab/fixture)
          ;; A second request lets us distinguish acknowledged and uncertain IO.
          functions (assoc-in functions [:entry :body 2 3 4 4]
                              [:host :lab/emit [[:imm 99]] 6 [:return [:var 3]]])
          ;; Re-enter so the modified function's continuation is actually active.
          world (m/run (m/start (assoc world :functions functions) :entry
                               [(get-in world [:locals 0]) (get-in world [:locals 1])]))
          s (lab/session world {})
          done (lab/advance! s (:initial s) (lab/runner backend functions) 10)
          attempts (atom [])
          emit! (fn [x] (swap! attempts conj x)
                  (when (= 99 x) (throw (ex-info "Effect outcome uncertain" {})))
                  :ack)]
      (is (= [10 99] (:outbox (lab/snapshot s done))))
      (is (rejected? #(lab/adopt! s done emit!)))
      (is (= :incomplete (:family @(:ledger s))))
      (is (= [{:intent 10 :receipt :ack}] (:completed @(:ledger s))))
      (is (rejected? #(lab/adopt! s done emit!)))
      (is (= [10 99] @attempts)))))

(deftest reentry-cannot-adopt-a-competing-branch
  (let [{:keys [world functions]} (lab/fixture)
        s (lab/session world {})
        [left right] (lab/fork! s (:initial s))
        run (lab/runner :mutable functions)
        left (lab/advance! s left run 10)
        right (lab/advance! s right run 20)]
    (lab/adopt! s left
                (fn [_]
                  (is (rejected? #(lab/adopt! s right identity)))
                  (is (rejected? #(lab/fork! s right)))
                  :ack))
    (is (= :adopted (:family @(:ledger s))))))

(deftest adoption-is-blocked-while-a-sibling-is-advancing
  (let [{:keys [world functions]} (lab/fixture)
        s (lab/session world {})
        [left right] (lab/fork! s (:initial s))
        run (lab/runner :persistent functions)
        left (lab/advance! s left run 10)
        entered (promise) release (promise)
        worker (future (lab/advance! s right
                                    (fn [w answer]
                                      (deliver entered true)
                                      (when (= ::timeout (deref release 5000 ::timeout))
                                        (throw (ex-info "Timed out" {})))
                                      (run w answer)) 20))]
    (try
      (is (= true (deref entered 5000 ::timeout)))
      (is (rejected? #(lab/adopt! s left identity)))
      (finally (deliver release true)))
    (let [right (deref worker 5000 ::timeout)]
      (is (not= ::timeout right))
      (is (= :open (:family @(:ledger s))))
      (lab/adopt! s right identity)
      (is (= :adopted (:family @(:ledger s)))))))

(deftest no-effectful-fallback-and-no-adoption-of-unfinished-guests
  (let [{:keys [world functions]} (lab/fixture)
        s (lab/session world {})]
    (is (rejected? #(lab/adopt! s (:initial s) identity)))
    (is (= :open (:family @(:ledger s))))
    (is (rejected? #(lab/advance! s (:initial s)
                                (fn [& _] (throw (ex-info "Runner failure" {}))) 0)))
    (is (= :incomplete (:family @(:ledger s))))
    (is (rejected? #(lab/advance! s (:initial s) (lab/runner :persistent functions) 0)))))

(deftest pending-host-requests-need-classification
  (let [{:keys [world functions]} (lab/fixture)
        run (lab/runner :persistent functions)
        pending (run world 10)]
    (is (= :host-call (:status pending)))
    (is (rejected? #(lab/session pending {})))
    (doseq [request [{:symbol :unknown :arguments [1]}
                     {:symbol :lab/emit :arguments [(m/->Ref 0)]}]]
      (let [s (lab/session world {})]
        (is (rejected? #(lab/advance! s (:initial s)
                                    (fn [& _] (assoc pending :host-request request)) 10)))
        (is (= :incomplete (:family @(:ledger s))))))
    (let [s (lab/session world {})]
      (is (rejected? #(lab/advance! s (:initial s) (fn [& _] pending) 10)))
      (is (= :incomplete (:family @(:ledger s)))))))

(deftest simultaneous-adoption-attempts-run-only-one-callback
  (let [{:keys [world functions]} (lab/fixture)
        s (lab/session world {})
        [left right] (lab/fork! s (:initial s))
        run (lab/runner :mutable functions)
        handles [(lab/advance! s left run 10) (lab/advance! s right run 20)]
        gate (promise) attempts (atom [])
        workers (mapv (fn [h]
                        (future
                          (when (= ::timeout (deref gate 5000 ::timeout))
                            (throw (ex-info "Timed out" {})))
                          (rejected? #(lab/adopt! s h (fn [x] (swap! attempts conj x))))))
                      handles)]
    (deliver gate true)
    (is (= [false true] (sort (mapv #(deref % 5000 ::timeout) workers))))
    (is (= 1 (count @attempts)))
    (is (#{[10] [20]} @attempts))
    (is (= :adopted (:family @(:ledger s))))))

(deftest two-advances-cannot-consume-the-same-handle
  (let [{:keys [world functions]} (lab/fixture)
        s (lab/session world {})
        run (lab/runner :mutable functions)
        entered (promise) release (promise)
        worker (future (lab/advance! s (:initial s)
                                    (fn [w x]
                                      (deliver entered true)
                                      (when (= ::timeout (deref release 5000 ::timeout))
                                        (throw (ex-info "Timed out" {})))
                                      (run w x)) 10))]
    (try
      (is (= true (deref entered 5000 ::timeout)))
      (is (rejected? #(lab/advance! s (:initial s) run 20)))
      (is (rejected? #(lab/fork! s (:initial s))))
      (finally (deliver release true)))
    (let [successor (deref worker 5000 ::timeout)]
      (is (not= ::timeout successor))
      (is (= 10 (get-in (lab/snapshot s successor) [:world :result]))))))

(deftest a-failed-sibling-prevents-publication-of-an-in-flight-result
  (let [{:keys [world functions]} (lab/fixture)
        s (lab/session world {})
        [left right] (lab/fork! s (:initial s))
        run (lab/runner :mutable functions)
        entered (promise) release (promise)
        worker (future
                 (rejected?
                  #(lab/advance! s left
                                 (fn [w x]
                                   (deliver entered true)
                                   (when (= ::timeout (deref release 5000 ::timeout))
                                     (throw (ex-info "Timed out" {})))
                                   (run w x)) 10)))]
    (try
      (is (= true (deref entered 5000 ::timeout)))
      (is (rejected? #(lab/advance! s right (fn [& _] (throw (ex-info "Fail" {}))) 20)))
      (finally (deliver release true)))
    (is (= true (deref worker 5000 ::timeout)))
    (is (= :incomplete (:family @(:ledger s))))
    (is (rejected? #(lab/adopt! s left identity)))
    (is (rejected? #(lab/adopt! s right identity)))))
