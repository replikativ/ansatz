;; Small HOST CONTROL MODELS ONLY: no actual Lean/guest/native execution.
;; cwd experiments/lean-ir; load typed-witness-next.clj first, then this file.
(require '[clojure.test :refer [deftest is testing]])

(defn tw-control-model []
  (let [target ["str" ["str" ["anonymous"] "ModuleDataTransport"] "finalizeTransport"]
        functions {target {:params [0 1 2] :body [:return [:imm 0]]}}
        source {:closed (atom false)}
        bindings {"model" {:handler identity}}
        world (assoc (tw-m/world functions) :status :done :native-imports [source])]
    {:status :typed-witness-prepared :world world :source source
     :session {:functions functions :bindings bindings}
     :state (tw-m/->Ref 0) :imports (tw-m/->Ref 1)
     :profile (atom {}) :start-claimed? (atom false)}))

(defn tw-control-open [cache]
  (fn [functions bindings options]
    (merge options {:functions functions :bindings bindings :cache cache})))

(deftest tw-start-and-outer-continuation-never-replay-test
  (let [prepared (tw-control-model) cache (atom {}) invocations (atom 0)
        calls (atom [])]
    (with-redefs [tw-raw/open-functions (tw-control-open cache)
                  tw-raw/continue
                  (fn [session world]
                    (swap! calls conj [session world])
                    (if (= 1 (swap! invocations inc))
                      (throw (ex-info "Raw runtime instruction budget exhausted"
                               {:checkpoint (assoc world :status :paused)
                                :checkpoint-session session}))
                      {:state (assoc world :status :done :result 0) :session session :value 0}))]
      (let [paused (start-full-init-finalizer-slice prepared {:fuel 7 :backend :mutable})]
        (is (= :paused-outer (:outcome paused)))
        (is (= 1 @invocations))
        (is (thrown-with-msg? clojure.lang.ExceptionInfo #"start already claimed"
                             (start-full-init-finalizer-slice prepared {:fuel 7})))
        (is (= 1 @invocations) "Duplicate start must not call the driver")
        (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Slice fuel"
                             (continue-full-init-finalizer-slice paused 0)))
        (is (false? @(:continue-claimed? paused)) "Failed preflight must not claim continuation")
        (let [returned (continue-full-init-finalizer-slice paused 11)
              [first-session first-world] (first @calls)
              [next-session next-world] (second @calls)]
          (is (= :guest-io-returned (:outcome returned)))
          (is (= 2 @invocations))
          (is (identical? cache (:cache first-session)))
          (is (identical? cache (:cache next-session)))
          (is (identical? (:bindings first-session) (:bindings next-session)))
          (is (identical? (:functions first-session) (:functions next-session)))
          (is (= 11 (:fuel next-session)))
          (is (identical? (:world paused) next-world) "Resume the exact paused snapshot, not m/start")
          (is (identical? (:source prepared) (:source returned)))
          (is (identical? (:source prepared) (first (:native-imports first-world))))
          (is (identical? (:source prepared) (first (:native-imports next-world))))
          (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Continuation already claimed"
                               (continue-full-init-finalizer-slice paused 11)))
          (is (= 2 @invocations)))))))

(deftest tw-nested-checkpoint-is-not-an-outer-continuation-test
  (doseq [message ["Raw runtime instruction budget exhausted" "handler already effected IO"]]
    (let [prepared (tw-control-model) invocations (atom 0) cache (atom {})]
      (with-redefs [tw-raw/open-functions (tw-control-open cache)
                    tw-raw/continue
                    (fn [session world]
                      (swap! invocations inc)
                      (throw (ex-info message
                               {:checkpoint (assoc world :status :paused)
                                :checkpoint-session session
                                :host-boundaries [{:checkpoint (assoc world :status :host-call)
                                                   :session session :helper {:target :model-nested}}]})))]
        (let [result (start-full-init-finalizer-slice prepared {:fuel 7})]
          (is (= :blocked-nested (:outcome result)))
          (is (= 1 (get-in result [:summary :host-boundary-depth])))
          (is (nil? (:continue-claimed? result)))
          (is (= message (.getMessage ^Throwable (:failure result))))
          (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Only a top-level"
                               (continue-full-init-finalizer-slice result 11)))
          (is (= 1 @invocations) "A nested checkpoint must never replay its effected host handler"))))))

(deftest tw-unrelated-failure-is-not-resumable-test
  (let [prepared (tw-control-model)]
    (with-redefs [tw-raw/open-functions (tw-control-open (atom {}))
                  tw-raw/continue (fn [session world]
                                    (throw (ex-info "model validation failure"
                                             {:checkpoint (assoc world :status :paused)
                                              :checkpoint-session session})))]
      (let [result (start-full-init-finalizer-slice prepared {:fuel 7})]
        (is (= :failed (:outcome result)))
        (is (nil? (:continue-claimed? result)))
        (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Only a top-level"
                             (continue-full-init-finalizer-slice result 11)))))))

(deftest tw-closed-source-and-mismatched-session-do-not-claim-test
  (let [prepared (tw-control-model) cache (atom {}) invocations (atom 0)]
    (with-redefs [tw-raw/open-functions (tw-control-open cache)
                  tw-raw/continue
                  (fn [session world]
                    (swap! invocations inc)
                    (throw (ex-info "Raw runtime instruction budget exhausted"
                             {:checkpoint (assoc world :status :paused) :checkpoint-session session})))]
      (let [paused (start-full-init-finalizer-slice prepared {:fuel 7})
            mismatch (assoc-in paused [:session :functions] {})]
        (is (thrown-with-msg? clojure.lang.ExceptionInfo #"executable mismatch"
                             (continue-full-init-finalizer-slice mismatch 7)))
        (is (false? @(:continue-claimed? paused)))
        (reset! (:closed (:source prepared)) true)
        (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Source already closed"
                             (continue-full-init-finalizer-slice paused 7)))
        (is (false? @(:continue-claimed? paused)))
        (is (= 1 @invocations))))))

(deftest tw-profile-storage-is-bounded-test
  (let [profile (atom {})]
    (doseq [i (range 100)] (tw-profile! profile [:model i] 1.0 3 false))
    (is (= 64 (count @profile)))
    (is (= 100 (reduce + (map :calls (vals @profile)))))
    (is (= 300 (reduce + (map :completed-guest-steps (vals @profile)))))
    (is (= 37 (get-in @profile [:other :calls])))))
