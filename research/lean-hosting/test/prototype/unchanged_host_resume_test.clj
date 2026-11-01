(ns prototype.unchanged-host-resume-test
  "Explicit small raw programs; no Init, Source or frontend loading."
  (:require [clojure.test :refer [deftest is]]
            [prototype.raw-interop :as raw] [prototype.mutable :as u]
            [prototype.machine :as m] [prototype.slot-count :as slots]
            [prototype.continuation-layout :as layout]
            [prototype.block-compile :as blocks]))

(def signature {:params [{:ty "uint64" :borrow false}] :return-type "uint64"})
(defn chain [n parameter destination tail]
  (reduce (fn [body _] [:host "ping" [[:var parameter]] destination body]) tail (range n)))
(defn functions [n]
  {"entry" {:params [1] :body (chain n 1 2 [:return [:var 2]])}})
(defn binding-for [handler] {"ping" {:signature signature :handler handler}})
(defn call [backend mode functions bindings & [options world]]
  (let [session (raw/open-functions functions bindings (merge {:backend backend :compile-threshold 1} options))
        world (or world (m/world functions)) counts (long-array 4) runner @#'raw/run-boundary
        invoke #(raw/call session world "entry" [42])
        result (with-bindings {#'raw/*boundary-counts* counts}
                 (if (= mode :baseline)
                   (with-redefs-fn {#'raw/run-boundary (fn [s w fuel] (runner s w fuel))} invoke)
                   (invoke)))]
    (assoc result :counts (vec counts))))

(deftest identity-callbacks-reuse-only-private-storage-and-preserve-frozen-worlds
  (doseq [backend [:mutable :jvm]]
    (let [functions (functions 10) retained (atom [])
          bindings (binding-for (fn [_ world [x]] (swap! retained conj world) [world x]))
          baseline (call backend :baseline functions bindings)
          before @retained _ (reset! retained [])
          fast (call backend :fast functions bindings)]
      (is (= (:state baseline) (:state fast)))
      (is (= 42 (:value fast)))
      (is (= [11 0 11 0] (:counts baseline)))
      (is (= [1 10 11 0] (:counts fast)))
      (is (= before @retained))
      ;; All earlier snapshots still have exactly their original control/owners.
      (is (= (vec (range 1 11)) (mapv #(get-in % [:stats :steps]) @retained)))
      (is (every? #(= :host-call (:status %)) @retained)))))

(deftest saved-frames-and-captured-joins-keep-their-independent-registers
  (doseq [backend [:mutable :jvm]]
    (let [functions {"entry" {:params [1] :body [:join 0 [700] [:return [:var 700]]
                                                [:call 500 [:direct "worker"] [[:var 1]]
                                                 [:jump 0 [[:var 500]]]]]}
                     "worker" {:params [3] :body (chain 10 3 900 [:return [:var 900]])}}
          bindings (binding-for (fn [_ world [x]] [world x]))
          ;; A cold callee continuation may require one ordinary restore first.
          _ (call backend :fast functions bindings)
          baseline (call backend :baseline functions bindings)
          fast (call backend :fast functions bindings)]
      (is (= 42 (:value fast)))
      (is (= (:state baseline) (:state fast)))
      (is (= [1 10 11 0] (:counts fast)))
      (is (= 1 (get-in fast [:state :stats :max-frames]))))))

(deftest nonidentical-world-and-session-changes-always-fall-back
  (doseq [backend [:mutable :jvm]
          change [(fn [_ world] (with-meta world {:new-wrapper (Object.)}))
                  (fn [_ world] (update world :entropy (fnil inc 0)))
                  (fn [_ world] (update-in world [:task-runtime :counter] (fnil inc 0)))
                  (fn [_ world] (update-in world [:stdio-runtime :counter] (fnil inc 0)))
                  (fn [_ world] (update-in world [:kernel-environments :counter] (fnil inc 0)))
                  (fn [_ world] (assoc-in world [:globals :new] {:status :ready :value (inc (get-in world [:globals :new :value] 0))}))
                  (fn [{:keys [switch-backend!]} world] (switch-backend! world backend))]]
    (let [functions (functions 2)
          bindings (binding-for (fn [context world [x]] [(change context world) x]))
          baseline (call backend :baseline functions bindings)
          fast (call backend :fast functions bindings)]
      (is (= (:state baseline) (:state fast)))
      (is (= [3 0 3 0] (:counts fast))))))

(deftest dirty-heap-and-forks-returned-from-helpers-are-not-reused
  (doseq [backend [:mutable :jvm]]
    (let [dirty {"entry" {:params [1] :body [:let 3 [:ctor 1 [[:var 1]]]
                                                   (chain 2 1 2 [:return [:var 2]])]}}
          identity (binding-for (fn [_ world [x]] [world x]))
          baseline (call backend :baseline dirty identity)
          fast (call backend :fast dirty identity)]
      (is (= (:state baseline) (:state fast)))
      ;; First dirty interval restores; the following clean interval can reuse.
      (is (= [2 1 3 0] (:counts fast)))))
  (doseq [backend [:mutable :jvm] discard? [false true]]
    (let [functions (assoc (functions 2) "helper" {:params [1] :body [:return [:var 1]]})
          effects (atom [])
          bindings (binding-for (fn [{:keys [invoke]} world [x]]
                                  (swap! effects conj :once)
                                  (let [[next result] (invoke world "helper" [x])]
                                    [(if discard? world next) result])))
          baseline (call backend :baseline functions bindings)
          _ (reset! effects []) fast (call backend :fast functions bindings)]
      (is (= (:state baseline) (:state fast)))
      (is (= [:once :once] @effects))
      (is (= (if discard? 2 0) (nth (:counts fast) 1))))))

(defn error-of [f] (try (f) nil (catch Throwable error error)))
(deftest failures-preserve-the-same-immutable-checkpoints-and-once-effects
  (doseq [backend [:mutable :jvm]
          kind [:handler :malformed :invalid-result :backend]]
    (let [functions (if (= kind :backend)
                      {"entry" {:params [1] :body [:host "ping" [[:var 1]] 2 [:unreachable]]}}
                      (functions 1))
          effects (atom 0)
          bindings (binding-for (fn [_ world [x]]
                                  (swap! effects inc)
                                  (case kind
                                    :handler (throw (ex-info "intentional" {}))
                                    :malformed nil :invalid-result [world :bad-scalar]
                                    :backend [world x])))
          baseline (error-of #(call backend :baseline functions bindings))
          _ (reset! effects 0) fast (error-of #(call backend :fast functions bindings))]
      (is baseline)
      (is fast)
      (is (= 1 @effects))
      (is (= (:checkpoint (ex-data baseline)) (:checkpoint (ex-data fast)))))))

(deftest exact-fuel-and-cooperative-boundaries-retain-their-original-contract
  (doseq [backend [:mutable :jvm] fuel [0 1 2 3 4]]
    (let [functions (functions 2) bindings (binding-for (fn [_ w [x]] [w x]))
          run #(call backend % functions bindings {:fuel fuel})
          before (try {:state (:state (run :baseline))} (catch Throwable e {:error (:checkpoint (ex-data e))}))
          after (try {:state (:state (run :fast))} (catch Throwable e {:error (:checkpoint (ex-data e))}))]
      (is (= before after))))
  (doseq [backend [:mutable :jvm]]
    (let [functions (functions 1) bindings (binding-for (fn [_ w [x]] [w x]))
          session (raw/open-functions functions bindings {:backend backend :compile-threshold 1})
          started (m/start (m/world functions) "entry" [42])
          counts (long-array 4)
          boundary (with-bindings {#'raw/*boundary-counts* counts} (raw/advance-to-boundary session started))
          completed (raw/complete-host-boundary (:token boundary) {:helper-fuel 100})]
      (is (= [1 0 1 0] (vec counts)))
      (is (= :handler-completed (:status completed)))
      (is (= 42 (:value (raw/continue (:session completed) (:state completed))))))))

(deftest capacity-and-alias-checks-decline-without-changing-private-control
  (let [snapshot (assoc (m/world {}) :status :host-call :body [:return [:imm 42]]
                        :locals {} :frames [] :joins {} :host-request {:symbol "ping" :arguments [] :dest 100})
        machine (u/thaw snapshot) frozen (u/freeze machine) token (u/boundary-storage-token)]
    (is token)
    (aset ^objects (:control machine) 1 (object-array 1))
    (is (nil? (u/resume-unchanged-host! machine frozen 42 token)))
    (is (= :host-call (u/status machine))))
  (let [snapshot (assoc (m/world {}) :status :host-call :body [:return [:imm 42]]
                        :locals {} :frames [] :joins {} :host-request {:symbol "ping" :arguments [] :dest 0})
        machine (u/thaw snapshot) token (u/boundary-storage-token)]
    (u/capture-join! machine 0 [] (:body snapshot) (u/locals-array machine))
    (is (nil? (u/resume-unchanged-host! machine (u/freeze machine) 42 token)))
    (is (= :host-call (u/status machine)))))

(deftest query-misses-and-runtime-redefinitions-use-normal-restoration
  (let [functions (functions 2) bindings (binding-for (fn [_ w [x]] [w x]))
        baseline (call :jvm :baseline functions bindings)]
    (with-redefs [u/thaw (let [original u/thaw] (fn [world] (original world)))]
      (let [result (call :jvm :fast functions bindings)]
        (is (= (:state baseline) (:state result)))
        (is (= [3 0 3 0] (:counts result)))))
    (with-redefs [slots/cached-program-slots (constantly nil)]
      (let [result (call :jvm :fast functions bindings)]
        (is (= (:state baseline) (:state result)))
        (is (= [3 0 3 0] (:counts result)))))
    (with-redefs [layout/proven-width (constantly nil)]
      (let [result (call :jvm :fast functions bindings)]
        (is (= (:state baseline) (:state result)))
        (is (= [3 0 3 0] (:counts result)))))))

(deftest actual-nested-host-callbacks-keep-candidates-in-their-own-invocations
  (doseq [backend [:mutable :jvm] discard? [false true]]
    (let [functions (assoc (functions 2) "helper"
                          {:params [1] :body (reduce (fn [body _] [:host "inner" [[:var 1]] 2 body])
                                                   [:return [:var 2]] (range 3))})
          effects (atom [])
          bindings {"ping" {:signature signature
                             :handler (fn [{:keys [invoke]} world [x]]
                                        (swap! effects conj :outer)
                                        (let [[next result] (invoke world "helper" [x])]
                                          [(if discard? world next) result]))}
                    "inner" {:signature signature
                              :handler (fn [_ world [x]] (swap! effects conj :inner) [world x])}}
          baseline (call backend :baseline functions bindings)
          before @effects _ (reset! effects []) fast (call backend :fast functions bindings)]
      (is (= (:state baseline) (:state fast)))
      (is (= before @effects))
      (is (= [:outer :inner :inner :inner :outer :inner :inner :inner] @effects))
      (is (= (if discard? [3 8 11 0] [5 6 11 0]) (:counts fast))))))

(deftest runtime-rules-changed-inside-a-handler-decline-existing-candidates
  (doseq [backend [:mutable :jvm]
          rule [#'m/resume #'u/thaw #'u/freeze #'u/frame-out #'layout/width #'layout/proven-width
                #'slots/cached-program-slots]]
    (let [functions (functions 2) original @rule changed (atom false)
          replacement (fn [& args] (apply original args))
          bindings (binding-for (fn [_ world [x]]
                                  (when (compare-and-set! changed false true)
                                    (alter-var-root rule (constantly replacement)))
                                  [world x]))]
      (try
        (let [result (call backend :fast functions bindings)]
          (is (= 42 (:value result)))
          (is (= [3 0 3 0] (:counts result))))
        (finally (alter-var-root rule (constantly original))))))
  ;; The ordinary mutable backend does not read this public inspection accessor.
  ;; The optimization must not introduce a new observable read either.
  (with-redefs [u/status (fn [& _] (throw (AssertionError. "unexpected inspection accessor")))]
    (let [functions (functions 2) bindings (binding-for (fn [_ w [x]] [w x]))
          baseline (call :mutable :baseline functions bindings) fast (call :mutable :fast functions bindings)]
      (is (= (:state baseline) (:state fast)))
      (is (= [1 2 3 0] (:counts fast))))))

(deftest backend-failure-after-confirmed-private-reuse-keeps-the-resumed-checkpoint
  (doseq [backend [:mutable :jvm]]
    (let [functions {"entry" {:params [1] :body [:host "ping" [[:var 1]] 2 [:unreachable]]}}
          bindings (binding-for (fn [_ w [x]] [w x]))
          session (raw/open-functions functions bindings {:backend backend :compile-threshold 1})
          world (m/world functions) counts (long-array 4) runner @#'raw/run-boundary
          baseline (with-redefs-fn {#'raw/run-boundary (fn [s w f] (runner s w f))}
                     #(error-of (fn [] (raw/call session world "entry" [42]))))
          fast (with-bindings {#'raw/*boundary-counts* counts}
                 (error-of #(raw/call session world "entry" [42])))]
      (is (= [1 1 1 0] (vec counts)))
      (is (= (:checkpoint (ex-data baseline)) (:checkpoint (ex-data fast))))
      (is (identical? session (:checkpoint-session (ex-data fast))))
      (is (= :running (:status (:checkpoint (ex-data fast))))))))

(deftest missing-real-layout-evidence-does-not-run-speculative-readers
  (let [snapshot (assoc (m/world {}) :status :host-call :body [:return [:imm 42]]
                        :locals {} :frames [] :joins {} :host-request {:symbol "ping" :arguments [] :dest 0})
        machine (u/thaw snapshot) frozen (u/freeze machine) token (u/boundary-storage-token)]
    (with-redefs-fn {#'slots/program-cache (atom [])}
      #(do
         (is (nil? (u/resume-unchanged-host! machine frozen 42 token)))
         (is (empty? @@#'slots/program-cache))))
    (with-redefs-fn {#'layout/cache {:buckets (java.util.HashMap.) :queue (java.lang.ref.ReferenceQueue.) :owner (volatile! nil)}}
      #(do
         (is (nil? (u/resume-unchanged-host! machine frozen 42 token)))
         (is (.isEmpty ^java.util.HashMap (:buckets @#'layout/cache)))))
    (is (= :host-call (u/status machine)))))

(deftest custom-compact-register-adapter-keeps-the-ordinary-boundary-path
  (let [functions {"entry" {:params [1] :body [:join 0 [700] [:return [:var 700]]
                                              [:call 500 [:direct "worker"] [[:var 1]]
                                               [:jump 0 [[:var 500]]]]]}
                   "worker" {:params [3] :body (chain 4 3 900 [:return [:var 900]])}}
        bindings (binding-for (fn [_ world [x]] [world x]))
        session (raw/open-functions functions bindings {:backend :jvm})
        program (blocks/compile-program functions nil {:compact-registers true :lexical-joins true})
        reference (raw/open-functions functions bindings {:backend :reference})
        world (m/world functions) expected (raw/call reference world "entry" [42])
        counts (long-array 4)
        actual (with-bindings {#'raw/*boundary-counts* counts}
                 (with-redefs-fn {#'raw/run-boundary
                                 (fn [_ w fuel] (u/freeze (blocks/run! program (u/thaw w) fuel)))}
                   #(raw/call session world "entry" [42])))]
    (is (= (:state expected) (:state actual)))
    (is (= 42 (:value actual)))
    (is (zero? (aget counts 1)))))

(deftest caught-helper-failure-preserves-explicit-checkpoints-session-and-effects
  (doseq [backend [:mutable :jvm] switch? [false true]]
    (let [functions (assoc (functions 1) "helper"
                          {:params [1] :body [:host "inner" [[:var 1]] 2 [:unreachable]]})
          effects (atom []) observed (atom nil)
          bindings {"ping" {:signature signature
                             :handler (fn [{:keys [invoke checkpoint!]} world args]
                                        (swap! effects conj :outer)
                                        (try (invoke world "helper" args)
                                             (catch Throwable error (reset! observed (ex-data error))))
                                        (checkpoint! world)
                                        (throw (ex-info "outer after caught helper" {})))}
                    "inner" {:signature signature
                              :handler (fn [{:keys [switch-backend!]} world [x]]
                                         (swap! effects conj :inner)
                                         [(if switch? (switch-backend! world backend) world) x])}}
          baseline (error-of #(call backend :baseline functions bindings))
          child-before @observed _ (reset! effects []) _ (reset! observed nil)
          fast (error-of #(call backend :fast functions bindings))
          child-after @observed]
      (is (= [:outer :inner] @effects))
      (is (= (:checkpoint (ex-data baseline)) (:checkpoint (ex-data fast))))
      (is (= (select-keys child-before [:checkpoint :host-boundary-checkpoint :helper-entry-checkpoint :failed-helper])
             (select-keys child-after [:checkpoint :host-boundary-checkpoint :helper-entry-checkpoint :failed-helper])))
      (is (= backend (get-in (ex-data fast) [:checkpoint-session :backend])))
      (is (= backend (get-in child-after [:checkpoint-session :backend])))
      (is (= 1 (count (:host-boundaries child-after)))))))
