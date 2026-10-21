(ns prototype.restored-import-check-test
  "Actual interpreter/helper and strict Java checks over native CI fixture data.
   Helper bodies/Environment layout are tiny ownership models, not Lean's frontend
   or a genuine checkpoint restore/finalizer run. No archive or native compiler."
  (:require [clojure.test :refer [deftest is]]
            [prototype.machine :as m]
            [prototype.raw-interop :as raw]
            [prototype.module-data :as data]
            [prototype.module-import :as imports]
            [prototype.imported-kernel :as imported])
  (:import [ansatz.kernel Env ConstantInfo]
           [java.util.concurrent CountDownLatch TimeUnit]))

(binding [*ns* *ns*] (load-file "scripts/check-restored-import.clj"))
(alias 'check 'prototype.restored-import-check)

(defn failure [f] (try (f) nil (catch clojure.lang.ExceptionInfo e e)))
(defn fixture
  ([] (fixture :reference))
  ([backend]
   (let [root {:params [1] :body [:let 2 [:project [:var 1] 0]
                                  [:inc [:var 2] 1 [:return [:var 2]]]]}
         constants {:params [1] :body [:let 2 [:project [:var 1] 0]
                                       [:let 3 [:project [:var 2] 0]
                                        [:inc [:var 3] 1 [:return [:var 3]]]]]}
         functions {(:root imports/helpers) root
                    (:constants imports/helpers) constants
                    (:constant-map imports/helpers) constants
                    (:quot-init? imports/helpers) {:params [1] :body [:return [:imm 1]]}}
         loaded (data/load-file (m/world functions) "fixtures/imported-kernel-native.jsonl")
         values (mapv :guest (imported/module-constants (:world loaded) (first (:roots loaded))))
         [world array] (m/allocate (:world loaded) :array 246 values)
         [world root] (m/allocate world :ctor 0 [array])
         [world environment] (m/allocate world :ctor 0 [root])
         [world io] (m/allocate world :ctor 0 [environment])
         world (assoc world :status :done :result io :frames [])
         session (raw/open-functions functions {} {:backend backend :fuel 10000})]
     {:entry {:world world :session session :io-result io}
      :environment environment :root root :values values
      :configuration {:trusted-functions functions :trusted-bindings {}
                      :kernel-helpers {} :kernel-policy {:allow-axioms? true :allow-unsafe? true}
                      :fuel 10000}})))

(deftest strict-whole-map-check-runs-real-helper-ir-without-finalizer-replay
  (doseq [backend [:reference :mutable :jvm]]
    (let [{:keys [entry configuration environment root]} (fixture backend)
          before (:world entry) control (check/prepare entry configuration)
          checked (check/check! control) world (:world checked) certificate (:certificate checked)]
      (is (= :ok (:status checked)))
      (is (= :checked (:phase (check/summary control))))
      (is (= 17 (count (:constants certificate))))
      (is (= #{"A"} (set (map str (:axioms certificate)))))
      (is (= (set (range 8)) (set (map #(.tag ^ConstantInfo %) (vals (:projected certificate))))))
      (is (.isQuotEnabled ^Env (:env certificate)))
      (is (identical? (:env certificate) (get-in world [:kernel-environments (:id root) :env])))
      (is (= environment (:environment checked)))
      (is (= 1 (:rc (m/node world environment))))
      (is (not (contains? (:heap world) (:id (:io-result entry)))))
      (is (= 1 (:rc (m/node before (:io-result entry)))))
      (is (nil? (:kernel-environments before)))
      (is (identical? (:functions world) (get-in checked [:session :functions])))
      (is (identical? (get-in entry [:session :cache]) (get-in checked [:session :cache])))
      (is (failure #(check/check! control))))))

(deftest effective-default-helpers-and-transitive-dependencies-are-protected
  (let [{:keys [entry configuration]} (fixture)
        functions (get-in entry [:world :functions]) target (:root imports/helpers)
        dependency ["str" ["anonymous"] "strict-dependency"]
        helper {:params [1] :body [:call 2 [:direct dependency] [[:var 1]] [:return [:var 2]]]}
        functions (assoc functions target helper dependency (get functions target))
        trusted (assoc configuration :trusted-functions functions)
        candidate (-> entry (assoc-in [:world :functions] functions)
                      (assoc :session (raw/open-functions functions {} {:backend :reference})))
        _ (is (some? (check/prepare candidate trusted)))
        changed (assoc-in functions [dependency :body] [:return [:imm 0]])
        changed-entry (-> candidate (assoc-in [:world :functions] changed)
                          (assoc :session (raw/open-functions changed {} {:backend :reference})))]
    ;; Override map is empty: inherited default helper roots still require exact identity.
    (is (failure #(check/prepare entry (update configuration :trusted-functions dissoc target))))
    (is (failure #(check/prepare changed-entry trusted)))
    (is (zero? (get-in changed-entry [:world :stats :steps])))))

(deftest unexpected-or-replaced-host-bindings-fail-before-execution
  (let [{:keys [entry configuration]} (fixture)
        capability {:signature {:params [] :return-type "object"} :handler (fn [& _] nil)}]
    (doseq [[bindings trusted] [[{"rogue" capability} {}]
                                [{"owned" capability} {"owned" (assoc capability :different true)}]]]
      (let [entry (assoc-in entry [:session :bindings] bindings)
            config (assoc configuration :trusted-bindings trusted)]
        (is (failure #(check/prepare entry config)))
        (is (zero? (get-in entry [:world :stats :steps])))))))

(deftest idle-and-owned-entry-contracts-fail-without-certificate-shortcuts
  (let [{:keys [entry configuration]} (fixture)]
    (doseq [candidate [(assoc-in entry [:world :status] :paused)
                       (assoc-in entry [:world :frames] [{}])
                       (assoc-in entry [:world :result] 0)
                       (update-in entry [:session :functions] with-meta {:changed true})
                       (assoc-in entry [:world :kernel-environments] {0 {:env (Env.)}})
                       (assoc entry :io-result (m/->Ref 99999999))]]
      (is (failure #(check/prepare (assoc candidate :certificate {:checked true} :phase :checked)
                                   configuration))))
    (doseq [configuration [(dissoc configuration :fuel)
                           (assoc configuration :fuel 0)
                           (assoc configuration :finalizer-attestation {})]]
      (is (failure #(check/prepare entry configuration))))))

(deftest io-error-retains-its-owner-and-does-not-run-helpers
  (let [{:keys [entry configuration]} (fixture)
        world (:world entry)
        [world error] (m/resource world "actual error model")
        [world io] (m/allocate world :ctor 1 [error])
        entry (assoc entry :world (assoc world :result io) :io-result io)
        control (check/prepare entry configuration)
        result (with-redefs [raw/call (fn [& _] (throw (AssertionError. "Unexpected guest call")))]
                 (check/check! control))]
    (is (= :io-error (:status result)))
    (is (identical? (:world entry) (:world result)))
    (is (= io (:io-result result)))
    (is (= 1 (:rc (m/node (:world result) io))))
    (is (= :guest-io-error (:phase (check/summary control))))
    (is (failure #(check/check! control)))))

(deftest a-child-failure-keeps-the-newer-session-and-paired-checkpoint
  (let [{:keys [entry configuration]} (fixture)
        target (:constants imports/helpers)
        child (atom nil) calls (atom 0)
        binding {:signature {:params [{:ty "object" :borrow true}] :return-type "object"}
                 :handler (fn [{:keys [switch-backend! checkpoint!]} world args]
                            (swap! calls inc)
                            (let [world (checkpoint! (assoc (switch-backend! world :jvm) :newer-helper true))]
                              (reset! child {:world world :arguments args})
                              (throw (ex-info "Child failed after actual backend upgrade" {}))))}
        bindings {"restored_check_failure" binding}
        row {:kind "decl" :name target
             :ir {:extern {:f target :xs [{:x {:idx 1} :ty "object" :borrow true}]
                           :type "object"
                           :ext {:entries [{:standard {:backend ["str" ["anonymous"] "all"]
                                                       :fn "restored_check_failure"}}]}}}}
        functions (assoc (get-in entry [:world :functions]) target (second (raw/lower bindings row)))
        entry (-> entry (assoc-in [:world :functions] functions)
                  (assoc :session (raw/open-functions functions bindings {:backend :reference})))
        configuration (assoc configuration :trusted-functions functions :trusted-bindings bindings)
        control (check/prepare entry configuration)
        error (failure #(check/check! control)) evidence (ex-data error)]
    (is (= 1 @calls))
    (is (identical? (:world @child) (:checkpoint evidence)))
    (is (= :jvm (get-in evidence [:checkpoint-session :backend])))
    (is (some? (get-in evidence [:checkpoint-session :program])))
    (is (identical? functions (get-in evidence [:checkpoint-session :functions])))
    (is (= entry (:restored-check-entry evidence)))
    (is (= :entry (get-in evidence [:restored-check-progress :phase])))
    (is (= :reference (get-in evidence [:restored-check-progress :session :backend])))
    (is (nil? (:restored-check-result evidence)))
    (is (nil? (:environment evidence)))
    (is (some? (:finalization-entry evidence)))
    (is (= :failed (:phase (check/summary control))))
    (is (failure #(check/check! control)))))

(deftest observer-failure-keeps-the-completed-checked-owner
  (let [{:keys [entry configuration environment]} (fixture)
        observations (atom [])
        control (check/prepare entry (assoc configuration :observe!
                                            (fn [summary]
                                              (swap! observations conj summary)
                                              (throw (ex-info "Observer failure"
                                                              {:restored-check-entry :forged-entry
                                                               :restored-check-progress :forged-progress
                                                               :restored-check-result :forged-result})))))
        error (failure #(check/check! control)) result (:result (check/checkpoint control))]
    (is (= 1 (count @observations)))
    (is (= :checking (:phase (first @observations))))
    (is (= true (:checking-completed (first @observations))))
    (is (= :ok (:status result)))
    (is (= environment (:environment result)))
    (is (= 1 (:rc (m/node (:world result) environment))))
    (is (identical? result (:restored-check-result (ex-data error))))
    (is (= entry (:restored-check-entry (ex-data error))))
    (is (= :return (get-in (ex-data error) [:restored-check-progress :phase])))
    (is (identical? (:raw-progress (check/checkpoint control))
                    (:restored-check-progress (ex-data error))))
    (is (= :failed (:phase (check/summary control))))
    (is (failure #(check/check! control)))))

(deftest racing-and-reentrant-callers-cannot-consume-the-io-again
  (let [{:keys [entry configuration]} (fixture)
        entered (CountDownLatch. 1) release (CountDownLatch. 1) callbacks (atom 0)
        control (check/prepare entry (assoc configuration :observe!
                                            (fn [_]
                                              (swap! callbacks inc)
                                              (.countDown entered)
                                              (when-not (.await release 5 TimeUnit/SECONDS)
                                                (throw (ex-info "Test release timed out" {}))))))
        worker (future (check/check! control))]
    (try
      (is (.await entered 5 TimeUnit/SECONDS))
      (is (failure #(check/check! control)))
      (.countDown release)
      (is (= :ok (:status (deref worker 5000 ::timeout))))
      (is (= 1 @callbacks))
      (is (failure #(check/check! control)))
      (finally (.countDown release) @worker)))
  (let [{:keys [entry configuration]} (fixture)
        control (atom nil) refused (atom false)
        observer (fn [_] (reset! refused (boolean (failure #(check/check! @control)))))]
    (reset! control (check/prepare entry (assoc configuration :observe! observer)))
    (is (= :ok (:status (check/check! @control))))
    (is @refused)))

(deftest actual-kernel-policy-rejection-is-terminal-and-preserves-owned-alternatives
  (let [{:keys [entry configuration]} (fixture)
        control (check/prepare entry (assoc configuration :kernel-policy {}))
        error (failure #(check/check! control)) evidence (ex-data error)]
    (is (some? error))
    (is (= :failed (:phase (check/summary control))))
    (is (empty? (:kernel-environments (:checkpoint evidence))))
    (is (some? (:finalization-entry evidence)))
    (is (= :return (get-in evidence [:restored-check-progress :phase])))
    (is (nil? (:restored-check-result evidence)))
    (is (failure #(check/check! control)))))
