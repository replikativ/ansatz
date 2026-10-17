(ns prototype.module-import-resume-test
  "Direct recovery/ownership protocol tests. The finalizer is handwritten guest
   IR and the Environment accessors are a helper-boundary model. This is NOT
   native Lean finalizeImport or frontend compatibility coverage. ConstantInfo
   checking uses the authentic small native fixture and the actual Java checker."
  (:require [clojure.test :refer [deftest is]]
            [prototype.module-import :as import] [prototype.module-import-test :as fixture]
            [prototype.machine :as m] [prototype.mutable :as u] [prototype.lazy-runtime :as lazy]
            [prototype.raw-interop :as raw] [prototype.kernel-bridge-test :as guest]))
(def finalizer ["recovery-test-finalizer"])
(defn functions [error?]
  {finalizer {:params [0]
              :body [:suspend 1
                     (if error?
                       [:let 2 [:ctor 1 [[:var 0]]] [:return [:var 2]]]
                       [:let 2 [:ctor 0 [[:var 0]]]
                        [:let 3 [:ctor 0 [[:var 2]]]
                         [:let 4 [:ctor 0 [[:var 3]]] [:return [:var 4]]]]])]}})
(defn run [backend session world]
  (case backend
    :reference (m/run world 100)
    :mutable (u/freeze (u/run! (u/thaw world) 100))
    :jvm (u/freeze (lazy/run! (:program session) (u/thaw world) 100))))
(defn complete [backend world input error?]
  (let [functions (functions error?) world (assoc world :functions functions)
        session (raw/open-functions functions {} {:backend backend :fuel 100})
        paused (run backend session (m/start world finalizer [input]))]
    (is (= :suspended (:status paused)))
    (let [finished (run backend session (m/resume paused m/erased))]
      (is (= :done (:status finished)))
      {:paused paused :finished finished :session session})))

(deftest independently-resumed-result-is-consumed-and-associated-in-one-fork
  (doseq [backend [:reference :mutable :jvm]]
    (let [loaded (fixture/loaded) before (:world loaded)
          [world values] (m/allocate before :array 246 (fixture/constants loaded))
          {:keys [paused finished session]} (complete backend world values false)
          wrapper (:result finished) calls (atom [])
          result (import/finish-finalization finished wrapper (fixture/helper-model calls []) fixture/options)
          after (:world result) environment (:environment result)
          root (first (:fields (m/node after environment)))
          constant-map (get-in after [:kernel-environments (:id root) :constant-map])
          cleaned (-> after (m/release environment 1) (update :kernel-environments dissoc (:id root))
                      (m/release root 1) (m/release constant-map 1))
          other-fork (run backend session (m/resume paused m/erased))]
      (is (= :ok (:status result)))
      (is (= 17 (count (get-in result [:certificate :constants]))))
      (is (not (contains? (:heap after) (:id wrapper))))
      (is (= 1 (:rc (m/node after environment))))
      (is (= 2 (:rc (m/node after root))))
      (is (identical? (get-in result [:certificate :env]) (get-in after [:kernel-environments (:id root) :env])))
      (is (= (:heap before) (:heap cleaned)))
      (is (nil? (:kernel-environments finished)))
      (is (= 1 (:rc (m/node finished wrapper))))
      (is (= (:heap finished) (:heap other-fork)))
      (is (= wrapper (:result other-fork)))
      (is (nil? (:kernel-environments other-fork))))))

(deftest independently-completed-io-error-keeps-its-owned-result-and-old-fork
  (doseq [backend [:reference :mutable :jvm]]
    (let [before (m/world {}) [world error] (m/resource before "finalizer-error")
          {:keys [paused finished]} (complete backend world error true)
          wrapper (:result finished) calls (atom [])
          result (import/finish-finalization finished wrapper (fixture/helper-model calls []) fixture/options)
          after (:world result) released (m/release after (:io-result result) 1)]
      (is (= :io-error (:status result)))
      (is (= wrapper (:io-result result)))
      (is (identical? finished after))
      (is (empty? @calls))
      (is (= 1 (:rc (m/node after wrapper))))
      (is (= 1 (:rc (m/node paused error))))
      (is (= (:heap before) (:heap released)))
      (is (= [[:released "finalizer-error"]] (:events released))))))

(deftest strict-negative-association-keeps-an-inspectable-checkpoint-and-original-fork
  (doseq [backend [:reference :mutable :jvm]]
    (let [loaded (fixture/loaded) original (:world loaded) alias (get (fixture/names loaded) "aliasA")
          payload (first (:fields (m/node original alias)))
          [world missing] (guest/constant original "MissingImportType")
          changed (assoc-in world [:heap (:id payload) :fields 1] missing)
          [world values] (m/allocate changed :array 246 (fixture/constants loaded))
          {:keys [finished]} (complete backend world values false)
          wrapper (:result finished)
          error (try (import/finish-finalization finished wrapper (fixture/helper-model (atom []) []) fixture/options)
                     nil (catch clojure.lang.ExceptionInfo e e))
          {:keys [checkpoint environment phase]} (ex-data error)]
      (is (= :kernel-association phase))
      (is (m/ref? environment))
      (is (= 1 (:rc (m/node checkpoint environment))))
      (is (nil? (:kernel-environments checkpoint)))
      (is (not (contains? (:heap checkpoint) (:id wrapper))))
      (is (contains? (:heap finished) (:id wrapper)))
      (is (= (m/node original payload) (m/node (:world loaded) payload)))
      (is (not= (m/node original payload) (m/node changed payload)))
      (is (nil? (:kernel-environments original))))))

(deftest failed-association-helper-preserves-latest-session-owners-and-original-finalizer
  ;; This executes real raw host boundaries/program installation/guest failure;
  ;; the constants getter remains a deliberately failing helper MODEL.
  (doseq [backend [:reference :mutable :jvm]]
    (let [loaded (fixture/loaded)
          [world values] (m/allocate (:world loaded) :array 246 (fixture/constants loaded))
          {:keys [finished]} (complete backend world values false)
          constants-target ["str" ["anonymous"] "recoveryConstants"]
          failed-target ["str" ["anonymous"] "recoveryWitnessFailure"]
          getter-signature {:params [{:ty "object" :borrow true}] :return-type "object"}
          witness-signature {:params [{:ty "object" :borrow true}] :return-type "object"}
          effects (atom 0)
          bindings
          {"recovery-constants"
           {:signature getter-signature
            :handler (fn [{:keys [install-compiled! invoke]} world _]
                       (swap! effects inc)
                       (let [[world _] (install-compiled! world (slurp "fixtures/runtime-compiled-identity.jsonl") {})
                             [world error] (m/resource world "witness-error")
                             [world wrapper] (m/allocate world :ctor 1 [error])]
                         (invoke world failed-target [wrapper])))}
           "recovery-witness-failure"
           {:signature witness-signature
            :handler (fn [_ _ [wrapper]]
                       (throw (ex-info "witness failed after program extension"
                                       {:witness-raw-result wrapper :diagnostic-token :preserve-me})))}}
          functions (assoc (:functions finished)
                           constants-target {:params [1] :raw-extern {:symbol "recovery-constants" :signature getter-signature}
                                             :body [:host "recovery-constants" [[:var 1]] 2 [:return [:var 2]]]}
                           failed-target {:params [1] :raw-extern {:symbol "recovery-witness-failure" :signature witness-signature}
                                          :body [:host "recovery-witness-failure" [[:var 1]] 2 [:return [:var 2]]]})
          finished (assoc finished :functions functions)
          original-wrapper (:result finished)
          original-session (raw/open-functions functions bindings {:backend backend})
          active (atom original-session)
          invoke (fn [state target args]
                   (let [r (raw/call @active state target args)]
                     (reset! active (:session r)) [(:state r) (:value r)]))
          error (try (import/finish-finalization finished original-wrapper invoke
                                                (assoc fixture/options :helpers {:constants constants-target}))
                     nil (catch clojure.lang.ExceptionInfo e e))
          {:keys [checkpoint checkpoint-session session finalizer-result finalization-entry
                  witness-raw-result host-boundaries] :as data} (ex-data error)
          environment (:environment finalization-entry)]
      (is (some? error))
      (is (= :preserve-me (:diagnostic-token data)))
      (is (= 1 @effects))
      (is (= :host-call (:status checkpoint)))
      (is (= "recovery-witness-failure" (get-in checkpoint [:host-request :symbol])))
      (is (identical? checkpoint-session session))
      (is (identical? (:functions checkpoint) (:functions session)))
      (is (contains? (:functions checkpoint) ["str" ["anonymous"] "answer"]))
      (is (not (contains? (:functions finished) ["str" ["anonymous"] "answer"])))
      (is (= 1 (count host-boundaries)))
      (is (= "recovery-constants" (get-in (first host-boundaries) [:checkpoint :host-request :symbol])))
      (is (not (contains? data :environment)))
      (is (= original-wrapper (:io-result finalizer-result)))
      (is (identical? finished (:checkpoint finalizer-result)))
      (is (= 1 (:rc (m/node (:checkpoint finalizer-result) original-wrapper))))
      (is (not (contains? (:heap checkpoint) (:id original-wrapper))))
      (is (= 1 (:rc (m/node (:checkpoint finalization-entry) environment))))
      (is (= 1 (:rc (m/node checkpoint witness-raw-result))))
      (is (= [[:released "witness-error"]] (:events (m/release checkpoint witness-raw-result 1))))
      (is (nil? (:kernel-environments checkpoint)))
      (is (nil? (:kernel-environments finished))))))

(deftest malformed-success-result-retains-the-exact-original-owned-io-snapshot
  (let [[world wrapper] (m/allocate (m/world {}) :ctor 0 [42])
        error (try (import/finish-finalization world wrapper (fn [& _] (throw (Exception. "must not invoke"))))
                   nil (catch clojure.lang.ExceptionInfo e e))
        data (ex-data error)]
    (is (re-find #"Environment reference" (.getMessage error)))
    (is (= wrapper (:io-result data)))
    (is (= wrapper (get-in data [:finalizer-result :io-result])))
    (is (identical? world (get-in data [:finalizer-result :checkpoint])))
    (is (= 1 (:rc (m/node (:checkpoint data) wrapper))))))
