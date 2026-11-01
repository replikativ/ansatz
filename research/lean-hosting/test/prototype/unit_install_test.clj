(ns prototype.unit-install-test
  (:require [clojure.test :refer [deftest is]]
            [prototype.eval-const :as eval]
            [prototype.eval-const-test :as fixtures]
            [prototype.eval-const-resolution-test :as resolution]
            [prototype.program-install :as install]
            [prototype.raw-interop :as raw]
            [prototype.machine :as m]))

(def tick (fixtures/n "sourceInitializerTick"))
(def init-names [(fixtures/n "sourceInitialize") (fixtures/n "futureMacroRegistration")])
(def tick-row
  {:kind "decl" :name tick :sourceLocal false
   :ir {:extern {:f tick :xs [{:x {:idx 1} :ty "uint8" :borrow false}
                              {:x {:idx 2} :ty "void" :borrow false}]
                 :type "object" :ext {:entries [{:standard {:backend ["str" ["anonymous"] "all"]
                                                           :fn "test_initializer_tick"}}]}}}})
(defn initializer-row [name]
  {:kind "decl" :name name :sourceLocal true :dependencies [tick]
   :runtime {:role "ordinary" :initializer nil}
   :ir {:fdecl {:f name :xs [{:x {:idx 1} :ty "void" :borrow false}]
                :type "object" :info {}
                :body ["vdecl" {:idx 2} "uint8" {:lit {:v {:num {:v (inc (.indexOf init-names name))}}}}
                       ["vdecl" {:idx 3} "object" {:fap {:c tick :ys [{:var {:id {:idx 2}}} {:var {:id {:idx 1}}}]}}
                        ["ret" {:var {:id {:idx 3}}}]]]}}})
(defn candidate []
  (-> resolution/fixture
      (update :declarations merge {tick tick-row} (into {} (map (juxt identity initializer-row)) init-names))
      (assoc-in [:manifests 0 :initializationPlan :actions]
                (mapv (fn [name] {:action {:kind "io" :name name :target name} :meta false}) init-names))))
(defn setup [backend fail-second?]
  (let [binding {:signature {:params [{:ty "uint8" :borrow false} {:ty "void" :borrow false}] :return-type "object"}
                 :handler (fn [_ world [index _]]
                            (is (true? (:initializing? world)))
                            (let [n (inc (count (:events world)))
                                  world (update world :events conj [:initializer index])]
                              (if (and fail-second? (= 2 n))
                                (m/allocate world :ctor 1 ["initializer failed"])
                                (m/allocate world :ctor 0 [m/erased]))))}
        bindings {"test_initializer_tick" binding}
        functions {tick (second (raw/lower bindings tick-row))}
        [world local-environment] (m/allocate (m/world functions) :ctor 57 ["already elaborated macro"])
        catalogue {:manifests (:manifests resolution/fixture) :declarations {tick tick-row}}
        options {:catalogue catalogue :trusted-functions functions}
        installed (eval/install-bundle world (resolution/bundle-text (candidate)) options)
        session (atom (raw/open-functions (get-in installed [:world :functions]) bindings {:backend backend}))
        context {:invoke (fn [world target args]
                           (let [result (raw/call @session world target args)]
                             (reset! session (:session result))
                             [(:state result) (:value result)]))}]
    {:installed installed :options options :context context :original world :local-environment local-environment}))

(deftest final-file-install-admits-code-without-replaying-source-or-macro-effects
  ;; Native RuntimeCompileShimInitializerTests confirms source elaboration runs
  ;; the local macro, but does not run these future module IO initializers.
  (doseq [backend [:reference :mutable :jvm]]
    (let [{:keys [installed options local-environment]} (setup backend false)
          world (:world installed)
          repeated (eval/install-bundle world (resolution/bundle-text (candidate)) options)]
      (is (empty? (:events world)))
      (is (= ["already elaborated macro"] (:fields (m/node world local-environment))))
      (is (= 2 (count (:pending-local-initializers installed))))
      (is (empty? (get-in world [:eval-const-authorizations :completed-actions])))
      (is (empty? (:new-functions repeated)))
      (is (= 2 (count (:pending-local-initializers repeated))))
      (is (= (:boxed-entrypoints installed) (:boxed-entrypoints repeated)))
      (doseq [[name f] (:functions world)] (is (identical? f (get-in repeated [:world :functions name])))))))

(deftest explicit-module-load-runs-producer-order-once-and-retains-fork-local-evidence
  (doseq [backend [:reference :mutable :jvm]]
    (let [{:keys [installed options context local-environment]} (setup backend false)
          world (:world installed)
          loaded (eval/run-initializers context world installed)
          again (eval/run-initializers context loaded installed)
          final (eval/install-bundle loaded (resolution/bundle-text (candidate)) options)
          fork (eval/run-initializers context world installed)]
      (is (= [[:initializer 1] [:initializer 2]] (:events loaded)))
      (is (= (:events loaded) (:events fork)))
      (is (empty? (:events world)))
      (is (= loaded again))
      (is (empty? (:pending-local-initializers final)))
      (is (= (:events loaded) (get-in final [:world :events])))
      (is (= 2 (count (get-in loaded [:eval-const-authorizations :completion-evidence]))))
      (is (= :ready (get-in loaded [:eval-const-authorizations :initializations (:unit-digest installed) :status])))
      (is (not (contains? loaded :initializing?)))
      (is (= ["already elaborated macro"] (:fields (m/node loaded local-environment))))
      (doseq [planned (get-in installed [:initialization-plan :actions])]
        (is (= :ready (get-in loaded [:globals [:prototype.initialization/io (get-in planned [:action :name])] :status])))
        (is (= planned (:planned (eval/completion-evidence loaded installed planned)))))
      ;; Explicit opt-in uses the same evidence; it does not replay a module.
      (is (= (:events loaded)
             (get-in (eval/install-bundle context loaded (resolution/bundle-text (candidate))
                                         (assoc options :initialize? true)) [:world :events]))))))

(deftest completion-is-not-inferred-from-plan-metadata-or-another-forks-effects
  (let [{:keys [installed options context]} (setup :reference false)
        world (:world installed)
        planned (first (get-in installed [:initialization-plan :actions]))
        loaded (eval/run-initializers context world installed)
        receipt (eval/completion-evidence loaded installed planned)
        text (resolution/bundle-text (candidate))]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"actual ready marker"
                         (eval/completion-evidence world installed planned)))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"explicit evidence"
                         (eval/install-bundle world text (assoc options :completed-local-actions #{planned}))))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Invalid initialization completion evidence"
                         (eval/install-bundle world text (assoc options :completion-evidence [receipt]))))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"initialization action differs"
                         (eval/install-bundle loaded (resolution/bundle-text
                                                       (assoc-in (candidate) [:manifests 0 :initializationPlan :actions 0 :meta] true)) options)))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"unit digest authority"
                         (eval/install-bundle (update-in loaded [:eval-const-authorizations] dissoc :unit-digests) text options)))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"omits selected dependency IR"
                         (eval/install-bundle world (resolution/bundle-text
                                                      (update (candidate) :declarations dissoc tick)) options)))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"selected IR differs"
                         (eval/install-bundle world (resolution/bundle-text
                                                      (assoc-in (candidate) [:declarations resolution/answer :ir :fdecl :xs 1 :borrow] false)) options)))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Invalid initialization completion evidence"
                         (eval/run-initializers context
                                                (assoc-in loaded [:globals (:marker receipt)]
                                                          (into {} (map identity) (:ready-entry receipt)))
                                                installed)))))

(deftest failed-module-initializer-world-cannot-be-retried-as-clean
  (doseq [backend [:reference :mutable :jvm]]
    (let [{:keys [installed context]} (setup backend true)
          failure (try (eval/run-initializers context (:world installed) installed) nil
                       (catch clojure.lang.ExceptionInfo error error))
          snapshot (:checkpoint (ex-data failure))]
      (is (some? failure))
      (is (map? snapshot))
      (is (= [[:initializer 1] [:initializer 2]] (:events snapshot)))
      (is (= 1 (count (get-in snapshot [:eval-const-authorizations :completion-evidence]))))
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"partially entered"
                           (eval/run-initializers context snapshot installed)))
      (is (empty? (get-in installed [:world :events]))))))

(deftest final-bundle-may-combine-previously-compiled-helpers-with-new-entrypoints
  (let [next-name (fixtures/n "fileAnswer")
        old-boxed ["str" resolution/answer "_boxed"]
        next-row {:kind "decl" :name next-name :sourceLocal true :dependencies [old-boxed]
                  :runtime {:role "value" :initializer nil}
                  :ir {:fdecl {:f next-name :xs [] :type "tobject" :info {}
                               :body ["vdecl" {:idx 1} "tagged" {:lit {:v {:num {:v 42}}}}
                                      ["vdecl" {:idx 2} "tobject"
                                       {:fap {:c old-boxed :ys ["erased" {:var {:id {:idx 1}}}]}}
                                       ["ret" {:var {:id {:idx 2}}}]]]}}}
        next-action {:action {:kind "value" :name next-name :target next-name} :meta false}
        combined (-> (candidate) (assoc-in [:declarations next-name] next-row)
                     (update-in [:manifests 0 :requestedRoots] conj next-name)
                     (update-in [:manifests 0 :entryPoints] conj {:name next-name :boxedTarget next-name})
                     (update-in [:manifests 0 :initializationPlan :actions] conj next-action))]
    (doseq [backend [:reference :mutable :jvm]]
      (let [{:keys [installed options]} (setup backend false)
            before (:world installed)
            result (eval/install-bundle before (resolution/bundle-text combined) options)
            after (:world result)
            bindings {"test_initializer_tick" {:signature {:params [{:ty "uint8" :borrow false}
                                                                     {:ty "void" :borrow false}]
                                                         :return-type "object"}
                                               :handler (fn [_ _ _] (throw (ex-info "IO must stay pending" {})))}}
            session (raw/open-functions (:functions after) bindings {:backend backend})
            called (raw/call session after next-name [])]
        (is (= 42 (:value called)))
        (is (empty? (:events (:state called))))
        (is (= 3 (count (:pending-local-initializers result))))
        (is (= #{next-name ["str" next-name "_ansatz_global_initializer"]}
               (set (keys (:new-functions result)))))
        (is (identical? (get-in before [:functions old-boxed]) (get-in after [:functions old-boxed])))
        (is (= #{resolution/answer next-name} (set (keys (:boxed-entrypoints result)))))
        (is (empty? (:new-functions (eval/install-bundle (:state called)
                                                        (resolution/bundle-text combined) options))))))))
