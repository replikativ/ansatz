(ns prototype.artifact-host-test
  "Artifact lineage across real Java checking and modeled guest publication.
   Generated CI encoding uses the existing captured Lean helper IR."
  (:require [clojure.test :refer [deftest is]]
            [prototype.artifact-association-test :as fixture]
            [prototype.kernel-host :as host]
            [prototype.imported-kernel :as kernel]
            [prototype.module-import :as module]
            [prototype.checked-delta :as delta]
            [prototype.kernel-projection-snapshot :as snapshot]
            [prototype.kernel-bridge-test :as guest]
            [prototype.guest-encoding :as encoding]
            [prototype.guest-encoding-test :as encoder]
            [prototype.raw-interop :as raw]
            [prototype.machine :as m]
            [ansatz.kernel.name :as name])
  (:import [ansatz.kernel Env ConstantInfo]))

(def publication ["str" ["anonymous"] "artifact-model-publication"])
(def helpers
  (assoc module/helpers :definition publication :definition-any publication :axiom publication
         :empty? ["str" ["anonymous"] "artifact-empty"]
         :error ["str" ["anonymous"] "artifact-error"]))
(defn publish-context [context generated? encode-invoke]
  (update context :invoke
    (fn [invoke]
      (fn [world target args]
        (cond
          (= target publication)
          (let [[environment declaration generated] args
                root (first (:fields (m/node world environment)))
                values (:fields (m/node world (first (:fields (m/node world root)))))
                additions (if generated? (:fields (m/node world generated)) [declaration])
                [world environment] (fixture/environment (m/release world environment 1)
                                                        (into values additions))]
            (m/allocate world :ctor 1 [environment]))
          (= target encoding/family-helper) (encode-invoke world target args)
          (= target (:error helpers))
          (let [[world error] (m/allocate world :ctor 12 [(first args)])]
            (m/allocate world :ctor 0 [error]))
          :else (invoke world target args))))))

(defn invoke-definition [context world environment declaration]
  (let [binding (host/make-binding helpers {})]
    ((:handler binding) context world
     [environment 1000000 1000 declaration (m/->Tag 0)])))

(defn take-result [world result]
  (is (= 1 (:tag (m/node world result))))
  (let [environment (first (:fields (m/node world result)))]
    [(-> world (m/retain environment 1) (m/release result 1)) environment]))

(deftest callback-extends-only-new-witnesses-and-header-inherits-the-same-lineage
  (fixture/with-issued
    (fn [{:keys [world environment context admission refs] :as base}]
      (let [root (first (:fields (m/node world environment)))
            original (get-in world [:kernel-environments (:id root)])
            [world declaration] (fixture/add-definition world refs "callbackValue" "aliasA")
            context (publish-context context false nil)
            seen (atom []) capture snapshot/expression-array-witnesses
            [world result]
            (with-redefs [snapshot/validate-segments (fn [& _] (throw (ex-info "Full base scan on callback" {})))
                          snapshot/expression-array-witnesses
                          (fn [projection] (swap! seen conj (count (:projected projection)))
                            (capture projection))]
              (invoke-definition context world environment declaration))
            [world next-env] (take-result world result)
            next-root (first (:fields (m/node world next-env)))
            next-entry (get-in world [:kernel-environments (:id next-root)])
            segments (:java-guard-segments next-entry)
            map-root (:constant-map next-entry)
            [world header-root] (m/allocate (m/retain world map-root 1) :ctor 0 [map-root])
            [world header-env] (m/allocate world :ctor 0 [header-root])
            [world header-entry] (host/resolve-association context world header-env module/helpers)]
        (is (= [1] @seen))
        (is (= 18 (.size ^Env (:env next-entry))))
        (is (= (:kernel-provenance original) (:kernel-provenance next-entry)
               (:kernel-provenance header-entry)))
        (is (identical? admission (get-in next-entry [:kernel-provenance :artifact-admission])))
        (is (= 2 (count segments)))
        (is (identical? (first (:java-guard-segments original)) (first segments)))
        (is (identical? segments (:java-guard-segments header-entry)))
        (is (thrown-with-msg? Exception #"Strict association"
                             (host/inherit-checked-association context world header-env module/helpers)))
        (let [[world cap] (delta/capture-artifact-base context world next-env module/helpers admission)
              values (:fields (m/node world map-root))
              checked (delta/verify-artifact-extension context world values cap {})]
          (is (identical? (:env next-entry) (:env checked))))
        (let [^ConstantInfo ci (.lookup ^Env (:env next-entry) (name/from-string "callbackValue"))
              value (.value ci)]
          (try
            (set! (.value ci) (.type ci))
            (is (thrown-with-msg? Exception #"checking shape changed"
                                 (delta/capture-artifact-base context world next-env module/helpers admission)))
            (finally (set! (.value ci) value))))))))

(defn empty-family [world]
  (let [[world label] (guest/guest-name world "CallbackEmpty")
        [world level] (guest/ctor world 1 [guest/nil-tag] 8)
        [world type] (guest/ctor world 3 [level] 8)
        [world inductive] (guest/ctor world 0 [label type guest/nil-tag] 0)
        [world types] (guest/ctor world 1 [inductive guest/nil-tag] 0)]
    (guest/ctor world 6 [guest/nil-tag 0 types] 1)))

(deftest generated-family-preserves-artifact-base-and-captures-only-generated-cis
  (fixture/with-issued
    (fn [{:keys [world environment context admission]}]
      (let [functions (merge (:functions world) @encoder/functions)
            world (assoc world :functions functions)
            session (raw/open-functions functions {} {:backend :reference :fuel 1000000})
            encode-invoke (fn [world target args]
                            (let [result (raw/call session world target args)]
                              [(:state result) (:value result)]))
            context (-> context (assoc :trusted-functions functions)
                        (publish-context true encode-invoke))
            [world declaration] (empty-family world)
            helpers (assoc helpers :generated publication :encode-family encoding/family-helper)
            binding (host/make-binding helpers {})
            [world result]
            (with-redefs [snapshot/validate-segments (fn [& _] (throw (ex-info "Full base scan on generation" {})))]
              ((:handler binding) context world
               [environment 1000000 1000 declaration (m/->Tag 0)]))
            [world next-env] (take-result world result)
            root (first (:fields (m/node world next-env)))
            entry (get-in world [:kernel-environments (:id root)])
            segment (peek (:java-guard-segments entry))]
        (is (= #{"CallbackEmpty" "CallbackEmpty.rec"} (set (map str (keys (:projected segment))))))
        (is (= 19 (.size ^Env (:env entry))))
        (is (identical? admission (get-in entry [:kernel-provenance :artifact-admission])))
        (is (= 2 (count (:java-guard-segments entry))))
        (is (vector? (snapshot/validate-segments (:env entry) (:java-guard-segments entry))))
        (let [[world cap] (delta/capture-artifact-base context world next-env module/helpers admission)]
          (is (some? cap)))))))

(deftest late-publication-guard-failure-retains-latest-world-and-owner-credits
  (fixture/with-issued
    (fn [{:keys [world environment context refs]}]
      (let [[entry declaration] (fixture/add-definition world refs "badPublication" "aliasA")
            checked-ci (atom nil) old-value (atom nil) post-helper (atom nil) calls (atom 0)
            context (-> (publish-context context false nil)
                        (update :invoke
                          (fn [invoke]
                            (fn [world target args]
                              (let [[world value] (invoke world target args)]
                                (if (= target (:constant-map module/helpers))
                                  (let [^ConstantInfo ci @checked-ci
                                        _ (swap! calls inc)
                                        _ (set! (.value ci) (.type ci))
                                        [world scratch] (m/allocate world :ctor 0 [])
                                        world (m/release world scratch 1)]
                                    (reset! post-helper world) [world value])
                                  [world value]))))))
            capture snapshot/snapshot-segment
            failure (try
                      (with-redefs [snapshot/snapshot-segment
                                    (fn [projected]
                                      (let [segment (capture projected) ^ConstantInfo ci (first (vals projected))]
                                        (reset! checked-ci ci) (reset! old-value (.value ci)) segment))]
                        (invoke-definition context entry environment declaration))
                      nil (catch clojure.lang.ExceptionInfo cause cause))]
        (try
          (let [{:keys [checkpoint temporary-owners kernel-publication-temporary-owners
                        kernel-publication-entry]} (ex-data failure)
                [result root map-root] temporary-owners
                cleaned (reduce #(m/release %1 %2 1) checkpoint temporary-owners)]
            (is (some? failure))
            (is (re-find #"checking shape changed" (.getMessage failure)))
            (is (= 1 @calls))
            (is (identical? @post-helper checkpoint))
            (is (= 3 (count temporary-owners)))
            (is (= temporary-owners kernel-publication-temporary-owners))
            (is (= entry (:checkpoint kernel-publication-entry)))
            (is (= 1 (:rc (m/node checkpoint result))))
            (is (= 2 (:rc (m/node checkpoint root)) (:rc (m/node checkpoint map-root))))
            (is (nil? (get-in checkpoint [:kernel-environments (:id root)])))
            (is (= (:heap (m/release entry environment 1)) (:heap cleaned))))
          (finally (when-let [^ConstantInfo ci @checked-ci] (set! (.value ci) @old-value))))))))

(deftest guarded-strict-callback-retains-complete-witnesses-and-strict-provenance
  (fixture/with-issued
    (fn [{:keys [world context values refs]}]
      (let [certificate (kernel/verify-constants world values {:allow-axioms? true :allow-unsafe? true})
            captured (snapshot/snapshot-projection certificate)
            certificate (assoc certificate :java-guard-segments
                               [(select-keys captured [:projected :shapes :expression-arrays])])
            [world environment] (fixture/environment world values)
            world (kernel/associate-checked-progress context world environment module/helpers certificate)
            [world declaration] (fixture/add-definition world refs "strictCallbackValue" "aliasA")
            [world result] (invoke-definition (publish-context context false nil) world environment declaration)
            [world environment] (take-result world result)
            root (first (:fields (m/node world environment)))
            entry (get-in world [:kernel-environments (:id root)])]
        (is (= :strict-fresh (get-in entry [:kernel-provenance :base-basis])))
        (is (= 2 (count (:java-guard-segments entry))))
        (is (vector? (snapshot/validate-segments (:env entry) (:java-guard-segments entry))))))))
