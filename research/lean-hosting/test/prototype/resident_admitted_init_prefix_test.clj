(ns prototype.resident-admitted-init-prefix-test
  "Bounded synthetic Init lifecycle models. Positive tests replace only artifact
   token authentication around the existing tiny Init transport fixture; they do
   not weaken supported issuer pins or establish full Init/provider acceptance."
  (:require [clojure.test :refer [deftest is]]
            [prototype.resident-init-prefix :as prefix]
            [prototype.resident-init-prefix-test :as strict-model]
            [prototype.resident-frontend :as resident]
            [prototype.source-import :as source]
            [prototype.module-import :as imports]
            [prototype.module-store :as store]
            [prototype.kernel-artifact :as artifact]
            [prototype.kernel-projection-snapshot :as projection]
            [prototype.raw-interop :as raw]
            [prototype.machine :as m]))

(defn with-lifecycle-model [f]
  (strict-model/with-fixture :reference
    (fn [{:keys [context checked configuration source] :as fixture}]
      (let [token (Object.) prepared (resident/snapshot context)
            assumptions {:basis :trusted-artifact :scope ::synthetic-init}
            provenance {:base-basis :trusted-artifact :artifact-admission token :base-assumptions assumptions}
            base (-> (:certificate checked) (dissoc :order :certificate)
                     (assoc :basis :trusted-artifact :profile ::synthetic-init :source source
                            :base-assumptions assumptions))
            guard (projection/snapshot-projection base)
            segments [(select-keys guard [:projected :shapes :expression-arrays])]
            projected (assoc base :kernel-provenance provenance :java-guard-segments segments)
            world (update (:world prepared) :kernel-environments
                          (fn [entries] (into {} (map (fn [[id entry]]
                                                       [id (assoc entry :kernel-provenance provenance
                                                                  :java-guard-segments segments)])) entries)))
            admitted {:status :ok :world world :session (:session prepared)
                      :environment (:environment prepared) :admission token
                      :checked-result projected :kernel-provenance provenance}]
        ;; This is the explicit model seam: actual artifact profiles remain fixed.
        ;; All native closure/scaffold, Java witness and resident checks execute.
        (with-redefs [artifact/inspect-for-world
                      (fn [world candidate]
                        (when-not (identical? token candidate)
                          (throw (ex-info "Synthetic issued token differs" {})))
                        (store/describe-attached world source)
                        (projection/validate-projection guard)
                        projected)]
          (let [admitted-context (resident/adopt-admitted (assoc prepared :world world) configuration token)]
            (try (f (assoc fixture :context admitted-context :admitted admitted :token token))
                 (finally (resident/close! admitted-context)))))))))

(defn prepare [{:keys [context admitted configuration native-bindings]}]
  (prefix/prepare-admitted-init-prefix context admitted
    {:configuration configuration :native-bindings native-bindings}))

(deftest synthetic-admitted-prefix-forks-releases-and-retires-with-its-original-mode
  (with-lifecycle-model
    (fn [{:keys [context source] :as fixture}]
      (let [entry (resident/snapshot context) prepared (prepare fixture)
            active (:context prepared) capability (:prefix prepared)
            world (:world (resident/snapshot active))
            scaffold (first (vals (:source-import-prefixes world)))
            branch (resident/fork active)]
        (is (= :trusted-artifact (:basis scaffold)))
        (is (not (contains? scaffold :certificate)))
        (is (= 17 (:constant-count (prefix/descriptor capability))))
        (is (= source/init-requests (:producer-imports scaffold)))
        (is (= 1 (:rc (m/node world (:state scaffold)))))
        (is (identical? entry (resident/snapshot context)))
        ;; The issued prefix's adopter keeps only mode/token, not this wrapper.
        (resident/abandon! context)
        (let [released (prefix/release-prefix active capability)
              released-context (:context released)]
          (is (empty? (get-in (resident/snapshot released-context) [:world :source-import-prefixes])))
          (is (thrown-with-msg? Exception #"artifact"
                (resident/adopt-prepared (resident/snapshot released-context) (:configuration fixture))))
          (resident/close! released-context))
        (is (= :closed (:status (prefix/release-prefix-and-close-branch branch capability))))
        (is (some? (source/validate-init-prefix! world scaffold)))
        (is (false? @(:closed source)))
        (resident/close! branch)
        (resident/close! active)))))

(deftest synthetic-artifact-prefix-rejects-legacy-imports-before-guest-effects
  (with-lifecycle-model
    (fn [{:keys [context calls] :as fixture}]
      (let [prepared (prepare fixture) active (:context prepared) capability (:prefix prepared)
            world (:world (resident/snapshot active)) scaffold (first (vals (:source-import-prefixes world)))
            effects (atom 0) budgets {:outer-fuel 10 :helper-fuel 10 :attempt-fuel 100}]
        (reset! calls [])
        (with-redefs [raw/call (fn [& _] (swap! effects inc) (throw (ex-info "Must not execute" {})))]
          (is (thrown-with-msg? Exception #"not implemented"
                (prefix/prepare-source-import-over-init active {} capability {:kernel-policy {} :budgets budgets})))
          (is (thrown-with-msg? Exception #"not implemented"
                (prefix/prepare-source-reconstruction-import-over-init active {} capability nil nil
                  {:kernel-policy {} :budgets budgets})))
          (is (thrown-with-msg? Exception #"not implemented"
                (source/assemble-over-init world (fn [& _] (swap! effects inc)) scaffold nil nil []))))
        (is (zero? @effects))
        (is (empty? @calls))
        (resident/close! active)))))

(deftest synthetic-artifact-prefix-keeps-positive-projection-and-lineage-checks
  (with-lifecycle-model
    (fn [{:keys [context admitted configuration native-bindings calls] :as fixture}]
      (let [options {:configuration configuration :native-bindings native-bindings}]
        (reset! calls [])
        (doseq [bad [(assoc admitted :admission (Object.))
                     (assoc-in admitted [:checked-result :constants] {})
                     (assoc-in admitted [:kernel-provenance :base-basis] :strict-fresh)]]
          (is (thrown? Exception (prefix/prepare-admitted-init-prefix context bad options))))
        (is (thrown? Exception (prefix/prepare-init-prefix context admitted options)))
        (is (empty? @calls)))
      (let [prepared (prepare fixture) active (:context prepared)
            world (:world (resident/snapshot active)) scaffold (first (vals (:source-import-prefixes world)))
            anchor (:id (:checked-anchor scaffold))]
        (is (thrown-with-msg? Exception #"not authenticated"
              (source/release-init-prefix
                (assoc-in world [:kernel-environments anchor :kernel-provenance :artifact-admission] (Object.)) scaffold)))
        (is (thrown-with-msg? Exception #"not authenticated"
              (source/release-init-prefix
                (assoc-in world [:kernel-environments anchor :constant-map] (m/->Ref -1)) scaffold)))
        (resident/close! active)))))

(deftest actual-native17-artifact-is-rejected-as-an-init-prefix-before-invocation
  (let [functions (into {} (for [target (vals imports/helpers)]
                             [target {:params [] :body [:return [:imm 0]]}]))
        loaded (artifact/load-admitted (m/world functions) artifact/native17-profile
                                      "fixtures/imported-kernel-native.jsonl")]
    (try
      (let [projected (artifact/inspect-for-world (:world loaded) (:admission loaded))
            admitted {:status :ok :world (:world loaded) :admission (:admission loaded)
                      :checked-result projected :kernel-provenance (:kernel-provenance projected)}
            context {:invoke (fn [& _] (throw (ex-info "Must not invoke" {})))
                     :trusted-functions functions :bindings {} :trusted-bindings {}}
            actual (store/describe-attached (:world loaded) (:source loaded))]
        (is (thrown-with-msg? Exception #"explicit native Init closure"
              (source/prepare-admitted-init-prefix context actual admitted))))
      (finally (.close ^java.io.Closeable (:source loaded))))))
