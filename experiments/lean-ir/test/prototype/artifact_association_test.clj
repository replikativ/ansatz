(ns prototype.artifact-association-test
  "Bounded artifact-relative kernel boundary, using the provider-pinned 17 CIs.
   Guest accessors are boundary models; this is not a full Init/provider test."
  (:require [clojure.test :refer [deftest is]]
            [prototype.kernel-artifact :as artifact]
            [prototype.checked-delta :as delta]
            [prototype.delta-import :as finish]
            [prototype.imported-kernel :as kernel]
            [prototype.module-import :as module]
            [prototype.module-import-test :as model]
            [prototype.imported-kernel-test :as fixture]
            [prototype.kernel-bridge-test :as guest]
            [prototype.machine :as m]
            [ansatz.kernel.name :as name])
  (:import [ansatz.kernel Env ConstantInfo]))

(defn environment [world values]
  (let [world (reduce #(m/retain %1 %2 1) world values)
        [world values] (m/allocate world :array 246 values)
        [world root] (m/allocate world :ctor 0 [values])]
    (m/allocate world :ctor 0 [root])))
(defn completed [world values]
  (let [[world env] (environment world values)] (m/allocate world :ctor 0 [env])))
(defn issue
  "Caller closes :source. :context has independent functions; helpers accept
   modeled [Environment [root [array CIs]]] and follow real borrowed/owned args."
  []
  (let [loaded (artifact/load-admitted (m/world {}) artifact/native17-profile
                                      "fixtures/imported-kernel-native.jsonl")
        world (:world loaded) admission (:admission loaded)
        projection (artifact/inspect-for-world world admission)
        values (vec (vals (:constants projection)))
        functions (into {} (map (fn [target] [target {:params [1] :body [:return [:var 1]]}]))
                        (mapv module/helpers [:root :constants :quot-init? :constant-map]))
        world (assoc world :functions functions)
        context {:invoke (model/helper-model (atom []) []) :trusted-functions functions
                 :bindings {} :trusted-bindings {}}
        [world env] (environment world values)
        world (artifact/associate-admitted-progress context world env module/helpers admission)]
    (merge loaded {:world world :environment env :context context :values values :projection projection
                   :refs (into {} (map (fn [[n ref]] [(str n) ref])) (:constants projection))})))
(defn with-issued [f]
  (let [base (issue)] (try (f base) (finally (.close ^java.io.Closeable (:source base))))))
(defn add-definition [world refs label body-name]
  (let [cv (first (:fields (m/node world (fixture/payload world (get refs "A")))))
        type (nth (:fields (m/node world cv)) 2)
        [world value] (guest/constant world body-name)]
    (guest/declaration world label type value)))
(defn capture [{:keys [world environment context admission]}]
  (delta/capture-artifact-base context world environment module/helpers admission))

(deftest issued-token-establishes-an-exact-artifact-anchor-with-stored-witnesses
  (with-issued
    (fn [{:keys [world environment admission projection]}]
      (let [root (first (:fields (m/node world environment)))
            anchor (get-in world [:kernel-environments (:id root)])]
        (is (= :trusted-artifact (get-in anchor [:kernel-provenance :base-basis])))
        (is (identical? admission (get-in anchor [:kernel-provenance :artifact-admission])))
        (is (= (:base-assumptions projection) (get-in anchor [:kernel-provenance :base-assumptions])))
        (is (identical? (:java-guard-segments projection) (:java-guard-segments anchor)))
        (is (identical? (:env projection) (:env anchor)))
        (is (not (contains? anchor :order)))))))

(deftest artifact-delta-checks-only-new-groups-and-never-claims-strict-order
  (with-issued
    (fn [{:keys [context values refs admission projection] :as base}]
      (let [[world capability] (capture base)
            [world added] (add-definition world refs "artifactFirst" "aliasA")
            [world io] (completed world (conj values added))
            result (with-redefs [kernel/verify-constants (fn [& _] (throw (ex-info "Whole base rechecked" {})))]
                     (finish/finish-artifact-finalization context world io capability))
            checked (:checked-result result)
            env (:environment result) world (:world result)
            root (first (:fields (m/node world env))) anchor (get-in world [:kernel-environments (:id root)])]
        (is (= :ok (:status result)))
        (is (nil? (:certificate result)))
        (is (= 18 (count (:constants checked))))
        (is (= ["artifactFirst"] (mapv #(str (second %)) (:new-order checked))))
        (is (not (contains? checked :order)))
        (is (identical? admission (get-in checked [:kernel-provenance :artifact-admission])))
        (is (= (:kernel-provenance checked) (:kernel-provenance anchor)))
        (is (= 2 (count (:java-guard-segments anchor))))
        (is (identical? (first (:java-guard-segments projection)) (first (:java-guard-segments anchor))))
        (doseq [[n ci] (:projected projection)]
          (is (identical? ci (.lookup ^Env (:env checked) n))))))))

(deftest strict-named-entry-points-reject-artifact-lineage-and-capabilities
  (with-issued
    (fn [{:keys [context world environment values admission projection] :as base}]
      (let [[world capability] (capture base)
            [world other] (prototype.artifact-association-test/environment world values)]
        (is (thrown-with-msg? Exception #"Strict association rejects"
              (kernel/associate-checked context world other module/helpers projection)))
        (is (thrown-with-msg? Exception #"Strict base capture rejects"
              (delta/capture-base context world environment module/helpers projection)))
        (is (thrown-with-msg? Exception #"different base provenance"
              (delta/verify-extension context world values capability {})))
        (is (thrown-with-msg? Exception #"issued in-process"
              (artifact/associate-admitted-progress context world other module/helpers {:artifact-admission admission})))))))

(deftest descendant-recapture-allows-a-second-checked-extension-with-the-original-token
  (with-issued
    (fn [{:keys [context values refs admission] :as base}]
      (let [[world capability] (capture base)
            [world first-ref] (add-definition world refs "artifactFirst" "aliasA")
            [world io] (completed world (conj values first-ref))
            first-result (finish/finish-artifact-finalization context world io capability)
            [world capability] (delta/capture-artifact-base context (:world first-result) (:environment first-result)
                                                           module/helpers admission)
            [world second-ref] (add-definition world refs "artifactSecond" "artifactFirst")
            [world io] (completed world (into values [first-ref second-ref]))
            second-result (finish/finish-artifact-finalization context world io capability)
            checked (:checked-result second-result)]
        (is (= :ok (:status second-result)))
        (is (= 19 (count (:constants checked))))
        (is (= ["artifactSecond"] (mapv #(str (second %)) (:new-order checked))))
        (is (not (contains? checked :order)))
        (is (identical? admission (get-in checked [:kernel-provenance :artifact-admission])))
        (is (= 3 (count (:java-guard-segments checked))))))))

(deftest earlier-added-java-mutation-cannot-be-laundered-by-recapture
  (with-issued
    (fn [{:keys [context values refs admission] :as base}]
      (let [[world capability] (capture base)
            [world added] (add-definition world refs "artifactFirst" "aliasA")
            [world io] (completed world (conj values added))
            result (finish/finish-artifact-finalization context world io capability)
            ^ConstantInfo ci (get-in result [:checked-result :projected (name/from-string "artifactFirst")])
            original (.value ci)]
        (try
          (set! (.value ci) (.type ci))
          (is (thrown? Exception
                (delta/capture-artifact-base context (:world result) (:environment result) module/helpers admission)))
          (finally (set! (.value ci) original)))))))

(deftest invalid-additions-and-inherited-ref-replacements-never-publish-a-final-anchor
  (with-issued
    (fn [{:keys [context values refs world] :as base}]
      (let [[world capability] (capture base)
            [world invalid] (add-definition world refs "artifactInvalid" "MissingArtifactBody")]
        (is (thrown? Exception (delta/verify-artifact-extension context world (conj values invalid) capability {})))
        (is (thrown? Exception (delta/verify-artifact-extension context world (subvec values 1) capability {})))
        (is (thrown-with-msg? Exception #"issued live"
              (delta/verify-artifact-extension context world values {:fabricated true} {})))))))

(deftest initial-artifact-association-preserves-prior-and-child-alias-owner-credits
  (doseq [alias? [false true]]
    (with-issued
      (fn [{:keys [world context values admission]}]
        (let [before world [world env] (environment world values)
              returned-root (atom nil) token (Object.)
              context (update context :invoke
                              (fn [invoke]
                                (fn [world target args]
                                  (cond
                                    (= target (:root module/helpers))
                                    (let [[world root] (invoke world target args)]
                                      (reset! returned-root root) [world root])
                                    (= target (:quot-init? module/helpers))
                                    (let [world (cond-> world alias? (m/retain @returned-root 1))]
                                      (throw (ex-info "injected artifact association quotient failure"
                                                      {:checkpoint world :checkpoint-session token
                                                       :temporary-owners (if alias? [@returned-root] [])})))
                                    :else (invoke world target args)))))
              error (try (artifact/associate-admitted-progress context world env module/helpers admission) nil
                         (catch clojure.lang.ExceptionInfo error error))
              {:keys [checkpoint association-temporary-owners temporary-owners checkpoint-session]} (ex-data error)
              [root array] association-temporary-owners]
          (is (some? error))
          (is (identical? token checkpoint-session))
          (is (= 2 (count association-temporary-owners)))
          (is (= @returned-root root))
          (is (= (if alias? [root] []) temporary-owners))
          (is (= (if alias? 3 2) (:rc (m/node checkpoint root))))
          (is (= 1 (:rc (m/node checkpoint array))))
          (is (nil? (get-in checkpoint [:kernel-environments (:id root)])))
          (let [cleaned (reduce #(m/release %1 %2 1) checkpoint
                                (concat temporary-owners association-temporary-owners [env]))]
            (is (= (:heap before) (:heap cleaned)))))))))

(deftest artifact-publication-validates-original-java-guards-after-the-last-helper-return
  (with-issued
    (fn [{:keys [world context values admission projection]}]
      (let [before world [world env] (environment world values)
            ^ConstantInfo ci (get (:projected projection) (name/from-string "aliasA"))
            original (.value ci)
            calls (atom 0)
            context (update context :invoke
                            (fn [invoke]
                              (fn [world target args]
                                (let [[world value] (invoke world target args)]
                                  (when (= target (:constant-map module/helpers))
                                    (swap! calls inc) (set! (.value ci) (.type ci)))
                                  [world value]))))]
        (try
          (let [error (try (artifact/associate-admitted-progress context world env module/helpers admission) nil
                           (catch clojure.lang.ExceptionInfo error error))
                {:keys [checkpoint association-temporary-owners]} (ex-data error)
                [root map-root] association-temporary-owners]
            (is (some? error))
            (is (= 1 @calls))
            (is (= 2 (count association-temporary-owners)))
            (is (= 2 (:rc (m/node checkpoint root))))
            (is (= 2 (:rc (m/node checkpoint map-root))))
            (is (nil? (get-in checkpoint [:kernel-environments (:id root)])))
            (let [cleaned (reduce #(m/release %1 %2 1) checkpoint (conj association-temporary-owners env))]
              (is (= (:heap before) (:heap cleaned)))))
          (finally (set! (.value ci) original)))))))

(deftest added-proof-and-assumption-policy-remain-kernel-enforced
  (with-issued
    (fn [{:keys [context values refs] :as base}]
      (let [[world capability] (capture base)
            cv (first (:fields (m/node world (fixture/payload world (get refs "A")))))
            type (nth (:fields (m/node world cv)) 2)
            [world bad] (guest/declaration world "artifactBadProof" type type)
            [world axiom] (guest/axiom-declaration world "artifactNewAxiom" type)
            [world unsafe] (add-definition world refs "artifactNewUnsafe" "aliasA")
            world (guest/scalar! world (fixture/payload world unsafe) 0 "uint8" 0)
            error (try (delta/verify-artifact-extension context world (conj values bad) capability {}) nil
                       (catch clojure.lang.ExceptionInfo error error))]
        (is (= :check (first (:stage (ex-data error)))))
        (is (thrown-with-msg? Exception #"New axiom"
              (delta/verify-artifact-extension context world (conj values axiom) capability {})))
        (is (= 18 (count (:constants (delta/verify-artifact-extension context world (conj values axiom)
                                                                   capability {:allow-axioms? true})))))
        (is (thrown-with-msg? Exception #"unsafe/partial"
              (delta/verify-artifact-extension context world (conj values unsafe) capability {})))
        (is (= 18 (count (:constants (delta/verify-artifact-extension context world (conj values unsafe)
                                                                   capability {:allow-unsafe? true})))))))))
