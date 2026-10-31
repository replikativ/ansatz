(ns artifact-declaration-adapter-v4-models-v1
  "Adapter branch models with real kernel Env/CI/snapshots. No guest capability admission."
  (:require [clojure.test :refer [deftest is run-tests]]
            [artifact-checked-declaration-adapter-v4 :as adapter]
            [java-matched-artifact-base-v1 :as base]
            [java-ir-baseline :as j]
            [ansatz.research.ir.kernel-projection :as projection]
            [prototype.kernel-bridge :as bridge]
            [prototype.kernel-projection-snapshot :as snapshot])
  (:import [ansatz.kernel Env Name Level Expr ConstantInfo TypeChecker]
           [java.util LinkedHashMap]))
(defn seam [s] (or (ns-resolve 'artifact-checked-declaration-adapter-v4 s)
                   (throw (ex-info "Missing adapter seam" {:symbol s}))))
(defn message [f] (try (f) nil (catch Throwable t (.getMessage t))))
(defn slot [v status] (object-array [v status]))
(defn- model-session [fields]
  ;; Private seam fixtures must carry the same journals as new real sessions.
  (merge {:events (atom []) :base-operation (atom nil)
          :versions (atom []) :options {:max-declarations 16}} fields))
(defn ci [s]
  (ConstantInfo/mkAxiom (Name/fromString s) (object-array [])
                       (Expr/sort (Level/succ Level/ZERO_LEVEL) false) false))
(defn local-entry [^Env env ^ConstantInfo c]
  {:env env :segments [(snapshot/snapshot-segment {(.name c) c})]
   :payloads {(.name c) {:kind :axiom :payload (Object.)}}})
(defn guarded [f]
  ;; Model only the opaque base controller's callback boundary. The actual
  ;; Env, ConstantInfo, snapshot and adapter checks execute unchanged.
  (let [live (atom true) domain (atom #{}) calls (atom 0) token (Object.)]
    (with-redefs [base/guard! (fn [_] (when-not @live (throw (ex-info "model base lease closed" {}))))
                  base/with-version! (fn [_ e callback]
                                       (swap! calls inc)
                                       (when-not @live (throw (ex-info "model base lease closed" {})))
                                       (callback e))
                  base/domain-names (fn [_] @domain)]
      (f {:matched-base token :live live :domain domain :guard-calls calls}))))

(deftest equal-shape-replacement-is-rejected-for-current-and-historical-entries
  (guarded
    (fn [{:keys [matched-base]}]
      (let [a (ci "ModelIdentity") b (ci "ModelIdentity")
            original (TypeChecker/checkConstant (.enableQuot (Env.)) a 1000000)
            replacement (TypeChecker/checkConstant (.enableQuot (Env.)) b 1000000)
            entry (local-entry original a) session (model-session {:matched-base matched-base})]
        (is (not (identical? a b)))
        (is (nil? ((seam 'validate-local-view!) session entry)))
        ;; Identical checking shape and typed Name do not authenticate member identity.
        (is (re-find #"not the actual Env member"
                     (message #((seam 'validate-local-view!) session (assoc entry :env replacement)))))
        (let [source (Object.) owner #(slot (Object.) :association-owned)
              historical (merge entry {:source source :quot true :base-token matched-base :base-basis :trusted-artifact
                                       :kernel-root (owner) :constant-map (owner)})
              empty-version (assoc historical :env (.enableQuot (Env.)) :segments [] :payloads {})
              s {:source source :matched-base matched-base :engine (Object.) :versions (atom [historical empty-version])}]
          (with-redefs-fn {(seam 'invoke1) (fn [& _] nil)}
            (fn []
               (is (nil? ((seam 'validate-versions!) s)))
               (swap! (:versions s) assoc 0 (assoc historical :env replacement))
               (is (re-find #"not the actual Env member" (message #((seam 'validate-versions!) s))))
               (swap! (:versions s) assoc 0 historical)
               (is (nil? ((seam 'validate-versions!) s))))))))))

(deftest local-domain-rejects-base-intersection-and-overlapping-segments
  (guarded
    (fn [{:keys [matched-base domain]}]
      (let [a (ci "ModelDomain") e (local-entry (.addConstant (.enableQuot (Env.)) a) a)
            s {:matched-base matched-base}]
        (is (nil? ((seam 'validate-local-view!) s e)))
        (reset! domain #{(.name a)})
        (is (re-find #"overlay domain differs" (message #((seam 'validate-local-view!) s e))))
        (reset! domain #{})
        (is (re-find #"Overlapping local snapshot segments"
                     (message #((seam 'validate-local-view!) s (update e :segments conj (first (:segments e)))))))
        (is (re-find #"overlay domain differs"
                     (message #((seam 'validate-local-view!) s (assoc e :payloads {})))))))))

(deftest actual-mutable-ci-and-parameter-array-snapshots-reject-and-recover
  (guarded
    (fn [{:keys [matched-base]}]
      (let [u (Name/fromString "u") v (Name/fromString "v")
            a (ConstantInfo/mkAxiom (Name/fromString "ModelMutable") (object-array [u])
                                    (Expr/sort (Level/succ Level/ZERO_LEVEL) false) false)
            e (local-entry (.addConstant (.enableQuot (Env.)) a) a) s {:matched-base matched-base}]
        (is (nil? ((seam 'validate-local-view!) s e)))
        (set! (.-isUnsafe a) true)
        (try (is (re-find #"checking shape changed" (message #((seam 'validate-local-view!) s e))))
             (finally (set! (.-isUnsafe a) false)))
        (aset ^objects (.levelParams a) 0 v)
        (try (is (re-find #"checking shape changed" (message #((seam 'validate-local-view!) s e))))
             (finally (aset ^objects (.levelParams a) 0 u)))
        (is (nil? ((seam 'validate-local-view!) s e)))))))

(deftest closed-base-lease-blocks-even-local-only-operation-before-snapshot-or-external-lookup
  (guarded
    (fn [{:keys [matched-base live guard-calls]}]
      (let [external (atom 0) snapshots (atom 0) a (ci "ModelClosed")
            env (.addConstant (.withExternalLookupUncached (.enableQuot (Env.))
                     (fn [_] (swap! external inc) nil) 2314) a)
            e (local-entry env a) session (model-session {:matched-base matched-base})]
        ;; addConstant itself consulted the real external lookup once.
        (reset! external 0) (reset! live false)
        (with-redefs [snapshot/validate-segment-values (fn [_] (swap! snapshots inc))]
          (is (re-find #"lease closed" (message #((seam 'validate-local-view!) session e))))
          (is (zero? @snapshots)) (is (zero? @external)) (is (= 1 @guard-calls)))))))

(deftest wrong-session-crossbinding-rejects-before-source-retain-checker-or-projection-work
  ;; This tests adapter sequencing, not authenticity of the real opaque base cap.
  (let [engine (Object.) source (Object.) run (Object.) token (Object.) calls (atom [])
        no-op (fn [& _] nil)
        authority (merge (zipmap [:begin-request! :artifact-environment! :checked-environment! :checked-constants!
                                 :diagnostics-disabled! :finish-request! :close!] (repeat no-op))
                         {:check-source! (fn [& _] (swap! calls conj :source))
                          :layout-receipt-sha256 (apply str (repeat 64 "a")) :finalized-run run})
        options {:allow-axioms? true :allow-theorems? false :allow-definitions? false :fuel 1000000
                 :projection-limits (fn [] {}) :max-declarations 4}]
    (with-redefs [base/assert-session! (fn [b e s r]
                                       (swap! calls conj :crossbinding)
                                       (when-not (and (identical? b token) (identical? e engine)
                                                      (identical? s source) (identical? r run))
                                         (throw (ex-info "model wrong session" {}))))
                  base/guard! (fn [_] (swap! calls conj :guard))
                  j/retain! (fn [& _] (swap! calls conj :retain))
                  projection/open-projector (fn [& _] (swap! calls conj :projection))
                  bridge/admit-axiom (fn [& _] (swap! calls conj :checker))]
      (doseq [[e s a b] [[(Object.) source authority token] [engine (Object.) authority token]
                         [engine source (assoc authority :finalized-run (Object.)) token]
                         [engine source authority (Object.)]]]
        (reset! calls [])
        (is (re-find #"wrong session" (message #(adapter/open-session {} e {} s a b options))))
        (is (= [:crossbinding] @calls)))
      (reset! calls [])
      (let [s (adapter/open-session {} engine {} source authority token options)]
        (is (= [:crossbinding :guard :source] @calls))
        (is (= :idle @(:phase s))) (is (zero? @(:published-count s))) (is (empty? @(:versions s)))))))

(deftest branch-from-seed-after-v1-uses-local-count-but-monotonic-publication-id
  (guarded
    (fn [{:keys [matched-base]}]
      (let [source (Object.) engine (Object.) receipt (apply str (repeat 64 "b"))
            external-calls (atom 0)
            ;; The actual Java Env advertises 2314 external declarations and zero locals.
            base-env (.withExternalLookupUncached (.enableQuot (Env.)) (fn [_] (swap! external-calls inc) nil) 2314)
            authority {:layout-receipt-sha256 receipt :check-source! (fn [& _] nil)
                       :checked-environment! (fn [_ guest k m _ _]
                                              {:kernel-root k :constant-map m :guest-environment guest :quot true
                                               :source-binding source :layout-receipt-sha256 receipt})
                       :diagnostics-disabled! (fn [_ k _] {:kernel-root k :source-binding source
                                                                           :layout-receipt-sha256 receipt :enabled 0})}
            session (model-session {:source source :thread (Thread/currentThread) :engine engine :matched-base matched-base :basis {}
                     :authority authority :options {:max-declarations 4 :fuel 1000000 :projection-limits (fn [] {})}
                     :versions (atom []) :published-count (atom 0)})
            seed-owners (doto (LinkedHashMap.) (.put :K0 (slot (Object.) :owned)) (.put :M0 (slot (Object.) :owned)))
            seed-inv (atom {:owners seed-owners})]
        (is (= 2314 (.size base-env)))
        (is (empty? (.allConstants base-env)))
        (with-redefs [base/with-env! (fn [_ callback] (callback base-env))]
          ((seam 'retain-seed-version!) session seed-inv {:origin :model-artifact-witness}))
        (let [seed (first @(:versions session)) a (ci "ModelBranchA") b (ci "ModelBranchB")
              v1 (merge seed (local-entry (TypeChecker/checkConstant base-env a 1000000) a)
                        {:id 1 :parent 0 :kernel-root (slot (Object.) :association-owned)
                         :constant-map (slot (Object.) :association-owned)})
              owners (doto (LinkedHashMap.)
                       (.put :K0 (slot (Object.) :owned)) (.put :M0 (slot (aget ^objects (:constant-map seed) 0) :owned))
                       (.put :empty0 (slot 0 :owned)) (.put :K1 (slot (Object.) :owned))
                       (.put :M1 (slot (Object.) :owned)) (.put :reply (slot (Object.) :owned)))
              inv (atom {:input-env (Object.) :owners owners :tokens {} :declaration (Object.)
                         :payload (Object.) :descriptor {:kind :axiom :declaration-projection :axiom-declaration}})
              closes (atom 0) checker-calls (atom 0)]
          (reset! (:versions session) [seed v1]) (reset! (:published-count session) 1)
          (with-redefs-fn
            {(seam 'invoke1) (fn [& _] nil)
             #'projection/open-projector (fn [& _] {:world :model :projector :model :close! #(swap! closes inc)})
             #'bridge/project-with-stats (fn [& _] {:value b})
             ;; Use the actual Java strict checker; only the guest projection transport is modeled.
             #'bridge/admit-axiom (fn [_ env _ fuel _]
                                    (swap! checker-calls inc)
                                    {:env (TypeChecker/checkConstant env b fuel) :constant b})
             (seam 'validate-readback!) (fn [& _] nil)}
            (fn []
               ((seam 'check-java!) session inv)
               (is (identical? seed (:base @inv)))
               (is (= 1 @checker-calls @closes))
               (is (= 1 (count (.allConstants ^Env (get-in @inv [:candidate :env])))))
               (is (identical? b (.lookupLocal ^Env (get-in @inv [:candidate :env]) (.name b))))
               (is (nil? (.lookupLocal ^Env (get-in @inv [:candidate :env]) (.name a))))
               ((seam 'commit!) session inv)
               (let [v2 (last @(:versions session))]
                 (is (= [0 1 2] (mapv :id @(:versions session))))
                 (is (= 0 (:parent v2))) (is (= 2 @(:published-count session)))
                 (is (= 1 (count (:payloads v2))))
                 (is (= :association-owned (aget ^objects (:kernel-root v2) 1)))
                 (is (= :association-owned (aget ^objects (:constant-map v2) 1)))
                 (is (not-any? #{:K1 :M1} (:cleanup @inv)))))))))))

(deftest retain-release-and-reply-exceptions-preserve-occurrence-disposition
  ;; The ownership protocol is unchanged v3 code. These are controller models;
  ;; the real engine's resumable release and HostCompletion are not manufactured.
  (let [owners (LinkedHashMap.) inv (atom {:owners owners}) session (model-session {:basis {} :engine (Object.)})]
    (with-redefs [j/retain! (fn [& _] (throw (ex-info "retain rejected" {})))]
      (is (re-find #"retain rejected" (message #((seam 'retain-into!) session inv :anchor (Object.)))))
      (is (= :unclaimed (aget ^objects (.get owners :anchor) 1)))))
  (let [owners (doto (LinkedHashMap.) (.put :temporary (slot (Object.) :owned)))
        inv (atom {:owners owners :cleanup [:temporary] :cleanup-index 0})
        session (model-session {:basis {} :engine (Object.)})]
    (with-redefs [j/host-owned-argument (fn [& _] :model-owned-description)
                  j/start-host-release! (fn [& _] (throw (ex-info "release publication rejected" {})))]
      (is (re-find #"publication rejected" (message #((seam 'cleanup-next!) session inv)))))
      (is (= :owned (aget ^objects (.get owners :temporary) 1)))
      (is (= 1 (:cleanup-index @inv)))
      (is (nil? (aget ^objects (get-in @inv [:operation :token]) 0))))
  (let [reply (slot (Object.) :owned) outer (Object.) owners (doto (LinkedHashMap.) (.put :reply reply))
        inv (atom {:owners owners :outer outer}) calls (atom [])
        session (model-session {:basis {} :engine (Object.) :source (Object.) :thread (Thread/currentThread)
                 :authority {:check-source! (fn [& _] nil)
                             :finish-request! (fn [& _] (swap! calls conj :finish) (throw (ex-info "finish rejected" {})))}
                 :versions (atom [{:id 1 :parent 0}])
                 :phase (atom :active) :invocation (atom inv) :last-request (atom nil)})]
    (with-redefs [j/resume-host! (fn [& _] (swap! calls conj :resume))]
      (is (re-find #"finish rejected" (message #((seam 'reply!) session inv)))))
      (is (= [:resume :finish] @calls))
      (is (= :transferred (aget ^objects reply 1)))
      (is (= :active @(:phase session))) (is (identical? inv @(:invocation session)))))
(defn check! [] (run-tests 'artifact-declaration-adapter-v4-models-v1))
