(ns prototype.source-reconstruction-test
  "Source-derived phase-order regressions with modeled frontend/finalizer data.
   Actual staged controls, raw callbacks and complementary evalConst witness
   transport run. No test establishes a genuine imported-macro failure."
  (:require [clojure.test :refer [deftest is]]
            [prototype.resident-init-import-test :as staged]
            [prototype.resident-init-prefix :as control]
            [prototype.resident-frontend :as resident]
            [prototype.source-import :as source]
            [prototype.source-import-test :as publication]
            [prototype.eval-const :as eval]
            [prototype.eval-const-resolution-test :as witness-model]
            [prototype.raw-interop :as raw]
            [prototype.machine :as m]))

(def local-name ["answer"])
(def local-row {:kind "decl" :name local-name :sourceLocal true :sourceModule publication/module
                :ir {:fdecl {:f local-name :xs [] :type "object" :body []}}})

(deftest imported-source-transition-before-finalizer-completion-has-no-final-receipt
  (doseq [backend [:reference :mutable :jvm]]
    (let [trusted-functions (atom nil) observed (atom nil)
          callback
          (fn [context world values]
            ;; Model finalizeImport's already-built native+A constant map before
            ;; extension reconstruction returns the final IO Environment.
            (let [[world io] (publication/final-result world values)
                  environment (first (:fields (m/node world io)))
                  root (first (:fields (m/node world environment)))
                  unit (get-in world [:eval-const-authorizations :units publication/digest])
                  before world
                  [world authorized?]
                  (source/authorize-imported-row
                    world (assoc context :check-trusted-functions!
                                 (fn [world roots]
                                   (eval/validate-executables! world @trusted-functions roots)))
                    environment (assoc local-row :sourceLocal false) local-row unit)
                  evidence {:environment environment :root root :io-result io
                            :authorized? authorized? :constant-count (count values)
                            :source-entry (get-in world [:source-modules publication/module])
                            :before before :world world}]
              (reset! observed evidence)
              ((:checkpoint! context) world)
              ;; The unchanged completed-import profile rejects reconstruction.
              ;; No early kernel association or fake receipt is manufactured.
              (throw (ex-info "Model source transition requires a receipt before finalizer completion"
                              {:checkpoint world :source-reconstruction-ordering evidence}))))]
      (staged/with-fixture backend
        (fn [{:keys [context configuration finalizer-calls source] :as fixture}]
          (reset! trusted-functions (:trusted-functions configuration))
          (let [before (resident/snapshot context)
                {:keys [control]} (staged/prepare fixture)
                failure (staged/error-of #(staged/run-to-io! control))
                evidence @observed world (:world evidence)]
            (is (some? failure))
            (is (= 1 @finalizer-calls))
            (is (false? (:authorized? evidence)))
            (is (= 18 (:constant-count evidence)))
            (is (some? (:source-entry evidence)))
            (is (identical? (get-in world [:eval-const-authorizations :units publication/digest])
                            (get-in evidence [:source-entry :unit])))
            (is (empty? (get-in evidence [:source-entry :imports])))
            (is (nil? (get-in world [:kernel-environments (:id (:root evidence))])))
            (is (= (:heap (:before evidence)) (:heap world)))
            (is (= (:kernel-environments (:before evidence)) (:kernel-environments world)))
            (is (some? (:checkpoint-session (ex-data failure))))
            (is (identical? world (:checkpoint (ex-data failure))))
            (is (identical? failure (staged/error-of #(control/finish-import! control))))
            (is (identical? failure (staged/error-of #(staged/run-to-io! control))))
            (is (= 1 @finalizer-calls))
            (is (identical? before (resident/snapshot context)))
            (is (false? @(:closed source)))))
        :world-transform #(-> %
                              (assoc-in [:eval-const-authorizations :declarations local-name] local-row)
                              (assoc-in [:eval-const-authorizations :unit-digests local-name] publication/digest))
        :finalizer-hook callback))))

(deftest completed-target-checking-alone-does-not-replace-the-source-import-receipt
  (doseq [backend [:reference :mutable :jvm]]
    (staged/with-fixture backend
      (fn [{:keys [configuration context] :as fixture}]
        (let [{:keys [control]} (staged/prepare fixture)
              _ (staged/run-to-io! control)
              finished (control/finish-import! control)
              prepared (resident/snapshot (:context finished))
              world (:world prepared) session (:session prepared)
              environment (:environment prepared)
              unit (get-in world [:eval-const-authorizations :units publication/digest])
              invoke (fn [world helper args]
                       (let [result (raw/call session world helper args)]
                         [(:state result) (:value result)]))
              callback-context {:invoke invoke
                                :check-trusted-functions!
                                (fn [world roots]
                                  (eval/validate-executables! world (:trusted-functions configuration) roots))}
              without-receipt (assoc-in world [:source-modules publication/module :imports] {})
              [rejected accepted?] (source/authorize-imported-row
                                    without-receipt callback-context environment
                                    (assoc local-row :sourceLocal false) local-row unit)
              [authorized accepted-with-receipt?]
              (source/authorize-imported-row world callback-context environment
                                            (assoc local-row :sourceLocal false) local-row unit)]
          (is (false? accepted?))
          (is (true? accepted-with-receipt?))
          (is (seq (get-in world [:source-modules publication/module :imports])))
          (is (identical? (:kernel-environments world) (:kernel-environments without-receipt)))
          (is (= (:kernel-environments without-receipt) (:kernel-environments rejected)))
          (is (= (:heap world) (:heap rejected) (:heap authorized)))
          (is (identical? (:source-modules world) (:source-modules authorized)))
          (resident/close! (:context finished))))
      :world-transform #(-> %
                              (assoc-in [:eval-const-authorizations :declarations local-name] local-row)
                              (assoc-in [:eval-const-authorizations :unit-digests local-name] publication/digest)))))

(deftest real-evalconst-witness-transport-still-requires-explicit-source-authority
  ;; Complement the staged ordering model with actual witness parsing, closure
  ;; validation, raw callback scope and the unchanged authorization callback.
  ;; This compiler fixture has an admitted local unit, but no source publication
  ;; or checked import receipt; it must not relabel that local unit as imported.
  (doseq [backend [:reference :mutable :jvm]]
    (let [seen (atom [])
          callback (fn [world context environment selected local unit]
                     (swap! seen conj {:selected selected :local local :unit unit})
                     (source/authorize-imported-row world context environment selected local unit))
          input (witness-model/source-import-context backend callback identity)
          before (get-in input [:world :eval-const-authorizations])
          failure (staged/error-of #(witness-model/evaluate input))]
      (is (some? failure))
      (is (re-find #"Source import lacks checked module installation authority" (.getMessage failure)))
      (is (= 1 (count @seen)))
      (is (false? (get-in @seen [0 :selected :sourceLocal])))
      (is (true? (get-in @seen [0 :local :sourceLocal])))
      (is (= (get-in @seen [0 :selected :sourceModule])
             (get-in @seen [0 :unit :manifest :initializationPlan :module])))
      (is (identical? before (get-in (ex-data failure) [:checkpoint :eval-const-authorizations])))
      (is (some? (:checkpoint-session (ex-data failure)))))))
