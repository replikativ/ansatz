(ns java-ir-initializer-publication-checks
  "Model tests for the bounded publication protocol; no native startup evidence."
  (:require [clojure.test :refer [deftest is run-tests]]
            [java-ir-baseline :as j] [java-ir-baseline-checks :as c]
            [java-ir-extern-checks :as x] [java-ir-generation-checks :as g]
            [java-ir-header-checks :as h]))
(def ^:dynamic *basis* nil)
(defn method [engine label types args]
  (.invoke (.getMethod (class engine) label (into-array Class types)) engine (object-array args)))
(defn begin! [engine global action]
  (method engine "startInitializer" [(class global) (class action)] [global action]))
(defn complete! [engine] (method engine "completeInitializer" [] []))
(defn finish! [engine] (method engine "finishInitialization" [] []))
(defn pending [engine] (g/field engine "result"))
(defn fields [ctx value] (.get ^java.lang.reflect.Field (:fields ctx) value))
(defn body [tag]
  (c/let-ir 2 "object" (c/ctor 7 [] 0)
    (c/let-ir 3 "object" (c/ctor tag [(c/v 2)] 0) (c/ret 3))))
(defn lab
  ([] (lab (body 0) {} {} false))
  ([body global-edit action-edit foreign?]
   (let [base (j/prepare-host-program *basis* [] [])
         source (j/source-binding base {:model "initializer-publication"})
         other (if foreign? (j/source-binding base (Object.)) source)
         global-row (merge (assoc (c/decl "global" [] "object" ["unreachable"])
                           :runtime {:role "initialized" :initializer (c/name-ir "init-global")}) global-edit)
         action-row (update (c/decl "init-global" [(c/p 1 "void")] "object"
                               (if (= "uint8" (:type action-edit))
                                 (c/let-ir 2 "uint8" (c/lit 0) (c/ret 2)) body))
                            :ir update :fdecl merge action-edit)
         global (h/header source global-row) action (h/header other action-row)
         registered (j/register-headers base [global action])
         prepared (if (= "uint8" (:type action-edit)) registered
                    (j/materialize-body registered action (first (x/raw [action-row])) []))
         ctx (assoc prepared :explicit true :initializing true)]
     {:ctx ctx :global global :action action})))
(defn run! [ctx e]
  (loop [left 100]
    (when (zero? left) (throw (ex-info "Initializer model exceeded bound" {})))
    (when-not (j/advance! ctx e 10) (recur (dec left)))))

(deftest publishes-the-actual-persistent-payload-and-consumes-only-wrapper-credit
  (let [{:keys [ctx global action]} (lab) e (j/machine ctx)]
    (try
      (begin! e global action)
      (is (g/bad? #(complete! e)))
      (is (g/bad? #(j/start! ctx e "global" [])))
      (is (g/bad? #(j/fork! ctx e [])))
      (is (g/bad? #(finish! e)))
      (run! ctx e)
      (let [wrapper (pending e) payload (aget (fields ctx wrapper) 0)
            before (c/rc ctx payload)]
        (is (= 1 before))
        (is (g/bad? #(j/take-result! ctx e)))
        (let [status (complete! e)]
          (is (= 0 (c/rc ctx payload)))
          (is (nil? (aget (fields ctx wrapper) 0)))
          (is (true? (g/field wrapper "dead")))
          (is (identical? payload (j/call ctx e "global" [])))
          (is (= 0 (c/rc ctx payload)))
          (j/release! ctx e status))
        (is (g/bad? #(complete! e)))
        (is (g/bad? #(begin! e global action)))
        (finish! e)
        (is (false? (method e "isInitializing" [] []))))
      (finally (j/close! ctx e)))))

(deftest shared-result-wrapper-loses-one-credit-without-clearing-surviving-alias
  (let [{:keys [ctx global action]} (lab) e (j/machine ctx)]
    (try
      (begin! e global action) (run! ctx e)
      (let [wrapper (pending e) payload (aget (fields ctx wrapper) 0)]
        (j/retain! ctx e wrapper)
        (let [status (complete! e)]
          (is (= 1 (c/rc ctx wrapper)))
          (is (identical? payload (aget (fields ctx wrapper) 0)))
          (is (= 0 (c/rc ctx payload)))
          (j/release! ctx e status) (j/release! ctx e wrapper)))
      (finally (j/close! ctx e)))))

(deftest rejects-pair-name-binding-and-action-abi-before-claiming-an-attempt
  (doseq [[global-edit action-edit foreign?]
          [[{:runtime {:role "initialized" :initializer (c/name-ir "different")}} {} false]
           [{} {} true]
           [{} {:xs [(c/p 1 "object")]} false]
           [{} {:xs [(assoc (c/p 1 "void") :borrow true)]} false]
           [{} {:xs []} false]
           [{} {:type "uint8"} false]]]
    (let [{:keys [ctx global action]} (lab (body 0) global-edit action-edit foreign?) e (j/machine ctx)]
      (try
        (is (g/bad? #(begin! e global action)))
        (is (= "idle" (j/phase ctx e)))
        (is (nil? (pending e)))
        (finally (j/close! ctx e))))))

(deftest post-boot-engine-cannot-enter-startup
  (let [{:keys [ctx global action]} (lab) ctx (assoc ctx :initializing false) e (j/machine ctx)]
    (try (is (g/bad? #(begin! e global action)))
         (is (= "idle" (j/phase ctx e)))
         (finally (j/close! ctx e)))))

(deftest io-error-transfers-the-original-result-without-publishing-or-replay
  (let [{:keys [ctx global action]} (lab (body 1) {} {} false) e (j/machine ctx)]
    (try
      (begin! e global action) (run! ctx e)
      (let [wrapper (pending e) error (aget (fields ctx wrapper) 0)]
        (is (identical? wrapper (complete! e)))
        (is (= 1 (c/rc ctx wrapper))) (is (= 1 (c/rc ctx error)))
        (is (g/bad? #(j/start! ctx e "global" [])))
        (is (g/bad? #(begin! e global action)))
        (is (g/bad? #(finish! e)))
        (j/release! ctx e wrapper))
      (finally (j/close! ctx e)))))

(deftest completion-preflight-is-atomic-and-keeps-the-owned-result-for-cleanup
  (doseq [mode [:interrupt :bad-payload :bad-wrapper]]
    (let [{:keys [ctx global action]} (lab) e (j/machine ctx)]
      (try
        (begin! e global action) (run! ctx e)
        (let [wrapper (pending e) payload (aget (fields ctx wrapper) 0)]
          (case mode
            :interrupt (.interrupt (Thread/currentThread))
            :bad-payload (.setInt ^java.lang.reflect.Field (:rc ctx) payload -1)
            :bad-wrapper (.setInt ^java.lang.reflect.Field (:tag ctx) wrapper 3))
          (try
            (is (g/bad? #(complete! e)))
            (finally
              (Thread/interrupted)
              (.setInt ^java.lang.reflect.Field (:rc ctx) payload 1)
              (.setInt ^java.lang.reflect.Field (:tag ctx) wrapper 0)))
          (is (identical? wrapper (pending e)))
          (is (= 1 (c/rc ctx payload)))
          (is (= 1 (c/rc ctx wrapper)))
          (is (false? (aget ^booleans (g/field e "constantReady") (j/function-id ctx "global")))))
        (finally (j/close! ctx e))))))

(deftest unregistered-header-identity-cannot-authorize-publication
  (let [{:keys [ctx global action]} (lab) e (j/machine ctx)
        source (method global "source" [] [])
        duplicate (h/header source (c/decl "init-global" [(c/p 1 "void")] "object" (body 0)))]
    (try
      (is (g/bad? #(begin! e global duplicate)))
      (is (= "idle" (j/phase ctx e)))
      ;; The rejected pair did not claim the actual pair's attempt.
      (begin! e global action) (run! ctx e)
      (j/release! ctx e (complete! e))
      (finally (j/close! ctx e)))))

(deftest execution-failure-remains-terminal-without-result-or-global-publication
  (let [{:keys [ctx global action]} (lab ["unreachable"] {} {} false) e (j/machine ctx)]
    (begin! e global action)
    (is (g/bad? #(run! ctx e)))
    (is (= "failed" (j/phase ctx e)))
    (is (g/bad? #(complete! e)))
    (is (g/bad? #(finish! e)))
    (is (g/bad? #(begin! e global action)))
    (is (false? (aget ^booleans (g/field e "constantReady") (j/function-id ctx "global"))))
    ;; Existing explicit-engine failure semantics retain diagnostic frames;
    ;; this protocol deliberately introduces no unsafe frame-discard operation.
    (is (g/bad? #(j/close! ctx e)))))

(defn check! [basis] (binding [*basis* basis] (run-tests 'java-ir-initializer-publication-checks)))
