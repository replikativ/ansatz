(ns java-ir-expr-transform-policy-checks
 (:require [clojure.test :refer [deftest is run-tests]] [java-ir-baseline :as j]
   [java-ir-expr-machinery-checks :as expr] [java-ir-sync-task-checks :as sync]
   [java-ir-host-checks :as h] [java-ir-baseline-checks :as c]
   [java-ir-continuation-checks :as k]))
(def ^:dynamic *basis*)
(defn fixture [options] (binding [expr/*basis* *basis*] (expr/context options)))
(defn policy [{:keys [ctx headers]}] (j/expr-transform-policy ctx (mapv headers expr/roles)))
(deftest configuration-is-idle-once-lazy-and-inherited-by-fork
 (let [{:keys [ctx] :as lab} (fixture {:defer (set expr/roles)}) e (j/machine ctx) p (policy lab)
       counters (k/counters ctx e)]
   (j/configure-expr-transforms! ctx e p)
   (is (= counters (k/counters ctx e))) (is (= "idle" (j/phase ctx e)))
   (is (nil? (j/code-request ctx e))) (is (identical? p (h/private-value e "exprTransformPolicy")))
   (is (re-find #"already configured" (c/failure #(j/configure-expr-transforms! ctx e p))))
   (let [{:keys [engine]} (j/fork! ctx e [])]
     (is (identical? p (h/private-value engine "exprTransformPolicy")))
     (sync/close! ctx engine))
   (sync/close! ctx e)))
(deftest foreign-program-policy-fails-without-poisoning-configuration
 (let [a (fixture {}) {:keys [ctx] :as b} (fixture {}) e (j/machine ctx) before (k/counters ctx e)]
   (is (some? (c/failure #(j/configure-expr-transforms! ctx e (policy a)))))
   (is (nil? (h/private-value e "exprTransformPolicy")))
   (is (= before (k/counters ctx e)))
   (j/configure-expr-transforms! ctx e (policy b))
   (is (some? (h/private-value e "exprTransformPolicy")))
   (sync/close! ctx e)))
(deftest running-configuration-rejects-before-policy-mutation
 (let [{:keys [ctx] :as lab} (fixture {}) e (j/machine ctx) p (policy lab)]
   (j/start! ctx e "model-setup-Lean.Expr.bvar._override" [0])
   (let [before (k/counters ctx e)]
     (is (re-find #"open idle" (c/failure #(j/configure-expr-transforms! ctx e p))))
     (is (= before (k/counters ctx e))) (is (nil? (h/private-value e "exprTransformPolicy"))))
   (let [v (sync/finish! ctx e)] (sync/release! ctx e v))
   (j/configure-expr-transforms! ctx e p) (sync/close! ctx e)))
(deftest inactive-runtime-cannot-configure-native-expression-transformations
 (let [{:keys [ctx] :as lab} (fixture {:inactive true}) e (j/machine ctx) before (k/counters ctx e)]
   (is (re-find #"active runtime" (c/failure #(j/configure-expr-transforms! ctx e (policy lab)))))
   (is (= before (k/counters ctx e))) (is (nil? (h/private-value e "exprTransformPolicy")))
   (j/close! ctx e)))
(defn check! [basis] (binding [*basis* basis] (run-tests 'java-ir-expr-transform-policy-checks)))

(deftest each-native-profile-entry-revalidates-current-constructor-functions
 ;; MODEL reflective Program tampering; this is not an allowed guest mutation.
 (let [{:keys [ctx] :as lab} (fixture {}) e (j/machine ctx) p (policy lab)
       functions ^objects (h/private-value (:program ctx) "functions")
       exports ^objects (h/private-value (:program ctx) "guestExports")
       id (j/function-id ctx "Lean.Expr.bvar._override")
       other (aget functions (j/function-id ctx "Lean.Expr.sort._override"))
       f (aget functions id)
       m (doto (.getDeclaredMethod ^Class (:class ctx) "exprTransformsProfile" (into-array Class [(class f)])) (.setAccessible true))
       enter #(.invoke m e (object-array [f]))]
   (j/configure-expr-transforms! ctx e p)
   (is (some? (enter)))
   (let [before (k/counters ctx e)]
     (aset exports id other)
     (try
       (is (re-find #"current exact ordinary" (c/failure enter)))
       (is (= before (k/counters ctx e)))
       (finally (aset exports id nil))))
   (is (some? (enter))) (sync/close! ctx e)))
