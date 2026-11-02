(ns java-ir-expr-loose-entry-checks
 "Borrowed PAP/Host admission and explicit constructor-policy boundary."
 (:require [clojure.test :refer [deftest is run-tests]]
  [java-ir-baseline :as j] [java-ir-baseline-checks :as c]
  [java-ir-expr-loose-checks :as loose] [java-ir-sync-task-checks :as sync]
  [java-ir-host-checks :as h] [java-ir-generation-checks :as g]
  [java-ir-continuation-checks :as k]))
(def ^:dynamic *basis* nil)
(defn context [options] (binding [loose/*basis* *basis*] (loose/context options)))

(deftest lower-identity-still-requires-the-active-configured-constructor-policy
 (let [{:keys [ctx]} (context {}) e (j/machine ctx) input (loose/bvar! ctx e 0)
       before (k/counters ctx e)]
  (is (g/bad? #(loose/lower! ctx e input 0 0)))
  (is (= before (k/counters ctx e))) (is (= 1 (c/rc ctx input)))
  (is (= "failed" (j/phase ctx e)))))

(deftest static-pap-and-dynamic-hostreply-fences-reject-both-borrowed-natives
 (doseq [raw ["Lean.Expr.hasLooseBVar" "Lean.Expr.lowerLooseBVars"]]
  (let [n (get-in (loose/named raw) ["row" "name"])
        bad (c/decl "model-invalid-loose-pap" [] "object"
             (c/let-ir 1 "object" {:pap {:c n :ys []}} (c/ret 1)))]
   (is (g/bad? #(context {:rows [bad]}))))
  (let [spec (h/spec "loose_reply" [] [] "object")
        {:keys [ctx] :as lab} (context {:rows [(h/ext "loose-reply" spec)] :host-specs [spec]})
        e (loose/machine lab) closure (j/make-closure! ctx e (str raw "._boxed") [])
        program (h/private-value e "program") functions (h/private-value program "functions")
        field (doto (.getDeclaredField (class closure) "closure") (.setAccessible true))
        original (.get field closure) target (aget ^objects functions (j/function-id ctx raw))]
   ;; MODEL changes only a private closure target; no API admits this borrowed
   ;; closure. The Host reply must reject it before claiming the pending reply.
   (.set field closure target)
   (j/start! ctx e "loose-reply" [])
   (let [request (j/host-request ctx e) before (k/counters ctx e)]
    (try
     (is (g/bad? #(j/resume-host! ctx e request closure)))
     (is (identical? request (j/host-request ctx e)))
     (is (= "host-call" (j/phase ctx e)))
     (is (= before (k/counters ctx e))) (is (= 1 (c/rc ctx closure)))
     (finally (.set field closure original)))
    (j/resume-host! ctx e request 0) (is (= 0 (sync/finish! ctx e)))
    (sync/release! ctx e closure) (sync/close! ctx e)))))

(defn check! [basis] (binding [*basis* basis] (run-tests 'java-ir-expr-loose-entry-checks)))
