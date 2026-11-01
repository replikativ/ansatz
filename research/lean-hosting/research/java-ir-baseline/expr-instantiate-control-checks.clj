(ns java-ir-expr-instantiate-control-checks
 "Policy and exceptional control supplement to the frozen fourteen value tests."
 (:require [clojure.test :refer [deftest is run-tests]]
  [java-ir-baseline :as j] [java-ir-baseline-checks :as c]
  [java-ir-expr-instantiate-checks :as pure] [java-ir-expr-machinery-checks :as expr]
  [java-ir-host-checks :as h] [java-ir-generation-checks :as g]
  [java-ir-sync-task-checks :as sync] [java-ir-continuation-checks :as k]))
(def ^:dynamic *basis* nil)
(defn context [options] (binding [pure/*basis* *basis*] (pure/context options)))

(deftest configured-policy-required-even-for-identity-and-inactive-entry
 (doseq [inactive? [false true]]
  (let [{:keys [ctx]} (context (if inactive? {:inactive true} {})) e (j/machine ctx)
        input (expr/bvar! ctx e 0) before (k/counters ctx e)]
   (is (g/bad? #(pure/apply! ctx e "liftLooseBVars" [input 0 0])))
   (is (= before (k/counters ctx e))) (is (= 1 (c/rc ctx input)))
   (is (not (pure/dead? input))))))

(deftest borrowed-pap-admission-rejects-all-six-before-publication
 (doseq [op pure/names]
  (let [raw (str "Lean.Expr." op)
        row (first (filter #(= raw (get % "label")) (pure/records)))
        pap (c/decl "invalid-pure-pap" [] "object"
             (c/let-ir 1 "object" {:pap {:c (get-in row ["row" "name"]) :ys []}} (c/ret 1)))]
   (is (g/bad? #(context {:rows [pap]}))))))

(deftest constructor-host-pause-fork-and-explicit-failure-retain-packets
 ;; MODEL observational prefix around the authentic original App constructor.
 (let [target (expr/roles 3)
       original (get-in (first (filter #(= target (get % "label")) (expr/records))) ["row" "ir" "fdecl" "body"])
       spec (h/spec "pure_constructor_event" ["object" "object"] [true true] "object")
       body (c/let-ir 100 "object" (c/fap "pure-constructor-event" [(c/v 1) (c/v 2)]) original)
       {:keys [ctx] :as lab} (context {:replacements {target body}
          :rows [(h/ext "pure-constructor-event" spec)] :host-specs [spec]})
       parent (pure/machine lab)
       input (expr/app! ctx parent (expr/bvar! ctx parent 0) (expr/bvar! ctx parent 1))
       values (pure/array! ctx parent [(expr/bvar! ctx parent 3)])]
  (j/start! ctx parent (pure/label "instantiate") [input values])
  (let [request (h/request! ctx parent) {child :engine} (j/fork! ctx parent [])]
   (is (= "pure_constructor_event" (j/request-value request "symbol")))
   (is (g/bad? #(j/resume-host! ctx child request 0)))
   (let [packet (h/private-value (pure/state child) "call")]
    (is (true? (h/private-value packet "entered")))
    (is (= [false false] (vec (h/private-value packet "owned")))))
   (j/fail-host! ctx child (j/host-request ctx child) (ex-info "deliberate constructor failure" {}))
   (is (= "failed" (j/phase ctx child))) (is (some? (pure/state child)))
   (is (not (pure/dead? input))) (is (not (pure/dead? values)))
   (j/resume-host! ctx parent request 0)
   (let [out (sync/finish! ctx parent)]
    (is (= [3 0] (mapv #(pure/index ctx %) (expr/fields ctx out))))
    (pure/release-close! ctx parent out)))))

(deftest live-offset-cache-fork-drains-each-result-owner
 (let [{:keys [ctx] :as lab} (context {}) parent (pure/machine lab)
       input (expr/bvar! ctx parent 0) values (pure/array! ctx parent [])]
  (j/retain! ctx parent input)
  (j/start! ctx parent (pure/label "instantiateRev") [input values])
  (pure/until! ctx parent #(some-> (pure/state parent) (h/private-value "liveCacheEntries") pos?))
  (let [{child :engine roots :roots} (j/fork! ctx parent [input]) ci (first roots)]
   (is (not (identical? input ci)))
   (doseq [[e outside] [[parent input] [child ci]]]
    (let [out (sync/finish! ctx e)]
     (is (not (identical? outside out))) (is (= 1 (c/rc ctx out) (c/rc ctx outside)))
     (is (nil? (pure/state e)))
     (sync/release! ctx e out) (sync/release! ctx e outside) (sync/close! ctx e))))))

(deftest aggregate-work-failure-preserves-borrowed-input-and-cache-owners
 (let [{:keys [ctx] :as lab} (context {}) e (pure/machine lab)
       input (expr/bvar! ctx e 0) values (pure/array! ctx e [])]
  (j/retain! ctx e input)
  (j/start! ctx e (pure/label "instantiateRev") [input values])
  (pure/until! ctx e #(some-> (pure/state e) (h/private-value "liveCacheEntries") pos?))
  (let [s (pure/state e) before (c/rc ctx input)]
   (sync/private-set! (h/private-value s "budget") "work" (long 1000000))
   (is (re-find #"work outside bounded" (c/failure #(j/advance! ctx e 1))))
   (is (= before (c/rc ctx input))) (is (= 2 before)) (is (= 1 (c/rc ctx values)))
   (is (= "failed" (j/phase ctx e))) (is (g/bad? #(j/fork! ctx e []))))))

(defn check! [basis] (binding [*basis* basis] (run-tests 'java-ir-expr-instantiate-control-checks)))
