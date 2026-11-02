(ns java-ir-expr-full-control-checks
 "Private two-pass exceptional control; setup adapters are explicit models."
 (:refer-clojure :exclude [run!])
 (:require [clojure.test :refer [deftest is run-tests]]
  [java-ir-baseline :as j] [java-ir-baseline-checks :as c]
  [java-ir-expr-full-checks :as full] [engine-support.expr :as expr]
  [engine-support.expr-context :as direct] [engine-support.delayed :as delayed]
  [java-ir-level-mvars-checks :as level] [java-ir-host-checks :as h]
  [java-ir-generation-checks :as g] [java-ir-sync-task-checks :as sync]))
(def ^:dynamic *basis* nil)
(def pv expr/private-value)
(defn context [options] (binding [full/*basis* *basis*] (full/context options)))
(defn state [e] (full/state e))
(defn transform [e] (some-> (state e) (pv "delayed")))
(defn session [e] (some-> (transform e) (pv "foundation")))
(defn simple-case! [ctx e]
 (let [name (level/name! ctx e "x")]
  (full/setup-delayed! ctx e {:fvars [(delayed/named-fvar! ctx e (expr/retain ctx e name))]
      :pending-value (delayed/named-fvar! ctx e name) :args [(expr/bvar! ctx e 3)]})))
(defn writeback-case! [ctx e]
 ;; A resolvable subtree and an unassigned bare MVar make the whole pending
 ;; assignment unresolvable. Pass2 normalizes that stored value in outer mode.
 (let [assign #(expr/call ctx e (str "model-setup-" (direct/helpers 4)) %)
       m (level/fresh! ctx e) pn (level/name! ctx e "ready-pending") qn (level/name! ctx e "mixed-pending")
       hi (level/name! ctx e "ready-head") ho (level/name! ctx e "stuck-head")
       value (expr/fvar! ctx e "resolved")
       m (assign [m (expr/retain ctx e pn) (expr/retain ctx e value)])
       install (fn [m name pending]
          (let [record (expr/call ctx e "model-delayed-record" [(delayed/array! ctx e []) pending])
                m (expr/call ctx e "model-swap-expr-delayed-maps" [m])
                m (assign [m name record])]
           (expr/call ctx e "model-swap-expr-delayed-maps" [m])))
       m (install m hi pn)
       inner (expr/app! ctx e (direct/mvar! ctx e (level/name! ctx e "ready-head")) (expr/sort! ctx e))
       old (expr/app! ctx e inner (direct/mvar! ctx e (level/name! ctx e "unassigned")))
       m (assign [m (expr/retain ctx e qn) old]) m (install m ho (expr/retain ctx e qn))
       input (expr/app! ctx e (direct/mvar! ctx e (level/name! ctx e "stuck-head")) (expr/sort! ctx e))]
  {:m m :input input :name qn :value value :old old}))

(deftest pass-two-fvars-code-request-forks-active-foundation-and-shared-cell
 (let [target (direct/helpers 2) {:keys [ctx headers] :as lab} (context {:defer #{target}})
       parent (full/engine lab) {:keys [m input]} (simple-case! ctx parent)]
  (full/start! lab parent m input)
  (expr/until! ctx parent #(some? (j/code-request ctx parent)))
  (is (= 3 (pv (state parent) "stage")))
  (let [packet (pv (session parent) "call") request (j/code-request ctx parent)
        {child :engine} (j/fork! ctx parent []) ready (expr/materialize lab target)]
   (is (identical? (headers target) (.header request)))
   (is (nil? (pv packet "target"))) (is (some? (pv packet "transformTarget")))
   (is (true? (pv packet "entered"))) (is (every? false? (vec (pv packet "owned"))))
   (doseq [e [parent child]]
    (is (identical? (pv (state e) "context") (pv (session e) "context")))
    (is (identical? (pv (state e) "budget") (pv (session e) "budget")))
    (j/resume-code! ready e (j/code-request ready e))
    (let [pair (expr/finish-research! ready e)]
     (is (= [3] (expr/fields ready (full/full-result ready pair)))) (full/close! ready e pair))))))

(deftest pass-two-setter-code-pause-has-empty-cell-and-preserved-old-assignment
 (let [target (direct/helpers 4) {:keys [ctx] :as lab} (context {:defer #{target}})
       parent (full/engine lab) {:keys [m input name value old]} (writeback-case! ctx parent)]
  (full/start! lab parent m input)
  (expr/until! ctx parent #(some? (j/code-request ctx parent)))
  (is (= 3 (pv (state parent) "stage")))
  (is (nil? (pv (pv (state parent) "context") "current")))
  (is (pos? (count (pv (session parent) "saved"))))
  (is (not (true? (pv old "dead"))))
  (let [{child :engine roots :roots} (j/fork! ctx parent [name value]) ready (expr/materialize lab target)]
   (doseq [[e n v] [[parent name value] [child (roots 0) (roots 1)]]]
    (is (nil? (pv (pv (state e) "context") "current")))
    (j/resume-code! ready e (j/code-request ready e))
    (let [pair (expr/finish-research! ready e) m2 (first (expr/fields ready pair))
          option (expr/call ready e (direct/helpers 0) [(expr/retain ready e m2) n])
          assigned (first (expr/fields ready option)) prefix (first (expr/fields ready assigned))]
     (is (identical? v (first (expr/fields ready prefix))))
     (sync/release! ready e option) (sync/release! ready e v) (full/close! ready e pair))))))

(deftest delayed-lift-child-code-fork-keeps-shared-budget-and-ancestor-input
 (let [target (expr/roles 0) {:keys [ctx] :as lab} (context {:defer #{target}})
       parent (full/engine lab) name (level/name! ctx parent "x")
       {:keys [m input]} (full/setup-delayed! ctx parent
          {:fvars [(delayed/named-fvar! ctx parent (expr/retain ctx parent name))]
           :pending-value (expr/lam! ctx parent (delayed/named-fvar! ctx parent name))
           :args [(expr/bvar! ctx parent 0)]})]
  (full/start! lab parent m input)
  (expr/until! ctx parent #(some? (j/code-request ctx parent)))
  (let [worker (expr/state parent)]
   (is (some? worker)) (is (nil? (pv worker "input")))
   (is (identical? (pv (state parent) "budget") (pv worker "budget"))))
  (let [{child :engine} (j/fork! ctx parent []) ready (expr/materialize lab target)]
   (doseq [e [parent child]]
    (is (identical? (pv (state e) "budget") (pv (expr/state e) "budget")))
    (j/resume-code! ready e (j/code-request ready e))
    (let [pair (expr/finish-research! ready e) body (nth (expr/fields ready (full/full-result ready pair)) 2)]
     (is (= [1] (expr/fields ready body))) (full/close! ready e pair))))))

(deftest pair-is-owned-before-e1-and-direct-member-retirement-and-forks
 (let [{:keys [ctx] :as lab} (context {}) parent (full/engine lab)
       name (level/name! ctx parent "direct") value (expr/sort! ctx parent)
       m (direct/assign! ctx parent (level/fresh! ctx parent) (expr/retain ctx parent name) (expr/retain ctx parent value))
       input (direct/mvar! ctx parent name)]
  (full/start! lab parent m input)
  (expr/until! ctx parent #(= 6 (pv (state parent) "stage")))
  (let [s (state parent) direct (pv s "direct")]
   (is (= 2 (pv s "pairFields"))) (is (= 3 (pv direct "phase")))
   (is (true? (pv (pv s "pair") "owned"))) (is (true? (pv (pv s "e1") "owned")))
   (is (false? (pv (pv s "e2") "owned"))) (is (nil? (pv (pv s "context") "current"))))
  (let [{child :engine roots :roots} (j/fork! ctx parent [value])]
   (doseq [[e v] [[parent value] [child (first roots)]]]
    (let [pair (expr/finish-research! ctx e)]
     (is (identical? v (full/full-result ctx pair))) (is (= 3 (c/rc ctx v)))
     (sync/release! ctx e v) (full/close! ctx e pair))))))

(deftest two-pass-budget-failure-retains-latest-context-and-inputs
 (let [{:keys [ctx] :as lab} (context {}) e (full/engine lab) {:keys [m input]} (simple-case! ctx e)]
  (full/start! lab e m input)
  (expr/until! ctx e #(= 3 (pv (state e) "stage")))
  (let [s (state e) budget (pv s "budget") old (c/rc ctx input)]
   (sync/private-set! budget "work" (long 1000000))
   (is (re-find #"work outside bounded" (c/failure #(j/advance! ctx e 1))))
   (is (= "failed" (j/phase ctx e))) (is (= old (c/rc ctx input)))
   (is (some? (pv (pv s "context") "current")))
   (is (g/bad? #(j/fork! ctx e []))))))

(defn check! [basis] (binding [*basis* basis] (run-tests 'java-ir-expr-full-control-checks)))
