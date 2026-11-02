(ns java-ir-expr-full-adversarial-checks
 "Integrated scoped-cache/lifetime gates; malformed-state cases are explicit models."
 (:require [clojure.test :refer [deftest is run-tests]]
  [java-ir-baseline :as j] [java-ir-baseline-checks :as c]
  [java-ir-expr-full-checks :as full] [java-ir-expr-full-control-checks :as control]
  [engine-support.expr :as expr] [engine-support.expr-context :as direct]
  [java-ir-level-mvars-checks :as level] [java-ir-host-checks :as h]
  [java-ir-sync-task-checks :as sync] [java-ir-generation-checks :as g]))
(def ^:dynamic *basis* nil)
(def pv expr/private-value)
(defn context [options] (binding [full/*basis* *basis*] (full/context options)))
(defn session [e] (full/delayed-session e))
(defn frames [e] (some-> (full/state e) (pv "delayed") (pv "tasks") vec))
(defn visit? [frame] (= "DelayedVisitFrame" (.getSimpleName (class frame))))
(defn shared-case! [ctx e]
 (let [{:keys [m input]} (control/simple-case! ctx e)
       root (expr/setup! ctx e 4 [0 (expr/retain ctx e input) input 0])]
  {:m m :input root :shared input}))

(deftest shared-subtree-cache-keys-retain-distinct-binder-depths
 (let [{:keys [ctx] :as lab} (context {}) e (full/engine lab)
       {:keys [m input shared]} (shared-case! ctx e)]
  (full/start! lab e m input)
  (expr/until! ctx e #(let [s (session e)]
    (and s (zero? (pv s "depth")) (= #{0 1} (set (for [b (pv (pv s "cache") "buckets")
                               :when (identical? shared (pv b "key"))] (pv b "depth")))))))
  (is (= 0 (pv (session e) "depth")))
  (is (= 0 (pv (session e) "resultScope")))
  (let [pair (expr/finish-research! ctx e) [_ domain body] (expr/fields ctx (full/full-result ctx pair))]
   (is (identical? domain body)) (is (= [3] (expr/fields ctx domain)))
   (full/close! ctx e pair))))

(deftest composite-child-locals-retire-before-scoped-insert-and-fork
 (let [{:keys [ctx] :as lab} (context {}) parent (full/engine lab)
       {:keys [m input]} (shared-case! ctx parent)]
  ;; One real outside occurrence ensures the outer binder is source-shared.
  (j/retain! ctx parent input) (full/start! lab parent m input)
  (expr/until! ctx parent #(some (fn [f] (and (visit? f) (identical? input (pv f "original"))
          (= 30 (pv f "stage")) (= 2 (pv f "cleanup")))) (frames parent)))
  (let [frame (first (filter #(and (visit? %) (identical? input (pv % "original"))) (frames parent)))
        children (vec (pv frame "children"))]
   (is (every? #(or (nil? %) (false? (pv % "owned"))) children))
   (is (true? (pv (pv frame "result") "owned"))))
  (expr/until! ctx parent #(some? (some-> (session parent) (pv "cacheOperation"))))
  (let [op (pv (session parent) "cacheOperation")
        {child :engine roots :roots} (j/fork! ctx parent [input])]
   (is (= 3 (pv op "kind"))) (is (true? (pv (pv op "computed") "owned")))
   (doseq [[e outside] [[parent input] [child (first roots)]]]
    (let [pair (expr/finish-research! ctx e)]
     (is (not (identical? outside (full/full-result ctx pair))))
     (is (= 1 (c/rc ctx outside)))
     (sync/release! ctx e outside) (full/close! ctx e pair))))))

(deftest final-delayed-member-drain-fork-keeps-context-before-pair-allocation
 (let [{:keys [ctx] :as lab} (context {}) parent (full/engine lab)
       {:keys [m input]} (control/simple-case! ctx parent)]
  (full/start! lab parent m input)
  (expr/until! ctx parent #(= 4 (pv (full/state parent) "stage")))
  (let [s (full/state parent)]
   (is (nil? (pv s "pair"))) (is (true? (pv (pv s "e1") "owned")))
   (is (true? (pv (pv s "e2") "owned")))
   (is (some? (pv (pv s "context") "current")))
   (is (= 3 (pv (session parent) "phase"))))
  (let [{child :engine} (j/fork! ctx parent [])]
   (doseq [e [parent child]]
    (let [pair (expr/finish-research! ctx e)]
     (is (= [3] (expr/fields ctx (full/full-result ctx pair))))
     (is (nil? (full/state e))) (full/close! ctx e pair))))))

(deftest pair-survives-final-direct-level-drain-fork
 (let [{:keys [ctx] :as lab} (context {}) parent (full/engine lab)
       name (level/name! ctx parent "u") lvl (level/mvar! ctx parent (expr/retain ctx parent name))
       m (level/assign! ctx parent (level/fresh! ctx parent) name (level/succ! ctx parent 0))
       input (expr/setup! ctx parent 1 [lvl])]
  (full/start! lab parent m input)
  (expr/until! ctx parent #(= 7 (pv (full/state parent) "stage")))
  (let [s (full/state parent)]
   (is (true? (pv (pv s "pair") "owned")))
   (is (false? (pv (pv s "e1") "owned")))
   (is (nil? (pv (pv s "context") "current")))
   (is (= 3 (pv (pv s "direct") "phase"))))
  (let [{child :engine} (j/fork! ctx parent [])]
   (doseq [e [parent child]]
    (let [pair (expr/finish-research! ctx e) level (first (expr/fields ctx (full/full-result ctx pair)))]
     (is (= 1 (.getInt ^java.lang.reflect.Field (:tag ctx) level)))
     (full/close! ctx e pair))))))

(deftest malformed-pass-two-accessor-result-remains-owned-in-receiver
 ;; MODEL source-compatible Header with a deliberately invalid fvars body.
 (let [target (direct/helpers 2) body (c/let-ir 10 "object" (c/ctor 3 [(c/v 1)] 0) (c/ret 10))
       {:keys [ctx] :as lab} (context {:replacements {target body}}) e (full/engine lab)
       {:keys [m input]} (control/simple-case! ctx e)]
  (full/start! lab e m input)
  (is (g/bad? #(expr/finish-research! ctx e)))
  (is (= "failed" (j/phase ctx e)))
  (let [action (full/action e) receiver (aget ^objects (pv e "objects") (pv action "slot"))
        packet (pv (session e) "call")]
   (is (= 3 (.getInt ^java.lang.reflect.Field (:tag ctx) receiver)))
   (is (= 1 (c/rc ctx receiver))) (is (true? (pv packet "entered")))
   (is (every? false? (vec (pv packet "owned"))))
   (is (some? (pv (pv (full/state e) "context") "current"))))))

(defn check! [basis] (binding [*basis* basis] (run-tests 'java-ir-expr-full-adversarial-checks)))

(deftest stale-resolver-cache-model-still-normalizes-a-no-mvar-assignment
 ;; Explicit analysis-cache model, not a source-produced ordinary-tree claim:
 ;; a preexisting NO pending result survives a context state in which its current
 ;; assignment is MVar-free. get_assignment must still insert the normalized Name.
 (let [{:keys [ctx] :as lab} (context {}) e (full/engine lab)
       {:keys [m input record]} (control/simple-case! ctx e)
       pending-name (second (expr/fields ctx record))]
  (full/start! lab e m input)
  (expr/until! ctx e #(= 3 (pv (full/state e) "stage")))
  (let [s (session e) method (.getDeclaredMethod ^Class (:class ctx) "pendingEntry"
                       (into-array Class [(class s) Object Boolean/TYPE]))]
   (.setAccessible method true)
   (let [entry (.invoke method e (object-array [s pending-name true]))]
    (sync/private-set! entry "state" (int 2))))
  (expr/until! ctx e #(pos? (count (pv (session e) "nameOwners"))))
  (is (= 1 (count (pv (session e) "nameOwners"))))
  (is (empty? (pv (session e) "saved")))
  (let [pair (expr/finish-research! ctx e)]
   (is (identical? input (full/full-result ctx pair)))
   (full/close! ctx e pair))))
