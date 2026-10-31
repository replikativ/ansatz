(ns java-ir-expr-full-checks
 "Private complete two-pass job. Native530 remains unavailable."
 (:refer-clojure :exclude [run!])
 (:require [clojure.test :refer [deftest is run-tests]]
  [java-ir-baseline :as j] [java-ir-baseline-checks :as c]
  [java-ir-expr-machinery-checks :as expr] [java-ir-expr-direct-checks :as direct]
  [java-ir-expr-delayed-checks :as delayed] [java-ir-level-mvars-checks :as level]
  [java-ir-sync-task-checks :as sync] [java-ir-generation-checks :as g]))
(def ^:dynamic *basis* nil)
(def pv expr/private-value)
(defn context ([] (context {}))
 ([options] (binding [direct/*basis* *basis*]
  (direct/context (update options :rows #(concat (direct/delayed-model-rows) %))))))
(def engine direct/engine)
(defn action [e]
 (loop [a (sync/action e)] (when a (if (pv a "exprFull") a (recur (pv a "parent"))))))
(defn state [e] (some-> (action e) (pv "exprFull")))
(defn start! [{:keys [ctx headers]} e m input]
 (let [cls (Class/forName "ansatz.research.ir.Interpreter$Header" true (:loader ctx))
       hs (into-array cls (mapv headers direct/helpers)) cs (into-array cls (mapv headers expr/roles))
       method (.getDeclaredMethod ^Class (:class ctx) "startExprFullResearch"
                (into-array Class [(class hs) (class cs) Object Object]))]
  (.setAccessible method true) (.invoke method e (object-array [hs cs m input]))))
(defn run! [lab e m input] (start! lab e m input) (expr/finish-research! (:ctx lab) e))
(defn close! [ctx e pair] (sync/release! ctx e pair) (sync/close! ctx e))
(defn delayed-session [e] (some-> (state e) (pv "delayed") (pv "foundation")))
(defn full-result [ctx pair] (second (expr/fields ctx pair)))
(defn setup-delayed! [ctx e {:keys [fvars pending-value args]}]
 ;; Explicit storage-model adapter for the delayed map; getters, setters and
 ;; constructors execute authentic source. This is not a source monadic API.
 (let [m (level/fresh! ctx e) n (level/name! ctx e "delayed") pending (level/name! ctx e "pending")
       m (direct/assign! ctx e m (expr/retain ctx e pending) pending-value)
       [m record] (delayed/delayed-with-fvars! ctx e m n pending (delayed/array! ctx e fvars))
       head (direct/mvar! ctx e (level/name! ctx e "delayed"))
       input (reduce #(expr/app! ctx e %1 %2) head args)]
  {:m m :input input :record record}))

(deftest original-native-stays-unregistered
 (let [native (last (direct/originals))]
  (is (re-find #"Unsupported baseline extern"
        (c/failure #(j/prepare-host-program *basis* [(get native "row")] []))))))

(deftest no-delayed-path-returns-pair-and-independent-input-occurrence
 (let [{:keys [ctx] :as lab} (context {:defer (set (concat direct/helpers expr/roles level/roles))})
       e (engine lab) m (level/fresh! ctx e) input (expr/bvar! ctx e 0)]
  (start! lab e m input)
  (expr/until! ctx e #(= 6 (pv (state e) "stage")))
  (let [s (state e) pair (pv (pv s "pair") "value")]
   (is (= 2 (pv s "pairFields"))) (is (identical? input (full-result ctx pair)))
   (is (= 2 (c/rc ctx input))) (is (nil? (pv (pv s "context") "current")))
   (is (true? (pv (pv s "e1") "owned"))) (is (false? (pv (pv s "e2") "owned"))))
  (let [pair (expr/finish-research! ctx e)]
   (is (identical? m (first (expr/fields ctx pair)))) (is (= 1 (c/rc ctx input)))
   (is (nil? (state e))) (close! ctx e pair))))

(deftest original-direct-assignment-and-level-context-readback
 (let [{:keys [ctx] :as lab} (context) e (engine lab) m (level/fresh! ctx e)
       n (level/name! ctx e "direct") value (expr/sort! ctx e)
       input (direct/mvar! ctx e (expr/retain ctx e n))
       m (direct/assign! ctx e m (expr/retain ctx e n) (expr/retain ctx e value))
       pair (run! lab e m input) [m2 out] (expr/fields ctx pair)
       assignment (expr/call ctx e (direct/helpers 0) [(expr/retain ctx e m2) n])]
  (is (identical? value out)) (is (identical? value (first (expr/fields ctx assignment))))
  (is (true? (pv input "dead"))) (sync/release! ctx e assignment)
  (sync/release! ctx e value) (close! ctx e pair)))

(deftest delayed-exact-arity-substitutes-the-source-fvar
 (let [{:keys [ctx] :as lab} (context) e (engine lab)
       name (level/name! ctx e "bound")
       pending (delayed/named-fvar! ctx e (expr/retain ctx e name))
       argument (expr/fvar! ctx e "argument")
       {:keys [m input]} (setup-delayed! ctx e {:fvars [(delayed/named-fvar! ctx e name)]
                                :pending-value pending :args [(expr/retain ctx e argument)]})
       pair (run! lab e m input)]
  (is (identical? argument (full-result ctx pair))) (is (= 2 (c/rc ctx argument)))
  (is (true? (pv input "dead"))) (sync/release! ctx e argument) (close! ctx e pair)))

(deftest zero-fvar-delayed-extra-argument-runs-beta
 (let [{:keys [ctx] :as lab} (context) e (engine lab)
       argument (expr/fvar! ctx e "beta-argument")
       {:keys [m input]} (setup-delayed! ctx e {:fvars []
         :pending-value (expr/lam! ctx e (expr/bvar! ctx e 0)) :args [(expr/retain ctx e argument)]})
       pair (run! lab e m input)]
  (is (identical? argument (full-result ctx pair))) (is (= 2 (c/rc ctx argument)))
  (sync/release! ctx e argument) (close! ctx e pair)))

(deftest delayed-too-few-and-unassigned-pending-preserve-app
 (doseq [mode [:too-few :unassigned]]
  (let [{:keys [ctx] :as lab} (context) e (engine lab) m (level/fresh! ctx e)
        name (level/name! ctx e "head") pending (level/name! ctx e "pending")
        m (if (= mode :too-few) (direct/assign! ctx e m (expr/retain ctx e pending) (expr/sort! ctx e)) m)
        fvars (if (= mode :too-few) [(expr/fvar! ctx e "x") (expr/fvar! ctx e "y")] [])
        [m _] (delayed/delayed-with-fvars! ctx e m name pending (delayed/array! ctx e fvars))
        input (expr/app! ctx e (direct/mvar! ctx e (level/name! ctx e "head")) (expr/sort! ctx e))
        pair (run! lab e m input)]
   (is (identical? input (full-result ctx pair))) (is (= 1 (c/rc ctx input))) (close! ctx e pair))))

(defn check! [basis] (binding [*basis* basis] (run-tests 'java-ir-expr-full-checks)))

(deftest delayed-fvar-under-binder-lifts-the-borrowed-argument
 (let [{:keys [ctx] :as lab} (context) e (engine lab) name (level/name! ctx e "under-binder")
       pending (expr/lam! ctx e (delayed/named-fvar! ctx e (expr/retain ctx e name)))
       {:keys [m input]} (setup-delayed! ctx e {:fvars [(delayed/named-fvar! ctx e name)]
                                  :pending-value pending :args [(expr/bvar! ctx e 0)]})
       pair (run! lab e m input) body (nth (expr/fields ctx (full-result ctx pair)) 2)]
  (is (= [1] (expr/fields ctx body))) (close! ctx e pair)))

(deftest duplicate-fvar-forward-restore-keeps-source-last-install-result
 (let [{:keys [ctx] :as lab} (context) e (engine lab) name (level/name! ctx e "duplicate")
       pending (delayed/named-fvar! ctx e (expr/retain ctx e name))
       first (expr/fvar! ctx e "first") last (expr/fvar! ctx e "last")
       {:keys [m input]} (setup-delayed! ctx e
         {:fvars [(delayed/named-fvar! ctx e (expr/retain ctx e name)) (delayed/named-fvar! ctx e name)]
          :pending-value pending :args [(expr/retain ctx e first) (expr/retain ctx e last)]})
       pair (run! lab e m input)]
  (is (identical? last (full-result ctx pair)))
  (is (= 1 (c/rc ctx first))) (is (= 2 (c/rc ctx last)))
  (sync/release! ctx e first) (sync/release! ctx e last) (close! ctx e pair)))

(deftest complete-nested-delayed-resolution-with-distinct-substitution-scopes
 (let [{:keys [ctx] :as lab} (context) e (engine lab) m (level/fresh! ctx e)
       x (level/name! ctx e "x") y (level/name! ctx e "y")
       p (level/name! ctx e "inner-pending") q (level/name! ctx e "outer-pending")
       inner (level/name! ctx e "inner-head") outer (level/name! ctx e "outer-head")
       m (direct/assign! ctx e m (expr/retain ctx e p) (delayed/named-fvar! ctx e (expr/retain ctx e y)))
       [m _] (delayed/delayed-with-fvars! ctx e m inner p
              (delayed/array! ctx e [(delayed/named-fvar! ctx e y)]))
       inner-input (expr/app! ctx e (direct/mvar! ctx e (level/name! ctx e "inner-head"))
                         (delayed/named-fvar! ctx e (expr/retain ctx e x)))
       m (direct/assign! ctx e m (expr/retain ctx e q) inner-input)
       [m _] (delayed/delayed-with-fvars! ctx e m outer q
              (delayed/array! ctx e [(delayed/named-fvar! ctx e x)]))
       argument (expr/fvar! ctx e "actual")
       input (expr/app! ctx e (direct/mvar! ctx e (level/name! ctx e "outer-head")) (expr/retain ctx e argument))
       pair (run! lab e m input)]
  (is (identical? argument (full-result ctx pair))) (is (= 2 (c/rc ctx argument)))
  (sync/release! ctx e argument) (close! ctx e pair)))

(deftest nonresolvable-outer-pending-is-normalized-and-written-back
 (let [{:keys [ctx] :as lab} (context) e (engine lab) m (level/fresh! ctx e)
       pn (level/name! ctx e "good-pending") qn (level/name! ctx e "mixed-pending")
       hi (level/name! ctx e "good-head") ho (level/name! ctx e "stuck-head")
       value (expr/fvar! ctx e "resolved")
       m (direct/assign! ctx e m (expr/retain ctx e pn) (expr/retain ctx e value))
       [m _] (delayed/delayed-with-fvars! ctx e m hi pn (delayed/array! ctx e []))
       inner (expr/app! ctx e (direct/mvar! ctx e (level/name! ctx e "good-head")) (expr/sort! ctx e))
       pending-value (expr/app! ctx e inner (direct/mvar! ctx e (level/name! ctx e "unassigned")))
       m (direct/assign! ctx e m (expr/retain ctx e qn) pending-value)
       [m _] (delayed/delayed-with-fvars! ctx e m ho (expr/retain ctx e qn) (delayed/array! ctx e []))
       input (expr/app! ctx e (direct/mvar! ctx e (level/name! ctx e "stuck-head")) (expr/sort! ctx e))
       pair (run! lab e m input) m2 (first (expr/fields ctx pair))
       option (expr/call ctx e (direct/helpers 0) [(expr/retain ctx e m2) qn])
       assigned (first (expr/fields ctx option)) f (first (expr/fields ctx assigned))]
  (is (identical? input (full-result ctx pair)))
  (is (not (identical? pending-value assigned)))
  (is (identical? value (first (expr/fields ctx f))))
  (is (true? (pv pending-value "dead")))
  (sync/release! ctx e option) (sync/release! ctx e value) (close! ctx e pair)))
