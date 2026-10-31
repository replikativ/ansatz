(ns java-ir-expr-delayed-checks
  "Private stage-four protocols; original Expr native and full pass two stay off."
  (:refer-clojure :exclude [run!])
  (:require [clojure.test :refer [deftest is run-tests]]
            [java-ir-baseline :as j] [java-ir-baseline-checks :as c]
            [java-ir-expr-direct-checks :as direct] [java-ir-expr-machinery-checks :as expr]
            [java-ir-level-mvars-checks :as level] [java-ir-mvars-session-checks :as mixed]
            [java-ir-sync-task-checks :as sync] [java-ir-generation-checks :as g]
            [java-ir-host-checks :as h] [java-ir-scope-cache-model :as model]))
(def ^:dynamic *basis* nil)
(def pv expr/private-value)
(defn context ([] (context {})) ([options] (binding [direct/*basis* *basis*] (direct/context options))))
(def engine direct/engine)
(defn action [e]
  (loop [a (sync/action e)] (when a (if (pv a "delayedResearch") a (recur (pv a "parent"))))))
(defn state [e] (some-> (action e) (pv "delayedResearch")))
(defn session [e] (some-> (state e) (pv "session")))
(defn start! [{:keys [ctx headers]} e mode m anchors commands]
  (let [hs (into-array (Class/forName "ansatz.research.ir.Interpreter$Header" true (:loader ctx)) (mapv headers direct/helpers))
        cs (into-array (Class/forName "ansatz.research.ir.Interpreter$Header" true (:loader ctx)) (mapv headers expr/roles))
        rows (into-array (Class/forName "[I") (map int-array commands))
        method (.getDeclaredMethod ^Class (:class ctx) "startDelayedFoundationResearch"
                 (into-array Class [(class hs) (class cs) Integer/TYPE Object (class (object-array 0)) (class rows)]))]
    (.setAccessible method true) (.invoke method e (object-array [hs cs (int mode) m (object-array anchors) rows]))))
(defn run! [lab e mode m anchors commands] (start! lab e mode m anchors commands) (expr/finish-research! (:ctx lab) e))
(defn close! [ctx e report] (sync/release! ctx e report) (sync/close! ctx e))
(defn value-token [anchors credit]
  (when credit (let [v (pv credit "value")] (first (keep-indexed #(when (identical? %2 v) %1) anchors)))))
(def cache-programs
  [[[3 0 0 1 0] [2 0 0]]
   [[3 0 0 1 0] [0] [2 0 0] [3 0 0 2 0] [2 0 0] [1] [2 0 0]]
   [[3 0 0 1 0] [0] [3 0 0 2 1] [0] [3 0 0 3 2] [1] [2 0 0] [1] [2 0 0]]
   [[3 0 0 1 0] [0] [3 0 0 2 1] [0] [3 0 0 3 2] [3 0 0 4 1] [2 0 0] [1] [2 0 0] [1] [2 0 0]]
   [[3 0 0 1 0] [0] [3 0 0 2 1] [1] [0] [2 0 0] [3 0 0 3 0] [1] [2 0 0]]
   [[3 0 0 1 0] [3 0 1 2 0] [2 0 0] [2 0 1] [3 0 0 3 2] [2 0 0]]])
(deftest scope-cache-agrees-with-independent-stack-of-maps-model
  (doseq [commands cache-programs]
    (let [{:keys [ctx] :as lab} (context) e (engine lab) m (level/fresh! ctx e)
          anchors (vec (cons (expr/bvar! ctx e 0) (map #(expr/fvar! ctx e (str "cache-" %)) (range 4))))]
      (start! lab e 0 m anchors commands)
      (let [s (state e)]
        (loop [index 0 expected (model/initial)]
          (when (< index (count commands))
            (let [[next-expected token hit] (model/command expected (commands index))]
              (expr/until! ctx e #(= (inc index) (pv s "commandCursor")))
              (is (= token (value-token anchors (pv s "lastResult"))))
              (is (= (dec (count (:scopes next-expected))) (pv (pv (session e) "cache") "scope")))
              (is (= (:watermark next-expected) (pv (session e) "resultScope")))
              (when (some? hit) (is (= (if hit 1 0) (pv s "lastObservation"))))
              (recur (inc index) next-expected))))
        (let [report (expr/finish-research! ctx e)]
          (is (nil? (session e))) (is (= (* 4 (count commands)) (count (pv s "observations"))))
          (close! ctx e report))))))
(deftest popped-cache-entry-stays-owned-until-resumable-rewind
  (let [{:keys [ctx] :as lab} (context) e (engine lab) m (level/fresh! ctx e)
        key (expr/bvar! ctx e 0) value (expr/fvar! ctx e "evicted")
        commands [[0] [3 0 0 1 1] [1] [2 0 0]]]
    (start! lab e 0 m [key value] commands)
    (expr/until! ctx e #(= 3 (pv (state e) "commandCursor")))
    (is (= 2 (c/rc ctx value)))
    (is (= 1 (pv (pv (session e) "cache") "liveEntries")))
    (expr/until! ctx e #(= 4 (pv (state e) "commandCursor")))
    (is (= 1 (c/rc ctx value))) (is (= 0 (pv (pv (session e) "cache") "liveEntries")))
    (let [report (expr/finish-research! ctx e)] (is (true? (pv value "dead"))) (close! ctx e report))))
(defn array! [ctx e values]
  (reduce (fn [array value] (expr/call ctx e "Array.push" [0 array value])) (expr/call ctx e "Array.mkEmpty" [0 0]) values))
(defn named-fvar! [ctx e name] (expr/call ctx e "Lean.Expr.fvar._override" [name]))
(deftest install-lookup-and-forward-restore-track-owned-copy-counts
  (let [{:keys [ctx] :as lab} (context) e (engine lab) m (level/fresh! ctx e)
        name (level/name! ctx e "subst") p (expr/bvar! ctx e 0)
        fvars (array! ctx e [(named-fvar! ctx e (expr/retain ctx e name))]) args (array! ctx e [p])
        commands [[5 0 1 0] [7 2 0] [6] [7 2 0]]]
    (start! lab e 2 m [fvars args name] commands)
    (expr/until! ctx e #(= 1 (pv (state e) "commandCursor")))
    (is (= 3 (c/rc ctx p))) (is (= 4 (c/rc ctx name)))
    (expr/until! ctx e #(= 2 (pv (state e) "commandCursor")))
    (is (identical? p (pv (pv (state e) "lastResult") "value"))) (is (= 4 (c/rc ctx p)))
    (expr/until! ctx e #(= 3 (pv (state e) "commandCursor")))
    (is (= 1 (c/rc ctx p))) (is (= 2 (c/rc ctx name)))
    (is (empty? (pv (session e) "substitutions")))
    (let [report (expr/finish-research! ctx e)] (is (= 0 (second (expr/fields ctx report))))
      (is (true? (pv p "dead"))) (is (true? (pv name "dead"))) (close! ctx e report))))
(deftest duplicate-forward-restoration-literally-leaves-the-second-saved-mapping
  (let [{:keys [ctx] :as lab} (context) e (engine lab) m (level/fresh! ctx e)
        name (level/name! ctx e "duplicate") p (expr/bvar! ctx e 0) q (expr/bvar! ctx e 1)
        fvars (array! ctx e [(named-fvar! ctx e (expr/retain ctx e name)) (named-fvar! ctx e (expr/retain ctx e name))])
        args (array! ctx e [q p])]
    (start! lab e 2 m [fvars args name] [[5 0 1 0] [7 2 0] [6] [7 2 0]])
    (expr/until! ctx e #(= 2 (pv (state e) "commandCursor")))
    (is (identical? q (pv (pv (state e) "lastResult") "value")))
    (expr/until! ctx e #(= 3 (pv (state e) "commandCursor")))
    (is (= 0 (pv (pv (session e) "cache") "scope")))
    (is (not (empty? (pv (session e) "substitutions"))))
    (expr/until! ctx e #(= 4 (pv (state e) "commandCursor")))
    (is (= 1 (pv (session e) "resultScope")))
    (let [report (expr/finish-research! ctx e)]
      (is (identical? p (second (expr/fields ctx report)))) (is (= 1 (c/rc ctx p))) (is (true? (pv q "dead")))
      (close! ctx e report))))
(deftest nested-shadowing-and-binder-lift-use-one-budget-without-retaining-lift-input
  (let [{:keys [ctx] :as lab} (context) e (engine lab) m (level/fresh! ctx e)
        name (level/name! ctx e "shadow") p (expr/bvar! ctx e 0) q (expr/bvar! ctx e 5)
        fvars (array! ctx e [(named-fvar! ctx e (expr/retain ctx e name))])
        outer (array! ctx e [p]) inner (array! ctx e [q])]
    (start! lab e 2 m [fvars outer inner name] [[5 0 1 0] [5 0 2 1] [7 3 1] [6] [7 3 1] [6]])
    (expr/until! ctx e #(= 3 (pv (state e) "commandCursor")))
    (is (identical? q (pv (pv (state e) "lastResult") "value")))
    (expr/until! ctx e #(some? (expr/state e)))
    (let [worker (expr/state e) job (expr/current-job e)]
      (is (identical? (pv (session e) "budget") (pv worker "budget")))
      (is (nil? (pv worker "input"))) (is (identical? p (pv job "input"))))
    (expr/until! ctx e #(= 5 (pv (state e) "commandCursor")))
    (is (= [1] (expr/fields ctx (pv (pv (state e) "lastResult") "value"))))
    (let [report (expr/finish-research! ctx e)] (is (= 0 (second (expr/fields ctx report)))) (close! ctx e report))))
(deftest zero-fvar-scope-is-nonzero-with-empty-substitution
  (let [{:keys [ctx] :as lab} (context) e (engine lab) m (level/fresh! ctx e)
        fvars (array! ctx e []) args (array! ctx e [])]
    (start! lab e 2 m [fvars args] [[5 0 1 0] [6]])
    (expr/until! ctx e #(= 1 (pv (state e) "commandCursor")))
    (is (= 1 (pv (pv (session e) "cache") "scope"))) (is (empty? (pv (session e) "substitutions")))
    (let [report (expr/finish-research! ctx e)] (close! ctx e report))))
(defn delayed-with-fvars! [ctx e m name pending fvars]
  ;; Same explicitly labeled storage adapter as Stage3; actual generic map
  ;; operations/getters/accessors execute original source. No monadic API claim.
  (let [record (expr/call ctx e "model-delayed-record" [fvars pending])
        m (expr/call ctx e "model-swap-expr-delayed-maps" [m])
        m (direct/assign! ctx e m name record)]
    [(expr/call ctx e "model-swap-expr-delayed-maps" [m]) record]))
(deftest resolver-fast-path-ignores-universe-mvars-and-bare-expr-mvar-is-false
  (doseq [kind [:sort :fvar :bare]]
    (let [{:keys [ctx] :as lab} (context {:defer (set direct/helpers)}) e (engine lab) m (level/fresh! ctx e)
          input (case kind :sort (expr/setup! ctx e 1 [(level/mvar! ctx e (level/name! ctx e "level"))])
                      :fvar (expr/fvar! ctx e "free") :bare (direct/mvar! ctx e (level/name! ctx e "bare")))
          report (run! lab e 1 m [input] [[4 0]])]
      (is (= (if (= kind :bare) 0 1) (nth (expr/fields ctx report) 2)))
      (is (true? (pv input "dead"))) (close! ctx e report))))
(deftest resolvability-arity-short-circuit-precedes-pending-accessor
  (let [label (direct/helpers 3) {:keys [ctx] :as lab}
        (context {:rows (direct/delayed-model-rows) :defer #{label}}) e (engine lab)
        m (level/fresh! ctx e) n (level/name! ctx e "not-enough")
        input (expr/app! ctx e (direct/mvar! ctx e (expr/retain ctx e n)) (expr/sort! ctx e))
        fvars (array! ctx e [(expr/fvar! ctx e "a") (expr/fvar! ctx e "b")])
        [m record] (delayed-with-fvars! ctx e m n (level/name! ctx e "pending") fvars)
        report (run! lab e 1 m [input] [[4 0]])]
    (is (= 0 (nth (expr/fields ctx report) 2))) (is (= 1 (c/rc ctx record))) (close! ctx e report)))
(deftest resolvable-pending-value-and-argument-conjunction-use-original-getters
  (doseq [argument-mvar? [false true] pending-assigned? [false true]]
    (let [{:keys [ctx] :as lab} (context {:rows (direct/delayed-model-rows)}) e (engine lab)
          m (level/fresh! ctx e) n (level/name! ctx e "resolve") pending (level/name! ctx e "pending")
          arg (if argument-mvar? (direct/mvar! ctx e (level/name! ctx e "stuck")) (expr/sort! ctx e))
          input (expr/app! ctx e (direct/mvar! ctx e (expr/retain ctx e n)) arg)
          m (if pending-assigned? (direct/assign! ctx e m (expr/retain ctx e pending) (expr/fvar! ctx e "value")) m)
          [m record] (delayed-with-fvars! ctx e m n pending (array! ctx e [(expr/fvar! ctx e "x")]))
          map-before (nth (expr/fields ctx m) 8) report (run! lab e 1 m [input] [[4 0]])]
      (is (= (if (and pending-assigned? (not argument-mvar?)) 1 0) (nth (expr/fields ctx report) 2)))
      (is (identical? m (first (expr/fields ctx report))))
      (is (identical? map-before (nth (expr/fields ctx m) 8))) (close! ctx e report))))
(deftest pending-semantic-name-cycle-becomes-no-without-context-writeback
  (let [{:keys [ctx] :as lab} (context {:rows (direct/delayed-model-rows)}) e (engine lab)
        x (level/name! ctx e "head-x") y (level/name! ctx e "head-y")
        a (level/name! ctx e "pending-a") b (level/name! ctx e "pending-b")
        appx (expr/app! ctx e (direct/mvar! ctx e (expr/retain ctx e x)) (expr/sort! ctx e))
        appy (expr/app! ctx e (direct/mvar! ctx e (expr/retain ctx e y)) (expr/sort! ctx e))
        m (level/fresh! ctx e) m (direct/assign! ctx e m (expr/retain ctx e a) appy)
        m (direct/assign! ctx e m (expr/retain ctx e b) (expr/retain ctx e appx))
        [m _] (delayed-with-fvars! ctx e m x a (array! ctx e []))
        [m _] (delayed-with-fvars! ctx e m y b (array! ctx e []))]
    (start! lab e 1 m [appx] [[4 0]])
    (expr/until! ctx e #(= 1 (pv (state e) "commandCursor")))
    (let [entries (vec (pv (session e) "pendingOwners"))]
      (is (= 2 (count entries))) (is (every? #(= 2 (pv % "state")) entries)))
    (let [report (expr/finish-research! ctx e)] (is (= 0 (nth (expr/fields ctx report) 2))) (close! ctx e report))))

(defn check! [basis] (binding [*basis* basis] (run-tests 'java-ir-expr-delayed-checks)))
