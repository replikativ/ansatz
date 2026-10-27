;; Port of Lean/Elab/Tactic/Omega/OmegaM.lean: Context, State, Cache,
;; lookup, commitWhen, withoutModifyingState (checkout 55f80e10).
(ns ansatz.tactic.omega.omega-m)

(def default-context
  {:cfg {:splitNatSub true :splitMinMax true :splitDisjunctions true :splitNatAbs true}})

(defn mk-state []
  {:atoms {} :expr->idx {} :idx->expr {} :idx->int-expr {} :next-idx 0 :cache {}})

(defn lookup
  "Immutable lookup. New atoms return analyzed proof facts, existing atoms nil.
   analyze-atom receives the canonical Int expression."
  [state expr analyze-atom]
  (if-some [i (get (:atoms state) expr)]
    [state [i nil]]
    (let [i (:next-idx state)]
      [(-> state
           (assoc-in [:atoms expr] i)
           (assoc-in [:expr->idx expr] i)
           (assoc-in [:idx->expr i] expr)
           (assoc-in [:idx->int-expr i] expr)
           (update :next-idx inc))
       [i (vec (analyze-atom expr))]])))

(defn atoms [state]
  (mapv val (sort-by key (:idx->int-expr state))))

(defn commit-when
  "f returns [value state cache commit?]. Roll back both snapshots together."
  [state cache f]
  (let [[value state' cache' commit?] (f state cache)]
    [value (if commit? state' state) (if commit? cache' cache)]))

(defn without-modifying-state [state cache f]
  (commit-when state cache
               (fn [s c] (let [[value s' c'] (f s c)] [value s' c' false]))))

;; Host adaptation: Lean uses MetaM heartbeats/recursion guards. There is no shared
;; tactic heartbeat in ansatz. These configurable limits fail explicitly; they
;; never turn incomplete work into a successful saturation or unsupported atom.
(def ^:dynamic *work-limit* 1000000)
(def ^:dynamic *depth-limit* 128)
(def ^:dynamic *work* nil)
(def ^:dynamic *depth* 0)

(defn limit! [limit value]
  (throw (ex-info (str "Tactic error: omega " (name limit) " budget exhausted (" value ")")
                  {:kind :tactic-error :tactic :omega :limit limit :value value})))

(defn charge! []
  (when (and *work* (> (swap! *work* inc) *work-limit*))
    (limit! :work *work-limit*)))

(defn guarded
  "Charge before recursive frontend/certificate descent, sharing work per call."
  [f]
  (fn [& args]
    (binding [*work* (or *work* (atom 0))
              *depth* (inc *depth*)]
      (charge!)
      (when (> *depth* *depth-limit*) (limit! :depth *depth-limit*))
      (apply f args))))
