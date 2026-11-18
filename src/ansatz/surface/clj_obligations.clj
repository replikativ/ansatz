(ns ansatz.surface.clj-obligations
  "Clojure faithfulness obligations, discharged after an a/defn body is elaborated.

   Nat subtraction truncates at 0 and Clojure's `-` does not, so a Clojure `(- a b)` at Nat is
   faithful exactly where `b ≤ a`. The elaborator marks such a subtraction (mdata
   {:ansatz.clj/obligation :nat-sub-le}); `discharge` walks the elaborated body, collects the
   facts in scope at each mark and proves `b ≤ a` with omega. A proved mark is removed, so every
   later consumer (structural/WF compilation, codegen, proofs) sees the same term as before;
   an unprovable one is refused (:nat-sub-may-be-negative).

   Facts in scope at a mark:
     - every enclosing lambda binder (so the hypotheses `h : a < b` / `h : ¬(n = 0)` of a `dite`
       that an `if` over a comparison elaborates to);
     - the test of an enclosing `Bool.rec` / `cond`, read as a proposition (Nat.beq → =,
       Nat.ble → ≤, Nat.blt → <, decide p → p), positively in the true branch and negated in the
       false branch;
     - `P (Subtype.val p)` for a parameter `p : Subtype T P` (a malli [:int {:min 1}] refinement);
     - `x = v` for a `let` binding x := v at Nat or Int."
  (:require [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.name :as name]))

;; The tactic layer requires the elaborator, which requires this namespace (for the marks), so
;; the prover is resolved when an obligation is discharged rather than at load time.
(defn- tactic [sym] (requiring-resolve sym))

(def marker-key :ansatz.clj/obligation)

(defn mark-nat-sub
  "Wrap the Nat subtraction `expr` (an `HSub.hSub Nat Nat Nat inst a b` application) as an
   obligation `b ≤ a`, recording the surface form for the refusal message."
  [form expr]
  (e/mdata {marker-key :nat-sub-le :form form} expr))

(defn- marker [x]
  (when (e/mdata? x)
    (let [d (e/mdata-data x)]
      (when (and (map? d) (marker-key d)) d))))

(defonce ^:private counter (atom 9600000))
(defn- fresh [] (swap! counter inc))

(defn- c [n & lv] (e/const' (name/from-string n) (vec lv)))
(def ^:private NAT (c "Nat"))
(def ^:private INT (c "Int"))
(def ^:private L0 lvl/zero)
(def ^:private L1 (lvl/succ lvl/zero))

(defn- head-name [x]
  (let [[h _] (e/get-app-fn-args x)]
    (when (e/const? h) (name/->string (e/const-name h)))))

(defn- le-nat [b a] (e/app* (c "LE.le" L0) NAT (c "instLENat") b a))
(defn- lt-nat [b a] (e/app* (c "LT.lt" L0) NAT (c "instLTNat") b a))
(defn- eq-at [T a b] (e/app* (c "Eq" L1) T a b))
(defn- not' [p] (e/app (c "Not") p))

(defn- bool-prop
  "The proposition a Bool test means, when it is one omega can read; nil otherwise."
  [d]
  (let [[_ as] (e/get-app-fn-args d)]
    (case (head-name d)
      "Nat.beq" (when (= 2 (count as)) (eq-at NAT (nth as 0) (nth as 1)))
      "Nat.ble" (when (= 2 (count as)) (le-nat (nth as 0) (nth as 1)))
      "Nat.blt" (when (= 2 (count as)) (lt-nat (nth as 0) (nth as 1)))
      "Decidable.decide" (when (= 2 (count as)) (first as))
      nil)))

(defn- test-facts
  "Facts for the true / false branch of a Bool test `d`: [[props-if-true] [props-if-false]]."
  [d]
  (case (head-name d)
    "Bool.not" (let [[_ as] (e/get-app-fn-args d)] (vec (reverse (test-facts (first as)))))
    "Bool.and" (let [[_ as] (e/get-app-fn-args d)]
                 [(vec (mapcat (comp first test-facts) as)) []])
    "Bool.or" (let [[_ as] (e/get-app-fn-args d)]
                [[] (vec (mapcat (comp second test-facts) as))])
    (if-let [p (bool-prop d)] [[p] [(not' p)]] [[] []])))

(defn- with-facts [scope props]
  (into scope (map (fn [p] [(fresh) p]) props)))

(defn- subtype-fact
  "For a binder `p : Subtype T P`, the fact `P (Subtype.val p)` (beta-reduced)."
  [fid ty]
  (let [[h as] (e/get-app-fn-args ty)]
    (when (and (e/const? h) (= "Subtype" (name/->string (e/const-name h))) (= 2 (count as)))
      (let [[T P] as
            v (e/app* (e/const' (name/from-string "Subtype.val") (vec (e/const-levels h))) T P (e/fvar fid))]
        (if (e/lam? P) (e/instantiate1 (e/lam-body P) v) (e/app P v))))))

(defn- prove-le
  "Prove `b ≤ a` under `scope` ([[fvar-id type] …], outermost first) with omega. True when proved."
  [env scope b a]
  (try
    (let [ids (mapv first scope) tys (mapv second scope)
          goal (loop [i (dec (count ids)) body (e/abstract-many (le-nat b a) ids)]
                 (if (< i 0) body
                     (recur (dec i) (e/forall' "s" (e/abstract-many (nth tys i) (subvec ids 0 i))
                                               body :default))))
          [ps _] ((tactic 'ansatz.tactic.proof/start-proof) env goal)
          ps ((tactic 'ansatz.tactic.basic/intros) ps (mapv #(str "s" %) (range (count ids))))
          ps ((tactic 'ansatz.core/run-tactic) ps '(omega))]
      (when ((tactic 'ansatz.tactic.proof/solved?) ps)
        ((tactic 'ansatz.tactic.extract/verify) ps)
        true))
    (catch Exception _ false)))

(defn- refuse! [data facts]
  (throw (ex-info (str "Refused " (pr-str (:form data)) ": this Nat subtraction may go below 0, "
                       "where Lean's Nat `-` truncates and Clojure's `-` goes negative"
                       "\n  hint: declare the operands Int (or the result Int), add a guard such as "
                       "(if (<= b a) …), or write (Nat.sub a b) to mean the truncated subtraction")
                  {:kind :clj/refused :reason :nat-sub-may-be-negative :form (:form data)
                   :hint "declare Int, guard with (<= b a), or write Nat.sub"
                   :facts-tried facts})))

(defn discharge
  "Discharge the Nat-subtraction obligations of an elaborated body. `expr` may have free fvars
   listed in `free` ([[fvar-id type] …], e.g. the self reference of a recursive definition).
   Returns `expr` with the obligation marks removed; throws a :clj/refused ex-info for one that
   omega cannot prove."
  ([env expr] (discharge env expr []))
  ([env expr free]
   (letfn [(walk [x scope]
             (case (e/tag x)
               :mdata
               (if-let [d (marker x)]
                 (let [inner (walk (e/mdata-expr x) scope)
                       [_ as] (e/get-app-fn-args inner)
                       a (nth as 4 nil) b (nth as 5 nil)]
                   (if (and a b (prove-le env scope b a))
                     inner
                     (refuse! d (count scope))))
                 (e/mdata (e/mdata-data x) (walk (e/mdata-expr x) scope)))

               :lam
               (let [id (fresh) bt (e/lam-type x)
                     scope' (cond-> (conj scope [id bt])
                              (subtype-fact id bt) (with-facts [(subtype-fact id bt)]))
                     body (walk (e/instantiate1 (e/lam-body x) (e/fvar id)) scope')]
                 (e/lam (e/lam-name x) (walk bt scope) (e/abstract-many body [id]) (e/lam-info x)))

               :let
               (let [id (fresh) t (e/let-type x)
                     v (walk (e/let-value x) scope)
                     tn (head-name t)
                     scope' (cond-> (conj scope [id t])
                              (#{"Nat" "Int"} tn) (with-facts [(eq-at (if (= tn "Nat") NAT INT) (e/fvar id) v)]))
                     body (walk (e/instantiate1 (e/let-body x) (e/fvar id)) scope')]
                 (e/let' (e/let-name x) t v (e/abstract-many body [id])))

               :app
               (let [[h as] (e/get-app-fn-args x)
                     hn (when (e/const? h) (name/->string (e/const-name h)))]
                 (cond
                   ;; Bool.rec motive false-case true-case major
                   (and (= hn "Bool.rec") (>= (count as) 4))
                   (let [[motive fc tc major & extra] as
                         major' (walk major scope)
                         [tf ff] (test-facts major')]
                     (apply e/app* h (walk motive scope) (walk fc (with-facts scope ff))
                            (walk tc (with-facts scope tf)) major' (map #(walk % scope) extra)))
                   ;; cond.{u} α c a b
                   (and (= hn "cond") (>= (count as) 4))
                   (let [[α cnd t f & extra] as
                         cnd' (walk cnd scope)
                         [tf ff] (test-facts cnd')]
                     (apply e/app* h α cnd' (walk t (with-facts scope tf)) (walk f (with-facts scope ff))
                            (map #(walk % scope) extra)))
                   :else
                   (apply e/app* (walk h scope) (map #(walk % scope) as))))

               :proj (e/proj (e/proj-type-name x) (e/proj-idx x) (walk (e/proj-struct x) scope))
               x))]
     (walk expr (reduce (fn [sc [id t]]
                          (cond-> (conj sc [id t])
                            (subtype-fact id t) (with-facts [(subtype-fact id t)])))
                        [] free)))))

(defn has-obligations?
  "Does `expr` contain an obligation mark?"
  [expr]
  (boolean
   (some marker
         (tree-seq #(contains? #{:app :lam :forall :let :mdata :proj} (e/tag %))
                   (fn [x] (case (e/tag x)
                             :app [(e/app-fn x) (e/app-arg x)]
                             :lam [(e/lam-type x) (e/lam-body x)]
                             :forall [(e/forall-type x) (e/forall-body x)]
                             :let [(e/let-type x) (e/let-value x) (e/let-body x)]
                             :mdata [(e/mdata-expr x)]
                             :proj [(e/proj-struct x)]))
                   expr))))
