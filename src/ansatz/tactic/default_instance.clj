(ns ansatz.tactic.default-instance
  "Lean's default instances (Lean/Meta/Instances.lean `defaultInstanceExtension`,
   Elab/SyntheticMVars.lean `synthesizeUsingDefault`, v4.33.1). When ordinary instance
   synthesis stalls on a class problem whose type still has metavariables, a
   `@[default_instance]` of that class is unified with it: `HDiv Int ?β ?γ` takes
   `instHDiv : [Div α] → HDiv α α α`, which fixes `?β ?γ := Int`. Priorities are tried from
   the highest down, and the pending problems oldest first; the first success returns, so
   ordinary synthesis runs again before the next default is considered."
  (:require [ansatz.kernel.env :as env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.name :as name]
            [ansatz.meta :as meta]
            [ansatz.tactic.instance :as inst])
  (:import [ansatz.kernel ConstantInfo]))

(def init-default-instances
  "Lean 4.33.1 Init's `@[default_instance]` table: class → [[instance priority] …] in the
   extension's own order (the order `getDefaultInstances` returns). Read from Lean with
   `defaultInstanceExtension.getState` over `import Init` (see test/lean/default_instances.lean).
   The seed for an env that carries no `:default-instances` extension; a store or bundle whose
   attribute corpus records the attribute supersedes it."
  {"HAdd" [["instHAdd" 1000]]
   "HSub" [["instHSub" 1000]]
   "HMul" [["instHMul" 1000]]
   "HDiv" [["instHDiv" 1000]]
   "HMod" [["instHMod" 1000]]
   "HPow" [["instHPow" 1000]]
   "Pow" [["instPowOfHomogeneousPow" 1000] ["instPowNat" 1000]]
   "HSMul" [["instHSMul" 1000]]
   "HAppend" [["instHAppendOfAppend" 1000]]
   "HOrElse" [["instHOrElseOfOrElse" 1000]]
   "HAndThen" [["instHAndThenOfAndThen" 1000]]
   "HAnd" [["instHAndOfAndOp" 1000]]
   "HXor" [["instHXorOfXorOp" 1000]]
   "HOr" [["instHOrOfOrOp" 1000]]
   "HShiftLeft" [["instHShiftLeftOfShiftLeft" 1000]]
   "HShiftRight" [["instHShiftRightOfShiftRight" 1000]]
   "OfScientific" [["instOfScientificFloat" 501]]
   "Neg" [["Int.instNegInt" 500]]
   "OfNat" [["instOfNatNat" 100]]
   "String.Slice.Pattern.ForwardPattern"
   [["String.Slice.Pattern.CharPred.instForwardPatternForallCharBool" 1000]]
   "String.Slice.Pattern.BackwardPattern"
   [["String.Slice.Pattern.CharPred.instBackwardPatternForallCharBool" 1000]]
   "String.Slice.Pattern.ToForwardSearcher"
   [["String.Slice.Pattern.CharPred.instToForwardSearcherForallCharBoolDefaultForwardSearcher" 1000]]
   "String.Slice.Pattern.ToBackwardSearcher"
   [["String.Slice.Pattern.CharPred.instToBackwardSearcherForallCharBoolDefaultBackwardSearcher" 1000]]})

(defn default-instances
  "class name string → [[instance-name-string priority] …] for `env`: its `:default-instances`
   extension when present, else the Init seed. Instances the env lacks are dropped."
  [env]
  (let [table (or (env/get-extension env :default-instances nil) init-default-instances)]
    (into {}
          (keep (fn [[cls entries]]
                  (let [present (filterv #(env/lookup env (name/from-string (first %))) entries)]
                    (when (seq present) [cls present]))))
          table)))

(defn priorities
  "The distinct default-instance priorities, highest first (Lean's `PrioritySet`)."
  [table]
  (sort > (distinct (map second (mapcat val table)))))

(defn- class-name-of
  "The class head name of an instance problem `type`, as a string, or nil."
  [mctx type]
  (let [h (e/get-app-fn (meta/zonk-expr mctx type))]
    (when (e/const? h) (name/->string (e/const-name h)))))

(defn- telescope
  "Lean's `forallMetaTelescopeReducing` on `type`: a fresh metavariable per binder, declared in
   `lctx` (instance binders as synthetic instance problems). [mctx mvars binder-infos body]."
  [mctx st lctx type]
  (loop [mctx mctx t type mvars [] infos []]
    (let [t (if (e/forall? t) t (let [w (meta/whnf mctx st t)] (if (e/forall? w) w t)))]
      (if (e/forall? t)
        (let [id (swap! (:next-id st) inc)
              info (e/forall-info t)
              inst? (= :inst-implicit info)
              mctx (meta/add-expr-mvar-decl mctx id (e/forall-type t) lctx
                                            {:kind (if inst? :synthetic :natural)
                                             :inst-implicit? inst?})]
          (recur mctx (e/instantiate1 (e/forall-body t) (e/mvar id))
                 (conj mvars id) (conj infos info)))
        [mctx mvars infos t]))))

(defn try-default-instance
  "Lean `synthesizeUsingDefaultInstance`: unify the instance problem `mvar-id` with
   `instance-name` applied to fresh metavariables and assign it; then synthesize the instance's
   own instance arguments that are now determined. Returns the metacontext, or nil (nothing
   committed) when unification or a determined sub-instance fails. Sub-problems still carrying
   metavariables stay pending, as Lean's `synthesizePending` leaves them to the next round."
  [mctx st mvar-id instance-name]
  (let [env (:env st)
        decl (meta/expr-decl mctx mvar-id)
        ^ConstantInfo ci (env/lookup env (name/from-string instance-name))]
    (when (and decl ci)
      (let [lctx (:lctx decl)
            st (cond-> st lctx (assoc :lctx lctx))
            lps (vec (.levelParams ci))
            lids (vec (repeatedly (count lps) #(swap! (:next-id st) inc)))
            mctx (reduce meta/add-level-mvar-decl mctx lids)
            lvls (mapv lvl/mvar lids)
            ctype (cond-> (.type ci) (seq lps) (e/instantiate-level-params (zipmap lps lvls)))
            [mctx mvars infos body] (telescope mctx st lctx ctype)
            candidate (apply e/app* (e/const' (name/from-string instance-name) lvls) (map e/mvar mvars))]
        (when-let [mctx (try (meta/is-def-eq mctx st (meta/zonk-expr mctx (:type decl)) body)
                             (catch clojure.lang.ExceptionInfo _ nil))]
          (let [mctx (meta/assign-expr mctx mvar-id candidate)]
            (reduce (fn [mctx [id info]]
                      (if (not= :inst-implicit info)
                        mctx
                        (let [goal (meta/zonk-expr mctx (:type (meta/expr-decl mctx id)))]
                          (if (or (meta/has-expr-mvar? goal) (seq (meta/unassigned-level-mvars mctx goal)))
                            mctx
                            (if-let [[mctx value] (inst/synth-instance mctx st goal)]
                              (meta/assign-expr mctx id value)
                              (reduced nil))))))
                    mctx (map vector mvars infos))))))))

(defn synthesize-using-default
  "Lean `synthesizeUsingDefault`: over `pending` (instance problem ids, oldest first), for each
   priority from the highest down, apply the first default instance that succeeds.
   Returns the new metacontext, or nil when no default instance applies."
  [mctx st pending]
  (let [table (default-instances (:env st))]
    (some (fn [prio]
            (some (fn [id]
                    (when-let [cls (class-name-of mctx (:type (meta/expr-decl mctx id)))]
                      (some (fn [[instance p]]
                              (when (= p prio) (try-default-instance mctx st id instance)))
                            (get table cls))))
                  pending))
          (priorities table))))
