(ns ansatz.meta.tactic.cases
  "Lean/Meta/Tactic/Cases.lean: CasesSubgoal, generalizeIndices, inductionCasesOn,
   unifyEqs?; supporting Subst.lean/substCore and UnifyEq.lean/unifyEq?
   (55f80e10a3). Uses the definitional casesOn constructions, independently of
   the public tactic's proof-recipe implementation. Context carries MetaM's
   local context, fresh-name supply, environment and metavariable context."
  (:require [ansatz.kernel.expr :as e]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.tc :as tc]
            [ansatz.meta :as meta]
            [ansatz.meta.fvar-subst :as subst]
            [ansatz.meta.constructions.util :as u]))

(defn tactic-error! [message data]
  (throw (ex-info (str "Tactic error: " message) (assoc data :kind :tactic-error))))

(defn context
  ([environment] (context environment {}))
  ([environment lctx]
   (atom (assoc (tc/attach-lctx (tc/mk-tc-state environment) lctx)
                :meta-mctx (atom meta/empty-context)))))

(defn set-lctx! [ctx lctx]
  (let [{:keys [env next-id meta-mctx]} @ctx]
    (reset! ctx (assoc (tc/attach-lctx (assoc (tc/mk-tc-state env) :next-id next-id) lctx)
                      :meta-mctx meta-mctx))))
(defn mctx [ctx] @(:meta-mctx @ctx))
(defn zonk [ctx expr] (meta/instantiate-expr-mvars (mctx ctx) expr))
(defn goal-decl [ctx id] (meta/expr-decl (mctx ctx) id))
(defn goal-type [ctx id] (zonk ctx (:type (goal-decl ctx id))))
(defn with-goal! [ctx id]
  (set-lctx! ctx (:lctx (goal-decl ctx id))))
(defn fresh-mvar! [ctx type]
  (let [id (swap! (:next-id @ctx) inc)]
    (swap! (:meta-mctx @ctx) meta/add-expr-mvar-decl id type (:lctx @ctx)
           {:kind :syntheticOpaque})
    id))
(defn assign! [ctx id value]
  (swap! (:meta-mctx @ctx) meta/checked-assign-expr id value {:check-type? false})
  nil)
(defn mk-lambda-fvars [ctx xs body]
  (reduce (fn [body x]
            (let [{:keys [name type info]} (u/decl ctx x)
                  id (e/fvar-id x)]
              (e/lam name type (if (.hasMVar ^ansatz.kernel.Expr body)
                                 (meta/abstract-fvars body [id]) (e/abstract1 body id))
                     (or info :default)))) body (reverse xs)))
(defn intro1 [ctx id]
  (with-goal! ctx id)
  (let [type (u/whnf ctx (goal-type ctx id))]
    (when-not (e/forall? type) (tactic-error! "intro: expected a forall" {:type type}))
    (let [x (u/local-decl ctx (e/forall-name type) (e/forall-type type) (e/forall-info type))
          child (fresh-mvar! ctx (e/instantiate1 (e/forall-body type) x))]
      (assign! ctx id (mk-lambda-fvars ctx [x] (e/mvar child)))
      [x child])))

(defn depends-on? [expr id]
  (not= expr (e/abstract1 expr id)))
(defn- dependent-locals [lctx ids]
  (first
   (reduce (fn [[ds ids] [id d]]
             (if (or (contains? ids id)
                     (some #(or (depends-on? (:type d) %)
                                (and (:value d) (depends-on? (:value d) %))) ids))
               [(conj ds id) (conj ids id)] [ds ids]))
           [[] (set ids)] (sort-by key lctx))))

(defn clear! [ctx id fid]
  (with-goal! ctx id)
  (let [t (goal-type ctx id) lctx (:lctx @ctx)]
    (when (or (depends-on? t fid)
              (some (fn [[i d]] (and (not= i fid) (depends-on? (:type d) fid))) lctx))
      (tactic-error! "clear: declaration has dependents" {:fvar-id fid}))
    (set-lctx! ctx (dissoc lctx fid))
    (let [child (fresh-mvar! ctx t)] (assign! ctx id (e/mvar child)) child)))

(defn subst-core
  "Subst.substCore: revert dependent locals, transport the target, reintroduce
   the dependent telescope, and return its substitution and new goal."
  [ctx id h-id symm incoming]
  (with-goal! ctx id)
  (let [lctx (:lctx @ctx)
        [head args] (e/get-app-fn-args (u/whnf ctx (:type (get lctx h-id))))]
    (when-not (and (e/const? head) (= "Eq" (str (e/const-name head))) (= 3 (count args)))
      (tactic-error! "subst: equality expected" {:hyp h-id}))
    (let [[type lhs rhs] args a (if symm rhs lhs) b (if symm lhs rhs)]
      (when-not (and (e/fvar? a) (not (depends-on? b (e/fvar-id a))))
        (tactic-error! "subst: variable expected without occurrence in replacement" {:lhs a :rhs b}))
      (let [aid (e/fvar-id a)
            deps (vec (remove #{aid h-id} (dependent-locals lctx #{aid h-id})))
            ds (mapv e/fvar deps)
            target (u/mk-forall-fvars ctx ds (goal-type ctx id))
            dep-elim (depends-on? target h-id)
            h (e/fvar h-id) ulevel (u/get-level ctx type)
            refl (u/mk-eq-refl ctx b)
            eq-symm (fn [x y h] (u/app (u/const' "Eq.symm" [ulevel]) [type x y h]))
            major (if symm h (eq-symm a b h))
            motive (if dep-elim
                     (if symm
                       (u/mk-lambda-fvars ctx [a h] target)
                       (let [ha (u/local-decl ctx "_h" (u/mk-eq ctx b a))]
                         (u/mk-lambda-fvars ctx [a ha]
                                            (subst/apply {h-id (eq-symm b a ha)} target))))
                     (u/mk-lambda-fvars ctx [a] target))
            base-subst {aid b h-id refl}
            target-new (subst/apply base-subst (goal-type ctx id))]
        (set-lctx! ctx (apply dissoc lctx aid h-id deps))
        (let [[new-ds s]
              (reduce (fn [[xs s] old]
                        (let [d (get lctx old)
                              x (u/local-decl ctx (:name d) (subst/apply s (:type d)) (:info d))]
                          [(conj xs x) (subst/insert s old x)])) [[] base-subst] deps)
              child (fresh-mvar! ctx (subst/apply s target-new))
              minor (mk-lambda-fvars ctx new-ds (e/mvar child))
              _ (set-lctx! ctx lctx)
              value (if dep-elim
                      (u/app (u/const' "Eq.rec" [(u/get-level ctx target) ulevel])
                             [type b motive minor a major])
                      (u/mk-eq-ndrec ctx type b motive minor a major))]
          ;; Restore the old context to apply the reverted dependent arguments.
          (set-lctx! ctx lctx)
          (assign! ctx id (u/app value ds))
          [(subst/append incoming s) child])))))

(defn- has-indep-indices [ctx major indices]
  (and (every? e/fvar? indices) (= (count indices) (count (set indices)))
       (every? (fn [[fid d]]
                 (or (= fid major) (some #(= fid (e/fvar-id %)) indices)
                     (not-any? #(depends-on? (:type d) (e/fvar-id %)) indices)))
               (:lctx @ctx))))

(defn get-inductive-universe-and-params [ctx type]
  (let [[f args] (e/get-app-fn-args (u/whnf ctx type))
        ci (when (e/const? f) (env/lookup (:env @ctx) (e/const-name f)))]
    (when-not (and ci (.isInduct ci))
      (tactic-error! "cases: inductive type expected" {:type type}))
    [(e/const-levels f) (subvec args 0 (.numParams ci))]))

(defn induction-cases-on [ctx id major]
  (with-goal! ctx id)
  (let [lctx (:lctx @ctx) x (e/fvar major)
        [f args] (e/get-app-fn-args (u/whnf ctx (u/infer-type ctx x)))
        ind (env/lookup! (:env @ctx) (e/const-name f))
        np (.numParams ind) ni (.numIndices ind)
        params (subvec args 0 np) indices (subvec args np)
        us (e/const-levels f)
        cn (name/mk-str (.name ind) "casesOn")
        ci (env/lookup! (:env @ctx) cn)
        reverting (set (conj (mapv e/fvar-id indices) major))
        deps (vec (remove reverting (dependent-locals lctx reverting)))
        ds (mapv e/fvar deps)
        target (goal-type ctx id)
        motive (u/mk-lambda-fvars ctx (conj indices x) (u/mk-forall-fvars ctx ds target))
        levels (if (> (count (.levelParams ci)) (count us))
                 (into [(u/get-level ctx target)] us) us)
        start (u/app (e/const' cn levels) (concat params [motive] indices [x]))
        base (apply dissoc lctx (concat reverting deps))
        [value _ subgoals]
        (reduce (fn [[value value-type subgoals] ctor-name]
                  (set-lctx! ctx lctx)
                  (let [ct (env/lookup! (:env @ctx) ctor-name)
                        t (u/whnf ctx value-type)
                        minor-type (e/forall-type t)]
                    (set-lctx! ctx base)
                    (let [[vs body] (u/forall-telescope ctx minor-type (+ (.numFields ct) (count deps)))
                          fields (subvec vs 0 (.numFields ct))
                          extra (subvec vs (.numFields ct))
                          ctor-app (u/app (e/const' ctor-name us) (concat params fields))
                          ret-args (e/get-app-args (u/whnf ctx (u/infer-type ctx ctor-app)))
                          s (reduce (fn [s [old new]] (subst/insert s old new)) {}
                                    (concat (map vector (map e/fvar-id indices) (subvec ret-args np))
                                            [[major ctor-app]] (map vector deps extra)))
                          child (fresh-mvar! ctx body)
                          minor (mk-lambda-fvars ctx vs (e/mvar child))]
                      [(e/app value minor) (e/instantiate1 (e/forall-body t) minor)
                       (conj subgoals {:mvar-id child :ctor-name ctor-name :fields fields :subst s})])))
                [start (u/infer-type ctx start) []] (.ctors ind))]
    (set-lctx! ctx lctx)
    (assign! ctx id (u/app value ds))
    subgoals))

(defn generalize-indices [ctx id major]
  (with-goal! ctx id)
  (let [x (e/fvar major) type (u/whnf ctx (u/infer-type ctx x))
        [f args] (e/get-app-fn-args type) ind (env/lookup! (:env @ctx) (e/const-name f))
        np (.numParams ind) indices (subvec args np)
        ia (u/app f (subvec args 0 np))
        [new-indices _] (u/forall-telescope ctx (u/infer-type ctx ia) (.numIndices ind))
        new-x (u/local-decl ctx (:name (get (:lctx @ctx) major)) (u/app ia new-indices))
        pairs (mapv vector (conj indices x) (conj new-indices new-x))
        eqs (mapv (fn [[a b]] (u/local-decl ctx "h" (u/mk-eq-heq ctx a b))) pairs)
        refls (mapv (fn [[a b]]
                      (if (tc/is-def-eq @ctx (u/infer-type ctx a) (u/infer-type ctx b))
                        (u/mk-eq-refl ctx a)
                        (u/app (u/const' "HEq.refl" [(u/get-level ctx (u/infer-type ctx a))])
                               [(u/infer-type ctx a) a]))) pairs)
        child-type (u/mk-forall-fvars ctx eqs (goal-type ctx id))
        ;; The original locals remain available during the generalized split.
        _ (set-lctx! ctx (apply dissoc (:lctx @ctx) (map e/fvar-id eqs)))
        child (fresh-mvar! ctx child-type)]
    (assign! ctx id (u/app (mk-lambda-fvars ctx (conj new-indices new-x) (e/mvar child))
                          (concat (conj indices x) refls)))
    {:mvar-id child :indices-fvar-ids (mapv e/fvar-id new-indices)
     :fvar-id (e/fvar-id new-x) :num-eqs (count eqs)}))

(defn- constructor-app? [ctx expr]
  (let [expr (u/whnf ctx expr)
        expr (if (e/lit-nat? expr)
               (if (zero? (e/lit-nat-val expr)) (u/const' "Nat.zero" [])
                   (e/app (u/const' "Nat.succ" []) (e/lit-nat (dec (e/lit-nat-val expr))))) expr)
        [f args] (e/get-app-fn-args expr)
        ci (when (e/const? f) (env/lookup (:env @ctx) (e/const-name f)))]
    (when (and ci (.isCtor ci)) {:info ci :args args :expr expr :us (e/const-levels f)})))

(defn- mk-no-confusion [ctx target type a b h]
  ;; AppBuilder.lean mkNoConfusion: ctorIdx for disjoint constructors, and
  ;; the per-constructor noConfusion declaration for an injective constructor.
  (let [{ca :info aa :args us :us} (constructor-app? ctx a)
        {cb :info ba :args} (constructor-app? ctx b)
        [ih ia] (e/get-app-fn-args (u/whnf ctx type))
        ind (.inductName ca) v (u/get-level ctx target)]
    (if (not= (.name ca) (.name cb))
      (u/app (u/const' "False.elim" [v])
             [target (u/app (u/const' "noConfusion_of_Nat" [(u/get-level ctx type)])
                             [type (u/app (e/const' (name/mk-str ind "ctorIdx") us) ia) a b h])])
      (if (zero? (.numFields ca))
        (let [p (u/local-decl ctx "P" target)] (u/mk-lambda-fvars ctx [p] p))
        (let [n (name/mk-str (.name ca) "noConfusion")
              ci (env/lookup! (:env @ctx) n)
              np (.numParams ca)
              start (u/app (e/const' n (into [v] us))
                           (concat (subvec ia 0 np) [target] (subvec aa np) (subvec ba np)))
              arity (loop [t (.type ci) n 0]
                      (if (e/forall? t) (recur (e/forall-body t) (inc n)) n))
              neqs (- arity (+ np (* 2 (.numFields ca)) 3))
              start (reduce (fn [val _]
                              (let [eq (e/forall-type (u/whnf ctx (u/infer-type ctx val)))
                                    [f as] (e/get-app-fn-args eq) x (nth as 1)]
                                (e/app val (if (= "HEq" (str (e/const-name f)))
                                             (u/app (u/const' "HEq.refl" [(u/get-level ctx (u/infer-type ctx x))])
                                                    [(u/infer-type ctx x) x])
                                             (u/mk-eq-refl ctx x))))) start (range neqs))
              eq (e/forall-type (u/whnf ctx (u/infer-type ctx start)))
              heq? (= "HEq" (str (e/const-name (e/get-app-fn eq))))]
          (e/app start (if heq?
                         (u/app (u/const' "heq_of_eq" [(u/get-level ctx type)]) [type a b h]) h)))))))

(defn unify-eqs? [ctx num-eqs id s]
  (loop [n num-eqs id id s s steps 0]
    (when (>= steps 1000) (tactic-error! "cases: maximum recursion depth (1000) exceeded" {}))
    (if (zero? n) [id s]
        (let [[h child] (intro1 ctx id) hid (e/fvar-id h)]
          (with-goal! ctx child)
          (let [eq-type (u/whnf ctx (u/infer-type ctx h))
                [f args] (e/get-app-fn-args eq-type)
                heq? (= "HEq" (str (e/const-name f)))]
            (if heq?
              (let [[ta a tb b] args]
                (when-not (tc/is-def-eq @ctx ta tb)
                  (tactic-error! "cases: heterogeneous equality types are not definitionally equal" {:type eq-type}))
                (let [prf (u/app (u/const' "eq_of_heq" [(u/get-level ctx ta)]) [ta a b h])
                      eq (u/local-decl ctx (:name (u/decl ctx h)) (u/mk-eq ctx a b))
                      next (fresh-mvar! ctx (goal-type ctx child))]
                  (assign! ctx child (e/app (mk-lambda-fvars ctx [eq] (e/mvar next)) prf))
                  ;; Turn the asserted equality back into a leading forall for the loop.
                  (let [wrapped (fresh-mvar! ctx (u/mk-forall-fvars ctx [eq] (goal-type ctx next)))]
                    (assign! ctx next (e/app (e/mvar wrapped) eq))
                    (recur n wrapped s (inc steps)))))
              (let [[type a b] args
                    a (zonk ctx a) b (zonk ctx b)
                    variable (cond
                               (and (e/fvar? a) (e/fvar? b))
                               (if (< (e/fvar-id a) (e/fvar-id b)) [b a true] [a b false])
                               (e/fvar? a) [a b false]
                               (e/fvar? b) [b a true])]
                (cond
                  (and variable (not (depends-on? (second variable) (e/fvar-id (first variable)))))
                  (let [[s' next] (subst-core ctx child hid (nth variable 2) s)]
                    (recur (dec n) next s' (inc steps)))

                  (tc/is-def-eq @ctx a b)
                  (recur (dec n) (clear! ctx child hid) s (inc steps))

                  (and (constructor-app? ctx a) (constructor-app? ctx b))
                  (let [val (mk-no-confusion ctx (goal-type ctx child) type a b h)
                        ca (:info (constructor-app? ctx a)) cb (:info (constructor-app? ctx b))]
                    (if (not= (.name ca) (.name cb))
                      (do (assign! ctx child val) nil)
                      (let [vt (u/whnf ctx (u/infer-type ctx val))
                            next (fresh-mvar! ctx (e/forall-type vt))
                            nnew (count (remove #(lvl/level-zero? (u/get-level ctx (u/infer-type ctx %)))
                                                (subvec (:args (constructor-app? ctx a)) (.numParams ca))))]
                        (assign! ctx child (e/app val (e/mvar next)))
                        (recur (+ (dec n) nnew) next s (inc steps)))))

                  :else (tactic-error! "cases: dependent elimination failed to solve equation" {:type eq-type})))))))))

(defn cases [ctx id major]
  (with-goal! ctx id)
  (let [[f args] (e/get-app-fn-args (u/whnf ctx (u/infer-type ctx (e/fvar major))))
        ind (when (e/const? f) (env/lookup (:env @ctx) (e/const-name f)))]
    (when-not (and ind (.isInduct ind)) (tactic-error! "cases: inductive type expected" {:major major}))
    (let [indices (subvec args (.numParams ind))]
      (if (has-indep-indices ctx major indices)
        (induction-cases-on ctx id major)
        (let [g (generalize-indices ctx id major)
              subgoals (induction-cases-on ctx (:mvar-id g) (:fvar-id g))]
          (vec (keep (fn [sg]
                       (when-let [[child s] (unify-eqs? ctx (:num-eqs g) (:mvar-id sg) (:subst sg))]
                         (assoc sg :mvar-id child :subst s :fields (mapv #(subst/apply s %) (:fields sg)))))
                     subgoals)))))))
