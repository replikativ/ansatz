(ns ansatz.elab.structural-eqns
  "Constructor equation fast path for `brecOn` definitions. Lean Structural/Eqns
   starts with reflexivity before unfolding and splitting; use that first when
   the matcher has one structural discriminant. Leaf splitting follows general
   Elab/PreDefinition/Eqns.lean mkEqnTypes (55f80e10a3)."
  (:require [ansatz.kernel.env :as env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.tc :as tc]
            [ansatz.kernel.reduce :as red]
            [ansatz.elab.eqns :as eqns]
            [ansatz.meta.constructions.util :as u]
            [ansatz.meta.match.matcher-app :as matcher-app]
            [ansatz.meta.fvar-subst :as subst])
  (:import [ansatz.kernel TypeChecker]))

(defn- reduce-matcher [environment lctx expr matcher-name ind-name]
  ;; Evaluate the source matcher on a constructor, preserving the RHS head.
  ;; Unrestricted whnf unfolds Nat.add and other recursive calls into their
  ;; brecOn encodings, which makes the equation unusable by simp.
  (let [checker (TypeChecker. environment)]
    (.setTransparency checker 0)
    (.setDeltaAllowSet checker
                       (java.util.HashSet. [matcher-name (name/mk-str ind-name "casesOn")]))
    (doseq [[fid decl] lctx]
      (.addLocal checker (long fid) (str (:name decl)) (:type decl)))
    (.whnf (.getReducer checker) expr)))

(defn- fvar-ids [x]
  (let [ids (volatile! #{})]
    (subst/map-expr-fvars (fn [id] (vswap! ids conj id) (e/fvar id)) x)
    @ids))

(defn- prove-by-splitting [ctx lhs rhs candidates depth]
  (let [result-type (u/infer-type ctx lhs)
        level (u/get-level ctx result-type)
        refl (u/app (u/const' "Eq.refl" [level]) [result-type lhs])]
    (if (tc/is-def-eq @ctx lhs rhs)
      refl
      (when (pos? depth)
        (some
         (fn [x]
           (try
             (let [[head args] (e/get-app-fn-args (u/whnf ctx (u/infer-type ctx x)))
                   ind (when (e/const? head)
                         (env/lookup (:env @ctx) (e/const-name head)))]
               (when (and ind (.isInduct ind)
                          ;; an indexed family splits when its indices are distinct variables
                          ;; outside the parameters: the motive generalizes them with the major
                          (let [indices (subvec args (.numParams ind))]
                            (and (every? e/fvar? indices) (= (count indices) (count (distinct indices)))
                                 (not-any? (fn [i] (some #(contains? (fvar-ids %) (e/fvar-id i)) (subvec args 0 (.numParams ind))))
                                           indices))))
                 (let [levels (vec (e/const-levels head))
                       params (subvec args 0 (.numParams ind))
                       indices (subvec args (.numParams ind))
                       cases-name (name/mk-str (.name ind) "casesOn")
                       cases-info (env/lookup! (:env @ctx) cases-name)
                       cases-levels (if (> (count (.levelParams cases-info)) (count levels))
                                      (into [lvl/zero] levels) levels)
                       goal (u/app (u/const' "Eq" [level]) [result-type lhs rhs])
                       ;; variables whose types depend on the major or its indices are generalized
                       ;; with them (Lean's cases reverts them), in declaration order
                       split-ids (set (map e/fvar-id (conj indices x)))
                       scope (loop [todo (vec (fvar-ids goal)) seen #{}]
                               ;; the goal's free variables and, transitively, those in their types
                               (if-let [fid (peek todo)]
                                 (if (seen fid) (recur (pop todo) seen)
                                     (recur (into (pop todo) (some-> (get (:lctx @ctx) fid) :type fvar-ids))
                                            (conj seen fid)))
                                 seen))
                       deps (reduce (fn [deps fid]
                                      (let [t (:type (get (:lctx @ctx) fid))
                                            ids (into split-ids (map e/fvar-id) deps)]
                                        (if (and t (not (split-ids fid)) (some ids (fvar-ids t)))
                                          (conj deps (e/fvar fid)) deps)))
                                    [] (sort scope))
                       motive (u/mk-lambda-fvars ctx (conj indices x) (u/mk-forall-fvars ctx deps goal))
                       other-candidates (vec (remove (set (concat indices [x] deps)) candidates))
                       minors
                       (mapv
                        (fn [ctor-name]
                          (let [ctor (env/lookup! (:env @ctx) ctor-name)
                                ctor-type (u/instantiate-forall ctx
                                                                (u/infer-type ctx
                                                                              (e/const' ctor-name levels))
                                                                params)
                                [fields ctor-result] (u/forall-telescope ctx ctor-type (.numFields ctor))
                                ctor-app (u/app (e/const' ctor-name levels) (concat params fields))
                                sub (into (mapv vector indices (subvec (vec (e/get-app-args ctor-result)) (.numParams ind)))
                                          [[x ctor-app]])
                                [deps' sub] (reduce (fn [[ds sub] d]
                                                      (let [dl (u/local-decl ctx (:name (u/decl ctx d))
                                                                             (u/replace-fvars (u/infer-type ctx d) sub))]
                                                        [(conj ds dl) (conj sub [d dl])]))
                                                    [[] sub] deps)
                                lhs' (u/replace-fvars lhs sub)
                                rhs' (u/replace-fvars rhs sub)
                                proof (prove-by-splitting ctx lhs' rhs'
                                                          (into (into other-candidates fields) deps')
                                                          (dec depth))]
                            (when proof (u/mk-lambda-fvars ctx (into fields deps') proof))))
                        (.ctors ind))]
                   (when (every? some? minors)
                     (u/app (u/app (e/const' cases-name cases-levels)
                                   (concat params [motive] indices [x] minors))
                            deps)))))
             (catch Exception _ nil)))
         candidates)))))

(defn constructor-equations
  "Kernel check constructor equations for a structurally recursive matcher.
   Returns checked names and per-constructor errors for equations needing
   Lean's general split-based proof pass."
  [environment fn-name source self-id rec-pos arity]
  (let [ctx (u/context environment)
        [xs source-body] (matcher-app/lambda-telescope ctx source arity)
        _ (swap! (:next-id @ctx) max self-id)
        major (nth xs rec-pos)
        [head ind-args] (e/get-app-fn-args (u/infer-type ctx major))
        ind (env/lookup! environment (e/const-name head))
        params (subvec ind-args 0 (.numParams ind))
        indices (subvec ind-args (.numParams ind))
        _ (when-not (and (every? e/fvar? indices)
                         (= (count indices) (count (distinct indices)))
                         (every? (set xs) indices))
            (throw (ex-info "Indexed constructor equations need distinct parameter indices"
                            {:inductive (.name ind)})))
        index-positions (mapv #(.indexOf ^java.util.List xs %) indices)
        levels (vec (e/const-levels head))
        fconst (e/const' (name/from-string (str fn-name)) [])
        ;; A leading `let` is zeta-reduced before finding the match auxiliary;
        ;; its runtime/proof source remains the original let expression.
        matcher-name (e/const-name
                      (e/get-app-fn
                       (red/whnf-no-delta environment source-body (:lctx @ctx))))]
    (reduce
     (fn [{:keys [env names errors]} ctor-name]
       (try
         (u/set-env! ctx env)
         (let [ctor (env/lookup! env ctor-name)
               ctor-type (u/instantiate-forall ctx
                                               (u/infer-type ctx (e/const' ctor-name levels))
                                               params)
               [fields ctor-result] (u/forall-telescope ctx ctor-type (.numFields ctor))
               ctor-result-args (e/get-app-args ctor-result)
               result-indices (subvec ctor-result-args (.numParams ind))
               index-subst (mapv vector indices result-indices)
               ;; A non-index parameter after an index may have a dependent
               ;; type. Specialize it to the constructor result indices before
               ;; binding it in the equation theorem.
               [param-subst unchanged-params specialized-params]
               (reduce (fn [[subst unchanged specialized] [pos x]]
                         (if (or (= pos rec-pos) (some #{pos} index-positions))
                           [subst unchanged specialized]
                           (let [type (u/replace-fvars (u/infer-type ctx x)
                                                       (into index-subst subst))
                                 x' (if (= type (u/infer-type ctx x))
                                      x
                                      (u/local-decl ctx "eqParam" type))]
                             [(conj subst [x x'])
                              (cond-> unchanged (= x x') (conj x'))
                              (cond-> specialized (not= x x') (conj x'))])))
                       [[] [] []] (map-indexed vector xs))
               substitutions (into index-subst param-subst)
               ctor-app (u/app (e/const' ctor-name levels) (concat params fields))
               actual-params (mapv (fn [pos x]
                                     (if (= pos rec-pos)
                                       ctor-app
                                       (u/replace-fvars x substitutions)))
                                   (range (count xs)) xs)
               lhs (u/app fconst actual-params)
               rhs (reduce-matcher env (:lctx @ctx)
                                   (u/replace-fvars source-body
                                                    (into [[(e/fvar self-id) fconst]
                                                           [major ctor-app]]
                                                          substitutions))
                                   matcher-name (e/const-name head))
               binders (vec (concat unchanged-params fields specialized-params))
               leaves (eqns/mk-eqn-types ctx lhs rhs binders #{(name/from-string (str fn-name))})]
           (reduce
            (fn [{:keys [env names errors]} {:keys [lhs rhs binders]}]
              (u/set-env! ctx env)
              (let [result-type (u/infer-type ctx lhs)
                    level (u/get-level ctx result-type)
                    eq-type (u/app (u/const' "Eq" [level]) [result-type lhs rhs])
                    theorem-type (u/mk-forall-fvars ctx binders eq-type)
                    eq-name (name/from-string (str fn-name ".eq_" (inc (+ (count names) (count errors)))))
                    proof (or (prove-by-splitting ctx lhs rhs binders 2)
                              (throw (ex-info "Structural equation needs Lean's general proof pass"
                                              {:equation (str eq-name)})))
                    theorem-value (u/mk-lambda-fvars ctx binders proof)
                    env (env/check-constant env (env/mk-thm eq-name [] theorem-type theorem-value))]
                {:env env :names (conj names eq-name) :errors errors}))
            {:env env :names names :errors errors} leaves))
         (catch Exception ex
           {:env env :names names
            :errors (conj errors [(name/from-string (str fn-name ".eq_" (inc (+ (count names) (count errors))))) ex])})))
     {:env environment :names [] :errors []}
     (.ctors ind))))

(defn- find-brec-on
  "Structural/Eqns.lean findBRecOnLHS: the `.brecOn` application in `lhs` (possibly under
   projections, with extra arguments) and the context `fun x => …x… ` around it."
  [ctx lhs]
  (letfn [(go [x k]
              (let [[f args] (e/get-app-fn-args x)]
                (cond
                  (e/proj? f)
                  (go (e/proj-struct f) (fn [app c hole]
                                          ;; rebuild the projection and its trailing arguments
                                          (k app (u/app (e/proj (e/proj-type-name f) (e/proj-idx f) c) args) hole)))
                  (and (e/const? f) (re-find #"\.brecOn(_\d+)?$" (name/->string (e/const-name f))))
                  (let [arity (loop [t (u/infer-type ctx f) n 0] (if (e/forall? t) (recur (e/forall-body t) (inc n)) n))]
                    (when (<= arity (count args))
                      (let [app (u/app f (take arity args))
                            hole (u/local-decl ctx "x" (u/infer-type ctx app))]
                        (k app (u/app hole (drop arity args)) hole))))
                  :else nil)))]
    (go lhs (fn [app c hole] [app c hole]))))

(defn- brec-on-rewrite
  "Structural/Eqns.lean goUnfold: delta the head of `lhs`, find its `.brecOn` application and
   rewrite it once with `.brecOn.eq`. Returns [proof-of `lhs = lhs'`, lhs'] or nil."
  [ctx lhs]
  (let [[f args] (e/get-app-fn-args lhs)
        ci (when (e/const? f) (env/lookup (:env @ctx) (e/const-name f)))]
    (when (and ci (.isDef ci))
      (let [unfolded (u/beta (e/instantiate-level-params (.value ci) (zipmap (.levelParams ci) (e/const-levels f))) args)
            found (find-brec-on ctx unfolded)]
        (when-let [[app context-body hole] found]
          (let [[bf bargs] (e/get-app-fn-args app)
                thm-name (name/mk-str (e/const-name bf) "eq")]
            (when (env/lookup (:env @ctx) thm-name)
              (let [thm (u/app (e/const' thm-name (e/const-levels bf)) bargs)
                    [_ _ rw-rhs] (e/get-app-args (u/infer-type ctx thm))
                    context (u/mk-lambda-fvars ctx [hole] context-body)
                    ty (u/infer-type ctx app)
                    rt (u/infer-type ctx context-body)
                    congr (u/app (u/const' "congrArg" [(u/get-level ctx ty) (u/get-level ctx rt)])
                                 [ty rt app rw-rhs context thm])]
                [congr (u/beta context [rw-rhs])]))))))))

(defn unfold-equation
  "Lean Meta/Eqns.lean getUnfoldEqnFor? / Structural/Eqns.lean mkProof: `f.eq_def :
   ∀ params, f params = body`, the body being the predefinition with recursive calls to `f`
   itself. As Lean: reflexivity first; otherwise unfold `f` to its `.brecOn` application and
   rewrite it once with `.brecOn.eq`, then split the residual on the structural argument (an
   indexed family with its index variables) and its fields until both sides are definitionally
   equal. Kernel-checked. Returns the extended env; throws when no proof is found."
  [environment fn-name source self-id rec-pos arity]
  (let [ctx (u/context environment)
        [xs source-body] (matcher-app/lambda-telescope ctx source arity)
        _ (swap! (:next-id @ctx) max self-id)
        fconst (e/const' (name/from-string (str fn-name)) [])
        lhs (u/app fconst xs)
        rhs (u/replace-fvars source-body [[(e/fvar self-id) fconst]])
        result-type (u/infer-type ctx lhs)
        level (u/get-level ctx result-type)
        eq-type (u/app (u/const' "Eq" [level]) [result-type lhs rhs])
        eq-name (name/from-string (str fn-name ".eq_def"))
        major (nth xs rec-pos)
        ;; the major's index variables split with it
        candidates (into [major] (filter #(e/fvar? %) (e/get-app-args (u/infer-type ctx major))))
        admit (fn [proof]
                (env/check-constant environment
                                    (env/mk-thm eq-name [] (u/mk-forall-fvars ctx xs eq-type)
                                                (u/mk-lambda-fvars ctx xs proof))))
        attempt (fn [f] (try (some-> (f) admit) (catch Exception _ nil)))]
    ;; each candidate proof is admitted inside its own attempt, so a failing rewrite falls
    ;; back to direct splitting
    (or (attempt #(when (tc/is-def-eq @ctx lhs rhs) (u/mk-eq-refl ctx lhs)))
        (attempt #(when-let [[rw lhs'] (brec-on-rewrite ctx lhs)]
                    (when-let [rest (prove-by-splitting ctx lhs' rhs candidates 3)]
                      (u/app (u/const' "Eq.trans" [level]) [result-type lhs lhs' rhs rw rest]))))
        (attempt #(prove-by-splitting ctx lhs rhs candidates 3))
        (throw (ex-info "Structural unfold equation: no proof found by unfolding `.brecOn` and splitting"
                        {:equation (str eq-name)})))))
