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
            [ansatz.meta.match.matcher-app :as matcher-app])
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
               (when (and ind (.isInduct ind) (zero? (.numIndices ind)))
                 (let [levels (vec (e/const-levels head))
                       params (subvec args 0 (.numParams ind))
                       cases-name (name/mk-str (.name ind) "casesOn")
                       cases-info (env/lookup! (:env @ctx) cases-name)
                       cases-levels (if (> (count (.levelParams cases-info)) (count levels))
                                      (into [lvl/zero] levels) levels)
                       goal (u/app (u/const' "Eq" [level]) [result-type lhs rhs])
                       motive (u/mk-lambda-fvars ctx [x] goal)
                       other-candidates (vec (remove #{x} candidates))
                       minors
                       (mapv
                        (fn [ctor-name]
                          (let [ctor (env/lookup! (:env @ctx) ctor-name)
                                ctor-type (u/instantiate-forall ctx
                                                                (u/infer-type ctx
                                                                              (e/const' ctor-name levels))
                                                                params)
                                [fields _] (u/forall-telescope ctx ctor-type (.numFields ctor))
                                ctor-app (u/app (e/const' ctor-name levels) (concat params fields))
                                lhs' (u/replace-fvars lhs [[x ctor-app]])
                                rhs' (u/replace-fvars rhs [[x ctor-app]])
                                proof (prove-by-splitting ctx lhs' rhs'
                                                          (into other-candidates fields)
                                                          (dec depth))]
                            (when proof (u/mk-lambda-fvars ctx fields proof))))
                        (.ctors ind))]
                   (when (every? some? minors)
                     (u/app (e/const' cases-name cases-levels)
                            (concat params [motive x] minors))))))
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

(defn unfold-equation
  "Lean 4.33.1 Meta/Eqns.lean getUnfoldEqnFor? / Structural mkUnfoldEq: `f.eq_def :
   ∀ params, f params = body`, the body being the predefinition with recursive calls to `f`
   itself. Proved by splitting the structural argument (then its fields) until both sides are
   definitionally equal, and kernel-checked. Returns the extended env; throws when no
   split proves it."
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
        proof (or (prove-by-splitting ctx lhs rhs [(nth xs rec-pos)] 3)
                  (throw (ex-info "Structural unfold equation needs Lean's general proof pass"
                                  {:equation (str eq-name)})))]
    (env/check-constant environment
                        (env/mk-thm eq-name []
                                    (u/mk-forall-fvars ctx xs eq-type)
                                    (u/mk-lambda-fvars ctx xs proof)))))
