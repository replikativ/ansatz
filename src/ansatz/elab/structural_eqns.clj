(ns ansatz.elab.structural-eqns
  "Constructor equation fast path for `brecOn` definitions. Lean Structural/Eqns
   starts with reflexivity before unfolding and splitting; use that first when
   the matcher has one unindexed structural discriminant."
  (:require [ansatz.kernel.env :as env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
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
        _ (when (pos? (.numIndices ind))
            (throw (ex-info "Indexed constructor equations need the general Lean proof pass"
                            {:inductive (.name ind)})))
        params (subvec ind-args 0 (.numParams ind))
        levels (vec (e/const-levels head))
        fconst (e/const' (name/from-string (str fn-name)) [])
        matcher-name (e/const-name (e/get-app-fn source-body))
        original-params (vec (keep-indexed (fn [i x] (when (not= i rec-pos) x)) xs))]
    (reduce
     (fn [{:keys [env names errors]} [i ctor-name]]
       (try
         (u/set-env! ctx env)
         (let [ctor (env/lookup! env ctor-name)
               ctor-type (u/instantiate-forall ctx
                                               (u/infer-type ctx (e/const' ctor-name levels))
                                               params)
               [fields _] (u/forall-telescope ctx ctor-type (.numFields ctor))
               ctor-app (u/app (e/const' ctor-name levels) (concat params fields))
               actual-params (assoc xs rec-pos ctor-app)
               lhs (u/app fconst actual-params)
               rhs (reduce-matcher env (:lctx @ctx)
                                   (u/replace-fvars source-body
                                                    [[(e/fvar self-id) fconst]
                                                     [major ctor-app]])
                                   matcher-name (e/const-name head))
               result-type (u/infer-type ctx lhs)
               level (u/get-level ctx result-type)
               eq-type (u/app (u/const' "Eq" [level]) [result-type lhs rhs])
               refl (u/app (u/const' "Eq.refl" [level]) [result-type lhs])
               binders (into original-params fields)
               theorem-type (u/mk-forall-fvars ctx binders eq-type)
               theorem-value (u/mk-lambda-fvars ctx binders refl)
               eq-name (name/from-string (str fn-name ".eq_" (inc i)))
               env (env/check-constant env (env/mk-thm eq-name [] theorem-type theorem-value))]
           {:env env :names (conj names eq-name) :errors errors})
         (catch Exception ex
           {:env env :names names
            :errors (conj errors [(name/from-string (str fn-name ".eq_" (inc i))) ex])})))
     {:env environment :names [] :errors []}
     (map-indexed vector (.ctors ind)))))
