(ns ansatz.meta.app-builder
  "Lean 4.33.1 Meta/AppBuilder.lean: constructorApp'? and mkNoConfusion.
   Shared proof construction for cases and the reduceCtorEq simproc."
  (:require [ansatz.kernel.expr :as e]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [ansatz.meta.constructions.util :as u]
            [ansatz.meta.constructions.no-confusion :as no-confusion]))

(defn constructor-app? [ctx expr]
  (let [expr (u/whnf ctx expr)
        expr (if (e/lit-nat? expr)
               (if (zero? (e/lit-nat-val expr)) (u/const' "Nat.zero" [])
                   (e/app (u/const' "Nat.succ" []) (e/lit-nat (dec (e/lit-nat-val expr))))) expr)
        [f args] (e/get-app-fn-args expr)
        ci (when (e/const? f) (env/lookup (:env @ctx) (e/const-name f)))]
    (when (and ci (.isCtor ci)) {:info ci :args args :expr expr :us (e/const-levels f)})))

(defn- ensure-no-confusion! [ctx ctor]
  ;; Lean realizes constructor noConfusion on demand (NoConfusion.lean).
  ;; Bundled environments may contain the parent declarations but omit its
  ;; constructor auxiliaries, so preserve each prerequisite already installed.
  (let [n (name/mk-str (.name ctor) "noConfusion")]
    (when-not (env/lookup (:env @ctx) n)
      (let [ind (.inductName ctor)
            out (:env @ctx)
            out (if (env/lookup out (name/mk-str ind "noConfusionType")) out
                    (no-confusion/mk-no-confusion-type out ind))
            out (if (env/lookup out (name/mk-str ind "noConfusion")) out
                    (no-confusion/mk-no-confusion-core-imp out ind))
            out (no-confusion/mk-no-confusion-ctors out ind)]
        (let [saved @ctx]
          (u/set-env! ctx out)
          (swap! ctx #(merge saved %)))))))

(defn mk-no-confusion [ctx target type a b h]
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
        (let [_ (ensure-no-confusion! ctx ca)
              n (name/mk-str (.name ca) "noConfusion")
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

