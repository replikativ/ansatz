(ns ansatz.elab.eqns
  "Lean Elab/PreDefinition/Eqns.lean, mkEqnTypes/findMatchToSplit? (55f80e10a3).
   Split source matchers into leaf equation types before proving the equations."
  (:require [ansatz.kernel.expr :as e]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [ansatz.meta.constructions.util :as u]
            [ansatz.meta.match.matcher-app :as matcher-app]))

(def ^:dynamic *max-rec-depth* 512)

(defn- check-depth! [depth]
  (when (> depth *max-rec-depth*)
    (throw (ex-info "Tactic error: equation generation maxRecDepth exceeded"
                    {:kind :tactic-error :limit :max-rec-depth :max-rec-depth *max-rec-depth*}))))

(defn- children [x]
  (case (e/tag x)
    :app (let [[f args] (e/get-app-fn-args x)] (into [f] args))
    :lam [(e/lam-type x) (e/lam-body x)]
    :forall [(e/forall-type x) (e/forall-body x)]
    :let [(e/let-type x) (e/let-value x) (e/let-body x)]
    :mdata [(e/mdata-expr x)]
    :proj [(e/proj-struct x)]
    []))

(defn find-match-to-split?
  "Lean findMatchToSplit? with deepRecursiveSplit: find a closed matcher with a
   free-variable discriminant. Source recursive calls remain folded here, so
   their implementation recursors are never traversed."
  [environment expr _decl-names exception-set]
  (loop [todo [expr]]
    (when-let [x (peek todo)]
      (let [todo (pop todo)
            matcher (when-not (or (e/has-loose-bvars? x) (contains? exception-set x))
                      (matcher-app/match-matcher-app? environment x))]
        (cond
          (and matcher (some e/fvar? (:discrs matcher))) matcher
          (let [head (e/get-app-fn x)]
            (and (e/const? head) (= "WellFounded.fix" (name/->string (e/const-name head)))))
          (recur todo)
          :else (recur (into todo (reverse (children x)))))))))

(defn- simp-match [ctx expr depth]
  ;; mkEqnTypes's simpMatch? uses Meta.reduceMatcher? on constructor discriminants.
  ;; Reuse that reducer rather than unfolding ordinary definitions in a branch.
  (check-depth! depth)
  (let [visit #(simp-match ctx % (inc depth))
        x (case (e/tag expr)
            :app (let [[f args] (e/get-app-fn-args expr)] (u/app (visit f) (mapv visit args)))
            :let (visit (e/instantiate1 (e/let-body expr) (e/let-value expr)))
            :mdata (visit (e/mdata-expr expr))
            :proj (e/proj (e/proj-type-name expr) (e/proj-idx expr) (visit (e/proj-struct expr)))
            expr)]
    (if (e/has-loose-bvars? x) x
        (if-let [step ((requiring-resolve 'ansatz.tactic.simp/try-reduce-matcher) @ctx x)]
          (if (= x (:expr step)) x (simp-match ctx (:expr step) (inc depth)))
          x))))

(defn- specialize-binders [ctx binders discr ctor-app fields]
  (reduce
   (fn [[subst out] x]
     (if (= x discr)
       [subst (into out fields)]
       (let [decl (u/decl ctx x)
             type (u/replace-fvars (:type decl) subst)
             x' (if (= type (:type decl)) x
                    (u/local-decl-preserving-name ctx decl type))]
         [(cond-> subst (not= x x') (conj [x x'])) (conj out x')])))
   [[[discr ctor-app]] []] binders))

(defn mk-eqn-types
  "Lean mkEqnTypes: simplify constructor matches, recursively split a free
   discriminant, and save leaves. Indexed discriminants remain for the general
   dependent split tactic; the outer structural constructor pass handles indices."
  [ctx lhs rhs binders decl-names]
  (letfn [(go [lhs rhs binders depth]
              (check-depth! depth)
              (let [rhs (simp-match ctx rhs 0)]
                (loop [exceptions #{}]
                  (if-let [matcher (find-match-to-split? (:env @ctx) rhs decl-names exceptions)]
                    (let [discr (some (fn [x] (when (and (e/fvar? x) (some #{x} binders)) x))
                                      (:discrs matcher))
                          [head args] (when discr (e/get-app-fn-args (u/whnf ctx (u/infer-type ctx discr))))
                          ind (when (e/const? head) (env/lookup (:env @ctx) (e/const-name head)))]
                      (if-not (and ind (.isInduct ind) (zero? (.numIndices ind)))
                        (recur (conj exceptions (matcher-app/to-expr matcher)))
                        (let [params (subvec args 0 (.numParams ind))
                              levels (vec (e/const-levels head))]
                          (into []
                                (mapcat
                                 (fn [ctor-name]
                                   (let [ctor (env/lookup! (:env @ctx) ctor-name)
                                         type (u/instantiate-forall ctx (u/infer-type ctx (e/const' ctor-name levels)) params)
                                         [fields _] (u/forall-telescope ctx type (.numFields ctor))
                                         ctor-app (u/app (e/const' ctor-name levels) (concat params fields))
                                         [subst binders] (specialize-binders ctx binders discr ctor-app fields)]
                                     (go (u/replace-fvars lhs subst) (u/replace-fvars rhs subst)
                                         binders (inc depth)))))
                                (.ctors ind)))))
                    [{:lhs lhs :rhs rhs :binders binders}]))))]
    (go lhs rhs binders 0)))
