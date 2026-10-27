(ns ansatz.meta.constructions.ctor-idx
  "Lean/Meta/Constructions/CtorIdx.lean, mkCtorIdx (55f80e10)."
  (:require [ansatz.meta.constructions.util :as u]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]))

(defn mk-ctor-idx [env n]
  (let [info (env/lookup! env (name/from-string (str n))) ctx (u/context env)
        cases (env/lookup! env (name/from-string (str n ".casesOn")))]
    (if (or (.isUnsafe info) (u/prop-former? ctx (.type info))
            (<= (count (.levelParams cases)) (count (.levelParams info)))
            (env/lookup env (name/from-string (str n ".ctorIdx")))) env
      (let [us (mapv lvl/param (.levelParams info))
            [xs _] (u/forall-telescope ctx (.type info) (+ (.numParams info) (.numIndices info)))
            _ (u/implicit! ctx xs)
            params (subvec xs 0 (.numParams info)) indices (subvec xs (.numParams info))
            x (u/local-decl ctx "x" (u/app (u/const' n us) xs))
            nat (u/const' "Nat" [])
            val (if (= 1 (count (.ctors info))) (e/lit-nat 0)
                  (u/app (u/const' (str n ".casesOn") (into [(lvl/succ lvl/zero)] us))
                    (concat params [(u/mk-lambda-fvars ctx (conj indices x) nat)] indices [x]
                      (map (fn [c]
                             (let [ci (env/lookup! env c)
                                   [ys _] (u/forall-telescope ctx
                                            (u/instantiate-forall ctx (.type ci) params) (.numFields ci))]
                               (u/mk-lambda-fvars ctx ys (e/lit-nat (.cidx ci))))) (.ctors info)))))
            decl (u/mk-definition ctx (str n ".ctorIdx") (vec (.levelParams info)) (conj xs x) nat val)
            decl (u/mk-definition-val-inferring-unsafe env (.name decl) (vec (.levelParams info))
                     (.type decl) (.value decl) {:regular (inc (u/get-max-height env (.value decl)))})
            env (env/check-constant env decl)]
        ;; Lean also emits this deprecated alias for enumeration types.
        (if (u/is-enum-type? env info)
          (u/add-definition env ctx (str n ".toCtorIdx") (vec (.levelParams info)) []
                            (u/mk-forall-fvars ctx (conj xs x) nat) (u/const' (str n ".ctorIdx") us))
          env)))))
