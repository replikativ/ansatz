(ns ansatz.meta.constructions.rec-on
  "Lean/Meta/Constructions/RecOn.lean, mkRecOn (55f80e10)."
  (:require [ansatz.meta.constructions.util :as u]
            [ansatz.meta.constructions.cases-on :as cases-on]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]))

(declare mk-rec-on-from-rec)

(defn- mk-rec-on-via-cases-on
  "Lean 4.36 mkRecOnViaCasesOn?: `recOn := casesOn` when `casesOn` exists and is built from
   projections (a nonrecursive, index-free type: both have the same type)."
  [env n target]
  (let [cases (env/lookup env (name/from-string (str n ".casesOn")))]
    (when (and cases (cases-on/cases-on-via-projs? env n))
      (env/check-constant
       env (u/mk-definition-val-inferring-unsafe env target (vec (.levelParams cases)) (.type cases)
                                                 (u/const' (str n ".casesOn") (mapv lvl/param (.levelParams cases)))
                                                 :abbrev)))))

(defn mk-rec-on
  ([env n] (mk-rec-on env n (str n ".recOn")))
  ([env n target]
   (or (mk-rec-on-via-cases-on env n target)
       (mk-rec-on-from-rec env n target))))

(defn- mk-rec-on-from-rec
  ([env n target]
   (let [rec (env/lookup! env (name/from-string (str n ".rec")))
         ctx (u/context env)
         [xs t] (u/forall-telescope ctx (.type rec))
         ac (- (count xs) (.numMinors rec) (.numIndices rec) 1)
         vs (vec (concat (subvec xs 0 ac) (subvec xs (+ ac (.numMinors rec)))
                         (subvec xs ac (+ ac (.numMinors rec)))))
         val (u/app (u/const' (.name rec) (mapv lvl/param (.levelParams rec))) xs)]
     (u/add-definition env ctx target (vec (.levelParams rec)) vs t val))))
