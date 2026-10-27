(ns ansatz.meta.constructions.rec-on
  "Lean/Meta/Constructions/RecOn.lean, mkRecOn (55f80e10)."
  (:require [ansatz.meta.constructions.util :as u]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]))

(defn mk-rec-on
  ([env n] (mk-rec-on env n (str n ".recOn")))
  ([env n target]
   (let [rec (env/lookup! env (name/from-string (str n ".rec")))
         ctx (u/context env)
         [xs t] (u/forall-telescope ctx (.type rec))
         ac (- (count xs) (.numMinors rec) (.numIndices rec) 1)
         vs (vec (concat (subvec xs 0 ac) (subvec xs (+ ac (.numMinors rec)))
                         (subvec xs ac (+ ac (.numMinors rec)))))
         val (u/app (u/const' (.name rec) (mapv lvl/param (.levelParams rec))) xs)]
     (u/add-definition env ctx target (vec (.levelParams rec)) vs t val))))
