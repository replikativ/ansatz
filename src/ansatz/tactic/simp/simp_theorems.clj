(ns ansatz.tactic.simp.simp-theorems
  "Lean 4.33.1 Meta/Tactic/Simp/SimpTheorems.lean:
   mkSimpEntryOfDeclToUnfold and unfoldEvenWithEqns."
  (:require [ansatz.eqns :as eqns]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [ansatz.meta.rec-ext :as rec-ext]))

(defn unfold-even-with-eqns [environment n]
  ;; Exports omit RecExt/smart-unfolding metadata. An eager local inventory
  ;; identifies definitions whose recursion status we know; imported equations
  ;; remain usable without guessing whether additional delta unfolding is safe.
  (and (some? (eqns/eqns-for environment n))
       (not (rec-ext/is-recursive-definition environment n))))

(defn mk-simp-entry-of-decl-to-unfold [environment n]
  (let [n (if (instance? ansatz.kernel.Name n) n (name/from-string (str n)))
        ci (env/lookup environment n)]
    (if-not (and ci (.isDef ci))
      []
      (let [equations (eqns/get-eqns-for? environment n)
            size (count equations)
            entries (mapv (fn [i equation]
                            {:kind :thm :name equation
                             :priority (if (> size 100)
                                         (if (= (inc i) size) 0 1)
                                         (- 100 i))})
                          (range size) equations)]
        (cond-> entries
          (or (not (seq equations)) (unfold-even-with-eqns environment n))
          (conj {:kind :to-unfold :name n}))))))
