(ns ansatz.meta.constructions.ctor-elim
  "Lean/Meta/Constructions/CtorElim.lean and Meta/NatTable.lean (55f80e10)."
  (:require [ansatz.meta.constructions.util :as u]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]))

(defn reassoc-max [l]
  (letfn [(args [l] (if (lvl/max? l) (concat (args (lvl/max-lhs l)) (args (lvl/max-rhs l))) [l]))]
    (let [xs (vec (args l))]
      (reduce (fn [b a] (lvl/level-max a b)) (peek xs) (reverse (pop xs))))))
(defn max-levels [ctx es]
  (reassoc-max (lvl/simplify (reduce lvl/level-max (map #(u/get-level ctx %) es)))))
(defn mk-pulift [ctx r t] (e/app (u/const' "PULift" [r (u/get-level ctx t)]) t))
(defn with-mk-pulift-up [ctx t k]
  (let [t (u/whnf ctx t) h (e/get-app-fn t) a (first (e/get-app-args t))]
    (u/app (u/const' "PULift.up" (e/const-levels h)) [a (k a)])))
(defn mk-pulift-down [ctx x]
  (let [t (u/whnf ctx (u/infer-type ctx x))]
    (u/app (u/const' "PULift.down" (e/const-levels (e/get-app-fn t))) [(first (e/get-app-args t)) x])))
(defn mk-nat-lookup-table [ctx i type es]
  (when (empty? es) (throw (ex-info "Tactic error: mkNatLookupTable: empty table" {:kind :tactic-error})))
  (let [u (u/get-level ctx type)]
    (letfn [(go [start stop]
                (if (= (inc start) stop) (nth es start)
                    (let [mid (quot (+ start stop) 2)]
                      (u/app (u/const' "cond" [u])
                             [type (u/app (u/const' "Nat.ble" []) [i (e/lit-nat (dec mid))])
                              (go start mid) (go mid stop)]))))]
      (go 0 (count es)))))
(defn mk-nat-lookup-table-lifting [ctx n es]
  (let [u (max-levels ctx es)
        u' (reassoc-max (lvl/simplify (lvl/level-max u (lvl/succ lvl/zero))))]
    (mk-nat-lookup-table ctx n (e/sort' u') (mapv #(mk-pulift ctx u %) es))))

(defn- cases-data [env n]
  (let [info (env/lookup! env (name/from-string (str n)))
        cases (env/lookup! env (name/from-string (str n ".casesOn")))
        ctx (u/context env) [xs _] (u/forall-telescope ctx (.type cases))
        np (.numParams info) ni (.numIndices info) ls (mapv lvl/param (.levelParams cases))]
    {:info info :cases cases :ctx ctx :ls ls :v (first ls) :us (subvec ls 1)
     :params (subvec xs 0 np) :motive (nth xs np)
     :ism (subvec xs (inc np) (+ np ni 2)) :alts (subvec xs (+ np ni 2))}))

(defn mk-ctor-elim-type [env n]
  (let [{:keys [cases ctx params motive alts]} (cases-data env n)
        idx (u/local-decl ctx "ctorIdx" (u/const' "Nat" []))
        val (mk-nat-lookup-table-lifting ctx idx (mapv #(u/infer-type ctx %) alts))]
    (u/add-definition env ctx (str n ".ctorElimType") (vec (.levelParams cases))
                      (vec (concat params [motive idx])) nil val)))

(defn mk-ind-ctor-elim [env n]
  (let [{:keys [info cases ctx params motive ism ls us]} (cases-data env n)
        idx (u/local-decl ctx "ctorIdx" (u/const' "Nat" []))
        ktf (u/app (u/const' (str n ".ctorElimType") ls) (conj params motive))
        kt (e/app ktf idx)
        ctor-app (u/app (u/const' (str n ".ctorIdx") us) (concat params ism))
        ht (u/mk-eq ctx idx ctor-app) h (u/local-decl ctx "h" ht) k (u/local-decl ctx "k" kt)
        motive' (u/mk-lambda-fvars ctx ism (u/mk-arrow ctx ht (u/app motive ism)))
        alts (mapv (fn [i ctor]
                     (let [ctor (u/app (u/const' ctor us) params)
                           [zs _] (u/forall-telescope ctx (u/infer-type ctx ctor))
                           h (u/local-decl ctx "h" (u/mk-eq ctx idx (e/lit-nat i)))
                           e (u/mk-eq-ndrec ctx (u/const' "Nat" []) idx ktf k (e/lit-nat i) h)
                           e (u/app (mk-pulift-down ctx e) zs)]
                       (u/mk-lambda-fvars ctx (conj zs h) e))) (range) (.ctors info))
        val (u/app (u/const' (str n ".casesOn") ls) (concat params [motive'] ism alts [h]))]
    (u/add-definition env ctx (str n ".ctorElim") (vec (.levelParams cases))
                      (vec (concat params [motive idx] ism [h k])) nil val)))

(defn mk-constructor-elim [env n]
  (reduce
   (fn [env i]
     (let [{:keys [info cases ctx params motive ism alts ls us]} (cases-data env n)
           ctor (nth (vec (.ctors info)) i) alt (nth alts i)
           ctor-app (u/app (u/const' (str n ".ctorIdx") us) (concat params ism))
           h (u/local-decl ctx "h" (u/mk-eq ctx ctor-app (e/lit-nat i)))
           symm (u/app (u/const' "Eq.symm" [(lvl/succ lvl/zero)]) [(u/const' "Nat" []) ctor-app (e/lit-nat i) h])
           kt (u/app (u/const' (str n ".ctorElimType") ls) (concat params [motive (e/lit-nat i)]))
           val (u/app (u/const' (str n ".ctorElim") ls)
                      (concat params [motive (e/lit-nat i)] ism [symm (with-mk-pulift-up ctx kt (fn [_] alt))]))]
       (u/add-definition env ctx (str ctor ".elim") (vec (.levelParams cases))
                         (vec (concat params [motive] ism [h alt])) nil val)))
   env (range (count (.ctors (env/lookup! env (name/from-string (str n))))))))

(defn mk-ctor-elim [env n]
  (let [ind (env/lookup! env (name/from-string (str n)))
        rec (env/lookup! env (name/from-string (str n ".rec")))]
    (if (or (nil? (env/lookup env (name/from-string (str n ".ctorIdx"))))
            (<= (count (.ctors ind)) 1) (u/prop-former? (u/context env) (.type ind))
            (<= (count (.levelParams rec)) (count (.levelParams ind)))) env
        (-> env (mk-ctor-elim-type n) (mk-ind-ctor-elim n) (mk-constructor-elim n)))))
