(ns ansatz.meta.constructions.no-confusion
  "Lean/Meta/Constructions/NoConfusion.lean (55f80e10).
   Dependent equality transport follows mkEqNDRecTelescope/substEq by reverting
   dependent locals before Eq.ndrec, and converting homogeneous HEq via eq_of_heq."
  (:require [ansatz.meta.constructions.util :as u]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.tc :as tc]))

(defn mk-no-confusion-ctor-arg [ctx ctor-name p]
  (let [ci (env/lookup! (:env @ctx) ctor-name)
        [xs1 t1] (u/forall-telescope ctx (.type ci) (.numParams ci))
        [fs1 _] (u/forall-telescope ctx t1)
        [xs2 t2] (u/forall-telescope ctx (.type ci) (.numParams ci))
        [fs2 _] (u/forall-telescope ctx t2)
        t (reduce (fn [t [f1 f2]]
                    (if (lvl/level-zero? (u/get-level ctx (u/infer-type ctx f1))) t
                        (u/mk-forall-fvars ctx
                                           [(u/local-decl ctx (str (:name (u/decl ctx f1)) "_eq") (u/mk-eq-heq ctx f1 f2))] t)))
                  p (reverse (map vector fs1 fs2)))]
    (u/mk-lambda-fvars ctx (vec (concat xs1 fs1 xs2 fs2)) t)))

(defn with-eq-telescope [ctx xs ys k]
  (let [eqs (mapv (fn [i x y]
                    (u/local-decl ctx (if (> (count xs) 1) (str "eq_" (inc i)) "eq") (u/mk-eq-heq ctx x y)))
                  (range) xs ys)]
    (k eqs)))

(defn with-needed-eq-telescope [ctx xs ys k]
  (loop [i 0 vs [] eqs []]
    (if (= i (count xs)) (k vs eqs)
        (let [x (nth xs i) y (nth ys i)]
          (if (and (< (inc i) (count xs)) (tc/is-def-eq @ctx x y))
            (recur (inc i) vs (conj eqs (u/mk-eq-refl ctx x)))
            (let [v (u/local-decl ctx (if (> (count xs) 1) (str "eq_" (inc i)) "eq") (u/mk-eq-heq ctx x y))]
              (recur (inc i) (conj vs v) (conj eqs v))))))))

(defn mk-eq-ndrec-telescope [ctx motive val xs ys]
  (with-eq-telescope ctx xs ys
    (fn [eqs]
      (letfn [(go [xs ys eqs target]
                  (if (empty? ys) val
                      (let [x (first xs) y (first ys) eq (first eqs)
                            rest-ys (vec (rest ys)) rest-eqs (vec (rest eqs))
                        ;; Subst.substCore reverts only the transitive dependents.
                        ;; Generalizing independent parameters changes the Eq.ndrec
                        ;; motive and fails definitional equality with Lean's output.
                            generalized
                            (first
                             (reduce (fn [[vs deps] v]
                                       (if (some #(not= (:type (u/decl ctx v))
                                                        (e/abstract1 (:type (u/decl ctx v)) (e/fvar-id %))) deps)
                                         [(conj vs v) (conj deps v)] [vs deps]))
                                     [[] [y]] (concat rest-ys rest-eqs)))
                            motive (u/mk-lambda-fvars ctx [y] (u/mk-forall-fvars ctx generalized target))
                        ;; Revert the dependent telescope, substitute y := x, and reintroduce it.
                            [new-locals subst]
                            (reduce (fn [[vs subst] v]
                                      (let [d (u/decl ctx v)
                                            v' (u/local-decl ctx (:name d) (u/replace-fvars (:type d) subst) (:info d))]
                                        [(conj vs v') (conj subst [v v'])]))
                                    [[] [[y x]]] generalized)
                            next-ys (mapv #(u/replace-fvars % subst) rest-ys)
                            next-eqs (mapv #(u/replace-fvars % subst) rest-eqs)
                            base (go (vec (rest xs)) next-ys next-eqs (u/replace-fvars target subst))
                            base (u/mk-lambda-fvars ctx new-locals base)
                            eq-type (u/whnf ctx (u/infer-type ctx eq))
                            eq (if (= (e/const-name (e/get-app-fn eq-type)) (name/from-string "HEq"))
                                 (u/app (u/const' "eq_of_heq" [(u/get-level ctx (u/infer-type ctx x))])
                                        [(u/infer-type ctx x) x y eq]) eq)]
                        (if (and (empty? generalized) (= target (e/abstract1 target (e/fvar-id y))))
                          base
                          (u/app (u/mk-eq-ndrec ctx (u/infer-type ctx x) x motive base y eq) generalized)))))]
        (u/mk-lambda-fvars ctx eqs (go xs ys eqs (u/beta motive ys)))))))

(defn- cases-data [env n]
  (let [info (env/lookup! env (name/from-string (str n)))
        cases (env/lookup! env (name/from-string (str n ".casesOn")))
        ls (mapv lvl/param (.levelParams cases))]
    {:info info :cases cases :ls ls :v (first ls) :us (subvec ls 1)}))

(defn mk-if-nat-eq [ctx p a b then else]
  (let [eq (u/mk-eq ctx a b)
        h (u/local-decl ctx "h" eq)
        hn (u/local-decl ctx "h" (u/app (u/const' "Not" []) [eq]))]
    (u/app (u/const' "dite" [(u/get-level ctx p)])
           [p eq (u/app (u/const' "Nat.decEq" []) [a b])
            (u/mk-lambda-fvars ctx [h] (then h))
            (u/mk-lambda-fvars ctx [hn] (else hn))])))

(defn mk-no-confusion-type
  ([env n] (mk-no-confusion-type env n (str n ".noConfusionType")))
  ([env n target]
   (let [{:keys [info cases v us]} (cases-data env n) ctx (u/context env)
         nc (count (.ctors info))
         linear? (and (> nc 2) (env/lookup env (name/from-string (str n ".ctorElim"))))
         cs (u/const' (str n ".casesOn") (into [(lvl/succ v)] us))
         t (u/infer-type ctx cs) ptype (e/sort' v) p (u/local-decl ctx "P" ptype)
         [xs1 t1] (u/forall-telescope ctx t (.numParams info))
         [xs2 t2] (u/forall-telescope ctx t (.numParams info))
         [m1args _] (u/forall-telescope ctx (e/forall-type (u/whnf ctx t1)))
         [m2args _] (u/forall-telescope ctx (e/forall-type (u/whnf ctx t2)))
         m1 (u/mk-lambda-fvars ctx m1args ptype) m2 (u/mk-lambda-fvars ctx m2args ptype)
         t1 (u/instantiate-forall ctx t1 [m1]) t2 (u/instantiate-forall ctx t2 [m2])
         [ys1 t1] (u/forall-telescope ctx t1 (inc (.numIndices info)))
         [ys2 _] (u/forall-telescope ctx t2 (inc (.numIndices info)))
         [alts _] (u/forall-telescope ctx t1 nc)
         alts (mapv (fn [i alt]
                      (let [[zs1 _] (u/forall-telescope ctx (u/infer-type ctx alt))
                            ctor (nth (vec (.ctors info)) i)
                            same (fn [zs2]
                                   (u/mk-arrow ctx
                                               (u/beta (mk-no-confusion-ctor-arg ctx ctor p)
                                                       (vec (concat xs1 zs1 xs2 zs2))) p))
                            body
                            (if linear?
                              (mk-if-nat-eq ctx ptype
                                            (u/app (u/const' (str n ".ctorIdx") us) (concat xs2 ys2)) (e/lit-nat i)
                                            (fn [h]
                                              (let [el (u/app (u/const' (str ctor ".elim") (into [(lvl/succ v)] us))
                                                              (concat xs2 [m2] ys2 [h]))
                                                    [zs2 _] (u/forall-telescope ctx (e/forall-type (u/whnf ctx (u/infer-type ctx el))))]
                                                (e/app el (u/mk-lambda-fvars ctx zs2 (same zs2)))))
                                            (fn [_] p))
                              (let [inner (u/app cs (concat xs2 [m2] ys2))
                                    [alts2 _] (u/forall-telescope ctx (u/infer-type ctx inner) nc)]
                                (u/app inner
                                       (mapv (fn [j a]
                                               (let [[zs2 _] (u/forall-telescope ctx (u/infer-type ctx a))]
                                                 (u/mk-lambda-fvars ctx zs2 (if (= i j) (same zs2) p))))
                                             (range) alts2))))]
                        (u/mk-lambda-fvars ctx zs1 body))) (range) alts)
         val (u/app cs (concat xs1 [m1] ys1 alts))]
     (u/add-definition env ctx target (vec (.levelParams cases))
                       (vec (concat [p] xs1 ys1 xs2 ys2)) nil val))))

(defn mk-no-confusion-core-imp
  ([env n] (mk-no-confusion-core-imp env n (str n ".noConfusion") (str n ".noConfusionType")))
  ([env n target nct]
   (let [{:keys [info cases ls us]} (cases-data env n) ctx (u/context env)
         nct (u/const' nct ls)
         [[p] t] (u/forall-telescope ctx (u/infer-type ctx nct) 1)
         nx (+ (.numParams info) (.numIndices info) 1)
         [xs1 t] (u/forall-telescope ctx t nx) [xs2 _] (u/forall-telescope ctx t nx)
         _ (u/implicit! ctx (concat [p] xs1 xs2))
         ps1 (subvec xs1 0 (.numParams info)) ys1 (subvec xs1 (.numParams info))
         target1 (u/app nct (concat [p] xs1 xs1))
         motive1 (u/mk-lambda-fvars ctx ys1 target1)
         alts (mapv (fn [ctor]
                      (let [ctor-app (u/app (u/const' ctor us) ps1)
                            [fs _] (u/forall-telescope ctx (u/infer-type ctx ctor-app))
                            kt (u/beta (mk-no-confusion-ctor-arg ctx ctor p) (vec (concat ps1 fs ps1 fs)))
                            k (u/local-decl ctx "k" kt)
                            [eqs _] (u/forall-telescope ctx kt)
                            val (u/app k
                                       (map (fn [eq]
                                              (let [t (u/whnf ctx (u/infer-type ctx eq))
                                                    args (e/get-app-args t) x (nth args 1)]
                                                (if (= (e/const-name (e/get-app-fn t)) (name/from-string "HEq"))
                                                  (u/app (u/const' "HEq.refl" [(u/get-level ctx (u/infer-type ctx x))])
                                                         [(u/infer-type ctx x) x])
                                                  (u/mk-eq-refl ctx x)))) eqs))]
                        (u/mk-lambda-fvars ctx (conj fs k) val))) (.ctors info))
         val (u/app (u/const' (str n ".casesOn") ls) (concat ps1 [motive1] ys1 alts))
         target2 (u/app nct (concat [p] xs1 xs2))
         motive2 (u/mk-lambda-fvars ctx xs2 target2)
         val (mk-eq-ndrec-telescope ctx motive2 val xs1 xs2)]
     (u/add-definition env ctx target (vec (.levelParams cases)) (vec (concat [p] xs1 xs2)) nil val))))

(defn mk-no-confusion-ctors [env n]
  (let [{:keys [info cases ls v us]} (cases-data env n)]
    (reduce
     (fn [env ctor]
       (let [ci (env/lookup! env ctor) ctx (u/context env)]
         (if (or (zero? (.numFields ci))
                 (env/lookup env (name/from-string (str ctor ".noConfusion")))) env
             (let [[xs t] (u/forall-telescope ctx (.type ci) (.numParams ci))
                   p (u/local-decl ctx "P" (e/sort' v))
                   [fs1 _] (u/forall-telescope ctx t (.numFields ci))
                   [fs2 _] (u/forall-telescope ctx t (.numFields ci))
                   _ (u/implicit! ctx (concat xs [p] fs1 fs2))
                   c1 (u/app (u/const' ctor us) (concat xs fs1))
                   c2 (u/app (u/const' ctor us) (concat xs fs2))
                   is1 (subvec (e/get-app-args (u/whnf ctx (u/infer-type ctx c1))) (.numParams info))
                   is2 (subvec (e/get-app-args (u/whnf ctx (u/infer-type ctx c2))) (.numParams info))]
               (with-needed-eq-telescope ctx (conj is1 c1) (conj is2 c2)
                 (fn [eqvs eqs]
                   (let [kt (u/beta (mk-no-confusion-ctor-arg ctx ctor p) (vec (concat xs fs1 xs fs2)))
                         k (u/local-decl ctx "k" kt)
                         start (u/app (u/const' (str n ".noConfusion") ls)
                                      (concat [p] xs is1 [c1] xs is2 [c2]))
                        ;; Main noConfusion quantifies parameter equalities too.
                         start (reduce (fn [e x]
                                         (let [et (e/forall-type (u/whnf ctx (u/infer-type ctx e)))
                                               heq? (= (e/const-name (e/get-app-fn et)) (name/from-string "HEq"))]
                                           (e/app e (if heq?
                                                      (u/app (u/const' "HEq.refl" [(u/get-level ctx (u/infer-type ctx x))]) [(u/infer-type ctx x) x])
                                                      (u/mk-eq-refl ctx x))))) start xs)
                         val (reduce (fn [e eq]
                                       (let [et (e/forall-type (u/whnf ctx (u/infer-type ctx e)))
                                             qt (u/whnf ctx (u/infer-type ctx eq))
                                             heq? (= (e/const-name (e/get-app-fn et)) (name/from-string "HEq"))
                                             eq? (= (e/const-name (e/get-app-fn qt)) (name/from-string "Eq"))]
                                         (e/app e (if (and heq? eq?)
                                                    (u/app (u/const' "heq_of_eq" (e/const-levels (e/get-app-fn qt)))
                                                           (conj (e/get-app-args qt) eq)) eq)))) start eqs)
                         val (e/app val k)]
                     ;; NoConfusion.lean markNoConfusion (.perCtor arity fields).
                     (let [binders (vec (concat xs [p] fs1 fs2 eqvs [k]))
                           fields (loop [t kt n 0]
                                    (if (e/forall? t) (recur (e/forall-body t) (inc n)) n))]
                       (env/update-extension
                        (u/add-definition env ctx (str ctor ".noConfusion") (vec (.levelParams cases))
                                          binders p val)
                        :no-confusion {} assoc (str ctor ".noConfusion")
                        {:kind :per-ctor :arity (dec (count binders)) :num-fields fields}))))))))) env (.ctors info))))

(defn mk-no-confusion-enum [env n]
  (let [info (env/lookup! env (name/from-string (str n))) ctx (u/context env)
        us (mapv lvl/param (.levelParams info))
        ;; Lean uses a fresh `v` here, rather than the recursor elimination level.
        vn (loop [s "v" i 1]
             (if (some #{(name/from-string s)} (.levelParams info)) (recur (str "v_" i) (inc i)) s))
        v (lvl/param (name/from-string vn)) ls (into [v] us)
        lps (into [(name/from-string vn)] (.levelParams info))
        t (u/const' n us) p (u/local-decl ctx "P" (e/sort' v))
        x (u/local-decl ctx "x" t) y (u/local-decl ctx "y" t)
        ctor (u/const' (str n ".ctorIdx") us)
        single? (= 1 (count (.ctors info)))
        prefix [t (u/const' "Nat" []) (u/const' "instDecidableEqNat" []) ctor]
        val (if single? (u/mk-arrow ctx p p)
                (u/app (u/const' "noConfusionTypeEnum" [(u/get-level ctx t) (lvl/succ lvl/zero) v]) (concat prefix [p x y])))
        env (u/add-definition env ctx (str n ".noConfusionType") lps [p x y] (e/sort' v) val)
        _ (u/set-env! ctx env)
        _ (u/implicit! ctx [p x y])
        h (u/local-decl ctx "h" (u/mk-eq ctx x y))
        val (if single? (let [q (u/local-decl ctx "p" p)] (u/mk-lambda-fvars ctx [q] q))
                (u/app (u/const' "noConfusionEnum" [(u/get-level ctx t) (lvl/succ lvl/zero) v]) (concat prefix [p x y h])))]
    (u/add-definition env ctx (str n ".noConfusion") lps [p x y h]
                      (u/app (u/const' (str n ".noConfusionType") ls) [p x y]) val)))

(defn mk-no-confusion-core [env n]
  (let [info (env/lookup! env (name/from-string (str n)))
        rec (env/lookup! env (name/from-string (str n ".rec")))]
    (if (or (u/prop-former? (u/context env) (.type info))
            (<= (count (.levelParams rec)) (count (.levelParams info)))) env
        (-> env (mk-no-confusion-type n) (mk-no-confusion-core-imp n) (mk-no-confusion-ctors n)))))

(defn mk-no-confusion [env n]
  (let [info (env/lookup! env (name/from-string (str n)))]
    (if (and (u/is-enum-type? env info) (env/lookup env (name/from-string "noConfusionEnum")))
      (mk-no-confusion-enum env n)
      (mk-no-confusion-core env n))))
