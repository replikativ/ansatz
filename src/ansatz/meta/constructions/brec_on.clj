(ns ansatz.meta.constructions.brec-on
  "Lean/Meta/Constructions/BRecOn.lean and Meta/PProdN.lean (55f80e10).
   The constructions follow recursor telescopes, including auxiliary nested motives."
  (:require [ansatz.meta.constructions.util :as u]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]))

;; Lean.Meta.mkPProd and PProdN.{pack,mk}: singletons are NOT paired with PUnit.
(defn mk-pprod [ctx a b]
  (let [la (u/get-level ctx a) lb (u/get-level ctx b)]
    (if (and (lvl/level-zero? la) (lvl/level-zero? lb))
      (u/app (u/const' "And" []) [a b])
      (u/app (u/const' "PProd" [la lb]) [a b]))))
(defn mk-pprod-mk [ctx a b]
  (let [ta (u/infer-type ctx a) tb (u/infer-type ctx b)
        la (u/get-level ctx ta) lb (u/get-level ctx tb)]
    (if (and (lvl/level-zero? la) (lvl/level-zero? lb))
      (u/app (u/const' "And.intro" []) [ta tb a b])
      (u/app (u/const' "PProd.mk" [la lb]) [ta tb a b]))))
(defn- pack [ctx rlvl xs values?]
  (if (empty? xs)
    (u/const' (if (lvl/level-zero? rlvl)
                (if values? "True.intro" "True")
                (if values? "PUnit.unit" "PUnit"))
              (if (lvl/level-zero? rlvl) [] [rlvl]))
    (reduce (fn [b a] ((if values? mk-pprod-mk mk-pprod) ctx a b))
            (peek xs) (reverse (pop xs)))))
(defn- proj [ctx i x]
  (let [t (u/whnf ctx (u/infer-type ctx x))]
    (e/proj (e/const-name (e/get-app-fn t)) i x)))

(defn build-below-minor-premise [ctx rlvl motives minor-type]
  (let [[args _] (u/forall-telescope ctx minor-type)]
    (letfn [(go [prods args]
              (if-let [arg (first args)]
                (let [arg-type (u/infer-type ctx arg)
                      [ys t] (u/forall-telescope ctx arg-type)]
                  (if (some #{(e/get-app-fn t)} motives)
                    (let [arg' (u/local-decl ctx (:name (u/decl ctx arg))
                                 (u/mk-forall-fvars ctx ys (e/sort' rlvl)))
                          p (u/mk-forall-fvars ctx ys (mk-pprod ctx t (u/app arg' ys)))]
                      (u/mk-lambda-fvars ctx [arg'] (go (conj prods p) (rest args))))
                    (u/mk-lambda-fvars ctx [arg] (go prods (rest args)))))
                (pack ctx rlvl prods false)))]
      (go [] args))))

(defn- rec-telescope [ctx rec np]
  (let [[xs body] (u/forall-telescope ctx (.type rec))
        nm (.numMotives rec) nn (.numMinors rec)
        params (subvec xs 0 np) motives (subvec xs np (+ np nm))
        minors (subvec xs (+ np nm) (+ np nm nn))
        ism (subvec xs (+ np nm nn))
        [_ major-sort] (u/forall-telescope ctx (u/infer-type ctx (u/infer-type ctx (peek ism))))
        ls (mapv lvl/param (.levelParams rec))]
    {:params params :motives motives :minors minors :ism ism :body body :ls ls
     :rlvl (lvl/level-max (e/sort-level major-sort) (first ls))}))

(defn mk-below-from-rec [env rec-name np below-name]
  (let [rec (env/lookup! env (name/from-string (str rec-name))) ctx (u/context env)
        {:keys [params motives minors ism ls rlvl]} (rec-telescope ctx rec np)
        val (u/app (u/const' rec-name (assoc ls 0 (lvl/succ rlvl)))
                   (concat params
                     (map (fn [m]
                            (let [[ys _] (u/forall-telescope ctx (u/infer-type ctx m))]
                              (u/mk-lambda-fvars ctx ys (e/sort' rlvl)))) motives)
                     (map #(build-below-minor-premise ctx rlvl motives (u/infer-type ctx %)) minors)
                     ism))]
    (u/add-definition env ctx below-name (vec (.levelParams rec))
                      (vec (concat params motives ism)) (e/sort' rlvl) val)))

(defn build-brec-on-minor-premise [ctx rlvl motives belows fs minor-type]
  (let [[args t] (u/forall-telescope ctx minor-type)]
    (letfn [(go [prods args]
              (if-let [arg (first args)]
                (let [[ys at] (u/forall-telescope ctx (u/infer-type ctx arg))
                      idx (.indexOf motives (e/get-app-fn at))]
                  (if (neg? idx)
                    (u/mk-lambda-fvars ctx [arg] (go prods (rest args)))
                    (let [arg' (u/local-decl ctx (:name (u/decl ctx arg))
                                 (u/mk-forall-fvars ctx ys
                                   (mk-pprod ctx at (u/app (nth belows idx) (e/get-app-args at)))))]
                      (u/mk-lambda-fvars ctx [arg'] (go (conj prods arg') (rest args))))))
                (let [idx (.indexOf motives (e/get-app-fn t))
                      b (pack ctx rlvl prods true)]
                  (mk-pprod-mk ctx (u/app (nth fs idx) (conj (e/get-app-args t) b)) b))))]
      (go [] args))))

(defn mk-brec-on-from-rec [env rec-name np all brec-name]
  (let [rec (env/lookup! env (name/from-string (str rec-name))) ctx (u/context env)
        {:keys [params motives minors ism body ls rlvl]} (rec-telescope ctx rec np)
        idx (.indexOf motives (e/get-app-fn body))
        belows (mapv (fn [i]
                       (u/app (u/const' (if (< i (count all)) (str (nth all i) ".below")
                                          (str (first all) ".below_" (inc (- i (count all))))) ls)
                              (concat params motives))) (range (count motives)))
        fs (mapv (fn [i m b]
                   (let [[ys _] (u/forall-telescope ctx (u/infer-type ctx m))
                         f (u/local-decl ctx "f" (u/app b ys))]
                     (u/local-decl ctx (str "F_" (inc i))
                       (u/mk-forall-fvars ctx (conj ys f) (u/app m ys)))))
                 (range) motives belows)
        go-val (u/app (u/const' rec-name (assoc ls 0 rlvl))
                      (concat params
                        (map (fn [m b]
                               (let [[ys _] (u/forall-telescope ctx (u/infer-type ctx m))]
                                 (u/mk-lambda-fvars ctx ys (mk-pprod ctx (u/app m ys) (u/app b ys))))) motives belows)
                        (map #(build-brec-on-minor-premise ctx rlvl motives belows fs (u/infer-type ctx %)) minors)
                        ism))
        vs (vec (concat params motives ism fs))
        ma (u/app (nth motives idx) ism) ba (u/app (nth belows idx) ism)
        go-name (str brec-name ".go")
        env (u/add-definition env ctx go-name (vec (.levelParams rec)) vs (mk-pprod ctx ma ba) go-val)
        _ (u/set-env! ctx env)
        go-app (u/app (u/const' go-name ls) vs)
        env (u/add-definition env ctx brec-name (vec (.levelParams rec)) vs ma (proj ctx 0 go-app))
        _ (u/set-env! ctx env)
        lhs (u/app (u/const' brec-name ls) vs)
        rhs (u/app (nth fs idx) (conj ism (proj ctx 1 go-app)))
        eq (u/mk-eq ctx lhs rhs)
        ;; Lean mkBRecOnFromRec proves `.eq` by cases on major, then refl.
        ;; Building that casesOn term directly avoids tactic-state elaboration.
        motive (u/mk-lambda-fvars ctx ism eq)
        ;; Nested auxiliary recursors have container majors, whose type names
        ;; provide the correct casesOn rather than an inaccessible auxiliary type.
        major-type (u/whnf ctx (u/infer-type ctx (peek ism)))
        head (e/get-app-fn major-type)
        case-name (str (e/const-name head) ".casesOn")
        case-ls (into [lvl/zero] (e/const-levels head))
        case-params (let [ind (env/lookup! env (e/const-name head))]
                      (subvec (e/get-app-args major-type) 0 (.numParams ind)))
        case-app (u/app (u/const' case-name case-ls) (concat case-params [motive] ism))
        [alts _] (u/forall-telescope ctx (u/infer-type ctx case-app))
        alts (mapv (fn [a]
                     (let [[ys t] (u/forall-telescope ctx (u/infer-type ctx a))
                           eq-args (e/get-app-args (u/whnf ctx t))]
                       (u/mk-lambda-fvars ctx ys (u/mk-eq-refl ctx (nth eq-args 1))))) alts)
        proof (u/mk-lambda-fvars ctx vs (u/app case-app alts))]
    (env/check-constant env
      (u/mk-thm-or-unsafe-def env (str brec-name ".eq") (vec (.levelParams rec))
                   (u/mk-forall-fvars ctx vs eq) proof))))

(defn- for-recursors [env n f suffix]
  (let [ind (env/lookup! env (name/from-string (str n))) ctx (u/context env)]
    (if (or (not (.isRec ind)) (u/prop-former? ctx (.type ind))) env
      (let [env (f env (str n ".rec") (.numParams ind) (str n suffix))]
        (if (= (first (vec (.all ind))) (name/from-string (str n)))
          (reduce (fn [env i]
                    (f env (str n ".rec_" (inc i)) (.numParams ind) (str n suffix "_" (inc i))))
                  env (range (.numNested ind))) env)))))

(defn mk-below [env n]
  (for-recursors env n mk-below-from-rec ".below"))
(defn mk-brec-on [env n]
  (let [ind (env/lookup! env (name/from-string (str n)))]
    (for-recursors env n (fn [env rec np target]
                          (mk-brec-on-from-rec env rec np (vec (.all ind)) target)) ".brecOn")))
