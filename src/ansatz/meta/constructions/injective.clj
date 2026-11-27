(ns ansatz.meta.constructions.injective
  "Lean v4.36.0 Meta/Injective.lean: `C.inj` and `C.injEq` for the constructors of an inductive
   type.

   `C.inj : ∀ {params} {fields} {fields'}, C params fields = C params fields' → eqs` and
   `C.injEq : ∀ params fields fields', (C params fields = C params fields') = eqs`, where `eqs`
   is the conjunction of `x = x'` (`HEq` when the types differ) over the fields that are neither
   proofs nor shared: a field occurring in the constructor's result type (a fixed index, or in
   the type of a field that does) is the same on both sides (mkInjectiveTheoremTypeCore?). A
   constructor without such fields gets neither.

   Proofs: `C.inj` applies the per-constructor `noConfusion` (AppBuilder.mkNoConfusion) to a
   continuation that packs its field equations; `C.injEq` is `Eq.propIntro` of `C.inj` and the
   converse, which eliminates the equations in field order (each heterogeneous one becomes
   homogeneous once the earlier fields are substituted) down to `Eq.refl`."
  (:require [ansatz.meta.constructions.util :as u]
            [ansatz.meta.app-builder :as app-builder]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.tc :as tc]
            [ansatz.meta.fvar-subst :as subst]))

(defn- fvar-ids [x]
  (let [ids (volatile! #{})]
    (subst/map-expr-fvars (fn [id] (vswap! ids conj id) (e/fvar id)) x)
    @ids))

(defn- occurs-or-in-type?
  "SameCtorUtils.lean occursOrInType: `x` occurs in `t`, or in the type of a free variable of `t`."
  [ctx x t]
  (let [id (e/fvar-id x)]
    (some (fn [fid] (or (= fid id) (contains? (fvar-ids (:type (get (:lctx @ctx) fid))) id)))
          (fvar-ids t))))

(defn- prop? [ctx x]
  (lvl/level-zero? (u/get-level ctx (u/infer-type ctx x))))

(defn- heq? [t] (= "HEq" (str (e/const-name (e/get-app-fn t)))))

(defn- mk-and [ctx props]
  (reduce (fn [acc p] (u/app (u/const' "And" []) [p acc])) (peek props) (rseq (pop props))))

(defn- and-intro [ctx props proofs]
  (if (= 1 (count props))
    (first proofs)
    (u/app (u/const' "And.intro" []) [(first props) (mk-and ctx (subvec props 1))
                                      (first proofs) (and-intro ctx (subvec props 1) (subvec proofs 1))])))

(defn- and-components [conj-proof n]
  ;; h.1, h.2.1, …, h.2…2
  (loop [h conj-proof i 0 out []]
    (if (= i (dec n)) (conj out h)
        (recur (e/proj (name/from-string "And") 1 h) (inc i) (conj out (e/proj (name/from-string "And") 0 h))))))

(defn- elim-opt-param
  "Injective.lean elimOptParam: `optParam T d` ↦ `T` throughout (a default value is not part of
   the field's type, and must not make another field look fixed)."
  [x]
  (let [[h args] (e/get-app-fn-args x)]
    (if (and (e/const? h) (= "optParam" (str (e/const-name h))) (= 2 (count args)))
      (recur (first args))
      (case (e/tag x)
        :app (e/app (elim-opt-param (e/app-fn x)) (elim-opt-param (e/app-arg x)))
        :lam (e/lam (e/lam-name x) (elim-opt-param (e/lam-type x)) (elim-opt-param (e/lam-body x)) (e/lam-info x))
        :forall (e/forall' (e/forall-name x) (elim-opt-param (e/forall-type x)) (elim-opt-param (e/forall-body x))
                           (e/forall-info x))
        :let (e/let' (e/let-name x) (elim-opt-param (e/let-type x)) (elim-opt-param (e/let-value x))
                     (elim-opt-param (e/let-body x)))
        x))))

(defn- open-ctor
  "params, fields, fields' (the new ones), the equated pairs and the result type of `ctor`."
  [ctx ctor-ci]
  (let [np (.numParams ctor-ci)
        [params t] (u/forall-telescope ctx (elim-opt-param (.type ctor-ci)) np)
        [args1 result] (u/forall-telescope ctx t)
        [args2 new]
        (loop [i 0 t t args2 [] new []]
          (if (< i (count args1))
            (let [t (u/whnf ctx t) a1 (nth args1 i)]
              (if (occurs-or-in-type? ctx a1 result)
                (recur (inc i) (e/instantiate1 (e/forall-body t) a1) (conj args2 a1) new)
                (let [a2 (u/local-decl ctx (e/forall-name t) (e/forall-type t))]
                  (recur (inc i) (e/instantiate1 (e/forall-body t) a2) (conj args2 a2) (conj new a2)))))
            [args2 new]))
        pairs (vec (keep (fn [[a b]] (when (and (not (prop? ctx a)) (not= a b)) [a b])) (map vector args1 args2)))]
    {:params params :args1 args1 :args2 args2 :new new :pairs pairs}))

(defn- inj-proof
  "`fun h => C.noConfusion … h (fun e… => ⟨…⟩)` : `C … = C … → eqs` in `ctx`."
  [ctx ctor-ci {:keys [params args1 args2 pairs]} eqs]
  (let [us (mapv lvl/param (.levelParams ctor-ci))
        lhs (u/app (e/const' (.name ctor-ci) us) (concat params args1))
        rhs (u/app (e/const' (.name ctor-ci) us) (concat params args2))
        h (u/local-decl ctx "h" (u/mk-eq ctx lhs rhs))
        target (mk-and ctx eqs)
        nc (app-builder/mk-no-confusion ctx target (u/infer-type ctx lhs) lhs rhs h)
        k-type (e/forall-type (u/whnf ctx (u/infer-type ctx nc)))
        ;; the continuation receives the data-field equations, in field order
        [ks _] (u/forall-telescope ctx k-type)
        data (vec (remove #(prop? ctx %) args1))
        by-field (zipmap data ks)
        proofs (mapv (fn [p want]
                       (if (= 4 (count (e/get-app-args (u/infer-type ctx p)))) ; HEq α a β b → eq_of_heq α a b p
                         (let [[ta a _ b] (e/get-app-args (u/infer-type ctx p))]
                           (if (heq? want) p
                               (u/app (u/const' "eq_of_heq" [(u/get-level ctx ta)]) [ta a b p])))
                         p))
                     (mapv #(get by-field (first %)) pairs) eqs)]
    [h (u/mk-lambda-fvars ctx [h] (e/app nc (u/mk-lambda-fvars ctx ks (and-intro ctx eqs proofs))))]))

(defn- pi-shape
  "∀ (news, retyped under `sub`) (equations under `sub`), goal — with the news rebound."
  [ctx news eqs goal sub]
  (let [[locals sub] (reduce (fn [[ls sub] x]
                               (let [d (u/decl ctx x)
                                     l (u/local-decl ctx (:name d) (u/replace-fvars (:type d) sub) :default)]
                                 [(conj ls l) (conj sub [x l])]))
                             [[] sub] news)
        es (mapv #(u/local-decl ctx "e" (u/replace-fvars % sub)) eqs)]
    (u/mk-forall-fvars ctx (into locals es) (u/replace-fvars goal sub))))

(defn- converse
  "A term of `∀ news (eqs), goal` (news: the remaining new fields, rebound; everything read under
   `sub`). The first equation `a = b` (made homogeneous: the earlier fields are substituted, so a
   heterogeneous one's types agree) is eliminated by `Eq.rec` whose motive generalizes `b`
   together with the later new fields and equations depending on it (Lean's subst reverts them);
   at `b := a` the rest recurses, ending in `Eq.refl` (proof fields agree by proof irrelevance)."
  [ctx news eqs pairs goal sub]
  (let [[locals sub] (reduce (fn [[ls sub] x]
                               (let [d (u/decl ctx x)
                                     l (u/local-decl ctx (:name d) (u/replace-fvars (:type d) sub) :default)]
                                 [(conj ls l) (conj sub [x l])]))
                             [[] sub] news)
        S #(u/replace-fvars % sub)
        es (mapv #(u/local-decl ctx "e" (S %)) eqs)
        body
        (if (empty? eqs)
          (u/mk-eq-refl ctx (second (e/get-app-args (S goal))))
          (let [[a b] (first pairs)
                bi (.indexOf ^java.util.List news b)
                b' (nth locals bi)
                post (subvec news (inc bi))
                a' (S a)
                ta (u/infer-type ctx a')
                e1 (first es)
                hom (if (heq? (u/infer-type ctx e1))
                      (u/app (u/const' "eq_of_heq" [(u/get-level ctx ta)]) [ta a' b' e1])
                      e1)
                pre-sub (vec (take bi (map vector news locals)))
                base (into (vec (remove (fn [[x _]] (some #{x} news)) sub)) pre-sub)
                y (u/local-decl ctx "y" ta)
                hy (u/local-decl ctx "h" (u/mk-eq ctx a' y))
                motive (u/mk-lambda-fvars ctx [y hy] (pi-shape ctx post (rest eqs) goal (conj base [b y])))
                minor (converse ctx post (vec (rest eqs)) (vec (rest pairs)) goal (conj base [b a']))
                rec (u/app (u/const' "Eq.rec" [lvl/zero (u/get-level ctx ta)]) [ta a' motive minor b' hom])]
            (u/app rec (concat (subvec locals (inc bi)) (rest es)))))]
    (u/mk-lambda-fvars ctx (into locals es) body)))

(defn- mk-for-ctor [env ind-ci ctor-ci]
  (let [ctx (u/context env)
        {:keys [params args1 args2 new pairs] :as opened} (open-ctor ctx ctor-ci)]
    (if (empty? pairs)
      env
      (let [lps (vec (.levelParams ctor-ci))
            us (mapv lvl/param lps)
            eqs (mapv (fn [[a b]] (u/mk-eq-heq ctx a b)) pairs)
            conj-type (mk-and ctx eqs)
            lhs (u/app (e/const' (.name ctor-ci) us) (concat params args1))
            rhs (u/app (e/const' (.name ctor-ci) us) (concat params args2))
            eq-type (u/mk-eq ctx lhs rhs)
            [_ inj-fn] (inj-proof ctx ctor-ci opened eqs)
            ;; mkNoConfusion may have realized the constructor's noConfusion in ctx
            env (:env @ctx)
            ;; C.inj: every binder implicit (withImplicitBinderInfos)
            all (vec (concat params args1 new))
            saved (into {} (map (fn [x] [x (:info (u/decl ctx x))])) all)
            _ (u/implicit! ctx all)
            inj-type (u/mk-forall-fvars ctx all (u/mk-arrow ctx eq-type conj-type))
            inj-val (u/mk-lambda-fvars ctx all inj-fn)
            env (env/check-constant env (env/mk-thm (name/mk-str (.name ctor-ci) "inj") lps inj-type inj-val))
            _ (u/set-env! ctx env)
            ;; C.injEq: the constructor's binder kinds, the new fields explicit
            _ (doseq [[x info] saved] (swap! ctx assoc-in [:lctx (e/fvar-id x) :info] info))
            _ (doseq [x new] (swap! ctx assoc-in [:lctx (e/fvar-id x) :info] :default))
            inj-app (u/app (e/const' (name/mk-str (.name ctor-ci) "inj") us) all)
            hc (u/local-decl ctx "hc" conj-type)
            back (u/mk-lambda-fvars ctx [hc] (u/app (converse ctx new eqs pairs eq-type [])
                                                    (concat new (and-components hc (count eqs)))))
            prop-intro (u/app (u/const' "Eq.propIntro" []) [eq-type conj-type inj-app back])
            inj-eq-type (u/mk-forall-fvars ctx all (u/mk-eq ctx eq-type conj-type))
            inj-eq-val (u/mk-lambda-fvars ctx all prop-intro)]
        (env/check-constant env (env/mk-thm (name/mk-str (.name ctor-ci) "injEq") lps inj-eq-type inj-eq-val))))))

(defn mk-injective-theorems
  "Lean mkInjectiveTheorems for `n`: `env` with `C.inj`/`C.injEq` for every constructor with
   fields that has equations; unchanged for an inductive predicate, an unsafe type, or an env
   without `Eq.propIntro`."
  [env n]
  (let [ind (env/lookup env (name/from-string (str n)))]
    (if (or (nil? ind) (not (.isInduct ind)) (.isUnsafe ind)
            (nil? (env/lookup env (name/from-string "Eq.propIntro")))
            (u/prop-former? (u/context env) (.type ind)))
      env
      (reduce (fn [env c]
                (let [ci (env/lookup! env c)]
                  (if (pos? (.numFields ci)) (mk-for-ctor env ind ci) env)))
              env (.ctors ind)))))
