(ns ansatz.meta.constructions.size-of
  "Lean v4.36.0 Meta/SizeOf.lean for one non-nested inductive: `mkSizeOfFn` (`T._sizeOf_1`),
   `mkSizeOfInstances` (`T._sizeOf_inst`, registered as an instance) and `mkSizeOfSpecTheorem`
   (`C.sizeOf_spec`, proved by `Eq.refl`).

   A field contributes `sizeOf field` through instance synthesis, with a local `[SizeOf p]`
   dictionary for every parameter `p` that is a type (mkLocalInstances); a recursive field
   contributes its induction hypothesis in `_sizeOf_1`; a higher-order field is ignored unless
   its domains are `Unit` (ignoreField). Lean's synthesis always succeeds through the low-priority
   `instSizeOfDefault`; an environment without it fails here before anything is installed. The
   result is a new env or an exception, never a partial one.

   A field type's inductive whose instance a smaller environment omits (the bundled Init tier
   has no `Option._sizeOf_inst` or `Bool._sizeOf_inst`) would otherwise resolve to the zero-valued
   default, where Lean's Init has the generated instance: such an inductive gets the same
   construction first (Lean generates those Init instances with this algorithm too)."
  (:require [ansatz.meta.constructions.util :as u]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]
            [ansatz.tactic.instance :as inst]))

(def ^:private nat (u/const' "Nat" []))

(defn- size-of-class [ctx ty] (u/app (u/const' "SizeOf" [(u/get-level ctx ty)]) [ty]))

(defn- synthesize! [ctx goal]
  (let [env (:env @ctx)]
    (or (inst/synthesize* @ctx env (inst/index-for env) goal 0)
        (throw (ex-info (str "failed to synthesize " (e/->string goal))
                        {:kind :size-of :goal goal})))))

(defn- mk-size-of
  "mkAppM ``SizeOf.sizeOf #[x]."
  [ctx x]
  (let [ty (u/infer-type ctx x)]
    (u/app (u/const' "SizeOf.sizeOf" [(u/get-level ctx ty)])
           [ty (synthesize! ctx (size-of-class ctx ty)) x])))

(defn- mk-add
  "AppBuilder.mkAdd at Nat."
  [a b]
  (u/app (u/const' "HAdd.hAdd" [lvl/zero lvl/zero lvl/zero])
         [nat nat nat (u/app (u/const' "instHAdd" [lvl/zero]) [nat (u/const' "instAddNat" [])]) a b]))

(defn- scoped
  "Run `f` and drop the local declarations it opened (Lean's telescopes are scoped), so a
   temporary binder can never be found as a local instance afterwards."
  [ctx f]
  (let [saved (:lctx @ctx)]
    (try (f) (finally (swap! ctx assoc :lctx saved)))))

(defn- with-local-instances
  "mkLocalInstances: an instance-implicit `inst : ∀ ys, SizeOf (p ys)` for each parameter `p`
   whose (reduced) telescope ends in a type."
  [ctx params]
  (vec (keep (fn [p]
               (when-let [it (scoped ctx #(let [[ys _] (u/forall-telescope ctx (u/infer-type ctx p))
                                                t (u/app p ys)]
                                            (when (e/sort? (u/whnf ctx (u/infer-type ctx t)))
                                              (u/mk-forall-fvars ctx ys (size-of-class ctx t)))))]
                 (u/local-decl ctx "inst" it :inst-implicit)))
             params)))

(defn- ignore-field-type?
  "ignoreFieldType: a (reduced) function type is ignored unless it is an arrow from `Unit`
   (the domain compared syntactically, as `isConstOf ``Unit`) to a type not ignored."
  [ctx t]
  (let [t (u/whnf ctx t)]
    (if (e/forall? t)
      (if (and (not (e/has-loose-bvars? (e/forall-body t)))
               (= (e/forall-type t) (u/const' "Unit" [])))
        (recur ctx (e/forall-body t))
        true)
      false)))

(defn- ih-target
  "isInductiveHypothesis?: the major `x` when `fvar : … → motive … x` for a motive in `motives`."
  [ctx motives fvar]
  (scoped ctx #(let [[_ body] (u/forall-telescope ctx (u/infer-type ctx fvar))]
                 (when (and (e/app? body) (some #{(e/get-app-fn body)} motives))
                   (e/app-arg body)))))

(defn- rec-field-form-ih [ctx ih]
  (if (e/forall? (u/whnf ctx (u/infer-type ctx ih)))
    (recur ctx (e/app ih (u/const' "Unit.unit" [])))
    ih))

(defn- mk-size-of-fn
  "mkSizeOfFn: `decl-name := fun params insts indices major => T.rec.{1,us} params motives minors indices major`."
  [env rec-name decl-name]
  (let [ctx (u/context env)
        rec (env/lookup! env (name/from-string rec-name))
        np (.numParams rec) nm (.numMotives rec) nmin (.numMinors rec) ni (.numIndices rec)
        [xs _] (u/forall-telescope ctx (.type rec))
        params (subvec xs 0 np)
        motives (subvec xs np (+ np nm))
        minors (subvec xs (+ np nm) (+ np nm nmin))
        indices (subvec xs (+ np nm nmin) (+ np nm nmin ni))
        major (nth xs (+ np nm nmin ni))
        lps (vec (rest (.levelParams rec)))
        insts (with-local-instances ctx params)
        motives' (mapv (fn [m] (let [[ys _] (u/forall-telescope ctx (u/infer-type ctx m))]
                                 (u/mk-lambda-fvars ctx ys nat))) motives)
        val (u/app (u/const' rec-name (into [(lvl/succ lvl/zero)] (map lvl/param lps)))
                   (concat params motives'))
        [minors' _] (u/forall-telescope ctx (u/infer-type ctx val) nmin)
        minor-vals
        (mapv (fn [m m']
                (let [[ys _] (u/forall-telescope ctx (u/infer-type ctx m))
                      [ys' _] (u/forall-telescope ctx (u/infer-type ctx m') (count ys))
                      ;; Lean's inferType instantiates the motives with instantiateBetaRevRange:
                      ;; an induction hypothesis has type `Nat`, not `(fun … => Nat) …`
                      _ (doseq [y ys']
                          (swap! ctx update-in [:lctx (e/fvar-id y) :type]
                                 #(let [[f as] (e/get-app-fn-args %)] (if (e/lam? f) (u/beta f as) %))))
                      ihs (into {} (keep-indexed (fn [i y] (when-let [x (ih-target ctx motives y)]
                                                             [(e/get-app-fn x) i])) ys))
                      body (reduce (fn [acc [y y']]
                                     (cond
                                       (ih-target ctx motives y) acc
                                       (ignore-field-type? ctx (u/infer-type ctx y)) acc
                                       :else (mk-add acc (if-let [i (get ihs y)]
                                                           (rec-field-form-ih ctx (nth ys' i))
                                                           (mk-size-of ctx y')))))
                                   (e/lit-nat 1) (map vector ys ys'))]
                  (u/mk-lambda-fvars ctx ys' body)))
              minors minors')
        _ (u/implicit! ctx (concat params indices))
        binders (vec (concat params insts indices [major]))]
    (u/add-definition env ctx decl-name lps binders nat
                      (u/app val (concat minor-vals indices [major])))))

(defn- mk-size-of-instance
  "mkSizeOfInstances for one type: `T._sizeOf_inst : ∀ params indices insts, SizeOf (T params indices)`."
  [env ind-name fn-name]
  (let [ctx (u/context env)
        info (env/lookup! env (name/from-string ind-name))
        np (.numParams info)
        us (mapv lvl/param (.levelParams info))
        [xs _] (u/forall-telescope ctx (.type info))
        params (subvec xs 0 np) indices (subvec xs np)
        insts (with-local-instances ctx params)
        ind-type (u/app (u/const' ind-name us) xs)
        m (u/local-decl ctx "m" ind-type)
        v (u/mk-lambda-fvars ctx [m] (u/app (u/const' fn-name us) (concat params insts indices [m])))
        mk (u/app (u/const' "SizeOf.mk" [(u/get-level ctx ind-type)]) [ind-type v])]
    (u/add-definition env ctx (str ind-name "._sizeOf_inst") (vec (.levelParams info))
                      (vec (concat xs insts)) (size-of-class ctx ind-type) mk)))

(defn- mk-size-of-spec
  "mkSizeOfSpecTheorem (non-nested): `C.sizeOf_spec : ∀ params insts fields, sizeOf (C …) = 1 + Σ sizeOf field`."
  [env info ctor]
  (let [ctx (u/context env)
        ci (env/lookup! env ctor)
        us (mapv lvl/param (.levelParams ci))
        np (.numParams ci)
        [xs _] (u/forall-telescope ctx (.type ci))
        params (subvec xs 0 np) fields (subvec xs np)
        ctor-app (u/app (e/const' ctor us) xs)
        insts (with-local-instances ctx params)
        ctor-type (u/infer-type ctx ctor-app)
        inst (u/app (u/const' (str (.name info) "._sizeOf_inst") us)
                    (concat params (subvec (vec (e/get-app-args ctor-type)) (.numParams info)) insts))
        lhs (u/app (u/const' "SizeOf.sizeOf" [(u/get-level ctx ctor-type)]) [ctor-type inst ctor-app])
        rhs (reduce (fn [acc f] (if (ignore-field-type? ctx (u/infer-type ctx f)) acc (mk-add acc (mk-size-of ctx f))))
                    (e/lit-nat 1) fields)
        binders (vec (concat params insts fields))
        type (u/mk-forall-fvars ctx binders (u/mk-eq ctx lhs rhs))
        value (u/mk-lambda-fvars ctx binders (u/mk-eq-refl ctx rhs))]
    (env/check-constant env (env/mk-thm (name/mk-str ctor "sizeOf_spec") (vec (.levelParams ci)) type value))))

(defn shape-eligible?
  "mkSizeOfInstances' guard (not an inductive predicate, large eliminating, safe), restricted to
   the shapes ported here: one type, no nested occurrences, no instance yet. The SizeOf prelude
   itself is the caller's to provide (see eligible?)."
  [env n]
  (let [info (env/lookup env (name/from-string (str n)))
        rec (env/lookup env (name/from-string (str n ".rec")))]
    (boolean
     (and info rec (.isInduct info)
          (not (.isUnsafe info)) (= 1 (count (.all info))) (zero? (.numNested info))
          (not (u/prop-former? (u/context env) (.type info)))
          (> (count (.levelParams rec)) (count (.levelParams info)))
          (not (env/lookup env (name/from-string (str n "._sizeOf_inst"))))))))

(defn eligible? [env n]
  (and (shape-eligible? env n) (some? (env/lookup env (name/from-string "SizeOf")))))

(defn- defaulted?
  "Whether `SizeOf (c xs)`, at fresh parameters with local dictionaries, resolves to the
   zero-valued `instSizeOfDefault` (no instance of its own in this environment)."
  [env c]
  (let [ctx (u/context env)
        info (env/lookup! env (name/from-string (str c)))
        [xs _] (u/forall-telescope ctx (.type info))
        _ (with-local-instances ctx (subvec xs 0 (.numParams info)))
        t (u/app (u/const' c (mapv lvl/param (.levelParams info))) xs)
        r (inst/synthesize* @ctx env (inst/index-for env) (size-of-class ctx t) 0)]
    (or (nil? r) (= "instSizeOfDefault" (str (e/const-name (e/get-app-fn r)))))))

(declare mk-size-of-instances*)

(defn- realize-field-instances
  "The construction for each inductive among the constructor field types (and their reduced
   forms: `Unit` is `PUnit`) that is eligible here and would otherwise resolve to the default.
   `st` = {:env :visited #{names} :order [installed names]}."
  [st n]
  (let [env (:env st)
        ctx (u/context env)
        ;; the heads of a field type and of its arguments (`Option Bool`: Option, Bool), through
        ;; non-dependent arrows (`Unit → Opt Nat`)
        heads (fn heads [t]
                (if (e/forall? t)
                  (concat (heads (e/forall-type t))
                          (when-not (e/has-loose-bvars? (e/forall-body t)) (heads (e/forall-body t))))
                  (let [[h as] (e/get-app-fn-args t)]
                    (concat (when (e/const? h) [(str (e/const-name h))]) (mapcat heads as)))))
        classes (env/get-extension env :classes #{})
        cs (reduce (fn [acc ctor]
                     (let [[xs _] (u/forall-telescope ctx (.type (env/lookup! env ctor)))]
                       (into acc (mapcat #(let [t (u/infer-type ctx %)] (concat (heads t) (heads (u/whnf ctx t)))))
                             xs)))
                   #{} (.ctors (env/lookup! env (name/from-string n))))]
    (reduce (fn [st c]
              (if (and (not ((:visited st) c)) (not (contains? classes c))
                       (shape-eligible? (:env st) c) (defaulted? (:env st) c))
                (mk-size-of-instances* st c)
                st))
            st (sort cs))))

(defn- mk-size-of-instances* [st n]
  (let [st (realize-field-instances (update st :visited conj n) n)
        env (:env st)
        fn-name (str n "._sizeOf_1")
        env (mk-size-of-fn env (str n ".rec") fn-name)
        env (mk-size-of-instance env n fn-name)
        env (inst/add-instance env (name/from-string (str n "._sizeOf_inst")))
        info (env/lookup! env (name/from-string n))]
    (-> st
        (assoc :env (reduce (fn [env c] (mk-size-of-spec env info c)) env (.ctors info)))
        (update :order conj n))))

(defn mk-size-of-instances
  "[env' types]: `env` with `T._sizeOf_1`, `T._sizeOf_inst` (registered as an instance at Lean's
   default priority) and every `C.sizeOf_spec`, for `n` and for the field-type inductives realized
   first (`types`, in installation order, `n` last); or an exception. `[env []]` when not eligible?."
  [env n]
  (if-not (eligible? env n)
    [env []]
    ((juxt :env :order) (mk-size-of-instances* {:env env :visited #{} :order []} (str n)))))
