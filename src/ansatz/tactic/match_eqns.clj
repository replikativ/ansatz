(ns ansatz.tactic.match-eqns
  "On-demand matcher equations and splitters, following Lean's MatchEqs.lean. Equations for
   later overlapping alternatives carry precedence hypotheses."
  (:require [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.reduce :as red]
            [ansatz.kernel.tc :as tc]
            [ansatz.meta.fvar-subst :as subst]
            [ansatz.meta.constructions.util :as u]
            [ansatz.meta.match.matcher-info :as mi]
            [ansatz.meta.match.match :as match]
            [ansatz.meta.match.simp-h :as simp-h]
            [ansatz.eqns :as eqns]
            [ansatz.matchers :as mtch]
            [ansatz.state :as state]
            [ansatz.simp-sources :as simp-sources]
            [ansatz.tactic.proof :as proof]
            [ansatz.tactic.basic :as basic]
            [ansatz.tactic.extract :as extract]))

(def ^:private fresh-counter (atom 70000000))
(defn- fresh-id [] (swap! fresh-counter inc))

(defn- open-foralls
  "Instantiate the first `n` Pi-binders of `ty` with fresh fvars. Returns [fvars body] where
   `fvars` is the vector of opened fvars (with their binder types) and `body` is the remaining type."
  [ty n]
  (loop [ty ty, i 0, fvars []]
    (if (or (>= i n) (not (e/forall? ty)))
      [fvars ty]
      (let [bt (e/forall-type ty)
            fid (fresh-id)
            fv (e/fvar fid)]
        (recur (e/instantiate1 (e/forall-body ty) fv) (inc i) (conj fvars [fid fv bt]))))))

(defn- count-foralls [ty]
  (loop [ty ty, n 0] (if (e/forall? ty) (recur (e/forall-body ty) (inc n)) n)))

(defn- close-foralls [body binders]
  (reduce (fn [b [fid _ bt]]
            (e/forall' "x" bt (e/abstract1 b fid) :default))
          body (reverse binders)))

(defn- close-lambdas [body binders]
  (reduce (fn [b [fid _ bt]]
            (e/lam "x" bt (e/abstract1 b fid) :default))
          body (reverse binders)))

(defn- precedence-guard
  "Lean MatchEqs.mkNotAlt, instantiated at the later arm's patterns. A guard says
   that no choice of the earlier arm's fields can make all discriminants equal."
  [environment scope current-patterns prior-alt prior-info]
  (let [[_ _ prior-type] prior-alt
        n (if (:unit-thunk prior-info) 1 (:num-fields prior-info))
        [opened result] (open-foralls prior-type n)
        fields (if (:unit-thunk prior-info) [] opened)
        [_ prior-patterns] (e/get-app-fn-args result)
        lctx (reduce (fn [lctx [id _ type]]
                       (red/lctx-add-local lctx id "x" type))
                     {} scope)
        field-decls (mapv (fn [[id _ type]] {:tag :local :id id :name "x" :type type})
                          fields)]
    (simp-h/not-alt environment lctx current-patterns prior-patterns field-decls)))

(defn- split-candidate [ps]
  (let [goal (proof/current-goal ps)
        [h args] (e/get-app-fn-args (:type goal))
        target (if (and (e/const? h)
                        (= "Eq" (name/->string (e/const-name h)))
                        (= 3 (count args)))
                 (nth args 1)
                 (:type goal))
        lctx (:lctx goal)]
    (some (fn [[id d]]
            (when (and (= :local (:tag d))
                       (not= target (e/abstract1 target id)))
              (let [ty (red/whnf (:env ps) (:type d) lctx)
                    h (e/get-app-fn ty)
                    ci (when (e/const? h) (env/lookup (:env ps) (e/const-name h)))]
                (when (and ci (.isInduct ci)) id))))
          (sort-by (comp - key) lctx))))

(defn- guard-eq-args [ty]
  (let [[h args] (e/get-app-fn-args ty)]
    (when (and (e/const? h) (= "Eq" (name/->string (e/const-name h)))
               (= 3 (count args)))
      args)))

(defn- match-guard-pattern [st field-ids pattern actual subst]
  (cond
    (and (e/fvar? pattern) (contains? field-ids (e/fvar-id pattern)))
    (let [id (e/fvar-id pattern)]
      (if-let [old (get subst id)]
        (when (tc/is-def-eq st old actual) subst)
        (assoc subst id actual)))
    :else
    (let [[ph pa] (e/get-app-fn-args pattern)
          [ah aa] (e/get-app-fn-args actual)]
      (if (and (e/const? ph) (e/const? ah)
               (= (e/const-name ph) (e/const-name ah))
               (= (count pa) (count aa)))
        (reduce (fn [s [p a]] (when s (match-guard-pattern st field-ids p a s)))
                subst (map vector pa aa))
        (when (tc/is-def-eq st pattern actual) subst)))))

(defn- close-by-guard [ps]
  ;; Solve the branch where an earlier arm would have matched. This is the
  ;; simple constructor-injection case of Lean Match.SolveOverlap: instantiate
  ;; the earlier arm's fields from the current constructor and apply its
  ;; precedence hypothesis to reflexive equalities.
  (let [goal (proof/current-goal ps)
        lctx (:lctx goal)
        st (tc/attach-lctx (tc/mk-tc-state (:env ps)) lctx)
        ctx (atom st)]
    (some
     (fn [[id d]]
       (try
         (let [[fields body]
               (loop [ty (:type d) fields []]
                 (if (and (e/forall? ty) (= "x" (e/forall-name ty)))
                   (let [fid (fresh-id) fv (e/fvar fid)]
                     (recur (e/instantiate1 (e/forall-body ty) fv)
                            (conj fields [fid fv])))
                   [fields ty]))
               field-ids (set (map first fields))
               equations
               (loop [ty body acc []]
                 (if (e/forall? ty)
                   (if-let [args (guard-eq-args (e/forall-type ty))]
                     (recur (e/instantiate1 (e/forall-body ty) (e/fvar (fresh-id)))
                            (conj acc args))
                     nil)
                   (when (and (e/const? ty)
                              (= "False" (name/->string (e/const-name ty))))
                     acc)))
               subst (when (seq equations)
                       (reduce (fn [s [_ lhs rhs]]
                                 (when s (match-guard-pattern st field-ids rhs lhs s)))
                               {} equations))]
           (when (and subst (every? #(contains? subst (first %)) fields))
             (let [values (mapv #(get subst (first %)) fields)
                   guard-term (apply e/app* (e/fvar id) values)
                   false-term
                   (reduce (fn [term _]
                             (let [ty (tc/infer-type st term)
                                   [alpha lhs rhs] (guard-eq-args (e/forall-type ty))]
                               (when-not (tc/is-def-eq st lhs rhs)
                                 (throw (ex-info "guard equality is not reflexive" {})))
                               (e/app term (u/mk-eq-refl ctx lhs))))
                           guard-term equations)
                   target (:type goal)
                   proof-term (e/app* (e/const' (name/from-string "False.elim")
                                                [(u/get-level ctx target)])
                                      target false-term)]
               (basic/exact ps proof-term))))
         (catch Exception _ nil)))
     (sort-by (comp - key) lctx))))

(defn- prove-by-stuck-cases [type names guard-names higher-guard?]
  ;; Lean MatchEqs.proveCondEqThm repeatedly tries refl/contradiction, then
  ;; casesOnStuckLHS. This fallback follows that loop on the inductive locals
  ;; still present in the equality target; simp handles the resulting iota and
  ;; precedence-hypothesis reductions. Each proof is checked by the kernel.
  (let [[ps _] (proof/start-proof @state/ansatz-env type)
        ps (basic/intros ps names)
        run (requiring-resolve 'ansatz.core/run-tactic)
        steps (atom 0)
        close-guard (when (seq guard-names)
                      (cons 'first
                            (map #(list 'and_then '(exfalso) (list 'apply %) '(rfl))
                                 guard-names)))]
    (letfn [(try-step [ps f]
              (try (f ps) (catch clojure.lang.ExceptionInfo _ ps)))
            (solve [ps depth]
              (when (> (swap! steps inc) 32)
                (throw (ex-info "match-eqns: cases search exceeded 32 goals"
                                {:kind :match-eqns-search-limit})))
              (let [ps (try-step ps basic/rfl)
                    ps (if (seq (:goals ps)) (try-step ps basic/contradiction) ps)
                    ps (if (seq (:goals ps)) (or (close-by-guard ps) ps) ps)
                    ps (if (and (seq (:goals ps)) close-guard)
                         (try-step ps #(run % close-guard)) ps)
                    ps (if (and (seq (:goals ps))
                                (or (pos? depth) (not higher-guard?)))
                         (try-step ps #(run % '(simp_all))) ps)]
                (if (empty? (:goals ps))
                  ps
                  (if (>= depth 4)
                    ps
                    (if-let [fid (split-candidate ps)]
                      (basic/all-goals (basic/cases ps fid) #(solve % (inc depth)))
                      ps)))))]
      (let [ps (solve ps 0)]
        (when-not (proof/solved? ps)
          (throw (ex-info (str "Stuck after cases\n" (proof/format-goals ps))
                          {:kind :match-eqns-stuck-cases})))
        (extract/verify ps)
        (extract/extract ps)))))

(defn- prove-conditional-equation [type binders guards]
  ;; Lean MatchEqs.proveCondEqThm tries reflexivity and contradiction, then
  ;; repeatedly splits stuck discriminants. The proof driver above follows
  ;; that shape and checks the extracted term with the kernel.
  (let [names (mapv #(str "x" %) (range (+ (count binders) (count guards))))
        guard-names (mapv #(symbol (nth names %))
                          (range (count binders) (+ (count binders) (count guards))))
        higher-guard? (some #(and (e/forall? %) (= "x" (e/forall-name %))) guards)]
    (try (prove-by-stuck-cases type names guard-names higher-guard?)
         (catch Exception e
           (throw (ex-info "match-eqns: could not prove conditional equation"
                           {:kind :match-eqns-proof-failure :type type}
                           e))))))

(defn matcher-alt-data
  "Telescope analysis of matcher `match-name` for the split tactic. Returns
     {:levels [..] :params [[id fv ty]..] :motive [id fv ty] :discr-types [ty..]
      :alts [{:pattern <discr pattern expr> :ys-types [ty..] :unit-thunk bool} ..]}
   where each alt's :pattern is the discriminant value (from the alt's conclusion `motive pattern`),
   :ys-types the alt's own binder types (the constructor fields; a single Unit for a unit thunk).
   Single-discriminant matchers only for now (multi-discriminant patterns nest)."
  [env match-name]
  (let [info (mtch/matcher-info env match-name)
        _ (when-not info (throw (ex-info "matcher-alt-data: no MatcherInfo" {:name match-name})))
        ci (env/lookup! env (name/from-string match-name))
        lvls (vec (.levelParams ci))
        {:keys [num-params num-discrs alts]} info
        num-alts (count alts)
        [tele _] (open-foralls (.type ci) (+ num-params 1 num-discrs num-alts))
        params (subvec tele 0 num-params)
        motive (nth tele num-params)
        discrs (subvec tele (+ num-params 1) (+ num-params 1 num-discrs))
        altfvs (subvec tele (+ num-params 1 num-discrs) (+ num-params 1 num-discrs num-alts))
        [_ motive-fv _] motive
        alt-data
        (mapv (fn [i [_ _ alt-ty]]
                (let [{:keys [num-fields num-overlaps unit-thunk]} (nth alts i)
                      n (+ num-fields num-overlaps (mi/get-num-discr-eqs info)
                           (if unit-thunk 1 0))
                      [opened alt-body] (open-foralls alt-ty n)
                      ys (subvec opened 0 (if unit-thunk 1 num-fields))
                      guards (if unit-thunk []
                                 (subvec opened num-fields (+ num-fields num-overlaps)))
                      [_ pat-args] (e/get-app-fn-args alt-body)]
                  {:pattern (first pat-args)        ; single-discriminant: one pattern
                   :patterns (vec pat-args)
                   :fields ys :guards guards
                   :ys-types (mapv (fn [[_ _ ty]] ty) ys)
                   :unit-thunk unit-thunk}))
              (range num-alts) altfvs)]
    {:levels lvls
     :params params
     :motive motive
     :discr-types (mapv (fn [[_ _ ty]] ty) discrs)
     :discrs discrs
     :num-params num-params :num-discrs num-discrs
     :alts alt-data}))

(defn get-equations-for
  "Generate matcher equations and a splitter on demand. Non-overlapping matchers
   receive a transparent splitter alias."
  [match-name]
  (if-let [cached (get (env/get-extension @state/ansatz-env :match-eqns {}) match-name)]
    cached
    (let [env0 @state/ansatz-env
          info (mtch/matcher-info env0 match-name)
          _ (when-not info (throw (ex-info "match-eqns: no MatcherInfo for matcher" {:name match-name})))
          ci (env/lookup! env0 (name/from-string match-name))
          lvls (vec (.levelParams ci))
          us (mapv #(lvl/param %) lvls)
          mconst (e/const' (name/from-string match-name) us)
          mtype (.type ci)
          {:keys [num-params num-discrs alts]} info
          num-alts (count alts)
        ;; Open the matcher telescope: params, motive, discrs, alts.
          [tele _] (open-foralls mtype (+ num-params 1 num-discrs num-alts))
          params (subvec tele 0 num-params)
          motive (nth tele num-params)
          discrs (subvec tele (+ num-params 1) (+ num-params 1 num-discrs))
          altfvs (subvec tele (+ num-params 1 num-discrs) (+ num-params 1 num-discrs num-alts))
          [_ motive-fv _] motive
        ;; Elimination universe: uElimPos picks which level param is the elim level (Prop if null).
          elim-lvl (if-let [p (:u-elim-pos info)] (lvl/param (nth lvls p)) lvl/zero)
          eq-base (str match-name ".eq_")
        ;; Build one equation per alt.
          results
          (map-indexed
           (fn [i [_ alt-fv alt-ty]]
             (let [{:keys [num-fields unit-thunk]} (nth alts i)
                 ;; Open the alt's own binders (ys): for a unit thunk that's the single Unit param.
                   n-alt-binders (if unit-thunk 1 num-fields)
                   [ys alt-body] (open-foralls alt-ty n-alt-binders)
                 ;; alt conclusion = motive-fv patterns…  → extract the discriminant patterns.
                   [head pat-args] (e/get-app-fn-args alt-body)
                   patterns (vec pat-args)
                 ;; rhsArgs: a unit thunk is applied to Unit.unit; otherwise the field fvars.
                   unit-unit (e/const' (name/from-string "Unit.unit") [])
                   rhs-args (if unit-thunk [unit-unit] (mapv second ys))
                 ;; eq binders: params ++ motive ++ (ys, only for non-thunk) ++ alts.
                   ys-binders (if unit-thunk [] ys)
                   binders (vec (concat params [motive] ys-binders altfvs))
                   binder-ids (mapv first binders)
                 ;; LHS: matcher params motive patterns alts   (discrs := patterns)
                   lhs (apply e/app* mconst
                              (concat (mapv second params) [motive-fv] patterns (mapv second altfvs)))
                 ;; RHS: alt rhsArgs
                   rhs (apply e/app* alt-fv rhs-args)
                 ;; result type = motive patterns (the matcher's conclusion at this pattern)
                   res-ty (apply e/app* motive-fv patterns)
                   eq-ty-open (e/app* (e/const' (name/from-string "Eq") [elim-lvl]) res-ty lhs rhs)
                   guards (vec (keep (fn [j]
                                       (precedence-guard env0
                                                         (concat params [motive] discrs altfvs ys)
                                                         patterns (nth altfvs j) (nth alts j)))
                                     (mi/overlaps-overlapping (:overlaps info) i)))
                   eq-ty-open (reduce (fn [body guard] (e/arrow guard body))
                                      eq-ty-open (reverse guards))
                 ;; proof: Eq.refl res-ty rhs  (lhs ≡ rhs by iota on the concrete pattern)
                   proof-open (e/app* (e/const' (name/from-string "Eq.refl") [elim-lvl]) res-ty rhs)
                   eq-ty (close-foralls eq-ty-open binders)
                   eq-val (if (seq guards)
                            (prove-conditional-equation eq-ty binders guards)
                            (close-lambdas proof-open binders))
                   eq-name (str eq-base (inc i))]
               {:name eq-name :type eq-ty :value eq-val}))
           altfvs)
        ;; Lean rebuilds a separate matcher when alternatives overlap. Otherwise
        ;; the splitter is a transparent alias of the original matcher.
          splitter-name (str match-name ".splitter")
          results (vec results)]
    ;; Install (idempotent): add the splitter def + each eq_i theorem to the GLOBAL env.
      (swap! state/ansatz-env
             (fn [env]
               (let [[env splitter-info]
                     (cond
                       (env/lookup env (name/from-string splitter-name))
                       [env (mi/get-matcher-info-core? env splitter-name)]

                       (mi/non-overlapping? info)
                       [(env/check-constant env (env/mk-def (name/from-string splitter-name)
                                                            lvls mtype mconst :hints :abbrev))
                        info]

                       :else
                       (let [{:keys [ctx input]} (match/input-from-matcher env match-name splitter-name)
                             res (match/mk-matcher ctx (assoc input :is-splitter (:overlaps info)))]
                         (when (seq (:counter-examples res))
                           (throw (ex-info "Splitter is not exhaustive"
                                           {:kind :match-splitter-error
                                            :matcher match-name
                                            :counter-examples (:counter-examples res)})))
                         [(:env res) (:info res)]))]
                 (let [env (reduce (fn [env {:keys [name type value]}]
                                     (if (env/lookup env (ansatz.kernel.name/from-string name))
                                       env
                                       (env/check-constant env (env/mk-thm (ansatz.kernel.name/from-string name)
                                                                           lvls type value))))
                                   env results)]
                 ;; Make the equations available to simp by default (the matcher reduces in each
                 ;; split branch via eqᵢ — Lean's simpMatchTargetCore; we route it through simp's set).
                   (let [env (reduce (fn [env {:keys [name]}]
                                       (-> env
                                           (env/update-extension :simp-lemmas #{} conj name)
                                           (simp-sources/mark-local-registration name)))
                                     env results)
                         names (mapv (comp name/from-string :name) results)
                         env (eqns/register-eqn-thms env match-name names [])]
                     (env/update-extension env :match-eqns {} assoc match-name
                                           {:eqn-names (mapv :name results)
                                            :splitter-name splitter-name
                                            :splitter-info splitter-info
                                            :info info :levels lvls}))))))
      (get (env/get-extension @state/ansatz-env :match-eqns {}) match-name))))

;; ── split-matcher: applyMatchSplitter for single-discriminant matchers ──
;; The splitter is the eliminator. We do `by-cases`
;; (basic.clj by-cases) generalized to it: motive  λd. (Eq DiscrType discr d) → Goal  applied to the
;; discriminant + Eq.refl, one minor premise per alternative carrying `h : discr = patternᵢ`.

(defn- mk-tc [env lctx] (tc/attach-lctx (tc/mk-tc-state env) lctx))

(defn replace-subterm
  "Structurally replace every occurrence of `target` in `expr` with `repl`. `target` must have no
   loose bvars (a goal-context term, e.g. the matcher discriminant), so no index adjustment is needed."
  [expr target repl]
  (if (= expr target)
    repl
    (case (e/tag expr)
      :app (e/app (replace-subterm (e/app-fn expr) target repl)
                  (replace-subterm (e/app-arg expr) target repl))
      :lam (e/lam (e/lam-name expr) (replace-subterm (e/lam-type expr) target repl)
                  (replace-subterm (e/lam-body expr) target repl) (e/lam-info expr))
      :forall (e/forall' (e/forall-name expr) (replace-subterm (e/forall-type expr) target repl)
                         (replace-subterm (e/forall-body expr) target repl) (e/forall-info expr))
      :let (e/let' (e/let-name expr) (replace-subterm (e/let-type expr) target repl)
                   (replace-subterm (e/let-value expr) target repl)
                   (replace-subterm (e/let-body expr) target repl))
      :proj (e/proj (e/proj-type-name expr) (e/proj-idx expr)
                    (replace-subterm (e/proj-struct expr) target repl))
      :mdata (e/mdata (e/mdata-data expr) (replace-subterm (e/mdata-expr expr) target repl))
      expr)))

(defn split-matcher
  "Split a single-discriminant matcher using its on-demand splitter. Overlapping
   alternatives receive the same precedence hypotheses as Lean's splitter."
  [ps tgt]
  (let [goal (proof/current-goal ps)
        _ (when-not goal (throw (ex-info "split-matcher: no goal" {:split-retry true})))
        head (:head tgt)
        match-name (name/->string (e/const-name head))
        args (vec (:args tgt))
        original-env @state/ansatz-env
        info (mtch/matcher-info original-env match-name)
        _ (when-not info
            (throw (ex-info "split-matcher: not a known matcher" {:split-retry true})))
        eqns (get-equations-for match-name)
        splitter-name (if (mi/non-overlapping? info) match-name (:splitter-name eqns))
        env @state/ansatz-env
        ps (assoc ps :env env)
        d (matcher-alt-data env splitter-name)
        np (:num-params d) nd (:num-discrs d)
        _ (when (not= nd 1)
            (throw (ex-info "split-matcher: multi-discriminant not yet supported" {:split-retry true})))
        _ (when (< (count args) (+ np 1 nd (count (:alts d))))
            (throw (ex-info "split-matcher: matcher application not fully applied" {:split-retry true})))
        st (mk-tc env (:lctx goal))
        params-actual (subvec args 0 np)
        discr (nth args (+ np 1))
        telescope-subst (into {}
                              (concat (map (fn [[id] actual] [id actual])
                                           (:params d) params-actual)
                                      [[(first (:motive d)) (nth args np)]]
                                      (map (fn [[id] actual] [id actual])
                                           (:discrs d) [discr])))
        discr-type (tc/infer-type st discr)
        sort-level (fn [t] (let [s (try (red/whnf env (tc/infer-type st t) (:lctx goal)) (catch Throwable _ nil))]
                             (if (and s (e/sort? s)) (e/sort-level s) lvl/zero)))
        eq-lvl (sort-level discr-type)            ; Eq over DiscrType elements (Bool → 1)
        goal-lvl (sort-level (:type goal))         ; Goal : Prop → 0
        head-lvls (vec (e/const-levels head))
        u-elim-pos (:u-elim-pos info)
        us (if (and u-elim-pos (< u-elim-pos (count head-lvls)))
             (assoc head-lvls u-elim-pos goal-lvl) head-lvls)
        eq-c (e/const' (name/from-string "Eq") [eq-lvl])
        ;; one subgoal per alternative
        [ps alt-infos]
        (reduce
         (fn [[ps acc] alt]
           (let [opened (vec (concat (:fields alt) (:guards alt)))
                 [ps local-ids] (reduce (fn [[ps ids] _]
                                          (let [[ps id] (proof/alloc-id ps)]
                                            [ps (conj ids id)]))
                                        [ps []] opened)
                 local-subst (into telescope-subst
                                   (map (fn [[old] id] [old (e/fvar id)])
                                        opened local-ids))
                 ys-ids (subvec local-ids 0 (count (:fields alt)))
                 guard-ids (subvec local-ids (count (:fields alt)))
                 ys-types (mapv #(subst/apply local-subst (nth % 2)) (:fields alt))
                 guard-types (mapv #(subst/apply local-subst (nth % 2)) (:guards alt))
                 pattern (subst/apply local-subst (:pattern alt))
                 [ps h-id] (proof/alloc-id ps)
                 h-type (e/app* eq-c discr-type discr pattern)
                 lctx (reduce (fn [lc [id ty]] (red/lctx-add-local lc id "y" ty))
                              (:lctx goal) (map vector ys-ids ys-types))
                 lctx (reduce (fn [lc [id ty]] (red/lctx-add-local lc id "notAlt" ty))
                              lctx (map vector guard-ids guard-types))
                 lctx (red/lctx-add-local lctx h-id "h" h-type)
                 ;; subgoal type = Goal[discr := patternᵢ]  (the matcher reduces via eqᵢ here)
                 sg-type (replace-subterm (:type goal) discr pattern)
                 [ps sg-id] (proof/fresh-mvar-replacing ps sg-type lctx (:id goal))]
             [ps (conj acc {:pattern pattern :ys-ids ys-ids :ys-types ys-types
                            :guard-ids guard-ids :guard-types guard-types
                            :h-id h-id :h-type h-type :goal sg-id})]))
         [ps []] (:alts d))
        ;; motive = λ d:DiscrType. (Eq DiscrType discr d) → Goal[discr := d]
        [ps dfv-id] (proof/alloc-id ps)
        dfv (e/fvar dfv-id)
        motive (e/lam "d" discr-type
                      (e/abstract1 (e/arrow (e/app* eq-c discr-type discr dfv)
                                            (replace-subterm (:type goal) discr dfv))
                                   dfv-id)
                      :default)]
    (-> (proof/assign-mvar ps (:id goal)
                           {:kind :split-matcher
                            :match-name splitter-name :us us
                            :params params-actual :discr discr :discr-type discr-type
                            :eq-lvl eq-lvl :motive motive
                            :alts alt-infos})
        (proof/record-tactic :split-matcher [discr] (:id goal)))))
