(ns ansatz.tactic.match-eqns
  "Faithful port of Lean's `Match.getEquationsFor` (MatchEqs.lean) for NON-OVERLAPPING matchers —
   the matchers we have (all casesOn-based, no overlapping patterns). For those Lean's splitter IS
   the matcher itself (a transparent alias, MatchEqs.lean:231-243), and each equation
     match_N params motive patternsᵢ alts = altᵢ rhsArgs
   is proved by `rfl` (the matcher applied to a concrete constructor pattern reduces, via casesOn,
   to the alternative). We GENERATE these on demand (they are not in the kernel export) and memoize.

   Returns a MatchEqns map {:eqn-names [..] :splitter-name <str> :info <MatcherInfo>} (the Lean
   MatchEqns struct, MatchEqsExt.lean:17-24). Overlapping matchers (mkMatcher/process) are deferred
   behind this same interface."
  (:require [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.reduce :as red]
            [ansatz.kernel.tc :as tc]
            [ansatz.matchers :as mtch]
            [ansatz.state :as state]
            [ansatz.tactic.proof :as proof]))

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
                (let [{:keys [num-fields unit-thunk]} (nth alts i)
                      n (if unit-thunk 1 num-fields)
                      [ys alt-body] (open-foralls alt-ty n)
                      [_ pat-args] (e/get-app-fn-args alt-body)]
                  {:pattern (first pat-args)        ; single-discriminant: one pattern
                   :patterns (vec pat-args)
                   :ys-types (mapv (fn [[_ _ ty]] ty) ys)
                   :unit-thunk unit-thunk}))
              (range num-alts) altfvs)]
    {:levels lvls
     :params params
     :motive motive
     :discr-types (mapv (fn [[_ _ ty]] ty) discrs)
     :num-params num-params :num-discrs num-discrs
     :alts alt-data}))

(defn get-equations-for
  "Generate (idempotently) the match equations + splitter for matcher `match-name`, add them to the
   GLOBAL env, and return the MatchEqns map. Non-overlapping only (asserts)."
  [match-name]
  (let [env0 @state/ansatz-env
        info (mtch/matcher-info env0 match-name)
        _ (when-not info (throw (ex-info "match-eqns: no MatcherInfo for matcher" {:name match-name})))
        _ (when-not (mtch/non-overlapping? info)
            (throw (ex-info "match-eqns: overlapping matcher not yet supported (deferred)" {:name match-name})))
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
                 ;; proof: Eq.refl res-ty rhs  (lhs ≡ rhs by iota on the concrete pattern)
                 proof-open (e/app* (e/const' (name/from-string "Eq.refl") [elim-lvl]) res-ty rhs)
                 ;; close over binder fvars (outermost first → abstract in reverse)
                 close (fn [body]
                         (reduce (fn [b [fid _ bt]]
                                   (e/forall' "x" bt (e/abstract1 b fid) :default))
                                 body (reverse binders)))
                 close-lam (fn [body]
                             (reduce (fn [b [fid _ bt]]
                                       (e/lam "x" bt (e/abstract1 b fid) :default))
                                     body (reverse binders)))
                 eq-ty (close eq-ty-open)
                 eq-val (close-lam proof-open)
                 eq-name (str eq-base (inc i))]
             {:name eq-name :type eq-ty :value eq-val}))
         altfvs)
        ;; Splitter alias: match_N.splitter := match_N  (abbrev = reducible alias; Lean
        ;; MatchEqs.lean:235-243 makes the non-overlapping splitter an @[inline] abbrev of the matcher).
        splitter-name (str match-name ".splitter")
        results (vec results)]
    ;; Install (idempotent): add the splitter def + each eq_i theorem to the GLOBAL env.
    (swap! state/ansatz-env
           (fn [env]
             (let [env (if (env/lookup env (name/from-string splitter-name))
                         env
                         (env/add-constant env (env/mk-def (name/from-string splitter-name)
                                                           lvls mtype mconst :hints :abbrev)))]
               (let [env (reduce (fn [env {:keys [name type value]}]
                                   (if (env/lookup env (ansatz.kernel.name/from-string name))
                                     env
                                     (env/add-constant env (env/mk-thm (ansatz.kernel.name/from-string name)
                                                                       lvls type value))))
                                 env results)]
                 ;; Make the equations available to simp by default (the matcher reduces in each
                 ;; split branch via eqᵢ — Lean's simpMatchTargetCore; we route it through simp's set).
                 (reduce (fn [env {:keys [name]}]
                           (env/update-extension env :simp-lemmas #{} conj name))
                         env results)))))
    {:eqn-names (mapv :name results) :splitter-name splitter-name :info info :levels lvls}))

;; ── split-matcher: faithful applyMatchSplitter for non-overlapping single-discriminant matchers ──
;; The matcher IS the eliminator (Lean's non-overlapping splitter = the matcher). We do `by-cases`
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
  "Split a non-overlapping single-discriminant matcher application `tgt` ({:head :args}) found in
   the current goal. Produces one subgoal per alternative, each with `h : discr = patternᵢ` (and the
   alt's field hyps); the installed match equations reduce the matcher in each branch. Signals
   {:split-retry true} for shapes not yet supported (multi-discriminant / overlapping)."
  [ps tgt]
  (let [goal (proof/current-goal ps)
        _ (when-not goal (throw (ex-info "split-matcher: no goal" {:split-retry true})))
        head (:head tgt)
        match-name (name/->string (e/const-name head))
        args (vec (:args tgt))
        env @state/ansatz-env
        info (mtch/matcher-info env match-name)
        _ (when-not (and info (mtch/non-overlapping? info))
            (throw (ex-info "split-matcher: not a known non-overlapping matcher" {:split-retry true})))
        d (matcher-alt-data env match-name)
        np (:num-params d) nd (:num-discrs d)
        _ (when (not= nd 1)
            (throw (ex-info "split-matcher: multi-discriminant not yet supported" {:split-retry true})))
        _ (when (< (count args) (+ np 1 nd (count (:alts d))))
            (throw (ex-info "split-matcher: matcher application not fully applied" {:split-retry true})))
        ;; install the match equations + splitter (idempotent) so simp can reduce each branch
        _ (get-equations-for match-name)
        st (mk-tc env (:lctx goal))
        params-actual (subvec args 0 np)
        discr (nth args (+ np 1))
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
           (let [pattern (:pattern alt)            ; param-free for filter.match_1 (TODO: instantiate w/ params)
                 ys-types (:ys-types alt)
                 [ps ys-ids] (reduce (fn [[ps ids] _] (let [[ps id] (proof/alloc-id ps)] [ps (conj ids id)]))
                                     [ps []] ys-types)
                 [ps h-id] (proof/alloc-id ps)
                 h-type (e/app* eq-c discr-type discr pattern)
                 lctx (reduce (fn [lc [id ty]] (red/lctx-add-local lc id "y" ty))
                              (:lctx goal) (map vector ys-ids ys-types))
                 lctx (red/lctx-add-local lctx h-id "h" h-type)
                 ;; subgoal type = Goal[discr := patternᵢ]  (the matcher reduces via eqᵢ here)
                 sg-type (replace-subterm (:type goal) discr pattern)
                 [ps sg-id] (proof/fresh-mvar-replacing ps sg-type lctx (:id goal))]
             [ps (conj acc {:pattern pattern :ys-ids ys-ids :ys-types ys-types
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
                            :match-name match-name :us us
                            :params params-actual :discr discr :discr-type discr-type
                            :eq-lvl eq-lvl :motive motive
                            :alts alt-infos})
        (proof/record-tactic :split-matcher [discr] (:id goal)))))
