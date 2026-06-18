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
            [ansatz.matchers :as mtch]
            [ansatz.state :as state]))

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
               (reduce (fn [env {:keys [name type value]}]
                         (if (env/lookup env (ansatz.kernel.name/from-string name))
                           env
                           (env/add-constant env (env/mk-thm (ansatz.kernel.name/from-string name)
                                                             lvls type value))))
                       env results))))
    {:eqn-names (mapv :name results) :splitter-name splitter-name :info info :levels lvls}))
