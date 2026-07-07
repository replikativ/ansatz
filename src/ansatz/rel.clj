;; Measurable relational programming over the ansatz metacontext.

(ns ansatz.rel
  "A weighted micro-Kanren whose substitution IS the ansatz metacontext.

   Ordinary miniKanren threads a substitution of logic variables through
   goals; here the state threads `ansatz.meta`'s metacontext, so the logic
   variables are real kernel `Expr.mvar`s / level mvars and unification is
   `meta/is-def-eq` — full CIC definitional equality with metavariable
   assignment. Everything the tactic layer can express (goals, holes,
   telescopes) is therefore directly relational, and holes can be filled in
   ANY position: the proof term, the goal, or a hypothesis TYPE
   (omnidirectional search — e.g. infer the assumption that closes a proof).

   Measure semantics: every state carries a provenance `:prov` (a semiring
   from ansatz.provenance; MaxMinProb/log by default) and a `:tag`. `condw`
   clause weights act as branch priors: they both order the search
   (weighted interleave, Barliman's conde-weighted) and multiply the
   branch's measure. `run` returns states best-first by weight, so the
   answer stream is an unnormalized measure over solutions; an SMC layer
   can resample on top (states are pure values — forking is free).

   The kernel disposes: `certify` zonks a solution and strict-checks it
   with the trusted kernel, so nothing the search does can smuggle in an
   ill-typed proof.

   Search states are pure Clojure values: fork = hold a reference. This is
   the SMC invariant inherited from the single-metacontext architecture."
  (:require [ansatz.meta :as meta]
            [ansatz.provenance :as prov]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.tc :as tc]
            [ansatz.tactic.instance :as inst]))

;; ============================================================
;; Search state
;; ============================================================

(def ^:private id-base
  "Fresh mvar ids start high above tactic/elaborator ranges to avoid
   collision when a rel search is embedded in a proof state."
  90000000)

(defn state
  "Fresh search state over `env`.

   :lctx    ambient local context (hypotheses), red/lctx shape
   :mctx    ansatz.meta metacontext (the substitution)
   :prov    the provenance semiring (measure algebra; default MaxMinProb)
   :tag     this branch's measure tag (default = prov-one)
   :overlay a RELATIONAL env extension above the fixed oracle: name →
            {:type Expr :value Expr|nil} declaration-holes the search may
            synthesize and SHARE across goals (see `declareo`/`lookupo`).
   :next-id fresh id counter (pure value — forking a state is safe)"
  [env & {:keys [lctx mctx prov tag overlay next-id]}]
  (let [prov (or prov prov/default-provenance)]
    {:env env
     :lctx (or lctx {})
     :mctx (or mctx meta/empty-context)
     :prov prov
     :tag (or tag (prov/prov-one prov))
     :overlay (or overlay {})
     :next-id (or next-id id-base)}))

(defn measure
  "The reported measure of a state's branch (prov-recover of its tag)."
  [s]
  (prov/prov-recover (:prov s) (:tag s)))

(defn combined-measure
  "The measure of a DISJUNCTION of branches (⊕ their tags, then recover). Under
   ProofsProb this is the exact probability-of-provability over the alternative
   proofs `states`, counting a shared uncertain fact ONCE (correlation-aware)."
  [prov states]
  (prov/prov-recover
   prov (reduce #(prov/prov-plus prov %1 %2)
                (prov/prov-zero prov) (map :tag states))))

(defn facto
  "Depend this branch on a LABELED uncertain fact `label` with credence `prob`
   — folds it into the measure via the provenance semiring (`prov-fact`). Under
   ProofsProb the label is tracked symbolically, so a fact shared by alternative
   proofs is counted once by `combined-measure` (exact WMC); under MaxMinProb it
   folds as a scalar log-prob. `k` continues."
  [label prob k]
  (fn [s]
    (let [prov (:prov s)]
      ((k) (update s :tag #(prov/prov-times prov % (prov/prov-fact prov label prob)))))))

(defn order-weight
  "The search-ordering key of a state (higher explored/returned first)."
  [s]
  (prov/prov-weight (:prov s) (:tag s)))

(defn- tc-st
  "Kernel TC view of a search state (env + ambient lctx)."
  [s]
  (tc/attach-lctx (tc/mk-tc-state (:env s)) (:lctx s)))

(defn- next-id! [s] [(:next-id s) (update s :next-id inc)])

;; ============================================================
;; Streams — microKanren: nil | (Choice state stream) | (fn [] stream)
;; A Choice pair (NOT a Clojure cons — the tail may be a thunk).
;; ============================================================

(deftype Choice [head tail])

(def mzero nil)
(defn unit [s] (Choice. s nil))

(defn mplus
  "Fair interleave of two streams (thunks swap sides = productive steps)."
  [$1 $2]
  (cond
    (nil? $1) $2
    (fn? $1) (fn [] (mplus $2 ($1)))
    :else (Choice. (.head ^Choice $1) (mplus $2 (.tail ^Choice $1)))))

(defn bind [$ g]
  (cond
    (nil? $) mzero
    (fn? $) (fn [] (bind ($) g))
    :else (mplus (g (.head ^Choice $)) (bind (.tail ^Choice $) g))))

(defn pull
  "Force a stream to its first mature answer (or nil)."
  [$]
  (if (fn? $) (recur ($)) $))

(defn stream-take
  "Take up to n states from a stream (n nil = all)."
  [n $]
  (lazy-seq
   (when-not (and n (zero? n))
     (when-let [$ (pull $)]
       (cons (.head ^Choice $) (stream-take (when n (dec n)) (.tail ^Choice $)))))))

;; ============================================================
;; Goal combinators — a goal is state → stream
;; ============================================================

(defn succeed [s] (unit s))
(defn fail [_] mzero)

(defn all
  "Conjunction."
  [& goals]
  (fn [s]
    (reduce (fn [$ g] (bind $ g)) (unit s) goals)))

(defn any
  "Fair disjunction."
  [& goals]
  (fn [s]
    (reduce (fn [$ g] (mplus $ (fn [] (g s)))) mzero goals)))

(defn condw
  "Weighted disjunction: clauses are [weight goal ...goals]. The weight is a
   branch PRIOR: it folds into the branch measure via the provenance ⊗
   (`prov-from-prob (w/Σw)`) and biases the search order (heavier clauses are
   streamed first). Barliman's conde-weighted unified with a provenance
   semiring (probKanren's weighted semantics, MaxMinProb by default)."
  [& clauses]
  (let [total (double (reduce + (map first clauses)))]
    (fn [s]
      (let [P (:prov s)]
        (->> clauses
             (sort-by (comp - first))
             (map (fn [[w & goals]]
                    (let [prior (prov/prov-from-prob P (/ (double w) total))
                          s' (update s :tag #(prov/prov-times P % prior))]
                      (fn [] ((apply all goals) s')))))
             (reduce mplus mzero))))))

(defn weightedo
  "Fold a probability mass `p` into the current branch measure (⊗)."
  [p]
  (fn [s] (unit (update s :tag #(prov/prov-times (:prov s) % (prov/prov-from-prob (:prov s) p))))))

(defn project*
  "Escape hatch: f gets the state and returns a goal."
  [f]
  (fn [s] ((f s) s)))

;; ============================================================
;; Core relational primitives over the metacontext
;; ============================================================

(defn ===
  "Unification = CIC definitional equality with mvar assignment.
   Succeeds with the updated metacontext, fails silently on mismatch."
  [a b]
  (fn [s]
    (when-let [mctx' (try (meta/is-def-eq (:mctx s) (tc-st s) a b)
                          (catch Exception _ nil))]
      (unit (assoc s :mctx mctx')))))

(defn fresh-level
  "Mint a fresh universe-level mvar; f : Level → goal."
  [f]
  (fn [s]
    (let [[id s] (next-id! s)
          s (update s :mctx meta/add-level-mvar-decl id)]
      ((f (lvl/mvar id)) s))))

(defn fresh
  "Mint a fresh expression mvar of type `type` in the ambient lctx;
   f : Expr(mvar) → goal. The mvar is a first-class hole: it can stand for
   a term, a proof, a type, or a proposition — direction-free."
  [type f]
  (fn [s]
    (let [[id s] (next-id! s)
          s (update s :mctx meta/add-expr-mvar-decl id type (:lctx s))]
      ((f (e/mvar id)) s))))

(defn fresh-ty
  "Mint a fresh TYPE hole: ?T : Sort ?u with ?u a fresh level.
   f : Expr(mvar) → goal."
  [f]
  (fresh-level
   (fn [u]
     (fresh (e/sort' u) f))))

(defn fresh-in
  "Like `fresh`, but declare the hole in an EXPLICIT local context (a
   sub-context of the ambient one). Needed when the hole's value must be
   assignable into another mvar declared in that smaller context — the
   checked-assignment scope guard rejects values mentioning mvars with a
   larger lctx (Lean would ctxApprox-restrict; we mint narrow instead)."
  [lctx type f]
  (fn [s]
    (let [[id s] (next-id! s)
          s (update s :mctx meta/add-expr-mvar-decl id type lctx)]
      ((f (e/mvar id)) s))))

(defn fresh-ty-in
  "`fresh-ty` in an explicit local context (see `fresh-in`)."
  [lctx f]
  (fresh-level
   (fn [u]
     (fresh-in lctx (e/sort' u) f))))

(defn zonk
  "Reify an expression under a state's metacontext."
  [s expr]
  (meta/zonk-expr (:mctx s) expr))

(defn assigned?
  "Is the mvar assigned (directly or delayed) in the state?"
  [s mv]
  (meta/expr-assigned-or-delayed? (:mctx s) (e/mvar-id mv)))

(defn mvar-type
  "Zonked declared type of an mvar in a state."
  [s mv]
  (zonk s (:type (meta/expr-decl (:mctx s) (e/mvar-id mv)))))

;; ============================================================
;; run
;; ============================================================

(defn run
  "Run `goal` from state `s0`; return up to n result states sorted
   best-first by log-weight (n nil = all — beware divergence)."
  ([n s0 goal] (run n s0 goal {}))
  ([n s0 goal {:keys [raw?]}]
   (let [states (stream-take n (goal s0))]
     (if raw? states (sort-by (comp - order-weight) states)))))

;; ============================================================
;; Proof relations — the omnidirectional tactic vocabulary
;; ============================================================

(defn- const-info [s cname]
  (env/lookup (:env s) (if (string? cname) (name/from-string cname) cname)))

(defn resolve-decl
  "Unified relational lookup: resolve `cname` to a declaration head+type from
   the env-OVERLAY first, then the fixed env ORACLE. Returns {:head Expr :type
   Expr :s state'} with fresh level mvars instantiated, or nil. Overlay decls
   are monomorphic (no level params) here. This is `lookupo`'s ground-compiled
   core: known name → oracle; overlay name → the relational declaration-hole."
  [s cname]
  (let [nm (if (string? cname) (name/from-string cname) cname)
        cstr (if (string? cname) cname (name/->string cname))]
    (if-let [ov (get (:overlay s) cstr)]
      {:head (e/const' nm []) :type (:type ov) :s s}
      (when-let [ci (const-info s cname)]
        (let [lparams (vec (.levelParams ci))
              [s lvls] (reduce (fn [[s acc] _]
                                 (let [[id s] (next-id! s)]
                                   [(update s :mctx meta/add-level-mvar-decl id)
                                    (conj acc (lvl/mvar id))]))
                               [s []] lparams)]
          {:head (e/const' (.name ci) lvls)
           :type (e/instantiate-level-params (.type ci) (zipmap lparams lvls))
           :s s})))))

(defn with-lemma
  "Resolve `cname` (overlay-or-oracle) and call f : [head-expr type] → goal. If
   `cname` is an UNCERTAIN overlay declaration (a `:credence` axiom not yet
   synthesized), fold that credence into the branch measure as a LABELED fact
   (keyed by the name, so the same uncertain lemma used by two proofs is counted
   once under ProofsProb) — probability-of-provability then falls out of the
   real search."
  [cname f]
  (fn [s]
    (if-let [{:keys [head type s]} (resolve-decl s cname)]
      (let [cstr (if (string? cname) cname (name/->string cname))
            ov (get (:overlay s) cstr)
            s (if (and ov (:credence ov) (nil? (:value ov)))
                (update s :tag #(prov/prov-times (:prov s) %
                                                 (prov/prov-fact (:prov s) cstr (:credence ov))))
                s)]
        ((f [head type]) s))
      mzero)))

(defn declareo
  "RELATIONALLY extend the env with a declaration-hole `name : type` (monomorphic,
   closed type) — a lemma/definition the search may use now (via
   `applyo`/`with-lemma`/`lookupo`) and synthesize/assume LATER, SHARED across
   goals. It is added to the WORKING env immediately as an AXIOM (so the kernel
   can type-check proof terms that reference it during the search) and tracked in
   `:overlay` with `:value nil` (an open obligation). `certify` upgrades any
   overlay decl whose value has been synthesized (`set-overlay-value`) to a
   checked DEF, and reports the rest as `:assumed`. `k` is the continuation.
   `:credence` (optional) marks this as an UNCERTAIN premise with that prior;
   the search folds it into the measure when the lemma is applied (see
   `with-lemma`), so probability-of-provability accounts for which uncertain
   premises a proof uses."
  [name type k & {:keys [credence]}]
  (fn [s]
    (let [ty (zonk s type)
          s (try (assoc s :env
                        (env/check-constant (:env s)
                                            (env/mk-axiom (name/from-string name) [] ty)))
                 (catch Throwable _ s))]  ; ill-formed type → decl not admitted
      ((k) (assoc-in s [:overlay name] {:type ty :value nil :credence credence})))))

(defn set-overlay-value
  "Record a synthesized value (proof/definition body) for an overlay decl."
  [s name value]
  (assoc-in s [:overlay name :value] value))

(defn hole-type
  "The (zonked) type of an open hole `mvar` in state `s` — for inspecting a
   stuck state's obligations at the staging level."
  [s mvar]
  (zonk s (mvar-type s mvar)))

(defn fill
  "Staging-level MODIFY: fill an open hole `mvar` in `s` with `term`
   (kernel-checked assignment). Returns s' or nil. This is how the LLM/proposer
   supplies an instance or lemma the search left OPEN (`*instance-mode* :hole`),
   then continues — certify / resume — WITHOUT re-running the search."
  [s mvar term]
  (when-let [mctx (try (meta/checked-assign-expr (:mctx s) (e/mvar-id mvar) term {:env (:env s)})
                       (catch Throwable _ nil))]
    (assoc s :mctx mctx)))

(defn lookupo
  "The relational env lookup as a goal: resolve `cname` (overlay ∪ oracle) and
   pass its [head type] to k; fail if unknown. Ground/known names take the fast
   oracle path; overlay names are the relational declaration-holes."
  [cname k]
  (with-lemma cname k))

(defn- peel-telescope
  "forallMetaTelescope: peel ∀-binders into fresh mvars. Instance-implicit
   binders are tagged `:inst-implicit?` in the metacontext (so they route to
   instance synthesis rather than blind term enumeration) and flagged
   `:inst?` in the returned args. Returns [s' args conclusion] where each arg
   is {:mvar Expr :inst? bool :explicit? bool}."
  [s ty]
  (loop [s s, t ty, args []]
    (if (e/forall? t)
      (let [info (e/forall-info t)
            inst? (= info :inst-implicit)
            [id s] (next-id! s)
            s (update s :mctx
                      #(meta/add-expr-mvar-decl % id (e/forall-type t) (:lctx s)
                                                (when inst? {:inst-implicit? true})))]
        (recur s
               (e/instantiate1 (e/forall-body t) (e/mvar id))
               (conj args {:mvar (e/mvar id) :inst? inst? :explicit? (= info :default)})))
      [s args t])))

(defonce ^:private inst-index-cache (java.util.concurrent.ConcurrentHashMap.))

(defn- instance-index
  "Cached typeclass instance index for `env` (build-instance-index; empty for a
   lazy PSS env, where synthesis falls back to on-demand discovery)."
  [env]
  (or (.get inst-index-cache env)
      (let [idx (try (inst/build-instance-index env) (catch Throwable _ {}))]
        (.put inst-index-cache env idx) idx)))

(def ^:dynamic *instance-mode*
  "How `applyo` handles an instance-implicit arg it can neither unify nor
   synthesize: `:prune` (default — kill the branch, the hygiene guard) or
   `:hole` (leave it as an OPEN obligation the search can prove OR the
   staging level / LLM can fill — capture/modify/continue, omnidirectional)."
  :prune)

(defn- assign-instances
  "SPECIALIZE-DOWN — instance synthesis. For each instance-implicit arg not
   already pinned by the conclusion unification: if its type is ground,
   synthesize an instance (ansatz.tactic.instance — Lean-4-style: local
   instances, the index, PSS on-demand discovery) and assign it. Returns
   [s' missing] where `missing` is the mvars that stayed undetermined AND
   unsynthesizable — the caller prunes (`:prune`) or exposes them as fillable
   holes (`:hole`). Lets a lemma over `[Preorder α]` apply to a concrete `Nat`."
  [s args]
  (let [tcst (tc-st s)
        idx (instance-index (:env s))]
    (reduce (fn [[s missing] a]
              (if (or (not (:inst? a)) (assigned? s (:mvar a)))
                [s missing]
                (let [ty (zonk s (mvar-type s (:mvar a)))]
                  (if (meta/has-expr-mvar? ty)
                    [s (conj missing (:mvar a))]    ; instance type undetermined
                    (if-let [it (try (inst/synthesize* tcst (:env s) idx ty 0)
                                     (catch Throwable _ nil))]
                      (if-let [mctx (try (meta/checked-assign-expr
                                          (:mctx s) (e/mvar-id (:mvar a)) it {:env (:env s)})
                                         (catch Throwable _ nil))]
                        [(assoc s :mctx mctx) missing]
                        [s (conj missing (:mvar a))]) ; assignment rejected
                      [s (conj missing (:mvar a))]))))) ; no instance found
            [s []] args)))

(defn- unify-concl
  "INSTANCE-AWARE conclusion unification (Lean's instance postponement). Unify
   goal type `gty` with the lemma `concl`, DEFERRING any head-argument position
   that contains an as-yet-unsynthesized instance mvar: unify the type/value
   positions first (determining the type mvars), then SYNTHESIZE the instances
   (their types are now ground), then unify the deferred positions — where the
   lemma's instance PROJECTION (e.g. `Preorder.toLE Nat ?inst`) is now concrete
   and defeq to the goal's (`instLENat`). Falls back to plain === (different
   heads / no instance args)."
  [gty concl args]
  (fn [s]
    (let [[ch cargs] (e/get-app-fn-args concl)
          [gh gargs] (e/get-app-fn-args gty)
          inst-ids (into #{} (keep (fn [a] (when (:inst? a) (e/mvar-id (:mvar a)))) args))]
      (if (and (seq inst-ids)
               (e/const? ch) (e/const? gh)
               (= (e/const-name ch) (e/const-name gh))
               (= (count cargs) (count gargs)))
        (let [defer? (fn [carg] (boolean (some #(meta/expr-occurs? (:mctx s) % carg) inst-ids)))
              pairs (map vector cargs gargs)
              nowp (remove (fn [[c _]] (defer? c)) pairs)
              defp (filter (fn [[c _]] (defer? c)) pairs)]
          ((all (apply all (for [[c gg] nowp] (=== c gg)))            ; type/value positions
                (fn [s2]
                  (let [[s3 missing] (assign-instances s2 args)       ; synthesize instances
                        missing-set (set (map e/mvar-id missing))]
                    (if (and (seq missing) (not= *instance-mode* :hole))
                      mzero
                      ;; unify the deferred positions whose instance was pinned;
                      ;; SKIP those still holed (they'll match once the hole is filled)
                      (let [holed? (fn [carg] (boolean (some #(meta/expr-occurs? (:mctx s3) % carg) missing-set)))]
                        ((apply all (for [[c gg] defp :when (not (holed? c))] (=== c gg))) s3))))))
           s))
        ((=== gty concl) s)))))

(defn applyo
  "Relational `apply`: refine goal-hole `g` with lemma `cname`.
   Peels the lemma's ∀-telescope into fresh mvars, INSTANCE-AWARELY unifies its
   conclusion with g's type (synthesizing typeclass instances — specialize-down,
   so a lemma over `[Preorder α]` applies to `Nat`), assigns g := (lemma …),
   then calls k : [unsolved-EXPLICIT-arg-mvars] → goal for the obligations."
  [g cname k]
  (with-lemma cname
    (fn [[lemma ty]]
      (fn [s]
        (let [[s args concl] (peel-telescope s ty)
              gty (mvar-type s g)]
          ((all (unify-concl gty concl args)
                ;; pin instance args; :prune kills the branch on a missing
                ;; instance, :hole records it as a fillable obligation.
                (fn [s]
                  (let [[s' missing] (assign-instances s args)]
                    (cond
                      (empty? missing) (unit s')
                      (= *instance-mode* :hole) (unit (assoc s' ::inst-holes missing))
                      :else mzero)))
                (=== g (reduce e/app lemma (map :mvar args)))
                (project*
                 (fn [s]
                   ;; obligations = explicit args + (in :hole mode) missing instances
                   (k (into (->> args (filter :explicit?) (map :mvar)
                                 (remove #(assigned? s %)) vec)
                            (remove #(assigned? s %) (::inst-holes s)))))))
           s))))))

(defn assumptiono
  "Relational `assumption`: close goal-hole `g` with a hypothesis.
   Unifies each hypothesis TYPE with g's type first — so when a hypothesis
   type is itself a hole (?A), this ASSIGNS it: inferring the assumption
   is the same relation run in the other direction."
  [g]
  (fn [s]
    (let [gty (mvar-type s g)
          hyps (for [[fid decl] (:lctx s)
                     :when (= :local (:tag decl))]
                 [fid decl])]
      ((apply any
              (for [[fid decl] hyps]
                (all (=== (:type decl) gty)
                     (=== g (e/fvar fid)))))
       s))))

(defn assigno
  "Directly assign a GOAL metavariable `g := v` via the checked-assignment
   (tactic/`exact`) path — after unifying v's inferred type with g's declared
   type. Unlike `===`, this succeeds on SYNTHETIC-OPAQUE goals (e.g. named
   surface holes `?x`, and every goal a tactic is meant to close): `===` refuses
   to *unify away* an opaque goal, but a search that FILLS one is doing an
   `exact`, not a unification. `v` may still carry holes — checked-assign
   validates the (zonked) assignment against the kernel-facing guards."
  [g v]
  (fn [s]
    (let [mctx (:mctx s)
          st (tc-st s)
          gty (mvar-type s g)
          vty (try (meta/infer-type mctx st v) (catch Exception _ nil))]
      (when vty
        (when-let [mctx (try (meta/is-def-eq mctx st vty gty) (catch Exception _ nil))]
          (when-let [mctx (try (meta/checked-assign-expr
                                mctx (e/mvar-id g) (meta/zonk-expr mctx v)
                                {:env (:env s)})
                               (catch Exception _ nil))]
            (unit (assoc s :mctx mctx))))))))

(defn exacto
  "Relational `exact`: fill goal-hole `g` with `term` (checked-assign path, so
   it works on synthetic-opaque goals). `term` may contain holes; so may g's
   type."
  [g term]
  (assigno g term))

(defn apply-hypo
  "Relational application of a HYPOTHESIS: close goal-hole `g` by applying
   local hypothesis `fid` to `k` fresh argument holes. Unifies the
   hypothesis type with the non-dependent arrow shape ?B₁ → … → ?Bₖ → goal.

   The hypothesis type may itself be a HOLE: unifying the hole with the
   arrow shape ASSIGNS it, so the search can infer an IMPLICATION — this is
   modus ponens run backwards (higher-order assumption inference). For a
   concrete ∀/→ hypothesis the same unification decomposes it structurally.
   k : obligation holes → goal (continuation over the argument proofs)."
  [g fid k cont]
  (fn [s]
    (when-let [decl (get (:lctx s) fid)]
      (let [gty (mvar-type s g)
            hyp-ty (:type decl)
            ;; When the hypothesis type is a HOLE, the arrow-shape type holes
            ;; end up INSIDE its assignment — so they must live in (a subset
            ;; of) ITS declared lctx, or the checked-assignment scope guard
            ;; rejects the value (Lean would ctxApprox-restrict instead).
            shape-lctx (if (e/mvar? hyp-ty)
                         (:lctx (meta/expr-decl (:mctx s) (e/mvar-id hyp-ty)))
                         (:lctx s))]
        ((letfn [(go [i bs shapes]
                     (if (zero? i)
                       (let [shape (reduce (fn [acc B] (e/arrow B acc))
                                           gty (rseq shapes))]
                         (all (=== hyp-ty shape)
                              (=== g (reduce e/app (e/fvar fid) bs))
                              (cont bs)))
                       (fresh-ty-in
                        shape-lctx
                        (fn [B]
                          (fresh B
                                 (fn [b]
                                   (go (dec i) (conj bs b) (conj shapes B))))))))]
           (go k [] []))
         s)))))

;; ============================================================
;; inhabito — THE inhabitation relation. proveo/expro/synthesizeo are presets:
;; one bidirectional judgment (Curry–Howard: prove = inhabit a type). The
;; primitives (assumptiono=Var, applyo=App-elim, Π-intro) are the typing rules;
;; the driver is the ONLY place that recurses; the measure rides on condw.
;; ============================================================

(declare telescope open-telescope inhabito)

(defn- solve-obligations
  "Discharge a refiner's obligation mvars, DEPENDENCY-AWARE: obligations whose
   zonked goal-TYPE is already ground are attacked first; those still mentioning
   an unsolved sibling mvar are deferred until an earlier `===` grounds them
   (Barliman's conde1 deferral — avoids enumerating against a flex goal type)."
  [obs moves depth]
  (fn [s]
    (let [ground? (fn [ob] (not (meta/has-expr-mvar? (mvar-type s ob))))
          {ready true deferred false} (group-by ground? obs)]
      ((apply all (map #(inhabito % moves depth) (concat ready deferred))) s))))

(defn- intro-and-inhabit
  "Π-INTRODUCTION (checking mode): goal type is `∀ …, C`; open the ∀-telescope
   into fresh fvar hypotheses, inhabit the conclusion C, then
   `g := λ telescope. proof`. Introduction is FREE — it does NOT consume
   application `depth` (it is structurally decreasing on the goal type), so a
   higher-order lemma whose conclusion is itself a Π is handled uniformly."
  [g gty moves depth]
  (fn [s]
    (let [base-lctx (:lctx s)
          [lctx' concl fids] (open-telescope base-lctx gty (:next-id s))
          s (assoc s :lctx lctx' :next-id (+ (long (:next-id s)) (count fids)))
          locals (mapv (fn [fid] (let [d (get lctx' fid)]
                                   {:fid fid :name (:name d) :type (:type d)}))
                       fids)]
      ((fresh-in lctx' concl
                 (fn [b]
                   (all (inhabito b moves depth)
                        (fn [s2]
                          (let [value (telescope e/lam locals
                                                 (e/abstract-many (zonk s2 b) fids))
                                s3 (assoc s2 :lctx base-lctx)]
                            (when-let [mctx (try (meta/checked-assign-expr
                                                  (:mctx s3) (e/mvar-id g)
                                                  (zonk s3 value) {:env (:env s3)})
                                                 (catch Exception _ nil))]
                              (unit (assoc s3 :mctx mctx))))))))
       s))))

(defn inhabito
  "THE inhabitation relation — fill goal-hole `g` with a term of its type by
   depth-bounded weighted search. `moves` : (state, goal) →
     {:leaves [[w leaf-goal] …]   ; g → goal, closes g (available at EVERY depth)
      :refiners [[w refiner] …]}  ; (g, k) → goal, k : obligations → goal
   A Π-goal fires the introduction rule; otherwise the moves supply the
   elimination/var rules and the driver — the ONLY recursion — discharges each
   refiner's obligations via `solve-obligations`. Moves never recurse. Measure
   and ordering ride on `condw`; the driver is measure-agnostic."
  [g moves depth]
  (fn [s]
    (if (assigned? s g)
      (unit s)
      (let [gty (mvar-type s g)]
        (if (e/forall? gty)
          ((intro-and-inhabit g gty moves depth) s)
          (let [{:keys [leaves refiners]} (moves s g)
                recur-obs (fn [obs] (solve-obligations obs moves (dec depth)))
                clauses (concat leaves
                                (when (pos? depth)
                                  (for [[w refine] refiners]
                                    [w (refine g recur-obs)])))]
            (if (seq clauses) ((apply condw clauses) s) mzero)))))))

(defn proveo
  "Depth-bounded relational prover — a preset of `inhabito`: close `g` by an
   assumption, an applied lemma (`lemmas` ∪ the env-overlay, so a declared
   lemma is automatically first-class), or an applied hypothesis.
   opts :hyp-arities — arities to try applying each local hypothesis at
   (default [] off; a hole-typed hyp then infers an implication)."
  ([g lemmas depth] (proveo g lemmas depth {}))
  ([g lemmas depth {:keys [hyp-arities] :or {hyp-arities []}}]
   (inhabito
    g
    (fn [s g]
      {:leaves [[8 (assumptiono g)]]
       :refiners (concat
                  (for [[w nm] (concat lemmas (map (fn [nm] [1 nm]) (keys (:overlay s))))]
                    [w (fn [g k] (applyo g nm k))])
                  (for [[fid decl] (:lctx s)
                        :when (= :local (:tag decl))
                        a hyp-arities]
                    [(/ 1.0 (double a)) (fn [g k] (apply-hypo g fid a k))]))})
    depth)))

;; ============================================================
;; expro — type-directed open-grammar term enumeration
;; ============================================================

(defn expro
  "Type-directed relational term ENUMERATOR: fill goal-hole `g` (of any type,
   not just Prop) by open-grammar synthesis. Productions, as weighted proposals:

   - a LOCAL variable of the goal's type (`assumptiono`) — cheap;
   - an optional leaf `:gen` generator `(g → goal)` (literals, refinement
     domains, constructors) — the datalog/refinement tier plugs in here;
   - a LIBRARY-HEADED application: for each `[weight const-name]` candidate,
     `applyo` it and recursively `expro` the unsolved EXPLICIT obligations at
     depth-1. Library-headed ONLY — we never synthesize the function head,
     which would need higher-order unification beyond Miller patterns.

   `candidates` is either a static seq of [weight const-name] OR a PROVIDER
   function `(state, goal-mvar) → [[weight name] …]` — resolved per sub-goal, so
   each obligation gets candidates for ITS OWN type (fully type-directed when
   backed by the datalog recall, ansatz.datalog/dq-provider).

   `depth` bounds application nesting (drive termination with `expro-deepen`).
   Instance-implicit args are handled by `applyo` (tagged, left to unification /
   instance synthesis), not enumerated."
  [g candidates depth & {:keys [gen]}]
  (inhabito
   g
   (fn [s g]
     (let [cands (if (fn? candidates) (candidates s g) candidates)]
       {:leaves (cond-> [[8 (assumptiono g)]] gen (conj [4 (gen g)]))
        :refiners (for [[w nm] cands] [w (fn [g k] (applyo g nm k))])}))
   depth))

(defn expro-deepen
  "Iterative deepening over `expro`: search depth 1, then 2, … up to `max-depth`,
   concatenating answer streams shallow-first (shallow = simpler = higher prior).
   `g` must be freshly unsolved in `s0` at each depth, so we re-run from `s0`."
  [s0 g candidates max-depth & {:keys [gen]}]
  (fn [_]
    (reduce (fn [$ d]
              (mplus $ (fn [] ((expro g candidates d :gen gen) s0))))
            mzero
            (range 1 (inc max-depth)))))

;; ============================================================
;; bestfirst — a priority-queue frontier over PARTIAL proof states, ordered by
;; the provenance measure. The operational (search) view of the same semiring
;; ProbLog evaluates declaratively; the Aesop-style best-first over an AND-OR
;; hypergraph. Fixes the fair-interleave breadth explosion: instead of exploring
;; N candidates × depth uniformly, expand the most-promising partial proof first
;; and stop at the first complete one.
;; ============================================================

(defn- fold-prior
  "Fold branch weight `w` (of `total`) into `s`'s measure via the semiring ⊗."
  [s w total]
  (let [P (:prov s)]
    (update s :tag #(prov/prov-times P % (prov/prov-from-prob P (/ (double w) (double total)))))))

(defn- expand-node
  "Expand open goal `g` (depth `d`) in state `s` → seq of {:state :open}. The
   move weight folds into each child's measure (so the frontier orders by the
   provenance-⊗ product along the path). Assigned goals collapse; Π-goals
   delegate to `inhabito` (intro+recurse); atomic goals expand via the
   leaves/refiners move set, refiners capturing their obligations as new OPEN
   goals rather than recursing. `branch-cap` bounds children per move."
  [s g d moves branch-cap]
  (cond
    (assigned? s g) [{:state s :open []}]
    (e/forall? (mvar-type s g))
    (for [cs (stream-take branch-cap ((inhabito g moves d) s))]
      {:state cs :open []})
    :else
    (let [{:keys [leaves refiners]} (moves s g)
          refiners (when (pos? d) refiners)
          total (max 1.0 (double (+ (reduce + (map first leaves))
                                    (reduce + (map first refiners)))))]
      (concat
       (for [[w lg] leaves
             cs (stream-take branch-cap (lg s))]
         {:state (fold-prior cs w total) :open []})
       (for [[w rf] refiners
             :let [cap (fn [obs] (fn [st] (unit (assoc st ::obs (vec obs)))))]
             cs (stream-take branch-cap ((rf g cap) s))]
         {:state (fold-prior (dissoc cs ::obs) w total)
          :open (mapv (fn [o] [o (dec d)]) (::obs cs))})))))

(defn bestfirst
  "Best-first inhabitation of `g0` from `s0`: a priority-queue frontier over
   PARTIAL proof states, popped in DESCENDING provenance measure (`order-weight`)
   — expand the most-promising partial proof first, stop at complete ones.
   `moves` is the same move-set inhabito/proveo/expro use. Returns solved states,
   best-first. `max-nodes` bounds expansions; `branch-cap` bounds children per
   move; `limit` bounds returned solutions."
  [g0 moves depth s0 & {:keys [max-nodes branch-cap limit]
                        :or {max-nodes 20000 branch-cap 8 limit 1}}]
  (let [okey (fn [node ctr] [(- (double (order-weight (:state node)))) (long ctr)])
        init {:state s0 :open [[g0 depth]]}]
    (loop [ag (sorted-map (okey init 0) init), ctr 1, n 0, sols []]
      (if (or (empty? ag) (>= n max-nodes) (>= (count sols) limit))
        sols
        (let [[k node] (first ag)
              ag (dissoc ag k)]
          (if (empty? (:open node))
            (recur ag ctr n (conj sols (:state node)))
            (let [[[g d] & rst] (:open node)
                  children (expand-node (:state node) g d moves branch-cap)
                  [ag' ctr'] (reduce (fn [[ag c] child]
                                       (let [nn {:state (:state child)
                                                 :open (into (vec (:open child)) rst)}]
                                         [(assoc ag (okey nn c) nn) (inc c)]))
                                     [ag ctr] children)]
              (recur ag' ctr' (inc n) sols))))))))

;; ============================================================
;; Kernel disposal
;; ============================================================

(defn- telescope
  "mkForallFVars / mkLambdaFVars: wrap `body` (already abstracted over every
   local's fvar) in nested binders, abstracting each binder's TYPE over the
   binders outer to it (dependent). `locals` is outermost-first."
  [mk-binder locals body]
  (let [fids (mapv :fid locals)]
    (reduce (fn [acc i]
              (let [{:keys [name type]} (nth locals i)]
                (mk-binder (or name "h")
                           (e/abstract-many type (subvec fids 0 i))
                           acc :default)))
            body
            (reverse (range (count locals))))))

(defn commit-overlay
  "The state's env already holds every overlay decl as an AXIOM (added by
   `declareo`). Here we UPGRADE any decl whose value has been synthesized to a
   checked DEF (replacing the axiom), and report the rest as `:assumed`. Returns
   [env' assumed]: a proof using overlay lemmas is certified GIVEN them — fully
   if all are synthesized, modulo the listed assumptions otherwise."
  [s]
  (reduce (fn [[env assumed] [nm {:keys [type value]}]]
            (let [ty (zonk s type)
                  val (some->> value (zonk s))
                  synth? (and val (not (meta/has-expr-mvar? val))
                              (not (meta/has-expr-mvar? ty)))]
              (if synth?
                [(env/check-constant-replace
                  env (env/mk-def (name/from-string nm) [] ty val))
                 assumed]
                [env (conj assumed nm)])))
          [(:env s) []]
          (:overlay s)))

(defn certify
  "The kernel disposes: zonk the solution for hole `g`, close it over the
   ambient hypotheses, and STRICT-check it with the TRUSTED Java kernel
   (`env/verifies?` → `TypeChecker.checkConstant`, which re-checks every
   application argument — NOT the lenient `inferType`). Returns {:term …
   :type … :ok? bool}; `:ok?` true means the result is a real, kernel-verified
   proof of the (closed) goal, independent of anything the search did.

   A goal with hypotheses `h : H` in the lctx is disposed as the closed
   judgement `⊢ (λ h:H. term) : (∀ h:H. goal)` — so `certify` is sound in an
   open context, not only for closed goals."
  [s g]
  (let [mctx (:mctx s)
        term0 (zonk s g)
        gty0 (mvar-type s g)
        lctx (meta/instantiate-lctx-mvars mctx (:lctx s))
        locals (->> lctx
                    (filter (fn [[_ d]] (= :local (:tag d))))
                    (sort-by first)
                    (mapv (fn [[fid d]] {:fid fid :name (:name d) :type (:type d)})))
        fids (mapv :fid locals)
        proof (telescope e/lam locals (e/abstract-many term0 fids))
        goal (telescope e/forall' locals (e/abstract-many gty0 fids))]
    (if (or (meta/has-expr-mvar? proof) (meta/has-expr-mvar? goal))
      {:term term0 :type gty0 :ok? false :reason :open-holes}
      ;; commit the relational env-overlay into a forked env first, so a proof
      ;; using synthesized/assumed lemmas checks against them.
      (let [[env assumed] (commit-overlay s)]
        {:term term0 :type gty0 :closed-goal goal :closed-proof proof
         :assumed assumed  ; overlay lemmas admitted as axioms (nil/[] = fully proved)
         ;; STRICT kernel check of `proof : goal` for ANY goal (Prop OR Type) —
         ;; a DEF `__certify__ : goal := proof`, checkConstant re-checking every
         ;; argument. (A THM/`verifies?` would reject a value hole whose type is
         ;; not a Prop, e.g. ?x : Nat.)
         :ok? (boolean
               (try (env/check-constant
                     env
                     (env/mk-def (name/from-string "__certify__") [] goal proof))
                    true
                    (catch Throwable _ false)))}))))

(defn- open-telescope
  "Peel `ty`'s ∀-telescope into fresh fvars added to `lctx` (binders →
   hypotheses). Returns [lctx' conclusion fvar-ids], fvar ids from `start-fid`."
  [lctx ty start-fid]
  (loop [t ty, lctx lctx, fids [], fid start-fid]
    (if (e/forall? t)
      (recur (e/instantiate1 (e/forall-body t) (e/fvar fid))
             (assoc lctx fid {:tag :local :id fid
                              :name (or (some-> (e/forall-name t) str) "x")
                              :type (e/forall-type t)})
             (conj fids fid) (inc fid))
      [lctx t fids])))

(defn synthesizeo
  "Synthesize the VALUE of overlay declaration `name` BY INHABITING its type:
   fresh a goal of the overlay type and prove it via `prove` — a preset like
   `#(proveo % …)` or `#(expro % …)`; `inhabito`'s Π-introduction opens the
   telescope, so `prove` receives the WHOLE Π-typed goal. Set the overlay value
   to the proof. Threads the same metacontext + overlay, so the proof may itself
   use env AND other overlay lemmas (mutual/staged synthesis). Turns a declared
   lemma-hole into a search-proven, kernel-checked def; `k` continues."
  [name prove k]
  (fn [s]
    (let [ty (get-in s [:overlay name :type])]
      ((fresh ty
              (fn [g]
                (all (prove g)
                     (fn [s2] ((k) (set-overlay-value s2 name (zonk s2 g)))))))
       s))))
