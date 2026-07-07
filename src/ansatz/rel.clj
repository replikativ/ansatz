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
            [ansatz.kernel.tc :as tc]))

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
   :next-id fresh id counter (pure value — forking a state is safe)"
  [env & {:keys [lctx mctx prov tag next-id]}]
  (let [prov (or prov prov/default-provenance)]
    {:env env
     :lctx (or lctx {})
     :mctx (or mctx meta/empty-context)
     :prov prov
     :tag (or tag (prov/prov-one prov))
     :next-id (or next-id id-base)}))

(defn measure
  "The reported measure of a state's branch (prov-recover of its tag)."
  [s]
  (prov/prov-recover (:prov s) (:tag s)))

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

(defn with-lemma
  "Instantiate constant `cname`'s universe params with fresh level mvars;
   f : [lemma-expr lemma-type] → goal."
  [cname f]
  (fn [s]
    (if-let [ci (const-info s cname)]
      (let [lparams (vec (.levelParams ci))
            [s lvls] (reduce (fn [[s acc] _]
                               (let [[id s] (next-id! s)]
                                 [(update s :mctx meta/add-level-mvar-decl id)
                                  (conj acc (lvl/mvar id))]))
                             [s []] lparams)
            nm (.name ci)
            ty (e/instantiate-level-params (.type ci) (zipmap lparams lvls))]
        ((f [(e/const' nm lvls) ty]) s))
      mzero)))

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

(defn applyo
  "Relational `apply`: refine goal-hole `g` with lemma `cname`.
   Peels the lemma's ∀-telescope into fresh mvars, unifies its conclusion
   with g's type, assigns g := (lemma ?a₁ … ?aₙ), then calls
   k : [unsolved-EXPLICIT-arg-mvars] → goal for the remaining obligations.
   Instance-implicit args are excluded from k (left for unification /
   instance synthesis); implicit args are typically pinned by the
   conclusion unification."
  [g cname k]
  (with-lemma cname
    (fn [[lemma ty]]
      (fn [s]
        (let [[s args concl] (peel-telescope s ty)
              gty (mvar-type s g)]
          ((all (=== concl gty)
                (=== g (reduce e/app lemma (map :mvar args)))
                (project*
                 (fn [s]
                   (k (->> args
                           (filter :explicit?)
                           (map :mvar)
                           (remove #(assigned? s %))
                           vec)))))
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

(defn proveo
  "Depth-bounded relational prover: close goal-hole `g` using assumptions
   and the lemma set, recursing on obligations. Branch priors: assumption
   is cheap/likely, each lemma application costs its prior.
   `lemmas` is a seq of [weight name].
   opts:
   - :hyp-arities — also try APPLYING each local hypothesis to this many
     fresh argument holes (e.g. [1 2]); with a hole-typed hypothesis this
     infers implications. Default [] (off)."
  ([g lemmas depth] (proveo g lemmas depth {}))
  ([g lemmas depth {:keys [hyp-arities] :or {hyp-arities []} :as opts}]
   (fn [s]
     (cond
       (assigned? s g) (unit s)
       (not (pos? depth)) mzero
       :else
       ((apply condw
               (concat
                [[8 (assumptiono g)]]
                (for [[w cname] lemmas]
                  [w (applyo g cname
                             (fn [obs]
                               (apply all
                                      (map #(proveo % lemmas (dec depth) opts)
                                           obs))))])
                (for [[fid decl] (:lctx s)
                      :when (= :local (:tag decl))
                      arity hyp-arities]
                  [(/ 1.0 (double arity))
                   (apply-hypo g fid arity
                               (fn [obs]
                                 (apply all
                                        (map #(proveo % lemmas (dec depth) opts)
                                             obs))))])))
        s)))))

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

   `depth` bounds application nesting (drive termination with `expro-deepen`).
   Instance-implicit args are handled by `applyo` (tagged, left to unification /
   instance synthesis), not enumerated."
  [g candidates depth & {:keys [gen]}]
  (fn [s]
    (cond
      (assigned? s g) (unit s)
      ;; at the depth bound, only LEAVES: a local variable or a generator
      ;; production (no further applications).
      (not (pos? depth)) ((apply any (assumptiono g) (when gen [(gen g)])) s)
      :else
      ((apply condw
              (concat
               [[8 (assumptiono g)]]
               (when gen [[4 (gen g)]])
               (for [[w cname] candidates]
                 [w (applyo g cname
                            (fn [obs]
                              (apply all
                                     (map #(expro % candidates (dec depth) :gen gen)
                                          obs))))])))
       s))))

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
      {:term term0 :type gty0 :closed-goal goal :closed-proof proof
       ;; STRICT kernel check of `proof : goal` for ANY goal (Prop OR Type) —
       ;; a DEF `__certify__ : goal := proof`, checkConstant re-checking every
       ;; argument. (A THM/`verifies?` would reject a value hole whose type is
       ;; not a Prop, e.g. ?x : Nat.)
       :ok? (boolean
             (try (env/check-constant
                   (:env s)
                   (env/mk-def (name/from-string "__certify__") [] goal proof))
                  true
                  (catch Throwable _ false)))})))
