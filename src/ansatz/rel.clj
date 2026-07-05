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

   Measure semantics: every state carries a log-weight `:logw`. `condw`
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
   :logw    log-weight of this branch (measure)
   :next-id fresh id counter (pure value — forking a state is safe)"
  [env & {:keys [lctx mctx logw next-id]}]
  {:env env
   :lctx (or lctx {})
   :mctx (or mctx meta/empty-context)
   :logw (or logw 0.0)
   :next-id (or next-id id-base)})

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
   branch PRIOR: it multiplies the branch measure (logw += log(w/Σw)) and
   biases the search order (heavier branches are explored first). This is
   Barliman's conde-weighted unified with probKanren's weighted semantics."
  [& clauses]
  (let [total (double (reduce + (map first clauses)))]
    (fn [s]
      (->> clauses
           (sort-by (comp - first))
           (map (fn [[w & goals]]
                  (let [s' (update s :logw + (Math/log (/ (double w) total)))]
                    (fn [] ((apply all goals) s')))))
           (reduce mplus mzero)))))

(defn weightedo
  "Multiply the current branch measure by `w` (add log w)."
  [w]
  (fn [s] (unit (update s :logw + (Math/log (double w))))))

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
     (if raw? states (sort-by (comp - :logw) states)))))

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
  "forallMetaTelescope: peel ∀-binders into fresh mvars.
   Returns [s' arg-mvars conclusion]."
  [s ty]
  (loop [s s, t ty, args []]
    (if (e/forall? t)
      (let [[id s] (next-id! s)
            s (update s :mctx meta/add-expr-mvar-decl id (e/forall-type t) (:lctx s))]
        (recur s
               (e/instantiate1 (e/forall-body t) (e/mvar id))
               (conj args (e/mvar id))))
      [s args t])))

(defn applyo
  "Relational `apply`: refine goal-hole `g` with lemma `cname`.
   Peels the lemma's ∀-telescope into fresh mvars, unifies its conclusion
   with g's type, assigns g := (lemma ?a₁ … ?aₙ), then calls
   k : [unsolved-arg-mvars] → goal for the remaining obligations."
  [g cname k]
  (with-lemma cname
    (fn [[lemma ty]]
      (fn [s]
        (let [[s args concl] (peel-telescope s ty)
              gty (mvar-type s g)]
          ((all (=== concl gty)
                (=== g (reduce e/app lemma args))
                (project*
                 (fn [s]
                   (k (vec (remove #(assigned? s %) args))))))
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

(defn exacto
  "Relational `exact`: g := term, with the type equation checked relationally
   (term may contain holes; so may g's type)."
  [g term]
  (fn [s]
    (let [gty (mvar-type s g)
          tty (try (meta/infer-type (:mctx s) (tc-st s) term)
                   (catch Exception _ nil))]
      (when tty
        ((all (=== tty gty) (=== g term)) s)))))

(defn proveo
  "Depth-bounded relational prover: close goal-hole `g` using assumptions
   and the lemma set, recursing on obligations. Branch priors: assumption
   is cheap/likely, each lemma application costs its prior.
   `lemmas` is a seq of [weight name]."
  [g lemmas depth]
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
                                     (map #(proveo % lemmas (dec depth))
                                          obs))))])))
       s))))

;; ============================================================
;; Kernel disposal
;; ============================================================

(defn certify
  "The kernel disposes: zonk the solution for hole `g`, require it closed,
   and STRICT-check it with the trusted kernel against the (zonked) goal
   type. Returns {:term … :type … :ok? bool} — :ok? true means the search
   result is a real proof, independent of anything the search did."
  [s g]
  (let [term (zonk s g)
        gty (mvar-type s g)
        ;; hypotheses may have had holes for types — zonk the lctx too
        s (update s :lctx #(meta/instantiate-lctx-mvars (:mctx s) %))]
    (if (or (meta/has-expr-mvar? term) (meta/has-expr-mvar? gty))
      {:term term :type gty :ok? false :reason :open-holes}
      (let [st (tc-st s)]
        (try
          (let [tty (tc/infer-type st term)]
            {:term term :type gty
             :ok? (boolean (tc/is-def-eq st tty gty))
             :inferred tty})
          (catch Exception ex
            {:term term :type gty :ok? false :reason (.getMessage ex)}))))))
