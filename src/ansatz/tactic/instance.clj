;; Follows Lean 4 (../lean4), Meta/Instances.lean:instanceExtension/addInstance and
;; Meta/SynthInstance.lean:getInstances. Candidates come only from registered instances.

(ns ansatz.tactic.instance
  "Typeclass instance resolution following Lean 4's synthesis algorithm.

   Resolution uses structural matching with isDefEq fallback,
   recursive synthesis for inst-implicit args, and depth limiting."
  (:require [ansatz.bundle :as bundle]
            [clojure.string :as str]
            [clojure.java.io :as io]
            [ansatz.meta :as meta]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.tc :as tc]
            [ansatz.config :as config])
  (:import [ansatz.kernel ConstantInfo Env]))

;; ============================================================
;; Instance index: class-name → [candidates]
;; ============================================================

(defn- return-type-head
  "Strip foralls from a type to get the return type, then return its head constant name."
  [ty]
  (loop [t ty arity 0]
    (if (e/forall? t)
      (recur (e/forall-body t) (inc arity))
      (let [[head _] (e/get-app-fn-args t)]
        (when (e/const? head)
          [(e/const-name head) arity])))))

(defn add-instance
  "Lean's `addInstance`: a NEW env whose instance table (the `:instances` extension) also
   holds the constant `inst-name`, keyed by the class its type concludes in, at `priority`
   (Lean's default 1000). Among equal priorities the newest registration is tried FIRST, as
   in Lean's DiscrTree insertion order; a higher priority still goes ahead of it. An env with
   no registry starts with the empty table, as Lean's instanceExtension does."
  [^Env env inst-name & {:keys [priority] :or {priority 1000}}]
  (let [ci (or (env/lookup env inst-name)
               (throw (ex-info "add-instance: no such constant" {:name (name/->string inst-name)})))
        [cls _] (or (return-type-head (.type ci))
                    (throw (ex-info "add-instance: the type does not conclude in a class"
                                    {:name (name/->string inst-name)})))
        idx (or (env/get-extension env :instances nil) {})
        entry {:name inst-name :priority priority}
        same? (fn [v] (= (:name v) inst-name))]
    (env/with-extension env :instances
      (update idx cls (fn [vs]
                        (->> (remove same? vs)
                             (cons entry)
                             (sort-by (fn [v] (- (or (:priority v) 1000))))
                             vec))))))

(defn get-instances
  "Get candidate instances for a class name from the index."
  [index class-name]
  (get index class-name []))

(defn parse-instance-tsv
  "Lean's @[instance] registry (scripts/dump_instances.lean: `class<TAB>instance<TAB>priority`
   lines) → an instance index {class-Name → [{:name Name :priority Nat} …]}. Within a class the
   candidates are in Lean's try order: HIGHER priority first (`instance (priority := low)` is
   tried last), the most recently declared first among equals. `present?` (name-string → bool) drops instances the
   env does not have, so a registry dumped from full Init serves a smaller bundled tier."
  ([lines] (parse-instance-tsv lines nil))
  ([lines present?]
   (let [seen (java.util.HashSet.)
         idx (reduce (fn [idx line]
                       (let [parts (str/split line #"\t")]
                         (if (and (>= (count parts) 2)
                                  (or (nil? present?) (present? (nth parts 1)))
                                  ;; an instance re-registered by a re-exporting module is one
                                  ;; instance: keep its first (earliest) registration
                                  (.add seen [(nth parts 0) (nth parts 1)]))
                           (update idx (name/from-string (nth parts 0)) (fnil conj [])
                                   {:name (name/from-string (nth parts 1))
                                    :priority (if (>= (count parts) 3)
                                                (Long/parseLong (nth parts 2))
                                                1000)})
                           idx)))
                     {} lines)]
     ;; Lean (SynthInstance.lean): candidates sorted by priority and consumed from the END —
     ;; highest priority first, and among equals the LAST registered (DiscrTree insertion order
     ;; = declaration order), so a carrier's own `Real.instMul` beats the generic
     ;; `CommMagma.toMul` projection declared before it. A stable sort over the reversed list.
     (into {} (map (fn [[k vs]] [k (vec (sort-by (comp - :priority) (rseq vs)))])) idx))))

(defn load-instance-tsv
  "Load Lean's instance registry from a TSV file (see parse-instance-tsv)."
  [path]
  (with-open [rdr (io/reader path)]
    (parse-instance-tsv (doall (line-seq rdr)))))

(def ^:private bundled-instances-resource "ansatz/init-instances.tsv.gz")

(defn load-bundled-instances
  "The instance index of the BUNDLED Init registry (resources/ansatz/init-instances.tsv.gz, dumped
   by scripts/regen-bundled-attrs.sh), intersected with the env through `present?` — the zero-config
   `load-init!` tier's counterpart of the store's derived `:instances` blob. Missing or inconsistent resources fail
   before installation."
  [{:keys [present?]}]
  (let [payload (bundle/verified-bytes bundled-instances-resource)]
    (let [lines (with-open [in (java.util.zip.GZIPInputStream. (java.io.ByteArrayInputStream. payload))]
                  (str/split-lines (slurp in)))]
      (parse-instance-tsv lines present?))))

(defn index-for
  "The environment's registered instances (Lean Meta/Instances.lean:getGlobalInstancesIndex).
   An empty registry is valid; a missing registry is an environment setup error."
  [env]
  (or (env/get-extension env :instances nil)
      (throw (ex-info "Tactic error: no instance registry"
                      {:kind :tactic-error}))))

;; ── Candidate selection — Lean's DiscrTree key, one level deep ─────────────────────────────
;; Lean's `getInstances` looks candidates up in a discrimination tree keyed by the instance
;; type's conclusion, so `OfNat ℝ 1` only ever sees the generic instances (conclusion `OfNat ?α n`)
;; and the ℝ-specific ones. A flat per-class list is not a substitute once it is CAPPED at
;; `*max-candidates*`: Mathlib registers 61 `OfNat` and 115 `Pow` instances, `One.toOfNat1` is
;; number 58 of the former and `Monoid.toNatPow` number 38 of the latter, and both sat forever
;; behind the cap. Keying each candidate by the head of its conclusion's FIRST argument (a bound
;; variable → generic) recovers the relevant subset.

(def ^:private conclusion-keys
  "instance Name → its conclusion key (a head-constant Name, or :generic). Filled on demand: only
   the classes a session actually synthesizes pay for resolving their instances' types."
  (atom {}))

(defn reset-caches!
  "Forget the per-name conclusion keys — a new env may spell the same names differently."
  []
  (reset! conclusion-keys {}))

(defn capture-caches
  "Capture immutable instance-selection cache values for a proof session."
  []
  @conclusion-keys)

(defn validate-caches! [snapshot]
  (when-not (map? snapshot)
    (throw (ex-info "Invalid instance cache snapshot" {})))
  snapshot)

(defn restore-caches! [snapshot]
  (reset! conclusion-keys (validate-caches! snapshot)))

(defn- strip
  "`x` without its mdata wrappers — definitionally transparent, and a matcher must not see it."
  [x] (if (e/mdata? x) (recur (e/mdata-expr x)) x))

(defn- head-key
  "The head constant of `x`, or :generic when it has none (a bound variable, a literal, …)."
  [x]
  (let [x (loop [x x] (if (and x (e/mdata? x)) (recur (e/mdata-expr x)) x))
        [h _] (when x (e/get-app-fn-args x))]
    (if (and h (e/const? h)) (e/const-name h) :generic)))

(defn- conclusion-first-arg-key
  "The DiscrTree-style key path of an instance type: the head constant of its conclusion's
   first argument, and — when that argument is itself an application — the head of ITS first
   argument. Two levels, because one is too coarse for the classes that take a proposition:
   every `Decidable (a ≤ b)` instance keys as `LE.le` at one level, so `Nat.decLe` sat among
   80 equals (`Real.decidableLE`, `Prod.instDecidableLE`, the whole of `Std.Time`…) and fell
   behind the candidate cap — `norm_num` could not decide `(2 : Nat) ≤ 3`. With the carrier as
   the second level, `Decidable (LE.le Nat …)` sees the Nat instances and the generic ones.
   :generic at a level means the instance applies to anything there."
  [ty]
  (let [concl (loop [t ty] (if (e/forall? t) (recur (e/forall-body t)) t))
        [_ args] (e/get-app-fn-args concl)
        a (first args)
        a (loop [x a] (if (and x (e/mdata? x)) (recur (e/mdata-expr x)) x))
        [_ aargs] (when a (e/get-app-fn-args a))]
    [(head-key a) (if (seq aargs) (head-key (first aargs)) :generic)]))

(defn- conclusion-key
  "Cached per instance NAME — and only when the instance is in `env`; an instance the env
   does not have is `:absent`, never a candidate. A miss is not cached: the cache outlives an
   env (tests switch envs; a session can too), and a name absent from one env and present in
   the next would otherwise stay \"generic\" forever — which is how `Nat.decLt` came to be
   offered, and accepted, for `Decidable (0 = 0)`. Lean's registry only ever names constants
   of its environment; ours can be wider (a registry dumped from Mathlib attached to a small
   env), and the 246 absent `Decidable` entries ahead of `instDecidableNot` pushed it past
   `*max-candidates*` when they counted as generic matches."
  [^Env env inst-name]
  (or (get @conclusion-keys inst-name)
      (if-let [^ConstantInfo ci (env/lookup env inst-name)]
        (let [k (conclusion-first-arg-key (.type ci))]
          (swap! conclusion-keys assoc inst-name k)
          k)
        :absent)))

(defn- key-matches?
  "Does the candidate's key path fit the goal's? A level is compatible when the keys agree or
   either side is generic there — Lean's DiscrTree, where a star matches anything."
  [ck gk]
  (every? true? (map (fn [c g] (or (= c g) (= c :generic) (= g :generic))) ck gk)))

(defn select-candidates
  "The candidates of `candidates` (a class's registry entries, in order) worth trying for
   `goal-type`, in order: the instances whose conclusion key matches the goal's first argument,
   then the generic ones at equal priority; higher priority always goes first.
   This approximates Lean's DiscrTree selection with a two-head key.

   The ORDER is load-bearing, not just the filtering. `getUnify` returns a class's star (generic)
   matches before its keyed ones and `SynthInstance.generate` consumes that array BACKWARDS
   (SynthInstance.lean:597, after a stable ascending sort by priority), so among instances of
   equal priority Lean tries the carrier-specific ones FIRST. Registry order alone put the
   generic parent projections first: `Add Int` resolved to `Distrib.toAdd Int Int.instDistrib`
   instead of `Int.instAdd`, a term defeq to Lean's but syntactically unlike it, so Mathlib's
   `Int` lemmas and omega's preprocessing — which are stated in Lean's spelling — matched
   nothing. Parent projections carry the default priority in Lean too (Structure.lean:1516),
   so specificity is the only thing that separates them."
  [env candidates goal-type]
  (let [gkey (let [[_ gargs] (e/get-app-fn-args goal-type)
                   g (first gargs)
                   g (loop [x g] (if (and x (e/mdata? x)) (recur (e/mdata-expr x)) x))
                   [_ gaargs] (when g (e/get-app-fn-args g))]
               [(head-key g) (if (seq gaargs) (head-key (first gaargs)) :generic)])]
    (if (= gkey [:generic :generic])
      (sort-by #(- (or (:priority %) 1000))
               (remove #(= :absent (conclusion-key env (:name %))) candidates))
      (let [scored (group-by (fn [c]
                               (let [ck (conclusion-key env (:name c))]
                                 (cond (= ck :absent) :no
                                       (= ck gkey) :exact
                                       (key-matches? ck gkey) :compatible
                                       :else :no)))
                             candidates)
            picked (into (vec (:exact scored)) (:compatible scored))]
        (sort-by #(- (or (:priority %) 1000))
                 (if (empty? picked)
                   (remove #(= :absent (conclusion-key env (:name %))) candidates)
                   picked))))))

;; ============================================================
;; Structural matching (avoids proof irrelevance)
;; ============================================================

(defn- structural-match
  "First-order structural match: pattern vs target.
   fvar-ids is a set of fvar IDs treated as unification variables.
   Returns a substitution map {fvar-id → Expr} or nil on failure.

   Unlike is-def-eq, this does NOT unfold definitions or use proof irrelevance."
  [pattern target fvar-ids]
  (let [subst (atom {})
        ok (atom true)]
    (letfn [(strip [x] (if (e/mdata? x) (recur (e/mdata-expr x)) x))
            (go [p0 t0]
                ;; mdata is definitionally transparent — the kernel ignores it, and so must a
                ;; matcher. Store-imported instance types carry it (the Mathlib export
                ;; preserves mdata so imported declarations stay close to Lean's trace space)
                ;; while an elaborated goal does not, so `Decidable (LE.le (mdata Nat) …)` vs
                ;; `Decidable (LE.le Nat …)` failed on the tag comparison alone: every
                ;; `Decidable` synthesis over Mathlib missed, which is what left `norm_num`
                ;; with "no instance found" on goals as simple as `(2 : Nat) ≤ 3`.
                (let [p (strip p0) t (strip t0)]
                  (when @ok
                    (cond
                  ;; Pattern is a unification variable
                      (and (e/fvar? p) (contains? fvar-ids (e/fvar-id p)))
                      (let [id (e/fvar-id p)]
                        (if-let [existing (get @subst id)]
                          (when-not (= existing t)
                            (reset! ok false))
                          (swap! subst assoc id t)))

                  ;; Both same tag — recurse structurally
                      (= (e/tag p) (e/tag t))
                      (case (e/tag p)
                        :bvar (when-not (= (e/bvar-idx p) (e/bvar-idx t))
                                (reset! ok false))
                        :sort (when-not (lvl/level= (e/sort-level p) (e/sort-level t))
                                (reset! ok false))
                        :const (do (when-not (= (e/const-name p) (e/const-name t))
                                     (reset! ok false))
                                   (when @ok
                                     (let [pl (e/const-levels p)
                                           tl (e/const-levels t)]
                                       (when-not (and (= (count pl) (count tl))
                                                      (every? true? (map lvl/level= pl tl)))
                                         (reset! ok false)))))
                        :app (do (go (e/app-fn p) (e/app-fn t))
                                 (go (e/app-arg p) (e/app-arg t)))
                        :lam (do (go (e/lam-type p) (e/lam-type t))
                                 (go (e/lam-body p) (e/lam-body t)))
                        :forall (do (go (e/forall-type p) (e/forall-type t))
                                    (go (e/forall-body p) (e/forall-body t)))
                        :fvar (when-not (= (e/fvar-id p) (e/fvar-id t))
                                (reset! ok false))
                        :proj (do (when-not (and (= (e/proj-type-name p) (e/proj-type-name t))
                                                 (= (e/proj-idx p) (e/proj-idx t)))
                                    (reset! ok false))
                                  (go (e/proj-struct p) (e/proj-struct t)))
                        (:lit-nat :lit-str) (when-not (= p t) (reset! ok false))
                        (reset! ok false))

                      :else (reset! ok false)))))]
      (go pattern target))
    (when @ok @subst)))

;; ============================================================
;; Synthesis engine
;; ============================================================

(defn- whnf [st expr]
  (#'tc/cached-whnf st expr))

(declare synthesize* synthesize-uncached*)

(defn- rigid-fvar-mismatch?
  "A candidate result-arg with a CONST head can never be defeq to a goal arg
   whose head is a (rigid, :local) fvar: closed registry terms cannot reduce
   to a stuck fvar application. Cheap sound pre-filter before defeq/recursive
   synthesis — kills e.g. every concrete `MetricSpace ℝ`-style leaf against an
   `fvar-applied` subject like `m β` without a kernel call (E0 cliff)."
  [r g]
  (let [[rh _] (e/get-app-fn-args r)
        [gh _] (e/get-app-fn-args g)]
    (and (e/const? rh) (e/fvar? gh))))

(defn- candidate-application
  "Check domains and the complete instantiated result before building a candidate term.
   Lean Meta/SynthInstance.lean:getSubgoals/tryResolve uses typed metavariables and
   full-result unification; an incompatible candidate is a mismatch, not an inference error."
  [st candidate-type goal-type candidate-term args]
  (loop [ty candidate-type remaining (seq args)]
    (if remaining
      (let [ty (whnf st ty)
            arg (first remaining)]
        (when (and (e/forall? ty)
                   (tc/is-def-eq st (tc/infer-type st arg) (e/forall-type ty)))
          (recur (e/instantiate1 (e/forall-body ty) arg) (next remaining))))
      (when (tc/is-def-eq st ty goal-type)
        (reduce e/app candidate-term args)))))

(defn- try-candidate
  "Try a single candidate instance against a goal type.
   Returns the fully-applied instance term, or nil on mismatch; unexpected errors propagate.
   Lean Meta/SynthInstance.lean:tryResolve represents mismatch with none, not an exception."
  [st env index candidate goal-type depth]
  (let [^ConstantInfo ci (env/lookup! env (:name candidate))
        ctype (.type ci)
        level-params (vec (.levelParams ci))
          ;; Infer level assignments from the goal
        goal-head-levels (let [[h _] (e/get-app-fn-args goal-type)]
                           (when (e/const? h) (e/const-levels h)))
        level-subst (if (and (seq level-params) (seq goal-head-levels))
                      (into {} (map vector level-params
                                    (take (count level-params)
                                          (concat goal-head-levels (repeat lvl/zero)))))
                      (into {} (map (fn [p] [p lvl/zero]) level-params)))
        ctype (if (seq level-subst)
                (e/instantiate-level-params ctype level-subst)
                ctype)
        inst-levels (mapv (fn [p] (get level-subst p lvl/zero)) level-params)
          ;; Peel foralls, creating fvars as pattern variables
        fvar-ids (atom #{})
        arg-info (atom [])
          ;; Peel foralls, WHNF at each step to handle type aliases
          ;; (e.g., DecidableEq Nat → ∀ a b, Decidable (Eq Nat a b))
          ;; …but stop at the instance's DECLARED conclusion when it already has the goal's
          ;; class head: `instDecidableEqFin : (n : Nat) → DecidableEq (Fin n)` for the goal
          ;; `DecidableEq (Fin 3)` must match at `DecidableEq (Fin ?n)`. Unfolding the alias to
          ;; `∀ a b, Decidable (a = b)` peels two binders the goal does not have, so nothing
          ;; matches (a zero-arity instance like `instDecidableEqBool` only got through the
          ;; name-based fallback).
        goal-head (let [[h _] (e/get-app-fn-args goal-type)] (when (e/const? h) (e/const-name h)))
        result-type (loop [t ctype]
                      (let [[th _] (e/get-app-fn-args t)
                            tw (if (and goal-head (not (e/forall? t)) (e/const? th)
                                        (= (e/const-name th) goal-head))
                                 t
                                 (or (whnf st t) t))]
                        (if (e/forall? tw)
                          (let [fv-id (swap! (:next-id st) inc)
                                fv (e/fvar fv-id)
                                info (e/forall-info tw)
                                arg-type (e/forall-type tw)]
                            (swap! fvar-ids conj fv-id)
                            (swap! arg-info conj {:fvar-id fv-id :fvar fv
                                                  :type arg-type :info info})
                            (recur (e/instantiate1 (e/forall-body tw) fv)))
                          tw)))]
      ;; Propose substitutions from the result type. Prefix/positional matches are
      ;; provisional: candidate-application checks domains and the full result.
    (let [result-type-w (or (whnf st result-type) result-type)
          goal-type-w (or (whnf st goal-type) goal-type)
            ;; Extract head + args from both sides
          [rh ra] (e/get-app-fn-args result-type-w)
          [gh ga] (e/get-app-fn-args goal-type-w)]
      (when-let [subst (or (structural-match result-type goal-type @fvar-ids)
                           (when (not= result-type result-type-w)
                             (structural-match result-type-w goal-type-w @fvar-ids))
                            ;; A matching prefix can propose substitutions, but cannot
                            ;; bypass the final complete-result check.
                           (when (and (e/const? rh) (e/const? gh)
                                      (tc/is-def-eq st rh gh)
                                      (>= (count ra) (count ga)))
                             (let [s (atom {}) ok (atom true)]
                                ;; Match only the first (count ga) args
                               (doseq [[r g] (map vector (take (count ga) ra) ga)]
                                 (when @ok
                                   (if (and (e/fvar? r) (contains? @fvar-ids (e/fvar-id r)))
                                     (swap! s assoc (e/fvar-id r) g)
                                     (when-not (and (not (rigid-fvar-mismatch? r g))
                                                    (tc/is-def-eq st r g))
                                       (reset! ok false)))))
                               (when @ok @s)))
                            ;; LENIENT positional match — DERIVED instances. Same head +
                            ;; arity; fill ONLY the pattern-fvar positions and SKIP the
                            ;; rest. A derived instance's result args are PROJECTIONS
                            ;; (`AddCommMonoid.toAdd α ?fv`) that are not structurally
                            ;; equal to the goal's DIRECT instances (`instAddNat`) but ARE
                            ;; defeq once ?fv is synthesized. So we don't require those
                            ;; positions to match here — the instance fvars get filled by
                            ;; recursive synthesis and the final is-def-eq below GATES
                            ;; soundness. (Only fires when the earlier, stricter matches
                            ;; failed, so ordinary instances are unaffected.)
                           (when (and (e/const? rh) (e/const? gh)
                                      (tc/is-def-eq st rh gh)
                                      (= (count ra) (count ga)))
                             (let [s (atom {}) ok (atom true)]
                               (doseq [[r g] (map vector ra ga)]
                                 (if (and (e/fvar? r) (contains? @fvar-ids (e/fvar-id r)))
                                   (swap! s assoc (e/fvar-id r) g)
                                     ;; skipped positions are gated by the final
                                     ;; is-def-eq — but a rigid const-vs-fvar head
                                     ;; mismatch can never pass it, and neither can two
                                     ;; DIFFERENT constant heads (`LT.lt …` against
                                     ;; `Eq …`): Lean's DiscrTree never offers such a
                                     ;; candidate, and this path once accepted `Nat.decLt`
                                     ;; for `Decidable (0 = 0)`. Fail fast.
                                   (let [[rh' _] (e/get-app-fn-args (strip r))
                                         [gh' _] (e/get-app-fn-args (strip g))]
                                     (when (or (rigid-fvar-mismatch? r g)
                                               (and (e/const? rh') (e/const? gh')
                                                    (not= (e/const-name rh') (e/const-name gh'))))
                                       (reset! ok false)))))
                               (when (and @ok (seq @s)) @s))))]
        ;; Try to fill all arguments
        (let [;; A structure-`extends` parent projection (e.g. `LawfulBEq.toReflBEq`). Lean auto-
                ;; registers these as instances whose structure argument is an instance subgoal,
                ;; even though as a plain function that argument is EXPLICIT. We mirror that ONLY for
                ;; projection-named candidates, so ordinary instances with genuine explicit args are
                ;; untouched (Lean gates on class metadata; this name gate is the faithful proxy).
              proj-candidate? (let [s (name/->string (:name candidate))]
                                (or (.contains s ".to") (.contains s ".toImpl")))
              filled-args
              (reduce
               (fn [acc {:keys [fvar-id fvar type info]}]
                 (when acc
                   (if-let [val (get subst fvar-id)]
                     ;; Solved by structural matching
                     (conj acc val)
                     ;; Not in subst — try other strategies
                     (let [resolved-type (reduce (fn [ty [fid val]]
                                                   (e/instantiate1 (e/abstract1 ty fid) val))
                                                 type subst)]
                       (case info
                         :inst-implicit
                           ;; Instance-implicit: synthesize recursively.
                         (if-let [inst (synthesize* st env index resolved-type (inc depth))]
                           (conj acc inst)
                           nil)

                         (:implicit :strict-implicit)
                           ;; Implicit arg not determined by structural match.
                           ;; This can happen if the arg appears only in other args' types.
                           ;; Try: look at other solved args to determine this one.
                         nil

                           ;; :default — explicit arg. For a structure-`extends` parent projection
                           ;; (`X.toY`), Lean treats the structure argument as an instance subgoal
                           ;; (the projection is registered as an instance `[X …] : Y …`). We mirror
                           ;; that here, gated to projection candidates so ordinary explicit args are
                           ;; not synthesized. `synthesize*` self-gates further (succeeds only for real
                           ;; class goals) and the full term is type-checked against the goal below, so
                           ;; this never loosens soundness.
                         (if proj-candidate?
                           (if-let [inst (synthesize* st env index resolved-type (inc depth))]
                             (conj acc inst)
                             nil)
                           nil))))))
               []
               @arg-info)]
          (when filled-args
            (candidate-application st ctype goal-type
                                   (e/const' (:name candidate) inst-levels)
                                   filled-args)))))))

(defn- at-least-two-instance
  "`Nat.AtLeastTwo n` for a numeral n >= 2. This is the side condition of Mathlib's
   `instOfNatAtLeastTwo`, i.e. of EVERY numeric literal >= 2 at a non-`Nat` type (`(2 : R)`).
   Lean discharges it with `instance [NeZero n] : (n+1).AtLeastTwo` plus literal unification —
   matching `?n + 1` against `2` is arithmetic our first-order matcher cannot do. The class is a
   one-field Prop (`2 <= n`), so build it directly from the decidable comparison, which the
   kernel evaluates on a literal. Returns nil for anything else."
  [^Env env goal-type]
  (let [[h args] (e/get-app-fn-args goal-type)]
    (when (and (e/const? h)
               (= "Nat.AtLeastTwo" (name/->string (e/const-name h)))
               (= 1 (count args))
               (e/lit-nat? (first args))
               (>= (e/lit-nat-val (first args)) 2)
               (env/lookup env (name/from-string "Nat.AtLeastTwo.mk"))
               (env/lookup env (name/from-string "Nat.le_of_ble_eq_true")))
      (let [n (first args)]
        (e/app* (e/const' (name/from-string "Nat.AtLeastTwo.mk") []) n
                (e/app* (e/const' (name/from-string "Nat.le_of_ble_eq_true") [])
                        (e/lit-nat 2) n
                        (e/app* (e/const' (name/from-string "Eq.refl") [(lvl/succ lvl/zero)])
                                (e/const' (name/from-string "Bool") [])
                                (e/const' (name/from-string "Bool.true") []))))))))

(declare synthesize*)

(defn- decidable-eq-instance
  "`Decidable (@Eq.{u} T a b)` ⇐ `(inst a b)` for a synthesized `inst : DecidableEq.{u} T`,
   type-checked against the goal. nil for any other goal."
  [st env index goal-type head-info depth]
  (when (= "Decidable" (name/->string head-info))
    (let [[_ gargs] (e/get-app-fn-args goal-type)
          [eh eargs] (when (= 1 (count gargs)) (e/get-app-fn-args (first gargs)))]
      (when (and eh (e/const? eh) (= "Eq" (name/->string (e/const-name eh))) (= 3 (count eargs)))
        (let [[T a b] eargs
              deq (e/app (e/const' (name/from-string "DecidableEq") (vec (e/const-levels eh))) T)]
          (when-let [inst (synthesize* st env index deq (inc depth))]
            (let [t (e/app* inst a b)]
              (when (tc/is-def-eq st (tc/infer-type st t) goal-type)
                t))))))))

(declare synthesize-tracked*)

(def ^:dynamic *depth-hits*
  "Within one `synthesize` call: an atom of the goals at which the depth bound cut a path."
  nil)

(defn synthesize*
  "Synthesis with depth limit and backtracking, memoized on the tc-state
   (`:synth-memo`, Lean's synthInstance cache — failures memoize too, which is
   what collapses the repeated exploration of an unsatisfiable class goal
   across hundreds of candidate chains).
   Candidates come from the explicitly supplied registry. The environment
   must carry its instance extension even when that registry is empty."
  [st env index goal-type depth]
  (index-for env)
  (if (nil? *depth-hits*)
    ;; every top-level search tracks its own depth cuts, so no caller can memoize a cut path;
    ;; a search that fails after a cut is exhausted, not negative (Lean checkSystem names its
    ;; limit), so it says so instead of returning nil
    (binding [*depth-hits* (atom [])]
      (or (synthesize-tracked* st env index goal-type depth)
          (when-let [hits (seq @*depth-hits*)]
            (throw (ex-info (str "Tactic error: instance synthesis exhausted the search depth bound "
                                 "(*max-synth-depth* " config/*max-synth-depth* ", " (count hits) " path(s) cut)")
                            {:kind :tactic-error :reason :depth-exhausted
                             :limit config/*max-synth-depth* :goal goal-type :depth-limit-hits (count hits)})))))
    (synthesize-tracked* st env index goal-type depth)))

(defn- synthesize-tracked*
  [st env index goal-type depth]
  ;; The depth bound is an artifact of this depth-first search (Lean's tabled resolution needs
  ;; none): exceeding it fails THIS candidate path, so the search goes on with the next
  ;; candidate, and the hit is recorded (`synthesize` reports it if the whole search fails).
  ;; A failure that involved a cut holds only for the remaining budget it was searched with, so
  ;; it is memoized as `{::cut-fail remaining}` and reused by attempts with no more budget left;
  ;; never memoizing it re-explores the same subgoals exponentially on Mathlib-sized registries.
  (if (> depth config/*max-synth-depth*)
    (do (when *depth-hits* (swap! *depth-hits* conj goal-type))
        nil)
    (let [memo (:synth-memo st)
          remaining (- config/*max-synth-depth* depth)
          hit (when memo (find @memo goal-type))
          cached (when hit (val hit))]
      (cond
        (and hit (not (map? cached)))
        cached

        (and hit (<= remaining (::cut-fail cached)))
        (do (when *depth-hits* (swap! *depth-hits* conj goal-type))
            nil)

        :else
        (let [hits-before (some-> *depth-hits* deref count)
              result (synthesize-uncached* st env index goal-type depth)
              cut? (not= hits-before (some-> *depth-hits* deref count))]
          (when memo
            (swap! memo assoc goal-type
                   (cond result result
                         cut? {::cut-fail (max remaining (or (::cut-fail cached) -1))}
                         :else nil)))
          result)))))

(defn- synthesize-uncached*
  [st env index goal-type depth]
  ;; Get the goal's head class name (try raw, then WHNF)
  (let [head-info (or (let [[h _] (e/get-app-fn-args goal-type)]
                        (when (e/const? h) (e/const-name h)))
                      (let [w (whnf st goal-type)
                            [h _] (e/get-app-fn-args w)]
                        (when (e/const? h) (e/const-name h))))]
    (when head-info
      (let [;; Local instances FIRST (Lean synthInstance checks local-context instances): an lctx
              ;; hypothesis whose type head is this class and is def-eq to the goal (e.g. a polymorphic
              ;; `dec : DecidableEq K` discharging a `DecidableEq K` obligation).
            local-inst
            (some (fn [[fid decl]]
                    (when (and (= :local (:tag decl)) (:type decl))
                      (let [[dh _] (e/get-app-fn-args (:type decl))]
                        (when (and (e/const? dh) (= (e/const-name dh) head-info)
                                   (tc/is-def-eq st (:type decl) goal-type))
                          (e/fvar fid)))))
                  (:lctx st))
            candidates (get-instances index head-info)
            ;; Lean Meta/SynthInstance.lean:getInstances/generate tries all keyed matches;
            ;; a candidate count must never change a successful search into a miss.
            from-candidates (when-not local-inst
                              (some (fn [candidate]
                                      (try-candidate st env index candidate goal-type depth))
                                    (select-candidates env candidates goal-type)))]
        (or local-inst
            from-candidates
              ;; `Nat.AtLeastTwo <numeral>` — built, not searched (see above). Type-checked
              ;; against the goal like every other path here.
            (when-let [t (at-least-two-instance env goal-type)]
              (when (tc/is-def-eq st (tc/infer-type st t) goal-type)
                t))
              ;; `Decidable (@Eq T a b)` from a `DecidableEq T` instance. Lean keys DecidableEq
              ;; instances under their unfolded conclusion `Decidable (Eq _ _ _)`, so they answer
              ;; such goals directly; the registry here lists them under `DecidableEq`. Type-checked.
            (decidable-eq-instance st env index goal-type head-info depth))))))

;; ============================================================
;; Public API
;; ============================================================

(defn synthesize
  "Synthesize a typeclass instance for the given goal type.
   Returns the fully-applied instance term, or throws if not found."
  [env index goal-type]
  (let [st (tc/mk-tc-state env)]
    (binding [*depth-hits* (or *depth-hits* (atom []))]
      (or (synthesize* st env index goal-type 0)
          (let [hits @*depth-hits*]
            (throw (ex-info (str "Tactic error: instance resolution: no instance found"
                                 (when (seq hits)
                                   (str "; the search depth bound (*max-synth-depth* "
                                        config/*max-synth-depth* ") cut " (count hits) " path(s)")))
                            {:kind :tactic-error :reason :no-instance :goal goal-type
                             :depth-limit-hits (count hits)})))))))

(defn resolve-decidable
  "Convenience: resolve a Decidable instance for a proposition, against the session's registry."
  [env prop]
  (let [index (index-for env)
        decidable-name (name/from-string "Decidable")
        goal (e/app (e/const' decidable-name []) prop)]
    (synthesize env index goal)))

(defn verify-instance
  "Verify that the resolved instance has the expected type `Decidable P`."
  [env prop instance]
  (let [st (tc/mk-tc-state env)
        decidable-name (name/from-string "Decidable")
        inferred (tc/infer-type st instance)
        expected (e/app (e/const' decidable-name []) prop)]
    (tc/is-def-eq st inferred expected)))

;; ============================================================
;; Tabled Resolution — additive, does NOT modify existing code
;; ============================================================

(defn tabled-synthesize
  "Tabled typeclass synthesis for deep instance chains.
   Iterative state machine — call explicitly for complex cases
   like AddRightMono Real that recursive synthesize* can't handle.
   Does NOT modify synthesize or synthesize*."
  [st env index goal-type]
  (index-for env)
  (let [max-steps 200
        result (atom nil)
        gen-stack (atom [])

        get-cands (fn [gtype]
                    (let [[h _] (e/get-app-fn-args gtype)]
                      (when (e/const? h)
                        (vec (select-candidates env
                                                (get-instances index (e/const-name h))
                                                gtype)))))

        try-fill (fn [candidate gtype]
                   (let [^ConstantInfo ci (env/lookup env (:name candidate))
                         cty (.type ci)
                         lps (vec (.levelParams ci))
                         lvls (mapv (fn [_] lvl/zero) lps)
                         cty (if (seq lps)
                               (e/instantiate-level-params cty (zipmap lps lvls))
                               cty)
                         [_ gargs] (e/get-app-fn-args gtype)
                         type-arg (first gargs)]
                     (loop [t cty args []]
                       (if (e/forall? t)
                         (let [pty (e/forall-type t)
                               pty-sub (reduce (fn [ty val] (e/instantiate1 ty val))
                                               pty (reverse args))
                               tw (#'tc/cached-whnf st pty-sub)
                               val (cond
                                     (and tw (e/sort? tw)) type-arg
                                     :else (synthesize* st env index pty-sub 10))]
                           (if val
                             (recur (e/instantiate1 (e/forall-body t) val)
                                    (conj args val))
                             nil))
                         (candidate-application st cty gtype
                                                (e/const' (:name candidate) lvls)
                                                args)))))]

    (when-let [cands (get-cands goal-type)]
      (swap! gen-stack conj {:type goal-type :candidates cands :idx 0}))

    (loop [steps 0]
      (cond
        @result @result
        (>= steps max-steps)
        (throw (ex-info "Tactic error: tabled instance synthesis exceeded max-steps"
                        {:kind :tactic-error :limit max-steps :goal goal-type}))
        (seq @gen-stack)
        (let [gnode (peek @gen-stack)]
          (if (>= (:idx gnode) (count (:candidates gnode)))
            (do (swap! gen-stack pop) (recur (inc steps)))
            (let [cand (nth (:candidates gnode) (:idx gnode))]
              (swap! gen-stack update (dec (count @gen-stack)) update :idx inc)
              (when-let [term (try-fill cand (:type gnode))]
                (reset! result term))
              (recur (inc steps)))))
        :else nil))))

;; ============================================================
;; synthPending — instance synthesis from inside unification
;; ============================================================

(defn synth-pending-instance
  "`ansatz.meta/*synth-pending-fn*`: synthesize the instance goal that `isDefEq` got stuck on
   (Lean's `synthPending`). Uses the session's registry (`index-for`) and the tc-state's synth
   memo, so a goal that keeps recurring during one match costs a single resolution."
  [_mctx st goal]
  (synthesize* st (:env st) (index-for (:env st)) goal 0))

;; Loading this namespace is what makes instances synthesizable; installing the hook here
;; keeps `ansatz.meta` free of any dependency on the tactic layer.
(alter-var-root #'meta/*synth-pending-fn* (constantly synth-pending-instance))
