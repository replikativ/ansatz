;; Tactic layer — general typeclass instance resolution.

(ns ansatz.tactic.instance
  "Typeclass instance resolution following Lean 4's synthesis algorithm.

   Two instance discovery strategies:
   1. Pre-built index (from scanning all constants at import time)
   2. On-demand name-based discovery (for PSS environments)

   Resolution uses structural matching with isDefEq fallback,
   recursive synthesis for inst-implicit args, and depth limiting."
  (:require [clojure.string :as str]
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

(defn build-instance-index
  "Build an instance index: class-name → [{:name Name :arity Nat} ...].
   Two modes:
   - With all-constants available: scan everything (used at import time)
   - With PSS env: use name-based discovery for common classes (fast, ~200ms)"
  ([^Env env] (build-instance-index env nil))
  ([^Env env types]
   (let [idx (atom {})
         all-consts (env/all-constants env)]
     (if (seq all-consts)
       ;; Full scan mode (import time, non-PSS env)
       (do
         (doseq [^ConstantInfo ci all-consts]
           (when (or (.isDef ci) (.isThm ci))
             (when-let [[head-name arity] (return-type-head (.type ci))]
               (let [s (name/->string (.name ci))]
                 ;; Include potential instances: inst*, *.inst*, *.to*, *.dec*
                 (when (or (.contains s "inst") (.contains s "Inst")
                           (.contains s ".to") (.contains s ".dec")
                           (.contains s "Dec"))
                   (swap! idx update head-name
                          (fnil conj []) {:name (.name ci) :arity arity}))))))
         ;; Sort candidates: more specific (higher arity) first
         (into {} (map (fn [[k vs]]
                         [k (sort-by (fn [v]
                                       (let [s (str (:name v))]
                                         (if (.startsWith s "Classical.")
                                           [1 (- (:arity v))]
                                           [0 (- (:arity v))])))
                                     vs)])
                       @idx)))
       ;; PSS mode: name-based discovery for common classes + types
       (let [common-classes ["Add" "Mul" "Sub" "Div" "Neg" "SMul" "Zero" "One"
                             "AddZeroClass" "MulZeroClass" "MulOneClass"
                             "AddMonoid" "Monoid" "AddGroup" "Group"
                             "AddCommMonoid" "CommMonoid" "AddCommGroup" "CommGroup"
                             "AddSemigroup" "Semigroup" "AddCommMagma" "CommMagma"
                             "Field" "DivisionRing" "Ring" "CommRing"
                             "NormedAddCommGroup" "NormedRing" "NormedField" "NormedSpace"
                             "InnerProductSpace" "RCLike" "NormedAlgebra"
                             "MulZeroOneClass" "MonoidWithZero" "SubtractionMonoid"
                             "NonUnitalNormedRing" "SeminormedAddCommGroup"
                             "Module" "Algebra" "NormedCommRing"
                             "HSMul" "HAdd" "HMul" "HSub" "HDiv" "HPow"
                             "Decidable" "DecidableEq" "BEq" "Repr" "ToString"]
             known-types (or types ["Nat" "Int" "Real" "Complex" "Float"])]
         (doseq [cls common-classes]
           (let [cls-name (name/from-string cls)
                 candidates (atom [])]
             ;; Try naming patterns for each type
             (doseq [typ known-types]
               (doseq [pattern [(str "inst" cls typ)
                                (str typ ".inst" cls)]]
                 (when-let [ci (env/lookup env (name/from-string pattern))]
                   (swap! candidates conj {:name (.name ci) :arity 0}))))
             ;; Try bare instCls pattern
             (when-let [ci (env/lookup env (name/from-string (str "inst" cls)))]
               (swap! candidates conj {:name (.name ci) :arity 0}))
             ;; Store if found
             (when (seq @candidates)
               (swap! idx assoc cls-name (distinct @candidates)))))
         @idx)))))

(defn add-instance
  "Lean's `addInstance`: a NEW env whose instance table (the `:instances` extension) also
   holds the constant `inst-name`, keyed by the class its type concludes in, at `priority`
   (Lean's default 1000). Among equal priorities the newest registration is tried FIRST, as
   in Lean's DiscrTree insertion order; a higher priority still goes ahead of it. An env with
   no registry yet is seeded by discovery, so the new instance never shadows what discovery
   would have found."
  [^Env env inst-name & {:keys [priority] :or {priority 1000}}]
  (let [ci (or (env/lookup env inst-name)
               (throw (ex-info "add-instance: no such constant" {:name (name/->string inst-name)})))
        [cls _] (or (return-type-head (.type ci))
                    (throw (ex-info "add-instance: the type does not conclude in a class"
                                    {:name (name/->string inst-name)})))
        idx (or (env/get-extension env :instances nil) (build-instance-index env))
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
                                                (try (Long/parseLong (nth parts 2)) (catch Exception _ 1000))
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
   `load-init!` tier's counterpart of the store's derived `:instances` blob. nil when the resource is
   not on the classpath."
  [{:keys [present?]}]
  (when-let [res (io/resource bundled-instances-resource)]
    (let [lines (with-open [in (java.util.zip.GZIPInputStream. (.openStream res))]
                  (str/split-lines (slurp in)))]
      (parse-instance-tsv lines present?))))

(defn index-for
  "The instance index to synthesize against for `env`: the registry carried ON the env (the
   `:instances` extension `setup-env!` attaches — a store's derived `:instances` blob, or the
   bundled Init registry; both are Lean's own @[instance] table), else name-based discovery
   over `env` — never a process-global registry that may belong to another env. Every
   synthesis entry point goes through this — an index built by discovery alone (39 hand-listed
   classes) never sees most of Mathlib. The env carries it because Lean's instance table is part of the environment:
   `decide` on an env must see THAT env's instances, and a process-global alone let a test's
   leftover registry for another env answer for it (the full suite failed nondeterministically
   in whichever namespace ran `decide` next)."
  [env]
  (let [on-env (env/get-extension env :instances nil)]
    (if (seq on-env) on-env (build-instance-index env))))

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
   then the generic ones — Lean's DiscrTree selection, one level deep, in Lean's order.

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
      (remove #(= :absent (conclusion-key env (:name %))) candidates)
      (let [scored (group-by (fn [c]
                               (let [ck (conclusion-key env (:name c))]
                                 (cond (= ck :absent) :no
                                       (= ck gkey) :exact
                                       (key-matches? ck gkey) :compatible
                                       :else :no)))
                             candidates)
            picked (into (vec (:exact scored)) (:compatible scored))]
        (if (empty? picked) (remove #(= :absent (conclusion-key env (:name %))) candidates) picked)))))

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

(defn- try-candidate
  "Try a single candidate instance against a goal type.
   Returns the fully-applied instance term, or nil on failure."
  [st env index candidate goal-type depth]
  (try
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
          result-type (loop [t ctype]
                        (let [tw (or (try (whnf st t) (catch Exception _ nil)) t)]
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
      ;; Match result-type vs goal-type.
      ;; Handles partial class applications: goal may have fewer args than result
      ;; (e.g., goal = InnerProductSpace ℝ ℝ with 2 args, result has 4 args)
      (let [result-type-w (or (try (whnf st result-type) (catch Exception _ nil)) result-type)
            goal-type-w (or (try (whnf st goal-type) (catch Exception _ nil)) goal-type)
            ;; Extract head + args from both sides
            [rh ra] (e/get-app-fn-args result-type-w)
            [gh ga] (e/get-app-fn-args goal-type-w)]
        (when-let [subst (or (structural-match result-type goal-type @fvar-ids)
                             (when (not= result-type result-type-w)
                               (structural-match result-type-w goal-type-w @fvar-ids))
                            ;; Partial application: result has MORE args than goal
                            ;; Match the first N args (goal's count), treat rest as extra
                             (when (and (e/const? rh) (e/const? gh)
                                        (= (e/const-name rh) (e/const-name gh))
                                        (>= (count ra) (count ga)))
                               (let [s (atom {}) ok (atom true)]
                                ;; Match only the first (count ga) args
                                 (doseq [[r g] (map vector (take (count ga) ra) ga)]
                                   (when @ok
                                     (if (and (e/fvar? r) (contains? @fvar-ids (e/fvar-id r)))
                                       (swap! s assoc (e/fvar-id r) g)
                                       (when-not (and (not (rigid-fvar-mismatch? r g))
                                                      (try (tc/is-def-eq st r g) (catch Exception _ false)))
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
                                        (= (e/const-name rh) (e/const-name gh))
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
            ;; Build fully applied term and verify it type-checks
              (let [term (reduce e/app (e/const' (:name candidate) inst-levels) filled-args)]
              ;; Verify: inferred type must match goal (handling partial applications)
                (try
                  (let [inferred (tc/infer-type st term)
                      ;; For partial class apps, check prefix match
                        [ih ia] (e/get-app-fn-args inferred)
                        n-goal-args (count ga)]
                    (if (or (tc/is-def-eq st inferred goal-type)
                          ;; Partial app: same head, first N args match
                            (and (e/const? ih) (e/const? gh)
                                 (= (e/const-name ih) (e/const-name gh))
                                 (>= (count ia) n-goal-args)
                                 (every? true?
                                         (map (fn [i g] (tc/is-def-eq st i g))
                                              (take n-goal-args ia) ga))))
                      term
                    ;; Try Java TC with more fuel
                      (let [jtc (ansatz.kernel.TypeChecker. (:env st))]
                        (.setFuel jtc config/*high-fuel*)
                        (let [jinf (.inferType jtc term)
                              [jh ja] (e/get-app-fn-args jinf)]
                          (when (and (e/const? jh)
                                     (= (e/const-name jh) (e/const-name gh))
                                     (>= (count ja) n-goal-args)
                                     (every? true?
                                             (map (fn [i g] (.isDefEq jtc i g))
                                                  (take n-goal-args ja) ga)))
                            term)))))
                  (catch Exception _ nil))))))))
    (catch Exception _ nil)))

(def ^:private parent-class-sources
  "Curated superclass → subclasses whose structure-`extends` parent projection `{Sub}.to{Super}`
   yields an instance of the superclass (Lean auto-registers these as instances). Needed for PSS
   envs, where `build-instance-index` can't scan the lazy store to find the `.to` projections (the
   full-scan path only sees the locally-added constants). Same curated style as `common-classes`;
   extend as new class hierarchies are exercised. The synthesizer fills the projection's structure
   argument by recursive synthesis (see try-candidate's projection-arg handling)."
  {"ReflBEq"    ["LawfulBEq" "EquivBEq"]
   "EquivBEq"   ["LawfulBEq"]
   ;; WSemiring extends WAddMonoid — its `WSemiring.toWAddMonoid` projection is the registered
   ;; instance that fills a `WAddMonoid S` goal from a local `WSemiring S` instance (the
   ;; instance-implicit `wsum` over WSemiring-parameterized laws relies on this resolution).
   "WAddMonoid" ["WSemiring"]})

(defn- discover-candidates
  "On-demand candidate discovery for PSS environments.
   Tries naming conventions to find instances without scanning all constants.
   Returns a seq of {:name Name :arity Nat} candidates."
  [env class-name goal-type]
  (let [class-str (name/->string class-name)
        [_ goal-args] (e/get-app-fn-args goal-type)
        ;; Extract type names from goal args for name pattern search
        type-names (keep (fn [arg]
                           (let [[h _] (e/get-app-fn-args arg)]
                             (when (e/const? h) (name/->string (e/const-name h)))))
                         goal-args)
        ;; Generate candidate names to try
        ;; Also extract head names from NESTED expressions (e.g., And in And (Eq ...) True)
        nested-heads (keep (fn [arg]
                             (let [[h _] (e/get-app-fn-args arg)]
                               (when (e/const? h) (name/->string (e/const-name h)))))
                           (mapcat (fn [arg]
                                     (let [[_ args] (e/get-app-fn-args arg)]
                                       (cons arg args)))
                                   goal-args))
        all-names (distinct (concat type-names nested-heads))
        candidate-names
        (distinct
         (concat
            ;; inst{Class}{Type} patterns
          (for [tn all-names]
            (str "inst" class-str tn))
            ;; {Type}.inst{Class} patterns
          (for [tn all-names]
            (str tn ".inst" class-str))
            ;; inst{Class} (bare, for classes with parameters handled by forall args)
          [(str "inst" class-str)]
            ;; DecidableEq pattern: when goal is Decidable (Eq T a b),
            ;; also try instDecidableEq{T} which returns DecidableEq T
          (when (= class-str "Decidable")
            (for [tn all-names]
              (str "instDecidableEq" tn)))
            ;; Structure-`extends` parent projections {Sub}.to{Class} — an instance of Class via a
            ;; subclass instance (e.g. ReflBEq via LawfulBEq.toReflBEq). try-candidate synthesizes the
            ;; projection's structure argument; the goal class is the projection's RETURN type.
          (for [sub (get parent-class-sources class-str)]
            (str sub ".to" class-str))))]
    (keep (fn [n]
            (let [nm (name/from-string n)]
              (when (env/lookup env nm)
                {:name nm :arity 0})))
          candidate-names)))

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

(defn synthesize*
  "Synthesis with depth limit and backtracking, memoized on the tc-state
   (`:synth-memo`, Lean's synthInstance cache — failures memoize too, which is
   what collapses the repeated exploration of an unsatisfiable class goal
   across hundreds of candidate chains).
   Uses the pre-built index when available, falls back to on-demand
   candidate discovery for PSS environments."
  [st env index goal-type depth]
  (let [memo (:synth-memo st)]
    (if-let [hit (when memo (find @memo goal-type))]
      (val hit)
      (let [result (synthesize-uncached* st env index goal-type depth)]
        (when (and memo (not (> depth config/*max-synth-depth*)))
          (swap! memo assoc goal-type result))
        result))))

(defn- synthesize-uncached*
  [st env index goal-type depth]
  (when-not (> depth config/*max-synth-depth*)  ;; configurable depth limit
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
                                     (try (tc/is-def-eq st (:type decl) goal-type)
                                          (catch Throwable _ false)))
                            (e/fvar fid)))))
                    (:lctx st))
              ;; Try pre-built index first, then on-demand discovery
              candidates (let [idx-cands (get-instances index head-info)]
                           (if (seq idx-cands)
                             idx-cands
                             (discover-candidates env head-info goal-type)))
            ;; Try candidates from index/discovery
            ;; Limit candidates to prevent combinatorial explosion
            ;; (some classes have 300+ instances in Mathlib)
              from-candidates (when-not local-inst
                                (some (fn [candidate]
                                        (try-candidate st env index candidate goal-type depth))
                                      (take config/*max-candidates*
                                            (select-candidates env candidates goal-type))))]
          (or local-inst
              from-candidates
              ;; `Nat.AtLeastTwo <numeral>` — built, not searched (see above). Type-checked
              ;; against the goal like every other path here.
              (when-let [t (at-least-two-instance env goal-type)]
                (when (try (tc/is-def-eq st (tc/infer-type st t) goal-type)
                           (catch Exception _ false))
                  t))
            ;; Fallback: name-based resolution with derivation chains (from ansatz.core).
            ;; TYPE-CHECKED before it is returned: that resolver builds terms from naming
            ;; conventions alone and its H-class rule assumes a HOMOGENEOUS operator, so on a
            ;; genuinely heterogeneous goal (`HPow Real Nat Real`) it produced an ill-typed
            ;; `instHPow Real Real.instPow` that silently poisoned the elaborated term. Every
            ;; other path here verifies its result; this one now does too, with the same
            ;; tolerance try-candidate applies (head + argument prefix, so a goal whose universe
            ;; the caller left at zero still resolves — inference alone rejects the poison).
              (try
                (let [resolve-fn (requiring-resolve 'ansatz.core/resolve-basic-instance)
                      [_ goal-args] (e/get-app-fn-args goal-type)
                      type-arg (first goal-args)
                      [th _] (when type-arg (e/get-app-fn-args type-arg))
                      class-str (name/->string head-info)
                      type-str (when (e/const? th) (name/->string (e/const-name th)))]
                  (when-let [term (when type-str (resolve-fn env class-str type-str type-arg))]
                    (let [inferred (tc/infer-type st term)
                          [ih ia] (e/get-app-fn-args inferred)]
                      (when (or (tc/is-def-eq st inferred goal-type)
                                (and (e/const? ih)
                                     (= (e/const-name ih) head-info)
                                     (>= (count ia) (count goal-args))
                                     (every? true?
                                             (map (fn [i g] (tc/is-def-eq st i g))
                                                  (take (count goal-args) ia) goal-args))))
                        term))))
                (catch Exception _ nil))))))))  ;; extra close for when-not

;; ============================================================
;; Public API
;; ============================================================

(defn synthesize
  "Synthesize a typeclass instance for the given goal type.
   Returns the fully-applied instance term, or throws if not found."
  [env index goal-type]
  (let [st (tc/mk-tc-state env)]
    (or (synthesize* st env index goal-type 0)
        (throw (ex-info "Instance resolution: no instance found"
                        {:kind :no-instance :goal goal-type})))))

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
  (let [max-steps 200
        jtc (doto (ansatz.kernel.TypeChecker. env) (.setFuel 30000000))
        result (atom nil)
        gen-stack (atom [])

        get-cands (fn [gtype]
                    (let [[h _] (e/get-app-fn-args gtype)]
                      (when (e/const? h)
                        (let [cands (get-instances index (e/const-name h))
                              sorted (sort-by (fn [c]
                                                (let [s (name/->string (:name c))]
                                                  (if (re-find #"\.to[A-Z]" s) 0 1)))
                                              cands)]
                          (vec (take 6 sorted))))))

        try-fill (fn [candidate gtype]
                   (try
                     (let [^ConstantInfo ci (env/lookup env (:name candidate))
                           cty (.type ci)
                           lps (vec (.levelParams ci))
                           lvls (mapv (fn [_] lvl/zero) lps)
                           cty (if (seq lps)
                                 (e/instantiate-level-params cty (zipmap lps lvls))
                                 cty)
                           [_ gargs] (e/get-app-fn-args gtype)
                           type-arg (first gargs)]
                       (loop [t cty args [] n 0]
                         (if (and (e/forall? t) (< n 8))
                           (let [pty (e/forall-type t)
                                 pty-sub (reduce (fn [ty val] (e/instantiate1 ty val))
                                                 pty (reverse args))
                                 tw (try (#'tc/cached-whnf st pty-sub) (catch Exception _ nil))
                                 val (cond
                                       (and tw (e/sort? tw)) type-arg
                                       :else (try (synthesize* st env index pty-sub 10)
                                                  (catch Exception _ nil)))]
                             (if val
                               (recur (e/instantiate1 (e/forall-body t) val)
                                      (conj args val) (inc n))
                               nil))
                           (when (seq args)
                             (let [term (reduce e/app (e/const' (:name candidate) lvls) args)]
                               (when (.isDefEq jtc (.inferType jtc term) gtype)
                                 term))))))
                     (catch Exception _ nil)))]

    (when-let [cands (get-cands goal-type)]
      (swap! gen-stack conj {:type goal-type :candidates cands :idx 0}))

    (loop [steps 0]
      (cond
        @result @result
        (>= steps max-steps) nil
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
  (try (synthesize* st (:env st) (index-for (:env st)) goal 0) (catch Throwable _ nil)))

;; Loading this namespace is what makes instances synthesizable; installing the hook here
;; keeps `ansatz.meta` free of any dependency on the tactic layer.
(alter-var-root #'meta/*synth-pending-fn* (constantly synth-pending-instance))
