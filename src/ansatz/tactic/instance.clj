;; Follows Lean 4 (../lean4), Meta/Instances.lean:instanceExtension/addInstance and
;; Meta/SynthInstance.lean:getInstances. Candidates come only from registered instances.

(ns ansatz.tactic.instance
  "Typeclass instance resolution following Lean 4's synthesis algorithm (Meta/SynthInstance.lean).

   A candidate is opened with metavariables (getSubgoals), its conclusion unified with the goal
   by `ansatz.meta/is-def-eq` with synthPending (tryResolve), and its instance-implicit
   arguments solved as subgoals in synthesis order (consume). The search is depth-first with
   backtracking, a memo of closed goals (Lean's synthInstance cache), a cycle cut standing in
   for tabling, and a depth bound."
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
   (let [seen (java.util.HashMap.)
         idx (reduce (fn [idx line]
                       (let [parts (str/split line #"\t")]
                         (if (and (>= (count parts) 2)
                                  (or (nil? present?) (present? (nth parts 1))))
                           (let [cls (name/from-string (nth parts 0))
                                 prio (if (>= (count parts) 3) (Long/parseLong (nth parts 2)) 1000)
                                 k [(nth parts 0) (nth parts 1)]]
                             (if-let [pos (.get seen k)]
                               ;; an instance registered again (`attribute [instance 50] C.toX` after
                               ;; the structure-parent registration at 1000, or a re-exporting
                               ;; module) is ONE entry: Lean's DiscrTree.insertVal replaces the
                               ;; equal value in place, so it keeps its position and takes the
                               ;; LATER priority
                               (assoc-in idx [cls pos :priority] prio)
                               (do (.put seen k (count (get idx cls [])))
                                   (update idx cls (fnil conj [])
                                           {:name (name/from-string (nth parts 1)) :priority prio}))))
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
  "Lean's DiscrTree root key of `x` (DiscrTree.lean `pushArgs`/`getKeyArgs`): the head constant;
   `.sort` for a sort, `.arrow` for a ∀ (Lean distinguishes `.arrow` and `.other` for dependent
   ones), `.fvar` for a local; :generic (Lean's `.star`) for a bound
   variable of the instance or a metavariable. A goal key that is not :generic only meets
   candidates with the same key or a star: `OfNat (Sort 1) 0` sees `One.toOfNat1`-style generic
   instances, not the 160 carrier-specific `OfNat` instances of Mathlib."
  [x]
  (let [x (loop [x x] (if (and x (e/mdata? x)) (recur (e/mdata-expr x)) x))
        [h _] (when x (e/get-app-fn-args x))]
    (cond
      (nil? h) :generic
      (e/const? h) (e/const-name h)
      (e/sort? h) :sort
      (e/forall? h) :arrow
      ;; literals stay stars: Lean keys offset terms `n + 2` as stars, so `(n+2).AtLeastTwo`
      ;; must still meet the goal `AtLeastTwo 5`
      (e/fvar? h) [:fvar (e/fvar-id h)]
      (e/lam? h) :other
      :else :generic)))

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
;; Synthesis engine
;; ============================================================

(defn- whnf [st expr]
  (#'tc/cached-whnf st expr))

(declare synthesize* synthesize-uncached*)

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

;; ============================================================
;; tryResolve — Lean's SynthInstance.getSubgoals / tryResolve / consume
;; ============================================================
;; A candidate is opened with METAVARIABLES for all of its binders (getSubgoals), its
;; conclusion is UNIFIED with the goal (tryResolve: `isDefEq mvarTypeBody instTypeBody`), and
;; the instance-implicit binders that unification left unassigned become subgoals, solved in
;; Lean's synthesis order (consume). Unification is `ansatz.meta/is-def-eq`, whose synthPending
;; hook synthesizes an instance metavariable that a projection chain is stuck on: that is how
;; `IsStrictOrderedRing.toPosMulStrictMono {inst : Semiring R} …`, whose conclusion mentions
;; `inst` only under `Distrib.toMul R (instDistribOfSemiring R inst)`, meets the goal's
;; `Real.instMul` (Lean trace: `found stuck MVar ?m : Semiring ℝ` → `synthInstance Semiring ℝ`).
;; A first-order matcher on pattern fvars cannot assign such a binder.

(def ^:private out-param-cache (atom {}))

(defn- has-loose-bvar?
  "Does `x` contain the loose bound variable `k` (counted at the top of `x`)?"
  [x k]
  (letfn [(go [x d]
            (when (e/has-loose-bvars? x d)
              (case (e/tag x)
                :bvar (= (e/bvar-idx x) (+ k d))
                :app (or (go (e/app-fn x) d) (go (e/app-arg x) d))
                :lam (or (go (e/lam-type x) d) (go (e/lam-body x) (inc d)))
                :forall (or (go (e/forall-type x) d) (go (e/forall-body x) (inc d)))
                :let (or (go (e/let-type x) d) (go (e/let-value x) d) (go (e/let-body x) (inc d)))
                :mdata (go (e/mdata-expr x) d)
                :proj (go (e/proj-struct x) d)
                false)))]
    (boolean (go x 0))))

(defn- out-param-positions
  "Lean's `getOutParamPositions?`: the argument positions of class `cls` whose binder type is
   `outParam _`, plus (Lean's `checkOutParam`) instance-implicit binders that depend on one."
  [^Env env cls]
  (if-let [hit (find @out-param-cache [env cls])]
    (val hit)
    (let [ci (env/lookup env cls)
          res (when ci
                (loop [t (.type ^ConstantInfo ci) i 0 outs #{} out-bvars []]
                  (if (e/forall? t)
                    (let [d (e/forall-type t)
                          [dh _] (e/get-app-fn-args d)
                          out? (or (and (e/const? dh) (= "outParam" (name/->string (e/const-name dh))))
                                   (and (= :inst-implicit (e/forall-info t))
                                        ;; loose bvar j in d refers to binder i-1-j
                                        (some (fn [k] (has-loose-bvar? d (- i 1 k))) out-bvars)))]
                      (recur (e/forall-body t) (inc i) (if out? (conj outs i) outs)
                             (if out? (conj out-bvars i) out-bvars)))
                    outs)))]
      (swap! out-param-cache assoc [env cls] res)
      res)))

(defn- fresh-mvar
  "Declare a fresh expression metavariable of `type` in the lctx of `st`. Class-typed mvars are
   marked instance mvars so `meta/is-def-eq` may synthPending them (Lean's synthPendingImp
   synthesizes any natural mvar whose type is a class)."
  [st index mctx type]
  (let [id (swap! (:next-id st) inc)
        [h _] (e/get-app-fn-args type)
        cls? (and (e/const? h)
                  (or (contains? index (e/const-name h))
                      ;; Lean's classExtension (`:classes`): classes without registered instances,
                      ;; e.g. a user structure only ever supplied by a local instance
                      (contains? (env/get-extension (:env st) :classes #{}) (name/->string (e/const-name h)))))]
    [(meta/add-expr-mvar-decl mctx id type (:lctx st) (if cls? {:inst-implicit? true} {}))
     (e/mvar id)]))

(defn- preprocess-out-params
  "Lean's `preprocessOutParam`: replace the goal's outParam arguments by fresh metavariables.
   The answer is checked against the ORIGINAL goal afterwards (Lean's `assignOutParams`)."
  [st env index mctx goal]
  (let [[h args] (e/get-app-fn-args goal)
        outs (when (e/const? h) (out-param-positions env (e/const-name h)))]
    (if (empty? outs)
      [mctx goal]
      (loop [i 0 ty (tc/infer-type st h) mctx mctx acc []]
        (if (< i (count args))
          (let [ty (whnf st ty)
                d (e/forall-type ty)
                [mctx arg] (if (contains? outs i)
                             (fresh-mvar st index mctx (meta/zonk-expr mctx d))
                             [mctx (nth args i)])]
            (recur (inc i) (e/instantiate1 (e/forall-body ty) arg) mctx (conj acc arg)))
          [mctx (apply e/app* h acc)])))))

(defn- open-candidate
  "Lean's `getSubgoals`: a metavariable per binder of the candidate's type (reducing to expose
   further binders, but not through the goal's own class head — `DecidableEq (Fin ?n)` must stay
   folded to meet the goal `DecidableEq (Fin 3)`). Universe parameters become level mvars.
   Returns {:mctx :val :body :mvars [{:mvar :info :type}]}."
  [st index mctx ^ConstantInfo ci cname goal-head]
  (let [lps (vec (.levelParams ci))
        lids (vec (repeatedly (count lps) #(swap! (:next-id st) inc)))
        mctx (reduce meta/add-level-mvar-decl mctx lids)
        lvls (mapv lvl/mvar lids)
        ty (cond-> (.type ci) (seq lps) (e/instantiate-level-params (zipmap lps lvls)))]
    (loop [t ty mctx mctx val (e/const' cname lvls) mvars []]
      (let [[th _] (e/get-app-fn-args t)
            t (if (or (e/forall? t)
                      (and goal-head (e/const? th) (= (e/const-name th) goal-head)))
                t
                (or (whnf st t) t))]
        (if (e/forall? t)
          (let [d (e/forall-type t)
                [mctx mv] (fresh-mvar st index mctx d)]
            (recur (e/instantiate1 (e/forall-body t) mv) mctx (e/app val mv)
                   (conj mvars {:mvar mv :info (e/forall-info t) :type d})))
          {:mctx mctx :val val :body t :mvars mvars})))))

(defn- ready-subgoal?
  "Lean's computeSynthOrder readiness: the subgoal's non-outParam class arguments carry no
   unassigned metavariables."
  [env mctx ty]
  (let [ty (meta/zonk-expr mctx ty)
        [h args] (e/get-app-fn-args ty)
        outs (if (e/const? h) (out-param-positions env (e/const-name h)) #{})]
    (every? (fn [[i a]] (or (contains? outs i) (not (meta/has-expr-mvar? a))))
            (map-indexed vector args))))

(defn- lazy-mapcat
  "`mapcat` without chunking: each candidate is resolved only when the previous ones are
   exhausted. (`mapcat` over a vector realizes 32 elements at a time, i.e. resolves up to 32
   candidates — recursively — before the first answer is looked at.)"
  [f coll]
  (lazy-seq
   (when-let [s (seq coll)]
     (concat (f (first s)) (lazy-mapcat f (rest s))))))

(declare answers)
(declare ^:dynamic *depth-hits*)

(defn- solve-subgoals
  "Lean's `consume` loop as depth-first search: drop the subgoals unification already assigned,
   take the next READY one (synthesis order), and solve it against every answer in turn
   (backtracking into later answers when a later subgoal fails). Lazy seq of mctxs."
  [st env index mctx subgoals depth]
  (let [pending (remove #(meta/expr-assigned? mctx (e/mvar-id (:mvar %))) subgoals)]
    (if (empty? pending)
      (list mctx)
      ;; No ready subgoal: an input argument is still a metavariable the conclusion did not fix.
      ;; Lean refuses to register such an instance (computeSynthOrder, "cannot find
      ;; synthesization order"), so its TC never enumerates e.g. every `Category ?C`; neither do we.
      (when-let [sg (first (filter #(ready-subgoal? env mctx (:type %)) pending))]
        (let [rest-sgs (remove #(identical? % sg) pending)
              goal (meta/zonk-expr mctx (:type sg))]
        (lazy-mapcat (fn [[mctx' v]]
                  (when-let [mctx'' (try (meta/is-def-eq mctx' st (:mvar sg) v)
                                         (catch clojure.lang.ExceptionInfo _ nil))]
                    (solve-subgoals st env index mctx'' rest-sgs depth)))
                (answers st env index mctx goal (inc depth))))))))

(defn- projection-instance?
  "Structure-`extends` parent projections (`X.toY`): Lean's computeSynthOrder makes their
   structure argument a subgoal even where the binder is explicit."
  [cname]
  (let [s (name/->string cname)] (or (.contains s ".to") (.contains s ".toImpl"))))

(def ^:dynamic *synth-trace* nil)

(defn- try-resolve
  "Lean's `tryResolve` + `consume` for one candidate against `goal` (which may carry mvars of
   `mctx`). Lazy seq of [mctx instance-value]."
  [st env index mctx candidate goal depth]
  (when *synth-trace* (swap! *synth-trace* conj [depth (name/->string (:name candidate)) (str (meta/zonk-expr mctx goal)) (System/nanoTime)]))
  (let [cname (:name candidate)
        ^ConstantInfo ci (env/lookup! env cname)
        [gh _] (e/get-app-fn-args goal)
        goal-head (when (e/const? gh) (e/const-name gh))
        {:keys [mctx val body mvars]} (open-candidate st index mctx ci cname goal-head)
        [rh _] (e/get-app-fn-args body)]
    ;; DiscrTree pre-filter: a candidate whose conclusion has another class head never unifies
    (when (or (not (e/const? rh)) (nil? goal-head) (= (e/const-name rh) goal-head))
      (when-let [mctx (try (meta/is-def-eq mctx st goal body)
                           (catch clojure.lang.ExceptionInfo _ nil))]
        (let [proj? (projection-instance? cname)
              ;; the structure argument of a parent projection is explicit as a function but a
              ;; subgoal of the instance (Lean: computeSynthOrder's projInfo case)
              subgoals (filter (fn [{:keys [info]}]
                                 (or (= :inst-implicit info) (and proj? (= :default info))))
                               mvars)]
          (map (fn [mctx'] [mctx' (meta/zonk-expr mctx' val)])
               (solve-subgoals st env index mctx subgoals depth)))))))

(defn- local-instance-answers
  "Local instances (Lean's getInstances appends them to the candidates; tried first)."
  [st mctx goal head]
  (keep (fn [[fid decl]]
          (when (and (= :local (:tag decl)) (:type decl))
            (let [[dh _] (e/get-app-fn-args (:type decl))]
              (when (and (e/const? dh) (= (e/const-name dh) head))
                (when-let [mctx' (try (meta/is-def-eq mctx st goal (:type decl))
                                      (catch clojure.lang.ExceptionInfo _ nil))]
                  [mctx' (e/fvar fid)])))))
        (:lctx st)))

(defn- answers
  "Answers to an instance subgoal `goal` in `mctx`: lazy seq of [mctx value]. A goal without
   metavariables goes through the memoized `synthesize*` (one answer: Lean's canonical-instance
   assumption, `backward.synthInstance.canonInstances`); one with metavariables (an outParam
   left open, a type still to be determined) is resolved in place against every candidate."
  [st env index mctx goal depth]
  (if (not (meta/zonked-has-mvar? goal))
    (when-let [v (synthesize* st env index goal depth)]
      (list [mctx v]))
    (if (> depth config/*max-synth-depth*)
      (do (when *depth-hits* (swap! *depth-hits* conj goal)) nil)
      (let [[h _] (e/get-app-fn-args goal)]
        (when (e/const? h)
          (concat (local-instance-answers st mctx goal (e/const-name h))
                  (lazy-mapcat #(try-resolve st env index mctx % goal depth)
                          (select-candidates env (get-instances index (e/const-name h)) goal))))))))

(defn- close-answer
  "Root answer → closed instance term, or nil (Lean's root waiter skips answers with mvars).
   Universe mvars left unconstrained default to level zero."
  [mctx v]
  (let [mctx (reduce #(meta/assign-level %1 %2 lvl/zero) mctx (meta/unassigned-level-mvars mctx v))
        v (meta/zonk-expr mctx v)]
    (when (meta/closed-expr? mctx v) v)))

(defn- resolve-root
  "Lean's `synthInstance?` main loop for a closed goal: preprocess outParams, take the first root
   answer whose type is defeq to the ORIGINAL goal (`assignOutParams`, checked by the kernel)."
  [st env index candidates goal-type depth]
  (let [[mctx0 goal'] (preprocess-out-params st env index meta/empty-context goal-type)]
    (some (fn [[mctx v]]
            (when-let [t (close-answer mctx v)]
              (when (try (tc/is-def-eq st (tc/infer-type st t) goal-type)
                         (catch Exception _ false))
                t)))
          (lazy-mapcat #(try-resolve st env index mctx0 % goal' depth) candidates))))

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

(def ^:dynamic *active-goals*
  "Memo keys of the goals being resolved on the current search path (Lean: open table entries)."
  #{})

(def ^:dynamic *cycle-hits*
  "Within one top-level search: an atom of the goal keys at which a cycle was cut."
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
  (cond
    (nil? *cycle-hits*)
    (binding [*cycle-hits* (atom [])] (synthesize* st env index goal-type depth))

    (nil? *depth-hits*)
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
    :else
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
          ;; Lean's synthInstance cache key carries `synthPendingDepth`
          key (if (zero? meta/*synth-pending-depth*) goal-type [goal-type meta/*synth-pending-depth*])
          hit (when memo (find @memo key))
          cached (when hit (val hit))]
      (cond
        (and hit (not (map? cached)))
        cached

        (and hit (<= remaining (::cut-fail cached)))
        (do (when *depth-hits* (swap! *depth-hits* conj goal-type))
            nil)

        ;; The goal is already being resolved further up this search path: a cycle
        ;; (`littleWedderburn : [DivisionRing D] [Finite D] → Field D` against
        ;; `Field.toDivisionRing`). Lean's tabled resolution makes this a consumer of the existing
        ;; table entry instead of a new generator; an answer could only arrive through that entry,
        ;; and the outer search finds it directly. So the branch fails, and the failure is not
        ;; memoized below the cycle's root (it holds only while that goal is open).
        (contains? *active-goals* key)
        (do (when *cycle-hits* (swap! *cycle-hits* conj key))
            nil)

        :else
        (let [hits-before (some-> *depth-hits* deref count)
              cycles-before (some-> *cycle-hits* deref count)
              result (binding [*active-goals* (conj *active-goals* key)]
                       (synthesize-uncached* st env index goal-type depth))
              cut? (not= hits-before (some-> *depth-hits* deref count))
              ;; cycle hits back to THIS goal are resolved here; others belong to open ancestors
              foreign-cycle? (when *cycle-hits*
                               (let [new (subvec @*cycle-hits* cycles-before)
                                     foreign (filterv #(not= % key) new)]
                                 (reset! *cycle-hits* (into (subvec @*cycle-hits* 0 cycles-before) foreign))
                                 (seq foreign)))]
          (when (and memo (or result (not foreign-cycle?)))
            (swap! memo assoc key
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
                              (resolve-root st env index
                                            (select-candidates env candidates goal-type)
                                            goal-type depth))]
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
