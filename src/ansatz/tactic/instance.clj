;; Copyright (c) 2026 Christian Weilbach. All rights reserved.
;; Tactic layer — general typeclass instance resolution.

(ns ansatz.tactic.instance
  "Typeclass instance resolution following Lean 4's synthesis algorithm.

   Two instance discovery strategies:
   1. Pre-built index (from scanning all constants at import time)
   2. On-demand name-based discovery (for PSS environments)

   Resolution uses structural matching with isDefEq fallback,
   recursive synthesis for inst-implicit args, and depth limiting."
  (:require [clojure.string]
            [clojure.java.io]
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

(defn get-instances
  "Get candidate instances for a class name from the index."
  [index class-name]
  (get index class-name []))

(defn load-instance-tsv
  "Load instance registry from a TSV file (exported from Lean 4).
   Format: class-name<TAB>instance-name<TAB>priority
   Returns an instance index: {Name → [{:name Name :priority Nat} ...]}"
  [path]
  (let [idx (atom {})]
    (with-open [rdr (clojure.java.io/reader path)]
      (doseq [line (line-seq rdr)]
        (let [parts (clojure.string/split line #"\t")]
          (when (>= (count parts) 2)
            (let [class-name (name/from-string (nth parts 0))
                  inst-name (name/from-string (nth parts 1))
                  priority (if (>= (count parts) 3)
                             (try (Long/parseLong (nth parts 2)) (catch Exception _ 1000))
                             1000)]
              (swap! idx update class-name
                     (fnil conj [])
                     {:name inst-name :priority priority}))))))
    ;; Sort by priority (lower = tried first)
    (into {} (map (fn [[k vs]]
                    [k (sort-by :priority vs)])
                  @idx))))

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
    (letfn [(go [p t]
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
                      :mdata (go (e/mdata-expr p) (e/mdata-expr t))
                      (reset! ok false))

                    :else (reset! ok false))))]
      (go pattern target))
    (when @ok @subst)))

;; ============================================================
;; Synthesis engine
;; ============================================================

(defn- whnf [st expr]
  (#'tc/cached-whnf st expr))

(declare synthesize*)

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
                                       (when-not (try (tc/is-def-eq st r g) (catch Exception _ false))
                                         (reset! ok false)))))
                                 (when @ok @s))))]
        ;; Try to fill all arguments
          (let [filled-args
                (reduce
                 (fn [acc {:keys [fvar-id fvar type info]}]
                   (when acc
                     (if-let [val (get subst fvar-id)]
                     ;; Solved by structural matching
                       (conj acc val)
                     ;; Not in subst — try other strategies
                       (case info
                         :inst-implicit
                       ;; Substitute known values into the type first
                         (let [resolved-type (reduce (fn [ty [fid val]]
                                                       (e/instantiate1 (e/abstract1 ty fid) val))
                                                     type subst)]
                           (if-let [inst (synthesize* st env index resolved-type (inc depth))]
                             (conj acc inst)
                             nil))

                         (:implicit :strict-implicit)
                       ;; Implicit arg not determined by structural match.
                       ;; This can happen if the arg appears only in other args' types.
                       ;; Try: look at other solved args to determine this one.
                         nil

                       ;; :default — explicit arg, can't infer
                         nil))))
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
            ;; Common coercion patterns: {Super}.to{Class}
            ;; These are tried if the class has known superclasses
          ))]
    (keep (fn [n]
            (let [nm (name/from-string n)]
              (when (env/lookup env nm)
                {:name nm :arity 0})))
          candidate-names)))

(defn synthesize*
  "Synthesis with depth limit and backtracking.
   Uses the pre-built index when available, falls back to on-demand
   candidate discovery for PSS environments."
  [st env index goal-type depth]
  (when-not (> depth config/*max-synth-depth*)  ;; configurable depth limit
  ;; Get the goal's head class name (try raw, then WHNF)
    (let [head-info (or (let [[h _] (e/get-app-fn-args goal-type)]
                          (when (e/const? h) (e/const-name h)))
                        (let [w (whnf st goal-type)
                              [h _] (e/get-app-fn-args w)]
                          (when (e/const? h) (e/const-name h))))]
      (when head-info
        (let [;; Try pre-built index first, then on-demand discovery
              candidates (let [idx-cands (get-instances index head-info)]
                           (if (seq idx-cands)
                             idx-cands
                             (discover-candidates env head-info goal-type)))
            ;; Try candidates from index/discovery
            ;; Limit candidates to prevent combinatorial explosion
            ;; (some classes have 300+ instances in Mathlib)
              from-candidates (some (fn [candidate]
                                      (try-candidate st env index candidate goal-type depth))
                                    (take config/*max-candidates* candidates))]
          (or from-candidates
            ;; Fallback: name-based resolution with derivation chains (from ansatz.core)
              (try
                (let [resolve-fn (requiring-resolve 'ansatz.core/resolve-basic-instance)
                      [_ args] (e/get-app-fn-args goal-type)
                      type-arg (first args)
                      [th _] (when type-arg (e/get-app-fn-args type-arg))
                      class-str (name/->string head-info)
                      type-str (when (e/const? th) (name/->string (e/const-name th)))]
                  (when type-str (resolve-fn env class-str type-str type-arg)))
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
  "Convenience: resolve a Decidable instance for a proposition.
   Builds the instance index on the fly."
  [env prop]
  (let [index (build-instance-index env)
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
