;; Copyright (c) 2026 Simmis GmbH. All rights reserved.
;; Tactic layer — general typeclass instance resolution.

(ns cic.tactic.instance
  "General typeclass instance resolution by searching the environment.

   Instances are CIC constants whose return type (after stripping foralls) is an
   application of a class. Resolution works by:
   1. Building an index: class-name → [candidate instances]
   2. For a goal like `Decidable (Eq Nat 0 0)`:
      a. Find candidates for `Decidable`
      b. Try each: instantiate its level params, peel its foralls,
         structurally match result with goal
      c. Recursively resolve instance-implicit arguments
      d. Return the first that succeeds

   Uses structural matching (NOT is-def-eq) to avoid proof irrelevance issues."
  (:require [cic.kernel.expr :as e]
            [cic.kernel.env :as env]
            [cic.kernel.name :as name]
            [cic.kernel.level :as lvl]
            [cic.kernel.tc :as tc]
            [cic.kernel.reduce :as red])
  (:import [cic.kernel ConstantInfo Env]))

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
  "Scan the environment and build a map: class-name → [{:name :arity} ...].
   Sorted by arity (fewer foralls = simpler = tried first)."
  [^Env env]
  (let [idx (atom {})]
    (doseq [^ConstantInfo ci (env/all-constants env)]
      (when (or (.isDef ci) (.isThm ci) (.isCtor ci))
        (when-let [[head-name arity] (return-type-head (.type ci))]
          (swap! idx update head-name
                 (fnil conj [])
                 {:name (.name ci) :arity arity}))))
    ;; Sort candidates: more specific (higher arity) first, but push
    ;; Classical.* to the very end (non-computational, matches everything).
    (into {} (map (fn [[k vs]]
                    [k (sort-by (fn [v]
                                  (let [s (str (:name v))]
                                    ;; Classical.* gets penalty, otherwise sort by -arity
                                    (if (.startsWith s "Classical.")
                                      [1 (- (:arity v))]
                                      [0 (- (:arity v))])))
                                vs)])
                  @idx))))

(defn get-instances
  "Get candidate instances for a class name from the index."
  [index class-name]
  (get index class-name []))

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
          result-type (loop [t ctype]
                        (if (e/forall? t)
                          (let [fv-id (swap! (:next-id st) inc)
                                fv (e/fvar fv-id)
                                info (e/forall-info t)
                                arg-type (e/forall-type t)]
                            (swap! fvar-ids conj fv-id)
                            (swap! arg-info conj {:fvar-id fv-id :fvar fv
                                                  :type arg-type :info info})
                            (recur (e/instantiate1 (e/forall-body t) fv)))
                          t))]
      ;; Structural match: result-type vs goal-type
      (when-let [subst (structural-match result-type goal-type @fvar-ids)]
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
              ;; Quick sanity check: type-check the result
              (try
                (let [inferred (tc/infer-type st term)]
                  (when (tc/is-def-eq st inferred goal-type)
                    term))
                (catch Exception _ nil)))))))
    (catch Exception _ nil)))

(defn- synthesize*
  "Internal synthesis with depth limit and backtracking."
  [st env index goal-type depth]
  (when (> depth 8) nil)
  ;; Get the goal's head class name (try raw, then WHNF)
  (let [head-info (or (let [[h _] (e/get-app-fn-args goal-type)]
                        (when (e/const? h) (e/const-name h)))
                      (let [w (whnf st goal-type)
                            [h _] (e/get-app-fn-args w)]
                        (when (e/const? h) (e/const-name h))))]
    (when head-info
      (let [candidates (get-instances index head-info)]
        (some (fn [candidate]
                (try-candidate st env index candidate goal-type depth))
              candidates)))))

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
