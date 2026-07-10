;; Tactic layer — search infrastructure for proof exploration.

(ns ansatz.tactic.search
  "Search infrastructure for automated and semi-automated proof construction.
   Implements the heuristic plugin interface from the research design:
   any function (proof-state → [{:ps proof-state :weight double}]) can serve
   as a search heuristic.

   Supports:
   - Breadth-first and best-first search over tactic applications
   - Sequential Monte Carlo (SMC) resampling over proof branches
   - Tactic enumeration for automated search
   - Trace collection for strategy learning"
  (:require [ansatz.tactic.proof :as proof]
            [ansatz.tactic.basic :as basic]
            [ansatz.tactic.extract :as extract]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.name :as name]
            [clojure.set :as set]))

;; ============================================================
;; Policy-search actions and state summaries
;; ============================================================

(defn goal-signature
  "Stable, JSON/EDN-friendly summary of a goal for dedupe/training data."
  [goal]
  (when goal
    {:id (:id goal)
     :type (e/->string (:type goal))
     :hypotheses
     (->> (:lctx goal)
          (filter (fn [[_ d]] (= :local (:tag d))))
          (sort-by first)
          (mapv (fn [[id d]]
                  {:id id
                   :name (:name d)
                   :type (e/->string (:type d))})))}))

(defn state-summary
  "Compact proof-state summary. This is the record shape we can later persist
   into Datahike or NDJSON without carrying full Expr objects."
  [ps]
  {:solved? (proof/solved? ps)
   :open-goals (count (:goals ps))
   :weight (:weight ps)
   :goals (mapv goal-signature (proof/goals ps))})

(defn state-key
  "Stable key for duplicate-state pruning. We intentionally ignore mvar ids so
   equivalent frontier states reached by different generated ids can collapse."
  [ps]
  (pr-str (mapv (fn [g]
                  {:type (:type g)
                   :hypotheses (mapv #(select-keys % [:name :type])
                                      (:hypotheses g))})
                (:goals (state-summary ps)))))

(defn make-action
  "Construct a policy-search action.

   `apply-fn` is a pure transition `(fn [ps] ps')`. Options:
   - `:args`   printable/action arguments
   - `:prior`  model/search prior in (0, 1], defaults to 1.0
   - `:source` provenance keyword/string, e.g. :enumerate, :llm, :datatype"
  ([name apply-fn]
   (make-action name apply-fn nil))
  ([name apply-fn {:keys [args prior source kind] :or {prior 1.0 kind :tactic}}]
   {:kind kind
    :name name
    :args (vec (or args []))
    :prior (double prior)
    :source (or source :manual)
    :apply apply-fn}))

(defn action-summary
  "Drop function values from an action so it can be logged or stored."
  [action]
  (select-keys action [:kind :name :args :prior :source]))

(defn normalize-action
  "Accept both the old enumerate-tactics shape and the new action shape."
  [action]
  (cond
    (:apply action)
    (update action :prior #(double (or % (:weight action) 1.0)))

    (:tactic action)
    (make-action (:name action)
                 (:tactic action)
                 {:args (:args action)
                  :prior (or (:prior action) (:weight action) 1.0)
                  :source (or (:source action) :enumerate)
                  :kind (or (:kind action) :tactic)})

    (:fn action)
    (make-action (:name action)
                 (:fn action)
                 {:args (:args action)
                  :prior (or (:prior action) (:weight action) 1.0)
                  :source (or (:source action) :legacy)
                  :kind (or (:kind action) :tactic)})

    :else
    (throw (ex-info "Invalid search action" {:action action}))))

(defn- throwable-summary [^Throwable ex]
  {:class (.getName (class ex))
   :message (.getMessage ex)
   :data (when (instance? clojure.lang.ExceptionInfo ex) (ex-data ex))})

(defn default-reward
  "Small shaped reward for deterministic best-first search. This is deliberately
   simple: it rewards goal reduction and completion, and mildly penalizes depth."
  [before after _action]
  (+ (* 1.0 (- (:open-goals before) (:open-goals after)))
     (if (:solved? after) 10.0 0.0)
     -0.01))

(defn apply-action
  "Apply one normalized action to a search node, returning a transition record.
   Success records carry `:ps`; error records carry serializable diagnostics."
  ([node action]
   (apply-action node action nil))
  ([node action {:keys [reward-fn] :or {reward-fn default-reward}}]
   (let [action (normalize-action action)
         ps (:ps node)
         before (state-summary ps)
         action-log (action-summary action)]
     (try
       (let [ps' ((:apply action) ps)
             after (state-summary ps')
             prior (max 1.0e-12 (double (:prior action)))
             reward (double (reward-fn before after action))
             score (+ (double (:score node)) (Math/log prior) reward)]
         {:status :ok
          :from (:id node)
          :depth (inc (:depth node))
          :action action-log
          :before before
          :after after
          :reward reward
          :score score
          :ps (proof/adjust-weight ps' prior)})
       (catch Throwable ex
         {:status :error
          :from (:id node)
          :depth (inc (:depth node))
          :action action-log
          :before before
          :error (throwable-summary ex)
          :reward -1.0
          :score (+ (double (:score node)) -1.0)})))))

;; ============================================================
;; Tactic enumeration — generate candidate tactics for a goal
;; ============================================================

(defn enumerate-tactics
  "Given a proof state, enumerate applicable tactics for the current goal.
   Returns a seq of {:tactic fn :name keyword :args vector :weight double}.
   Weight represents prior probability of success."
  [ps]
  (when-let [goal (proof/current-goal ps)]
    (let [tactics (transient [])]
      ;; intro — if goal is forall
      (try
        (basic/intro ps)
        (conj! tactics {:tactic basic/intro :name :intro :args [] :weight 0.8})
        (catch Exception _))

      ;; assumption — if any hyp matches
      (try
        (basic/assumption ps)
        (conj! tactics {:tactic basic/assumption :name :assumption :args [] :weight 0.9})
        (catch Exception _))

      ;; rfl — if goal is Eq
      (try
        (basic/rfl ps)
        (conj! tactics {:tactic basic/rfl :name :rfl :args [] :weight 0.95})
        (catch Exception _))

      ;; constructor — if goal head is inductive
      (try
        (basic/constructor ps)
        (conj! tactics {:tactic basic/constructor :name :constructor :args [] :weight 0.5})
        (catch Exception _))

      ;; apply with each hypothesis that has a function type
      (doseq [[id decl] (:lctx goal)]
        (when (= :local (:tag decl))
          (try
            (basic/apply-tac ps (e/fvar id))
            (conj! tactics {:tactic #(basic/apply-tac % (e/fvar id))
                            :name :apply-hyp
                            :args [id]
                            :weight 0.3})
            (catch Exception _))))

      (persistent! tactics))))

(defn default-proposer
  "Default policy: reuse the existing tactic enumerator and normalize its output
   into action records."
  ([ps]
   (default-proposer ps nil nil))
  ([ps _node _opts]
   (mapv normalize-action (enumerate-tactics ps))))

(defn expr-constants
  "Return constant-name strings mentioned in `expr`."
  [expr]
  (letfn [(go [acc expr]
            (if-not expr
              acc
              (case (e/tag expr)
                :const (conj acc (name/->string (e/const-name expr)))
                :app (-> acc
                         (go (e/app-fn expr))
                         (go (e/app-arg expr)))
                :lam (-> acc
                         (go (e/lam-type expr))
                         (go (e/lam-body expr)))
                :forall (-> acc
                            (go (e/forall-type expr))
                            (go (e/forall-body expr)))
                :let (-> acc
                         (go (e/let-type expr))
                         (go (e/let-value expr))
                         (go (e/let-body expr)))
                :mdata (go acc (e/mdata-expr expr))
                :proj (-> acc
                          (conj (name/->string (e/proj-type-name expr)))
                          (go (e/proj-struct expr)))
                acc)))]
    (go #{} expr)))

(defn proof-state-symbols
  "Constant symbols visible in all current goals and local hypotheses."
  [ps]
  (reduce
   (fn [acc goal]
     (let [acc (set/union acc (expr-constants (:type goal)))]
       (reduce
        (fn [acc [_ decl]]
          (if (= :local (:tag decl))
            (set/union acc (expr-constants (:type decl)))
            acc))
        acc
        (:lctx goal))))
   #{}
   (proof/goals ps)))

(def premise-index-extension-key
  "Env extension key for cached premise facts. The extension stores raw
   declaration facts, not goal-specific instantiations."
  :tactic/premise-index)

(defn- unify-level-pattern
  "Unify a candidate level pattern against a concrete goal level. Candidate
   level params in `unknowns` are assigned in `subst`."
  [unknowns pattern target subst]
  (cond
    (and (lvl/param? pattern) (contains? unknowns (lvl/param-name pattern)))
    (let [param-name (lvl/param-name pattern)]
      (if-let [current (get subst param-name)]
        (when (lvl/level= current target) subst)
        (assoc subst param-name target)))

    (lvl/succ? pattern)
    (when (lvl/succ? target)
      (unify-level-pattern unknowns (lvl/succ-pred pattern) (lvl/succ-pred target) subst))

    (lvl/max? pattern)
    (when (lvl/max? target)
      (when-let [subst (unify-level-pattern unknowns (lvl/max-lhs pattern) (lvl/max-lhs target) subst)]
        (unify-level-pattern unknowns (lvl/max-rhs pattern) (lvl/max-rhs target) subst)))

    (lvl/imax? pattern)
    (when (lvl/imax? target)
      (when-let [subst (unify-level-pattern unknowns (lvl/imax-lhs pattern) (lvl/imax-lhs target) subst)]
        (unify-level-pattern unknowns (lvl/imax-rhs pattern) (lvl/imax-rhs target) subst)))

    :else
    (when (lvl/level= pattern target) subst)))

(defn- unify-level-vectors [unknowns patterns targets subst]
  (when (= (count patterns) (count targets))
    (reduce (fn [subst [pattern target]]
              (if subst
                (unify-level-pattern unknowns pattern target subst)
                (reduced nil)))
            subst
            (map vector patterns targets))))

(defn- collect-level-subst
  "Permissively traverse a candidate expression beside a goal expression and
   collect level-param assignments. Shape mismatches are ignored; conflicts in
   levels return nil."
  [unknowns pattern target subst]
  (cond
    (nil? subst) nil
    (or (nil? pattern) (nil? target)) subst

    (and (e/sort? pattern) (e/sort? target))
    (unify-level-pattern unknowns (e/sort-level pattern) (e/sort-level target) subst)

    (and (e/const? pattern) (e/const? target)
         (= (e/const-name pattern) (e/const-name target)))
    (unify-level-vectors unknowns (e/const-levels pattern) (e/const-levels target) subst)

    (and (e/app? pattern) (e/app? target))
    (when-let [subst (collect-level-subst unknowns (e/app-fn pattern) (e/app-fn target) subst)]
      (collect-level-subst unknowns (e/app-arg pattern) (e/app-arg target) subst))

    (and (e/lam? pattern) (e/lam? target))
    (when-let [subst (collect-level-subst unknowns (e/lam-type pattern) (e/lam-type target) subst)]
      (collect-level-subst unknowns (e/lam-body pattern) (e/lam-body target) subst))

    (and (e/forall? pattern) (e/forall? target))
    (when-let [subst (collect-level-subst unknowns (e/forall-type pattern) (e/forall-type target) subst)]
      (collect-level-subst unknowns (e/forall-body pattern) (e/forall-body target) subst))

    (and (e/let? pattern) (e/let? target))
    (when-let [subst (collect-level-subst unknowns (e/let-type pattern) (e/let-type target) subst)]
      (when-let [subst (collect-level-subst unknowns (e/let-value pattern) (e/let-value target) subst)]
        (collect-level-subst unknowns (e/let-body pattern) (e/let-body target) subst)))

    (e/mdata? pattern)
    (collect-level-subst unknowns (e/mdata-expr pattern) target subst)

    (e/mdata? target)
    (collect-level-subst unknowns pattern (e/mdata-expr target) subst)

    (and (e/proj? pattern) (e/proj? target)
         (= (e/proj-type-name pattern) (e/proj-type-name target)))
    (collect-level-subst unknowns (e/proj-struct pattern) (e/proj-struct target) subst)

    :else subst))

(defn- forall-conclusion [expr]
  (loop [expr expr]
    (if (e/forall? expr)
      (recur (e/forall-body expr))
      expr)))

(defn premise-index-entry
  "Extract reusable premise facts from a ConstantInfo. Goal-specific universe
   instantiation is deliberately done later."
  [ci]
  (let [ty (env/ci-type ci)
        conclusion (forall-conclusion ty)]
    {:name (env/ci-name ci)
     :name-string (name/->string (env/ci-name ci))
     :tag (env/ci-tag ci)
     :level-params (env/ci-level-params ci)
     :type ty
     :type-string (e/->string ty)
     :symbols (expr-constants ty)
     :conclusion-symbols (expr-constants conclusion)}))

(defn build-premise-index
  "Build a reusable premise index from an env.

   Options:
   - `:premise-tags` declaration tags to include
   - `:premise-scan-limit` maximum env constants scanned"
  ([env]
   (build-premise-index env nil))
  ([env {:keys [premise-tags premise-scan-limit]
         :or {premise-tags #{:axiom :thm :def :opaque}
              premise-scan-limit 1024}}]
   {:kind :ansatz.tactic/premise-index
    :premise-tags premise-tags
    :premise-scan-limit premise-scan-limit
    :entries
    (->> (env/all-constants env)
         (filter #(contains? premise-tags (env/ci-tag %)))
         (take premise-scan-limit)
         (mapv premise-index-entry))}))

(defn install-premise-index
  "Return a new env carrying a cached premise index extension."
  ([env]
   (install-premise-index env nil))
  ([env opts]
   (env/with-extension env premise-index-extension-key
                       (build-premise-index env opts))))

(defn index-proof-state
  "Return a proof state whose env carries a cached premise index."
  ([ps]
   (index-proof-state ps nil))
  ([ps opts]
   (update ps :env install-premise-index opts)))

(defn- premise-index-from [ps {:keys [premise-index] :as opts}]
  (or premise-index
      (env/get-extension (:env ps) premise-index-extension-key)
      (build-premise-index (:env ps) opts)))

(defn- infer-candidate-levels
  "Infer concrete universe levels for a candidate constant from the current goal.
   Returns nil when any level parameter remains unconstrained."
  [ps entry]
  (let [params (:level-params entry)]
    (if (empty? params)
      []
      (when-let [goal (proof/current-goal ps)]
        (let [unknowns (set params)
              goal-type (:type goal)
              candidate-type (:type entry)
              conclusion (forall-conclusion candidate-type)
              attempts [(collect-level-subst unknowns candidate-type goal-type {})
                        (collect-level-subst unknowns conclusion goal-type {})]
              subst (some (fn [subst]
                            (when (and subst (every? #(contains? subst %) params))
                              subst))
                          attempts)]
          (when subst
            (mapv #(get subst %) params)))))))

(defn- constant-term [entry levels]
  (e/const' (:name entry) levels))

(defn premise-candidate
  "Instantiate one premise-index entry for the current goal, or nil when it is not
   usable by this first conservative premise proposer."
  [ps entry]
  (when-let [levels (infer-candidate-levels ps entry)]
    (let [level-subst (zipmap (:level-params entry) levels)
          ty (e/instantiate-level-params (:type entry) level-subst)
          term (constant-term entry levels)]
      {:name (:name-string entry)
       :tag (:tag entry)
       :levels levels
       :type ty
       :type-string (e/->string ty)
       :symbols (expr-constants ty)
       :term term})))

(defn premise-candidates
  "Extract premise candidates from the current env, keeping only constants whose
   universe levels are absent or inferable from the current goal."
  [ps {:keys [premise-tags] :as opts
       :or {premise-tags #{:axiom :thm :def :opaque}}}]
  (->> (:entries (premise-index-from ps opts))
       (filter #(contains? premise-tags (:tag %)))
       (keep #(premise-candidate ps %))
       vec))

(defn score-premise
  "Heuristic premise score. Exact target-type match dominates, then symbol
   overlap with current goals/hypotheses."
  [ps candidate]
  (let [goal (proof/current-goal ps)
        goal-type-string (when goal (e/->string (:type goal)))
        goal-symbols (proof-state-symbols ps)
        overlap (set/intersection goal-symbols (:symbols candidate))
        exact? (= goal-type-string (:type-string candidate))]
    (+ (if exact? 10.0 0.0)
       (* 1.0 (count overlap))
       ;; Deterministic tie-breakers that also mildly prefer smaller local facts.
       (/ 1.0 (+ 1 (count (:symbols candidate))))
       (/ 1.0 (+ 1 (count (:name candidate)))))))

(defn ranked-premise-candidates
  "Return premise candidates sorted by descending heuristic score."
  ([ps]
   (ranked-premise-candidates ps nil))
  ([ps opts]
   (->> (premise-candidates ps opts)
        (map #(assoc % :score (score-premise ps %)))
        (sort-by (juxt (comp - double :score) :name))
        vec)))

(defn theorem-proposer
  "Propose actions from constants already present in the environment.

   Options:
   - `:premise-limit` maximum premise candidates returned, default 32
   - `:premise-scan-limit` maximum constants scanned, default 1024
   - `:premise-tags` declaration tags to consider, default #{:axiom :thm :def :opaque}
   - `:premise-prior` base prior, default 0.2

   This intentionally proposes both `exact` and `apply`; the ordinary tactic
   machinery and kernel verification decide which branches survive."
  ([ps]
   (theorem-proposer ps nil nil))
  ([ps _node {:keys [premise-limit premise-tags premise-prior premise-scan-limit premise-index]
              :as opts
              :or {premise-limit 32
                   premise-tags #{:axiom :thm :def :opaque}
                   premise-prior 0.2
                   premise-scan-limit 1024}}]
   (let [goal (proof/current-goal ps)]
     (if-not goal
       []
       (->> (ranked-premise-candidates ps (assoc opts
                                                 :premise-tags premise-tags
                                                 :premise-scan-limit premise-scan-limit
                                                 :premise-index premise-index))
            (take premise-limit)
            (mapcat (fn [{:keys [name term score]}]
                      (let [prior (min 0.95 (* premise-prior (max 1.0 score)))]
                        [(make-action :exact-const
                                      #(basic/exact % term)
                                      {:args [name]
                                       :prior prior
                                       :source :env})
                         (make-action :apply-const
                                      #(basic/apply-tac % term)
                                      {:args [name]
                                       :prior (* 0.75 prior)
                                       :source :env})])))
            vec)))))

(defn- call-proposer [proposer ps node opts]
  (proposer ps node opts))

(defn propose-actions
  "Run one or more action proposers. A proposer is `(fn [ps node opts] actions)`.
   Proposal failures should be represented as actions that fail during
   `apply-action`, so they become transition records."
  ([ps]
   (propose-actions ps nil nil))
  ([ps node {:keys [proposer proposers] :as opts}]
   (let [proposers (or proposers (when proposer [proposer]) [default-proposer])]
     (->> proposers
          (mapcat #(call-proposer % ps node opts))
          (mapv normalize-action)))))

;; ============================================================
;; Search strategies
;; ============================================================

(defn try-tactic
  "Try applying a tactic function, returning the new ps or nil on failure."
  [ps tactic-fn & args]
  (try
    (apply tactic-fn ps args)
    (catch Exception _ nil)))

(defn auto-solve
  "Try to automatically solve the current goal using simple tactics.
   Returns solved ps or nil."
  [ps max-depth]
  (when (and (pos? max-depth) (not (proof/solved? ps)))
    (let [candidates (enumerate-tactics ps)]
      (some (fn [{:keys [tactic]}]
              (when-let [ps' (try (tactic ps) (catch Exception _ nil))]
                (if (proof/solved? ps')
                  ps'
                  (auto-solve ps' (dec max-depth)))))
            ;; Sort by weight descending (best first)
            (sort-by :weight > candidates)))))

;; ============================================================
;; Branching and SMC
;; ============================================================

(defn fork
  "Fork a proof state into multiple branches by applying different tactics.
   tactics is a seq of {:name keyword :fn/:tactic/:apply (fn [ps] → ps')}.
   Returns a seq of {:name keyword :ps proof-state :weight double} for
   successful branches."
  [ps tactics]
  (->> tactics
       (keep (fn [{:keys [name weight] :or {weight 1.0} :as tactic}]
               (let [f (or (:fn tactic) (:tactic tactic) (:apply tactic))]
                 (when-let [ps' (try (f ps) (catch Exception _ nil))]
                   {:name name
                    :ps (proof/adjust-weight ps' weight)
                    :weight (* (:weight ps') weight)}))))
       vec))

(defn resample
  "SMC resampling: given a seq of {:ps :weight} particles, resample
   proportional to weight. Returns n particles (with replacement)."
  [particles n]
  (when (seq particles)
    (let [total-weight (reduce + (map :weight particles))
          normalized (map #(update % :weight / total-weight) particles)]
      (loop [result [] remaining n]
        (if (zero? remaining)
          result
          (let [r (rand)
                selected (loop [ps normalized cum 0.0]
                           (let [p (first ps)
                                 cum' (+ cum (:weight p))]
                             (if (or (>= cum' r) (nil? (next ps)))
                               p
                               (recur (next ps) cum'))))]
            (recur (conj result (proof/set-weight (:ps selected) 1.0))
                   (dec remaining))))))))

(defn beam-search
  "Beam search over tactic applications.
   At each step, expand the best beam-width states, keeping the top ones.
   Returns the first solved state, or nil after max-steps."
  [ps beam-width max-steps]
  (loop [beam [{:ps ps :weight 1.0}]
         step 0]
    (when (< step max-steps)
      ;; Check if any state is solved
      (if-let [solved (first (filter #(proof/solved? (:ps %)) beam))]
        (:ps solved)
        ;; Expand each state
        (let [expanded (mapcat
                        (fn [{:keys [ps weight]}]
                          (let [candidates (enumerate-tactics ps)]
                            (keep (fn [{:keys [tactic weight tac-weight] :as c}]
                                    (when-let [ps' (try (tactic ps) (catch Exception _ nil))]
                                      {:ps ps'
                                       :weight (* weight (or (:weight c) 0.5))}))
                                  candidates)))
                        beam)
              ;; Keep top beam-width by weight
              top (take beam-width (sort-by :weight > expanded))]
          (if (empty? top)
            nil
            (recur top (inc step))))))))

;; ============================================================
;; Deterministic policy search
;; ============================================================

(defn- root-node [ps]
  {:id 0
   :ps ps
   :depth 0
   :score 0.0
   :path []
   :state-key (state-key ps)})

(defn- pop-best [frontier]
  (let [ordered (sort-by (juxt (fn [node] (- (double (:score node)))) :id) frontier)]
    [(first ordered) (vec (rest ordered))]))

(defn- trim-frontier [frontier beam-width]
  (let [ordered (sort-by (juxt (fn [node] (- (double (:score node)))) :id) frontier)]
    (vec (if beam-width (take beam-width ordered) ordered))))

(defn- verify-node [node verify?]
  (when verify?
    (try
      {:ok? true
       :proof (extract/verify (:ps node))}
      (catch Throwable ex
        {:ok? false
         :error (throwable-summary ex)}))))

(defn- terminal-result [status node nodes transitions expanded verify?]
  (let [verification (verify-node node verify?)]
    (if (and verify? (not (:ok? verification)))
      {:status :invalid
       :node node
       :ps (:ps node)
       :verification verification
       :nodes nodes
       :transitions transitions
       :expanded expanded}
      (cond-> {:status status
               :node node
               :ps (:ps node)
               :proof (:proof verification)
               :path (:path node)
               :summary (state-summary (:ps node))
               :nodes nodes
               :transitions transitions
               :expanded expanded}
        verification (assoc :verification verification)))))

(defn best-first-search
  "Policy-guided deterministic proof search over persistent proof states.

   Options:
   - `:proposer`/`:proposers` action proposer(s); defaults to `default-proposer`
   - `:reward-fn` shaped reward `(fn [before after action] double)`
   - `:max-steps` max expanded nodes, default 100
   - `:max-depth` max action depth, default 20
   - `:beam-width` optional frontier cap after each expansion
   - `:dedupe?` prune duplicate goal states, default true
   - `:verify?` run authoritative extraction/kernel verification on success, default true

   Returns a map with `:status` one of `:solved`, `:invalid`,
   `:exhausted`, or `:step-limit`, plus `:transitions` suitable for
   NDJSON/Datahike persistence."
  ([ps]
   (best-first-search ps nil))
  ([ps {:keys [max-steps max-depth beam-width dedupe? verify?] :as opts
        :or {max-steps 100
             max-depth 20
             dedupe? true
             verify? true}}]
   (let [root (root-node ps)]
     (loop [frontier [root]
            seen #{(:state-key root)}
            nodes {0 (dissoc root :ps)}
            transitions []
            next-id 1
            expanded 0]
       (cond
         (empty? frontier)
         {:status :exhausted
          :nodes nodes
          :transitions transitions
          :expanded expanded}

         (>= expanded max-steps)
         {:status :step-limit
          :frontier (mapv #(dissoc % :ps) frontier)
          :nodes nodes
          :transitions transitions
          :expanded expanded}

         :else
         (let [[node frontier] (pop-best frontier)]
           (cond
             (proof/solved? (:ps node))
             (terminal-result :solved node nodes transitions expanded verify?)

             (>= (:depth node) max-depth)
             (recur frontier seen nodes transitions next-id (inc expanded))

             :else
             (let [attempts (mapv #(apply-action node % opts)
                                  (propose-actions (:ps node) node opts))
                   [children seen nodes transitions next-id]
                   (reduce
                    (fn [[children seen nodes transitions next-id] attempt]
                      (if (= :ok (:status attempt))
                        (let [k (state-key (:ps attempt))
                              duplicate? (and dedupe? (contains? seen k))
                              transition (cond-> (dissoc attempt :ps)
                                           duplicate? (assoc :status :duplicate))]
                          (if duplicate?
                            [children seen nodes (conj transitions transition) next-id]
                            (let [child {:id next-id
                                         :ps (:ps attempt)
                                         :depth (:depth attempt)
                                         :score (:score attempt)
                                         :parent (:id node)
                                         :action (:action attempt)
                                         :path (conj (:path node) (:action attempt))
                                         :state-key k}
                                  child-log (dissoc child :ps)]
                              [(conj children child)
                               (conj seen k)
                               (assoc nodes next-id child-log)
                               (conj transitions (assoc transition :to next-id))
                               (inc next-id)])))
                        [children
                         seen
                         nodes
                         (conj transitions (dissoc attempt :ps))
                         next-id]))
                    [[] seen nodes transitions next-id]
                    attempts)
                   frontier (trim-frontier (into frontier children) beam-width)]
               (recur frontier seen nodes transitions next-id (inc expanded))))))))))

;; ============================================================
;; Trace analysis
;; ============================================================

(defn trace-summary
  "Summarize the tactic trace from a proof state."
  [ps]
  {:tactics (mapv :tactic (:trace ps))
   :num-steps (count (:trace ps))
   :solved (proof/solved? ps)
   :open-goals (count (:goals ps))
   :weight (:weight ps)})
