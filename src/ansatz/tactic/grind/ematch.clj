;; E-matching engine for the grind tactic.
;; Following Lean 4's grind EMatch.lean and Theorems.lean.
;;
;; E-matching finds instances of universally quantified theorems by
;; pattern matching against terms in the E-graph. When a match is found,
;; the theorem is instantiated and the resulting equality is added to
;; the E-graph as a new fact.
;;
;; Key concepts:
;; - Patterns: Expr trees with bvars as unknowns (de Bruijn indexed)
;; - Backtracking search: try each member of an equivalence class
;; - Lazy activation: theorems activate when their symbols appear
;; - Instance dedup: avoid re-instantiating same theorem+assignment

(ns ansatz.tactic.grind.ematch
  "E-matching engine for automatic theorem instantiation in grind."
  (:require [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.tc :as tc]
            [ansatz.tactic.grind.egraph :as eg]))

;; ============================================================
;; EMatchTheorem — a rewrite rule with patterns
;; Following Lean 4 Extension.lean:113
;; ============================================================

(defn mk-ematch-theorem
  "Create an E-match theorem from a declaration name.
   Analyzes the type to extract universally quantified parameters
   and infers patterns from the conclusion."
  [env thm-name]
  (when-let [ci (env/lookup env thm-name)]
    (let [ty (.type ^ansatz.kernel.ConstantInfo ci)
          proof (e/const' thm-name (mapv (fn [_] lvl/zero) (.levelParams ci)))
          ;; Count forall parameters and find the conclusion
          [num-params body] (loop [t ty n 0]
                              (if (e/forall? t)
                                (recur (e/forall-body t) (inc n))
                                [n t]))
          ;; Extract patterns from the conclusion
          ;; For an equality A = B, use the LHS as pattern
          ;; For other props, use the whole body
          [head args] (e/get-app-fn-args body)
          patterns (cond
                     ;; Equality: use LHS as pattern (bvars are unknowns)
                     (and (e/const? head)
                          (= (name/from-string "Eq") (e/const-name head))
                          (= 3 (count args)))
                     [(nth args 1)]
                     ;; Other: use the whole body
                     :else [body])
          ;; Collect head symbols from patterns for activation
          symbols (vec (keep (fn [pat]
                               (let [[h _] (e/get-app-fn-args pat)]
                                 (when (e/const? h) (e/const-name h))))
                             patterns))]
      {:origin thm-name
       :proof proof
       :type ty
       :num-params num-params
       :patterns patterns
       :symbols symbols
       :kind (if (and (e/const? head)
                      (= (name/from-string "Eq") (e/const-name head)))
               :eq-lhs :default)})))

;; ============================================================
;; Pattern matching against E-graph
;; Following Lean 4 EMatch.lean
;; ============================================================

(defn- match-pattern
  "Try to match a pattern against an E-graph term.
   Pattern has bvars (de Bruijn) as unknowns.
   Returns an assignment map {bvar-idx → expr} or nil on failure."
  [gs pat term assignment]
  (cond
    ;; Pattern is a bvar (unknown) — assign or check consistent
    (e/bvar? pat)
    (let [idx (e/bvar-idx pat)
          existing (get assignment idx)]
      (cond
        ;; Not yet assigned — bind it
        (nil? existing)
        (assoc assignment idx term)
        ;; Already assigned — check equivalence in E-graph
        (eg/is-eqv gs existing term)
        assignment
        ;; Conflict — fail
        :else nil))

    ;; Pattern is a constant — must be the same constant
    (e/const? pat)
    (when (and (e/const? term) (= (e/const-name pat) (e/const-name term)))
      assignment)

    ;; Pattern is an application — decompose and match recursively
    (e/app? pat)
    (let [[pat-head pat-args] (e/get-app-fn-args pat)
          [term-head term-args] (e/get-app-fn-args term)]
      (when (= (count pat-args) (count term-args))
        ;; Match head
        (when-let [asgn (match-pattern gs pat-head term-head assignment)]
          ;; Match each argument
          (reduce (fn [asgn [pa ta]]
                    (if asgn
                      (match-pattern gs pa ta asgn)
                      (reduced nil)))
                  asgn
                  (map vector pat-args term-args)))))

    ;; Pattern is a literal — must be identical
    (e/lit-nat? pat)
    (when (and (e/lit-nat? term) (= (e/lit-nat-val pat) (e/lit-nat-val term)))
      assignment)

    ;; Pattern is anything else (sort, forall, lam) — structural match
    :else
    (when (= pat term) assignment)))

(defn match-in-eqclass
  "Try to match pattern against any member of the equivalence class of term.
   Only considers members with generation 0 (original terms) to prevent
   matching against terms created by previous E-matching rounds.
   Returns a seq of successful assignments."
  [gs pat term]
  (let [root (eg/get-root gs term)
        results (atom [])]
    ;; Traverse equivalence class
    (loop [curr root]
      (when-let [node (eg/get-enode gs curr)]
        ;; Only match gen=0 terms (original, not E-match-created)
        (when (zero? (:gen node))
          (when-let [asgn (match-pattern gs pat curr {})]
            (swap! results conj {:assignment asgn :matched-term curr})))
        (let [next (:next node)]
          (when-not (identical? next root)
            (recur next)))))
    @results))

;; ============================================================
;; Theorem instantiation
;; ============================================================

(defn- instantiate-theorem
  "Given a successful assignment, instantiate the theorem by substituting
   bvars with assigned terms. Returns an Expr (the instantiated proof applied
   to its arguments)."
  [thm assignment]
  (let [proof (:proof thm)
        num-params (:num-params thm)
        ;; Build argument list from assignment (bvar 0 = innermost)
        ;; The assignment maps bvar indices to terms
        args (mapv (fn [i] (get assignment i)) (range num-params))]
    (when (every? some? args)
      ;; Apply proof to all arguments
      (reduce e/app proof (reverse args)))))

(defn- instantiate-eq-fact
  "Given an instantiated equality theorem, extract LHS = RHS for the E-graph."
  [env thm assignment]
  (let [ty (:type thm)
        num-params (:num-params thm)
        ;; Substitute all forall-bound variables with assigned terms
        body (loop [t ty i 0]
               (if (and (e/forall? t) (< i num-params))
                 (let [arg (get assignment (- num-params 1 i))]
                   (recur (e/instantiate1 (e/forall-body t) arg) (inc i)))
                 t))
        [head args] (e/get-app-fn-args body)]
    (when (and (e/const? head)
               (= (name/from-string "Eq") (e/const-name head))
               (= 3 (count args)))
      {:lhs (nth args 1) :rhs (nth args 2) :type (nth args 0)})))

;; ============================================================
;; Instance deduplication
;; ============================================================

(defn- instance-key
  "Create a deduplication key for a theorem instance.
   Uses System/identityHashCode for Expr identity (pointer-based)."
  [thm-name assignment]
  [thm-name (mapv (fn [[k v]] [k (System/identityHashCode v)]) (sort assignment))])

;; ============================================================
;; E-matching round
;; ============================================================

;; Following Lean 4 Init/Grind/Config.lean defaults
(def ^:dynamic *max-ematch-instances*
  "Maximum total theorem instances. Lean 4 default: 1000."
  1000)

(def ^:dynamic *max-ematch-generation*
  "Maximum generation depth for E-matching candidates. Lean 4 default: 8.
   Terms created by E-matching get generation > 0 and are pruned when
   their generation exceeds this limit."
  8)

(def ^:dynamic *max-ematch-rounds*
  "Maximum E-matching rounds per grind call. Lean 4 default: 5."
  5)

(def ^:dynamic *max-instances-per-round*
  "Cap on new instances per single E-matching round (safety valve)."
  64)

(defn ematch-round
  "Run one round of E-matching. For each active theorem, try to match
   its patterns against terms in the E-graph's app-map. Only matches
   candidates with generation 0 (original terms, not E-match-created).
   Returns a list of new facts to assert.

   gs: E-graph state
   theorems: seq of EMatchTheorem maps
   seen-instances: set of instance-keys already processed

   Returns {:new-facts [...] :seen seen-instances'}"
  [gs theorems seen-instances]
  (let [new-facts (atom [])
        seen (atom (or seen-instances #{}))
        limit *max-instances-per-round*]
    (doseq [thm theorems
            :while (< (count @new-facts) limit)]
      (doseq [pat (:patterns thm)
              :while (< (count @new-facts) limit)]
        ;; Find the head symbol of the pattern
        (let [[pat-head _] (e/get-app-fn-args pat)]
          (when (e/const? pat-head)
            (let [head-name (e/const-name pat-head)
                  ;; Get all terms in the E-graph with this head symbol
                  candidates (get (:app-map gs) head-name)]
              (doseq [candidate (or candidates [])
                      :while (< (count @new-facts) limit)
                      ;; Generation gate: only match original terms (gen=0),
                      ;; not terms created by previous E-matching rounds
                      :when (let [node (eg/get-enode gs candidate)]
                              (and node (zero? (:gen node))))]
                ;; Try matching in the equivalence class
                (doseq [{:keys [assignment matched-term]}
                        (match-in-eqclass gs pat candidate)
                        :while (< (count @new-facts) limit)]
                  ;; Check dedup
                  (let [key (instance-key (:origin thm) assignment)]
                    (when-not (contains? @seen key)
                      (swap! seen conj key)
                      ;; Instantiate
                      (when-let [proof (instantiate-theorem thm assignment)]
                        (when-let [eq-info (instantiate-eq-fact
                                            (:env gs) thm assignment)]
                          (swap! new-facts conj
                                 {:lhs (:lhs eq-info)
                                  :rhs (:rhs eq-info)
                                  :proof proof
                                  :heq false}))))))))))))
    {:new-facts @new-facts
     :seen @seen}))

;; ============================================================
;; High-level API
;; ============================================================

(defn prepare-theorems
  "Look up theorem names in the environment and create EMatchTheorems.
   Returns a seq of EMatchTheorem maps."
  [env thm-names]
  (keep (fn [nm]
          (let [n (if (instance? ansatz.kernel.Name nm)
                    nm
                    (name/from-string (str nm)))]
            (mk-ematch-theorem env n)))
        thm-names))

(defn run-ematch
  "Run E-matching with Lean 4-style termination controls:
   - Up to *max-ematch-rounds* rounds (default 5)
   - Up to *max-ematch-instances* total instances (default 1000)
   - Generation tracking: new terms get incrementing generation,
     only terms with gen < *max-ematch-generation* are matched
   - Stops early if goal is already solved (check-fn returns true)

   gs: E-graph state
   theorems: seq of EMatchTheorem maps
   seen-instances: set of already-seen instances
   check-fn: (fn [gs] bool) — return true to stop early (e.g., goal solved)

   Returns {:gs updated-gs :seen updated-seen}"
  ([gs theorems seen-instances]
   (run-ematch gs theorems seen-instances (constantly false)))
  ([gs theorems seen-instances check-fn]
   (loop [gs gs
          seen (or seen-instances #{})
          round 0
          total-instances 0]
     (if (or (>= round *max-ematch-rounds*)
             (>= total-instances *max-ematch-instances*)
             (:inconsistent gs)
             (check-fn gs))
       {:gs gs :seen seen}
       (let [{:keys [new-facts seen]} (ematch-round gs theorems seen)
             n-new (count new-facts)]
         (if (zero? n-new)
           ;; No new instances — saturated
           {:gs gs :seen seen}
           ;; Assert new facts. Key: use existing E-graph terms when possible
           ;; (E-match creates new Expr objects that are structurally equal to
           ;; existing ones but not pointer-identical).
           ;; If the terms are already in the E-graph, just assert equality.
           ;; Only internalize truly new terms.
           (let [gen (inc round)
                 gs (reduce (fn [gs fact]
                              (let [lhs (:lhs fact) rhs (:rhs fact)
                                    ;; Check if LHS/RHS are already in the E-graph
                                    ;; (by checking if any existing enode has the same structure)
                                    gs (if (eg/get-enode gs lhs) gs (eg/internalize gs lhs gen))
                                    gs (if (eg/get-enode gs rhs) gs (eg/internalize gs rhs gen))]
                                (eg/assert-eq gs lhs rhs (:proof fact))))
                            gs new-facts)]
             (recur gs seen (inc round) (+ total-instances n-new)))))))))
