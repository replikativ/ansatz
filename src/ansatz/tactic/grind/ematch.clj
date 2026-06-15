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
       :level-params (vec (.levelParams ci))
       :patterns patterns
       :symbols symbols
       :kind (if (and (e/const? head)
                      (= (name/from-string "Eq") (e/const-name head)))
               :eq-lhs :default)})))

;; ============================================================
;; Pattern matching against E-graph
;; Following Lean 4 EMatch.lean
;; ============================================================

(defn- unify-level
  "Unify a pattern level `pl` (may mention theorem level-param Names in `unknowns`)
   against a concrete term level `tl`, accumulating into the level subst `lv`
   ({param-Name → Level}). Returns updated lv, or nil on conflict.
   Handles the level shapes our laws actually use: bare param, succ, max, imax,
   zero; anything else falls back to definitional level equality."
  [unknowns pl tl lv]
  (cond
    ;; Pattern is an unknown param — bind or check consistency
    (and (lvl/param? pl) (contains? unknowns (lvl/param-name pl)))
    (let [pn (lvl/param-name pl)
          cur (get lv pn)]
      (cond (nil? cur) (assoc lv pn tl)
            (lvl/level= cur tl) lv
            :else nil))
    ;; succ p  vs  succ t  → recurse
    (lvl/succ? pl)
    (when (lvl/succ? tl) (unify-level unknowns (lvl/succ-pred pl) (lvl/succ-pred tl) lv))
    ;; max / imax → recurse both sides (term must match shape)
    (lvl/max? pl)
    (when (lvl/max? tl)
      (some->> lv (unify-level unknowns (lvl/max-lhs pl) (lvl/max-lhs tl))
               (unify-level unknowns (lvl/max-rhs pl) (lvl/max-rhs tl))))
    (lvl/imax? pl)
    (when (lvl/imax? tl)
      (some->> lv (unify-level unknowns (lvl/imax-lhs pl) (lvl/imax-lhs tl))
               (unify-level unknowns (lvl/imax-rhs pl) (lvl/imax-rhs tl))))
    ;; No unknowns involved — require definitional level equality
    :else
    (when (lvl/level= pl tl) lv)))

(defn- unify-levels
  "Unify two equal-length level vectors, threading the level subst `lv`."
  [unknowns pls tls lv]
  (when (= (count pls) (count tls))
    (reduce (fn [lv [pl tl]]
              (if lv (unify-level unknowns pl tl lv) (reduced nil)))
            lv (map vector pls tls))))

(defn- match-pattern
  "Try to match a pattern against an E-graph term. Pattern has bvars (de Bruijn)
   as term unknowns and may mention theorem level-params (in `unknowns`) as level
   unknowns. Threads match state `m` = {:vars {bvar-idx → expr} :levels {param→lvl}}.
   `depth` = number of pattern binders opened so far (for fresh-fvar generation under
   binders). Returns updated `m` or nil on failure."
  ([gs unknowns pat term m] (match-pattern gs unknowns pat term m 0))
  ([gs unknowns pat term m depth]
   (cond
     ;; Pattern is a bvar (unknown) — assign or check consistent
     (e/bvar? pat)
     (let [idx (e/bvar-idx pat)
           existing (get (:vars m) idx)]
       (cond
         ;; Not yet assigned — bind it
         (nil? existing)
         (assoc-in m [:vars idx] term)
         ;; Already assigned — check equivalence in E-graph
         (eg/is-eqv gs existing term)
         m
         ;; Conflict — fail
         :else nil))

     ;; Pattern is a constant — same constant + unify universe levels
     (e/const? pat)
     (when (and (e/const? term) (= (e/const-name pat) (e/const-name term)))
       (when-let [lv (unify-levels unknowns (e/const-levels pat) (e/const-levels term)
                                   (:levels m))]
         (assoc m :levels lv)))

     ;; Pattern is an application — first try a HIGHER-ORDER (Miller) pattern, else decompose.
     (e/app? pat)
     (let [[pat-head pat-args] (e/get-app-fn-args pat)]
       (or
         ;; MILLER HIGHER-ORDER PATTERN: `?f x1 … xn` where `?f` is an UNASSIGNED metavar (bvar) and
         ;; x1…xn are DISTINCT opened-binder LOCALS (the fresh fvars introduced under λ/∀, tracked in
         ;; `:ftypes`). Unify by SYNTHESIZING the function: `?f := λ x1…xn. term[x1…xn abstracted]`.
         ;; This is what laws like `List.sum_map_mul_const` need — `map (λx. f x * c) xs` binds `f` to a
         ;; function applied to the bound `x`, which first-order matching cannot do (it would bind `f`
         ;; to a head symbol). Restricted to distinct bound locals (the Miller pattern fragment) so the
         ;; abstraction is well-defined and unique; the e-matcher is an untrusted oracle, so even a too-
         ;; liberal synthesis only yields a candidate that the downstream kernel proof check rejects.
        (when (and (e/bvar? pat-head)
                   (nil? (get (:vars m) (e/bvar-idx pat-head)))      ; ?f not yet assigned
                   (seq pat-args)
                   (every? e/fvar? pat-args)
                   (every? #(contains? (:ftypes m) (e/fvar-id %)) pat-args)  ; all are opened locals
                   (apply distinct? (map e/fvar-id pat-args)))
          (let [pairs (map (fn [a] [(e/fvar-id a) (get (:ftypes m) (e/fvar-id a))]) pat-args)
                 ;; abstract innermost-first so arg i becomes the (n-1-i)th binder (λ x1 … xn. body)
                fexpr (reduce (fn [body [fvid ftype]]
                                (e/lam "x" ftype (e/abstract1 body fvid) :default))
                              term (reverse pairs))]
            (assoc-in m [:vars (e/bvar-idx pat-head)] fexpr)))
         ;; FIRST-ORDER: structural decomposition (equal arity, head + args matched recursively).
        (let [[term-head term-args] (e/get-app-fn-args term)]
          (when (= (count pat-args) (count term-args))
            (when-let [m (match-pattern gs unknowns pat-head term-head m depth)]
              (reduce (fn [m [pa ta]]
                        (if m
                          (match-pattern gs unknowns pa ta m depth)
                          (reduced nil)))
                      m
                      (map vector pat-args term-args)))))))

     ;; Pattern is a literal — must be identical
     (e/lit-nat? pat)
     (when (and (e/lit-nat? term) (= (e/lit-nat-val pat) (e/lit-nat-val term)))
       m)

     ;; Pattern is a LAMBDA/FORALL — match UNDER the binder (enables laws whose LHS
     ;; contains a binder with pattern vars, e.g. the semijoin section `elem · ys` =
     ;; `fun x => List.elem x ys`). Faithful to Lean 4 `Grind/EMatch.lean` (opens the
     ;; binder with a fresh local and matches the body): the LAMBDA binder TYPE is
     ;; IGNORED (defeq, not syntactic — Lean's "type info in lambdas is ignored"), the
     ;; FORALL DOMAIN is matched (semantically part of the type). Open both binders with
     ;; the SAME fresh fvar (depth-indexed, far above any real fvar); `instantiate1`
     ;; shifts the outer pattern-var bvars back to their telescope indices, so `:vars`
     ;; keys stay consistent. A pattern var that CAPTURES the bound fvar yields a
     ;; dangling-fvar instantiation the downstream kernel check rejects — so under-binder
     ;; matching never costs soundness, only finds more (valid) rewrites.
     (or (e/lam? pat) (e/forall? pat))
     (let [pat-lam? (e/lam? pat)
           term-binder? (if pat-lam? (e/lam? term) (e/forall? term))]
       (when term-binder?
         (let [pbody (if pat-lam? (e/lam-body pat) (e/forall-body pat))
               tbody (if pat-lam? (e/lam-body term) (e/forall-body term))
               ;; forall: match the domain; lambda: ignore the binder type (Lean)
               m (if pat-lam? m
                     (match-pattern gs unknowns (e/forall-type pat) (e/forall-type term) m depth))]
           (when m
             (let [fvid (+ 900000000 depth)
                   fv (e/fvar fvid)
                   ;; record the opened local's TYPE (from the concrete term side) so a HIGHER-ORDER
                   ;; (Miller) match in the body can synthesize a well-typed `λ (x : T). …`.
                   fvtype (if pat-lam? (e/lam-type term) (e/forall-type term))
                   m (assoc-in m [:ftypes fvid] fvtype)]
               (match-pattern gs unknowns
                              (e/instantiate1 pbody fv)
                              (e/instantiate1 tbody fv)
                              m (inc depth)))))))

     ;; Anything else (sort, mdata, …) — structural match
     :else
     (when (= pat term) m))))

(defn match-in-eqclass
  "Try to match pattern against any member of the equivalence class of term.
   `unknowns` is the set of theorem level-param Names (level unknowns).
   Only considers members with generation 0 (original terms) to prevent
   matching against terms created by previous E-matching rounds.
   Returns a seq of {:assignment {:vars .. :levels ..} :matched-term ..}."
  [gs unknowns pat term]
  (let [root (eg/get-root gs term)
        results (atom [])]
    ;; Traverse equivalence class
    (loop [curr root]
      (when-let [node (eg/get-enode gs curr)]
        ;; Only match gen=0 terms (original, not E-match-created)
        (when (zero? (:gen node))
          (when-let [m (match-pattern gs unknowns pat curr {:vars {} :levels {} :ftypes {}})]
            (swap! results conj {:assignment m :matched-term curr})))
        (let [next (:next node)]
          (when-not (identical? next root)
            (recur next)))))
    @results))

;; ============================================================
;; Theorem instantiation
;; ============================================================

(defn- level-subst
  "Build the {param-Name → Level} subst for a matched theorem: the unified levels,
   defaulting any level-param not constrained by the match to zero."
  [thm assignment]
  (let [lv (:levels assignment)]
    (into {} (map (fn [p] [p (get lv p lvl/zero)]) (:level-params thm)))))

(defn- instantiate-theorem
  "Given a successful match (rich assignment), instantiate the theorem by applying
   its proof const — at the UNIFIED universe levels — to the assigned term args.
   Returns an Expr (the instantiated proof)."
  [thm assignment]
  (let [num-params (:num-params thm)
        vars (:vars assignment)
        proof (e/const' (:origin thm)
                        (mapv (fn [p] (get (:levels assignment) p lvl/zero))
                              (:level-params thm)))
        ;; Build argument list from assignment (bvar 0 = innermost)
        args (mapv (fn [i] (get vars i)) (range num-params))]
    (when (every? some? args)
      ;; Apply proof to all arguments
      (reduce e/app proof (reverse args)))))

(defn- instantiate-eq-fact
  "Given an instantiated equality theorem, extract LHS = RHS for the E-graph,
   with universe levels resolved to the matched concrete levels (so the LHS is
   pointer/structure-comparable to the term that triggered the match)."
  [env thm assignment]
  (let [ty (e/instantiate-level-params (:type thm) (level-subst thm assignment))
        num-params (:num-params thm)
        vars (:vars assignment)
        ;; Substitute all forall-bound variables with assigned terms
        body (loop [t ty i 0]
               (if (and (e/forall? t) (< i num-params))
                 (let [arg (get vars (- num-params 1 i))]
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
                        (match-in-eqclass gs (set (:level-params thm)) pat candidate)
                        :while (< (count @new-facts) limit)]
                  ;; Check dedup (by term-var assignment; levels are derived)
                  (let [key (instance-key (:origin thm) (:vars assignment))]
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
