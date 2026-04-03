;; Tactic layer — grind: general-purpose automation following Lean 4.
;;
;; Combines:
;; 1. Persistent E-graph with congruence closure (grind/egraph.clj)
;; 2. Propositional propagators (And/Or/Not/Eq/ite)
;; 3. Proof reconstruction from E-graph paths (grind/proof.clj)
;; 4. Linear arithmetic via omega
;; 5. Polynomial reasoning via ring
;; 6. Case splitting on constructors/booleans
;; 7. Rewriting via simp

(ns ansatz.tactic.grind
  "General-purpose automation tactic combining congruence closure,
   linear arithmetic, polynomial reasoning, and case splitting.

   Usage:
     (grind ps)              ;; full automation
     (grind ps {:fuel 100})  ;; with custom fuel"
  (:require [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.tc :as tc]
            [ansatz.kernel.reduce :as red]
            [ansatz.tactic.proof :as proof]
            [ansatz.tactic.basic :as basic]
            [ansatz.tactic.simp :as simp]
            [ansatz.tactic.grind.egraph :as eg]
            [ansatz.tactic.grind.proof :as egproof]
            [ansatz.tactic.grind.ematch :as ematch]
            [ansatz.config :as config]))

;; ============================================================
;; Names
;; ============================================================

(def ^:private eq-name (name/from-string "Eq"))
(defn- tactic-error! [msg data]
  (throw (ex-info (str "grind: " msg) (merge {:kind :tactic-error} data))))

;; ============================================================
;; E-graph congruence closure (pure Clojure)
;; ============================================================

(def ^:private false-name (name/from-string "False"))
(def ^:private false-elim-name (name/from-string "False.elim"))
(def ^:private true-intro-name (name/from-string "True.intro"))
(def ^:private eq-mp-name (name/from-string "Eq.mp"))

(defn- build-grind-state*
  "Add hypothesis equalities and Prop assertions to an existing E-graph state.
   Goal terms should already be internalized (for parent tracking)."
  [gs ps goal st]
  (let [lctx (:lctx goal)
        ;; Internalize and assert all hypothesis equalities
        gs (reduce
            (fn [gs [id decl]]
              (if (= :local (:tag decl))
                (let [ty (:type decl)
                      wty (try (#'tc/cached-whnf st ty)
                               (catch clojure.lang.ExceptionInfo _ ty))
                      [hd args] (e/get-app-fn-args wty)]
                  (if (and (e/const? hd) (= (e/const-name hd) eq-name)
                           (= 3 (count args)))
                    (let [lhs (nth args 1) rhs (nth args 2)
                          gs (-> gs (eg/internalize lhs 0) (eg/internalize rhs 0))
                          gs (eg/assert-eq gs lhs rhs (e/fvar id))]
                      gs)
                    gs))
                gs))
            gs lctx)
        ;; Also internalize Prop hypotheses as True
        gs (reduce
            (fn [gs [id decl]]
              (if (= :local (:tag decl))
                (let [ty (:type decl)
                      [hd _] (e/get-app-fn-args ty)]
                  (if (and (e/const? hd)
                           (not= (e/const-name hd) eq-name)
                           (try (let [s (#'tc/cached-whnf st (tc/infer-type st ty))]
                                  (and (e/sort? s) (= (e/sort-level s) lvl/zero)))
                                (catch Exception _ false)))
                    (let [gs (eg/internalize gs ty 0)]
                      (eg/assert-true gs ty {:tag :hyp-true :fvar-id id}))
                    gs))
                gs))
            gs lctx)]
    gs))

(defn- try-egraph-close
  "Try to close goal via E-graph. Handles three cases following Lean 4:
   1. Eq goal: CC + E-matching, build proof from E-graph paths
   2. Inconsistency: True=False in E-graph → close ANY goal via False.elim
   3. Prop goal = True: goal type equivalent to True → close via hypothesis

   Returns updated proof state with goal closed, or nil."
  [ps & {:keys [lemma-names] :or {lemma-names []}}]
  (let [goal (proof/current-goal ps)
        st (assoc (tc/mk-tc-state (:env ps)) :lctx (:lctx goal))
        goal-type (:type goal)
        whnf-goal (try (#'tc/cached-whnf st goal-type)
                       (catch clojure.lang.ExceptionInfo _ goal-type))
        [gh gargs] (e/get-app-fn-args whnf-goal)
        is-eq-goal (and (e/const? gh) (= (e/const-name gh) eq-name) (= 3 (count gargs)))
        ;; Initialize E-graph and internalize goal terms FIRST
        ;; (so parent tracking is set up before hypothesis merges)
        gs (eg/mk-grind-state (:env ps))
        gs (if is-eq-goal
             (-> gs (eg/internalize (nth gargs 1) 0) (eg/internalize (nth gargs 2) 0))
             (eg/internalize gs whnf-goal 0))
        ;; Then build E-graph state with all hypotheses
        gs (build-grind-state* gs ps goal st)
        ;; Run E-matching if lemma names provided
        gs (if (and (seq lemma-names)
                    (not (:inconsistent gs))
                    (if is-eq-goal
                      (not (eg/is-eqv gs (nth gargs 1) (nth gargs 2)))
                      true))
             (let [thms (ematch/prepare-theorems (:env ps) lemma-names)]
               (if (seq thms)
                 (:gs (ematch/run-ematch gs thms #{}
                                         (if is-eq-goal
                                           #(eg/is-eqv % (nth gargs 1) (nth gargs 2))
                                           #(:inconsistent %))))
                 gs))
             gs)]
    (or
      ;; Case 1: Eq goal solved by CC
     (when (and is-eq-goal (eg/is-eqv gs (nth gargs 1) (nth gargs 2)))
       (let [proof-term (try (egproof/mk-eq-proof gs st (nth gargs 1) (nth gargs 2))
                             (catch Exception _ nil))]
         (when proof-term
           (-> (proof/assign-mvar ps (:id goal) {:kind :exact :term proof-term})
               (proof/record-tactic :grind [:egraph-cc] (:id goal))))))

      ;; Case 2: Inconsistency → close any goal via False.elim
      ;; Two sub-cases:
      ;; 2a: True=False in E-graph → Eq.mp True False proof True.intro
      ;; 2b: Constructor discrimination → use noConfusion or just
      ;;     close goal=False via basic tactics (exfalso + contradiction chain)
     (when (:inconsistent gs)
       (or
          ;; 2a: True=False path
        (when (eg/is-eqv gs (:true-expr gs) (:false-expr gs))
          (let [true-expr (:true-expr gs) false-expr (:false-expr gs)
                true-eq-false (try (egproof/mk-eq-proof gs st true-expr false-expr)
                                   (catch Exception _ nil))]
            (when true-eq-false
              (let [false-proof (e/app* (e/const' eq-mp-name [])
                                        true-expr false-expr true-eq-false
                                        (e/const' true-intro-name []))
                    goal-sort-level (try (let [s (#'tc/cached-whnf st (tc/infer-type st goal-type))]
                                           (if (e/sort? s) (e/sort-level s) lvl/zero))
                                         (catch Exception _ lvl/zero))
                    proof-term (e/app* (e/const' false-elim-name [goal-sort-level])
                                       goal-type false-proof)]
                (-> (proof/assign-mvar ps (:id goal) {:kind :exact :term proof-term})
                    (proof/record-tactic :grind [:inconsistent] (:id goal)))))))
          ;; 2b: ctor-conflict detected but no True=False — the subst strategy
          ;; in grind-core will handle this on next iteration
        ))

      ;; Case 3: Non-Eq Prop goal — try direct hypothesis match + And.left/right
     (when (not is-eq-goal)
       (let [and-name (name/from-string "And")]
         (or
            ;; 3a: Direct hypothesis match (h : P where goal is P)
          (some (fn [[id decl]]
                  (when (and (= :local (:tag decl))
                             (or (.equals (:type decl) goal-type)
                                 (.equals (:type decl) whnf-goal)))
                    (-> (proof/assign-mvar ps (:id goal) {:kind :exact :term (e/fvar id)})
                        (proof/record-tactic :grind [:assumption] (:id goal)))))
                (:lctx goal))
            ;; 3b: And.left / And.right (h : P ∧ Q, goal is P or Q)
          (some (fn [[id decl]]
                  (when (= :local (:tag decl))
                    (let [ty (:type decl)
                          [hd args] (e/get-app-fn-args ty)]
                      (when (and (e/const? hd) (= (e/const-name hd) and-name)
                                 (= 2 (count args)))
                        (let [p (nth args 0) q (nth args 1)]
                          (cond
                              ;; Goal matches left conjunct
                            (or (.equals p goal-type) (.equals p whnf-goal))
                            (let [proof (e/app* (e/const' (name/from-string "And.left") [])
                                                p q (e/fvar id))]
                              (-> (proof/assign-mvar ps (:id goal)
                                                     {:kind :exact :term proof})
                                  (proof/record-tactic :grind [:and-left] (:id goal))))
                              ;; Goal matches right conjunct
                            (or (.equals q goal-type) (.equals q whnf-goal))
                            (let [proof (e/app* (e/const' (name/from-string "And.right") [])
                                                p q (e/fvar id))]
                              (-> (proof/assign-mvar ps (:id goal)
                                                     {:kind :exact :term proof})
                                  (proof/record-tactic :grind [:and-right] (:id goal))))
                            :else nil))))))
                (:lctx goal))))))))

;; ============================================================
;; Integration with other tactics
;; ============================================================

(defn- try-omega [ps]
  (try
    (require 'ansatz.tactic.omega)
    (let [omega-fn (resolve 'ansatz.tactic.omega/omega)]
      (omega-fn ps))
    (catch clojure.lang.ExceptionInfo _ nil)
    (catch Exception ex
      (when config/*grind-debug*
        (println "grind try-omega:" (.getMessage ex)))
      nil)))

(defn- try-simp [ps]
  (try
    (simp/simp ps)
    (catch clojure.lang.ExceptionInfo _ nil)
    (catch Exception ex
      (when config/*grind-debug*
        (println "grind try-simp:" (.getMessage ex)))
      nil)))

(defn- try-ring [ps]
  (try
    (require 'ansatz.tactic.ring)
    (let [ring-fn (resolve 'ansatz.tactic.ring/ring)]
      (ring-fn ps))
    (catch clojure.lang.ExceptionInfo _ nil)
    (catch Exception ex
      (when config/*grind-debug*
        (println "grind try-ring:" (.getMessage ex)))
      nil)))

(defn- try-rfl [ps]
  (try
    (basic/rfl ps)
    (catch clojure.lang.ExceptionInfo _ nil)
    (catch Exception ex
      (when config/*grind-debug*
        (println "grind try-rfl:" (.getMessage ex)))
      nil)))

(defn- try-assumption [ps]
  (try
    (basic/assumption ps)
    (catch clojure.lang.ExceptionInfo _ nil)
    (catch Exception ex
      (when config/*grind-debug*
        (println "grind try-assumption:" (.getMessage ex)))
      nil)))

;; ============================================================
;; Public API
;; ============================================================

;; ============================================================
;; Case splitting — Lean 4's Split.lean
;; ============================================================

(declare grind-core)

(defn- find-splittable-hyp
  "Find the first hypothesis suitable for case splitting.
   Skip types in already-split set (Lean 4 generation tracking).
   Priority: Prop inductives > stuck Bool.rec in goal.
   Returns {:fvar-id :name :type :kind :head-name} or nil."
  [ps goal already-split]
  (let [env (:env ps)
        st (assoc (tc/mk-tc-state env) :lctx (:lctx goal))]
    (or
      ;; 1. Prop-valued inductive hypotheses (skip already-split types)
     (some (fn [[id decl]]
             (when (and (= :local (:tag decl))
                        (not (contains? already-split id)))
               (let [ty (:type decl)
                     [head args] (e/get-app-fn-args ty)]
                 (when (and (e/const? head)
                            (not (contains? already-split (name/->string (e/const-name head))))
                            (not (#{"True" "False" "Eq" "HEq" "Iff" "And" "Or" "Not"
                                    "LE.le" "LT.lt" "GE.ge" "GT.gt"} (name/->string (e/const-name head))))
                            (let [ci (env/lookup env (e/const-name head))]
                              (and ci (.isInduct ^ansatz.kernel.ConstantInfo ci)
                                   (let [ind-sort (try (#'tc/cached-whnf st (tc/infer-type st ty))
                                                       (catch Exception _ nil))]
                                     (and ind-sort (e/sort? ind-sort)
                                          (= (e/sort-level ind-sort) lvl/zero))))))
                   {:fvar-id id :name (:name decl) :type ty :kind :inductive
                    :head-name (name/->string (e/const-name head))}))))
           (:lctx goal))
      ;; 2. Stuck Bool.rec anywhere in the WHNF'd goal type (scan recursively)
      ;;    WHNF first so that Bool.not(Bool.not b) reduces to Bool.rec form
     (let [found (atom nil)
           whnf-type (try (#'tc/cached-whnf st (:type goal))
                          (catch Exception _ (:type goal)))]
       (letfn [(scan [e]
                 (when-not @found
                   (let [[h a] (e/get-app-fn-args e)]
                     (when (and (e/const? h)
                                (= "Bool.rec" (name/->string (e/const-name h)))
                                (>= (count a) 4))
                       (reset! found (nth a 3))))
                   (when (e/app? e)
                     (scan (e/app-fn e))
                     (scan (e/app-arg e)))))]
         (scan whnf-type))
       (when-let [cond-expr @found]
         {:cond-expr cond-expr :kind :bool}))
      ;; 3. Bool-typed variable in context (Lean 4: split on value types)
      ;;    When the goal depends on a Bool variable, case-split on it
     (let [bool-name (name/from-string "Bool")]
       (some (fn [[id decl]]
               (when (and (= :local (:tag decl))
                          (not (contains? already-split id))
                          (let [ty (:type decl)
                                [th _] (e/get-app-fn-args ty)]
                            (and (e/const? th) (= (e/const-name th) bool-name))))
                 {:fvar-id id :name (:name decl) :type (:type decl)
                  :kind :inductive :head-name "Bool"}))
             (:lctx goal))))))

(defn- try-case-split
  "Try splitting on a hypothesis. Does NOT recurse — the outer loop handles it.
   Tracks Bool conditions by string to prevent re-splitting."
  [ps _depth lemma-names already-split]
  (when-let [target (find-splittable-hyp ps (proof/current-goal ps) already-split)]
    (try
      (case (:kind target)
        :inductive (basic/cases ps (:fvar-id target))
        :bool (basic/by-cases ps (:cond-expr target)))
      (catch clojure.lang.ExceptionInfo _ nil))))

;; ============================================================
;; Core grind loop — Lean 4's Finish.lean
;; ============================================================

(defn- try-constructors
  "Try applying constructors of the goal's inductive type. Does NOT recurse.
   Skips goals with stuck Bool.rec (those need case-split first)."
  [ps _depth _lemma-names _already-split]
  (let [goal (proof/current-goal ps)
        ;; Don't try constructors if goal has stuck Bool.rec (needs by_cases first)
        has-boolrec (let [found (atom false)]
                      (letfn [(scan [e]
                                (when-not @found
                                  (let [[h _] (e/get-app-fn-args e)]
                                    (when (and (e/const? h) (= "Bool.rec" (name/->string (e/const-name h))))
                                      (reset! found true)))
                                  (when (e/app? e) (scan (e/app-fn e)) (scan (e/app-arg e)))))]
                        (scan (:type goal)))
                      @found)]
    (when-not has-boolrec
      (let [[gh _] (e/get-app-fn-args (:type goal))]
        (when (e/const? gh)
          (let [ci (env/lookup (:env ps) (e/const-name gh))]
            (when (and ci (.isInduct ^ansatz.kernel.ConstantInfo ci))
              (some (fn [ctor-name]
                      (try
                        (let [ctor-ci (env/lookup (:env ps) ctor-name)
                              lps (vec (.levelParams ^ansatz.kernel.ConstantInfo ctor-ci))
                              levels (mapv (fn [_] lvl/zero) lps)
                              ps' (basic/apply-tac ps (e/const' ctor-name levels))]
                          ps')
                        (catch clojure.lang.ExceptionInfo _ nil)))
                    (.ctors ci)))))))))

(defn- changed?
  "Check if a tactic result shows meaningful progress.
   Progress = goal count changed, current goal closed, type changed, or lctx changed."
  [ps result]
  (and result (not (identical? result ps))
       (let [g1 (proof/current-goal ps)
             g2 (proof/current-goal result)]
         (or (not= (count (:goals result)) (count (:goals ps)))
             (and g1 (not g2))  ;; current goal closed
             (and g1 g2 (not= (:id g1) (:id g2)))  ;; different goal now current
             (and g1 g2 (= (:id g1) (:id g2))
                  (or (not (identical? (:type g1) (:type g2)))
                      (not= (count (:lctx g1)) (count (:lctx g2)))))))))

(defn- simp-normalize
  "Run simp as post-processing normalization on ALL open goals (not just current).
   Following Lean 4: simp runs in preprocessing, not in the main loop.
   After case-split creates multiple branches, each needs simp to reduce Bool.rec
   using the new hypothesis (hc: ble x a = true/false).
   Runs simp-all THEN simp (not or'd) — simp-all rewrites the discriminant,
   simp reduces Bool.rec with the constant discriminant."
  [ps lemma-names]
  (let [simp-one (fn [p]
                   (let [p (if (seq lemma-names)
                             (try (simp/simp-all p lemma-names)
                                  (catch clojure.lang.ExceptionInfo _ p))
                             p)]
                     (try (simp/simp p)
                          (catch clojure.lang.ExceptionInfo _ p))))]
    (try (basic/all-goals ps simp-one)
         (catch clojure.lang.ExceptionInfo _ ps))))

(defn- changed?
  "Check if a tactic result shows meaningful progress."
  [ps result]
  (and result (not (identical? result ps))
       (let [g1 (proof/current-goal ps)
             g2 (proof/current-goal result)]
         (or (not= (count (:goals result)) (count (:goals ps)))
             (and g1 (not g2))
             (and g1 g2 (not= (:id g1) (:id g2)))
             (and g1 g2 (= (:id g1) (:id g2))
                  (or (not (identical? (:type g1) (:type g2)))
                      (not= (count (:lctx g1)) (count (:lctx g2)))))))))

(defn- grind-core
  "Try one step on the current goal. Returns updated ps or nil.
   Non-recursive — the outer grind loop handles iteration.
   Following Lean 4 Finish.lean: solvers <|> instantiate <|> splitNext <|> mbtc.
   Simp runs as post-processing (after splits/intros), NOT as a strategy."
  [ps _depth lemma-names already-split]
  (let [goal (proof/current-goal ps)
        ;; Following Lean 4: "not applicable" = nil (silent), real errors propagate.
        ;; Catch ExceptionInfo (tactic failures) but let real Exception through.
        ;; Lean 4 pattern: "not applicable" = kna (nil), real errors propagate.
        ;; We catch ExceptionInfo (tactic), ClassCastException/IAE (Clojure
        ;; type errors from wrong-shape data), and StackOverflow.
        try-with-progress (fn [f]
                            (let [r (try (f)
                                         (catch clojure.lang.ExceptionInfo _ nil)
                                         (catch ClassCastException _ nil)
                                         (catch IllegalArgumentException _ nil)
                                         (catch RuntimeException _ nil)
                                         (catch StackOverflowError _ nil))]
                              (when (changed? ps r) r)))]
    (when goal
      (or
        ;; === Fast paths (Lean 4: these fire before the main loop) ===

        ;; Fast path 1: False hypothesis → close any goal immediately
        ;; (Lean 4: assertAll detects False=True → markAsInconsistent → done)
       (some (fn [[id decl]]
               (when (and (= :local (:tag decl))
                          (let [ty (:type decl)
                                [hd _] (e/get-app-fn-args ty)]
                            (and (e/const? hd) (= (e/const-name hd) false-name))))
                  ;; h : False — close via False.elim
                 (let [goal-sort (try (let [s (#'tc/cached-whnf
                                               (assoc (tc/mk-tc-state (:env ps)) :lctx (:lctx goal))
                                               (tc/infer-type
                                                (assoc (tc/mk-tc-state (:env ps)) :lctx (:lctx goal))
                                                (:type goal)))]
                                        (if (e/sort? s) (e/sort-level s) lvl/zero))
                                      (catch Exception _ lvl/zero))
                       proof (e/app* (e/const' false-elim-name [goal-sort])
                                     (:type goal) (e/fvar id))]
                   (-> (proof/assign-mvar ps (:id goal) {:kind :exact :term proof})
                       (proof/record-tactic :grind [:false-elim] (:id goal))))))
             (:lctx goal))

        ;; Fast path 2: Bool Eq goal with Bool-typed variable → case-split early
        ;; (Lean 4: simp preprocessing reduces to Bool.rec, then E-graph splits.
        ;; We skip directly to case-split since it's the most effective strategy.)
       (let [wgt (try (#'tc/cached-whnf
                       (assoc (tc/mk-tc-state (:env ps)) :lctx (:lctx goal))
                       (:type goal))
                      (catch Exception _ (:type goal)))
             [wh wa] (e/get-app-fn-args wgt)]
         (when (and (e/const? wh) (= (e/const-name wh) eq-name) (= 3 (count wa))
                    (let [[bh _] (e/get-app-fn-args (nth wa 0))]
                      (and (e/const? bh) (= (name/from-string "Bool") (e/const-name bh)))))
            ;; Bool Eq goal — try case-split on Bool variables
           (when-let [split-result (try-case-split ps 0 lemma-names already-split)]
             (simp-normalize split-result lemma-names))))

        ;; === Closing strategies (solvers) ===
       (try-with-progress #(basic/rfl ps))
       (try-with-progress #(basic/assumption ps))
        ;; IH application: apply function-typed hyps (forall or lambda), close subgoals with assumption
        ;; (Lean 4: E-matching does this; we emulate with apply+assumption)
        ;; Match when conclusion head = goal head (both const), OR when both are the same fvar,
        ;; OR when conclusion IS the goal type (modus ponens: P→Q with goal Q)
       (some (fn [[id decl]]
               (when (and (= :local (:tag decl))
                          (or (e/forall? (:type decl)) (e/lam? (:type decl)))
                          (let [ty (:type decl)
                                conclusion (loop [t ty]
                                             (cond (e/forall? t) (recur (e/forall-body t))
                                                   (e/lam? t) (recur (e/lam-body t))
                                                   :else t))
                                [ch _] (e/get-app-fn-args conclusion)
                                [gh _] (e/get-app-fn-args (:type goal))]
                            (or ;; Both const with same name
                             (and (e/const? ch) (e/const? gh)
                                  (= (e/const-name ch) (e/const-name gh)))
                                 ;; Both fvar with same id
                             (and (e/fvar? ch) (e/fvar? gh)
                                  (= (e/fvar-id ch) (e/fvar-id gh)))
                                 ;; Conclusion is exactly the goal type (fvar Prop)
                             (and (e/fvar? conclusion) (e/fvar? (:type goal))
                                  (= (e/fvar-id conclusion) (e/fvar-id (:type goal)))))))
                 (try
                   (let [ps' (basic/apply-tac ps (e/fvar id))
                         ps'' (basic/all-goals ps'
                                               (fn [p] (or (try (basic/assumption p)
                                                                (catch clojure.lang.ExceptionInfo _ nil)) p)))]
                     (when (changed? ps ps'') ps''))
                   (catch clojure.lang.ExceptionInfo _ nil))))
             (:lctx goal))
        ;; Subst: substitute fvar=expr hypotheses to simplify context
        ;; (Lean 4: grind normalizes via E-graph; we use subst as preprocessing)
        ;; This exposes indirect ctor equations (a=nil, b=cons, a=b → nil=cons)
       (some (fn [[id decl]]
               (when (= :local (:tag decl))
                 (let [ty (:type decl)
                       [hd args] (e/get-app-fn-args ty)]
                   (when (and (e/const? hd) (= (e/const-name hd) eq-name) (= 3 (count args)))
                     (let [lhs-eq (nth args 1) rhs-eq (nth args 2)]
                       (when (or (and (e/fvar? lhs-eq) (not (e/fvar? rhs-eq)))
                                 (and (e/fvar? rhs-eq) (not (e/fvar? lhs-eq))))
                         (try (basic/subst ps id)
                              (catch clojure.lang.ExceptionInfo _ nil))))))))
             (:lctx goal))
        ;; Constructor injection: h : ctor a₁..aₙ = ctor b₁..bₙ → aᵢ = bᵢ
        ;; Uses T.ctor.inj lemma + And.left/And.right
        ;; (Lean 4: Ctor.lean uses per-ctor noConfusion)
       (some (fn [[id decl]]
               (when (= :local (:tag decl))
                 (let [ty (:type decl)
                       st-local (assoc (tc/mk-tc-state (:env ps)) :lctx (:lctx goal))
                       wty (try (#'tc/cached-whnf st-local ty)
                                (catch clojure.lang.ExceptionInfo _ ty))
                       [hd args] (e/get-app-fn-args wty)]
                   (when (and (e/const? hd) (= (e/const-name hd) eq-name) (= 3 (count args)))
                     (let [eq-type (nth args 0) lhs-eq (nth args 1) rhs-eq (nth args 2)
                           [lh la] (e/get-app-fn-args lhs-eq)
                           [rh ra] (e/get-app-fn-args rhs-eq)]
                       (when (and (e/const? lh) (e/const? rh))
                         (let [ci-l (env/lookup (:env ps) (e/const-name lh))
                               ci-r (env/lookup (:env ps) (e/const-name rh))]
                           (when (and ci-l ci-r
                                      (.isCtor ^ansatz.kernel.ConstantInfo ci-l)
                                      (.isCtor ^ansatz.kernel.ConstantInfo ci-r))
                             (if (= (e/const-name lh) (e/const-name rh))
                                ;; SAME ctor: use T.ctor.inj to get field equalities
                                ;; T.ctor.inj : {params} → {fields1} → {fields2} → ctor fields1 = ctor fields2 → And (f1=f1') (And ...)
                               (let [inj-name (name/mk-str (e/const-name lh) "inj")
                                     inj-ci (env/lookup (:env ps) inj-name)]
                                 (when inj-ci
                                   (try
                                      ;; T.ctor.inj.{u} : {α} {a as b bs} → ctor = ctor → And (a=b) (as=bs)
                                     (let [ind-ci (env/lookup (:env ps) (.inductName ^ansatz.kernel.ConstantInfo ci-l))
                                           num-params (.numParams ^ansatz.kernel.ConstantInfo ind-ci)
                                           params-l (subvec (vec la) 0 (min num-params (count la)))
                                           fields-l (subvec (vec la) (min num-params (count la)))
                                           fields-r (subvec (vec ra) (min num-params (count ra)))
                                           inj-levels (e/const-levels lh)
                                            ;; T.ctor.inj params fields-l fields-r h : And (a=b) (xs=ys)
                                           inj-app (reduce e/app
                                                           (e/const' inj-name inj-levels)
                                                           (concat params-l fields-l fields-r [(e/fvar id)]))
                                           inj-type (tc/infer-type st-local inj-app)
                                            ;; Extract And components
                                           [and-head and-args] (e/get-app-fn-args inj-type)
                                            ;; Build And.left (inj-app) or And.right (inj-app) as exact proof
                                           and-left-name (name/from-string "And.left")
                                           and-right-name (name/from-string "And.right")
                                           left-conj (when (= 2 (count and-args)) (nth and-args 0))
                                           right-conj (when (= 2 (count and-args)) (nth and-args 1))
                                           goal-type (:type goal)
                                           proof-term (cond
                                                         ;; Goal matches left conjunct
                                                        (and left-conj (.equals left-conj goal-type))
                                                        (e/app* (e/const' and-left-name [])
                                                                left-conj right-conj inj-app)
                                                         ;; Goal matches right conjunct
                                                        (and right-conj (.equals right-conj goal-type))
                                                        (e/app* (e/const' and-right-name [])
                                                                left-conj right-conj inj-app)
                                                        :else nil)]
                                       (when proof-term
                                         (-> (proof/assign-mvar ps (:id goal)
                                                                {:kind :exact :term proof-term})
                                             (proof/record-tactic :grind [:ctor-injection] (:id goal)))))
                                     (catch clojure.lang.ExceptionInfo _ nil))))
                                ;; DIFFERENT ctor: build noConfusion proof directly
                                ;; T.noConfusion.{u_1, u} : {P} {α} {t : T α} {α'} {t' : T α'} →
                                ;;   (α = α') → (t ≍ t') → T.noConfusionType P ...
                                ;; For same-type case: α=α', use Eq.refl and heq_of_eq
                               (try
                                 (let [ind-name (.inductName ^ansatz.kernel.ConstantInfo ci-l)
                                       nc-name (name/mk-str ind-name "noConfusion")
                                       nc-ci (env/lookup (:env ps) nc-name)]
                                   (when nc-ci
                                     (let [st-local (assoc (tc/mk-tc-state (:env ps)) :lctx (:lctx goal))
                                           goal-sort (try (#'tc/cached-whnf st-local (tc/infer-type st-local (:type goal)))
                                                          (catch Exception _ nil))
                                           u1 (if (and goal-sort (e/sort? goal-sort)) (e/sort-level goal-sort) lvl/zero)
                                           ind-levels (e/const-levels lh)
                                           levels (into [u1] ind-levels)
                                           ind-ci (env/lookup (:env ps) ind-name)
                                           num-params (.numParams ^ansatz.kernel.ConstantInfo ind-ci)
                                           params-l (subvec (vec la) 0 (min num-params (count la)))
                                           params-r (subvec (vec ra) 0 (min num-params (count ra)))
                                            ;; Count how many args noConfusion expects
                                           nc-type (.type ^ansatz.kernel.ConstantInfo nc-ci)
                                           nc-arity (loop [t nc-type n 0] (if (e/forall? t) (recur (e/forall-body t) (inc n)) n))
                                            ;; Simple case: nc takes P, params, t1, t2, eq-proof (5 args for Bool)
                                            ;; HEq case: nc takes P, α, t1, α', t2, eq_α, heq_t (7 args for List)
                                           args (if (<= nc-arity 5)
                                                   ;; Simple (Bool-style)
                                                  (concat [(:type goal)] params-l [lhs-eq rhs-eq (e/fvar id)])
                                                   ;; HEq (List-style): P α t α' t' (Eq.refl α) (heq_of_eq h)
                                                  (let [alpha (first params-l)
                                                        alpha-type (tc/infer-type st-local alpha)
                                                        alpha-sort (#'tc/cached-whnf st-local (tc/infer-type st-local alpha-type))
                                                        alpha-level (if (e/sort? alpha-sort) (e/sort-level alpha-sort) (lvl/succ lvl/zero))
                                                        eq-refl-alpha (e/app* (e/const' (name/from-string "Eq.refl") [alpha-level])
                                                                              alpha-type alpha)
                                                         ;; heq_of_eq.{u} : {α : Sort u} → {a b : α} → a = b → a ≍ b
                                                        elem-sort (#'tc/cached-whnf st-local (tc/infer-type st-local eq-type))
                                                        elem-level (if (e/sort? elem-sort) (e/sort-level elem-sort) (lvl/succ lvl/zero))
                                                        heq-of-eq (e/app* (e/const' (name/from-string "heq_of_eq") [elem-level])
                                                                          eq-type lhs-eq rhs-eq (e/fvar id))]
                                                    (concat [(:type goal)] params-l [lhs-eq] params-r [rhs-eq eq-refl-alpha heq-of-eq])))
                                           nc-app (reduce e/app (e/const' nc-name levels) args)]
                                       (-> (proof/assign-mvar ps (:id goal) {:kind :exact :term nc-app})
                                           (proof/record-tactic :grind [:noConfusion] (:id goal))))))
                                 (catch Exception _ nil)))))))))))
             (:lctx goal))
        ;; E-graph congruence closure + E-matching + inconsistency closing
       (try-with-progress #(try-egraph-close ps :lemma-names lemma-names))
        ;; Constructors (structural closing)
       (try-with-progress #(try-constructors ps 0 lemma-names already-split))
        ;; Arithmetic
       (try-with-progress #(let [f (requiring-resolve 'ansatz.tactic.omega/omega)] (f ps)))
       (try-with-progress #(let [f (requiring-resolve 'ansatz.tactic.ring/ring)] (f ps)))
        ;; Case split (Lean 4: splitNext) — then simp as post-processing on ALL branches
       (when-let [split-result (try-case-split ps 0 lemma-names already-split)]
         (simp-normalize split-result lemma-names))
        ;; Simp as last resort (no structural step available)
       (when (seq lemma-names)
         (try-with-progress #(simp/simp-all ps lemma-names)))
       (try-with-progress #(simp/simp ps))))))

;; ============================================================
;; Public API
;; ============================================================

(defn grind
  "General-purpose automation tactic (Lean 4's grind).

   Combines congruence closure, simplification, linear arithmetic,
   polynomial reasoning, and case splitting.

   Usage:
     (grind ps)                    ;; full automation
     (grind ps [\"insertSorted\"])   ;; with simp lemmas for unfolding

   Following Lean 4 Finish.lean: flat loop processes goals one at a time,
   applying strategies until all goals are closed or max iterations reached."
  ([ps] (grind ps []))
  ([ps lemma-names]
   (let [lnames (if (sequential? lemma-names) lemma-names [])
         max-iter 2000]
     (loop [ps ps
            iter 0
            already-split #{}
            last-goal-count (count (:goals ps))
            seen-goals #{}]
       (if (or (proof/solved? ps) (>= iter max-iter))
         (if (proof/solved? ps)
           ps
           (tactic-error! "grind: iteration limit reached" {:iter iter}))
         ;; Try one step on the current goal.
         ;; If we've seen this exact goal type before, skip non-splitting strategies
         ;; and go straight to case-split (prevents simp loops).
         (let [goal-before (proof/current-goal ps)
               ;; Include hypothesis fingerprint in the key to distinguish goals with
               ;; different contexts (e.g., hc=false vs hc=true after by_cases)
               goal-type-key (when goal-before
                               (str (.toString (:type goal-before))
                                    "|" (hash (mapv (fn [[_ d]] (.toString (:type d)))
                                                    (:lctx goal-before)))))
               _ (when config/*grind-debug*
                   (let [ts (when goal-before (e/->string (:type goal-before)))]
                     (println (str "grind[" iter "] goals=" (count (:goals ps))
                                   " type=" (when ts (subs ts 0 (min 80 (count ts))))))))
               seen? (and goal-type-key (contains? seen-goals goal-type-key))
               result (if seen?
                        ;; Skip simp — we've already tried it on this goal.
                        ;; Still try quick tactics + constructors + case-split.
                        (or (try (basic/rfl ps) (catch clojure.lang.ExceptionInfo _ nil))
                            (try (basic/assumption ps) (catch clojure.lang.ExceptionInfo _ nil))
                            (try-constructors ps 0 lnames already-split)
                            (try (let [f (requiring-resolve 'ansatz.tactic.omega/omega)] (f ps))
                                 (catch clojure.lang.ExceptionInfo _ nil))
                            (try-case-split ps 0 lnames already-split))
                        (grind-core ps 0 lnames already-split))]
           (if (or (nil? result) (identical? result ps))
             ;; grind-core failed or made no progress — give up
             (tactic-error! "grind: all strategies failed"
                            {:goal (when goal-before (:type goal-before))})
             ;; Progress — continue loop
             (let [new-count (count (:goals result))
                   ;; Track split types from this iteration
                   new-split (if (> new-count last-goal-count)
                               (let [g (proof/current-goal ps)
                                     ty (when g (:type g))
                                     [h _] (when ty (e/get-app-fn-args ty))]
                                 (if (and h (e/const? h))
                                   (conj already-split (name/->string (e/const-name h)))
                                   already-split))
                               already-split)]
               (recur result (inc iter) new-split new-count
                      (if goal-type-key (conj seen-goals goal-type-key) seen-goals))))))))))
