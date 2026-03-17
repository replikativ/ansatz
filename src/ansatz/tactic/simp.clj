;; Copyright (c) 2026 Christian Weilbach. All rights reserved.
;; Tactic layer — simp: simplification by term rewriting.
;;
;; Implements a simplification tactic following Lean 4's simp architecture:
;;
;; Core concepts:
;; - SimpResult: {:expr Expr, :proof? (Option Expr)} where proof? is an
;;   equality proof old = new (nil means rfl / definitional equality)
;; - Step: 3-way return type (:done/:visit/:continue) matching Lean 4
;; - Pre/post rewriting phases (pre before subterm descent, post after)
;; - Simprocs: custom simplification procedures for arithmetic, etc.
;; - Congruence: proper descent into subterms with proof construction
;; - Contextual: hypotheses added as rewrite lemmas
;; - Discharge: recursive simp for conditional rewrite side-conditions
;;
;; Algorithm (following Lean 4's Simp.Main.lean):
;; 1. Pre-phase: try pre-rewrite rules and simprocs
;;    - :done → return immediately (terminal, no further processing)
;;    - :visit → recurse simpLoop on result
;;    - :continue → proceed to reduction + structural descent
;; 2. Reduce (beta/iota/zeta/proj/unfold/fvar)
;; 3. Structural descent (simpStep) with congruence proofs
;; 4. Post-phase: try post-rewrite rules and simprocs
;; 5. If not single-pass and changed: re-enter simpLoop

(ns ansatz.tactic.simp
  "Simplification tactic by term rewriting.

   Supports:
   - Rewriting with equality lemmas (∀ x y ..., lhs = rhs)
   - Iff lemmas (∀ x y ..., P ↔ Q)
   - Definitional simplification (beta, iota, projection)
   - Pre/post rewriting phases with Step type
   - Built-in simprocs for Nat/Int arithmetic reduction
   - Contextual rewriting (hypotheses as lemmas)
   - simp_all (simplify goal + all hypotheses)
   - Discharge for conditional rewrites (recursive simp)
   - implies_congr/forall_congr proof terms
   - Discrimination tree indexing (Lean 4's DiscrTree)
   - Proof construction via Eq.trans/congrArg/congrFun/congr chains"
  (:require [ansatz.kernel.expr :as e]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [ansatz.tactic.discr-tree :as dt]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.tc :as tc]
            [ansatz.kernel.reduce :as red]
            [ansatz.tactic.proof :as proof]
            [ansatz.tactic.decide :as decide-tac]
            [ansatz.tactic.instance :as inst]
            [ansatz.config :as config])
  (:import [ansatz.kernel ConstantInfo]))

;; ============================================================
;; Names
;; ============================================================

(def ^:private eq-name (name/from-string "Eq"))
(def ^:private iff-name (name/from-string "Iff"))
(def ^:private true-name (name/from-string "True"))
(def ^:private false-name (name/from-string "False"))
(def ^:private eq-refl-name (name/from-string "Eq.refl"))
(def ^:private eq-trans-name (name/from-string "Eq.trans"))
(def ^:private true-intro-name (name/from-string "True.intro"))
(def ^:private congr-arg-name (name/from-string "congrArg"))
(def ^:private congr-fun-name (name/from-string "congrFun"))
(def ^:private congr-name (name/from-string "congr"))
(def ^:private funext-name (name/from-string "funext"))
(def ^:private implies-congr-name (name/from-string "implies_congr"))
(def ^:private of-eq-true-name (name/from-string "of_eq_true"))
(def ^:private eq-true-name (name/from-string "eq_true"))
(def ^:private eq-false-name (name/from-string "eq_false"))
(def ^:private eq-mpr-name (name/from-string "Eq.mpr"))
(def ^:private propext-name (name/from-string "propext"))
(def ^:private and-name (name/from-string "And"))
(def ^:private and-left-name (name/from-string "And.left"))
(def ^:private and-right-name (name/from-string "And.right"))

;; simpUsingDecide names
(def ^:private eq-true-of-decide-name (name/from-string "eq_true_of_decide"))
(def ^:private eq-false-of-decide-name (name/from-string "eq_false_of_decide"))
(def ^:private decidable-decide-name (name/from-string "Decidable.decide"))
(def ^:private decidable-name (name/from-string "Decidable"))
(def ^:private bool-name (name/from-string "Bool"))

;; ============================================================
;; Step type — Lean 4's Simp.Step
;; ============================================================
;; {:tag :done/:visit/:continue, :result SimpResult-or-nil}

;; ============================================================
;; SimpResult — the core output type
;; ============================================================

(defn- mk-result
  "Create a simp result. proof?=nil means definitional equality (rfl)."
  ([expr] {:expr expr :proof? nil :cache true})
  ([expr proof] {:expr expr :proof? proof :cache true}))

(defn- mk-eq-trans
  "Compose two simp results via Eq.trans.
   r1 proves a = b, r2 proves b = c, returns a = c."
  [st r1 r2]
  (cond
    (nil? (:proof? r1)) r2
    (nil? (:proof? r2)) (assoc r1 :expr (:expr r2))
    :else
    (let [ty (try (tc/infer-type st (:proof? r1)) (catch Exception _ nil))
          ty-whnf (when ty (#'tc/cached-whnf st ty))
          [head args] (when ty-whnf (e/get-app-fn-args ty-whnf))
          alpha (when (and head (e/const? head) (= (e/const-name head) eq-name)
                           (= 3 (count args)))
                  (nth args 0))
          u (when alpha
              (let [s (try (tc/infer-type st alpha) (catch Exception _ nil))
                    sw (when s (#'tc/cached-whnf st s))]
                (when (and sw (e/sort? sw)) (e/sort-level sw))))]
      (if (and alpha u)
        {:expr (:expr r2)
         :proof? (e/app* (e/const' eq-trans-name [u])
                         alpha (nth args 1) (nth args 2) (:expr r2)
                         (:proof? r1) (:proof? r2))
         :cache (and (:cache r1) (:cache r2))}
        ;; Composition failed — keep r1's proof (which is valid) with r2's expr
        ;; The kernel will accept this since r1's RHS and r2's expr should be def-eq
        (assoc r1 :expr (:expr r2))))))

;; ============================================================
;; Congruence proof builders — following Lean 4's Types.lean
;; ============================================================

(defn- safe-infer [st e]
  (try (tc/infer-type st e)
       (catch Exception _
      ;; Fallback: try Java TypeChecker with more fuel for complex proof terms
         (try
           (let [tc (ansatz.kernel.TypeChecker. (:env st))]
             (.setFuel tc config/*high-fuel*)
             (.inferType tc e))
           (catch Exception _ nil)))))

(defn- safe-whnf [st e]
  (try (#'tc/cached-whnf st e)
       (catch Exception _
      ;; Fallback: try Java TypeChecker's whnf for deep chains
         (try
           (let [tc (ansatz.kernel.TypeChecker. (:env st))]
             (.setFuel tc config/*default-fuel*)
             (.whnf tc e))
           (catch Exception _ nil)))))

(defn- get-sort-level [st e]
  (let [ty (safe-infer st e)
        sw (when ty (safe-whnf st ty))]
    (if (and sw (e/sort? sw)) (e/sort-level sw) lvl/zero)))

(defn- mk-congr-fun
  "congrFun h a : f₁ a = f₂ a, given h : f₁ = f₂.
   congrFun : {α : Sort u} {β : α → Sort v} {f₁ f₂ : ∀ a, β a} (h : f₁ = f₂) (a : α) → f₁ a = f₂ a"
  ([st f-result a] (mk-congr-fun st f-result a nil nil))
  ([st f-result a orig-f1 orig-f2]
   (if (nil? (:proof? f-result))
     (mk-result (e/app (:expr f-result) a))
     (try
       (let [h (:proof? f-result)
             h-type (safe-infer st h)
             h-whnf (when h-type (safe-whnf st h-type))
             [head args] (when h-whnf (e/get-app-fn-args h-whnf))
            ;; Fallback: infer fn-type from f1 directly
             [fn-type f1 f2]
             (if (and head (e/const? head) (= (e/const-name head) eq-name) (= 3 (count args)))
               [(nth args 0) (nth args 1) (nth args 2)]
              ;; Fallback: use orig-f1/orig-f2 if available, infer type from f1
               (let [f1 (or orig-f1 (:expr f-result))
                     f2 (or orig-f2 (:expr f-result))
                     ft (safe-infer st f1)]
                 (when ft [ft f1 f2])))]
         (if fn-type
           (let [fn-type-whnf (or (safe-whnf st fn-type) fn-type)
                 alpha (if (e/forall? fn-type-whnf) (e/forall-type fn-type-whnf) fn-type-whnf)
                 beta-body (if (e/forall? fn-type-whnf) (e/forall-body fn-type-whnf) fn-type-whnf)
                 beta (e/lam "a" alpha beta-body :default)
                 u (get-sort-level st alpha)
                 result-type (safe-infer st (e/app f1 a))
                 v (if result-type (get-sort-level st result-type) lvl/zero)]
             {:expr (e/app (:expr f-result) a)
             ;; congrFun.{u,v} {α} {β} {f₁} {f₂} h a
              :proof? (e/app* (e/const' congr-fun-name [u v])
                              alpha beta f1 f2 h a)
              :cache true})
           (mk-result (e/app (:expr f-result) a))))
       (catch Exception _ (mk-result (e/app (:expr f-result) a)))))))

(defn- mk-congr-arg
  "congrArg f h : f a₁ = f a₂, given h : a₁ = a₂.
   congrArg : {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β) (h : a₁ = a₂) → f a₁ = f a₂"
  ([st f a-result]
   (mk-congr-arg st f a-result nil nil))
  ([st f a-result orig-a1 orig-a2]
   (if (nil? (:proof? a-result))
     (mk-result (e/app f (:expr a-result)))
     (try
       (let [h (:proof? a-result)
             ;; Try to get alpha, a1, a2 from proof type
             h-type (safe-infer st h)
             h-whnf (when h-type (safe-whnf st h-type))
             [head args] (when h-whnf (e/get-app-fn-args h-whnf))
             ;; Fall back to inferring alpha from orig-a1 if proof type unavailable
             [alpha a1 a2]
             (if (and head (e/const? head) (= (e/const-name head) eq-name) (= 3 (count args)))
               [(nth args 0) (nth args 1) (nth args 2)]
               ;; Fallback: use orig-a1/orig-a2 and infer alpha from the argument type
               (let [a1 (or orig-a1 (:orig a-result))
                     a2 (or orig-a2 (:expr a-result))
                     alpha (when a1 (safe-infer st a1))]
                 (when (and alpha a1 a2) [alpha a1 a2])))]
         (if (and alpha a1 a2)
           (let [u (get-sort-level st alpha)
                 beta (safe-infer st (e/app f a1))
                 v (if beta (get-sort-level st beta) lvl/zero)]
             {:expr (e/app f (:expr a-result))
              :proof? (e/app* (e/const' congr-arg-name [u v])
                              alpha beta a1 a2 f h)
              :cache true})
           (mk-result (e/app f (:expr a-result)))))
       (catch Exception _ (mk-result (e/app f (:expr a-result))))))))

(defn- mk-congr
  "congr hf ha : f₁ a₁ = f₂ a₂. Optimizes reflexivity cases."
  [st f-result a-result orig-f orig-a]
  (cond
    (and (nil? (:proof? f-result)) (nil? (:proof? a-result)))
    (mk-result (e/app (:expr f-result) (:expr a-result)))

    (nil? (:proof? a-result))
    (mk-congr-fun st f-result (:expr a-result) orig-f (:expr f-result))

    (nil? (:proof? f-result))
    (mk-congr-arg st (:expr f-result) a-result orig-a (:expr a-result))

    :else
    (try
      (let [ha (:proof? a-result)
            ha-type (safe-infer st ha)
            ha-whnf (when ha-type (safe-whnf st ha-type))
            [head args] (when ha-whnf (e/get-app-fn-args ha-whnf))]
        (if (and head (e/const? head) (= (e/const-name head) eq-name) (= 3 (count args)))
          (let [alpha (nth args 0)       ;; α (arg type)
                u (get-sort-level st alpha)
                beta (safe-infer st (e/app orig-f orig-a))  ;; β (result type)
                v (if beta (get-sort-level st beta) lvl/zero)]
            {:expr (e/app (:expr f-result) (:expr a-result))
             ;; congr.{u,v} {α} {β} {f₁} {f₂} {a₁} {a₂} hf ha
             :proof? (e/app* (e/const' congr-name [u v])
                             alpha beta
                             orig-f (:expr f-result)
                             orig-a (:expr a-result)
                             (:proof? f-result) (:proof? a-result))
             :cache true})
          (mk-result (e/app (:expr f-result) (:expr a-result)))))
      (catch Exception _
        (mk-result (e/app (:expr f-result) (:expr a-result)))))))

(defn- mk-implies-congr
  "implies_congr hp hq : (p₁ → q₁) = (p₂ → q₂).
   Lean 4: mkImpCongr for non-dependent arrow types."
  [st p-result q-result orig-p orig-q]
  (cond
    (and (nil? (:proof? p-result)) (nil? (:proof? q-result)))
    (mk-result (e/arrow (:expr p-result) (:expr q-result)))

    :else
    (try
      (let [hp (or (:proof? p-result)
                   (e/app* (e/const' eq-refl-name [lvl/zero])
                           (e/sort' lvl/zero) orig-p))
            hq (or (:proof? q-result)
                   (e/app* (e/const' eq-refl-name [lvl/zero])
                           (e/sort' lvl/zero) orig-q))]
        {:expr (e/arrow (:expr p-result) (:expr q-result))
         :proof? (e/app* (e/const' implies-congr-name [])
                         orig-p (:expr p-result)
                         orig-q (:expr q-result) hp hq)
         :cache true})
      (catch Exception _
        (mk-result (e/arrow (:expr p-result) (:expr q-result)))))))

;; ============================================================
;; Error helpers
;; ============================================================

(defn- tactic-error! [msg data]
  (throw (ex-info (str "simp: " msg) (merge {:kind :tactic-error} data))))

;; ============================================================
;; Perm detection — Lean 4's isPerm (SimpTheorems.lean:261-273)
;; ============================================================
;; A theorem is permutative if its LHS and RHS are structurally identical
;; modulo permutation of bound variables. For commutativity (a*b = b*a)
;; this returns true; for associativity ((a*b)*c = a*(b*c)) this returns
;; false because the nesting structure differs.
;;
;; In Lean 4, mvars can be swapped via isDefEq.
;; In our extracted lemmas, the analogous role is played by bvars
;; (forall-bound parameters).

(defn- is-perm?
  "Lean 4's isPerm: check if two expressions are structurally identical
   modulo permutation of bound variables (bvars).
   Returns true if a and b differ only in which bvar appears where."
  [a b]
  (cond
    ;; Both apps — recurse on fn and arg (Lean 4: .app f₁ a₁, .app f₂ a₂)
    (and (e/app? a) (e/app? b))
    (and (is-perm? (e/app-fn a) (e/app-fn b))
         (is-perm? (e/app-arg a) (e/app-arg b)))

    ;; Both bvars — permutable (Lean 4: .mvar, .mvar => isDefEq)
    (and (e/bvar? a) (e/bvar? b)) true

    ;; Both foralls — recurse on domain and body
    (and (e/forall? a) (e/forall? b))
    (and (is-perm? (e/forall-type a) (e/forall-type b))
         (is-perm? (e/forall-body a) (e/forall-body b)))

    ;; Both lambdas — recurse on domain and body
    (and (e/lam? a) (e/lam? b))
    (and (is-perm? (e/lam-type a) (e/lam-type b))
         (is-perm? (e/lam-body a) (e/lam-body b)))

    ;; Both projs — same index, recurse on struct
    (and (e/proj? a) (e/proj? b))
    (and (= (e/proj-idx a) (e/proj-idx b))
         (is-perm? (e/proj-struct a) (e/proj-struct b)))

    ;; Strip mdata
    (e/mdata? a) (is-perm? (e/mdata-expr a) b)
    (e/mdata? b) (is-perm? a (e/mdata-expr b))

    ;; Default — strict structural equality (Lean 4: s == t)
    :else (= a b)))

;; ============================================================
;; Simp lemma representation and extraction
;; ============================================================

(defn- is-rfl-proof?
  "Check if a constant's value is an rfl proof (Eq.refl applied to args).
   Lean 4: isRflTheorem checks if proof is definitionally rfl.
   Peels lambda wrappers to find the Eq.refl inside."
  [^ConstantInfo ci]
  (when-let [v (.value ci)]
    (let [body (loop [e v]
                 (if (e/lam? e) (recur (e/lam-body e)) e))
          head (e/get-app-fn body)]
      (and (e/const? head)
           (= (e/const-name head) eq-refl-name)))))

(defn- extract-from-conclusion
  "Extract simp lemma(s) from a conclusion type (after forall stripping).
   Returns a vector of lemma maps. Handles Eq, Iff, Not P (→ P = False),
   Ne a b (→ (a = b) = False), And P Q (split into separate lemmas),
   and general prop→True.
   Lean 4: SimpTheorems.lean:324-359 — preprocess + shouldPreprocess."
  [env cname level-params num-params rfl-flag priority ty]
  (let [[head args] (e/get-app-fn-args ty)]
    (cond
      ;; Eq: standard rewrite lemma (lhs = rhs)
      (and (e/const? head) (= (e/const-name head) eq-name) (= 3 (count args)))
      (let [lhs (nth args 1) rhs (nth args 2)
            [lhs-head _] (e/get-app-fn-args lhs)
            lhs-nargs (count (e/get-app-args lhs))
            head-name (when (e/const? lhs-head) (e/const-name lhs-head))
            ;; Detect perm: LHS and RHS are identical modulo variable permutation
            ;; Lean 4: isPerm (SimpTheorems.lean:261-273)
            perm (is-perm? lhs rhs)]
        [{:name cname :level-params level-params :num-params num-params
          :lhs-pattern lhs :rhs rhs :eq-type (nth args 0)
          :kind :eq :priority priority :perm perm :rfl rfl-flag
          :head-name head-name :lhs-nargs lhs-nargs}])

      ;; Iff: bidirectional rewrite (P ↔ Q)
      (and (e/const? head) (= (e/const-name head) iff-name) (= 2 (count args)))
      (let [lhs (nth args 0) rhs (nth args 1)
            [lhs-head _] (e/get-app-fn-args lhs)
            lhs-nargs (count (e/get-app-args lhs))
            head-name (when (e/const? lhs-head) (e/const-name lhs-head))
            ;; Detect perm: Lean 4's isPerm
            perm (is-perm? lhs rhs)]
        [{:name cname :level-params level-params :num-params num-params
          :lhs-pattern lhs :rhs rhs :eq-type nil
          :kind :iff :priority priority :perm perm :rfl false
          :head-name head-name :lhs-nargs lhs-nargs}])

      ;; Not P → P = False
      ;; In Ansatz, Not P = ∀ _ : P, False. After stripping all outer foralls,
      ;; if ty is itself a forall whose body is False, it's Not P.
      ;; Special case: if P is @Eq α a b, this is Ne α a b → (a = b) = False.
      ;; num-params stays as the outer forall count — the Not-forall is NOT a
      ;; matchable param. raw-proof applied to outer params yields ¬P, then
      ;; we wrap with eq_false.
      (and (e/forall? ty)
           (let [body (e/forall-body ty)]
             (and (e/const? body) (= (e/const-name body) false-name))))
      (let [p (e/forall-type ty)
            [p-head p-args] (e/get-app-fn-args p)]
        (if (and (e/const? p-head) (= (e/const-name p-head) eq-name) (= 3 (count p-args)))
          ;; Ne a b → (a = b) = False
          ;; P is @Eq α a b, so lhs = @Eq α a b, rhs = False
          (let [lhs p  ;; @Eq α a b
                rhs (e/const' false-name [])
                [lhs-head _] (e/get-app-fn-args lhs)
                lhs-nargs (count (e/get-app-args lhs))
                head-name (when (e/const? lhs-head) (e/const-name lhs-head))]
            [{:name cname :level-params level-params
              :num-params num-params
              :lhs-pattern lhs :rhs rhs
              :eq-type (e/sort' lvl/zero)
              :kind :ne-false :priority priority :perm false :rfl false
              :head-name head-name :lhs-nargs lhs-nargs}])
          ;; General Not P → P = False
          (let [lhs p
                rhs (e/const' false-name [])
                [lhs-head _] (e/get-app-fn-args lhs)
                lhs-nargs (count (e/get-app-args lhs))
                head-name (when (e/const? lhs-head) (e/const-name lhs-head))]
            [{:name cname :level-params level-params
              :num-params num-params
              :lhs-pattern lhs :rhs rhs
              :eq-type (e/sort' lvl/zero)
              :kind :not-false :priority priority :perm false :rfl false
              :head-name head-name :lhs-nargs lhs-nargs}])))

      ;; And P Q: split into two lemmas by recursing on each conjunct
      ;; Lean 4: SimpTheorems.lean:337-344 (preprocess And)
      ;; Proof wrapping: And.left {P} {Q} proof / And.right {P} {Q} proof
      ;; We store :and-proj — a vector of {:side :left/:right, :args [P Q]}
      ;; steps to support nested And (e.g. And (And P Q) R).
      (and (e/const? head) (= (e/const-name head) and-name) (= 2 (count args)))
      (let [p (nth args 0)
            q (nth args 1)
            proj-step-left {:side :left :args [p q]}
            proj-step-right {:side :right :args [p q]}
            left-lemmas (extract-from-conclusion env cname level-params num-params
                                                 rfl-flag priority p)
            right-lemmas (extract-from-conclusion env cname level-params num-params
                                                  rfl-flag priority q)
            ;; Prepend this level's projection step to any existing :and-proj chain
            add-proj (fn [step lemma]
                       (update lemma :and-proj #(into [step] %)))]
        (into (vec (map #(add-proj proj-step-left %) left-lemmas))
              (map #(add-proj proj-step-right %)) right-lemmas))

      ;; General proposition P (not Eq/Iff/Not/Ne/And): preprocess to P = True
      ;; Lean 4: SimpTheorems.lean:353-359 (preprocess else branch)
      ;; Guard: only for Prop-typed conclusions (not Type like Bool, List, etc.)
      ;; Without this guard, functions returning Bool (like sorted) generate
      ;; Bool → True rewrites that corrupt motive bodies.
      (and (e/const? head)
           (not= (e/const-name head) true-name)
           (not= (e/const-name head) false-name)
           ;; Check the conclusion lives in Prop: look up head constant,
           ;; if it IS a type (its own type is Sort u, u > 0), skip it.
           (not (when-let [^ConstantInfo ci-head (env/lookup env (e/const-name head))]
                  (let [ht (.type ci-head)]
                    (or (e/sort? ht)
                        ;; If head type starts with a forall, check result sort
                        ;; (e.g., List : Type → Type is NOT Prop)
                        (and (e/forall? ht)
                             (let [result-type (loop [t ht]
                                                 (if (e/forall? t) (recur (e/forall-body t)) t))]
                               (and (e/sort? result-type)
                                    (not= (e/sort-level result-type) lvl/zero)))))))))
      (let [lhs ty  ;; The whole proposition becomes the LHS
            rhs (e/const' true-name [])
            [lhs-head _] (e/get-app-fn-args lhs)
            lhs-nargs (count (e/get-app-args lhs))
            head-name (when (e/const? lhs-head) (e/const-name lhs-head))]
        [{:name cname :level-params level-params :num-params num-params
          :lhs-pattern lhs :rhs rhs
          :eq-type (e/sort' lvl/zero)  ;; Prop = Sort 0
          :kind :prop-true :priority priority :perm false :rfl false
          :head-name head-name :lhs-nargs lhs-nargs}])

      :else nil)))

(defn- extract-simp-lemma
  "Extract simp lemma(s) from a constant's type.
   Returns a vector of lemma maps (possibly multiple for And splitting).
   Handles Eq, Iff, Not P (→ P = False), Ne a b (→ (a = b) = False),
   And P Q (split), and general propositions (→ P = True).
   Lean 4: SimpTheorems.lean — preprocess + shouldPreprocess + mkSimpTheoremKeys."
  [env ^ConstantInfo ci priority]
  (let [ctype (.type ci)
        cname (.name ci)
        level-params (vec (.levelParams ci))
        rfl-flag (is-rfl-proof? ci)]
    (loop [ty ctype num-params 0]
      (if (e/forall? ty)
        ;; Check for Not P pattern: forall whose body is False
        (let [body (e/forall-body ty)]
          (if (and (e/const? body) (= (e/const-name body) false-name))
            ;; This forall is Not P — handle via extract-from-conclusion
            (extract-from-conclusion env cname level-params num-params
                                     rfl-flag priority ty)
            ;; Regular forall parameter — continue stripping
            (recur body (inc num-params))))
        (extract-from-conclusion env cname level-params num-params
                                 rfl-flag priority ty)))))

;; ============================================================
;; Discrimination tree index — Lean 4's DiscrTree
;; ============================================================

(defn build-lemma-index
  "Build a discrimination tree from simp lemmas.
   Each lemma's LHS pattern is flattened to keys and inserted.
   BVar patterns become star wildcards (match anything).
   With st/env: filters instance-implicit args to stars for polymorphic matching."
  ([lemmas] (dt/make-simp-tree lemmas))
  ([st env lemmas]
   (let [sorted (sort-by (comp - :priority) lemmas)]
     (dt/make-simp-tree st env sorted))))

(defn- lookup-lemmas
  "Look up candidate lemmas from the discrimination tree.
   Flattens the query expression to keys and walks the trie,
   exploring both exact matches and star (wildcard) branches.
   With st/env: filters instance-implicit args for correct matching."
  ([lemma-index expr] (dt/lookup-simp-tree lemma-index expr))
  ([st env lemma-index expr] (dt/lookup-simp-tree st env lemma-index expr)))

;; ============================================================
;; Pattern matching for rewrite rules
;; ============================================================

(def ^:private ofnat-name (name/from-string "OfNat.ofNat"))
(defn- extract-ofnat-value
  "If expr is OfNat.ofNat _ n _, extract n as a Nat literal value. Else nil."
  [e]
  (let [[head args] (e/get-app-fn-args e)]
    (when (and (e/const? head)
               (= (e/const-name head) ofnat-name)
               (= 3 (count args)))
      (let [n-arg (nth args 1)]
        (when (e/lit-nat? n-arg)
          (e/lit-nat-val n-arg))))))

(defn- match-lemma
  "Try to match a simp lemma's LHS pattern against a target expression.
   Returns a substitution map {bvar-idx → Expr} or nil.
   Handles OfNat.ofNat ↔ literal matching (Lean 4's foldRawNatLit).
   Skips instance-implicit arguments (matched by def-eq or ignored)."
  [st pattern target num-params]
  (let [subst (atom {})
        ok (atom true)
        env (:env st)]
    (letfn [(go [p t depth]
                (when @ok
                  (cond
                    (and (e/bvar? p) (>= (e/bvar-idx p) depth))
                    (let [param-idx (- (e/bvar-idx p) depth)]
                      (if-let [existing (get @subst param-idx)]
                        (when-not (tc/is-def-eq st existing t)
                          (reset! ok false))
                        (swap! subst assoc param-idx t)))

                  ;; OfNat.ofNat pattern vs literal target
                    (and (e/app? p) (e/lit-nat? t))
                    (if-let [pv (extract-ofnat-value p)]
                      (when-not (= pv (e/lit-nat-val t))
                        (reset! ok false))
                      (reset! ok false))

                  ;; Literal pattern vs OfNat.ofNat target
                    (and (e/lit-nat? p) (e/app? t))
                    (if-let [tv (extract-ofnat-value t)]
                      (when-not (= (e/lit-nat-val p) tv)
                        (reset! ok false))
                      (reset! ok false))

                    (= (e/tag p) (e/tag t))
                    (case (e/tag p)
                      :bvar (when-not (= (e/bvar-idx p) (e/bvar-idx t)) (reset! ok false))
                      :sort nil
                      :const (when-not (= (e/const-name p) (e/const-name t)) (reset! ok false))
                      :app (let [;; Check if this arg is instance-implicit by looking at head function
                                 [p-head p-args] (e/get-app-fn-args p)
                                 [t-head t-args] (e/get-app-fn-args t)
                                 p-infos (when (and env (e/const? p-head))
                                           (dt/get-param-infos env p-head))
                               ;; If the last arg is inst-implicit, skip matching its sub-tree
                                 last-idx (dec (count p-args))
                                 skip-last (and p-infos (< last-idx (count p-infos))
                                                (= :inst-implicit (nth p-infos last-idx)))]
                             (go (e/app-fn p) (e/app-fn t) depth)
                             (when-not skip-last
                               (go (e/app-arg p) (e/app-arg t) depth)))
                      :lam (do (go (e/lam-type p) (e/lam-type t) depth)
                               (go (e/lam-body p) (e/lam-body t) (inc depth)))
                      :forall (do (go (e/forall-type p) (e/forall-type t) depth)
                                  (go (e/forall-body p) (e/forall-body t) (inc depth)))
                      :fvar (when-not (= (e/fvar-id p) (e/fvar-id t)) (reset! ok false))
                      (:lit-nat :lit-str) (when-not (= p t) (reset! ok false))
                      :proj (do (when-not (and (= (e/proj-type-name p) (e/proj-type-name t))
                                               (= (e/proj-idx p) (e/proj-idx t)))
                                  (reset! ok false))
                                (go (e/proj-struct p) (e/proj-struct t) depth))
                      (reset! ok false))

                  ;; Tags don't match structurally — try def-eq as fallback
                  ;; This handles instance-implicit args where the pattern has
                  ;; AddCommMagma.toAdd but the target has Real.instAdd (def-eq via chain)
                    :else (when-not (try (tc/is-def-eq st p t) (catch Exception _ false))
                            (reset! ok false)))))]
      (go pattern target 0))
    (when @ok @subst)))

(defn- apply-subst
  "Apply a substitution to an expression."
  [expr subst num-params]
  (if (empty? subst)
    expr
    (letfn [(go [e depth]
                (case (e/tag e)
                  :bvar (let [idx (e/bvar-idx e)]
                          (if (>= idx depth)
                            (let [param-idx (- idx depth)]
                              (if-let [val (get subst param-idx)]
                                (if (zero? depth) val (e/lift val depth 0))
                                e))
                            e))
                  :app (let [f (go (e/app-fn e) depth) a (go (e/app-arg e) depth)]
                         (if (and (identical? f (e/app-fn e)) (identical? a (e/app-arg e)))
                           e (e/app f a)))
                  :lam (let [t (go (e/lam-type e) depth) b (go (e/lam-body e) (inc depth))]
                         (if (and (identical? t (e/lam-type e)) (identical? b (e/lam-body e)))
                           e (e/lam (e/lam-name e) t b (e/lam-info e))))
                  :forall (let [t (go (e/forall-type e) depth) b (go (e/forall-body e) (inc depth))]
                            (if (and (identical? t (e/forall-type e)) (identical? b (e/forall-body e)))
                              e (e/forall' (e/forall-name e) t b (e/forall-info e))))
                  :proj (let [s (go (e/proj-struct e) depth)]
                          (if (identical? s (e/proj-struct e)) e
                              (e/proj (e/proj-type-name e) (e/proj-idx e) s)))
                  :mdata (go (e/mdata-expr e) depth)
                  e))]
      (go expr 0))))

;; ============================================================
;; Level inference
;; ============================================================

(defn- infer-level-params
  "Infer universe level assignments from matched parameter values.
   Solves level equations: if param has type Sort(succ u), and value has
   type Sort n, then u = n-1. This handles the common Sort(u+1) pattern."
  [st lemma subst]
  (let [lparams (:level-params lemma)]
    (if (empty? lparams)
      []
      (let [levels (atom (into {} (map (fn [lp] [lp lvl/zero]) lparams)))
            ;; Walk the forall telescope to get expected binder types
            ^ConstantInfo ci (env/lookup (:env st) (:name lemma))
            ctype (when ci (.type ci))]
        (loop [i 0 ty ctype]
          (when (and (< i (:num-params lemma)) ty (e/forall? ty))
            (when-let [val (get subst i)]
              (try
                (let [;; Expected binder type (e.g., Sort(succ u))
                      expected-sort (e/forall-type ty)
                      ;; Actual value type (e.g., Sort 1)
                      val-ty (tc/infer-type st val)
                      val-tw (#'tc/cached-whnf st val-ty)]
                  (when (and (e/sort? expected-sort) (e/sort? val-tw))
                    (let [expected-level (e/sort-level expected-sort)
                          actual-level (e/sort-level val-tw)]
                      ;; Solve: expected-level = actual-level
                      ;; If expected = succ(param u), then u = actual - 1
                      (doseq [lp lparams]
                        (when (= lvl/zero (get @levels lp))
                          (let [param-lvl (lvl/param lp)]
                            (cond
                              ;; Sort(u) = Sort(n) → u = n
                              (= expected-level param-lvl)
                              (swap! levels assoc lp actual-level)
                              ;; Sort(succ u) = Sort(n) → u = n-1
                              (and (lvl/succ? expected-level)
                                   (= (lvl/succ-pred expected-level) param-lvl)
                                   (lvl/succ? actual-level))
                              (swap! levels assoc lp (lvl/succ-pred actual-level))
                              ;; Sort(succ(succ u)) = Sort(n) → u = n-2
                              (and (lvl/succ? expected-level)
                                   (lvl/succ? (lvl/succ-pred expected-level))
                                   (= (lvl/succ-pred (lvl/succ-pred expected-level)) param-lvl))
                              (when (and (lvl/succ? actual-level)
                                         (lvl/succ? (lvl/succ-pred actual-level)))
                                (swap! levels assoc lp (lvl/succ-pred (lvl/succ-pred actual-level)))))))))))
                (catch Exception _ nil)))
            (recur (inc i) (e/forall-body ty))))
        (mapv (fn [lp] (get @levels lp lvl/zero)) lparams)))))

;; ============================================================
;; Discharge — recursive simp for conditional rewrites
;; ============================================================
;; Lean 4: Rewrite.lean dischargeDefault? tries:
;; 1. Find matching hypothesis in local context
;; 2. Try eqn-theorem hypothesis discharge
;; 3. Recursive simp (with depth limit)

(declare simp-expr* ac-lt? make-hyp-lemmas is-prop-type?)

(defn- try-discharge
  "Try to discharge a Prop-typed obligation (conditional rewrite side condition).
   Following Lean 4's dischargeDefault? (Rewrite.lean:626-637).

   Strategies:
   1. Find matching hypothesis in local context (assumption)
   2. Typeclass synthesis (for instance obligations)
   3. Recursive simp with fresh cache (depth-limited):
      a. If simplified to True → of_eq_true proof
      b. If simplified to Eq with def-eq sides → Eq.mpr simp-proof rfl (Lean 4: dischargeRfl)
   4. Omega fallback (for linear arithmetic side conditions)

   Returns a proof term or nil."
  [st env lemma-index config obligation-type depth]
  (let [max-depth (get config :max-discharge-depth 2)]
    (when (< depth max-depth)
      ;; Strategy 1: find matching hypothesis in local context
      (or (some (fn [[id decl]]
                  (when (and (= :local (:tag decl))
                             (try (tc/is-def-eq st (:type decl) obligation-type)
                                  (catch Exception _ false)))
                    (e/fvar id)))
                (:lctx st))
          ;; Strategy 2: typeclass synthesis (Lean 4: synthesizeInstance)
          (try
            (let [inst-index (if-let [idx (:inst-index config)]
                               (if (instance? clojure.lang.Delay idx) @idx idx)
                               (inst/build-instance-index env))]
              (inst/synthesize env inst-index obligation-type))
            (catch Exception _ nil))
          ;; Strategy 3: recursive simp with fresh cache (Lean 4: withPreservedCache)
          (try
            (let [r (simp-expr* st env lemma-index obligation-type
                                (assoc config
                                       :max-depth (min 8 (:max-depth config))
                                       :discharge-depth (inc depth)
                                       ;; Fresh cache per discharge (Lean 4: withPreservedCache)
                                       :cache (atom {})
                                       :max-steps (atom 0)))
                  rw (#'tc/cached-whnf st (:expr r))]
              (cond
                ;; 3a. Simplified to True → of_eq_true
                ;; of_eq_true : {p : Prop} → (p = True) → p
                (and (e/const? rw) (= (e/const-name rw) true-name))
                (if (:proof? r)
                  (e/app* (e/const' of-eq-true-name []) obligation-type (:proof? r))
                  ;; Def-eq to True: True.intro proves it
                  (e/const' true-intro-name []))

                ;; 3b. Simplified to Eq with def-eq sides → dischargeRfl
                ;; Lean 4: Rewrite.lean:631 — if let some p ← dischargeRfl r.expr
                (let [[h args] (e/get-app-fn-args rw)]
                  (and (e/const? h) (= (e/const-name h) eq-name) (= 3 (count args))
                       (try (tc/is-def-eq st (nth args 1) (nth args 2))
                            (catch Exception _ false))))
                (let [[_ args] (e/get-app-fn-args rw)
                      rfl-proof (e/app* (e/const' eq-refl-name
                                                  (e/const-levels (e/get-app-fn rw)))
                                        (nth args 0) (nth args 1))]
                  (if (:proof? r)
                    ;; Eq.mpr (simp-proof : obligation = (a = a)) rfl
                    (e/app* (e/const' eq-mpr-name [lvl/zero])
                            obligation-type (:expr r) (:proof? r) rfl-proof)
                    rfl-proof))

                :else nil))
            (catch Exception _ nil))
          ;; Strategy 4: omega + decide (for linear arithmetic obligations)
          ;; Lean 4 doesn't do this in dischargeDefault?, but it's essential for
          ;; our use case (inductive proofs with arithmetic side conditions).
          (try
            (let [omega-check (requiring-resolve 'ansatz.tactic.omega/omega-check)
                  omega-st (assoc (tc/mk-tc-state env) :lctx (:lctx st))]
              (when (omega-check omega-st obligation-type (:lctx st))
                ;; Omega says provable — try decide to certify the proof term
                (let [inst-index (if-let [idx (:inst-index config)]
                                   (if (instance? clojure.lang.Delay idx) @idx idx)
                                   (inst/build-instance-index env))
                      decidable-goal (e/app (e/const' decidable-name [])
                                            obligation-type)
                      inst (inst/synthesize* st env inst-index decidable-goal 0)]
                  (when inst
                    (let [bt-name (name/from-string "Bool.true")
                          decide-term (e/app* (e/const' decidable-decide-name [])
                                              obligation-type inst)
                          result (#'tc/cached-whnf st decide-term)
                          bool-true-val (e/const' bt-name [])]
                      (when (and (e/const? result)
                                 (= (e/const-name result) bt-name))
                        ;; of_decide_eq_true P inst (Eq.refl true)
                        (let [of-decide-name (name/from-string "of_decide_eq_true")
                              u1 (lvl/succ lvl/zero)
                              bool-type (e/const' bool-name [])
                              eq-refl-proof (e/app* (e/const' eq-refl-name [u1])
                                                    bool-type bool-true-val)]
                          (e/app* (e/const' of-decide-name [])
                                  obligation-type inst eq-refl-proof))))))))
            (catch Exception _ nil))))))

;; ============================================================
;; Rewriting engine
;; ============================================================

(declare find-eqn-theorems)

(defn- try-rewrite-step
  "Try to rewrite an expression using the lemma index.
   Returns a SimpResult or nil.
   Following Lean 4's rewrite? with synthesizeArgs + discharge."
  [st env lemma-index expr config]
  (let [;; Disc tree candidates + direct equation theorem lookup by head constant.
        ;; Direct lookup avoids disc tree star-arity mismatch for equation theorems.
        dt-candidates (lookup-lemmas st env lemma-index expr)
        head-fn (e/get-app-fn expr)
        eqn-candidates (when (e/const? head-fn)
                         (when-let [eqns (find-eqn-theorems env (e/const-name head-fn))]
                           (vec (mapcat (fn [eqn-name]
                                          (when-let [ci (env/lookup env eqn-name)]
                                            (extract-simp-lemma env ci 50)))
                                        eqns))))
        ;; Lean 4: rewriteUsingIndex? sorts candidates by priority (descending)
        ;; before trying them. This ensures hypothesis rewrites (priority 2000)
        ;; fire before equation theorems (priority 50), letting the IH match
        ;; before sorted/insertSorted get unfolded.
        candidates (sort-by (comp - :priority)
                            (if (seq eqn-candidates)
                              (distinct (concat dt-candidates eqn-candidates))
                              dt-candidates))]
    (some (fn [lemma]
            (when-let [subst (match-lemma st (:lhs-pattern lemma) expr (:num-params lemma))]
              (let [num-params (:num-params lemma)
                    matched (count subst)]
                (when (>= matched (- num-params 3))
                  ;; Try to fill missing params via discharge
                  (let [full-subst
                        (if (= matched num-params)
                          subst
                          ;; Walk forall telescope with progressive instantiation.
                          ;; Uses instantiate1 to keep bvar indices correct.
                          (let [ci (env/lookup env (:name lemma))
                                ctype (when ci (.type ^ConstantInfo ci))
                                ;; Map forall-index → value from subst (body bvar to forall index)
                                idx->val (into {} (map (fn [[bvar-idx val]]
                                                         [(- num-params bvar-idx 1) val])
                                                       subst))]
                            (loop [s subst i 0 ty ctype]
                              (if (or (>= i num-params) (nil? ty) (not (e/forall? ty)))
                                s
                                (if-let [val (get idx->val i)]
                                  ;; Already resolved — instantiate and advance
                                  (recur s (inc i) (e/instantiate1 (e/forall-body ty) val))
                                  ;; Missing — try instance synthesis or discharge
                                  (let [param-type (e/forall-type ty)
                                        binfo (e/forall-info ty)
                                        resolved
                                        (if (= binfo :inst-implicit)
                                          (try
                                            (let [[head args] (e/get-app-fn-args param-type)]
                                              (when (and (e/const? head) (seq args))
                                                (let [cn (name/->string (e/const-name head))
                                                      ta (first args)
                                                      [th _] (when ta (e/get-app-fn-args ta))
                                                      tn (when (e/const? th) (name/->string (e/const-name th)))
                                                      f (requiring-resolve 'ansatz.core/resolve-basic-instance)]
                                                  (when tn (f env cn tn ta)))))
                                            (catch Exception _ nil))
                                          (try-discharge st env lemma-index config
                                                         param-type
                                                         (or (:discharge-depth config) 0)))]
                                    (if resolved
                                      (recur (assoc s (- num-params i 1) resolved)
                                             (inc i) (e/instantiate1 (e/forall-body ty) resolved))
                                      ;; Not resolved — create a placeholder fvar
                                      ;; so later param-types are properly instantiated
                                      ;; (Lean 4 uses metavariables for this)
                                      (let [placeholder (e/fvar (+ 7000000 i))]
                                        (recur s (inc i)
                                               (e/instantiate1 (e/forall-body ty) placeholder))))))))))]
                    (let [param-vals (mapv #(get full-subst %) (range num-params))]
                      (when (every? some? param-vals)
                        (let [rhs-raw (apply-subst (:rhs lemma) full-subst num-params)
                              ;; Instantiate level params in RHS
                              inst-levels-for-rhs (infer-level-params st lemma full-subst)
                              level-subst (zipmap (:level-params lemma) inst-levels-for-rhs)
                              rhs (if (seq level-subst)
                                    (e/instantiate-level-params rhs-raw level-subst)
                                    rhs-raw)
                              ;; Perm check (Lean 4: Rewrite.lean:142-149)
                              ;; For permutative lemmas, only allow if RHS < expr
                              perm-ok (if (:perm lemma)
                                        (ac-lt? env rhs expr)
                                        true)]
                          (when perm-ok
                            ;; RFL optimization (Lean 4: useImplicitDefEqProof)
                            ;; If theorem is rfl, skip proof construction
                            (if (:rfl lemma)
                              (mk-result rhs)  ;; proof? = nil (definitional equality)
                              (let [inst-levels (infer-level-params st lemma full-subst)
                                    ;; For hypothesis lemmas (from local context), use fvar as proof.
                                    ;; For named lemmas (from env), use const.
                                    base-proof (if-let [fid (:hyp-fvar-id lemma)]
                                                 (e/fvar fid)
                                                 (reduce e/app
                                                         (e/const' (:name lemma) inst-levels)
                                                         (reverse param-vals)))
                                    ;; And projection: if lemma came from And splitting,
                                    ;; apply the chain of And.left/And.right projections.
                                    ;; And.left : {a b : Prop} → And a b → a
                                    ;; And.right : {a b : Prop} → And a b → b
                                    ;; :and-proj is a vec of {:side :left/:right, :args [P Q]}
                                    ;; from outermost to innermost projection.
                                    raw-proof (if-let [proj-chain (seq (:and-proj lemma))]
                                                (reduce (fn [proof {:keys [side args]}]
                                                          (let [p-inst (apply-subst (nth args 0) full-subst num-params)
                                                                q-inst (apply-subst (nth args 1) full-subst num-params)]
                                                            (case side
                                                              :left (e/app* (e/const' and-left-name [])
                                                                            p-inst q-inst proof)
                                                              :right (e/app* (e/const' and-right-name [])
                                                                             p-inst q-inst proof))))
                                                        base-proof proj-chain)
                                                base-proof)
                                    ;; Proof wrapping depends on lemma kind:
                                    ;; :eq        → raw-proof is already P = Q
                                    ;; :iff       → propext P Q (raw-proof : P ↔ Q) → P = Q
                                    ;; :prop-true → eq_true P (raw-proof : P) → (P = True)
                                    ;; :not-false → eq_false P (raw-proof : ¬P) → (P = False)
                                    ;; :ne-false  → eq_false (a=b) (raw-proof : ¬(a=b)) → ((a=b) = False)
                                    proof-term (case (:kind lemma)
                                                 :iff (e/app* (e/const' propext-name [])
                                                              (apply-subst (:lhs-pattern lemma) full-subst num-params)
                                                              rhs raw-proof)
                                                 :prop-true (e/app* (e/const' eq-true-name [])
                                                                    expr  ;; the instantiated proposition
                                                                    raw-proof)
                                                 :not-false (e/app* (e/const' eq-false-name [])
                                                                    expr  ;; P (the proposition)
                                                                    raw-proof)
                                                 :ne-false (e/app* (e/const' eq-false-name [])
                                                                   expr  ;; @Eq α a b
                                                                   raw-proof)
                                                 raw-proof)]
                                (mk-result rhs proof-term))))))))))))
          candidates)))

;; ============================================================
;; Built-in simprocs — arithmetic reduction
;; ============================================================

;; Nat simproc names
(def ^:private nat-add-name (name/from-string "Nat.add"))
(def ^:private nat-mul-name (name/from-string "Nat.mul"))
(def ^:private nat-sub-name (name/from-string "Nat.sub"))
(def ^:private nat-div-name (name/from-string "Nat.div"))
(def ^:private nat-mod-name (name/from-string "Nat.mod"))
(def ^:private nat-succ-name (name/from-string "Nat.succ"))
(def ^:private nat-ble-name (name/from-string "Nat.ble"))
(def ^:private nat-beq-name (name/from-string "Nat.beq"))
(def ^:private bool-true-name (name/from-string "Bool.true"))
(def ^:private bool-false-name (name/from-string "Bool.false"))

;; Int simproc names (Lean 4: BuiltinSimprocs/Int.lean)
(def ^:private int-add-name (name/from-string "Int.add"))
(def ^:private int-mul-name (name/from-string "Int.mul"))
(def ^:private int-sub-name (name/from-string "Int.sub"))
(def ^:private int-neg-name (name/from-string "Int.neg"))
(def ^:private int-div-name (name/from-string "Int.div"))
(def ^:private int-mod-name (name/from-string "Int.mod"))
(def ^:private int-ofnat-name (name/from-string "Int.ofNat"))
(def ^:private int-negsucc-name (name/from-string "Int.negSucc"))

(defn- whnf-to-nat [st e]
  (let [w (#'tc/cached-whnf st e)]
    (when (e/lit-nat? w) (e/lit-nat-val w))))

(defn- whnf-to-int
  "Try to reduce an expression to an Int literal via WHNF.
   Int values in Ansatz are represented as Int.ofNat n or Int.negSucc n."
  [st e]
  (let [w (#'tc/cached-whnf st e)
        [head args] (e/get-app-fn-args w)]
    (cond
      ;; Nat literal → non-negative Int
      (e/lit-nat? w) (e/lit-nat-val w)
      ;; Int.ofNat n
      (and (e/const? head) (= (e/const-name head) int-ofnat-name) (= 1 (count args)))
      (whnf-to-nat st (nth args 0))
      ;; Int.negSucc n → -(n+1)
      (and (e/const? head) (= (e/const-name head) int-negsucc-name) (= 1 (count args)))
      (when-let [n (whnf-to-nat st (nth args 0))]
        (- (inc n)))
      :else nil)))

(defn- int-to-expr
  "Convert a Clojure integer to a Ansatz Int expression."
  [n]
  (if (>= n 0)
    (e/app (e/const' int-ofnat-name []) (e/lit-nat n))
    (e/app (e/const' int-negsucc-name []) (e/lit-nat (dec (- n))))))

(defn- try-nat-literal-reduce
  "Reduce arithmetic on Nat literals.
   Lean 4: BuiltinSimprocs/Nat.lean."
  [st expr]
  (let [[head args] (e/get-app-fn-args expr)]
    (when (e/const? head)
      (let [hname (e/const-name head) nargs (count args)]
        (cond
          (and (= hname nat-succ-name) (= 1 nargs))
          (when-let [n (whnf-to-nat st (nth args 0))]
            (mk-result (e/lit-nat (inc n))))

          (= 2 nargs)
          (when-let [a (whnf-to-nat st (nth args 0))]
            (when-let [b (whnf-to-nat st (nth args 1))]
              (cond
                (= hname nat-add-name) (mk-result (e/lit-nat (+ a b)))
                (= hname nat-mul-name) (mk-result (e/lit-nat (* a b)))
                (= hname nat-sub-name) (mk-result (e/lit-nat (max 0 (- a b))))
                (= hname nat-div-name) (when (pos? b) (mk-result (e/lit-nat (quot a b))))
                (= hname nat-mod-name) (when (pos? b) (mk-result (e/lit-nat (mod a b))))
                (= hname nat-ble-name)
                (mk-result (e/const' (if (<= a b) bool-true-name bool-false-name) []))
                (= hname nat-beq-name)
                (mk-result (e/const' (if (= a b) bool-true-name bool-false-name) []))
                :else nil)))

          :else nil)))))

(defn- try-int-literal-reduce
  "Reduce arithmetic on Int literals.
   Lean 4: BuiltinSimprocs/Int.lean."
  [st expr]
  (let [[head args] (e/get-app-fn-args expr)]
    (when (e/const? head)
      (let [hname (e/const-name head) nargs (count args)]
        (cond
          ;; Unary: Int.neg
          (and (= hname int-neg-name) (= 1 nargs))
          (when-let [n (whnf-to-int st (nth args 0))]
            (mk-result (int-to-expr (- n))))

          ;; Binary: Int.add, Int.mul, Int.sub, Int.div, Int.mod
          (= 2 nargs)
          (when-let [a (whnf-to-int st (nth args 0))]
            (when-let [b (whnf-to-int st (nth args 1))]
              (cond
                (= hname int-add-name) (mk-result (int-to-expr (+ a b)))
                (= hname int-mul-name) (mk-result (int-to-expr (* a b)))
                (= hname int-sub-name) (mk-result (int-to-expr (- a b)))
                (= hname int-div-name) (when-not (zero? b) (mk-result (int-to-expr (quot a b))))
                (= hname int-mod-name) (when-not (zero? b) (mk-result (int-to-expr (mod a b))))
                :else nil)))

          :else nil)))))

;; ============================================================
;; AC-compatible LPO term ordering — Lean 4's ACLt (ACLt.lean)
;; ============================================================
;; Prevents infinite loops for commutative rewrites (e.g., a + b = b + a)
;; by only allowing the rewrite if RHS < LHS in a term ordering.
;;
;; This is a proper Lexicographic Path Ordering (LPO) following Lean 4:
;; - Flattens applications and compares arg-by-arg
;; - Skips instance-implicit arguments (avoids issue #972)
;; - Uses proper LPO conditions: someChildGe + allChildrenLt + lexSameCtor

(def ^:private ctor-weight
  "Lean 4's Expr.ctorWeight — constructor weights for term ordering."
  {:bvar 0 :fvar 1 :mvar 2 :sort 3 :const 4 :lit-nat 5 :lit-str 5
   :mdata 6 :proj 7 :app 8 :lam 9 :forall 10 :let 11})

(defn- ac-lt?
  "Lean 4's acLt: a < b in AC-compatible LPO term ordering.
   env is used to look up parameter info for skipping instance args.
   Returns true if a is strictly smaller than b."
  ([a b] (ac-lt? nil a b))
  ([env a b]
   (letfn [(lt [a b]
             (cond
               ;; Pointer/structural equality → not less
               (identical? a b) false
               (= a b) false
               ;; Strip mdata (Lean 4: ignore metadata)
               (e/mdata? a) (lt (e/mdata-expr a) b)
               (e/mdata? b) (lt a (e/mdata-expr b))
               :else (lpo a b)))

           (lt-pair [a1 a2 b1 b2]
             (cond
               (lt a1 b1) true
               (lt b1 a1) false
               :else (lt a2 b2)))

           (get-param-infos [f nargs]
             ;; Lean 4: getFunInfoNArgs — get binder infos for f's params.
             ;; We use dt/get-param-infos for const heads.
             (when env (dt/get-param-infos env f)))

           (instance-arg? [infos i]
             (and infos (< i (count infos)) (= :inst-implicit (nth infos i))))

           (lt-app [a b]
             ;; Lean 4: ACLt.ltApp — flatten apps, compare fn then args
             ;; skipping instance-implicit arguments.
             (let [a-fn (e/get-app-fn a) b-fn (e/get-app-fn b)]
               (cond
                 (lt a-fn b-fn) true
                 (lt b-fn a-fn) false
                 :else
                 (let [a-args (e/get-app-args a) b-args (e/get-app-args b)
                       na (count a-args) nb (count b-args)]
                   (cond
                     (< na nb) true
                     (> na nb) false
                     :else
                     (let [infos (get-param-infos a-fn na)]
                       ;; Lexicographic comparison skipping instance args
                       (loop [i 0]
                         (if (>= i na)
                           false  ;; all equal
                           (if (instance-arg? infos i)
                             (recur (inc i))
                             (let [ai (nth a-args i) bi (nth b-args i)]
                               (cond
                                 (lt ai bi) true
                                 (lt bi ai) false
                                 :else (recur (inc i)))))))))))))

           (lex-same-ctor [a b]
             ;; Lean 4: ACLt.lexSameCtor — compare within same constructor
             (let [ta (e/tag a)]
               (case ta
                 :bvar (< (e/bvar-idx a) (e/bvar-idx b))
                 :fvar (< (e/fvar-id a) (e/fvar-id b))
                 :lit-nat (< (e/lit-nat-val a) (e/lit-nat-val b))
                 :lit-str (neg? (compare (str (e/lit-str-val a)) (str (e/lit-str-val b))))
                 :const (neg? (compare (name/->string (e/const-name a))
                                       (name/->string (e/const-name b))))
                 :sort (< (hash (e/sort-level a)) (hash (e/sort-level b)))
                 :app (lt-app a b)
                 :proj (if (not= (e/proj-idx a) (e/proj-idx b))
                         (< (e/proj-idx a) (e/proj-idx b))
                         (lt (e/proj-struct a) (e/proj-struct b)))
                 :lam (lt-pair (e/lam-type a) (e/lam-body a)
                               (e/lam-type b) (e/lam-body b))
                 :forall (lt-pair (e/forall-type a) (e/forall-body a)
                                  (e/forall-type b) (e/forall-body b))
                 false)))

           (all-children-lt [a b]
             ;; Lean 4: ACLt.allChildrenLt — all children of a are < b
             (let [ta (e/tag a)]
               (case ta
                 :app (let [a-fn (e/get-app-fn a)
                            a-args (e/get-app-args a)
                            infos (get-param-infos a-fn (count a-args))]
                        (loop [i 0]
                          (if (>= i (count a-args))
                            true
                            (if (instance-arg? infos i)
                              (recur (inc i))
                              (if (lt (nth a-args i) b)
                                (recur (inc i))
                                false)))))
                 :proj (lt (e/proj-struct a) b)
                 :lam (and (lt (e/lam-type a) b) (lt (e/lam-body a) b))
                 :forall (and (lt (e/forall-type a) b) (lt (e/forall-body a) b))
                 ;; Atomic — no children → trivially true
                 true)))

           (lpo [a b]
             ;; Lean 4: ACLt.lpo — the core LPO algorithm
             ;; Case 1: a < b if some child of b >= a
             (if (not (all-children-lt b a))
               true
               (let [wa (get ctor-weight (e/tag a) 12)
                     wb (get ctor-weight (e/tag b) 12)]
                 (cond
                   (> wa wb) false
                   ;; Case 2: a < b if ctorWeight(a) < ctorWeight(b) and all children of a < b
                   (not (all-children-lt a b)) false
                   (< wa wb) true
                   ;; Case 3: same ctor, lex comparison, all children of a < b
                   :else (lex-same-ctor a b)))))]
     (lt a b))))

;; ============================================================
;; OfNat literal folding — Lean 4's foldRawNatLit
;; ============================================================

;; ============================================================
;; Core simprocs — Lean 4's BuiltinSimprocs/Core.lean
;; ============================================================

(def ^:private ite-name (name/from-string "ite"))
(def ^:private dite-name (name/from-string "dite"))

(defn- try-reduce-ite
  "Reduce if-then-else when condition is True or False.
   Lean 4: reduceIte/reduceDIte from BuiltinSimprocs/Core.lean.
   ite {α} (p : Prop) [inst : Decidable p] (a b : α) → α
   When p reduces to True: return a. When False: return b."
  [st expr]
  (let [[head args] (e/get-app-fn-args expr)]
    (when (e/const? head)
      (let [hname (e/const-name head)]
        (cond
          ;; ite : 5 args (α, p, inst, a, b)
          (and (= hname ite-name) (= 5 (count args)))
          (let [cond-expr (nth args 1)
                cond-whnf (#'tc/cached-whnf st cond-expr)]
            (cond
              (and (e/const? cond-whnf) (= (e/const-name cond-whnf) true-name))
              (mk-result (nth args 3))  ;; return 'a' (then-branch)
              (and (e/const? cond-whnf) (= (e/const-name cond-whnf) false-name))
              (mk-result (nth args 4))  ;; return 'b' (else-branch)
              :else nil))

          ;; dite : 5 args (α, p, inst, a : p → α, b : ¬p → α)
          (and (= hname dite-name) (= 5 (count args)))
          (let [cond-expr (nth args 1)
                cond-whnf (#'tc/cached-whnf st cond-expr)]
            (cond
              (and (e/const? cond-whnf) (= (e/const-name cond-whnf) true-name))
              ;; Apply 'a' to True.intro
              (mk-result (e/app (nth args 3) (e/const' true-intro-name [])))
              (and (e/const? cond-whnf) (= (e/const-name cond-whnf) false-name))
              ;; For False case: b takes ¬False which is True → False → something
              ;; This is complex; for now rely on WHNF
              nil
              :else nil))

          :else nil)))))

(defn- try-reduce-ctor-eq
  "Reduce constructor equality to False when constructors differ.
   Lean 4: reduceCtorEq from BuiltinSimprocs/Core.lean.
   Also handles Nat literal disequality: 0 = 1 → False."
  [st expr]
  (let [[head args] (e/get-app-fn-args expr)]
    (when (and (e/const? head)
               (= (e/const-name head) eq-name)
               (= 3 (count args)))
      (let [lhs (#'tc/cached-whnf st (nth args 1))
            rhs (#'tc/cached-whnf st (nth args 2))]
        (cond
          ;; Different Nat literals → False
          (and (e/lit-nat? lhs) (e/lit-nat? rhs)
               (not= (e/lit-nat-val lhs) (e/lit-nat-val rhs)))
          (mk-result (e/const' false-name []))

          ;; Different String literals → False
          (and (e/lit-str? lhs) (e/lit-str? rhs)
               (not= (e/lit-str-val lhs) (e/lit-str-val rhs)))
          (mk-result (e/const' false-name []))

          ;; Different constructors
          :else
          (let [[lh _] (e/get-app-fn-args lhs)
                [rh _] (e/get-app-fn-args rhs)]
            (when (and (e/const? lh) (e/const? rh)
                       (not= (e/const-name lh) (e/const-name rh)))
          ;; Check if they're constructors of the same type
              (let [env (:env st)
                    lci (env/lookup env (e/const-name lh))
                    rci (env/lookup env (e/const-name rh))]
                (when (and lci rci
                           (.isCtor ^ConstantInfo lci)
                           (.isCtor ^ConstantInfo rci))
              ;; Both are constructors — check if same inductive
              ;; Constructor name is Ind.ctorName, parent is Ind
                  (let [lparent (name/name-prefix (e/const-name lh))
                        rparent (name/name-prefix (e/const-name rh))]
                    (when (and lparent rparent (= lparent rparent))
                  ;; Different constructors of same inductive → Eq is False
                      (mk-result (e/const' false-name [])))))))))))))

;; ============================================================
;; Match/recursor reduction simproc
;; ============================================================

;; ============================================================
;; Ground evaluation — Lean 4's sevalGround (Rewrite.lean:426-455)
;; ============================================================
;; For fully concrete expressions (no free vars), unfold step by step
;; using equation theorems: f.eq_1, f.eq_2, ...

(defn- find-eqn-theorems
  "Find equation theorems for a declaration: declName.eq_1, eq_1t, eq_1f, eq_2, ...
   Lean 4: getEqnsFor? discovers these lazily.
   Also finds conditional variants (eq_Nt, eq_Nf) for Bool-split branches."
  [env decl-name]
  (loop [i 1 result []]
    (let [base-name (name/mk-str decl-name (str "eq_" i))
          base-ci (env/lookup env base-name)
          ;; Also check conditional variants
          true-name (name/mk-str decl-name (str "eq_" i "t"))
          true-ci (env/lookup env true-name)
          false-name (name/mk-str decl-name (str "eq_" i "f"))
          false-ci (env/lookup env false-name)
          found (cond-> []
                  base-ci (conj base-name)
                  true-ci (conj true-name)
                  false-ci (conj false-name))]
      (if (seq found)
        (recur (inc i) (into result found))
        (when (seq result) result)))))

(defn- try-ground-eval
  "Try to evaluate a ground term using equation theorems.
   Lean 4: sevalGround from Rewrite.lean.
   Only applies to fully concrete expressions (no fvars, no loose bvars).
   Tries each equation theorem in order; first match wins."
  [st env expr]
  ;; Guard: must be ground (no free variables)
  (when (and (not (e/has-fvar-flag expr))
             (not (e/has-loose-bvars? expr)))
    (let [head (e/get-app-fn expr)]
      (when (e/const? head)
        (let [decl-name (e/const-name head)]
          ;; Find equation theorems for this function
          (when-let [eqn-names (find-eqn-theorems env decl-name)]
            ;; Try each equation theorem in order (first match wins)
            (some (fn [eqn-name]
                    (when-let [^ConstantInfo ci (env/lookup env eqn-name)]
                      (let [lemma (first (extract-simp-lemma env ci 500))]
                        (when lemma
                          (when-let [subst (match-lemma st (:lhs-pattern lemma) expr
                                                        (:num-params lemma))]
                            (when (= (count subst) (:num-params lemma))
                              (let [rhs (apply-subst (:rhs lemma) subst (:num-params lemma))
                                    param-vals (mapv #(get subst %) (range (:num-params lemma)))
                                    inst-levels (infer-level-params st lemma subst)
                                    proof (reduce e/app
                                                  (e/const' eqn-name inst-levels)
                                                  (reverse param-vals))]
                                (mk-result rhs proof))))))))
                  eqn-names)))))))

(def ^:private hpow-name (name/from-string "HPow.hPow"))
(def ^:private hdiv-name (name/from-string "HDiv.hDiv"))

(defn- try-hpow-reduce
  "Reduce HPow.hPow and HDiv.hDiv on ground Nat literals.
   HPow.hPow args: [α β γ inst a b] → a^b
   HDiv.hDiv args: [α β γ inst a b] → a/b"
  [st expr]
  (let [[head args] (e/get-app-fn-args expr)]
    (when (and (e/const? head) (= 6 (count args)))
      (let [hname (e/const-name head)
            a (whnf-to-nat st (nth args 4))
            b (whnf-to-nat st (nth args 5))]
        (when (and a b)
          (cond
            (= hname hpow-name)
            (mk-result (e/lit-nat (.pow (biginteger a) (int b))))
            (= hname hdiv-name)
            (when (pos? b) (mk-result (e/lit-nat (quot a b))))
            :else nil))))))

(defn- try-simp-using-decide
  "Lean 4's simpUsingDecide (Rewrite.lean:275-290).
   For a proposition P (without free/bound variables, not already True/False):
   1. Synthesize a Decidable P instance
   2. Build @Decidable.decide P inst and WHNF it
   3. If it reduces to Bool.true  → return {P = True, proof: eq_true_of_decide P inst (Eq.refl true)}
   4. If it reduces to Bool.false → return {P = False, proof: eq_false_of_decide P inst (Eq.refl false)}
   5. Otherwise return nil"
  [st expr config]
  (when (and (:decide? config true)
             ;; Guard: skip if expr has free variables or bound variables
             (not (e/has-fvar-flag expr))
             (not (e/has-loose-bvars? expr))
             ;; Guard: expr must be a Prop (Lean 4: simpUsingDecide only for Props)
             (is-prop-type? st expr)
             ;; Guard: skip if eq_true_of_decide not in env (e.g., Init-only env)
             (env/lookup (:env st) eq-true-of-decide-name))
    ;; Guard: skip if already True or False
    (let [[head _] (e/get-app-fn-args expr)]
      (when-not (and (e/const? head)
                     (or (= (e/const-name head) true-name)
                         (= (e/const-name head) false-name)))
        (try
          (let [env (:env st)
                inst-index (if-let [idx (:inst-index config)]
                             (if (instance? clojure.lang.Delay idx) @idx idx)
                             (inst/build-instance-index env))
                decidable-goal (e/app (e/const' decidable-name []) expr)
                inst (inst/synthesize* st env inst-index decidable-goal 0)]
            (when inst
              (let [decide-term (e/app* (e/const' decidable-decide-name []) expr inst)
                    result (#'tc/cached-whnf st decide-term)
                    u1 (lvl/succ lvl/zero)
                    bool-type (e/const' bool-name [])
                    bool-true-val (e/const' bool-true-name [])
                    bool-false-val (e/const' bool-false-name [])]
                (cond
                  ;; reduces to Bool.true → P = True
                  (and (e/const? result) (= (e/const-name result) bool-true-name))
                  (let [eq-refl-proof (e/app* (e/const' eq-refl-name [u1]) bool-type bool-true-val)
                        proof (e/app* (e/const' eq-true-of-decide-name []) expr inst eq-refl-proof)]
                    (mk-result (e/const' true-name []) proof))

                  ;; reduces to Bool.false → P = False
                  (and (e/const? result) (= (e/const-name result) bool-false-name))
                  (let [eq-refl-proof (e/app* (e/const' eq-refl-name [u1]) bool-type bool-false-val)
                        proof (e/app* (e/const' eq-false-of-decide-name []) expr inst eq-refl-proof)]
                    (mk-result (e/const' false-name []) proof))

                  :else nil))))
          (catch Exception _ nil))))))

(declare try-fold-bool-and)

(defn- try-simproc
  "Try built-in simplification procedures, then user-registered simprocs.
   Lean 4: postDefault pipeline order:
   1. rewritePost (handled separately)
   2. userPostSimprocs (via config/*simprocs*)
   3. simpGround — equation theorem unfolding for ground terms
   4. simpArith (we have omega externally)
   5. simpUsingDecide — decide on ground decidable propositions"
  [st expr config & {:keys [env lemma-index]}]
  (or (try-nat-literal-reduce st expr)
      (try-int-literal-reduce st expr)
      (try-hpow-reduce st expr)
      (try-reduce-ite st expr)
      (try-reduce-ctor-eq st expr)
      ;; Bool.rec → Bool.and folding inside (Eq Bool (Bool.rec ...) Bool.true).
      ;; Folds the inner Bool.rec to Bool.and so Bool.and_eq_true can match.
      ;; Only fires in this specific context — standalone Bool.rec is handled
      ;; by simpMatch for discriminant simplification.
      (let [[eq-head eq-args] (e/get-app-fn-args expr)]
        (when (and (e/const? eq-head) (= (e/const-name eq-head) eq-name) (= 3 (count eq-args))
                   (e/const? (nth eq-args 0)) (= (name/->string (e/const-name (nth eq-args 0))) "Bool")
                   (e/const? (nth eq-args 2)) (= (name/->string (e/const-name (nth eq-args 2))) "Bool.true"))
          (when-let [folded (try-fold-bool-and st (nth eq-args 1))]
            ;; Rebuild the Eq with the folded inner expression
            (mk-result (e/app* eq-head (nth eq-args 0) (:expr folded) (nth eq-args 2))))))
      ;; simpMatch (Lean 4: Simp/Rewrite.lean): Handle stuck Bool.rec
      (let [[head args] (e/get-app-fn-args expr)]
        (when (and (e/const? head)
                   (= (name/->string (e/const-name head)) "Bool.rec")
                   (= 4 (count args)))
          (let [motive (nth args 0) fc (nth args 1) tc (nth args 2) discr (nth args 3)
                bool-type (e/const' (name/from-string "Bool") [])
                bool-false (e/const' (name/from-string "Bool.false") [])
                bool-true (e/const' (name/from-string "Bool.true") [])]
            (or
             ;; Strategy 1: branches are def-eq → eliminate Bool.rec
             (when (try (tc/is-def-eq st fc tc) (catch Exception _ false))
               (mk-result fc))
             ;; Strategy 2: simpMatch — simplify discriminant with full simp.
             ;; Lean 4: simpMatch (Simp/SimpMatch.lean) applies full simp to the
             ;; discriminant even though CongrArgKind marks it :fixed. If the
             ;; discriminant reduces to true/false, the Bool.rec reduces.
             (when (and env lemma-index)
               (try
                 (let [d-result (simp-expr* st env lemma-index discr
                                            (assoc config
                                                   :max-depth (min 10 (:max-depth config))
                                                   :cache (atom {})
                                                   :max-steps (atom 0)))
                       dw (#'tc/cached-whnf st (:expr d-result))]
                   (cond
                     ;; Discriminant reduced to true → return tc (true branch)
                     (and (e/const? dw) (= (e/const-name dw)
                                           (name/from-string "Bool.true")))
                     (mk-result tc)
                     ;; Discriminant reduced to false → return fc (false branch)
                     (and (e/const? dw) (= (e/const-name dw)
                                           (name/from-string "Bool.false")))
                     (mk-result fc)
                     ;; Discriminant changed but didn't reduce to true/false
                     ;; → rebuild Bool.rec with simplified discriminant
                     (not (identical? (:expr d-result) discr))
                     (mk-result (e/app* head motive fc tc (:expr d-result)))
                     :else nil))
                 (catch Exception _ nil)))
             ;; Strategy 3: Bool.rec identity — Bool.rec (fun _ => Bool) false true b = b
             ;; Lean 4: simpMatch recognizes when the recursor is the identity.
             ;; Proof: Bool.rec (fun b => Eq Bool (Bool.rec ... b) b) rfl rfl discr
             (when (and (try (tc/is-def-eq st fc bool-false) (catch Exception _ false))
                        (try (tc/is-def-eq st tc bool-true) (catch Exception _ false)))
               (let [rec-level (first (e/const-levels head))
                     ;; The motive for the proof:
                     ;; fun b => Eq Bool (Bool.rec (fun _ => Bool) false true b) b
                     eq-motive (e/lam "b" bool-type
                                 (e/app* (e/const' (name/from-string "Eq") [(lvl/succ lvl/zero)])
                                         bool-type
                                         (e/app* (e/const' (name/from-string "Bool.rec") [rec-level])
                                                 motive fc tc (e/bvar 0))
                                         (e/bvar 0))
                                 :default)
                     ;; rfl : false = false and rfl : true = true
                     rfl-false (e/app* (e/const' eq-refl-name [(lvl/succ lvl/zero)])
                                       bool-type bool-false)
                     rfl-true (e/app* (e/const' eq-refl-name [(lvl/succ lvl/zero)])
                                      bool-type bool-true)
                     ;; Bool.rec eq-motive rfl-false rfl-true discr
                     proof (e/app* (e/const' (name/from-string "Bool.rec") [lvl/zero])
                                   eq-motive rfl-false rfl-true discr)]
                 (mk-result discr proof)))))))
      (try-ground-eval st (:env st) expr)
      (try-simp-using-decide st expr config)
      ;; User-registered simprocs: dynamic var + persistent registry
      (some (fn [sp]
              (try (sp st expr)
                   (catch Exception _ nil)))
            (concat config/*simprocs*
                    (try (deref @(requiring-resolve 'ansatz.core/simproc-registry))
                         (catch Exception _ []))))))

;; ============================================================
;; Reduction
;; ============================================================

(defn- try-fold-bool-and
  "Fold Bool.rec false b a back to Bool.and a b.
   This is needed because equation theorems produce Bool.rec (WHNF-expanded)
   but simp lemmas like Bool.and_eq_true expect Bool.and (pre-WHNF).
   The fold is a def-eq (Bool.and unfolds to Bool.rec), so proof? = nil.
   Lean 4 handles this implicitly since disc tree uses whnfR on keys."
  [st expr]
  (let [[head args] (e/get-app-fn-args expr)]
    (when (and (e/const? head)
               (= (name/->string (e/const-name head)) "Bool.rec")
               (= 4 (count args)))
      (let [motive (nth args 0) fc (nth args 1) tc (nth args 2) discr (nth args 3)]
        ;; Check pattern: Bool.rec (fun _ => Bool) false b a → Bool.and a b
        (when (and (e/lam? motive)
                   (let [mt (e/lam-type motive) mb (e/lam-body motive)]
                     (and (e/const? mt) (= (name/->string (e/const-name mt)) "Bool")
                          (e/const? mb) (= (name/->string (e/const-name mb)) "Bool")))
                   (e/const? fc)
                   (= (name/->string (e/const-name fc)) "Bool.false"))
          ;; Fold: Bool.rec false tc discr → Bool.and discr tc
          (let [bool-and (e/const' (name/from-string "Bool.and") [])]
            (when (env/lookup (:env st) (name/from-string "Bool.and"))
              (mk-result (e/app* bool-and discr tc)))))))))

(defn- try-reduce-fvar [st expr]
  (when (e/fvar? expr)
    (let [id (e/fvar-id expr)
          decl (red/lctx-lookup (:lctx st) id)]
      (when decl (when-let [v (:value decl)] v)))))

(defn- try-unfold
  "Unfold a definition if its name is in the to-unfold set."
  [st env to-unfold expr]
  (when (seq to-unfold)
    (let [head (e/get-app-fn expr)]
      (when (e/const? head)
        (let [hname (e/const-name head)]
          (when (contains? to-unfold (name/->string hname))
            (when-let [^ConstantInfo ci (env/lookup env hname)]
              (when (or (.isDef ci) (.isThm ci))
                (when-let [value (.value ci)]
                  (let [levels (e/const-levels head)
                        lparams (vec (.levelParams ci))
                        level-subst (into {} (map vector lparams
                                                  (concat levels (repeat lvl/zero))))
                        body (if (seq level-subst)
                               (e/instantiate-level-params value level-subst)
                               value)
                        args (e/get-app-args expr)]
                    (reduce e/app body args)))))))))))

(defn- try-eta-reduce
  "Eta reduction: (fun x => f x) → f when x is not free in f.
   In de Bruijn terms: (lam _ T (app f (bvar 0))) → f when bvar 0 not in f.
   Conservative: only fires when f has no loose bvars (common case: f is a const/fvar)."
  [expr]
  (when (e/lam? expr)
    (let [body (e/lam-body expr)]
      (when (e/app? body)
        (let [arg (e/app-arg body)
              f (e/app-fn body)]
          (when (and (e/bvar? arg)
                     (= 0 (e/bvar-idx arg))
                     (not (e/has-loose-bvars? f)))
            f))))))

(defn- reduce-step
  "Try reduction without delta unfolding.
   Following Lean 4's reduceStep which operates at 'reducible' transparency:
   beta, iota (recursor on constructor), projection, let expansion, fvar-let,
   eta reduction.
   Does NOT unfold named definitions — that's handled by try-unfold and lemmas.
   This prevents aggressive instance chain unfolding (e.g., HAdd → instHAdd → Nat.add → brecOn)."
  [st expr]
  (or (when-let [expanded (try-reduce-fvar st expr)] (mk-result expanded))
      (when-let [eta-reduced (try-eta-reduce expr)] (mk-result eta-reduced))
      (let [reduced (red/whnf-no-delta (:env st) expr (:lctx st))]
        (when-not (= reduced expr) (mk-result reduced)))))

;; ============================================================
;; dsimp — definitional simplification (Lean 4's dsimpImpl)
;; ============================================================
;; Lean 4: dsimp is a SEPARATE traversal from simp. It uses transformWithCache
;; with dpre/dpost hooks that only do:
;; 1. Structural reductions (beta, iota, proj, let, zeta, eta) via dsimpReduce
;; 2. rfl-theorem rewrites (theorems whose proof IS definitional equality)
;; NO rewrite lemmas, NO simprocs, NO discharge, NO CongrArgKind computation.
;; Propagates transitively: same restricted processing for ALL sub-expressions
;; including lambda bodies. This prevents type annotation corruption.
;;
;; Used for: :fixed args in CongrArgKind, lambda binder types (lambdaTelescopeDSimp).

(defn- dsimp-expr
  "Definitional simplification — Lean 4's dsimpImpl.
   Recursively traverses all sub-expressions applying ONLY structural reductions
   (beta/iota/proj/let/zeta via whnf-no-delta). No rewrite lemmas, no simprocs.
   Returns the simplified expression (no proof — all changes are def-eq)."
  [env lctx expr max-depth]
  (if (or (<= max-depth 0) (nil? expr) (not (instance? ansatz.kernel.Expr expr)))
    expr
    (try
    (let [;; First try structural reduction on the whole expression
          reduced (red/whnf-no-delta env expr lctx)
          expr (if (= reduced expr) expr reduced)
          ;; Then recurse into sub-expressions
          dec-depth (dec max-depth)]
      (case (e/tag expr)
        :app (let [f (dsimp-expr env lctx (e/app-fn expr) dec-depth)
                   a (dsimp-expr env lctx (e/app-arg expr) dec-depth)]
               (if (and (identical? f (e/app-fn expr))
                        (identical? a (e/app-arg expr)))
                 ;; Try reduction again after sub-expression changes
                 (let [r2 (red/whnf-no-delta env expr lctx)]
                   (if (= r2 expr) expr r2))
                 (let [rebuilt (e/app f a)
                       r2 (red/whnf-no-delta env rebuilt lctx)]
                   (if (= r2 rebuilt) rebuilt r2))))
        :lam (let [t (dsimp-expr env lctx (e/lam-type expr) dec-depth)
                   b (dsimp-expr env lctx (e/lam-body expr) dec-depth)]
               (if (and (identical? t (e/lam-type expr))
                        (identical? b (e/lam-body expr)))
                 expr
                 (e/lam (e/lam-name expr) t b (e/lam-info expr))))
        :forall (let [t (dsimp-expr env lctx (e/forall-type expr) dec-depth)
                      b (dsimp-expr env lctx (e/forall-body expr) dec-depth)]
                  (if (and (identical? t (e/forall-type expr))
                           (identical? b (e/forall-body expr)))
                    expr
                    (e/forall' (e/forall-name expr) t b (e/forall-info expr))))
        :let (let [expanded (e/instantiate1 (e/let-body expr) (e/let-value expr))]
               (dsimp-expr env lctx expanded dec-depth))
        :proj (let [s (dsimp-expr env lctx (e/proj-struct expr) dec-depth)]
                (if (identical? s (e/proj-struct expr))
                  expr
                  (let [rebuilt (e/proj (e/proj-type-name expr) (e/proj-idx expr) s)
                        r2 (red/whnf-no-delta env rebuilt lctx)]
                    (if (= r2 rebuilt) rebuilt r2))))
        :mdata (dsimp-expr env lctx (e/mdata-expr expr) dec-depth)
        ;; Atoms (const, fvar, bvar, sort, lit) — no descent
        expr))
    (catch Exception _ expr))))

;; ============================================================
;; Simplification engine — Lean 4's simpLoop
;; ============================================================

(defn- is-proof-term?
  "Check if an expression is a proof (inhabits a Prop).
   Lean 4: isProof e checks that type(e) : Prop, i.e., type(type(e)) = Sort 0.
   NOT the same as 'is a proposition' — Eq Nat 1 0 is a Prop (type), not a proof."
  [st expr]
  (try
    (let [ty (tc/infer-type st expr)        ;; type of expr
          ty-sort (tc/infer-type st ty)      ;; type of type (should be Sort u)
          tw (#'tc/cached-whnf st ty-sort)]
      ;; expr is a proof iff its type's type is Prop (Sort 0)
      ;; i.e., type(expr) : Prop means expr IS a proof
      (and (e/sort? tw) (= (e/sort-level tw) lvl/zero)))
    (catch Exception _ false)))

(defn- is-prop-type?
  "Check if a type lives in Prop."
  [st ty]
  (try
    (let [s (tc/infer-type st ty) sw (#'tc/cached-whnf st s)]
      (and (e/sort? sw) (= (e/sort-level sw) lvl/zero)))
    (catch Exception _ false)))

;; ============================================================
;; @[congr] theorem support
;; ============================================================
;; Lean 4: trySimpCongrTheorem? in Types.lean
;; A congr theorem for function f has the form:
;;   ∀ (a₁ a₂ : α) ... (h₁ : a₁ = a₁') ..., f a₁ ... = f a₁' ...
;; The key insight: hypotheses h_i allow simplifying individual args
;; independently, even when they have dependencies between them.

(def ^:private known-congr-theorems
  "Known @[congr] theorems indexed by head function name.
   Lean 4 gets these from the @[congr] attribute."
  {"ite" "ite_congr"
   "dite" "dite_congr"
   "And" "and_congr"})

(defn- try-congr-theorem
  "Try to apply a @[congr] theorem to an application.
   Returns a SimpResult or nil.
   Following Lean 4's trySimpCongrTheorem? (Types.lean:585-634)."
  [st env lemma-index expr config]
  (let [[head args] (e/get-app-fn-args expr)]
    (when (e/const? head)
      (let [hname (name/->string (e/const-name head))
            congr-name (get known-congr-theorems hname)]
        (when congr-name
          ;; Look up the congr theorem
          (when-let [^ConstantInfo ci (env/lookup env (name/from-string congr-name))]
            ;; For now, try to use the congr theorem as a rewrite rule
            ;; The full implementation would:
            ;; 1. Match the theorem's LHS with expr
            ;; 2. For each hypothesis position, recursively simp the argument
            ;; 3. Discharge remaining obligations
            ;; For now, delegate to the rewrite engine which handles this
            ;; via the standard lemma matching pipeline
            (let [lemma (first (extract-simp-lemma env ci 5000))]
              (when lemma
                (let [candidates [lemma]
                      subst (match-lemma st (:lhs-pattern lemma) expr (:num-params lemma))]
                  (when (and subst (= (count subst) (:num-params lemma)))
                    (let [rhs (apply-subst (:rhs lemma) subst (:num-params lemma))
                          param-vals (mapv #(get subst %) (range (:num-params lemma)))
                          inst-levels (infer-level-params st lemma subst)
                          proof (reduce e/app
                                        (e/const' (:name lemma) inst-levels)
                                        (reverse param-vals))]
                      (mk-result rhs proof))))))))))))

;; ============================================================
;; FunInfo + CongrArgKind — Lean 4's congruence argument classification
;; ============================================================
;; Determines which app arguments get full simp vs dsimp-only.
;; Lean 4: CongrTheorems.lean + FunInfo.lean

(defn- collect-bvar-deps
  "Collect de Bruijn indices of free bvars in expr that refer to params
   (bvars with index >= depth). Returns a set of param indices."
  [expr depth]
  (let [result (volatile! #{})]
    (letfn [(walk [e d]
              (case (e/tag e)
                :bvar (when (>= (e/bvar-idx e) d)
                        (vswap! result conj (- (e/bvar-idx e) d)))
                :app (do (walk (e/app-fn e) d) (walk (e/app-arg e) d))
                :lam (do (walk (e/lam-type e) d) (walk (e/lam-body e) (inc d)))
                :forall (do (walk (e/forall-type e) d) (walk (e/forall-body e) (inc d)))
                :let (do (walk (e/let-type e) d) (walk (e/let-value e) d) (walk (e/let-body e) (inc d)))
                :proj (walk (e/proj-struct e) d)
                :mdata (walk (e/mdata-expr e) d)
                nil))]
      (walk expr depth))
    @result))

;; Per-env cache to avoid stale entries across environments
(def ^:private fun-info-cache (atom {}))
(def ^:private fun-info-cache-env (atom nil))

(defn- get-fun-info
  "Compute FunInfo for a function applied to nargs arguments.
   Returns {:param-infos [{:binder-info :back-deps :has-fwd-deps :is-prop :is-instance} ...]
            :result-deps #{...}}
   Lean 4: getFunInfoAux (FunInfo.lean)."
  [st env fn-expr nargs]
  (let [cache-key [(when (e/const? fn-expr) (e/const-name fn-expr)) nargs]]
    ;; Invalidate cache if env changed
    (when-not (identical? env @fun-info-cache-env)
      (reset! fun-info-cache {})
      (reset! fun-info-cache-env env))
    (or (get @fun-info-cache cache-key)
        (let [fn-type (try (safe-infer st fn-expr) (catch Exception _ nil))]
          (when fn-type
            (let [;; Walk forall telescope up to nargs
                  info
                  (loop [ty fn-type i 0 params []]
                    (if (or (>= i nargs) (not (e/forall? ty)))
                      ;; Done — compute result-deps from remaining type
                      ;; Convert raw bvar indices to param indices:
                      ;; at depth i (nargs stripped), bvar k → param (i-1-k)
                      (let [result-deps-raw (collect-bvar-deps ty 0)
                            result-deps (into #{} (keep (fn [bv]
                                                          (let [p (- i 1 bv)]
                                                            (when (>= p 0) p))))
                                              result-deps-raw)
                            ;; Update has-fwd-deps: param j has fwd-deps if any later
                            ;; param's back-deps contains j, or result-deps contains j
                            params (reduce
                                    (fn [ps j]
                                      (let [has-fwd (or (contains? result-deps j)
                                                        (some (fn [p]
                                                                (contains? (:back-deps p) j))
                                                              (subvec ps (inc j))))]
                                        (if has-fwd
                                          (assoc-in ps [j :has-fwd-deps] true)
                                          ps)))
                                    params
                                    (range (count params)))]
                        {:param-infos params :result-deps result-deps})
                      ;; Process param i
                      (let [param-type (e/forall-type ty)
                            binfo (e/forall-info ty)
                            ;; back-deps: which earlier params does this type reference?
                            ;; In the telescope at depth i, bvar k (k < i) refers to param (i-1-k)
                            raw-deps (collect-bvar-deps param-type 0)
                            back-deps (into #{} (keep (fn [bv] (let [p (- i 1 bv)]
                                                                  (when (>= p 0) p))))
                                            raw-deps)
                            is-prop (try (let [s (tc/infer-type st param-type)
                                              sw (#'tc/cached-whnf st s)]
                                          (and (e/sort? sw) (= (e/sort-level sw) lvl/zero)))
                                        (catch Exception _ false))
                            is-inst (= binfo :inst-implicit)]
                        (recur (e/forall-body ty) (inc i)
                               (conj params {:binder-info binfo
                                             :back-deps back-deps
                                             :has-fwd-deps false  ;; computed in post-pass
                                             :is-prop is-prop
                                             :is-instance is-inst})))))]
              (swap! fun-info-cache assoc cache-key info)
              info))))))

(defn- get-congr-simp-kinds
  "Compute CongrArgKind for each argument of a function application.
   Returns a vector of :eq, :fixed, or :cast.
   Lean 4: getCongrSimpKinds + fixKindsForDependencies (CongrTheorems.lean)."
  [fun-info]
  (let [{:keys [param-infos result-deps]} fun-info
        n (count param-infos)
        ;; Phase 1: initial classification
        kinds (mapv (fn [i]
                      (let [pi (nth param-infos i)]
                        (cond
                          (contains? result-deps i) :fixed  ;; result depends on this
                          (:is-prop pi)             :cast   ;; Prop → auto-transport
                          (:is-instance pi)         :fixed  ;; instance → fixed
                          :else                     :eq)))  ;; full simp
                    (range n))
        ;; Phase 2: fixKindsForDependencies
        ;; If param j (j > i) has back-dep on i AND kinds[j] is :eq or :fixed,
        ;; then i must be :fixed (can't rewrite something a later :eq depends on)
        kinds (reduce (fn [ks i]
                        (if (= (nth ks i) :fixed)
                          ks  ;; already fixed
                          (let [needs-fix (some (fn [j]
                                                  (and (contains? (:back-deps (nth param-infos j)) i)
                                                       (#{:eq :fixed} (nth ks j))))
                                                (range (inc i) n))]
                            (if needs-fix
                              (assoc ks i :fixed)
                              ks))))
                      kinds
                      (range n))]
    kinds))

(defn- simp-subterms
  "Simplify subterms (congruence step).
   Dispatches by expression type, builds proper congruence proofs."
  [st env lemma-index expr config]
  (let [max-depth (:max-depth config)]
    (if (<= max-depth 0)
      (mk-result expr)
      (case (e/tag expr)
        ;; Application — Lean 4: simpApp → congr → trySimpCongrTheorem? → congrDefault
        :app (let [;; First try @[congr] theorem (Lean 4: trySimpCongrTheorem?)
                   congr-result (try-congr-theorem st env lemma-index expr config)]
               (if congr-result
                 congr-result
                 ;; Pre-descent simpMatch for Bool.rec: simplify discriminant with
                 ;; full simp BEFORE CongrArgKind marks it :fixed.
                 ;; Lean 4: simpMatch (SimpMatch.lean) handles recursors specially.
                 (let [app-fn-full (e/get-app-fn expr)
                       app-args-full (e/get-app-args expr)]
                   (or
                     ;; Bool.rec with constant motive: override discriminant to :eq.
                     ;; When motive body doesn't reference its bound variable (e.g.,
                     ;; fun _ : Bool => Bool), the result type doesn't depend on the
                     ;; discriminant, so congrArg works and full simp is safe.
                     ;; Lean 4 handles this via auto-generated congr theorems; we
                     ;; detect the non-dependent case at runtime.
                     nil  ;; fall through to generic descent with override below

                 ;; Default: simplify fn and arg separately, build congruence proof.
                 ;; Lean 4: simpAppUsingCongr — use CongrArgKind to determine
                 ;; which args get full simp (:eq) vs dsimp-only (:fixed/:cast).
                 (let [orig-f (e/app-fn expr) orig-a (e/app-arg expr)
                       f-result (simp-expr* st env lemma-index orig-f (update config :max-depth dec))
                       ;; Determine if this arg position should be :fixed (dsimp only)
                       ;; Compute from the full application's head function + arg count
                       app-fn (e/get-app-fn expr)
                       app-args (e/get-app-args expr)
                       arg-idx (dec (count app-args))
                       fun-info (when (and (e/const? app-fn) (pos? (count app-args)))
                                  (try (get-fun-info st env app-fn (count app-args))
                                       (catch Exception _ nil)))
                       kinds (when fun-info (get-congr-simp-kinds fun-info))
                       raw-kind (if (and kinds (< arg-idx (count kinds)))
                                  (nth kinds arg-idx)
                                  ;; No info available — use safe heuristic:
                                  ;; if arg's type is Sort u (u > 0), it's a type → :fixed
                                  (let [at (safe-infer st orig-a)
                                        atw (when at (safe-whnf st at))]
                                    (if (and atw (e/sort? atw)
                                             (not= (e/sort-level atw) lvl/zero))
                                      :fixed :eq)))
                       ;; Override :fixed → :eq for recursor discriminants with constant motive.
                       ;; When the motive doesn't depend on its bound variable (e.g.,
                       ;; Bool.rec (fun _ => Bool) ...), the result type is non-dependent,
                       ;; so congrArg works and full simp on the discriminant is safe.
                       ;; Lean 4 handles this via auto-generated congr theorems.
                       arg-kind (if (and (= raw-kind :fixed)
                                         (e/const? app-fn)
                                         (let [n (name/->string (e/const-name app-fn))]
                                           (or (= n "Bool.rec") (= n "List.rec")
                                               (.endsWith ^String n ".rec")
                                               (.endsWith ^String n ".casesOn")))
                                         ;; Last arg = discriminant
                                         (= arg-idx (dec (count app-args)))
                                         ;; Check motive (first arg) is constant (non-dependent)
                                         (let [motive (first app-args)]
                                           (and (e/lam? motive)
                                                (not (e/has-loose-bvars?
                                                       (e/lam-body motive) 0)))))
                                  :eq  ;; safe: motive is constant, congrArg works
                                  raw-kind)
                       a-result (if (= arg-kind :eq)
                                  ;; :eq — full simp (with rewrite lemmas + simprocs)
                                  (simp-expr* st env lemma-index orig-a (update config :max-depth dec))
                                  ;; :fixed/:cast — dsimp only (Lean 4's dsimpImpl).
                                  ;; Separate traversal: structural reductions only,
                                  ;; propagates transitively through all sub-expressions
                                  ;; including lambda bodies. No rewrite lemmas.
                                  (let [reduced (dsimp-expr env (:lctx st) orig-a
                                                            (:max-depth config))]
                                    (if (= reduced orig-a)
                                      (mk-result orig-a)
                                      (mk-result reduced))))]
                   (if (and (identical? (:expr f-result) orig-f)
                            (identical? (:expr a-result) orig-a))
                     (mk-result expr)
                     (mk-congr st f-result a-result orig-f orig-a)))))))

        ;; Lambda — Lean 4: simpLambda with funext proof
        ;; funext : {α} {β : α → Sort v} {f g : ∀ a, β a} →
        ;;          (∀ a, f a = g a) → f = g
        ;; When body changes with proof h(x), wrap in funext (λ x => h(x))
        :lam (let [lam-type (e/lam-type expr)
                   lam-body (e/lam-body expr)
                   lam-nm (e/lam-name expr)
                   lam-bi (e/lam-info expr)
                   ;; dsimp the binder type (Lean 4: lambdaTelescopeDSimp)
                   ;; Uses dsimp-expr: structural reductions only, no rewrite lemmas.
                   ;; This prevents type annotation corruption (Bool → True).
                   t-r (let [reduced (dsimp-expr env (:lctx st) lam-type
                                                  (:max-depth config))]
                         (if (= reduced lam-type)
                           (mk-result lam-type)
                           (mk-result reduced)))
                   ;; simp the body
                   b-r (simp-expr* st env lemma-index lam-body (update config :max-depth dec))]
               (if (and (identical? (:expr t-r) lam-type)
                        (identical? (:expr b-r) lam-body))
                 (mk-result expr)
                 ;; Something changed — build new lambda
                 (let [new-lam (e/lam lam-nm (:expr t-r) (:expr b-r) lam-bi)]
                   (if (nil? (:proof? b-r))
                     ;; Body change is definitional — no proof needed
                     (mk-result new-lam)
                     ;; Body changed with proof — need funext
                     ;; funext (λ x => proof(x)) : (λ x => old(x)) = (λ x => new(x))
                     ;; Lean 4: r.addLambdas xs uses foldrM mkFunExt
                     (try
                       (let [;; Build λ x => proof(x)  (proof already has bvar 0 for x)
                             proof-lam (e/lam lam-nm (:expr t-r) (:proof? b-r) :default)
                             ;; funext {α} {β} {f} {g} proof-lam
                             ;; Let kernel infer implicit args
                             alpha (:expr t-r)
                             u (get-sort-level st alpha)
                             ;; β is the return type family — for non-dependent, constant
                             result-type (safe-infer st (e/app expr (e/bvar 0)))
                             v (if result-type (get-sort-level st result-type) lvl/zero)]
                         {:expr new-lam
                          :proof? (e/app* (e/const' funext-name [u v])
                                          alpha expr new-lam proof-lam)
                          :cache true})
                       (catch Exception _
                         ;; Fallback: return without proof
                         (mk-result new-lam)))))))

        ;; Forall/arrow — Lean 4's simpForall/simpArrow
        ;; Per-binder contextual: add h:P as a simp lemma when simplifying Q
        :forall
        (let [is-arrow (not (e/has-loose-bvars? (e/forall-body expr) 0))
              orig-p (e/forall-type expr)
              orig-q (e/forall-body expr)]
          (if is-arrow
            ;; Arrow: P → Q
            (let [p-result (simp-expr* st env lemma-index orig-p (update config :max-depth dec))
                  ;; Per-binder contextual simp (Lean 4: simpArrow lines 339-361)
                  ;; If contextual and both P,Q are Props, add h:P as lemma for Q
                  q-lemma-index
                  (if (and (:contextual? config)
                           (is-prop-type? st orig-p)
                           (is-prop-type? st orig-q))
                    ;; Add simplified P as a rewrite lemma
                    ;; This creates a hypothetical proof h:P that can be used
                    ;; to discharge side conditions when simplifying Q
                    (let [p-simplified (:expr p-result)
                          [ph _] (e/get-app-fn-args p-simplified)
                          phn (when (e/const? ph) (e/const-name ph))
                          ;; Create a hypothesis-like lemma entry for P
                          ;; If P is an Eq/Iff, it becomes a rewrite rule for Q
                          [phead pargs] (e/get-app-fn-args p-simplified)]
                      (if (and (e/const? phead)
                               (or (= (e/const-name phead) eq-name)
                                   (= (e/const-name phead) iff-name)))
                        ;; P is Eq/Iff: add as rewrite lemma
                        (let [lhs (if (= 3 (count pargs)) (nth pargs 1) (nth pargs 0))
                              rhs (if (= 3 (count pargs)) (nth pargs 2) (nth pargs 1))
                              [lh _] (e/get-app-fn-args lhs)
                              hn (when (e/const? lh) (e/const-name lh))
                              hyp-lemma {:name nil :level-params [] :num-params 0
                                         :lhs-pattern lhs :rhs rhs
                                         :eq-type (when (= 3 (count pargs)) (nth pargs 0))
                                         :kind (if (= (e/const-name phead) eq-name) :eq :iff)
                                         :priority 3000 :perm false
                                         :head-name hn :lhs-nargs (count (e/get-app-args lhs))}]
                          ;; Insert the new hyp lemma into existing tree
                          (dt/trie-insert lemma-index
                                          (dt/expr->keys lhs)
                                          hyp-lemma))
                        ;; P is not Eq/Iff: keep same index
                        lemma-index))
                    lemma-index)
                  ;; Simplify Q with potentially augmented lemma index
                  ;; Reset cache for fresh context (Lean 4: withFreshCache)
                  q-config (if (not= q-lemma-index lemma-index)
                             (assoc config :cache (atom {}))
                             config)
                  q-result (simp-expr* st env q-lemma-index orig-q
                                       (update q-config :max-depth dec))]
              (if (and (identical? (:expr p-result) orig-p)
                       (identical? (:expr q-result) orig-q))
                (mk-result expr)
                (if (and (is-prop-type? st orig-p) (is-prop-type? st orig-q))
                  (mk-implies-congr st p-result q-result orig-p orig-q)
                  (mk-result (e/forall' (e/forall-name expr) (:expr p-result)
                                        (:expr q-result) (e/forall-info expr))))))
            ;; Dependent forall: dsimp domain, simp body
            (let [t-r (simp-expr* st env lemma-index orig-p (update config :max-depth dec))
                  b-r (simp-expr* st env lemma-index orig-q (update config :max-depth dec))]
              (if (and (identical? (:expr t-r) orig-p) (identical? (:expr b-r) orig-q))
                (mk-result expr)
                (mk-result (e/forall' (e/forall-name expr) (:expr t-r)
                                      (:expr b-r) (e/forall-info expr)))))))

        ;; Let — zeta reduce
        :let (let [expanded (e/instantiate1 (e/let-body expr) (e/let-value expr))]
               (simp-expr* st env lemma-index expanded config))

        ;; Projection
        :proj (let [s-r (simp-expr* st env lemma-index (e/proj-struct expr) (update config :max-depth dec))]
                (if (identical? (:expr s-r) (e/proj-struct expr))
                  (mk-result expr)
                  (mk-result (e/proj (e/proj-type-name expr) (e/proj-idx expr) (:expr s-r)))))

        ;; Mdata — unwrap
        :mdata (simp-expr* st env lemma-index (e/mdata-expr expr) config)

        ;; Atoms
        (mk-result expr)))))

(def ^:dynamic *simp-trace*
  "When bound to an atom, simp-expr* logs rewrites for debugging.
   Each entry: {:expr-before :expr-after :phase :depth :lemma-name}"
  nil)

(defn- simp-expr*
  "Core simplification loop (Lean 4's simpLoop).
   config: {:max-depth :single-pass? :max-steps :cache :to-unfold :discharge-depth}"
  [st env lemma-index expr config]
  (when-let [steps (:max-steps config)]
    (when (> @steps config/*max-simp-steps*)
      (tactic-error! "maximum number of steps exceeded" {:expr expr}))
    (swap! steps inc))

  (if (<= (:max-depth config) 0)
    (mk-result expr)

    ;; Check cache
    (let [cache (:cache config)
          cached (when cache (get @cache expr))]
      (if cached
        cached

        (let [result
              ;; Skip proof terms
              (if (and (not (e/has-fvar-flag expr))
                       (not (e/has-loose-bvars? expr))
                       (is-proof-term? st expr))
                (mk-result expr)

                ;; PRE-PHASE
                (let [pre-step (try-rewrite-step st env lemma-index expr config)]
                  (if pre-step
                    ;; .visit: recurse on result
                    (let [inner (simp-expr* st env lemma-index (:expr pre-step) (update config :max-depth dec))]
                      (mk-eq-trans st pre-step inner))

                    ;; .continue: reduce + descend
                    (let [whnf-r (reduce-step st expr)
                          unfold-r (when-not whnf-r
                                     (when-let [u (try-unfold st env (:to-unfold config) expr)]
                                       (mk-result u)))
                          reduced (or whnf-r unfold-r)
                          current (if reduced
                                    (let [inner (simp-expr* st env lemma-index (:expr reduced) (update config :max-depth dec))]
                                      (mk-eq-trans st reduced inner))
                                    (simp-subterms st env lemma-index expr config))]

                      ;; POST-PHASE
                      ;; Lean 4: after congruence may have introduced reducible redexes
                      ;; (e.g. Bool.rec ... true after discriminant rewrite).
                      ;; Try WHNF reduction before post-rewrite.
                      (let [post-reduced (when (not (identical? (:expr current) expr))
                                           (reduce-step st (:expr current)))
                            current (if post-reduced
                                      (mk-eq-trans st current post-reduced)
                                      current)
                            post-r (or (try-rewrite-step st env lemma-index (:expr current) config)
                                       (try-simproc st (:expr current) config
                                                    :env env :lemma-index lemma-index))]
                        (if post-r
                          (let [composed (mk-eq-trans st current post-r)]
                            (if (or (:single-pass? config) (= expr (:expr composed)))
                              composed
                              (let [again (simp-expr* st env lemma-index (:expr composed)
                                                      (update config :max-depth dec))]
                                (mk-eq-trans st composed again))))
                          current))))))]
          ;; Trace: log when Bool→True corruption occurs
          (when (and *simp-trace*
                     (e/const? expr)
                     (= (name/->string (e/const-name expr)) "Bool")
                     (not (identical? (:expr result) expr)))
            ;; Find which lemma matched via disc tree
            (let [dt-cands (lookup-lemmas st env lemma-index expr)
                  matching (filter (fn [l]
                                     (match-lemma st (:lhs-pattern l) expr (:num-params l)))
                                   dt-cands)]
              (swap! *simp-trace* conj
                     {:depth (:max-depth config)
                      :before "Bool"
                      :after (subs (str (:expr result)) 0 (min 80 (count (str (:expr result)))))
                      :n-candidates (count dt-cands)
                      :matching-lemmas (mapv (fn [l]
                                               {:name (some-> (:name l) name/->string)
                                                :hyp-id (:hyp-fvar-id l)
                                                :kind (:kind l)
                                                :priority (:priority l)
                                                :lhs (subs (str (:lhs-pattern l)) 0 (min 40 (count (str (:lhs-pattern l)))))})
                                             matching)})))
          (when (and cache (:cache result))
            (swap! cache assoc expr result))
          result)))))

;; Public wrapper
(defn simp-expr
  "Simplify an expression. Returns the simplified expression."
  ([st env lemma-index expr max-depth]
   (simp-expr st env lemma-index expr max-depth #{}))
  ([st env lemma-index expr max-depth to-unfold]
   (:expr (simp-expr* st env lemma-index expr
                      {:max-depth max-depth :single-pass? false
                       :max-steps (atom 0) :cache (atom {})
                       :to-unfold to-unfold :discharge-depth 0}))))

;; ============================================================
;; Public API
;; ============================================================

(defn make-simp-lemmas
  "Create simp lemma entries from a list of constant names.
   Flattens vector returns from extract-simp-lemma (e.g. And splitting)."
  [env lemma-names]
  (vec (mapcat (fn [n]
                 (let [cname (if (instance? ansatz.kernel.Name n) n (name/from-string (str n)))
                       ci (env/lookup env cname)]
                   (when ci (extract-simp-lemma env ci 1000))))
               lemma-names)))

(def ^:private default-simp-lemmas
  "Default simp lemma names (commonly used in Lean 4 Init)."
  [;; Nat arithmetic
   "Nat.add_zero" "Nat.zero_add" "Nat.mul_one" "Nat.one_mul"
   "Nat.mul_zero" "Nat.zero_mul" "Nat.succ_eq_add_one"
   ;; Bool/decide (Lean 4: @[simp] in Init/SimpLemmas.lean)
   "Bool.true_and" "Bool.and_true" "Bool.false_and" "Bool.and_false"
   "Bool.true_or" "Bool.or_true" "Bool.false_or" "Bool.or_false"
   "Bool.not_true" "Bool.not_false"
   ;; Nat.ble → ≤ conversion (Lean 4: @[simp] ble_eq in Init/Data/Nat/Basic.lean)
   ;; Connects boolean Nat.ble to propositional ≤
   "Nat.ble_eq"
   ;; Eq
   "eq_self_iff_true"
   ;; List
   "List.length_nil" "List.length_cons"
   ;; if/then/else
   "ite_true" "ite_false" "dite_true" "dite_false"
   ;; And/Or/Not
   "and_true" "true_and" "and_false" "false_and"
   "or_true" "true_or" "or_false" "false_or"
   "not_true" "not_false"
   ;; Bool ∧ Prop bridge (Lean 4: @[simp] in Init/SimpLemmas.lean)
   ;; Converts boolean && equality to propositional And
   "Bool.and_eq_true"
   ;; Prop
   "implies_true" "true_implies"
   ;; Function
   "Function.comp_id" "Function.id_comp"])

(defn- ensure-ble-eq
  "Derive Nat.ble_eq if not already in env.
   Lean 4: @[simp] theorem ble_eq : (Nat.ble x y = true) = (x ≤ y)
   Proof: propext (Iff.intro Nat.le_of_ble_eq_true Nat.ble_eq_true_of_le)"
  [env]
  (let [ble-eq-name (name/from-string "Nat.ble_eq")]
    (when-not (env/lookup env ble-eq-name)
      (when (and (env/lookup env (name/from-string "Nat.le_of_ble_eq_true"))
                 (env/lookup env (name/from-string "Nat.ble_eq_true_of_le"))
                 (env/lookup env (name/from-string "propext"))
                 (env/lookup env (name/from-string "Iff.intro")))
        ;; Build: ∀ (x y : Nat), (Nat.ble x y = true) = (x ≤ y)
        ;; Proof: fun x y => propext (Iff.intro (Nat.le_of_ble_eq_true) (Nat.ble_eq_true_of_le))
        (try
          (let [nat (e/const' (name/from-string "Nat") [])
                lz lvl/zero l1 (lvl/succ lz)
                bool-type (e/const' (name/from-string "Bool") [])
                bool-true (e/const' (name/from-string "Bool.true") [])
                inst-le-nat (e/const' (name/from-string "instLENat") [])
                ;; LE.le Nat instLENat x y = x ≤ y
                mk-le (fn [a b] (e/app* (e/const' (name/from-string "LE.le") [lz])
                                         nat inst-le-nat a b))
                ;; Type: ∀ (x y : Nat), (Nat.ble x y = true) = (x ≤ y)
                ble-xy (e/app* (e/const' (name/from-string "Nat.ble") [])
                               (e/bvar 1) (e/bvar 0))
                ble-eq-true (e/app* (e/const' (name/from-string "Eq") [l1])
                                    bool-type ble-xy bool-true)
                le-xy (mk-le (e/bvar 1) (e/bvar 0))
                eq-body (e/app* (e/const' (name/from-string "Eq") [l1])
                                (e/sort' lz) ble-eq-true le-xy)
                full-type (e/forall' "y" nat
                            (e/forall' "x" nat eq-body :default) :default)
                ;; Proof with fvars then abstract
                fv-x (e/fvar 9900000) fv-y (e/fvar 9900001)
                ble-fv (e/app* (e/const' (name/from-string "Nat.ble") []) fv-x fv-y)
                ble-eq-fv (e/app* (e/const' (name/from-string "Eq") [l1])
                                  bool-type ble-fv bool-true)
                le-fv (mk-le fv-x fv-y)
                ;; Nat.le_of_ble_eq_true {n m} h → partial: takes h
                fwd (e/app* (e/const' (name/from-string "Nat.le_of_ble_eq_true") [])
                            fv-x fv-y)
                bwd (e/app* (e/const' (name/from-string "Nat.ble_eq_true_of_le") [])
                            fv-x fv-y)
                iff-proof (e/app* (e/const' (name/from-string "Iff.intro") [])
                                  ble-eq-fv le-fv fwd bwd)
                proof-body (e/app* (e/const' (name/from-string "propext") [])
                                   ble-eq-fv le-fv iff-proof)
                ;; Abstract fvars and wrap in lambdas
                proof-abs (e/abstract-many proof-body [9900000 9900001])
                full-proof (e/lam "y" nat
                             (e/lam "x" nat proof-abs :default) :default)]
            ;; Verify and register
            (let [tc (ansatz.kernel.TypeChecker. env)]
              (.setFuel tc 20000000)
              (.inferType tc full-proof))
            (env/add-constant env (env/mk-thm ble-eq-name [] full-type full-proof)))
          (catch Exception _ env))))))

(defn- try-close-eq-rfl
  "If expr is Eq T a b where a and b are def-eq, return rfl proof. Else nil."
  [st expr]
  (let [w (or (safe-whnf st expr) expr)
        [h a] (e/get-app-fn-args w)]
    (when (and (e/const? h) (= (e/const-name h) eq-name) (= 3 (count a)))
      (let [lhs (nth a 1) rhs (nth a 2)
            deq (or (tc/is-def-eq st lhs rhs)
                    ;; Fallback: Java TC with generous fuel for deep instance chains
                    (try (let [tc (ansatz.kernel.TypeChecker. (:env st))]
                           (.setFuel tc config/*default-fuel*)
                           (.isDefEq tc lhs rhs))
                         (catch Exception _ false)))]
        (when deq
          (e/app* (e/const' eq-refl-name (e/const-levels h)) (nth a 0) lhs))))))

(defn- close-goal-with-proof
  "Try to close the goal using a simp result.
   Following Lean 4's simpTargetCore (Main.lean:780-790):
   - If simplified to True: close with of_eq_true
   - If simplified is an Eq with def-eq sides: close with rfl
   - Otherwise: replace goal type with simplified (via Eq.mpr)"
  [ps goal st result lemma-names]
  (let [simplified (:expr result)
        simplified-whnf (#'tc/cached-whnf st simplified)
        goal-type (:type goal)]
    (cond
      ;; Simplified to True
      ;; Lean 4: if r.expr.isTrue → close with of_eq_true
      ;; of_eq_true : {p : Prop} → (p = True) → p
      (and (e/const? simplified-whnf) (= (e/const-name simplified-whnf) true-name))
      (if (:proof? result)
        (let [;; of_eq_true takes {p} (the original goal) and h : p = True
              proof-term (e/app* (e/const' of-eq-true-name [])
                                 goal-type (:proof? result))]
          (-> (proof/assign-mvar ps (:id goal) {:kind :exact :term proof-term})
              (proof/record-tactic :simp lemma-names (:id goal))))
        (try (decide-tac/decide ps)
             (catch Exception _
               (tactic-error! "simplified to True but cannot certify" {:goal goal-type}))))

      ;; Simplified to False
      (and (e/const? simplified-whnf) (= (e/const-name simplified-whnf) false-name))
      (tactic-error! "goal simplified to False" {:goal goal-type})

      ;; Try rfl on SIMPLIFIED or ORIGINAL expression
      :else
      (if-let [rfl-proof (if (:proof? result)
                           ;; Simp has a proof → try rfl on simplified, wrap with Eq.mpr
                           (try-close-eq-rfl st simplified)
                           ;; Simp changed expr but lost proof → try rfl on ORIGINAL goal
                           ;; (kernel may reduce n-n to 0 via def-eq)
                           (or (try-close-eq-rfl st goal-type)
                               (try-close-eq-rfl st simplified)))]
        (let [mpr-level (let [gs (safe-infer st goal-type)
                              gsw (when gs (safe-whnf st gs))]
                          (if (and gsw (e/sort? gsw)) (e/sort-level gsw) lvl/zero))
              final-proof (if (and (:proof? result) (not= simplified goal-type))
                            (e/app* (e/const' eq-mpr-name [mpr-level])
                                    goal-type simplified (:proof? result) rfl-proof)
                            rfl-proof)]
          (-> (proof/assign-mvar ps (:id goal) {:kind :exact :term final-proof})
              (proof/record-tactic :simp lemma-names (:id goal))))
        ;; Try decide as last resort
        (try (decide-tac/decide ps)
             (catch Exception _
               (if (= simplified goal-type)
                 (tactic-error! "simp made no progress" {:goal goal-type})
                 ;; Lean 4: simp replaces goal with simplified form via Eq.mpr
                 ;; when it can't close. Create a new goal with the simplified type.
                 ;; This follows Lean 4's applySimpResultToTarget (Main.lean:780).
                 (if (:proof? result)
                   (let [mpr-level (let [gs (safe-infer st goal-type)
                                         gsw (when gs (safe-whnf st gs))]
                                     (if (and gsw (e/sort? gsw)) (e/sort-level gsw) lvl/zero))
                         [ps' new-id] (proof/fresh-mvar ps simplified (:lctx goal))]
                     (-> (proof/assign-mvar ps' (:id goal)
                                            {:kind :simp-reduce
                                             :eq-proof (:proof? result)
                                             :child new-id
                                             :mpr-level mpr-level
                                             :goal-type goal-type
                                             :simplified simplified})
                         (proof/record-tactic :simp lemma-names (:id goal))))
                   ;; Proof chain is nil (all rfl steps) but simp simplified.
                   ;; The simplified type is def-eq to the original goal type.
                   ;; Create a sub-goal with the simplified type — the child's proof
                   ;; directly proves the original goal (kernel verifies def-eq).
                   (let [[ps' new-id] (proof/fresh-mvar ps simplified (:lctx goal))]
                     (-> (proof/assign-mvar ps' (:id goal)
                                            {:kind :simp-reduce
                                             :eq-proof nil  ;; def-eq, no explicit proof
                                             :child new-id
                                             :mpr-level lvl/zero
                                             :goal-type goal-type
                                             :simplified simplified})
                         (proof/record-tactic :simp lemma-names (:id goal))))))))))))


(defn simp
  "Simplify the current goal using rewrite lemmas.
   Options: :contextual? :single-pass? :max-depth :decide? (default true)"
  ([ps] (simp ps []))
  ([ps lemma-names] (simp ps lemma-names {}))
  ([ps lemma-names opts]
   (let [goal (proof/current-goal ps)
         _ (when-not goal (tactic-error! "No goals" {}))
         env (or (ensure-ble-eq (:env ps)) (:env ps))
         ;; Update proof state with enriched env (e.g., derived Nat.ble_eq)
         ps (if (not (identical? env (:env ps))) (assoc ps :env env) ps)
         st (tc/mk-tc-state env)
         st (assoc st :lctx (:lctx goal))
         ;; Lean 4: user lemma names are ADDED to the default @[simp] set.
         all-names (if (seq lemma-names)
                     (distinct (concat default-simp-lemmas lemma-names))
                     default-simp-lemmas)
         lemmas (make-simp-lemmas env all-names)
         ;; Contextual: add hypotheses as lemmas
         ;; Lean 4: SimpTheorems.lean preprocess — handles Eq, Iff, And (split),
         ;; implications (conditional rewrites), and general props (→ True).
         ;; Safe now: hasFwdDeps guard in simp-subterms prevents type annotation corruption.
         hyp-lemmas (when (:contextual? opts)
                      (make-hyp-lemmas st (:lctx goal)))
         ;; For user definitions with equation theorems, add those as rewrite lemmas
         eqn-lemmas (vec (mapcat (fn [n]
                                   (let [cn (if (instance? ansatz.kernel.Name n) n (name/from-string (str n)))]
                                     (when-let [eqns (find-eqn-theorems env cn)]
                                       (mapcat (fn [eqn-name]
                                                 (when-let [ci (env/lookup env eqn-name)]
                                                   (extract-simp-lemma env ci 50)))
                                               eqns))))
                                 all-names))
         all-lemmas (concat lemmas hyp-lemmas eqn-lemmas)
         lemma-index (build-lemma-index st env all-lemmas)
         to-unfold (into #{} (keep (fn [n]
                                     (let [cn (if (instance? ansatz.kernel.Name n) n (name/from-string (str n)))
                                           ci (env/lookup env cn)]
                                       (when (and ci
                                                  (not (seq (extract-simp-lemma env ci 0)))
                                                  (not (find-eqn-theorems env cn)))
                                         (str n)))))
                         all-names)
         config {:max-depth (or (:max-depth opts) 20)
                 :single-pass? (:single-pass? opts)
                 :contextual? (:contextual? opts)
                 :decide? (get opts :decide? true)
                 :max-steps (atom 0)
                 :cache (atom {})
                 :to-unfold to-unfold
                 :discharge-depth 0
                 ;; Lazy instance index for TC synthesis in discharge
                 :inst-index (delay (inst/build-instance-index env))}
         result (simp-expr* st env lemma-index (:type goal) config)]
     (close-goal-with-proof ps goal st result lemma-names))))

(defn- hyp-type->lemmas
  "Extract simp lemma(s) from a single hypothesis type.
   Following Lean 4's preprocess (SimpTheorems.lean:288):
   - Eq/Iff: direct rewrite
   - And P Q: split into sub-lemmas (using And.left/And.right projections)
   - Implications P → Q: conditional rewrite (num-params > 0)
   - General propositions: → P = True
   Returns a vector of lemma maps. st is used for is-prop checks."
  [st hyp-type hyp-fvar-id]
  (let [;; Strip non-dependent arrows (propositional implications)
        [num-params conclusion]
        (loop [ty hyp-type n 0]
          (if (and (e/forall? ty)
                   (not (e/has-loose-bvars? (e/forall-type ty)))
                   ;; Only peel Prop-typed domains (not Type params like Nat)
                   (is-prop-type? st (e/forall-type ty)))
            (recur (e/forall-body ty) (inc n))
            [n ty]))
        [head args] (e/get-app-fn-args conclusion)]
    (cond
      ;; Eq α a b → direct rewrite: a → b
      (and (e/const? head) (= (e/const-name head) eq-name) (= 3 (count args)))
      (let [lhs (nth args 1) rhs (nth args 2)
            [lh _] (e/get-app-fn-args lhs)
            hn (when (e/const? lh) (e/const-name lh))]
        [{:name nil :level-params [] :num-params num-params
          :lhs-pattern lhs :rhs rhs
          :eq-type (nth args 0) :kind :eq
          :priority 2000 :head-name hn
          :lhs-nargs (count (e/get-app-args lhs))
          :hyp-fvar-id hyp-fvar-id}])

      ;; Iff P Q → rewrite via propext
      (and (e/const? head) (= (e/const-name head) iff-name) (= 2 (count args)))
      (let [lhs (nth args 0) rhs (nth args 1)
            [lh _] (e/get-app-fn-args lhs)
            hn (when (e/const? lh) (e/const-name lh))]
        [{:name nil :level-params [] :num-params num-params
          :lhs-pattern lhs :rhs rhs
          :eq-type nil :kind :iff
          :priority 2000 :head-name hn
          :lhs-nargs (count (e/get-app-args lhs))
          :hyp-fvar-id hyp-fvar-id}])

      ;; And P Q → split into two sub-lemmas (Lean 4: preprocess And branch)
      (and (e/const? head) (= (e/const-name head) and-name) (= 2 (count args)))
      (let [left-lemmas (hyp-type->lemmas st (nth args 0) hyp-fvar-id)
            right-lemmas (hyp-type->lemmas st (nth args 1) hyp-fvar-id)]
        ;; Add And.left/And.right projection chains
        (into (mapv #(update % :and-proj (fnil conj [])
                             {:side :left :args [(nth args 0) (nth args 1)]})
                    left-lemmas)
              (mapv #(update % :and-proj (fnil conj [])
                             {:side :right :args [(nth args 0) (nth args 1)]})
                    right-lemmas)))

      ;; General proposition → P = True (only for Prop-typed hypotheses)
      ;; Lean 4: preprocess else branch + isProp guard
      (and (e/const? head)
           (not= (e/const-name head) true-name)
           (is-prop-type? st conclusion))
      (let [[lh _] (e/get-app-fn-args conclusion)
            hn (when (e/const? lh) (e/const-name lh))]
        [{:name nil :level-params [] :num-params num-params
          :lhs-pattern conclusion :rhs (e/const' true-name [])
          :eq-type nil :kind :prop-true
          :priority 2000 :head-name hn
          :lhs-nargs (count (e/get-app-args conclusion))
          :hyp-fvar-id hyp-fvar-id}])

      :else nil)))

(defn- make-hyp-lemmas
  "Extract contextual rewrite lemmas from hypotheses in lctx.
   Handles Eq, Iff, And (splitting), Not, implications (conditional rewrites),
   and general propositions (→ True).
   Optionally excludes a specific hypothesis (by fvar id) to prevent self-rewrite.
   Lean 4: SimpAll.lean + SimpTheorems.lean preprocess."
  [st lctx & {:keys [exclude-id]}]
  (vec (mapcat (fn [[id decl]]
                 (when (and (= :local (:tag decl))
                            (not= id exclude-id))
                   (try (hyp-type->lemmas st (:type decl) id)
                        (catch Exception _ nil))))
               lctx)))

(defn simp-all
  "Simplify goal + all hypotheses (Lean 4's SimpAll).
   Phase 1: simp the goal with contextual hypotheses.
   Phase 2: simplify Prop hypothesis types and add alongside originals."
  ([ps] (simp-all ps []))
  ([ps lemma-names]
   (let [goal (proof/current-goal ps)
         _ (when-not goal (tactic-error! "No goals" {}))
         env (or (ensure-ble-eq (:env ps)) (:env ps))
         ps (if (not (identical? env (:env ps))) (assoc ps :env env) ps)
         all-names (if (seq lemma-names)
                     (distinct (concat default-simp-lemmas lemma-names))
                     default-simp-lemmas)
         ;; Phase 1: simp the goal with contextual
         ;; Catch "no progress" — Phase 2 can still be useful even if
         ;; Phase 1 doesn't simplify the goal (it decomposes hypotheses
         ;; for the NEXT simp_all call). Lean 4: SimpAll.loop continues
         ;; even when simpTarget makes no progress.
         ps' (try (simp ps lemma-names {:contextual? true})
                  (catch Exception _ ps))
         goal' (proof/current-goal ps')]
     (if (nil? goal')
       ps'  ;; Goal closed — done
       ;; Phase 2: hypothesis simplification
       ;; Only accept def-eq changes (proof? = nil) to avoid type annotation
       ;; corruption from full simp on hypothesis types. Non-def-eq changes
       ;; need transitive CongrArgKind propagation through lambda bodies.
       (let [lctx (:lctx goal')
             st (assoc (tc/mk-tc-state env) :lctx lctx)
             base-lemmas (make-simp-lemmas env all-names)
             eqn-lemmas (vec (mapcat (fn [n]
                                       (let [cn (if (instance? ansatz.kernel.Name n) n (name/from-string (str n)))]
                                         (when-let [eqns (find-eqn-theorems env cn)]
                                           (mapcat (fn [eqn-name]
                                                     (when-let [ci (env/lookup env eqn-name)]
                                                       (extract-simp-lemma env ci 50)))
                                                   eqns))))
                                     all-names))
             to-unfold (into #{} (keep (fn [n]
                                         (let [cn (if (instance? ansatz.kernel.Name n) n (name/from-string (str n)))
                                               ci (env/lookup env cn)]
                                           (when (and ci
                                                      (not (seq (extract-simp-lemma env ci 0)))
                                                      (not (find-eqn-theorems env cn)))
                                             (str n)))))
                             all-names)
             inst-index (delay (inst/build-instance-index env))
             hyps (vec (filter (fn [[_ d]] (= :local (:tag d))) lctx))
             ;; Compute simplified hypothesis types
             replacements
             (reduce
              (fn [acc [id decl]]
                (try
                  ;; Only simplify non-implication Prop hypotheses.
                  ;; Skip: Type-valued declarations (x : Nat, l : List Nat)
                  ;; Skip: Implications/foralls (IH: P → Q) — these must be
                  ;; preserved in original form for apply/rewrite tactics.
                  ;; Lean 4: simp_all processes implications via simpArrow,
                  ;; but for Bool-valued functions the equation theorem
                  ;; unfolding makes the IH unusable after simplification.
                  (let [ty (:type decl)]
                    (when (or (not (is-prop-type? st ty))
                              (and (e/forall? ty)
                                   (not (e/has-loose-bvars? (e/forall-type ty)))))
                      (throw (ex-info "skip" {}))))
                  (let [hyp-lemmas (make-hyp-lemmas st lctx :exclude-id id)
                        all-lemmas (concat base-lemmas eqn-lemmas hyp-lemmas)
                        lemma-index (build-lemma-index st env all-lemmas)
                        config {:max-depth 20 :single-pass? false :decide? true
                                :max-steps (atom 0) :cache (atom {})
                                :to-unfold to-unfold :discharge-depth 0
                                :inst-index inst-index}
                        result (simp-expr* st env lemma-index (:type decl) config)]
                    (if (or (identical? (:expr result) (:type decl))
                            (= (:expr result) (:type decl)))
                      acc
                      ;; Accept the simplification. Root cause of Bool→True corruption
                      ;; is fixed (Prop guards in extract-from-conclusion +
                      ;; try-simp-using-decide). Lean 4 doesn't TC-verify
                      ;; intermediate proofs during simp_all — final extract/verify
                      ;; catches any remaining issues.
                      (conj acc {:old-fvar-id id :name (:name decl)
                                 :old-type (:type decl) :new-type (:expr result)
                                 :eq-proof (:proof? result)})))
                  (catch Exception _ acc)))
              []
              hyps)]
         (if (empty? replacements)
           ps'  ;; No hypothesis changes — return simp result as-is
           ;; Add simplified hypotheses alongside originals
           (let [;; Allocate new fvar ids
                 [ps'' replacements']
                 (reduce (fn [[ps reps] rep]
                           (let [[ps' new-id] (proof/alloc-id ps)]
                             [ps' (conj reps (assoc rep :new-fvar-id new-id))]))
                         [ps' []]
                         replacements)
                 ;; Build new lctx: keep originals, add simplified versions
                 ;; Use distinct names (append ') to avoid name collision with
                 ;; originals — otherwise sexp->ansatz name lookup picks the wrong one
                 new-lctx (reduce (fn [lctx {:keys [new-fvar-id name new-type]}]
                                    (assoc lctx new-fvar-id
                                           {:tag :local :id new-fvar-id
                                            :name (str name "'") :type new-type}))
                                  lctx
                                  replacements')
                 ;; Create body sub-goal (insert at front for priority)
                 [ps'' body-goal-id]
                 (let [[ps''' id] (proof/alloc-id ps'')]
                   [(-> ps'''
                        (assoc-in [:mctx id] {:type (:type goal') :lctx new-lctx :assignment nil})
                        (update :goals #(into [id] %)))
                    id])
                 ;; Assign current goal with simp-all-hyps wrapper
                 ps'' (-> (proof/assign-mvar ps'' (:id goal')
                                              {:kind :simp-all-hyps
                                               :replacements replacements'
                                               :child body-goal-id})
                          (proof/record-tactic :simp-all (vec lemma-names) (:id goal')))]
             ps'')))))))


;; ============================================================
;; Nat offset decomposition — Lean 4's NatOffset (Simprocs/Nat.lean)
;; ============================================================

(defn nat-offset-parse
  "Decompose a Nat expression into {:base expr :offset n}.
   e.g., x + 3 → {:base x :offset 3}, Nat.succ x → {:base x :offset 1},
   pure literal 5 → {:base nil :offset 5}."
  [st expr]
  (let [w (#'tc/cached-whnf st expr)
        [head args] (e/get-app-fn-args w)]
    (cond
      ;; Pure literal
      (e/lit-nat? w)
      {:base nil :offset (e/lit-nat-val w)}

      ;; Nat.succ a
      (and (e/const? head) (= (e/const-name head) nat-succ-name) (= 1 (count args)))
      (let [inner (nat-offset-parse st (nth args 0))]
        (update inner :offset inc))

      ;; Nat.add a b
      (and (e/const? head) (= (e/const-name head) nat-add-name) (= 2 (count args)))
      (let [b-val (whnf-to-nat st (nth args 1))]
        (if b-val
          (let [inner (nat-offset-parse st (nth args 0))]
            (update inner :offset + b-val))
          (let [a-val (whnf-to-nat st (nth args 0))]
            (if a-val
              (let [inner (nat-offset-parse st (nth args 1))]
                (update inner :offset + a-val))
              {:base w :offset 0}))))

      ;; HAdd.hAdd Nat Nat Nat inst a b (6 args)
      (and (e/const? head)
           (= (name/->string (e/const-name head)) "HAdd.hAdd")
           (= 6 (count args)))
      (let [b-val (whnf-to-nat st (nth args 5))]
        (if b-val
          (let [inner (nat-offset-parse st (nth args 4))]
            (update inner :offset + b-val))
          (let [a-val (whnf-to-nat st (nth args 4))]
            (if a-val
              (let [inner (nat-offset-parse st (nth args 5))]
                (update inner :offset + a-val))
              {:base w :offset 0}))))

      :else {:base w :offset 0})))

(defn dsimp
  "Definitional simplification — only kernel reduction."
  [ps]
  (let [goal (proof/current-goal ps)
        _ (when-not goal (tactic-error! "No goals" {}))
        env (:env ps) st (tc/mk-tc-state env)
        st (assoc st :lctx (:lctx goal))
        goal-type (:type goal)
        simplified (#'tc/cached-whnf st goal-type)
        [head args] (e/get-app-fn-args simplified)]
    (cond
      (and (e/const? head) (= (e/const-name head) true-name))
      (-> (proof/assign-mvar ps (:id goal) {:kind :exact :term (e/const' true-intro-name [])})
          (proof/record-tactic :dsimp [] (:id goal)))

      (and (e/const? head) (= (e/const-name head) eq-name) (= 3 (count args))
           (tc/is-def-eq st (nth args 1) (nth args 2)))
      (let [proof (e/app* (e/const' eq-refl-name (e/const-levels head)) (nth args 0) (nth args 1))]
        (-> (proof/assign-mvar ps (:id goal) {:kind :exact :term proof})
            (proof/record-tactic :dsimp [] (:id goal))))

      :else
      (tactic-error! "dsimp: cannot close goal" {:goal goal-type :simplified simplified}))))
