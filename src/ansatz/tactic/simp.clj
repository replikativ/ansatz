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
            [ansatz.meta :as meta]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.tc :as tc]
            [ansatz.kernel.reduce :as red]
            [ansatz.tactic.proof :as proof]
            [ansatz.tactic.decide :as decide-tac]
            [ansatz.tactic.instance :as inst]
            [ansatz.simp-index :as si]
            [ansatz.config :as config])
  (:import [ansatz.kernel ConstantInfo ExprMap LeanExprKey]))

;; ============================================================
;; Names
;; ============================================================

(def ^:private eq-name (name/from-string "Eq"))
(def ^:private iff-name (name/from-string "Iff"))
(def ^:private true-name (name/from-string "True"))
(def ^:private false-name (name/from-string "False"))

(defn- true-const? [t] (and (e/const? t) (= "True" (name/->string (e/const-name t)))))
(defn- false-const? [t] (and (e/const? t) (= (e/const-name t) false-name)))
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
(def ^:private decidable-istrue-name (name/from-string "Decidable.isTrue"))
(def ^:private decidable-isfalse-name (name/from-string "Decidable.isFalse"))
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

(declare tactic-error!)

(defn- mk-eq-trans
  "Compose two simp results via Eq.trans.
   r1 proves a = b, r2 proves b = c, returns a = c."
  [st r1 r2]
  (cond
    (nil? (:proof? r1)) r2
    (nil? (:proof? r2)) (assoc r1 :expr (:expr r2))
    :else
    (let [ty (tc/infer-type st (:proof? r1))
          ty-whnf (when ty (#'tc/cached-whnf st ty))
          [head args] (when ty-whnf (e/get-app-fn-args ty-whnf))
          alpha (when (and head (e/const? head) (= (e/const-name head) eq-name)
                           (= 3 (count args)))
                  (nth args 0))
          u (when alpha
              (let [s (tc/infer-type st alpha)
                    sw (when s (#'tc/cached-whnf st s))]
                (when (and sw (e/sort? sw)) (e/sort-level sw))))]
      (if (and alpha u)
        {:expr (:expr r2)
         :proof? (e/app* (e/const' eq-trans-name [u])
                         alpha (nth args 1) (nth args 2) (:expr r2)
                         (:proof? r1) (:proof? r2))
         :cache (and (:cache r1) (:cache r2))}
        ;; Lean Simp/Types.lean Result.mkEqTrans requires both equality proofs.
        (tactic-error! "cannot compose equality proofs" {:proof-construction true :result r1})))))

;; ============================================================
;; Congruence proof builders — following Lean 4's Types.lean
;; ============================================================

(defn- safe-infer [st e]
  (tc/infer-type st e))

(defn- safe-whnf [st e]
  (#'tc/cached-whnf st e))

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
         (tactic-error! "cannot build congrFun proof" {:proof-construction true}))))))

(defn- mk-congr-arg
  "congrArg f h : f a₁ = f a₂, given h : a₁ = a₂.
   congrArg : {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β) (h : a₁ = a₂) → f a₁ = f a₂"
  ([st f a-result]
   (mk-congr-arg st f a-result nil nil))
  ([st f a-result orig-a1 orig-a2]
   (if (nil? (:proof? a-result))
     (mk-result (e/app f (:expr a-result)))
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
         (tactic-error! "cannot build congrArg proof" {:proof-construction true}))))))

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
        (tactic-error! "cannot build congr proof" {:proof-construction true})))))

(defn- mk-implies-congr
  "implies_congr hp hq : (p₁ → q₁) = (p₂ → q₂).
   Lean 4: mkImpCongr for non-dependent arrow types."
  [st p-result q-result orig-p orig-q]
  (cond
    (and (nil? (:proof? p-result)) (nil? (:proof? q-result)))
    (mk-result (e/arrow (:expr p-result) (:expr q-result)))

    :else

      ;; implies_congr.{u,v} (a₁ a₂ : Sort u) (b₁ b₂ : Sort v) (ha)(hb) : (a₁→b₁)=(a₂→b₂)
      ;; u,v are the sorts of the antecedent p and consequent q (Lean's mkImpCongr).
      ;; ha : Eq.{u+1} (Sort u) p₁ p₂, so refl fallback is Eq.refl.{u+1} (Sort u) p.
    (let [u (get-sort-level st orig-p)
          v (get-sort-level st orig-q)
          hp (or (:proof? p-result)
                 (e/app* (e/const' eq-refl-name [(lvl/succ u)])
                         (e/sort' u) orig-p))
          hq (or (:proof? q-result)
                 (e/app* (e/const' eq-refl-name [(lvl/succ v)])
                         (e/sort' v) orig-q))]
      {:expr (e/arrow (:expr p-result) (:expr q-result))
       :proof? (e/app* (e/const' implies-congr-name [u v])
                       orig-p (:expr p-result)
                       orig-q (:expr q-result) hp hq)
       :cache true})))

;; ============================================================
;; Error helpers
;; ============================================================

(defn- tactic-error! [msg data]
  (throw (ex-info (str "Tactic error: simp: " msg) (merge {:kind :tactic-error} data))))

(def ^:dynamic ^:private *simp-recursion* {:rec-depth 0})

(def ^:dynamic *max-rec-depth* 512)

(defn- check-rec-depth! [depth expr]
  (when (> depth *max-rec-depth*)
    (tactic-error! (str "maximum recursion depth exceeded (maxRecDepth = " *max-rec-depth* ")")
                   {:expr expr :limit :max-rec-depth :max-rec-depth *max-rec-depth*})))

(defmacro ^:private with-inc-rec-depth [frames expr & body]
  ;; Lean/Exception.lean withIncRecDepth; Simp/Main.lean simpImpl/simpLoop
  ;; and Meta/Transform.lean transformWithCache share one recursion context.
  `(let [context# (update *simp-recursion* :rec-depth + ~frames)]
     (check-rec-depth! (:rec-depth context#) ~expr)
     (binding [*simp-recursion* context#]
       ~@body)))

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
  (with-inc-rec-depth 1 a
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
      :else (= a b))))

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
  (with-inc-rec-depth 1 ty
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

        :else nil))))

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

(defn- extract-simp-lemma-term
  "Like extract-simp-lemma, but from a proof TERM and its (already-inferred) type `ty`, rather than a
   named constant. The resulting lemma map carries `:proof-term` (the term) instead of `:name`, so the
   rewrite proof is the term applied to the matched params — NOT a fresh `(const name levels)`. This is
   what lets `simp [<term>]` accept any proof term (Lean's `simp [h]`), e.g. a projected typeclass axiom
   `WSemiring.mul_zero S inst`. The term is level-closed (its universe args are already concrete), so
   `:level-params []` and level inference is a no-op."
  [env ty priority proof-term]
  (let [mk (fn [t np]
             (mapv #(assoc % :proof-term proof-term :name nil)
                   (extract-from-conclusion env nil [] np false priority t)))]
    (loop [t ty np 0]
      (if (e/forall? t)
        (let [body (e/forall-body t)]
          (if (and (e/const? body) (= (e/const-name body) false-name))
            (mk t np)
            (recur body (inc np))))
        (mk t np)))))

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
   Expands query nodes on demand while walking exact and wildcard branches;
   a wildcard skips its entire query subtree.
   With st/env: filters instance-implicit args for correct matching.
   With `config`: when the call carries the store's persistent @[simp] index (`:ext-trie`,
   ansatz.simp-index), ALSO returns the inherited @[simp] candidates for `expr`, each lemma
   resolved+extracted on first match and cached — the ~91k-name Mathlib corpus is never
   keyed eagerly. Nil `:ext-trie` (simp only, a store without the artifact, the expression-level
   API) means the eager index is the whole candidate set, as before."
  ([lemma-index expr] (dt/lookup-simp-tree lemma-index expr))
  ([st env lemma-index expr] (dt/lookup-simp-tree st env lemma-index expr))
  ([st env lemma-index expr config]
   (let [;; An empty trie has no candidates and needs no type-forcing keying.
         eager (when (or (seq (:children lemma-index)) (seq (:values lemma-index)))
                 (dt/lookup-simp-tree st env lemma-index expr))]
     (if-let [trie (:ext-trie config)]
       (concat eager (si/candidate-rules trie st env expr))
       eager))))

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
                (with-inc-rec-depth 1 p
                  (when @ok
                  ;; Lean tryTheoremCore matches with reducible isDefEq. Normalize
                  ;; both heads with the same reduction used by the index first.
                    (let [p (dt/reduce-dt env p false)
                          t (dt/reduce-dt env t false)]
                      (cond
                        (and (e/bvar? p) (>= (e/bvar-idx p) depth))
                        (let [param-idx (- (e/bvar-idx p) depth)]
                      ;; Lean's scoped metavariables cannot capture a binder
                      ;; introduced while matching. Extracted pattern bvars are
                      ;; telescope parameters, so their values must be closed.
                          (if (e/has-loose-bvars? t)
                            (reset! ok false)
                            (if-let [existing (get @subst param-idx)]
                              (when-not (tc/is-def-eq st existing t)
                                (reset! ok false))
                              (swap! subst assoc param-idx t))))

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
                                 (if skip-last
                               ;; Bind parameters inside instance arguments while
                               ;; tolerating definitionally equal instance spellings.
                                   (let [pa (e/app-arg p)]
                                 ;; Lean Rewrite.lean tryTheoremCore unifies the
                                 ;; entire instance argument. Parameters can occur
                                 ;; INSIDE it: instBEqOfDecidableEq α dec is the only
                                 ;; occurrence of `dec` in lookup_filter_ne's LHS.
                                 ;; Preserve the defeq-instance fallback if the
                                 ;; structural spelling does not expose parameters.
                                     (when (and @ok (e/has-loose-bvars? pa))
                                       (let [saved @subst]
                                         (go pa (e/app-arg t) depth)
                                         (when-not @ok
                                           (reset! subst saved)
                                           (reset! ok true)))))
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
                    ;; Extracted patterns contain loose parameter bvars; they are
                    ;; placeholders, not terms the kernel can compare (Lean uses mvars).
                        :else (when-not (and (not (e/has-loose-bvars? p))
                                             (not (e/has-loose-bvars? t))
                                             (tc/is-def-eq st p t))
                                (reset! ok false)))))))]
      (go pattern target 0))
    (when @ok @subst)))

(defn- apply-subst
  "Apply a substitution to an expression."
  [expr subst num-params]
  (if (empty? subst)
    expr
    (letfn [(go [e depth]
                (with-inc-rec-depth 1 e
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
                    ;; Lean Simp/Rewrite.lean tryTheoremCore (55f80e10a3) instantiates the entire
                    ;; RHS, including lets. Only the body is under the let binder.
                    :let (let [t (go (e/let-type e) depth)
                               v (go (e/let-value e) depth)
                               b (go (e/let-body e) (inc depth))]
                           (if (and (identical? t (e/let-type e))
                                    (identical? v (e/let-value e))
                                    (identical? b (e/let-body e)))
                             e (e/let' (e/let-name e) t v b)))
                    :proj (let [s (go (e/proj-struct e) depth)]
                            (if (identical? s (e/proj-struct e)) e
                                (e/proj (e/proj-type-name e) (e/proj-idx e) s)))
                    :mdata (go (e/mdata-expr e) depth)
                    e)))]
      (go expr 0))))

;; ============================================================
;; Level inference
;; ============================================================

(defn- unify-pattern-levels!
  "Structurally align `pattern` (the lemma LHS, carrying the lemma's level params)
   with the concrete matched `target`; for each const-with-levels in common, bind
   any still-unresolved level param to the target's corresponding level. This
   recovers universes the telescope walk misses — e.g. `eq_self_iff_true.{u}`'s
   implicit `{α : Sort u}` is starred by the discr tree, but the LHS `Eq.{u} α a a`
   matched against `Eq.{1} (List _) …` pins u=1 directly. `levels`/`resolved` are
   atoms; `lpset` is the set of the lemma's level-param names."
  [levels resolved lpset pattern target]
  (with-inc-rec-depth 1 pattern
    (when (and pattern target)
      (cond
        (and (e/const? pattern) (e/const? target)
             (= (e/const-name pattern) (e/const-name target)))
        (doseq [[pl tl] (map vector (e/const-levels pattern) (e/const-levels target))]
          (when (lvl/param? pl)
            (let [nm (lvl/param-name pl)]
              (when (and (lpset nm) (not (@resolved nm)))
                (swap! levels assoc nm tl)
                (swap! resolved conj nm)))))
        (and (e/app? pattern) (e/app? target))
        (do (unify-pattern-levels! levels resolved lpset (e/app-fn pattern) (e/app-fn target))
            (unify-pattern-levels! levels resolved lpset (e/app-arg pattern) (e/app-arg target)))
        (and (e/lam? pattern) (e/lam? target))
        (do (unify-pattern-levels! levels resolved lpset (e/lam-type pattern) (e/lam-type target))
            (unify-pattern-levels! levels resolved lpset (e/lam-body pattern) (e/lam-body target)))
        :else nil))))

(defn- infer-level-params
  "Infer universe level assignments from matched parameter values.
   Solves level equations: if param has type Sort(succ u), and value has
   type Sort n, then u = n-1. This handles the common Sort(u+1) pattern.
   When `target` (the matched expression) is given, levels the telescope walk
   leaves unresolved are recovered by unifying the lemma LHS-pattern against the
   target's concrete levels — needed when an implicit type param is starred by
   the discr tree (e.g. eq_self_iff_true)."
  ([st lemma subst] (infer-level-params st lemma subst nil))
  ([st lemma subst target]
   (let [lparams (:level-params lemma)]
     (if (empty? lparams)
       []
       (let [levels (atom {})
             resolved (atom #{})
             lpset (set lparams)
             ^ConstantInfo ci (env/lookup (:env st) (:name lemma))
             ctype (when ci (.type ci))]
         (loop [i 0 ty ctype]
           (when (and (< i (:num-params lemma)) ty (e/forall? ty))
             (when-let [val (get subst i)]
               (let [expected-sort (e/forall-type ty)
                     val-ty (tc/infer-type st val)
                     val-tw (#'tc/cached-whnf st val-ty)]
                 (when (and (e/sort? expected-sort) (e/sort? val-tw))
                   (let [expected-level (e/sort-level expected-sort)
                         actual-level (e/sort-level val-tw)]
                     (doseq [lp lparams]
                       (when-not (@resolved lp)
                         (let [param-lvl (lvl/param lp)
                               put! (fn [v] (swap! levels assoc lp v) (swap! resolved conj lp))]
                           (cond
                               ;; Sort(u) = Sort(n) → u = n
                             (= expected-level param-lvl) (put! actual-level)
                               ;; Sort(succ u) = Sort(n) → u = n-1
                             (and (lvl/succ? expected-level)
                                  (= (lvl/succ-pred expected-level) param-lvl)
                                  (lvl/succ? actual-level))
                             (put! (lvl/succ-pred actual-level))
                               ;; Sort(succ(succ u)) = Sort(n) → u = n-2
                             (and (lvl/succ? expected-level)
                                  (lvl/succ? (lvl/succ-pred expected-level))
                                  (= (lvl/succ-pred (lvl/succ-pred expected-level)) param-lvl)
                                  (lvl/succ? actual-level)
                                  (lvl/succ? (lvl/succ-pred actual-level)))
                             (put! (lvl/succ-pred (lvl/succ-pred actual-level)))))))))))
             (recur (inc i) (e/forall-body ty))))
         ;; Fallback: recover any unresolved levels by unifying the LHS pattern
         ;; against the concrete matched target.
         (when (and target (:lhs-pattern lemma) (not= (count @resolved) (count lparams)))
           (unify-pattern-levels! levels resolved lpset (:lhs-pattern lemma) target))
         (mapv (fn [lp] (get @levels lp lvl/zero)) lparams))))))

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
                             (tc/is-def-eq st (:type decl) obligation-type))
                    (e/fvar id)))
                (:lctx st))
          ;; Strategy 2: typeclass synthesis (Lean 4: synthesizeInstance)
          (let [inst-index (if-let [idx (:inst-index config)]
                             (if (instance? clojure.lang.Delay idx) @idx idx)
                             (inst/index-for env))]
            (inst/synthesize* st env inst-index obligation-type 0))
          ;; Strategy 3: recursive simp with fresh cache (Lean 4: withPreservedCache)
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
                     (tc/is-def-eq st (nth args 1) (nth args 2))))
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
          ;; Strategy 4: omega + decide (for linear arithmetic obligations)
          ;; Lean 4 doesn't do this in dischargeDefault?, but it's essential for
          ;; our use case (inductive proofs with arithmetic side conditions).

            ;; `omega-proof/decides?` runs the REAL engine's reifier and solver and
            ;; skips only the proof extraction — so this filter agrees with the tactic
            ;; by construction. (It used to call a second, proof-free omega whose
            ;; verdicts could silently disagree with it.)
          (let [omega-decides? (requiring-resolve 'ansatz.tactic.omega-proof/decides?)]
            (when (omega-decides? env obligation-type (:lctx st))
                ;; Omega says provable — try decide to certify the proof term
              (let [inst-index (if-let [idx (:inst-index config)]
                                 (if (instance? clojure.lang.Delay idx) @idx idx)
                                 (inst/index-for env))
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
                                obligation-type inst eq-refl-proof))))))))))))

;; ============================================================
;; Rewriting engine
;; ============================================================

(declare find-eqn-theorems)

(defn- forall-meta-telescope
  "Instantiate a ∀-telescope with fresh metavariables (Lean's forallMetaTelescopeReducing).
   Declares real `Expr.mvar`s in the atom-held metacontext, scoped to `lctx`.
   Returns [xs body] where xs are the mvar nodes and body is the type with
   them substituted."
  [mctx lctx id-base type]
  (loop [ty type xs [] i 0]
    (if (e/forall? ty)
      (let [id (+ id-base i)
            _ (swap! mctx meta/add-expr-mvar-decl id (e/forall-type ty) lctx)]
        (recur (e/instantiate1 (e/forall-body ty) (e/mvar id))
               (conj xs (e/mvar id)) (inc i)))
      [xs ty])))

(defn- try-theorem
  "Lean 4's tryTheoremCore (Simp/Rewrite.lean:114). Instantiate the lemma's ∀-params as fresh
   metavariables, then unify its LHS against the goal `expr` via the reduction-aware `is-def-eq!`
   (so a named-accessor goal matches a projection-spelled lemma). Build the proof by applying the
   lemma value to the now-assigned metavariables; REJECT (nil) if any metavariable is left
   unassigned (Lean's `hasAssignableMVar`). Used as a fallback when the structural `match-lemma`
   fails — it can only ADD sound matches, never corrupt an existing one. Only handles the `:eq`
   kind with a level-concrete value (term lemmas `simp [proof-term]` and monomorphic named lemmas)."
  [st env expr lemma]
  (let [val (cond (:proof-term lemma) (:proof-term lemma)
                  (and (:name lemma) (empty? (:level-params lemma)))
                  (e/const' (:name lemma) [])
                  :else nil)]
    (when val
      (let [type (tc/infer-type st val)]
        (when (and type (e/forall? type))
          ;; Lean's withNewMCtxDepth: lemma-parameter mvars at depth 1; the
          ;; context is discarded once the zonked proof is extracted.
          (let [mctx (atom (meta/inc-depth meta/empty-context))
                [xs body] (forall-meta-telescope mctx (:lctx st) 9000000 type)
                [head args] (e/get-app-fn-args body)]
            (when (and (e/const? head) (= (e/const-name head) eq-name) (= 3 (count args)))
              (let [lhs (nth args 1) rhs (nth args 2)]
                (when (when-let [m (meta/is-def-eq @mctx st lhs expr)]
                        (reset! mctx m)
                        true)
                  (let [proof (meta/zonk-expr @mctx (reduce e/app val xs))
                        rhs' (meta/zonk-expr @mctx rhs)]
                    (when (and (not (meta/has-expr-mvar? proof))
                               (not (meta/has-expr-mvar? rhs'))
                               (not= rhs' expr))
                      (mk-result rhs' proof))))))))))))

(defn- try-rewrite-step
  "Try to rewrite an expression using the lemma index.
   Returns a SimpResult or nil.
   Following Lean 4's rewrite? with synthesizeArgs + discharge."
  [st env lemma-index expr config]
  (let [;; Disc tree candidates + direct equation theorem lookup by head constant.
        ;; Direct lookup avoids disc tree star-arity mismatch for equation theorems.
        dt-candidates (lookup-lemmas st env lemma-index expr config)
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
    (or
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
                           (let [;; the lemma's statement: a hypothesis rule (a conditional IH
                                 ;; `h : p → lhs = rhs`) has no constant — its type is the local's,
                                 ;; a term rule's is inferred. Only the premise prefix is walked, and
                                 ;; premises are peeled BEFORE an And split, so an And-projected
                                 ;; hypothesis shares its premises with the hypothesis type.
                                 ctype0 (cond
                                          (:proof-term lemma)
                                          (tc/infer-type st (:proof-term lemma))
                                          (:hyp-fvar-id lemma)
                                          (:type (red/lctx-lookup (:lctx st) (:hyp-fvar-id lemma)))
                                          (:name lemma)
                                          (when-let [ci (env/lookup env (:name lemma))] (.type ^ConstantInfo ci))
                                          :else nil)
                                ;; Resolve the lemma's universe level params from the matched subst
                                ;; FIRST, then instantiate them into ctype — so discharge obligations
                                ;; carry CONCRETE levels. Without this, e.g. `beq_iff_eq`'s `LawfulBEq α`
                                ;; obligation keeps the lemma's raw level param `u_1`, while the matched
                                ;; BEq instance arg is at the goal's concrete level (0); the resulting
                                ;; `LawfulBEq.{u_1} K (instBEqOfDecidableEq.{0} K dec)` is level-
                                ;; inconsistent and instance synthesis (which type-checks the candidate)
                                ;; fails. Mirrors the RHS level instantiation done after the loop.
                                 lvl-subst (when ctype0
                                             (let [ils (infer-level-params st lemma subst expr)]
                                               (when (and (seq ils)
                                                          (= (count ils) (count (:level-params lemma))))
                                                 (zipmap (:level-params lemma) ils))))
                                 ctype (if (seq lvl-subst)
                                         (e/instantiate-level-params ctype0 lvl-subst)
                                         ctype0)
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
                                          ;; Real recursive instance synthesis (Lean synthInstance):
                                          ;; local instances + global index/discovery + recursive arg
                                          ;; discharge. `st` carries the goal lctx so a polymorphic
                                          ;; `[DecidableEq K]` hyp discharges e.g. beq_iff_eq's LawfulBEq.
                                          ;; Use config's full-scan index (the delay built from THIS
                                          ;; env, which includes structure-`extends` parent projections
                                          ;; like LawfulBEq.toReflBEq); the process-global
                                          ;; ansatz.core/instance-index is often empty for replayed/
                                          ;; non-init! envs, which silently starved parent-projection
                                          ;; synthesis. Fall back to the global, then a fresh scan.
                                           ((requiring-resolve 'ansatz.tactic.instance/synthesize*)
                                            st env
                                            (or (when-let [idx (:inst-index config)]
                                                  (if (instance? clojure.lang.Delay idx) @idx idx))
                                                (not-empty ((requiring-resolve 'ansatz.core/instance-index)))
                                                (inst/index-for env))
                                            param-type 0)
                                           (when (is-prop-type? st param-type)
                                             (try-discharge st env lemma-index config
                                                            param-type
                                                            (or (:discharge-depth config) 0))))]
                                     (if resolved
                                       (recur (assoc s (- num-params i 1) resolved)
                                              (inc i) (e/instantiate1 (e/forall-body ty) resolved))
                                       ;; Lean Simp/Rewrite.lean synthesizeArgs/tryTheoremCore:
                                       ;; an unresolved argument rejects this candidate. Our
                                       ;; substitution map cannot represent typed metavariables.
                                       nil)))))))]
                     (let [param-vals (mapv #(get full-subst %) (range num-params))]
                       (when (every? some? param-vals)
                         (let [rhs-raw (apply-subst (:rhs lemma) full-subst num-params)
                              ;; Instantiate level params in RHS
                               inst-levels-for-rhs (infer-level-params st lemma full-subst expr)
                               level-subst (zipmap (:level-params lemma) inst-levels-for-rhs)
                               rhs (if (seq level-subst)
                                     (e/instantiate-level-params rhs-raw level-subst)
                                     rhs-raw)
                              ;; Perm check (Lean 4: Rewrite.lean:142-149)
                              ;; For permutative lemmas, only allow if RHS < expr
                               perm-ok (if (:perm lemma)
                                         (ac-lt? env rhs expr)
                                         true)]
                           ;; Lean Rewrite.lean tryTheoremCore rejects a structurally
                           ;; unchanged RHS, even for rfl rules. Index reduction can
                           ;; match Nat.add_eq against its own packed HAdd RHS.
                           (when (and perm-ok (not= rhs expr))
                            ;; RFL optimization (Lean 4: useImplicitDefEqProof)
                            ;; If theorem is rfl, skip proof construction
                             (if (:rfl lemma)
                               (mk-result rhs)  ;; proof? = nil (definitional equality)
                               (let [inst-levels (infer-level-params st lemma full-subst expr)
                                    ;; For hypothesis lemmas (from local context), use fvar as proof.
                                    ;; For named lemmas (from env), use const.
                                     base-proof (cond
                                                 ;; term lemma (`simp [<proof-term>]`): apply the term
                                                  (:proof-term lemma)
                                                  (reduce e/app (:proof-term lemma) (reverse param-vals))
                                                  (:hyp-fvar-id lemma)
                                                  ;; a conditional hypothesis `h : p₁ → … → lhs = rhs`
                                                  ;; is applied to its discharged premises (And
                                                  ;; projections, if any, wrap the applied proof)
                                                  (reduce e/app (e/fvar (:hyp-fvar-id lemma)) (reverse param-vals))
                                                  :else (reduce e/app
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
                                                              ;; level-instantiate the LHS proposition too, else a
                                                              ;; poly lemma (e.g. eq_self_iff_true) leaks Eq.{u} here
                                                               (let [l (apply-subst (:lhs-pattern lemma) full-subst num-params)]
                                                                 (if (seq level-subst)
                                                                   (e/instantiate-level-params l level-subst) l))
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
           candidates)
        ;; Fallback: Lean's isDefEq-based tryTheoremCore. The structural match-lemma above is a
        ;; syntactic approximation; when it fails on a candidate the disc-tree DID return (e.g. a
        ;; goal in named-accessor spelling vs a projection-spelled typeclass lemma), retry that
        ;; candidate via reduction-aware metavariable unification. The hasAssignableMVar guard in
        ;; try-theorem makes this strictly sound — it only adds matches, never corrupts one.
     (some (fn [lemma]
             (when (and (= (:kind lemma) :eq) (not (:perm lemma))
                           ;; Only rescue PROJECTION-spelled lemmas — the exact case the structural
                           ;; match-lemma cannot handle (a typeclass accessor goal vs a lemma whose
                           ;; LHS head is `.proj`). Ordinary const-headed lemmas already go through
                           ;; match-lemma; keeping them off this path avoids perturbing rewrite
                           ;; selection elsewhere (e.g. the optimizer's cost-based strategy choice).
                        (e/proj? (e/get-app-fn (:lhs-pattern lemma))))
               (try-theorem st env expr lemma)))
           candidates))))

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

(defn- get-nat-value? [st expr]
  ;; Meta/LitValues.lean getNatValue?: recognize literals, do not normalize
  ;; arbitrary operands. Simp visits/simplifies their children separately.
  (let [expr (loop [e expr] (if (e/mdata? e) (recur (e/mdata-expr e)) e))
        [head args] (e/get-app-fn-args expr)]
    (cond
      (e/lit-nat? expr) (e/lit-nat-val expr)
      (and (e/const? expr) (= "Nat.zero" (name/->string (e/const-name expr)))) 0
      (and (e/const? head) (= "OfNat.ofNat" (name/->string (e/const-name head)))
           (= 3 (count args)) (= (first args) (e/const' (name/from-string "Nat") []))
           (e/lit-nat? (second args))) (e/lit-nat-val (second args)))))

(defn- get-int-value? [st expr]
  ;; LitValues.getIntValue? with the surface's canonical Int.ofNat/negSucc
  ;; representation. As for Nat, no eager WHNF of an open arithmetic DAG.
  (let [expr (loop [e expr] (if (e/mdata? e) (recur (e/mdata-expr e)) e))
        [head args] (e/get-app-fn-args expr)]
    (cond
      (e/lit-nat? expr) (e/lit-nat-val expr)
      (and (e/const? head) (= 1 (count args)) (= (e/const-name head) int-ofnat-name))
      (get-nat-value? st (first args))
      (and (e/const? head) (= 1 (count args)) (= (e/const-name head) int-negsucc-name))
      (when-let [n (get-nat-value? st (first args))] (- (inc n)))
      (and (e/const? head) (= "OfNat.ofNat" (name/->string (e/const-name head)))
           (= 3 (count args)) (= (first args) (e/const' (name/from-string "Int") []))
           (e/lit-nat? (second args))) (e/lit-nat-val (second args)))))

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
          (when-let [n (get-nat-value? st (nth args 0))]
            (mk-result (e/lit-nat (inc n))))

          (and (= 2 nargs)
               (contains? #{nat-add-name nat-mul-name nat-sub-name nat-div-name nat-mod-name
                            nat-ble-name nat-beq-name} hname))
          (when-let [a (get-nat-value? st (nth args 0))]
            (when-let [b (get-nat-value? st (nth args 1))]
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
          (when-let [n (get-int-value? st (nth args 0))]
            (mk-result (int-to-expr (- n))))

          ;; Binary: Int.add, Int.mul, Int.sub, Int.div, Int.mod
          (and (= 2 nargs)
               (contains? #{int-add-name int-mul-name int-sub-name int-div-name int-mod-name} hname))
          (when-let [a (get-int-value? st (nth args 0))]
            (when-let [b (get-int-value? st (nth args 1))]
              (cond
                (= hname int-add-name) (mk-result (int-to-expr (+ a b)))
                (= hname int-mul-name) (mk-result (int-to-expr (* a b)))
                (= hname int-sub-name) (mk-result (int-to-expr (- a b)))
                (= hname int-div-name) (when-not (zero? b) (mk-result (int-to-expr (quot a b))))
                (= hname int-mod-name) (when-not (zero? b) (mk-result (int-to-expr (mod a b))))
                :else nil)))

          :else nil)))))

;; ============================================================
;; AC-compatible LPO term ordering — Lean Meta/ACLt.lean, checkout 55f80e10a3.
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

(defn- name-cmp
  "Lean Data/Name.lean Name.cmp (prefix first, numeric before string)."
  [a b]
  (cond
    (= a b) 0
    (name/anonymous? a) -1
    (name/anonymous? b) 1
    (and (name/num-name? a) (name/str-name? b)) -1
    (and (name/str-name? a) (name/num-name? b)) 1
    :else (let [c (name-cmp (name/name-prefix a) (name/name-prefix b))]
            (if (zero? c) (compare (name/name-component a) (name/name-component b)) c))))

(defn- level-norm-lt?
  "Lean Level.lean normLtAux; constructor order differs from the kernel tags."
  [a b]
  (letfn [(lt [a ka b kb]
            (cond
              (lvl/succ? a) (recur (lvl/succ-pred a) (inc ka) b kb)
              (lvl/succ? b) (recur a ka (lvl/succ-pred b) (inc kb))
              (= a b) (< ka kb)
              (and (lvl/max? a) (lvl/max? b))
              (if (= (lvl/max-lhs a) (lvl/max-lhs b))
                (lt (lvl/max-rhs a) 0 (lvl/max-rhs b) 0)
                (lt (lvl/max-lhs a) 0 (lvl/max-lhs b) 0))
              (and (lvl/imax? a) (lvl/imax? b))
              (if (= (lvl/imax-lhs a) (lvl/imax-lhs b))
                (lt (lvl/imax-rhs a) 0 (lvl/imax-rhs b) 0)
                (lt (lvl/imax-lhs a) 0 (lvl/imax-lhs b) 0))
              (and (lvl/param? a) (lvl/param? b))
              (neg? (name-cmp (lvl/param-name a) (lvl/param-name b)))
              (and (lvl/mvar? a) (lvl/mvar? b)) (< (lvl/mvar-id a) (lvl/mvar-id b))
              :else (< ({:zero 0 :param 1 :mvar 2 :succ 3 :max 4 :imax 5} (lvl/tag a))
                       ({:zero 0 :param 1 :mvar 2 :succ 3 :max 4 :imax 5} (lvl/tag b)))))]
    (lt a 0 b 0)))

(defn- ac-lt?
  "Lean 4's acLt: a < b in AC-compatible LPO term ordering.
   env is used to look up parameter info for skipping instance args.
   Returns true if a is strictly smaller than b."
  ([a b] (ac-lt? nil a b))
  ([env a b]
   (letfn [(lt [a b]
             (with-inc-rec-depth 1 a
               (cond
               ;; Pointer/structural equality → not less
                 (identical? a b) false
                 (= a b) false
               ;; Strip mdata (Lean 4: ignore metadata)
                 (e/mdata? a) (lt (e/mdata-expr a) b)
                 (e/mdata? b) (lt a (e/mdata-expr b))
                 :else (lpo (if (and env (not (e/has-loose-bvars? a)))
                              (dt/reduce-dt env a false) a)
                            (if (and env (not (e/has-loose-bvars? b)))
                              (dt/reduce-dt env b false) b)))))

           (lt-pair [a1 a2 b1 b2]
             (with-inc-rec-depth 1 a1
               (cond
                 (lt a1 b1) true
                 (lt b1 a1) false
                 :else (lt a2 b2))))

           (get-param-infos [f nargs]
             ;; Lean 4: getFunInfoNArgs — get binder infos for f's params.
             ;; We use dt/get-param-infos for const heads.
             (when env (dt/get-param-infos env f)))

           (instance-arg? [infos i]
             (and infos (< i (count infos)) (= :inst-implicit (nth infos i))))

           (lt-app [a b]
             (with-inc-rec-depth 1 a
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
                                   :else (recur (inc i))))))))))))))

           (lex-same-ctor [a b]
             (with-inc-rec-depth 1 a
             ;; Lean 4: ACLt.lexSameCtor — compare within same constructor
               (let [ta (e/tag a)]
                 (case ta
                   :mvar (< (e/mvar-id a) (e/mvar-id b))
                   :let (lt-pair (e/let-value a) (e/let-body a)
                                 (e/let-value b) (e/let-body b))
                   :bvar (< (e/bvar-idx a) (e/bvar-idx b))
                   :fvar (< (e/fvar-id a) (e/fvar-id b))
                   :lit-nat (or (e/lit-str? b) (< (e/lit-nat-val a) (e/lit-nat-val b)))
                   :lit-str (and (e/lit-str? b)
                                 (neg? (compare (str (e/lit-str-val a)) (str (e/lit-str-val b)))))
                   :const (neg? (name-cmp (e/const-name a) (e/const-name b)))
                   :sort (level-norm-lt? (e/sort-level a) (e/sort-level b))
                   :app (lt-app a b)
                   :proj (if (not= (e/proj-idx a) (e/proj-idx b))
                           (< (e/proj-idx a) (e/proj-idx b))
                           (lt (e/proj-struct a) (e/proj-struct b)))
                   :lam (lt-pair (e/lam-type a) (e/lam-body a)
                                 (e/lam-type b) (e/lam-body b))
                   :forall (lt-pair (e/forall-type a) (e/forall-body a)
                                    (e/forall-type b) (e/forall-body b))
                   false))))

           (all-children-lt [a b]
             (with-inc-rec-depth 1 a
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
                   :let (and (lt (e/let-value a) b) (lt (e/let-body a) b))
                   :lam (and (lt (e/lam-type a) b) (lt (e/lam-body a) b))
                   :forall (and (lt (e/forall-type a) b) (lt (e/forall-body a) b))
                 ;; Atomic — no children → trivially true
                   true))))

           (lpo [a b]
             (with-inc-rec-depth 1 a
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
                     :else (lex-same-ctor a b))))))]
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
              :else
              ;; Faithful Lean reduceIte: the proposition need not reduce to the literal
              ;; `True`/`False` constant (e.g. `Eq Bool true true` is propositionally, not
              ;; definitionally, True). Lean whnfs the *Decidable instance* instead and
              ;; matches `Decidable.isTrue`/`Decidable.isFalse`.
              (let [[ih _] (e/get-app-fn-args (#'tc/cached-whnf st (nth args 2)))]
                (when (e/const? ih)
                  (condp = (e/const-name ih)
                    decidable-istrue-name (mk-result (nth args 3))
                    decidable-isfalse-name (mk-result (nth args 4))
                    nil)))))

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
              :else
              ;; Whnf the Decidable instance (as for ite); isTrue h → a h, isFalse h → b h.
              (let [[ih iargs] (e/get-app-fn-args (#'tc/cached-whnf st (nth args 2)))]
                (when (e/const? ih)
                  (condp = (e/const-name ih)
                    decidable-istrue-name  (mk-result (e/app (nth args 3) (last iargs)))
                    decidable-isfalse-name (mk-result (e/app (nth args 4) (last iargs)))
                    nil)))))

          :else nil)))))

(def ^:private nat-name (name/from-string "Nat"))
(def ^:private nat-succ-name (name/from-string "Nat.succ"))
(def ^:private nat-zero-name (name/from-string "Nat.zero"))
(def ^:private nat-noconfusion-name (name/from-string "Nat.noConfusion"))

(defn- nat-value
  "Concrete Nat value of a term built from literals / Nat.succ / Nat.zero, else nil."
  [st e]
  (with-inc-rec-depth 1 e
    (let [w (#'tc/cached-whnf st e)]
      (cond
        (e/lit-nat? w) (e/lit-nat-val w)
        :else (let [[h a] (e/get-app-fn-args w)]
                (cond
                  (and (e/const? h) (= (e/const-name h) nat-zero-name)) 0
                  (and (e/const? h) (= (e/const-name h) nat-succ-name) (= 1 (count a)))
                  (some-> (nat-value st (first a)) inc)
                  :else nil))))))

(defn- nat-pred-term
  "Predecessor TERM of a Nat term: Nat.succ X → X; literal k>0 → lit (k-1)."
  [st e]
  (let [w (#'tc/cached-whnf st e)
        [h a] (e/get-app-fn-args w)]
    (cond
      (and (e/const? h) (= (e/const-name h) nat-succ-name) (= 1 (count a))) (first a)
      (and (e/lit-nat? w) (pos? (e/lit-nat-val w))) (e/lit-nat (dec (e/lit-nat-val w)))
      :else nil)))

(defn- nat-ne-neg
  "Term of type `¬(a = b)` for distinct concrete Nat terms a, b, via recursive
   Nat.noConfusion: distinct outer (zero vs succ) closes directly; same outer (succ
   vs succ) peels one level — `noConfusion h (¬(a-1 = b-1))` — and recurses on the
   predecessors. The kernel reduces Nat.noConfusionType on literals, so this needs no
   decide lemmas (works in a minimal Init env). Returns nil if a,b aren't concrete/distinct."
  [st a b]
  (with-inc-rec-depth 1 a
    (let [va (nat-value st a) vb (nat-value st b)
          natT (e/const' nat-name [])
          eqp (e/app* (e/const' eq-name [(lvl/succ lvl/zero)]) natT a b)
          noconf (fn [& xs] (apply e/app* (e/const' nat-noconfusion-name [lvl/zero])
                                   (e/const' false-name []) a b xs))]
      (cond
        (or (nil? va) (nil? vb) (= va vb)) nil
        (or (zero? va) (zero? vb))                 ;; distinct outer ctor → direct
        (e/lam "h" eqp (noconf (e/bvar 0)) :default)
        :else                                       ;; both succ → peel + recurse
        (when-let [inner (nat-ne-neg st (nat-pred-term st a) (nat-pred-term st b))]
          (e/lam "h" eqp (e/app (noconf (e/bvar 0)) inner) :default))))))

(defn- nat-lit-ne-false-proof
  "Result proving `(a = b) = False` for distinct concrete Nat terms (literals or
   succ/zero forms). Faithful intent of Lean's Nat.reduceEqDiff, but proof-carrying
   via noConfusion so it is sound in a decide-lemma-free env. nil if not applicable."
  [st expr a b]
  (when-let [neg (nat-ne-neg st a b)]
    {:expr (e/const' false-name [])
     :proof? (e/app* (e/const' eq-false-name []) expr neg)
     :cache true}))

(defn- nat-type?
  [st alpha]
  (let [w (#'tc/cached-whnf st alpha)]
    (and (e/const? w) (= (e/const-name w) nat-name))))

(defn- mk-ctor-ne-false-proof
  "Build a kernel-checkable proof of `(t1 = t2) = False` for distinct constructors of
   the same parameter-free inductive, faithful to Lean 4's reduceCtorEq:
       eq_false (fun h : t1 = t2 => @Ind.noConfusion.{0,us} False t1 t2 h)
   `Ind.noConfusionType False t1 t2` reduces to `False` (the kernel whnfs the discrs),
   so the inner term inhabits False and `eq_false` lifts `¬(t1=t2)` to `(t1=t2)=False`.
   Restricted to the SIMPLE homogeneous noConfusion telescope [P, t, t', h] (4 binders)
   — parametrized/indexed inductives use the heterogeneous HEq form and are left to the
   decide-based path. Returns a proof-carrying Result, or nil if not buildable."
  [st expr alpha]
  (let [[ahead _] (e/get-app-fn-args alpha)]
    (when (e/const? ahead)
      (let [env (:env st)
            ind-name (e/const-name ahead)
            ind-levels (e/const-levels ahead)
            noconf-name (name/mk-str ind-name "noConfusion")
            noconf-ci (env/lookup env noconf-name)]
        (when noconf-ci
          (let [nty (.type ^ConstantInfo noconf-ci)
                arity (loop [t nty n 0] (if (e/forall? t) (recur (e/forall-body t) (inc n)) n))]
            (when (= arity 4)                       ;; simple [P t t' h] form only
              (let [[_ args] (e/get-app-fn-args expr)
                    t1 (nth args 1) t2 (nth args 2)
                    neg (e/lam "h" expr
                               (e/app* (e/const' noconf-name (cons lvl/zero ind-levels))
                                       (e/const' false-name []) t1 t2 (e/bvar 0))
                               :default)
                    proof (e/app* (e/const' eq-false-name []) expr neg)]
                {:expr (e/const' false-name []) :proof? proof :cache true}))))))))

(defn- try-reduce-ctor-eq
  "Reduce constructor equality to False when constructors differ — Lean 4's reduceCtorEq
   (BuiltinSimprocs/Core.lean). Builds a real `(t1=t2)=False` proof via noConfusion+eq_false.
   `false=true → False` is PROPOSITIONAL, not definitional, so a nil/rfl proof would be
   unsound (it desyncs the simp Result's :expr from its proof RHS in the Eq.trans chain).
   Literal disequalities (0=1, distinct strings) are left to the decide-based path
   (try-simp-using-decide), which certifies them via eq_false_of_decide."
  [st expr]
  (let [[head args] (e/get-app-fn-args expr)]
    (when (and (e/const? head)
               (= (e/const-name head) eq-name)
               (= 3 (count args)))
      (let [alpha (nth args 0)]
        (or
          ;; Nat: distinct concrete values (literals / succ / zero), recursive noConfusion.
         (when (nat-type? st alpha)
           (nat-lit-ne-false-proof st expr (nth args 1) (nth args 2)))
          ;; Distinct named constructors of the same inductive (Bool, etc.) — simple
          ;; noConfusion. (Same-ctor and non-Nat literals fall through to decide.)
         (let [lhs (#'tc/cached-whnf st (nth args 1))
               rhs (#'tc/cached-whnf st (nth args 2))
               [lh _] (e/get-app-fn-args lhs)
               [rh _] (e/get-app-fn-args rhs)]
           (when (and (e/const? lh) (e/const? rh)
                      (not= (e/const-name lh) (e/const-name rh)))
             (let [env (:env st)
                   lci (env/lookup env (e/const-name lh))
                   rci (env/lookup env (e/const-name rh))]
               (when (and lci rci
                          (.isCtor ^ConstantInfo lci)
                          (.isCtor ^ConstantInfo rci))
                 (let [lparent (name/name-prefix (e/const-name lh))
                       rparent (name/name-prefix (e/const-name rh))]
                   (when (and lparent rparent (= lparent rparent))
                     (mk-ctor-ne-false-proof st expr alpha))))))))))))

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
   Also finds conditional variants (eq_Nt, eq_Nf) and inner-split variants
   (eq_N_M from nested match splitting) for Bool-split branches."
  [env decl-name]
  (loop [i 1 result []]
    (let [base-name (name/mk-str decl-name (str "eq_" i))
          base-ci (env/lookup env base-name)
          ;; Also check conditional variants
          true-name (name/mk-str decl-name (str "eq_" i "t"))
          true-ci (env/lookup env true-name)
          false-name (name/mk-str decl-name (str "eq_" i "f"))
          false-ci (env/lookup env false-name)
          ;; Check leaf-level split variants (Lean 4 style: flat sequential).
          ;; Names: eq_Ns1, eq_Ns2, ... (one per leaf of match tree).
          split-names (loop [j 1 splits []]
                        (let [sn (name/mk-str decl-name (str "eq_" i "s" j))]
                          (if (env/lookup env sn)
                            (recur (inc j) (conj splits sn))
                            splits)))
          found (cond-> (vec split-names)
                  base-ci (conj base-name)
                  true-ci (conj true-name)
                  false-ci (conj false-name))]
      (if (seq found)
        (recur (inc i) (into result found))
        ;; No more direct equations — also search for auxiliary matcher equations.
        ;; Lean 4: each nested match becomes a named matcher with its own equations.
        ;; We generate these as fn._match_N with their own eq_1, eq_2, etc.
        (let [aux-results (loop [m 1 aux-acc []]
                            (let [aux-name (name/mk-str decl-name (str "_match_" m))]
                              (if-let [aux-eqns (when (env/lookup env aux-name)
                                                  (find-eqn-theorems env aux-name))]
                                (recur (inc m) (into aux-acc aux-eqns))
                                aux-acc)))]
          (when (seq (into result aux-results))
            (into result aux-results)))))))

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
            a (get-nat-value? st (nth args 4))
            b (get-nat-value? st (nth args 5))]
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
        (let [env (:env st)
              inst-index (if-let [idx (:inst-index config)]
                           (if (instance? clojure.lang.Delay idx) @idx idx)
                           (inst/index-for env))
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

                :else nil))))))))

(declare try-fold-bool-and)

(defn- try-reduce-proj-fn
  "Reduce a projection FUNCTION applied to a constructor: `Prod.fst α β (Prod.mk
   α β a b)` → `a` (Lean 4: reduceProjFn?). Needed because simp matches at
   `reducible` transparency, whose whnf does not unfold a projection function — so
   without this, projections inside e.g. a match discriminant never reduce. A
   projection function's value is `fun params… => structParam.idx` (body is an
   e/proj on a bound param); we whnf the corresponding struct arg and, if it is a
   constructor application, return the projected field. Definitional ⇒ nil proof."
  [st expr]
  (let [env (:env st)
        [head args] (e/get-app-fn-args expr)]
    (when (and (e/const? head) (seq args))
      (when-let [ci (env/lookup env (e/const-name head))]
        (when-let [v (and (= 0 (.hints ci)) (.getValue ci))]   ; reducible (abbrev) def
          (loop [body v np 0]
            (cond
              (e/lam? body) (recur (e/lam-body body) (inc np))
              (and (e/proj? body) (e/bvar? (e/proj-struct body)) (= (count args) np))
              (let [j (e/bvar-idx (e/proj-struct body))
                    struct-arg (nth args (- np 1 j))
                    ;; whnf the struct WITHOUT delta: we reduce projections of an
                    ;; EXPLICIT constructor (data, e.g. `Prod.mk x head`), but do NOT
                    ;; unfold a named typeclass instance (`instLTNat`, `instAddNat`)
                    ;; to reduce its method projection — that collapses `LT.lt→Nat.lt`,
                    ;; `Add.add→Nat.add`, `OfNat.ofNat→lit` etc., which strips the
                    ;; typeclass forms that downstream decision procedures (omega) match
                    ;; on and exposes a buggy `Nat.lt` equation lemma (malformed `1`).
                    sw (red/whnf-no-delta (:env st) struct-arg (:lctx st))
                    [sh sargs] (e/get-app-fn-args sw)]
                (when (e/const? sh)
                  (when-let [cci (env/lookup env (e/const-name sh))]
                    (when (.isCtor ^ConstantInfo cci)
                      (let [fidx (+ (.numParams ^ConstantInfo cci) (e/proj-idx body))]
                        (when (< fidx (count sargs))
                          (mk-result (nth sargs fidx))))))))
              :else nil)))))))

(defn- ctor-headed?
  "After whnf-no-delta, is `e` headed by a constructor / Nat literal? Used as a
   cheap gate: a matcher only iota-reduces when a discriminant is concrete."
  [st e]
  (let [w (red/whnf-no-delta (:env st) e (:lctx st))]
    (or (e/lit-nat? w)
        (let [[h _] (e/get-app-fn-args w)]
          (and (e/const? h)
               (when-let [ci (env/lookup (:env st) (e/const-name h))]
                 (.isCtor ^ConstantInfo ci)))))))

(defn- try-reduce-matcher
  "reduceRecMatcher? (Lean 4): reduce a matcher auxiliary `T.match_N … discr …
   (fun _:Unit => bᵢ) …` when a discriminant is a constructor, to the SELECTED
   branch bₖ — without over-reducing bₖ. A naive full whnf would keep unfolding a
   non-constructor-headed branch (e.g. `List.filter` → `brecOn.go`/`below` monster).
   Technique: replace each Unit-thunk alternative's body with a fresh opaque marker
   fvar, full-whnf the matcher (the markers block any over-reduction past the iota
   step), and if the head reduces to exactly one marker, return that alternative's
   real body (β-applied to `Unit.unit`, as the matcher would). Definitional ⇒ nil
   proof. Restricted to Unit-thunk alts (the form Lean emits for matches whose cases
   bind no discriminant fields, e.g. a `Bool`/`Nat`-comparison match) so replacing a
   body with a closed marker never drops a captured field."
  [st expr]
  (let [env (:env st)
        [head args] (e/get-app-fn-args expr)]
    (when (and (e/const? head)
               (>= (count args) 2)
               (re-find #"\.match_\d+$" (name/->string (e/const-name head))))
      (let [n (count args)
            ;; trailing contiguous lambda args = the alternatives
            alt-start (loop [i n] (if (and (> i 0) (e/lam? (nth args (dec i)))) (recur (dec i)) i))
            alts (subvec (vec args) alt-start)
            unit? (fn [a] (let [t (e/lam-type a)]
                            (and (e/const? t) (= "Unit" (name/->string (e/const-name t))))))]
        (when (and (seq alts) (every? unit? alts)
                   ;; cheap gate: some discriminant (a non-alt arg) is concrete
                   (some #(ctor-headed? st %) (subvec (vec args) 0 alt-start)))
          (let [unit-unit (e/const' (name/from-string "Unit.unit") [])
                marker-id (fn [i] (+ 920000 i))
                new-alts (mapv (fn [a i]
                                 (e/lam (e/lam-name a) (e/lam-type a)
                                        (e/fvar (marker-id i)) (e/lam-info a)))
                               alts (range))
                marker->body (into {} (map-indexed
                                       (fn [i a] [(marker-id i)
                                                  (e/instantiate1 (e/lam-body a) unit-unit)])
                                       alts))
                probe (apply e/app* head (into (subvec (vec args) 0 alt-start) new-alts))
                reduced (red/whnf env probe (:lctx st))]
            (when (and reduced (e/fvar? reduced)
                       (contains? marker->body (e/fvar-id reduced)))
              (mk-result (get marker->body (e/fvar-id reduced))))))))))

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
      (try-reduce-proj-fn st expr)
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
                bool-true (e/const' (name/from-string "Bool.true") [])
                constant-motive? (let [m (#'tc/cached-whnf st motive)]
                                   (and (e/lam? m) (not (e/has-loose-bvars? (e/lam-body m)))))]
            (or
             ;; Raw Bool.rec is our match encoding. Lean Simp/Rewrite.lean
             ;; simpMatchCore uses equation proofs; equal branches are not def-eq
             ;; to a stuck recursor. Prove this equation by Bool induction.
             (when (and constant-motive? (tc/is-def-eq st fc tc))
               (let [alpha (tc/infer-type st fc)
                     u (get-sort-level st alpha)
                     rec-b (e/app* head (e/lift motive 1 0) (e/lift fc 1 0)
                                   (e/lift tc 1 0) (e/bvar 0))
                     eq-motive (e/lam "b" bool-type
                                      (e/app* (e/const' eq-name [u])
                                              (e/lift alpha 1 0) rec-b (e/lift fc 1 0)) :default)
                     refl (e/app* (e/const' eq-refl-name [u]) alpha fc)
                     h (e/app* (e/const' (name/from-string "Bool.rec") [lvl/zero])
                               eq-motive refl refl discr)]
                 (mk-result fc h)))
             ;; Strategy 2: simpMatch — simplify discriminant with full simp.
             ;; Lean Simp/Rewrite.lean simpMatchDiscrs? applies full simp to the
             ;; discriminant even though CongrArgKind marks it :fixed. If the
             ;; discriminant reduces to true/false, the Bool.rec reduces.
             (when (and constant-motive? env lemma-index)
               (let [d-result (simp-expr* st env lemma-index discr
                                          (assoc config
                                                 :max-depth (min 10 (:max-depth config))
                                                 :cache (atom {})
                                                 :max-steps (atom 0)))
                     dw (#'tc/cached-whnf st (:expr d-result))
                     ;; Lean simpMatchDiscrs? uses congruence; discriminant
                     ;; rewriting may itself need a propositional equality proof.
                     r (when (not= discr (:expr d-result))
                         (mk-congr-arg st (e/app* head motive fc tc) d-result discr (:expr d-result)))]
                 (when r
                   (let [result (cond
                                  (= dw bool-true) tc
                                  (= dw bool-false) fc
                                  :else (:expr r))]
                     (assoc r :expr result)))))
             ;; Strategy 3: Bool.rec identity — Bool.rec (fun _ => Bool) false true b = b
             ;; Lean 4: simpMatch recognizes when the recursor is the identity.
             ;; Proof: Bool.rec (fun b => Eq Bool (Bool.rec ... b) b) rfl rfl discr
             (when (and (tc/is-def-eq st fc bool-false)
                        (tc/is-def-eq st tc bool-true))
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
      ;; reduceRecMatcher? — matcher applied to a constructor discriminant reduces
      ;; to the selected branch (one controlled iota step, no branch over-reduction).
      (try-reduce-matcher st expr)
      ;; General matcher auxiliary (`*.match_N`): simplify its discriminant args so
      ;; projections / redexes inside a scrutinee reduce (Lean 4: simpMatchDiscrs?,
      ;; Simp/Rewrite.lean). e.g. `List.filter.match_1 (p (Prod.fst (Prod.mk x h))) …`
      ;; → `… (p x) …`. We commit only DEFINITIONAL changes (the sub-simp returned a
      ;; nil/rfl proof), so rebuilding the matcher with the reduced discriminant is
      ;; sound without an explicit congruence proof. Non-lambda args are the
      ;; discriminants; motive/alternatives are lambdas and are left to congruence.
      (when (and env lemma-index)
        (let [[head args] (e/get-app-fn-args expr)]
          (when (and (e/const? head) (>= (count args) 2)
                     (re-find #"\.match_\d+$" (name/->string (e/const-name head))))
            (let [dconf (assoc config :max-depth (min 8 (or (:max-depth config) 8))
                               :cache (atom {}) :max-steps (atom 0))
                  ;; Simp each non-lambda arg (the discriminants); motive/alternatives are lambdas → rfl.
                  ;; Keep the FULL result (it may carry a propositional proof, e.g. a `beq … = false`
                  ;; rewrite using a hypothesis), not just the def-eq cases.
                  results (mapv (fn [arg]
                                  (if (e/lam? arg)
                                    (mk-result arg)
                                    (or (simp-expr* st env lemma-index arg dconf)
                                        (mk-result arg))))
                                args)
                  changed? (some (fn [[a r]] (not (identical? (:expr r) a)))
                                 (map vector args results))]
              (when changed?
                ;; If every discriminant change is DEFINITIONAL (nil proof) we can rebuild the matcher
                ;; with no proof (cheap path, also lets reduceRecMatcher? reduce when a discriminant
                ;; became a constructor by reduction). If a change carries a PROOF, build the
                ;; app-congruence faithfully — Lean's generic congruence over the matcher application
                ;; simplifies the discriminants WITH a proof (our CongrArgKind marks them :fixed, so the
                ;; normal congruence skips them, hence we do it here), after which reduceRecMatcher? iota-
                ;; reduces on the next pass. Fold mk-congr over the args; verify the proof type-checks
                ;; (congrArg is ill-typed for a dependent motive), else fall back to the def-eq commit.
                ;; def-eq-only commit: keep the simplified expr ONLY for discriminants whose change was
                ;; definitional (nil proof); revert propositional changes to the original arg (committing
                ;; a propositional change with a nil/rfl proof would be unsound).
                (let [deq-only (mk-result (apply e/app* head
                                                 (mapv (fn [a r] (if (nil? (:proof? r)) (:expr r) a))
                                                       args results)))]
                  (if-not (some (fn [r] (some? (:proof? r))) results)
                    deq-only
                    (let [[folded _]
                          (reduce (fn [[facc orig-f] [orig-arg r]]
                                    [(mk-congr st facc r orig-f orig-arg)
                                     (e/app orig-f orig-arg)])
                                  [(mk-result head) head]
                                  (map vector args results))
                          ok (and (:proof? folded)
                                  (let [pt (safe-infer st (:proof? folded))
                                        ptw (when pt (safe-whnf st pt))
                                        [h as] (when ptw (e/get-app-fn-args ptw))]
                                    (and h (e/const? h) (= (e/const-name h) eq-name) (= 3 (count as))
                                         (tc/is-def-eq st (nth as 1) expr))))]
                      (if ok folded deq-only)))))))))
      (try-ground-eval st (:env st) expr)
      (try-simp-using-decide st expr config)
      ;; User-registered simprocs: dynamic var + persistent registry
      (some (fn [sp]
              (try (sp st expr)
                   (catch clojure.lang.ExceptionInfo ex
                     (if (and (= :tactic-error (:kind (ex-data ex)))
                              (not (:limit (ex-data ex)))
                              (not (:proof-construction (ex-data ex)))) nil (throw ex)))))
            (concat config/*simprocs*
                    (deref @(requiring-resolve 'ansatz.core/simproc-registry))))))

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
              ;; definitions only: theorems are opaque to unfolding (lean4#12973 —
              ;; Meta.unfoldDefinition?/getUnfoldableConst? no longer look through them)
              (when (.isDef ci)
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
  "Definitional simplification; the legacy fourth argument is ignored."
  [env lctx expr _max-depth]
  ;; Lean Simp/Main.lean dsimpImpl / Meta/Transform.lean transformWithCache:
  ;; cache hits precede guarded visits. Cache identity preserves DAG sharing;
  ;; it is local to this traversal's environment and local context.
  (let [cache (java.util.IdentityHashMap.)]
    (letfn [(visit [expr]
              (if-let [hit (.get cache expr)]
                hit
                (with-inc-rec-depth 1 expr
                  (if-not (instance? ansatz.kernel.Expr expr)
                    expr
                    (let [original expr
                          reduced (red/whnf-no-delta env expr lctx)
                          expr (if (= reduced expr) expr reduced)
                          result
                          (case (e/tag expr)
                            :app (let [f (visit (e/app-fn expr))
                                       a (visit (e/app-arg expr))
                                       rebuilt (if (and (identical? f (e/app-fn expr))
                                                        (identical? a (e/app-arg expr)))
                                                 expr (e/app f a))]
                                   (red/whnf-no-delta env rebuilt lctx))
                            :lam (let [t (visit (e/lam-type expr)) b (visit (e/lam-body expr))]
                                   (if (and (identical? t (e/lam-type expr))
                                            (identical? b (e/lam-body expr)))
                                     expr (e/lam (e/lam-name expr) t b (e/lam-info expr))))
                            :forall (let [t (visit (e/forall-type expr))
                                          b (visit (e/forall-body expr))]
                                      (if (and (identical? t (e/forall-type expr))
                                               (identical? b (e/forall-body expr)))
                                        expr (e/forall' (e/forall-name expr) t b (e/forall-info expr))))
                            :let (visit (e/instantiate1 (e/let-body expr) (e/let-value expr)))
                            :proj (let [v (visit (e/proj-struct expr))]
                                    (if (identical? v (e/proj-struct expr)) expr
                                        (red/whnf-no-delta env
                                                           (e/proj (e/proj-type-name expr)
                                                                   (e/proj-idx expr) v) lctx)))
                            :mdata (visit (e/mdata-expr expr))
                            expr)]
                      (.put cache original result)
                      result)))))]
      (visit expr))))

;; ============================================================
;; Simplification engine — Lean 4's simpLoop
;; ============================================================

(defn- is-proof-term?
  "Check if an expression is a proof (inhabits a Prop).
   Lean 4: isProof e checks that type(e) : Prop, i.e., type(type(e)) = Sort 0.
   NOT the same as 'is a proposition' — Eq Nat 1 0 is a Prop (type), not a proof."
  [st expr]
  (let [ty (tc/infer-type st expr)        ;; type of expr
        ty-sort (tc/infer-type st ty)      ;; type of type (should be Sort u)
        tw (#'tc/cached-whnf st ty-sort)]
      ;; expr is a proof iff its type's type is Prop (Sort 0)
      ;; i.e., type(expr) : Prop means expr IS a proof
    (and (e/sort? tw) (= (e/sort-level tw) lvl/zero))))

(defn- is-prop-type?
  "Check if a type lives in Prop."
  [st ty]
  (let [s (tc/infer-type st ty) sw (#'tc/cached-whnf st s)]
    (and (e/sort? sw) (= (e/sort-level sw) lvl/zero))))

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
                          proof (cond
                                  (:proof-term lemma)
                                  (reduce e/app (:proof-term lemma) (reverse param-vals))
                                  (:hyp-fvar-id lemma)
                                  (reduce e/app (e/fvar (:hyp-fvar-id lemma)) (reverse param-vals))
                                  :else (reduce e/app
                                                (e/const' (:name lemma) inst-levels)
                                                (reverse param-vals)))]
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
              (with-inc-rec-depth 1 e
                (case (e/tag e)
                  :bvar (when (>= (e/bvar-idx e) d)
                          (vswap! result conj (- (e/bvar-idx e) d)))
                  :app (do (walk (e/app-fn e) d) (walk (e/app-arg e) d))
                  :lam (do (walk (e/lam-type e) d) (walk (e/lam-body e) (inc d)))
                  :forall (do (walk (e/forall-type e) d) (walk (e/forall-body e) (inc d)))
                  :let (do (walk (e/let-type e) d) (walk (e/let-value e) d) (walk (e/let-body e) (inc d)))
                  :proj (walk (e/proj-struct e) d)
                  :mdata (walk (e/mdata-expr e) d)
                  nil)))]
      (walk expr depth))
    @result))

;; Per-env cache to avoid stale entries across environments
(def ^:private fun-info-cache (atom {}))
(def ^:private fun-info-cache-env (atom nil))

(defn capture-caches
  "Capture the immutable function-information cache and its exact Env identity."
  []
  {:env @fun-info-cache-env :entries @fun-info-cache})

(defn validate-caches! [snapshot]
  (when-not (and (map? snapshot) (= #{:env :entries} (set (keys snapshot)))
                 (or (nil? (:env snapshot)) (instance? ansatz.kernel.Env (:env snapshot)))
                 (map? (:entries snapshot)))
    (throw (ex-info "Invalid simp function-information cache snapshot" {})))
  snapshot)

(defn restore-caches! [snapshot]
  (validate-caches! snapshot)
  (reset! fun-info-cache (:entries snapshot))
  (reset! fun-info-cache-env (:env snapshot))
  snapshot)

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
        (let [fn-type (safe-infer st fn-expr)]
          (when fn-type
            (let [;; Walk forall telescope up to nargs
                  info
                  (loop [ty fn-type i 0 params [] xs [] local-st st]
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
                            ;; Lean Meta/FunInfo.lean getFunInfoAux opens the telescope.
                            opened-type (e/instantiate param-type xs)
                            xid (swap! (:next-id st) inc)
                            is-prop (let [s (tc/infer-type local-st opened-type)
                                          sw (#'tc/cached-whnf local-st s)]
                                      (and (e/sort? sw) (= (e/sort-level sw) lvl/zero)))
                            is-inst (= binfo :inst-implicit)]
                        (recur (e/forall-body ty) (inc i)
                               (conj params {:binder-info binfo
                                             :back-deps back-deps
                                             :has-fwd-deps false  ;; computed in post-pass
                                             :is-prop is-prop
                                             :is-instance is-inst})
                               (conj xs (e/fvar xid))
                               (update local-st :lctx assoc xid {:type opened-type})))))]
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

(defn- simp-proj
  "Lean Meta/Tactic/Simp/Main.lean simpProj, v4.33.1: transport a projection
   equality with Eq.ndrec; dependent fields permit only dsimp."
  [st env lemma-index expr config]
  (let [struct (e/proj-struct expr)
        struct-type (tc/infer-type st struct)
        fid (swap! (:next-id st) inc)
        fv (e/fvar fid)
        st' (update st :lctx red/lctx-add-local fid "s" struct-type)
        projected (e/proj (e/proj-type-name expr) (e/proj-idx expr) fv)
        field-type (tc/infer-type st' projected)]
    (if (not= field-type (e/abstract1 field-type fid))
      (mk-result (dsimp-expr env (:lctx st) expr (:max-depth config)))
      (let [v (get-sort-level st' field-type)
            motive (e/lam "s" struct-type
                          (e/abstract1 (e/app* (e/const' eq-name [v])
                                               field-type expr projected) fid) :default)
            _ (tc/infer-type st motive)
            r (simp-expr* st env lemma-index struct (update config :max-depth dec))
            result (e/proj (e/proj-type-name expr) (e/proj-idx expr) (:expr r))]
        (if-let [h (:proof? r)]
          (mk-result result
                     (e/app* (e/const' (name/from-string "Eq.ndrec")
                                       [lvl/zero (get-sort-level st struct-type)])
                             struct-type struct motive
                             (e/app* (e/const' eq-refl-name [v]) field-type expr)
                             (:expr r) h))
          (mk-result result))))))

(defn- simp-subterms
  "Simplify subterms (congruence step).
   Dispatches by expression type, builds proper congruence proofs."
  [st env lemma-index expr config]
  (let [max-depth (:max-depth config)]
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
                                   (get-fun-info st env app-fn (count app-args)))
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
                        arg-kind (cond
                                  ;; Override 1: recursor discriminant with constant motive → :eq
                                   (and (= raw-kind :fixed)
                                        (e/const? app-fn)
                                        (let [n (name/->string (e/const-name app-fn))]
                                          (or (= n "Bool.rec") (= n "List.rec")
                                              (.endsWith ^String n ".rec")
                                              (.endsWith ^String n ".casesOn")))
                                        (= arg-idx (dec (count app-args)))
                                        (let [motive (first app-args)]
                                          (and (e/lam? motive)
                                               (not (e/has-loose-bvars? (e/lam-body motive) 0)))))
                                   :eq
                                  ;; Override 2: indexed family arg containing stuck Bool.rec → :eq
                                  ;; Without this, hypothesis lemmas can't reduce Bool.rec inside indices.
                                  ;; Lean 4 grind handles this via E-graph, not simp CongrArgKind.
                                   (and (= raw-kind :fixed)
                                        (let [found (atom false)
                                              seen (java.util.IdentityHashMap.)]
                                          (letfn [(scan [e]
                                                    (with-inc-rec-depth 1 e
                                                      (when-not (or @found (.containsKey seen e))
                                                        (.put seen e true)
                                                        (let [[h a] (e/get-app-fn-args e)]
                                                          (when (and (e/const? h)
                                                                     (= "Bool.rec" (name/->string (e/const-name h))))
                                                            (reset! found true)))
                                                        (when (e/app? e)
                                                          (scan (e/app-fn e))
                                                          (scan (e/app-arg e))))))]
                                            (scan orig-a))
                                          @found))
                                   :eq
                                   :else raw-kind)
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

        ;; Lambda — Lean 4: simpLambda (Main.lean:328) via lambdaTelescopeDSimp.
        ;; CRITICAL: open the binder with a FRESH FVAR before simplifying the body
        ;; (Lean: `withLocalDecl n c (← dsimp d) fun x => ... b.instantiate1 x`). Simp-ing
        ;; the CLOSED body (loose bvar 0, no lctx binding) corrupts de-Bruijn indices in
        ;; sub-congruence abstractions — e.g. a free type var inside the body gets
        ;; mis-abstracted, yielding ill-typed congrArg proofs. After simp, re-abstract:
        ;;   eNew = mkLambdaFVars [x] r.expr ;  proof = mkFunExt (mkLambdaFVars [x] h)
        ;; (Lean: Result.addLambdas, Types.lean:916).
      :lam (let [lam-type (e/lam-type expr)
                 lam-body (e/lam-body expr)
                 lam-nm (e/lam-name expr)
                 lam-bi (e/lam-info expr)
                   ;; dsimp the binder type (Lean: lambdaTelescopeDSimp dsimps `d`)
                 alpha (let [reduced (dsimp-expr env (:lctx st) lam-type (:max-depth config))]
                         (if (= reduced lam-type) lam-type reduced))
                   ;; OPEN the binder with a fresh fvar; simp the opened body in proper lctx
                 xid (swap! (:next-id st) inc)
                 xf (e/fvar xid)
                 st' (update st :lctx assoc xid {:name (str lam-nm) :type alpha})
                 body-x (e/instantiate1 lam-body xf)
                 b-r (simp-expr* st' env lemma-index body-x (update config :max-depth dec))]
             (if (and (identical? alpha lam-type)
                      (identical? (:expr b-r) body-x))
               (mk-result expr)
                 ;; Re-abstract: new lambda over the fresh fvar (mkLambdaFVars [x] expr).
               (let [new-body (e/abstract1 (:expr b-r) xid)
                     new-lam (e/lam lam-nm alpha new-body lam-bi)]
                 (if (nil? (:proof? b-r))
                     ;; Body change is definitional — no proof needed
                   (mk-result new-lam)
                     ;; funext.{u,v} α β f g (λx. proof x) : f = g
                     ;; β : α → Sort v is the (possibly DEPENDENT) result family,
                     ;; f = old lambda, g = new lambda. h = mkLambdaFVars [x] (proof x).
                   (let [u (get-sort-level st alpha)
                         beta-body (safe-infer st' body-x)           ; type of (f x)
                         v (if beta-body (get-sort-level st' beta-body) lvl/zero)
                         beta (e/lam lam-nm alpha
                                     (e/abstract1 (or beta-body (e/sort' v)) xid) :default)
                             ;; h = λx:α. proof(x), proof abstracted over the fresh fvar
                         proof-lam (e/lam lam-nm alpha (e/abstract1 (:proof? b-r) xid) :default)]
                     {:expr new-lam
                      :proof? (e/app* (e/const' funext-name [u v])
                                      alpha beta expr new-lam proof-lam)
                      :cache true})))))

        ;; Forall/arrow — Lean 4's simpForall/simpArrow
        ;; Per-binder contextual: add h:P as a simp lemma when simplifying Q
      :forall
      (let [is-arrow (not (e/has-loose-bvars? (e/forall-body expr) 0))
            orig-p (e/forall-type expr)
            orig-q (e/forall-body expr)]
        (if is-arrow
            ;; Arrow: P → Q
          (let [p-result (simp-expr* st env lemma-index orig-p (update config :max-depth dec))
                contextual? (and (:contextual? config)
                                 (is-prop-type? st orig-p) (is-prop-type? st orig-q))
                ;; Lean Simp/Main.lean simpArrow: withLocalDeclD + withNewLemmas.
                ;; The premise has an actual proof variable, scoped over the
                ;; consequent's proof with implies_congr_ctx (never a fake lemma).
                xid (when contextual? (swap! (:next-id st) inc))
                decl (when contextual? {:tag :local :id xid :name "h" :type (:expr p-result)})
                st' (if contextual? (update st :lctx assoc xid decl) st)
                q-index (if contextual?
                          (reduce (fn [idx lemma]
                                    (dt/trie-insert idx (dt/expr->keys st' env (:lhs-pattern lemma)) lemma))
                                  lemma-index (make-hyp-lemmas st' {xid decl}))
                          lemma-index)
                q-result (simp-expr* st' env q-index orig-q
                                     (cond-> (update config :max-depth dec)
                                       contextual? (assoc :cache (atom {}))))]
            (if (and contextual? (:proof? q-result))
              (let [p (:expr p-result)
                    q (:expr q-result)
                    hq (e/lam "h" p (e/abstract1 (:proof? q-result) xid) :default)
                    hp (or (:proof? p-result)
                           (e/app* (e/const' eq-refl-name [(lvl/succ lvl/zero)])
                                   (e/sort' lvl/zero) orig-p))
                    dependent? (not= q (e/abstract1 q xid))
                    q' (e/abstract1 q xid)]
                (if dependent?
                  (mk-result (e/forall' "h" p q' :default)
                             (e/app* (e/const' (name/from-string "implies_dep_congr_ctx") [])
                                     orig-p p orig-q hp (e/lam "h" p q' :default) hq))
                  (mk-result (e/arrow p q)
                             (e/app* (e/const' (name/from-string "implies_congr_ctx") [])
                                     orig-p p orig-q q hp hq))))
              (if (and (is-prop-type? st orig-p) (is-prop-type? st orig-q))
                (mk-implies-congr st p-result q-result orig-p orig-q)
                (mk-result (e/forall' (e/forall-name expr) (:expr p-result)
                                      (:expr q-result) (e/forall-info expr))))))
            ;; Lean Simp/Main.lean simpForall: open the binder before
            ;; inferring/simplifying its body, then reabstract with forall_congr.
          (if-not (is-prop-type? st expr)
            (mk-result (dsimp-expr env (:lctx st) expr (:max-depth config)))
            (let [domain (dsimp-expr env (:lctx st) orig-p (:max-depth config))
                  xid (swap! (:next-id st) inc)
                  xf (e/fvar xid)
                  st' (update st :lctx assoc xid {:tag :local :id xid
                                                  :name (str (e/forall-name expr)) :type domain})
                  body (e/instantiate1 orig-q xf)
                  rb (simp-expr* st' env lemma-index body (assoc config :cache (atom {})))
                  new-body (e/abstract1 (:expr rb) xid)
                  result (e/forall' (e/forall-name expr) domain new-body (e/forall-info expr))]
              (if-let [h (:proof? rb)]
                (let [u (get-sort-level st domain)
                      p (e/lam (e/forall-name expr) domain orig-q (e/forall-info expr))
                      q (e/lam (e/forall-name expr) domain new-body (e/forall-info expr))
                      h (e/lam (e/forall-name expr) domain (e/abstract1 h xid) (e/forall-info expr))]
                  (mk-result result
                             (e/app* (e/const' (name/from-string "forall_congr") [u]) domain p q h)))
                (if (= result expr) (mk-result expr) (mk-result result)))))))

        ;; Let — zeta reduce
      :let (let [expanded (e/instantiate1 (e/let-body expr) (e/let-value expr))]
             (simp-expr* st env lemma-index expanded config))

      :proj (simp-proj st env lemma-index expr config)

        ;; Mdata — unwrap
      :mdata (simp-expr* st env lemma-index (e/mdata-expr expr) config)

        ;; Atoms
      (mk-result expr))))

(def ^:dynamic *simp-trace*
  "When bound to an atom, simp-expr* logs rewrites for debugging.
   Each entry: {:expr-before :expr-after :phase :depth :lemma-name}"
  nil)

(defn- cached-result [cache expr]
  (when-let [result (if (instance? ExprMap cache) (.get ^ExprMap cache expr)
                        (when cache (get @cache expr)))]
    ;; Lean's expression cache equates separately allocated equal nodes. Reuse
    ;; the caller's node when unchanged, preserving sharing through congruence.
    (if (and (not (identical? expr (:expr result)))
             (.equals (LeanExprKey. expr) (LeanExprKey. (:expr result))))
      (assoc result :expr expr) result)))

(defn- simp-expr*
  "Core simplification loop (Lean 4's simpLoop).
   config: {:max-depth :single-pass? :max-steps :cache :to-unfold :discharge-depth}"
  [st env lemma-index expr config]
  ;; Lean Simp/Main.lean simpLoop returns cached results before doing work.
  (if-let [cached (cached-result (:cache config) expr)]
    cached
    ;; The merged entry accounts for simpImpl and simpLoop's two frames.
    (with-inc-rec-depth 2 expr
      (if-let [on-step (:on-step config)]
        (on-step)
        (when-let [steps (:max-steps config)]
          (when (> @steps config/*max-simp-steps*)
            (tactic-error! "maximum number of steps exceeded" {:expr expr :limit :max-simp-steps}))
          (swap! steps inc)))

    ;; Lean simpLoop also bounds total rewrite work with maxSteps.
    ;; Check cache
      (let [cache (:cache config)
            cached (cached-result cache expr)]
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
              (let [dt-cands (lookup-lemmas st env lemma-index expr config)
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
              (if (instance? ExprMap cache) (.put ^ExprMap cache expr result)
                  (swap! cache assoc expr result)))
            result))))))

;; Public wrapper
(defn simp-expr
  "Simplify an expression. Returns the simplified expression.
   The legacy max-depth argument is ignored; max-simp-steps bounds rewriting."
  ([st env lemma-index expr max-depth]
   (simp-expr st env lemma-index expr max-depth #{}))
  ([st env lemma-index expr max-depth to-unfold]
   (:expr (simp-expr* st env lemma-index expr
                      {:max-depth max-depth :single-pass? false
                       :max-steps (atom 0) :cache (atom {})
                       :to-unfold to-unfold :discharge-depth 0}))))

(defn simp-expr-result
  "Like `simp-expr` but returns the full SimpResult `{:expr Expr, :proof? (Option
   Expr)}` — `:proof?` is an equality proof `orig = result` (nil means rfl, i.e.
   no rewrite or definitional). Used by the verified optimizer to obtain both the
   rewritten term and its kernel-checkable proof."
  ([st env lemma-index expr] (simp-expr-result st env lemma-index expr 20))
  ([st env lemma-index expr max-depth]
   (simp-expr-result st env lemma-index expr max-depth {}))
  ([st env lemma-index expr max-depth state]
   ;; Grind/Simp.lean simpCore reuses Simp.State across calls. :on-step runs
   ;; only after the simpLoop cache miss, including recursive/discharger work.
   (simp-expr* st env lemma-index expr
               (merge {:max-depth max-depth :single-pass? false
                       :max-steps (atom 0) :cache (atom {})
                       :to-unfold #{} :discharge-depth 0} state))))

;; ============================================================
;; Public API
;; ============================================================

(def default-simp-priority
  "Lean's `eval_prio default`: the priority a @[simp] lemma has unless the attribute says
   otherwise. `build-lemma-index` and `rewriteUsingIndex?` both order candidates by
   descending priority, so this is the number everything else is relative to."
  1000)

(defn make-simp-lemmas
  "Create simp lemma entries from a list of constant names.
   Flattens vector returns from extract-simp-lemma (e.g. And splitting).

   Honours Lean's per-lemma @[simp] PRIORITY, inherited via the env's :simp-priorities
   extension (ansatz.attrs). This is not a nicety: `Bool.false_eq : (false = b) = (b = false)`
   and `Bool.true_eq : (true = b) = (b = true)` rewrite each other's output and are confluent
   only because Lean marks them `@[simp low]`, letting `Bool.false_eq_true`/`Bool.true_eq_false`
   (default priority, both collapsing to `False`) fire first. At a flat priority simp
   oscillates between the two orientations until it hits its step limit."
  [env lemma-names]
  (let [prios (env/get-extension env :simp-priorities {})]
    (vec (mapcat (fn [n]
                   (let [cname (if (instance? ansatz.kernel.Name n) n (name/from-string (str n)))
                         ci (env/lookup env cname)]
                     (when ci
                       (extract-simp-lemma env ci (get prios (name/->string cname)
                                                       default-simp-priority)))))
                 lemma-names))))

(def ^:private simp-only-builtins
  "Lean 4's `simpOnlyBuiltins` (Elab/Tactic/Simp.lean): the ONLY lemmas `simp only` starts
   with — the reflexive closers — before adding the user-given lemmas. No default @[simp] set,
   no simprocs. Lean core spells them `eq_self : (a = a) = True` and `iff_self : (p ↔ p) = True`
   (`eq_self_iff_true` is the MATHLIB name and resolves against nothing on the Init tier — it was
   spelled that way here, and `simp only` therefore started with an empty lemma set)."
  ["eq_self" "iff_self"])

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
   ;; Eq  (Lean core's name; `eq_self_iff_true` is Mathlib's and resolved against nothing)
   "eq_self"
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

(defn ensure-ble-eq
  "Derive Nat.ble_eq if not already in env.
   Lean 4: @[simp] theorem ble_eq : (Nat.ble x y = true) = (x ≤ y)
   Proof: propext (Iff.intro Nat.le_of_ble_eq_true Nat.ble_eq_true_of_le)

   The bundled Init tier now SHIPS `Nat.ble_eq` (it is a root in scripts/init-store-roots.txt
   and pinned by ansatz.tactic.tactic-constants-test), so this is a no-op there. It stays for
   stores that predate that — a tier built without it would otherwise lose the Bool→Prop
   bridge for `≤` entirely, which is why it was written in the first place."
  [env]
  (let [ble-eq-name (name/from-string "Nat.ble_eq")]
    (when-not (env/lookup env ble-eq-name)
      (when (and (env/lookup env (name/from-string "Nat.le_of_ble_eq_true"))
                 (env/lookup env (name/from-string "Nat.ble_eq_true_of_le"))
                 (env/lookup env (name/from-string "propext"))
                 (env/lookup env (name/from-string "Iff.intro")))
        ;; Build: ∀ (x y : Nat), (Nat.ble x y = true) = (x ≤ y)
        ;; Proof: fun x y => propext (Iff.intro (Nat.le_of_ble_eq_true) (Nat.ble_eq_true_of_le))
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
          (env/check-constant env (env/mk-thm ble-eq-name [] full-type full-proof)))))))

(defn- ensure-nat-packing
  "Init/Data/Nat/Basic.lean add_eq/le_eq (Lean 55f80e10a3).
   Older Init exports omit these packing theorems. Derive their exact rfl
   statements so explicit `simp only` requests retain Lean's normal forms."
  [env lemma-names]
  (reduce
   (fn [env nm]
     (let [cn (name/from-string nm)]
       (if (or (env/lookup env cn) (not (some #(= nm (str %)) lemma-names)))
         env
         (let [nat (e/const' (name/from-string "Nat") [])
               x (e/bvar 1) y (e/bvar 0)
               add? (= nm "Nat.add_eq")
               lhs (e/app* (e/const' (name/from-string (if add? "Nat.add" "Nat.le")) []) x y)
               rhs (if add?
                     (e/app* (e/const' (name/from-string "HAdd.hAdd") [lvl/zero lvl/zero lvl/zero])
                             nat nat nat
                             (e/app* (e/const' (name/from-string "instHAdd") [lvl/zero])
                                     nat (e/const' (name/from-string "instAddNat") [])) x y)
                     (e/app* (e/const' (name/from-string "LE.le") [lvl/zero])
                             nat (e/const' (name/from-string "instLENat") []) x y))
               carrier (if add? nat (e/sort' lvl/zero))
               u (lvl/succ lvl/zero)
               type (e/app* (e/const' eq-name [u]) carrier lhs rhs)
               value (e/app* (e/const' eq-refl-name [u]) carrier lhs)
               bind (fn [ctor body] (ctor "x" nat (ctor "y" nat body :implicit) :implicit))]
           (env/check-constant env (env/mk-thm cn [] (bind e/forall' type) (bind e/lam value)))))))
   env ["Nat.add_eq" "Nat.le_eq"]))

(defn- try-close-eq-rfl
  "If expr is Eq T a b where a and b are def-eq, return rfl proof. Else nil."
  [st expr]
  (let [w (or (safe-whnf st expr) expr)
        [h a] (e/get-app-fn-args w)]
    (when (and (e/const? h) (= (e/const-name h) eq-name) (= 3 (count a)))
      (let [lhs (nth a 1) rhs (nth a 2)
            ;; tc/is-def-eq already uses the Java checker with this lctx.
            deq (tc/is-def-eq st lhs rhs)]
        (when deq
          (e/app* (e/const' eq-refl-name (e/const-levels h)) (nth a 0) lhs))))))

(defn- decide-goal
  "Preflight optional decide with the nonthrowing instance API."
  [ps]
  ;; Lean Simp/Rewrite.lean simpUsingDecide treats missing instances as inapplicable.
  ;; As in evalDecideCore, synthesis must share the goal's local context.
  (let [[ps idx] (#'decide-tac/get-instance-index ps)
        goal (proof/current-goal ps)
        prop (:type goal)
        env (:env ps)]
    ;; Lean Simp/Rewrite.lean simpUsingDecide: only closed terms (`e.hasFVar || e.hasMVar` → no-op)
    (when (e/has-fvar-flag (decide-tac/zeta-let-locals (:lctx goal) prop))
      (tactic-error! "decide: goal is not closed" {:goal prop}))
    (when-not (inst/synthesize* (tc/mk-tc-state env) env idx
                                (e/app (e/const' decidable-name []) prop) 0)
      (tactic-error! "no Decidable instance for goal" {:goal prop}))
    (decide-tac/decide ps)))

(defn- close-goal-with-proof
  "Try to close the goal using a simp result.
   Following Lean 4's simpTargetCore (Main.lean:780-790):
   - If simplified to True: close with of_eq_true
   - If simplified is an Eq with def-eq sides: close with rfl
   - Otherwise: replace goal type with simplified (via Eq.mpr)"
  ([ps goal st result lemma-names]
   (close-goal-with-proof ps goal st result lemma-names false))
  ([ps goal st result lemma-names target-core?]
   (close-goal-with-proof ps goal st result lemma-names target-core? true))
  ([ps goal st result lemma-names target-core? may-close-goal?]
   (let [simplified (:expr result)
         simplified-whnf (#'tc/cached-whnf st simplified)
        ;; For Eq.mpr, goal-type must match the eq-proof's LHS exactly.
        ;; simp-expr* may start from a WHNF'd or rewritten form, so the eq-proof's
        ;; LHS might differ from (:type goal). Extract the actual LHS from the proof.
         raw-goal-type (:type goal)
        ;; A proof-free simp step must be definitional equality. Check both
        ;; endpoints before assigning a goal or constructing Eq.mpr transport.
         _ (if-let [h (:proof? result)]
             (let [[head args] (e/get-app-fn-args (#'tc/cached-whnf st (tc/infer-type st h)))]
               (when-not (and (e/const? head) (= eq-name (e/const-name head))
                              (= 3 (count args))
                              (tc/is-def-eq st raw-goal-type (nth args 1))
                              (tc/is-def-eq st simplified (nth args 2)))
                 (tactic-error! "simp: invalid equality proof" {:proof-construction true :goal raw-goal-type})))
             (when-not (tc/is-def-eq st raw-goal-type simplified)
               (tactic-error! "simp: uncertified simplification" {:proof-construction true :goal raw-goal-type})))
        ;; Extract actual LHS/RHS from eq-proof for Eq.mpr consistency.
        ;; simp-expr* may WHNF before rewriting, so the proof's type endpoints
        ;; might differ from the raw input/output expressions.
         [goal-type simplified-from-proof]
         (if-let [proof (:proof? result)]
           (let [proof-type (tc/infer-type st proof)
                 proof-whnf (when proof-type (#'tc/cached-whnf st proof-type))
                 [head args] (when proof-whnf (e/get-app-fn-args proof-whnf))]
             (if (and head (e/const? head)
                      (= (e/const-name head) (name/from-string "Eq"))
                      (= 3 (count args)))
               [(nth args 1) (nth args 2)]
               [raw-goal-type nil]))
           [raw-goal-type nil])
        ;; Use proof-extracted simplified if available, otherwise the raw simp result
         simplified (or simplified-from-proof simplified)]
     (cond
       ;; Lean SplitIf.lean simpIfTarget uses simpTarget (mayCloseGoal := false).
       ;; Keep even True and reflexive targets available to the branch tactics.
       (not may-close-goal?)
       (if (= simplified raw-goal-type) ps
         (let [goal-sort (#'tc/cached-whnf st (tc/infer-type st goal-type))
               [ps child] (proof/fresh-mvar-replacing ps simplified (:lctx goal) (:id goal))]
           (-> (proof/assign-mvar ps (:id goal)
                                  {:kind :simp-reduce :eq-proof (:proof? result)
                                   :child child :mpr-level (e/sort-level goal-sort)
                                   :goal-type goal-type :simplified simplified})
               (proof/record-tactic :simp lemma-names (:id goal)))))

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
         (try (decide-goal ps)
              (catch clojure.lang.ExceptionInfo ex
                (if (and (= :tactic-error (:kind (ex-data ex)))
                         (not (:limit (ex-data ex)))
                         (not (:proof-construction (ex-data ex))))
                  (tactic-error! "simplified to True but cannot certify" {:goal goal-type}) (throw ex)))))

      ;; Simplified to False
       (and (not target-core?) (e/const? simplified-whnf) (= (e/const-name simplified-whnf) false-name))
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
         (try (decide-goal ps)
              (catch clojure.lang.ExceptionInfo ex
                (if (and (= :tactic-error (:kind (ex-data ex)))
                         (not (:limit (ex-data ex)))
                         (not (:proof-construction (ex-data ex))))
                  (if (= simplified goal-type)
                    (if target-core? ps (tactic-error! "simp made no progress" {:goal goal-type}))
                 ;; Lean 4: simp replaces goal with simplified form via Eq.mpr
                 ;; when it can't close. Create a new goal with the simplified type.
                 ;; This follows Lean 4's applySimpResultToTarget (Main.lean:780).
                    (if (:proof? result)
                      (let [mpr-level (let [gs (safe-infer st goal-type)
                                            gsw (when gs (safe-whnf st gs))]
                                        (if (and gsw (e/sort? gsw)) (e/sort-level gsw) lvl/zero))
                            [ps' new-id] (proof/fresh-mvar-replacing ps simplified (:lctx goal) (:id goal))]
                        (-> (proof/assign-mvar ps' (:id goal)
                                               {:kind :simp-reduce
                                                :eq-proof (:proof? result)
                                                :child new-id
                                                :mpr-level mpr-level
                                                :goal-type goal-type
                                                :simplified simplified})
                            (proof/record-tactic :simp lemma-names (:id goal))))
                   ;; Proof chain is nil (all rfl steps) but simp simplified.
                      (let [[ps' new-id] (proof/fresh-mvar-replacing ps simplified (:lctx goal) (:id goal))]
                        (-> (proof/assign-mvar ps' (:id goal)
                                               {:kind :simp-reduce
                                                :eq-proof nil
                                                :child new-id
                                                :mpr-level lvl/zero
                                                :goal-type goal-type
                                                :simplified simplified})
                            (proof/record-tactic :simp lemma-names (:id goal)))))) (throw ex)))))))))

(defn- simp-setup
  "The simp context for `goal`: [ps st env lemma-index config]. `:exclude-hyp` drops that local
   from the contextual / term lemmas (Lean erases the simplified hypothesis itself in `simp at h`)."
  [ps goal lemma-names opts]
  (let [env (ensure-nat-packing (or (ensure-ble-eq (:env ps)) (:env ps)) lemma-names)
         ;; Update proof state with enriched env (e.g., derived Nat.ble_eq)
        ps (if (not (identical? env (:env ps))) (assoc ps :env env) ps)
         ;; attach-lctx (NOT plain assoc): bumps :next-id above the goal's max fvar id so
         ;; fresh binder fvars during inference don't collide with context fvars (which
         ;; corrupts abstraction — e.g. a fold step λacc x:K losing its K). See tc/attach-lctx.
        st (tc/attach-lctx (tc/mk-tc-state env) (:lctx goal))
         ;; Lean 4: user lemma names are ADDED to the default @[simp] set. The default set is the
         ;; hand-curated core PLUS any @[simp] lemmas inherited from Lean into the env's :simp-lemmas
         ;; extension (ansatz.attrs) — empty unless attributes were imported, so this is a no-op for
         ;; ansatz-alone and lets `(simp)` use Lean's real @[simp] corpus once inherited.
         ;; Lean's `simp [h]` accepts any proof TERM, not just a lemma name. Split the user list:
         ;; Expr entries are proof terms (e.g. a projected typeclass axiom `WSemiring.mul_zero S inst`,
         ;; or a hypothesis fvar); everything else is a name to resolve against the env.
        term-args (filter #(instance? ansatz.kernel.Expr %) lemma-names)
        name-args (remove #(instance? ansatz.kernel.Expr %) lemma-names)
         ;; Lean 4 `simp only`: start from `simpOnlyBuiltins` (reflexive closers) + the user
         ;; lemmas ONLY — the default @[simp] corpus and @[simp]-extension are excluded.
         ;; Otherwise the inherited @[simp] extension is part of the default set. When the store
         ;; has a persistent simp index (ansatz.simp-index, loaded on first use) that extension is
         ;; served LAZILY from `lookup-lemmas` and is NOT put through the eager per-call work below
         ;; (resolve+extract+key, equation-theorem probe, unfold probe — ~91k hydrations per call
         ;; on Mathlib). Without one (the bundled Init tiers) it stays eager.
        ext-trie (when-not (:only? opts) (si/ensure-simp-trie! env))
        all-names (if (:only? opts)
                    (distinct (concat (when (get opts :simp-only-builtins? true)
                                        simp-only-builtins) name-args))
                    (distinct (concat default-simp-lemmas
                                      (si/eager-lemma-names env ext-trie)
                                      name-args)))
        lemmas (make-simp-lemmas env all-names)
         ;; Proof-term lemmas: infer each term's type and extract its rewrite rule.
        term-lemmas (vec (mapcat (fn [t]
                                   (extract-simp-lemma-term env (tc/infer-type st t) 1000 t))
                                 term-args))
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
        all-lemmas (concat lemmas term-lemmas hyp-lemmas eqn-lemmas)
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
                :ext-trie ext-trie
                 ;; Lazy instance index for TC synthesis in discharge
                :inst-index (delay (inst/index-for env))}]
    [ps st env lemma-index config]))

(defn simp
  "Simplify the current goal using rewrite lemmas.
   Options: :contextual? :single-pass? :decide? (default true)"
  ([ps] (simp ps []))
  ([ps lemma-names] (simp ps lemma-names {}))
  ([ps lemma-names opts]
   (let [goal (proof/current-goal ps)
         _ (when-not goal (tactic-error! "No goals" {}))
         [ps st env lemma-index config] (simp-setup ps goal lemma-names opts)
         result (simp-expr* st env lemma-index (:type goal) config)]
     (close-goal-with-proof ps goal st result lemma-names false))))

(defn simp-target
  "Lean Meta/Tactic/Simp/Main.lean simpTargetCore, used by Mathlib reduceIfsAt:
   replace the target even when it becomes False; unchanged targets are allowed.
   `:may-close-goal? false` preserves reduced goals for Lean's simpIfTarget;
   `:simp-only-builtins? false` uses its conditional-only theorem set."
  [ps lemma-names opts]
  (let [goal (proof/current-goal ps)
        _ (when-not goal (tactic-error! "No goals" {}))
        [ps st env lemma-index config] (simp-setup ps goal lemma-names opts)
        result (simp-expr* st env lemma-index (:type goal) config)]
    (close-goal-with-proof ps goal st result lemma-names true
                           (get opts :may-close-goal? true))))

(defn simp-at
  "Lean's `simp [lemmas] at h` (Meta/Tactic/Simp/Main.lean `simpLocalDecl`/`applySimpResultToLocalDecl`):
   simplify the TYPE of hypothesis `hyp-id` with the simp set (not containing `h` itself).
   `False` closes the goal; `True` clears `h`; otherwise `h` is replaced (same name) by its
   simplified form, transported with `Eq.mp`. No progress is an error, as in Lean."
  ([ps hyp-id lemma-names] (simp-at ps hyp-id lemma-names {}))
  ([ps hyp-id lemma-names opts]
   (let [goal (proof/current-goal ps)
         _ (when-not goal (tactic-error! "No goals" {}))
         decl (red/lctx-lookup (:lctx goal) hyp-id)
         _ (when-not decl (tactic-error! "simp at: hypothesis not in context" {:id hyp-id}))
         lemma-names (remove #(and (instance? ansatz.kernel.Expr %) (e/fvar? %) (= hyp-id (e/fvar-id %)))
                             lemma-names)
         [ps st env lemma-index config] (simp-setup ps goal lemma-names opts)
         old-type (:type decl)
         result (simp-expr* st env lemma-index old-type config)
         new-type (:expr result)
         _ (when (or (identical? new-type old-type) (= new-type old-type))
             (tactic-error! "simp at: made no progress" {:hyp (:name decl)}))
         [proof-old proof-new]
         (if-let [pf (:proof? result)]
           (let [pw (#'tc/cached-whnf st (tc/infer-type st pf))
                 [h a] (e/get-app-fn-args pw)]
             (if (and (e/const? h) (= (e/const-name h) eq-name) (= 3 (count a)))
               [(nth a 1) (nth a 2)]
               [old-type new-type]))
           [old-type new-type])
         [ps new-id] (proof/alloc-id ps)
         rep {:old-fvar-id hyp-id :new-fvar-id new-id :name (:name decl)
              :old-type old-type :new-type new-type
              :proof-old-type proof-old :proof-new-type proof-new
              :eq-proof (:proof? result)}
         child-lctx (cond-> (dissoc (:lctx goal) hyp-id)
                      (not (true-const? new-type))
                      (assoc new-id {:tag :local :id new-id :name (:name decl) :type new-type}))
         [ps child-id] (proof/fresh-mvar ps (:type goal) child-lctx)
         ps (-> (update ps :goals #(into [child-id] (remove #{child-id} %)))
                (proof/assign-mvar (:id goal) {:kind :simp-all-hyps :replacements [rep] :child child-id})
                (proof/record-tactic :simp-at (vec lemma-names) (:id goal)))]
     (if (false-const? new-type)
       (let [st' (tc/attach-lctx (tc/mk-tc-state (:env ps)) child-lctx)
             s (#'tc/cached-whnf st' (tc/infer-type st' (:type goal)))
             u (if (and s (e/sort? s)) (e/sort-level s) lvl/zero)]
         (proof/assign-mvar ps child-id
                            {:kind :exact
                             :term (e/app* (e/const' (name/from-string "False.elim") [u])
                                           (:type goal) (e/fvar new-id))}))
       ps))))

(defn- hyp-type->lemmas
  "Extract simp lemma(s) from a single hypothesis type.
   Following Lean 4's preprocess (SimpTheorems.lean:288):
   - Eq/Iff: direct rewrite
   - And P Q: split into sub-lemmas (using And.left/And.right projections)
   - Implications P → Q: conditional rewrite (num-params > 0)
   - General propositions: → P = True
   Returns a vector of lemma maps. st is used for is-prop checks."
  [st hyp-type hyp-fvar-id]
  (with-inc-rec-depth 1 hyp-type
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

        :else nil))))

(defn- make-hyp-lemmas
  "Extract contextual rewrite lemmas from hypotheses in lctx.
   Handles Eq, Iff, And (splitting), Not, implications (conditional rewrites),
   and general propositions (→ True).
   Optionally excludes a specific hypothesis (by fvar id) to prevent self-rewrite.
   Lean 4: SimpAll.lean + SimpTheorems.lean preprocess."
  [st lctx & {:keys [exclude-id]}]
  (let [env (:env st)]
    (vec (mapcat (fn [[id decl]]
                   (when (and (= :local (:tag decl))
                              (not= id exclude-id))
                     (let [ty (:type decl)]
                       (if (and (e/forall? ty)
                                (not (is-prop-type? st (e/forall-type ty))))
                           ;; QUANTIFIED-rewrite hypothesis — a `∀ (a : T), lhs = rhs` whose T is a
                           ;; Type (not a Prop implication), e.g. an accumulator-generalized IH
                           ;; `∀ acc, foldl f acc xs = …`. Peel the FULL ∀-telescope (the bound vars
                           ;; become pattern vars) via the proof-TERM path, with the hyp fvar as the
                           ;; proof — so the IH fires at any accumulator. hyp-type->lemmas only peels
                           ;; Prop implications, so it mis-classifies this as a general prop (`→ True`).
                         (extract-simp-lemma-term env ty 2000 (e/fvar id))
                         (hyp-type->lemmas st ty id)))))
                 lctx))))

(def ^:private ^:dynamic *simp-all-superseded*
  "Within one `simp-all` call: an atom of the hypothesis fvar ids an earlier round replaced."
  nil)

(defn- simp-all-pass
  "ONE round of Lean 4's SimpAll `loop` (Meta/Tactic/Simp/SimpAll.lean):
   Phase 1: simplify every hypothesis entry against the others.
   Phase 2: assert the simplified entries (`simp-all-hyps` wrapper) as `h'` NEXT TO the
            originals — unlike Lean, which clears them: code compiles `(<= x y)` to `Nat.ble x y`,
            and only the original form still rewrites it once the entry is in normal form `x ≤ y`.
            Later rounds do not re-simplify a replaced original (`*simp-all-superseded*`). An entry
            simplified to `True` is not asserted; one simplified to `False` closes the goal.
   Phase 3: simp the goal in the updated lctx (eq-proof consistent).
   This order ensures the goal's Eq.mpr is built in the correct lctx."
  [ps lemma-names opts]
  (let [goal (proof/current-goal ps)
        _ (when-not goal (tactic-error! "No goals" {}))
        env (ensure-nat-packing (or (ensure-ble-eq (:env ps)) (:env ps)) lemma-names)
        ps (if (not (identical? env (:env ps))) (assoc ps :env env) ps)
         ;; the inherited @[simp] extension: lazy via the persistent index when present (see simp)
        ext-trie (when-not (:only? opts) (si/ensure-simp-trie! env))
        all-names (if (:only? opts)
                    (distinct (concat simp-only-builtins lemma-names))
                    (distinct (concat default-simp-lemmas
                                      (si/eager-lemma-names env ext-trie)
                                      lemma-names)))]
    ;; Phase 1: hypothesis simplification (Lean SimpAll.loop).
    (let [goal' goal
          lctx (:lctx goal')
          st (tc/attach-lctx (tc/mk-tc-state env) lctx)
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
          inst-index (delay (inst/index-for env))
           ;; an entry a previous round already simplified stays in the context (its original
           ;; form keeps rewriting the goal: `(<= x y)` in code is `Nat.ble x y`, which the
           ;; normal form `x ≤ y` no longer matches) but is not simplified again — Lean erases the
           ;; replaced entry; re-simplifying it would re-add the same entry every round.
          superseded (if *simp-all-superseded* @*simp-all-superseded* #{})
          hyps (vec (filter (fn [[id d]] (and (= :local (:tag d)) (not (superseded id)))) lctx))
             ;; Compute simplified hypothesis types
          replacements
          (reduce
           (fn [acc [id decl]]
             ;; Lean Simp/SimpAll.lean initEntries: simplify nondependent Prop
             ;; hypotheses, including arrows and foralls. Keep superseded entries above.
             (if (or (not (is-prop-type? st (:type decl)))
                     (not= (:type goal') (e/abstract1 (:type goal') id))
                     (some (fn [[other-id d]]
                             (and (not= id other-id)
                                  (or (not= (:type d) (e/abstract1 (:type d) id))
                                      (when-let [v (:value d)]
                                        (not= v (e/abstract1 v id)))))) lctx))
               acc
               (let [;; SimpAll.loop erases previous theorem versions. Originals
                     ;; remain available to the goal for our Bool encoding, but
                     ;; must not simplify their own replacements back to True.
                     hyp-lemmas (make-hyp-lemmas st (apply dissoc lctx superseded) :exclude-id id)
                     all-lemmas (concat base-lemmas eqn-lemmas hyp-lemmas)
                     lemma-index (build-lemma-index st env all-lemmas)
                     config {:max-depth 20 :single-pass? false :decide? true
                             :max-steps (atom 0) :cache (atom {})
                             :to-unfold to-unfold :discharge-depth 0
                             :ext-trie ext-trie :inst-index inst-index}
                     result (simp-expr* st env lemma-index (:type decl) config)]
                 (if (or (identical? (:expr result) (:type decl))
                         (= (:expr result) (:type decl)))
                   acc
                      ;; Accept the simplification. Root cause of Bool→True corruption
                      ;; is fixed (Prop guards in extract-from-conclusion +
                      ;; try-simp-using-decide). Lean 4 doesn't TC-verify
                      ;; intermediate proofs during simp_all — final extract/verify
                      ;; catches any remaining issues.
                      ;; Extract actual proof types for Eq.mp consistency at extraction time.
                      ;; simp-expr* may WHNF before rewriting, so eq-proof endpoints
                      ;; might differ from the raw hypothesis type / simp result.
                   (let [[proof-old proof-new]
                         (if-let [proof (:proof? result)]
                           (let [pt (tc/infer-type st proof)
                                 pw (when pt (#'tc/cached-whnf st pt))
                                 [h a] (when pw (e/get-app-fn-args pw))]
                             (if (and h (e/const? h)
                                      (= (e/const-name h) (name/from-string "Eq"))
                                      (= 3 (count a)))
                               [(nth a 1) (nth a 2)]
                               [nil nil]))
                           [nil nil])]
                     (conj acc {:old-fvar-id id :name (:name decl)
                                :old-type (:type decl) :new-type (:expr result)
                                   ;; proof-consistent types for extraction
                                :proof-old-type (or proof-old (:type decl))
                                :proof-new-type (or proof-new (:expr result))
                                :eq-proof (:proof? result)}))))))
           []
           hyps)]
      (if (empty? replacements)
           ;; No hypothesis changes — just simp the goal directly
        (try (simp ps lemma-names {:contextual? true})
             (catch clojure.lang.ExceptionInfo ex
               (if (and (= :tactic-error (:kind (ex-data ex)))
                        (not (:limit (ex-data ex)))
                        (not (:proof-construction (ex-data ex)))) ps (throw ex))))
           ;; Add simplified hypotheses alongside originals
        (let [;; Allocate new fvar ids, decomposing And types recursively.
                 ;; Lean 4: SimpTheorems.preprocess splits And into left/right
                 ;; via mkProj. We do the same here so each conjunct becomes
                 ;; a separate hypothesis visible to omega and other tactics.
              [ps' replacements']
              (reduce (fn [[ps reps] rep]
                        (letfn [(expand [ps ty name-base proj]
                                  (with-inc-rec-depth 1 ty
                                    (let [[head args] (e/get-app-fn-args ty)]
                                      (if (and (e/const? head)
                                               (= (e/const-name head) and-name)
                                               (= 2 (count args)))
                                         ;; And P Q → expand left and right; each conjunct is reached
                                         ;; from the transported whole by its And.left/And.right chain
                                        (let [[ps' left-reps] (expand ps (nth args 0) (str name-base "\u2081")
                                                                      (conj proj [:left (nth args 0) (nth args 1)]))
                                              [ps' right-reps] (expand ps' (nth args 1) (str name-base "\u2082")
                                                                       (conj proj [:right (nth args 0) (nth args 1)]))]
                                          [ps' (into left-reps right-reps)])
                                         ;; Leaf — allocate one fvar
                                        (let [[ps' new-id] (proof/alloc-id ps)]
                                          [ps' [(assoc rep :new-fvar-id new-id
                                                       :new-type ty :name name-base
                                                       :and-proj proj)]])))))]
                          (let [[ps' new-entries] (expand ps (:new-type rep) (:name rep) [])]
                            [ps' (into reps new-entries)])))
                      [ps []]
                      replacements)
                 ;; Build new lctx: keep originals, add simplified versions
                 ;; Use distinct names (append ') to avoid name collision with
                 ;; originals — otherwise sexp->ansatz name lookup picks the wrong one
              new-lctx (reduce (fn [lctx {:keys [new-fvar-id name new-type]}]
                                 (if (true-const? new-type)
                                   lctx
                                   (assoc lctx new-fvar-id
                                          {:tag :local :id new-fvar-id
                                           :name (str name "'") :type new-type})))
                               lctx
                               replacements')
              _ (when *simp-all-superseded*
                  (swap! *simp-all-superseded* into (map :old-fvar-id replacements')))
                 ;; Create body sub-goal (insert at front for priority)
              [ps'' body-goal-id]
              (let [[ps''' id] (proof/fresh-mvar ps' (:type goal') new-lctx)]
                [(update ps''' :goals #(into [id] (remove #{id} %)))
                 id])
                 ;; Assign current goal with simp-all-hyps wrapper
              ps'' (-> (proof/assign-mvar ps'' (:id goal')
                                          {:kind :simp-all-hyps
                                           :replacements replacements'
                                           :child body-goal-id})
                       (proof/record-tactic :simp-all (vec lemma-names) (:id goal')))]
             ;; An entry simplified to `False` closes the goal (SimpAll `simpStep` → none).
          (if-let [false-rep (first (filter #(false-const? (:new-type %)) replacements'))]
            (let [goal-sort (let [st' (tc/attach-lctx (tc/mk-tc-state (:env ps'')) new-lctx)
                                  s (#'tc/cached-whnf st' (tc/infer-type st' (:type goal')))]
                              (if (e/sort? s) (e/sort-level s) lvl/zero))]
              (proof/assign-mvar ps'' body-goal-id
                                 {:kind :exact
                                  :term (e/app* (e/const' (name/from-string "False.elim") [goal-sort])
                                                (:type goal') (e/fvar (:new-fvar-id false-rep)))}))
             ;; Phase 3 (Lean 4 order): simp the goal AFTER hypothesis expansion.
             ;; The goal's eq-proof is now built in the expanded lctx — consistent!
            (try (simp ps'' lemma-names {:contextual? true})
                 (catch clojure.lang.ExceptionInfo ex
                   (if (and (= :tactic-error (:kind (ex-data ex)))
                            (not (:limit (ex-data ex)))
                            (not (:proof-construction (ex-data ex)))) ps'' (throw ex))))))))))

(def ^:private simp-all-max-rounds
  "Bound on SimpAll rounds (Lean bounds the loop by `maxSteps` through the shared stats)."
  32)

(defn simp-all
  "Simplify goal + all hypotheses (Lean 4's SimpAll): repeat `simp-all-pass` while it changes
   the focused goal — each round simplifies the hypotheses against the ones the previous round
   produced — until a fixpoint, the goal is closed, or `simp-all-max-rounds`."
  ([ps] (simp-all ps []))
  ([ps lemma-names] (simp-all ps lemma-names {}))
  ([ps lemma-names opts]
   (binding [*simp-all-superseded* (atom #{})]
     (loop [ps ps round 0]
       (let [g (proof/current-goal ps)
             n (count (:goals ps))
             ps' (simp-all-pass ps lemma-names opts)
             g' (proof/current-goal ps')]
         (if (or (< (count (:goals ps')) n)            ; focused goal closed
                 (nil? g')
                 (= (:id g) (:id g'))                   ; no change this round
                 (>= (inc round) simp-all-max-rounds))
           ps'
           (recur ps' (inc round))))))))

;; ============================================================
;; Nat offset decomposition — Lean 4's NatOffset (Simprocs/Nat.lean)
;; ============================================================

(defn nat-offset-parse
  "Decompose a Nat expression into {:base expr :offset n}.
   e.g., x + 3 → {:base x :offset 3}, Nat.succ x → {:base x :offset 1},
   pure literal 5 → {:base nil :offset 5}."
  [st expr]
  (with-inc-rec-depth 1 expr
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
        (let [b-val (get-nat-value? st (nth args 1))]
          (if b-val
            (let [inner (nat-offset-parse st (nth args 0))]
              (update inner :offset + b-val))
            (let [a-val (get-nat-value? st (nth args 0))]
              (if a-val
                (let [inner (nat-offset-parse st (nth args 1))]
                  (update inner :offset + a-val))
                {:base w :offset 0}))))

      ;; HAdd.hAdd Nat Nat Nat inst a b (6 args)
        (and (e/const? head)
             (= (name/->string (e/const-name head)) "HAdd.hAdd")
             (= 6 (count args)))
        (let [b-val (get-nat-value? st (nth args 5))]
          (if b-val
            (let [inner (nat-offset-parse st (nth args 4))]
              (update inner :offset + b-val))
            (let [a-val (get-nat-value? st (nth args 4))]
              (if a-val
                (let [inner (nat-offset-parse st (nth args 5))]
                  (update inner :offset + a-val))
                {:base w :offset 0}))))

        :else {:base w :offset 0}))))

(defn dsimp
  "Definitional simplification — faithful port of Lean 4's `dsimpGoal`
   (Lean/Meta/Tactic/Simp/Main.lean:928), TARGET form (bare `dsimp`).

   Reduces the goal by STRUCTURAL/definitional reductions only — beta, eta, iota
   (incl. matcher/recursor on a constructor scrutinee), proj, let-zeta — via the
   recursive `dsimp-expr` traversal (= Lean's `dsimpReduce`, whnf-no-delta). NO
   propositional rewrite lemmas, NO simprocs (that is `dsimp [...]`, not yet wired).

   Then mirrors `dsimpGoal`'s target handling:
   - `targetNew.isTrue`               → close with `True.intro`
   - `targetNew = (a = b)`, isDefEq   → close with `Eq.refl a`
   - failIfUnchanged (target == new)  → error \"dsimp made no progress\"
   - otherwise `replaceTargetDefEq`   → swap the goal to the def-eq reduced form and
     leave it OPEN (the new goal carries the reduced type; soundness is the def-eq
     of `dsimp-expr`, so no proof term is needed — `:simp-reduce` with `:eq-proof nil`,
     the same mechanism `simp` uses for all-rfl steps).

   Unlike the previous closing-only stub (single head whnf, errored when it couldn't
   close), this is the transforming tactic: after simp rewrites a match scrutinee to a
   literal, `dsimp` fires the iota step the rewrite pass leaves pending."
  [ps]
  (let [goal (proof/current-goal ps)
        _ (when-not goal (tactic-error! "No goals" {}))
        env (:env ps)
        ;; attach-lctx bumps :next-id above the goal's fvars (see note at simp entry).
        st (tc/attach-lctx (tc/mk-tc-state env) (:lctx goal))
        goal-type (:type goal)
        ;; dsimpReduce: recursive structural reduction of the whole target.
        simplified (dsimp-expr env (:lctx goal) goal-type 100)
        simplified-whnf (#'tc/cached-whnf st simplified)
        [head args] (e/get-app-fn-args simplified-whnf)]
    (cond
      ;; targetNew.isTrue → True.intro
      (and (e/const? head) (= (e/const-name head) true-name))
      (-> (proof/assign-mvar ps (:id goal) {:kind :exact :term (e/const' true-intro-name [])})
          (proof/record-tactic :dsimp [] (:id goal)))

      ;; targetNew is `Eq α a b` with isDefEq a b → Eq.refl
      (and (e/const? head) (= (e/const-name head) eq-name) (= 3 (count args))
           (tc/is-def-eq st (nth args 1) (nth args 2)))
      (let [proof (e/app* (e/const' eq-refl-name (e/const-levels head)) (nth args 0) (nth args 1))]
        (-> (proof/assign-mvar ps (:id goal) {:kind :exact :term proof})
            (proof/record-tactic :dsimp [] (:id goal))))

      ;; failIfUnchanged (config default)
      (= simplified goal-type)
      (tactic-error! "dsimp made no progress" {:goal goal-type})

      ;; replaceTargetDefEq — leave the reduced goal open (def-eq, no proof term)
      :else
      (let [[ps' new-id] (proof/fresh-mvar-replacing ps simplified (:lctx goal) (:id goal))]
        (-> (proof/assign-mvar ps' (:id goal)
                               {:kind :simp-reduce :eq-proof nil :child new-id
                                :mpr-level lvl/zero :goal-type goal-type :simplified simplified})
            (proof/record-tactic :dsimp [] (:id goal)))))))
