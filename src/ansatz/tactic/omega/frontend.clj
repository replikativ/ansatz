;; Port of Lean/Elab/Tactic/Omega/Frontend.lean: asLinearCombo, addFact,
;; processFacts, splitDisjunction, omegaImpl (checkout 55f80e10).
(ns ansatz.tactic.omega.frontend
  "Omega reification, proof facts, branch search, and tactic continuation.
   Core owns interval algebra, elimination, and delayed certificate assembly."
  (:require [clojure.string]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.tc :as tc]
            [ansatz.kernel.env :as kenv]
            [ansatz.kernel.reduce :as red]
            [ansatz.tactic.proof :as proof]
            [ansatz.tactic.decide :as decide-tac]
            [ansatz.tactic.omega.core :as op]
            [ansatz.tactic.omega.omega-m :as om]))

;; ============================================================
;; Ansatz names for Lean.Omega.* constants
;; ============================================================

(def ^:private nat-to-int op/nat-to-int)
(def ^:private omega-names op/omega-names)
(def ^:private int-type op/int-type)
(def ^:private u1 op/u1)

;; ============================================================
;; Lean.Omega data structures mirrored in Clojure
;; ============================================================

;; A LinearCombo: {:const Int, :coeffs [Int ...]}
;; Dense representation: coeffs[i] is the coefficient of atom i
;; Evaluates to: const + Σ coeffs[i] * atoms[i]
;;
;; Solver arithmetic uses auto-promoting ops (*' +' -') to avoid
;; long overflow when tidying is disabled and coefficients grow
;; through Fourier-Motzkin elimination.

;; ============================================================
;; Core algebra and certificate helpers
;; ============================================================

(def ^:private mk-lc op/mk-lc)
(def ^:private lc-coordinate op/lc-coordinate)
(def ^:private lc-add op/lc-add)
(def ^:private lc-sub op/lc-sub)
(def ^:private lc-negate op/lc-negate)
(def ^:private lc-scale op/lc-scale)
(def ^:private int-bmod op/int-bmod)

(def ^:private constraint-exact op/constraint-exact)

(def ^:private mk-atom-table op/mk-atom-table)

(defn- intern-atom
  "Intern an expression as an atom. Returns [table' idx].
   Also stores the Int version of the atom for proof construction.
   If int-expr is provided, it's used as the Int expression; otherwise
   the expression itself is assumed to be Int."
  ([table st expr] (intern-atom table st expr nil))
  ([table st expr int-expr]
   (let [expr-whnf (#'tc/cached-whnf st expr)]
     (if-let [idx (get (:expr->idx table) expr-whnf)]
       [table idx]
       (let [match (some (fn [[e idx]]
                           (when (tc/is-def-eq st e expr-whnf) idx))
                         (:expr->idx table))]
         (if match
           [table match]
           (let [idx (:next-idx table)
                 ;; Store Int version: if provided use it, else derive from the atom's type.
                 ;; A Nat atom is wrapped in Int.ofNat; an Int atom is used as-is; any other
                 ;; (non-arithmetic, e.g. Bool) means the goal isn't linear arithmetic — reject
                 ;; gracefully here rather than building `Int.ofNat (<Bool>)` and crashing the
                 ;; kernel during proof verification.
                 int-e (or int-expr
                           (let [ty (#'tc/cached-whnf st (tc/infer-type st expr-whnf))
                                 cn (when (and ty (e/const? ty)) (name/->string (e/const-name ty)))]
                             (cond
                               (= cn "Nat") (nat-to-int expr-whnf)
                               (= cn "Int") expr-whnf
                               :else
                               (throw (ex-info (str "omega: atom of non-arithmetic type "
                                                    (or cn "?")
                                                    " — goal is not linear arithmetic over Nat/Int")
                                               {:kind :tactic-error})))))
                 [table' [idx facts]]
                 (om/lookup table int-e
                            (fn [int-expr]
                              ;; OmegaM.analyzeAtom: the Nat cast contributes its
                              ;; nonnegativity proof exactly once at first lookup.
                              (let [[head args] (e/get-app-fn-args int-expr)]
                                (if (and (e/const? head)
                                         (= (e/const-name head) (:int-ofnat omega-names))
                                         (= 1 (count args)))
                                  [(e/app (e/const' (name/from-string "Int.natCast_nonneg") []) (first args))]
                                  []))))
                 table' (-> table'
                            (assoc-in [:expr->idx expr-whnf] idx)
                            (assoc-in [:idx->expr idx] expr-whnf)
                            (update :new-facts into facts))]
             [table' idx])))))))

;; ============================================================
;; Eval proof construction (asLinearCombo equivalent)
;; ============================================================

;; An eval proof is a delayed function: atoms-expr → proof that lc.eval atoms = original_expr
;; Used for building assumption proofs for non-ground goals.
;; The "original_expr" is an Int expression.

(def ^:private mk-eq-refl-int op/mk-eq-refl-int)
(def ^:private mk-eq-symm op/mk-eq-symm)
(def ^:private mk-eq-trans op/mk-eq-trans)
(def ^:private mk-int-hadd op/mk-int-hadd)
(def ^:private mk-int-hsub op/mk-int-hsub)
(def ^:private mk-int-hmul op/mk-int-hmul)
(def ^:private mk-int-mul op/mk-int-mul)
(def ^:private mk-int-lit op/mk-int-lit)
(def ^:private mk-int-add op/mk-int-add)
(def ^:private mk-int-sub op/mk-int-sub)
(def ^:private mk-int-add-congr op/mk-int-add-congr)
(def ^:private mk-int-sub-congr op/mk-int-sub-congr)
(def ^:private mk-lc-eval-expr op/mk-lc-eval-expr)
(def ^:private mk-eval-rfl-proof op/mk-eval-rfl-proof)
(def ^:private mk-coordinate-eval-proof op/mk-coordinate-eval-proof)
(def ^:private mk-add-eval-proof op/mk-add-eval-proof)
(def ^:private mk-sub-eval-proof op/mk-sub-eval-proof)
(def ^:private mk-neg-eval-proof op/mk-neg-eval-proof)
(def ^:private mk-nat-hadd op/mk-nat-hadd)
(def ^:private mk-nat-hmul op/mk-nat-hmul)
(def ^:private mk-nat-ofnat-lit op/mk-nat-ofnat-lit)
(def ^:private mk-eq-trans-nat op/mk-eq-trans-nat)
(def ^:private mk-eq-symm-nat op/mk-eq-symm-nat)
(def ^:private mk-congr-arg-nat op/mk-congr-arg-nat)
(def ^:private mk-nat-add-chain op/mk-nat-add-chain)
(def ^:private mk-right-mul-expand op/mk-right-mul-expand)
(def ^:private mk-nat-mul-expand-proof op/mk-nat-mul-expand-proof)
(def ^:private mk-scale-eval-proof op/mk-scale-eval-proof)

(defn- ground-int-val
  "The integer VALUE of a ground literal, seeing THROUGH the two `Int` constructors.

   `e/lit-nat?` alone only recognises the raw `Nat` literal, so every `Int` literal —
   which is always spelled `Int.ofNat k` or `Int.negSucc k` — used to look like an
   opaque term at the ground-operand checks in `reify-term` below. That is what made
   `x / (3 : Int)` reify as an unconstrained atom instead of a quotient with bounds.

   Returns a Long, or nil when the expression is not a ground literal."
  [expr]
  (cond
    (e/lit-nat? expr) (long (e/lit-nat-val expr))
    (e/app? expr)
    (let [[h as] (e/get-app-fn-args expr)]
      (when (and (e/const? h) (= 1 (count as)) (e/lit-nat? (first as)))
        (let [k (long (e/lit-nat-val (first as)))
              cn (name/->string (e/const-name h))]
          (cond
            (= cn "Int.ofNat") k
            ;; Int.negSucc k denotes -(k+1)
            (= cn "Int.negSucc") (- (- k) 1)
            :else nil))))
    :else nil))

(defn- ground-nat-val
  "`ground-int-val` restricted to NON-NEGATIVE values.

   Used wherever the value feeds a `Nat`-flavoured computation (`quot`, `mod`, the
   `0 < k` divisor test): `Int` division floors while Clojure's `quot` truncates, so
   folding a negative ground quotient here would be quietly wrong."
  [expr]
  (when-let [v (ground-int-val expr)]
    (when (>= v 0) v)))

(defn- try-match-head [st expr]
  (let [[head args] (e/get-app-fn-args expr)]
    (if (e/const? head)
      [(e/const-name head) (e/const-levels head) (vec args)]
      (let [w (#'tc/cached-whnf st expr)
            [whead wargs] (e/get-app-fn-args w)]
        (when (e/const? whead)
          [(e/const-name whead) (e/const-levels whead) (vec wargs)])))))

(declare reify-term)

;; ------------------------------------------------------------
;; Division / modulo, shared by all four spellings
;; ------------------------------------------------------------
;;
;; Lean's frontend (Lean/Elab/Tactic/Omega/Frontend.lean) treats the two
;; operators asymmetrically, and we mirror that exactly:
;;
;;   x / k  for a positive literal k  →  a fresh ATOM q, plus the two facts
;;          `k*q ≤ x` and `x < k*q + k` attached by `analyzeAtom`
;;          (Lean/Elab/Tactic/Omega/OmegaM.lean). Those two are added later, by
;;          `add-div-bounds`; here we only intern the atom and TAG it.
;;   x % k  is never atomised BY LEAN — it is rewritten `x % k = x - k * (x / k)`
;;          (`Int.emod_def`), so there is no separate remainder variable: `r` is
;;          eliminated by the rewrite and `0 ≤ r < k` falls out of the two div
;;          bounds above. We DO atomise it on the Nat path and tie it back down with
;;          `Nat.mod_add_div`, because that rewrite is a theorem about casts rather
;;          than a definitional equality here — see `reify-mod-atom` for why, and
;;          note the solver eliminates the extra variable by substitution anyway.
;;
;; The ansatz surface elaborates `Nat.div`/`Nat.mod` BARE (ansatz.surface.ingest),
;; while Lean's own library carries the `HDiv.hDiv`/`HMod.hMod` typeclass spelling,
;; so all four spellings must reach the same code. They must also be handled
;; PRE-WHNF: `Nat.div` is well-founded-recursive, so WHNF unfolds it into a stuck
;; `Nat.div.go`/`Decidable.rec` blob whose head is no longer `Nat.div`.

(def ^:private arithmetic-heads
  "Head constants `reify-term` can decompose. Used to decide when to STOP delta-unfolding."
  (into #{} (map omega-names)
        [:nat-add :nat-sub :nat-mul :nat-div :nat-mod :nat-succ :nat-zero
         :hadd :hsub :hmul :hdiv :hmod :ofnat :neg-name :int-ofnat :int-negsucc
         :min-name :max-name]))

(defn- delta-step
  "One DELTA step at the head: unfold the head constant's value and beta-reduce the
   application (beta/iota/proj only — `whnf-no-delta` — so no further definitions are
   unfolded). Returns nil if the head is not a constant with a value."
  [st expr]
  (let [[head args] (e/get-app-fn-args expr)]
    (when (e/const? head)
      (when-let [ci (kenv/lookup (:env st) (e/const-name head))]
        (when-let [value (kenv/get-value ci)]
          (let [subst (into {} (map vector (vec (.levelParams ci)) (e/const-levels head)))
                body (e/instantiate-level-params value subst)]
            (red/whnf-no-delta (:env st) (apply e/app* body args) (:lctx st))))))))

(defn- delta-to-arithmetic
  "Unfold one head at a time, stopping before recognized arithmetic is lost to
   recursive implementation details. Opaque heads return nil; work exhaustion throws."
  [st expr]
  (loop [x expr]
    (om/charge!)
    (let [head (e/get-app-fn x)]
      (cond
        (and (e/const? head) (contains? arithmetic-heads (e/const-name head)))
        (when-not (identical? x expr) x)
        (not (e/const? head)) nil
        :else (when-let [x' (delta-step st x)]
                (when-not (identical? x' x) (recur x')))))))

(defn- mk-hdiv-expr
  "Rebuild `a / b` in the HDiv.hDiv spelling, given the element-type arguments of
   the application we are rewriting (`T0 T1 T2` = args 0..2)."
  [st T0 T1 T2 a b]
  (let [tw (#'tc/cached-whnf st T0)
        tn (when (e/const? tw) (e/const-name tw))]
    (e/app* (e/const' (:hdiv omega-names) [lvl/zero lvl/zero lvl/zero])
            T0 T1 T2
            (e/app* (e/const' (name/from-string "instHDiv") [lvl/zero])
                    T0 (if (= tn (:nat-name omega-names))
                         (e/const' (name/from-string "Nat.instDiv") [])
                         (e/const' (name/from-string "Int.instDiv") [])))
            a b)))

(defn- mk-hmul-expr
  "Rebuild `a * b` in the HMul.hMul spelling — the shape `mk-scale-eval-proof`'s
   Nat.mul_succ/Nat.mul_comm bridge is stated in."
  [st T0 T1 T2 a b]
  (let [tw (#'tc/cached-whnf st T0)
        tn (when (e/const? tw) (e/const-name tw))]
    (e/app* (e/const' (:hmul omega-names) [lvl/zero lvl/zero lvl/zero])
            T0 T1 T2
            (e/app* (e/const' (name/from-string "instHMul") [lvl/zero])
                    T0 (if (= tn (:nat-name omega-names))
                         (e/const' (name/from-string "instMulNat") [])
                         (e/const' (name/from-string "Int.instMul") [])))
            a b)))

(defn- reify-div-atom
  "Reify a division `a / b` (in ANY spelling) into a LinearCombo.

   `expr` is the ORIGINAL, un-WHNF'd division expression and is interned verbatim
   — `intern-atom` keys on `cached-whnf`, which agrees for `Nat.div a b` and
   `HDiv.hDiv … a b` (both reduce to the same stuck `Nat.div.go` blob), so the two
   spellings share one atom index. The tagged `:expr` is the spelling
   `add-div-bounds` will re-state the bounds over, so it must stay faithful.

   Literal divisors are folded away instead of atomised:
     b = 0     → 0     (`Nat.div n 0` reduces to 0 definitionally — the `0 < b`
                        guard in Nat.div fails, so this needs no rewrite lemma)
     a, b both literal → the computed quotient."
  [st table expr a b type-name]
  (let [av (ground-nat-val (#'tc/cached-whnf st a))
        bv (ground-nat-val (#'tc/cached-whnf st b))]
    (cond
      ;; NAT only: `Nat.div n 0` reduces to `0` because the `0 < b` guard fails before
      ;; the recursion, so the rfl eval proof holds definitionally. `Int.ediv x 0` is
      ;; STUCK for symbolic x (ediv matches on both arguments) — `= 0` there is a
      ;; theorem, not a defeq, and asserting it by rfl would build a proof the kernel
      ;; rejects. An Int zero divisor stays an atom.
      (and (= bv 0) (= type-name (:nat-name omega-names)))
      (let [lc (mk-lc 0)] [table lc (mk-eval-rfl-proof lc)])

      (and av bv (pos? bv))
      (let [lc (mk-lc (quot av bv))]
        [table lc (mk-eval-rfl-proof lc)])

      :else
      (let [[table' idx] (intern-atom table st expr)
            ;; Only a positive LITERAL divisor gets bounds: for a symbolic divisor
            ;; the quotient is a plain opaque atom (Lean does the same — a symbolic
            ;; divisor would need the `b = 0` case split, which we do not do).
            table' (if (and bv (pos? bv))
                     (assoc-in table' [:div-atoms idx]
                               {:a a :b b :type-name type-name :expr expr})
                     table')]
        [table' (lc-coordinate idx) (mk-coordinate-eval-proof idx)]))))

(defn- reify-mod-decomp
  "Reify an INT remainder `a % b` by rewriting it to `a - b * (a / b)` (Lean's
   `Int.emod_def`). `mk-div` rebuilds the quotient in the SAME spelling as the
   input; `mk-mul` rebuilds the product in the HMul spelling that
   `mk-scale-eval-proof`'s bridge is stated in.

   Returns nil (caller falls through) when `b` is not a positive literal.

   NOTE — this is the INT path only, and it is currently DEAD on the bundled init
   slice: the eval proof it builds claims `lc.eval = ↑a - ↑(b*(a/b))`, whereas the
   surrounding constraint proof needs `lc.eval = ↑(a % b)`. Those are equal by
   `Int.emod_def` but NOT definitionally, so the bridge still has to be built and
   spliced in before this can certify. (It never fired before either — the Int div
   bounds it depends on need `Int.mul_ediv_self_le`, absent from init-medium.) The
   Nat path deliberately does NOT come here; see `reify-mod-atom`."
  [st table a b mk-div mk-mul]
  (let [bv (ground-nat-val (#'tc/cached-whnf st b))]
    (when (and bv (pos? bv))
      (let [k bv
            [table' lc-a prf-a] (reify-term st table a)
            div-expr (mk-div a b)
            [table'' lc-div prf-div] (reify-term st table' div-expr)
            lc-bq (lc-scale lc-div k)
            mul-expr (mk-mul b div-expr)
            prf-bq (mk-scale-eval-proof lc-div k prf-div div-expr mul-expr :left)]
        [table'' (lc-sub lc-a lc-bq) (mk-sub-eval-proof lc-a lc-bq prf-a prf-bq)]))))

(defn- reify-mod-atom
  "Reify a NAT remainder `a % b` (in ANY spelling) as its own omega atom `r`,
   tagged for fact generation.

   This DIVERGES from lean4, which never atomises `%`: its frontend rewrites
   `a % b = a - b * (a / b)` (`Int.emod_def`) so the remainder is eliminated and
   `0 ≤ r < b` falls out of the two quotient bounds. We cannot reproduce that here
   because the reconstruction needs the cast bridge `↑(a % b) = ↑a - ↑(b*(a/b))`,
   which is a THEOREM (`Nat.mod_add_div`), not a definitional equality — an eval
   proof that simply asserts it is rejected by the kernel.

   So we keep the remainder as a variable and tie it down with the very lemma that
   bridge would have needed, stated over the ORIGINAL terms where `reify-prop` can
   certify it (see `add-div-bounds`):
       r + b*q = a   (Nat.mod_add_div)
   The solver then eliminates `r` by substitution, reaching exactly Lean's
   constraint set with one redundant variable.

   A fully ground remainder folds to its value. A literal ZERO divisor does NOT
   fold: unlike `Nat.div n 0` (which reduces to `0` because the guard fails before
   the recursion), `Nat.mod n 0` stays stuck on `Nat.rec` over `n`, so `n % 0 = n`
   is a theorem (`Nat.mod_zero`), not a definitional equality. It is tagged like any
   other literal divisor and `add-div-bounds` states the right lemma for it."
  [st table expr a b]
  (let [av (ground-nat-val (#'tc/cached-whnf st a))
        bv (ground-nat-val (#'tc/cached-whnf st b))]
    (cond
      (and av bv (pos? bv))
      (let [lc (mk-lc (mod av bv))]
        [table lc (mk-eval-rfl-proof lc)])

      :else
      (let [[table' idx] (intern-atom table st expr)
            table' (if bv
                     (assoc-in table' [:mod-atoms idx] {:a a :b b :expr expr})
                     table')]
        [table' (lc-coordinate idx) (mk-coordinate-eval-proof idx)]))))

(defn- reify-min-max
  "Frontend.handleNatCast/asLinearComboImpl: use ofNat_min/max and Int.min/max_def.
   Standard Nat/Int instances are checked before constructing the rewrite. Other
   instance shapes remain opaque; no bounded instance peeling is needed."
  [st table expr alpha inst a b min?]
  (let [[table idx] (intern-atom table st expr)
        ty (#'tc/cached-whnf st alpha)
        nat? (and (e/const? ty) (= (e/const-name ty) (:nat-name omega-names)))
        int? (and (e/const? ty) (= (e/const-name ty) (:int-name omega-names)))
        le (e/const' (name/from-string (if nat? "instLENat" "Int.instLEInt")) [])
        dec (e/const' (name/from-string (if nat? "Nat.decLe" "Int.decLe")) [])
        standard (e/app* (e/const' (if min? (:min-of-le omega-names) (:max-of-le omega-names)) [lvl/zero])
                         alpha le dec)]
    (if-not (and (or nat? int?) (tc/is-def-eq st inst standard))
      [table (lc-coordinate idx) (mk-coordinate-eval-proof idx)]
      (let [a' (if nat? (nat-to-int a) a)
            b' (if nat? (nat-to-int b) b)
            int-expr (if nat? (nat-to-int expr) expr)
            int-inst (e/const' ((if min? :int-inst-min :int-inst-max) omega-names) [])
            int-minmax (e/app* (e/const' (if min? (:min-name omega-names) (:max-name omega-names)) [lvl/zero])
                              int-type int-inst a' b')
            def-proof (e/app* (e/const' ((if min? :int-min-def :int-max-def) omega-names) []) a' b')
            le (e/const' (:int-inst-le omega-names) [])
            dec (e/const' (name/from-string "Int.decLe") [])
            prop (e/app* (e/const' (:le-name omega-names) [lvl/zero]) int-type le a' b')
            ite (e/app* (e/const' (name/from-string "ite") [u1]) int-type prop
                       (e/app* dec a' b') (if min? a' b') (if min? b' a'))
            rewrite (if nat?
                      (mk-eq-trans int-expr int-minmax ite
                                   (e/app* (e/const' ((if min? :ofnat-min :ofnat-max) omega-names) []) a b)
                                   def-proof)
                      def-proof)]
        [(assoc-in table [:minmax-atoms idx]
                   {:expr int-expr :alpha int-type :a a' :b b' :min? min?
                    :le-inst le :dec-rel dec :rewrite rewrite :ite ite})
         (lc-coordinate idx) (mk-coordinate-eval-proof idx)]))))

(defn- as-linear-combo-impl
  "Reify a Ansatz term into a LinearCombo (dense coefficients).
   Returns [atom-table linear-combo eval-proof-fn] where
   eval-proof-fn : atoms-expr → proof of (lc.eval atoms = Int-version-of-expr).
   For ground constants, eval-proof-fn uses rfl (definitional equality).
   For atoms, uses coordinate_eval."
  [st table expr]
  ;; Pre-WHNF check for Nat arithmetic ops (WHNF unfolds them to brecOn)
  (or (when (e/app? expr)
        (let [[head args] (e/get-app-fn-args expr)
              head-name (when (e/const? head) (e/const-name head))]
          (cond
            ;; OfNat.ofNat α n _ → n, BEFORE whnf. This is how Lean spells a numeral at a
            ;; type, so every Int literal arrives in this shape; whnf turns it into
            ;; `Int.ofNat n`, which the post-whnf cond below does not recognise, and the
            ;; numeral became an opaque atom (`a + 0 = a` was unprovable while `a + 1 = 1 + a`
            ;; passed, because there the atom cancelled).
            (and (= head-name (:ofnat omega-names)) (>= (count args) 2))
            (reify-term st table (nth args 1))

            ;; Int.ofNat(x) → reify x as Nat (reuses Nat-level atoms)
            ;; This ensures ↑(a-b) creates the same atom as bare Nat.sub a b,
            ;; and ↑a creates the same atom as bare a.
            (and (= head-name (:int-ofnat omega-names)) (= 1 (count args)))
            (reify-term st table (nth args 0))

            ;; HSub.hSub α _ _ _ a b → a - b. CRUCIAL: distinguish by the element type α.
            ;; Nat subtraction is TRUNCATED (max(0,a-b)), NOT integer subtraction, so it must be
            ;; atomized + tagged for the Int.ofNat_sub_dichotomy (same as bare Nat.sub) — linearizing
            ;; it as `a - b` builds an unsound eval-proof (le_of_le_of_eq Int-transport mismatch).
            ;; Only Int (or other ring) subtraction linearizes.
            (and (= head-name (:hsub omega-names)) (= 6 (count args)))
            (let [alpha (#'tc/cached-whnf st (nth args 0))
                  a (nth args 4) b (nth args 5)]
              (if (and (e/const? alpha) (= (e/const-name alpha) (:nat-name omega-names)))
                ;; Nat subtraction: ground → max(0,a-b); else atom + dichotomy tag
                (let [av (ground-nat-val (#'tc/cached-whnf st a))
                      bv (ground-nat-val (#'tc/cached-whnf st b))]
                  (if (and av bv)
                    (let [lc (mk-lc (max 0 (- av bv)))]
                      [table lc (mk-eval-rfl-proof lc)])
                    (let [[table' idx] (intern-atom table st expr)
                          table' (assoc-in table' [:nat-sub-atoms idx] {:a a :b b})]
                      [table' (lc-coordinate idx) (mk-coordinate-eval-proof idx)])))
                ;; Int subtraction: linearize
                (let [[table' lc-a prf-a] (reify-term st table a)
                      [table'' lc-b prf-b] (reify-term st table' b)]
                  [table'' (lc-sub lc-a lc-b) (mk-sub-eval-proof lc-a lc-b prf-a prf-b)])))

            ;; HAdd.hAdd _ _ _ _ a b → a + b (pre-WHNF)
            (and (= head-name (:hadd omega-names)) (= 6 (count args)))
            (let [[table' lc-a prf-a] (reify-term st table (nth args 4))
                  [table'' lc-b prf-b] (reify-term st table' (nth args 5))]
              [table'' (lc-add lc-a lc-b) (mk-add-eval-proof lc-a lc-b prf-a prf-b)])

            ;; Nat.sub a b → ground or atom with dichotomy tag
            (and (= head-name (:nat-sub omega-names)) (= 2 (count args)))
            (let [av (ground-nat-val (#'tc/cached-whnf st (nth args 0)))
                  bv (ground-nat-val (#'tc/cached-whnf st (nth args 1)))]
              (if (and av bv)
                (let [lc (mk-lc (max 0 (- av bv)))]
                  [table lc (mk-eval-rfl-proof lc)])
                (let [[table' idx] (intern-atom table st expr)
                      table' (assoc-in table' [:nat-sub-atoms idx]
                                       {:a (nth args 0) :b (nth args 1)})]
                  [table' (lc-coordinate idx) (mk-coordinate-eval-proof idx)])))

            ;; Nat.add a b → a + b
            (and (= head-name (:nat-add omega-names)) (= 2 (count args)))
            (let [[table' lc-a prf-a] (reify-term st table (nth args 0))
                  [table'' lc-b prf-b] (reify-term st table' (nth args 1))]
              [table'' (lc-add lc-a lc-b) (mk-add-eval-proof lc-a lc-b prf-a prf-b)])

            ;; Nat.succ n → n + 1
            (and (= head-name (:nat-succ omega-names)) (= 1 (count args)))
            (let [[table' lc prf] (reify-term st table (nth args 0))
                  one-lc (mk-lc 1)
                  result-lc (lc-add lc one-lc)]
              [table' result-lc (mk-add-eval-proof lc one-lc prf (mk-eval-rfl-proof one-lc))])

            ;; Nat.mul a b → handle if one operand is ground
            (and (= head-name (:nat-mul omega-names)) (= 2 (count args)))
            (let [a-whnf (#'tc/cached-whnf st (nth args 0))
                  b-whnf (#'tc/cached-whnf st (nth args 1))]
              (cond
                (e/lit-nat? a-whnf)
                (let [[table' lc-b prf-b] (reify-term st table (nth args 1))
                      k (e/lit-nat-val a-whnf)
                      result-lc (lc-scale lc-b k)]
                  [table' result-lc (mk-scale-eval-proof lc-b k prf-b (nth args 1) expr :left)])
                (e/lit-nat? b-whnf)
                (let [[table' lc-a prf-a] (reify-term st table (nth args 0))
                      k (e/lit-nat-val b-whnf)
                      result-lc (lc-scale lc-a k)]
                  [table' result-lc (mk-scale-eval-proof lc-a k prf-a (nth args 0) expr :right)])
                :else nil))  ;; fall through to WHNF path

            ;; HMul.hMul _ _ _ _ a b → a * b (pre-WHNF, handles ground operand)
            (and (= head-name (:hmul omega-names)) (= 6 (count args)))
            (let [a-whnf (#'tc/cached-whnf st (nth args 4))
                  b-whnf (#'tc/cached-whnf st (nth args 5))]
              (cond
                (e/lit-nat? a-whnf)
                (let [[table' lc-b prf-b] (reify-term st table (nth args 5))
                      k (e/lit-nat-val a-whnf)
                      result-lc (lc-scale lc-b k)]
                  [table' result-lc (mk-scale-eval-proof lc-b k prf-b (nth args 5) expr :left)])
                (e/lit-nat? b-whnf)
                (let [[table' lc-a prf-a] (reify-term st table (nth args 4))
                      k (e/lit-nat-val b-whnf)
                      result-lc (lc-scale lc-a k)]
                  [table' result-lc (mk-scale-eval-proof lc-a k prf-a (nth args 4) expr :right)])
                :else nil))  ;; fall through to WHNF path

            ;; HDiv.hDiv _ _ _ _ a b → atom + div-bounds tag
            (and (= head-name (:hdiv omega-names)) (= 6 (count args)))
            (let [type-whnf (#'tc/cached-whnf st (nth args 0))
                  type-name (when (e/const? type-whnf) (e/const-name type-whnf))]
              (reify-div-atom st table expr (nth args 4) (nth args 5) type-name))

            ;; Nat.div a b (BARE) → same, in the spelling the ansatz surface emits.
            ;; Must be handled here, pre-WHNF: Nat.div is well-founded-recursive and
            ;; WHNF turns it into a stuck Nat.div.go blob with a non-arithmetic head.
            (and (= head-name (:nat-div omega-names)) (= 2 (count args)))
            (reify-div-atom st table expr (nth args 0) (nth args 1) (:nat-name omega-names))

            ;; HMod.hMod _ _ _ _ a b → Nat: atom + Nat.mod_add_div; Int: emod_def
            (and (= head-name (:hmod omega-names)) (= 6 (count args)))
            (let [T0 (nth args 0) T1 (nth args 1) T2 (nth args 2)
                  tw (#'tc/cached-whnf st T0)
                  tn (when (e/const? tw) (e/const-name tw))]
              (if (= tn (:nat-name omega-names))
                (reify-mod-atom st table expr (nth args 4) (nth args 5))
                (reify-mod-decomp st table (nth args 4) (nth args 5)
                                  (fn [a b] (mk-hdiv-expr st T0 T1 T2 a b))
                                  (fn [b d] (mk-hmul-expr st T0 T1 T2 b d)))))

            ;; Nat.mod a b (BARE) → same atom as the HMod spelling above
            ;; (`intern-atom` keys on cached-whnf, which agrees for both).
            (and (= head-name (:nat-mod omega-names)) (= 2 (count args)))
            (reify-mod-atom st table expr (nth args 0) (nth args 1))

            ;; Neg.neg α inst a → -a (pre-WHNF to avoid unfolding)
            (and (= head-name (:neg-name omega-names)) (= 3 (count args)))
            (let [[table' lc prf] (reify-term st table (nth args 2))]
              [table' (lc-negate lc) (mk-neg-eval-proof lc prf)])

            ;; Int.negSucc k → the constant -(k+1). `Int.negSucc` is the ONLY spelling
            ;; a negative Int literal has, and without this clause every one of them
            ;; degraded to an opaque atom (`delta-to-arithmetic` cannot rescue it —
            ;; negSucc is a constructor, so it has no value to unfold).
            (and (= head-name (:int-negsucc omega-names)) (= 1 (count args))
                 (some? (ground-int-val expr)))
            (let [lc (mk-lc (ground-int-val expr))]
              [table lc (mk-eval-rfl-proof lc)])

            ;; Min.min α inst a b / Max.max α inst a b → atom + case-split facts
            (and (= head-name (:min-name omega-names)) (= 4 (count args)))
            (reify-min-max st table expr (nth args 0) (nth args 1)
                           (nth args 2) (nth args 3) true)

            (and (= head-name (:max-name omega-names)) (= 4 (count args)))
            (reify-min-max st table expr (nth args 0) (nth args 1)
                           (nth args 2) (nth args 3) false)

            ;; Nat.zero → 0
            (and (e/const? head) (= head-name (:nat-zero omega-names)) (= 0 (count args)))
            (let [lc (mk-lc 0)]
              [table lc (mk-eval-rfl-proof lc)])

            ;; A USER DEFINITION wrapping arithmetic (`byz-tolerance n = (n-1)/3`):
            ;; delta-unfold one step at a time until an arithmetic head appears, then
            ;; reify THAT. The blanket `whnf` below would unfold past `Nat.div` into a
            ;; stuck brecOn blob and lose the quotient. Def-eq, so the proof still checks.
            (and (e/const? head) (not (contains? arithmetic-heads head-name)))
            (when-let [unfolded (delta-to-arithmetic st expr)]
              (reify-term st table unfolded)))))
      (let [expr-whnf (#'tc/cached-whnf st expr)
            N (:nat-name omega-names)]
        (cond
      ;; Nat literal
          (e/lit-nat? expr-whnf)
          (let [lc (mk-lc (e/lit-nat-val expr-whnf))]
            [table lc (mk-eval-rfl-proof lc)])

      ;; Nat.zero
          (and (e/const? expr-whnf) (= (e/const-name expr-whnf) (:nat-zero omega-names)))
          (let [lc (mk-lc 0)]
            [table lc (mk-eval-rfl-proof lc)])

      ;; Application
          (e/app? expr-whnf)
          (let [matched (try-match-head st expr-whnf)]
            (if-not matched
              (let [[table' idx] (intern-atom table st expr-whnf)]
                [table' (lc-coordinate idx) (mk-coordinate-eval-proof idx)])
              (let [[head-name _ args] matched]
                (cond
              ;; Nat.succ n → n + 1
                  (and (= head-name (:nat-succ omega-names)) (= 1 (count args)))
                  (let [[table' lc prf] (reify-term st table (nth args 0))
                        one-lc (mk-lc 1)
                        result-lc (lc-add lc one-lc)]
                    [table' result-lc (mk-add-eval-proof lc one-lc prf (mk-eval-rfl-proof one-lc))])

              ;; Nat.add a b → a + b
                  (and (= head-name (:nat-add omega-names)) (= 2 (count args)))
                  (let [[table' lc-a prf-a] (reify-term st table (nth args 0))
                        [table'' lc-b prf-b] (reify-term st table' (nth args 1))]
                    [table'' (lc-add lc-a lc-b) (mk-add-eval-proof lc-a lc-b prf-a prf-b)])

              ;; HAdd.hAdd _ _ _ _ a b → a + b
                  (and (= head-name (:hadd omega-names)) (= 6 (count args)))
                  (let [[table' lc-a prf-a] (reify-term st table (nth args 4))
                        [table'' lc-b prf-b] (reify-term st table' (nth args 5))]
                    [table'' (lc-add lc-a lc-b) (mk-add-eval-proof lc-a lc-b prf-a prf-b)])

              ;; Nat.sub a b → ground evaluate or atom
                  (and (= head-name (:nat-sub omega-names)) (= 2 (count args)))
                  (let [a-whnf (#'tc/cached-whnf st (nth args 0))
                        b-whnf (#'tc/cached-whnf st (nth args 1))]
                    (if (and (e/lit-nat? a-whnf) (e/lit-nat? b-whnf))
                      (let [lc (mk-lc (max 0 (- (e/lit-nat-val a-whnf) (e/lit-nat-val b-whnf))))]
                        [table lc (mk-eval-rfl-proof lc)])
                  ;; Non-ground: intern as atom, tag for dichotomy generation
                      (let [[table' idx] (intern-atom table st expr-whnf)
                            table' (assoc-in table' [:nat-sub-atoms idx]
                                             {:a (nth args 0) :b (nth args 1)})]
                        [table' (lc-coordinate idx) (mk-coordinate-eval-proof idx)])))

              ;; HSub.hSub _ _ _ _ a b → a - b (Int subtraction)
                  (and (= head-name (:hsub omega-names)) (= 6 (count args)))
                  (let [[table' lc-a prf-a] (reify-term st table (nth args 4))
                        [table'' lc-b prf-b] (reify-term st table' (nth args 5))]
                    [table'' (lc-sub lc-a lc-b) (mk-sub-eval-proof lc-a lc-b prf-a prf-b)])

              ;; Multiplication: Nat.mul or HMul
                  (and (or (= head-name (:nat-mul omega-names))
                           (= head-name (:hmul omega-names))))
                  (let [[a b] (if (= head-name (:hmul omega-names))
                                [(nth args 4) (nth args 5)]
                                [(nth args 0) (nth args 1)])
                        a-whnf (#'tc/cached-whnf st a)
                        b-whnf (#'tc/cached-whnf st b)]
                    (cond
                  ;; Both ground: evaluate and use constant
                      (and (e/lit-nat? a-whnf) (e/lit-nat? b-whnf))
                      (let [val (* (e/lit-nat-val a-whnf) (e/lit-nat-val b-whnf))
                            lc (mk-lc val)]
                        [table lc (mk-eval-rfl-proof lc)])
                      (e/lit-nat? a-whnf)
                      (let [[table' lc-b prf-b] (reify-term st table b)
                            k (e/lit-nat-val a-whnf)
                            result-lc (lc-scale lc-b k)]
                        [table' result-lc (mk-scale-eval-proof lc-b k prf-b b expr-whnf :left)])
                      (e/lit-nat? b-whnf)
                      (let [[table' lc-a prf-a] (reify-term st table a)
                            k (e/lit-nat-val b-whnf)
                            result-lc (lc-scale lc-a k)]
                        [table' result-lc (mk-scale-eval-proof lc-a k prf-a a expr-whnf :right)])
                      :else
                      (let [[table' idx] (intern-atom table st expr-whnf)]
                        [table' (lc-coordinate idx) (mk-coordinate-eval-proof idx)])))

              ;; Div/mod reached only through WHNF (an unusual spelling). Route through
              ;; the same helpers as the pre-WHNF clauses so every spelling decides
              ;; identically — in particular so a symbolic divisor still gets bounds.
                  (and (= head-name (:nat-div omega-names)) (= 2 (count args)))
                  (reify-div-atom st table expr-whnf (nth args 0) (nth args 1)
                                  (:nat-name omega-names))

                  (and (= head-name (:nat-mod omega-names)) (= 2 (count args)))
                  (reify-mod-atom st table expr-whnf (nth args 0) (nth args 1))

              ;; OfNat.ofNat _ n _ → n
                  (and (= head-name (:ofnat omega-names)) (>= (count args) 2))
                  (reify-term st table (nth args 1))

              ;; Unknown → atom
                  :else
                  (let [[table' idx] (intern-atom table st expr-whnf)]
                    [table' (lc-coordinate idx) (mk-coordinate-eval-proof idx)])))))

      ;; Free variable → atom
          (e/fvar? expr-whnf)
          (let [[table' idx] (intern-atom table st expr-whnf)]
            [table' (lc-coordinate idx) (mk-coordinate-eval-proof idx)])

      ;; Constant
          (e/const? expr-whnf)
          (if (= (e/const-name expr-whnf) (:nat-zero omega-names))
            (let [lc (mk-lc 0)]
              [table lc (mk-eval-rfl-proof lc)])
            (let [[table' idx] (intern-atom table st expr-whnf)]
              [table' (lc-coordinate idx) (mk-coordinate-eval-proof idx)]))

      ;; Anything else → atom
          :else
          (let [[table' idx] (intern-atom table st expr-whnf)]
            [table' (lc-coordinate idx) (mk-coordinate-eval-proof idx)])))))

;; ============================================================
;; Problem: delegated to ansatz.tactic.omega.problem
;; ============================================================

(defn as-linear-combo
  "Frontend.asLinearCombo cache. Delayed proof orientation is lc.eval = original.
   Keys are exact original expressions; branch rollback restores the whole table."
  [st table expr]
  (if-let [[lc proof] (get (:cache table) expr)]
    [table lc proof]
    (let [[table lc proof] (as-linear-combo-impl st table expr)]
      [(assoc-in table [:cache expr] [lc proof]) lc proof])))

(defn- reify-term [st table expr] (as-linear-combo st table expr))

(def ^:private mk-problem op/mk-problem)
(def ^:private queue-disjunction op/queue-disjunction)
(def ^:private coeffs-key op/coeffs-key)
(def ^:private all-zero-coeffs? op/all-zero-coeffs?)
(def ^:private constraint-unsat-at-zero? op/constraint-unsat-at-zero?)
(def ^:private is-impossible? op/is-impossible?)
(def ^:private insert-constraint op/insert-constraint)
(def ^:private add-constraint op/add-constraint)

;; ============================================================
;; Ansatz term builders for Lean.Omega data structures
;; ============================================================

(def ^:private to-lean-int op/to-lean-int)
(def ^:private to-lean-coeffs op/to-lean-coeffs)
(def ^:private to-lean-option-int op/to-lean-option-int)
(def ^:private to-lean-constraint op/to-lean-constraint)
(def ^:private to-lean-linear-combo op/to-lean-linear-combo)
(def ^:private mk-int-neg op/mk-int-neg)
(def ^:private mk-add-inequality-proof op/mk-add-inequality-proof)
(def ^:private mk-add-equality-proof op/mk-add-equality-proof)

(defn- add-inequality
  "Add: const + dot(coeffs, atoms) >= 0.
   Stored as: coeffs in [-const, infinity).
   proof-fn: delayed fn producing a proof of `const + dot(coeffs, atoms) >= 0`."
  [problem const coeffs proof-fn]
  (op/add-inequality problem const coeffs proof-fn mk-add-inequality-proof))

(defn- add-equality
  "Add: const + dot(coeffs, atoms) = 0.
   Stored as: coeffs in {-const}.
   proof-fn: delayed fn producing a proof of `const + dot(coeffs, atoms) = 0`."
  [problem const coeffs proof-fn]
  (op/add-equality problem const coeffs proof-fn mk-add-equality-proof))

;; ============================================================
;; Equality solving
;; ============================================================

;; ============================================================
;; Solver: delegated to ansatz.tactic.omega.fm
;; ============================================================

(def ^:private mk-bmod-expr op/mk-bmod-expr)
(def run-omega-solver op/run-omega-solver)
(def ^:private pad-coeffs op/pad-coeffs)
(def ^:private extract-proof op/extract-proof)
(def ^:private build-atoms-expr op/build-atoms-expr)
(def ^:private build-decide-proof op/build-decide-proof)
(def ^:private prove-false-from-justification op/prove-false-from-justification)

(defn- tactic-error! [msg data]
  (throw (ex-info (str "omega: " msg) (merge {:kind :tactic-error} data))))

(declare reify-prop reify-prop-forall reify-prop-iff negate-goal negate-goal-forall)

(def ^:private int-zero
  "The Int expression for 0: Int.ofNat 0"
  (e/app (e/const' (name/from-string "Int.ofNat") []) (e/lit-nat 0)))

(defn- mk-nat-to-int-le
  "Convert h : a ≤ b (Nat) to ↑a ≤ ↑b (Int).
   Uses: Iff.mpr {↑a ≤ ↑b} {a ≤ b} (Int.ofNat_le a b) h"
  [a-nat b-nat hyp-proof]
  (let [int-le-prop (e/app* (e/const' (:le-name omega-names) [lvl/zero])
                            int-type (e/const' (:int-inst-le omega-names) [])
                            (nat-to-int a-nat) (nat-to-int b-nat))
        nat-le-prop (e/app* (e/const' (:le-name omega-names) [lvl/zero])
                            (e/const' (:nat-name omega-names) [])
                            (e/const' (:inst-le-nat omega-names) [])
                            a-nat b-nat)]
    (e/app* (e/const' (:iff-mpr omega-names) [])
            int-le-prop nat-le-prop
            (e/app* (e/const' (:int-ofnat-le omega-names) []) a-nat b-nat)
            hyp-proof)))

(defn- mk-le-of-le-of-eq
  "Build le_of_le_of_eq.{0} Int a b c Int.instLEInt h1 h2 : a ≤ c
   given h1 : a ≤ b, h2 : b = c"
  [a b c h1 h2]
  (e/app* (e/const' (:le-of-le-of-eq omega-names) [lvl/zero])
          int-type a b c (e/const' (:int-inst-le omega-names) []) h1 h2))

(defn- mk-ineq-proof-fn
  "Build a proof function for an inequality hypothesis h : a ≤ b.
   Chain: h → ↑a ≤ ↑b → 0 ≤ ↑b - ↑a → 0 ≤ lc.eval atoms.
   diff-prf-fn returns {:proof :lhs :rhs} where proof : lhs = rhs, lhs = lc.eval atoms."
  [hyp-proof a-expr b-expr _diff-lc diff-prf-fn type-name]
  (if (nil? hyp-proof)
    nil
    (fn [atoms-expr]
      (let [a-int (if (= type-name (:nat-name omega-names)) (nat-to-int a-expr) a-expr)
            b-int (if (= type-name (:nat-name omega-names)) (nat-to-int b-expr) b-expr)
            h-int (if (= type-name (:nat-name omega-names))
                    (mk-nat-to-int-le a-expr b-expr hyp-proof)
                    hyp-proof)
            ;; Int.sub_nonneg_of_le : ∀ {a b}, b ≤ a → 0 ≤ a - b
            ;; h-int : a-int ≤ b-int, so pass {b-int} {a-int} h-int → 0 ≤ b-int - a-int
            sub-expr (mk-int-sub b-int a-int)
            h-sub (e/app* (e/const' (:int-sub-nonneg-of-le omega-names) [])
                          b-int a-int h-int)
            ;; Get eval proof: lc.eval atoms = ↑b - ↑a (or similar)
            eval-result (if (fn? diff-prf-fn) (diff-prf-fn atoms-expr) diff-prf-fn)
            eval-lhs (:lhs eval-result)
            eval-rhs (:rhs eval-result)
            ;; Eq.symm: (↑b - ↑a) = lc.eval atoms
            symm-proof (mk-eq-symm eval-lhs eval-rhs (:proof eval-result))]
        ;; le_of_le_of_eq: 0 ≤ (↑b - ↑a) → (↑b - ↑a) = lc.eval → 0 ≤ lc.eval
        (mk-le-of-le-of-eq int-zero sub-expr eval-lhs h-sub symm-proof)))))

(defn- mk-eq-proof-fn
  "Build a proof function for an equality hypothesis h : a = b.
   Chain: h → ↑a = ↑b → ↑a - ↑b = 0 → lc.eval atoms = 0."
  [hyp-proof a-expr b-expr _diff-lc diff-prf-fn type-name]
  (if (nil? hyp-proof)
    nil
    (fn [atoms-expr]
      (let [a-int (if (= type-name (:nat-name omega-names)) (nat-to-int a-expr) a-expr)
            b-int (if (= type-name (:nat-name omega-names)) (nat-to-int b-expr) b-expr)
            ;; Convert Nat = to Int = via congrArg Int.ofNat h
            ;; congrArg.{u,v} : {α} {β} {a1} {a2} (f : α→β) (h : a1=a2) → f a1 = f a2
            h-int (if (= type-name (:nat-name omega-names))
                    (e/app* (e/const' (:congr-arg omega-names) [u1 u1])
                            (e/const' (:nat-name omega-names) []) ;; α = Nat
                            int-type ;; β = Int
                            a-expr b-expr ;; {a1} {a2}
                            (e/const' (:int-ofnat omega-names) []) ;; f = Int.ofNat
                            hyp-proof)
                    hyp-proof)
            ;; Int.sub_eq_zero_of_eq : {a b : Int} → a = b → a - b = 0
            sub-expr (mk-int-sub a-int b-int)
            h-sub (e/app* (e/const' (:int-sub-eq-zero-of-eq omega-names) [])
                          a-int b-int h-int)
            ;; eval proof: lc.eval atoms = (a-int - b-int)
            eval-result (if (fn? diff-prf-fn) (diff-prf-fn atoms-expr) diff-prf-fn)
            eval-lhs (:lhs eval-result)
            eval-rhs (:rhs eval-result)
            ;; Chain: lc.eval = (↑a - ↑b) = 0
            symm-proof (mk-eq-symm eval-lhs eval-rhs (:proof eval-result))]
        ;; Eq.trans ((↑a - ↑b) = lc.eval) ... no wait
        ;; We want: lc.eval atoms = 0
        ;; eval proof: lc.eval = rhs (where rhs ≈ ↑a - ↑b)
        ;; h-sub: ↑a - ↑b = 0
        ;; So: Eq.trans eval_proof h-sub : lc.eval = 0
        ;; But rhs may differ from sub-expr... for now assume they match
        (mk-eq-trans eval-lhs eval-rhs int-zero (:proof eval-result) h-sub)))))

(defn- mk-lt-proof-fn
  "Build a proof function for a strict inequality hypothesis h : a < b.
   Chain: h → ↑a < ↑b → ↑a + 1 ≤ ↑b → 0 ≤ ↑b - (↑a + 1) → 0 ≤ lc.eval atoms."
  [hyp-proof a-expr b-expr _diff-lc diff-prf-fn type-name]
  (if (nil? hyp-proof)
    nil
    (fn [atoms-expr]
      (let [a-int (if (= type-name (:nat-name omega-names)) (nat-to-int a-expr) a-expr)
            b-int (if (= type-name (:nat-name omega-names)) (nat-to-int b-expr) b-expr)
            ;; Convert Nat < to Int <
            ;; Iff.mpr {↑a < ↑b} {a < b} (Int.ofNat_lt a b) h
            h-int (if (= type-name (:nat-name omega-names))
                    (let [int-lt-prop (e/app* (e/const' (:lt-name omega-names) [lvl/zero])
                                              int-type (e/const' (name/from-string "Int.instLTInt") [])
                                              (nat-to-int a-expr) (nat-to-int b-expr))
                          nat-lt-prop (e/app* (e/const' (:lt-name omega-names) [lvl/zero])
                                              (e/const' (:nat-name omega-names) [])
                                              (e/const' (:inst-lt-nat omega-names) [])
                                              a-expr b-expr)]
                      (e/app* (e/const' (:iff-mpr omega-names) [])
                              int-lt-prop nat-lt-prop
                              (e/app* (e/const' (:int-ofnat-lt omega-names) []) a-expr b-expr)
                              hyp-proof))
                    hyp-proof)
            ;; Int.add_one_le_of_lt : {a b : Int} → a < b → a + 1 ≤ b
            int-one (e/app (e/const' (name/from-string "Int.ofNat") []) (e/lit-nat 1))
            a-plus-1 (mk-int-add a-int int-one)
            h-le (e/app* (e/const' (:int-add-one-le-of-lt omega-names) [])
                         a-int b-int h-int)
            ;; sub_nonneg_of_le : ∀ {a b}, b ≤ a → 0 ≤ a - b
            ;; h-le : a+1 ≤ b, so pass {b} {a+1} → 0 ≤ b - (a+1)
            sub-expr (mk-int-sub b-int a-plus-1)
            h-sub (e/app* (e/const' (:int-sub-nonneg-of-le omega-names) [])
                          b-int a-plus-1 h-le)
            ;; Eval proof bridge
            eval-result (if (fn? diff-prf-fn) (diff-prf-fn atoms-expr) diff-prf-fn)
            eval-lhs (:lhs eval-result)
            eval-rhs (:rhs eval-result)
            symm-proof (mk-eq-symm eval-lhs eval-rhs (:proof eval-result))]
        (mk-le-of-le-of-eq int-zero sub-expr eval-lhs h-sub symm-proof)))))

(defn- mk-nat-sub-dichotomy
  "Build the Nat.sub dichotomy disjunction.
   For atom = ↑(a - b), generates:
     Nat.le_total b a : b ≤ a ∨ a ≤ b  (note: we want b ≤ a ∨ a < b, but le_total gives b ≤ a ∨ a ≤ b)
   Left branch (b ≤ a):  ↑(a-b) = ↑a - ↑b  via Int.ofNat_sub
   Right branch (a ≤ b): a - b = 0 via Nat.sub_eq_zero_of_le, so ↑(a-b) = 0

   Actually, Nat.le_total gives m ≤ n ∨ n ≤ m. We use Nat.le_total b a : b ≤ a ∨ a ≤ b.
   Left (b ≤ a): ↑(a-b) = ↑a - ↑b  [real subtraction]
   Right (a ≤ b): a-b = 0, so ↑(a-b) = ↑0 = 0  [truncated to zero]

   Returns a disjunction to queue:
   {:or-proof (Nat.le_total b a), :left-type (b ≤ a), :right-type (a ≤ b),
    :left-facts [...], :right-facts [...]}

   But for simplicity, we queue the raw Or and let reify-prop handle each branch."
  [table atom-idx nat-a nat-b]
  (let [nat-type (e/const' (:nat-name omega-names) [])
        le-inst (e/const' (:inst-le-nat omega-names) [])
        ;; b ≤ a
        left-type (e/app* (e/const' (:le-name omega-names) [lvl/zero])
                          nat-type le-inst nat-b nat-a)
        ;; a ≤ b
        right-type (e/app* (e/const' (:le-name omega-names) [lvl/zero])
                           nat-type le-inst nat-a nat-b)
        ;; Nat.le_total b a : b ≤ a ∨ a ≤ b
        or-proof (e/app* (e/const' (:nat-le-total omega-names) [])
                         nat-b nat-a)]
    {:or-proof or-proof
     :left-type left-type
     :right-type right-type
     ;; Metadata for building equality constraints in branches
     :nat-sub-info {:atom-idx atom-idx :nat-a nat-a :nat-b nat-b}}))

(defn- add-nat-sub-dichotomies
  "For each Nat.sub atom in the table, queue a dichotomy disjunction. Returns
   [table problem].

   IDEMPOTENT (:sub-dichotomies-added), because it has to run more than once: a
   truncated subtraction can first appear INSIDE a quotient — `(n-1)/3` reifies to
   a single opaque quotient atom, and the `n-1` sub-atom only gets interned later,
   while `add-div-bounds` reifies `Nat.div_mul_le_self (n-1) 3`. A single up-front
   pass therefore misses exactly the dichotomy that goal needs."
  [table problem]
  (reduce (fn [[table problem] [idx {:keys [a b]}]]
            (if (contains? (:sub-dichotomies-added table) idx)
              [table problem]
              [(update table :sub-dichotomies-added (fnil conj #{}) idx)
               (queue-disjunction problem (mk-nat-sub-dichotomy table idx a b))]))
          [table problem]
          (:nat-sub-atoms table)))

(defn- mk-minmax-dichotomy
  "Build the case split that pins down a `min`/`max` atom.

   With `P := a ≤ b`, `dec : Decidable P` and the atom `m := min a b` (whose instance
   field is `ite α P dec a b`), the disjunction is

       (P ∧ m = a) ∨ (¬P ∧ m = b)          -- for min
       (P ∧ m = b) ∨ (¬P ∧ m = a)          -- for max  (maxOfLe swaps the ite branches)

   proved by `Or.elim (Decidable.em P dec)` with `if_pos`/`if_neg` supplying the
   equation in each branch. Both halves are stated over the ORIGINAL `Min.min …`
   spelling, def-eq to the `ite`, so the kernel accepts them and `reify-prop`'s `And`
   handler feeds the ordering fact and the value equation to the solver separately."
  [{:keys [expr alpha a b min? le-inst dec-rel rewrite ite]}]
  (let [P      (e/app* (e/const' (:le-name omega-names) [lvl/zero]) alpha le-inst a b)
        not-P  (e/app (e/const' (:not-name omega-names) []) P)
        dec    (e/app* dec-rel a b)
        ;; the `ite α P dec t e` branches of minOfLe / maxOfLe
        [t-br e-br] (if min? [a b] [b a])
        eq-of  (fn [rhs] (e/app* (e/const' (:eq-name omega-names) [u1]) alpha expr rhs))
        eq-t   (eq-of t-br)
        eq-e   (eq-of e-br)
        left-type  (e/app* (e/const' (:and-name omega-names) []) P eq-t)
        right-type (e/app* (e/const' (:and-name omega-names) []) not-P eq-e)
        or-type    (e/app* (e/const' (:or-name omega-names) []) left-type right-type)
        ;; if_pos/if_neg : (c) (inst) (h) (α) (t e) → ite α c inst t e = t / = e
        mk-if  (fn [k h]
                 (let [p (e/app* (e/const' (k omega-names) [u1]) P dec h alpha t-br e-br)]
                   (if rewrite
                     (mk-eq-trans expr ite (if (= k :if-pos) t-br e-br) rewrite p)
                     p)))
        left-lam
        (e/lam "h_le" P
               (e/app* (e/const' (:or-inl omega-names) []) left-type right-type
                       (e/app* (e/const' (:and-intro omega-names) []) P eq-t
                               (e/bvar 0) (mk-if :if-pos (e/bvar 0))))
               :default)
        right-lam
        (e/lam "h_gt" not-P
               (e/app* (e/const' (:or-inr omega-names) []) left-type right-type
                       (e/app* (e/const' (:and-intro omega-names) []) not-P eq-e
                               (e/bvar 0) (mk-if :if-neg (e/bvar 0))))
               :default)
        or-proof (e/app* (e/const' (:or-elim omega-names) [])
                         P not-P or-type
                         (e/app* (e/const' (:decidable-em omega-names) []) P dec)
                         left-lam right-lam)]
    {:or-proof or-proof :left-type left-type :right-type right-type}))

(defn- add-minmax-dichotomies
  "Queue one `mk-minmax-dichotomy` per min/max atom. IDEMPOTENT
   (:minmax-dichotomies-added), for the same reason `add-nat-sub-dichotomies` is:
   a min/max can first surface while reifying a disjunction branch."
  [table problem]
  (reduce (fn [[table problem] [idx info]]
            (if (contains? (:minmax-dichotomies-added table) idx)
              [table problem]
              [(update table :minmax-dichotomies-added (fnil conj #{}) idx)
               (queue-disjunction problem (mk-minmax-dichotomy info))]))
          [table problem]
          (:minmax-atoms table)))

(defn- add-nat-sub-equality
  "Add Nat.sub equality constraint for a dichotomy branch.
   For left branch (b ≤ a): add Eq Int ↑(a-b) (↑a - ↑b) via Int.ofNat_sub
   For right branch (a ≤ b): add Eq Int ↑(a-b) ↑0 via congrArg ofNat (Nat.sub_eq_zero_of_le)
   Delegates to reify-prop's Eq handler for proper proof chain construction."
  [st table problem {:keys [atom-idx nat-a nat-b]} branch hyp-proof]
  (let [nat-sub-expr (e/app* (e/const' (:nat-sub omega-names) []) nat-a nat-b)
        nat-sub-int (nat-to-int nat-sub-expr)]
    (case branch
      :left
      ;; b ≤ a, so ↑(a-b) = ↑a - ↑b
      ;; Int.ofNat_sub : (arg0 arg1 : Nat) → arg0 ≤ arg1 → ↑(arg1 - arg0) = ↑arg1 - ↑arg0
      ;; arg0=nat-b, arg1=nat-a, hyp : nat-b ≤ nat-a
      (let [eq-proof (e/app* (e/const' (:int-ofnat-sub omega-names) [])
                             nat-b nat-a hyp-proof)
            ;; eq-proof : @Eq Int ↑(a-b) (↑a - ↑b)
            rhs (mk-int-sub (nat-to-int nat-a) (nat-to-int nat-b))
            eq-type (e/app* (e/const' (:eq-name omega-names) [u1])
                            int-type nat-sub-int rhs)]
        ;; Feed through reify-prop as Eq Int ↑(a-b) (↑a - ↑b)
        (reify-prop st table problem eq-type eq-proof))
      :right
      ;; a ≤ b, so a - b = 0 in Nat, hence ↑(a-b) = ↑0 in Int
      ;; Nat.sub_eq_zero_of_le : {n m : Nat} → n ≤ m → n - m = 0
      ;; n=nat-a, m=nat-b, hyp : nat-a ≤ nat-b
      (let [nat-sub-zero (e/app* (e/const' (:nat-sub-eq-zero-of-le omega-names) [])
                                 nat-a nat-b hyp-proof)
            ;; nat-sub-zero : @Eq Nat (a - b) 0
            ;; congrArg Int.ofNat nat-sub-zero : @Eq Int ↑(a-b) ↑0
            ofnat-fn (e/const' (:int-ofnat omega-names) [])
            nat-zero (e/lit-nat 0)
            congr-proof (e/app* (e/const' (:congr-arg omega-names) [u1 u1])
                                (e/const' (:nat-name omega-names) [])
                                int-type
                                nat-sub-expr nat-zero
                                ofnat-fn
                                nat-sub-zero)
            ;; congr-proof : @Eq Int ↑(a-b) ↑0
            zero-int (nat-to-int nat-zero)
            eq-type (e/app* (e/const' (:eq-name omega-names) [u1])
                            int-type nat-sub-int zero-int)]
        (reify-prop st table problem eq-type congr-proof)))))

(defn- mk-not-eq-true-of-eq-false
  "From `h : b = false` build `¬(b = true)`, i.e.
     fun (ht : b = true) => Bool.noConfusion (Eq.trans (Eq.symm h) ht : false = true)"
  [b-expr h]
  (let [bool-t (e/const' (:bool-name omega-names) [])
        b-true (e/const' (:bool-true omega-names) [])
        b-false (e/const' (:bool-false omega-names) [])
        eq-b-true (e/app* (e/const' (:eq-name omega-names) [u1]) bool-t b-expr b-true)
        symm-h (e/app* (e/const' (:eq-symm omega-names) [u1]) bool-t b-expr b-false h)
        trans (e/app* (e/const' (:eq-trans omega-names) [u1])
                      bool-t b-false b-expr b-true symm-h (e/bvar 0))]
    (e/lam "h_true" eq-b-true
           (e/app* (e/const' (:bool-noconfusion omega-names) [lvl/zero])
                   (e/const' (:false-name omega-names) [])
                   b-false b-true trans)
           :default)))

(defn- bool-cmp-bridge
  "The Bool→Prop bridge: turn a BOOLEAN comparison equation into the arithmetic Prop
   it denotes, together with a proof of that Prop. Returns [prop proof] or nil.

     Nat.ble a b = true   →  a ≤ b       (Nat.le_of_ble_eq_true)
     Nat.ble a b = false  →  ¬(a ≤ b)    (Nat.not_le_of_not_ble_eq_true)
     Nat.blt a b = v      →  the same, at `Nat.ble (a+1) b` — `Nat.blt` is *defined*
                             as `Nat.ble (Nat.succ a) b`, so the very same `h` proves
                             the `ble` form and `Nat.succ a ≤ b` IS `a < b`.

   This is where our frontend deliberately goes beyond lean4's. lean4's `addFact`
   drops these on the floor — its `Eq α x y` match has no `Bool` case, it falls
   through to `pure (p, 0)` (Frontend.lean:441-448) — because a `simp` pre-pass has
   already rewritten `Nat.ble a b = true` to `a ≤ b` via `Nat.ble_eq`. We have no
   such pre-pass, and `grind`/`simp` case-splitting a `Nat.ble` discriminant through
   `Bool.rec` hands omega exactly this shape (it is what the insertion-sort
   preservation proofs hit), so the bridge lives in the reifier instead."
  [st args hyp-proof]
  (when hyp-proof
    (let [lhs (nth args 1)
          rhs-w (#'tc/cached-whnf st (nth args 2))
          [lh la] (e/get-app-fn-args lhs)
          lh-name (when (e/const? lh) (e/const-name lh))
          rhs-name (when (e/const? rhs-w) (e/const-name rhs-w))
          true? (= rhs-name (:bool-true omega-names))
          false? (= rhs-name (:bool-false omega-names))
          ble? (= lh-name (:nat-ble omega-names))
          blt? (= lh-name (:nat-blt omega-names))]
      (when (and (or ble? blt?) (= 2 (count la)) (or true? false?))
        ;; `Nat.blt a b` unfolds to `Nat.ble (Nat.succ a) b`; state everything over
        ;; the `ble` operands so one code path serves both.
        (let [a (if blt? (e/app (e/const' (:nat-succ omega-names) []) (nth la 0)) (nth la 0))
              b (nth la 1)
              nat-t (e/const' (:nat-name omega-names) [])
              le-prop (e/app* (e/const' (:le-name omega-names) [lvl/zero])
                              nat-t (e/const' (:inst-le-nat omega-names) []) a b)]
          (if true?
            [le-prop (e/app* (e/const' (:nat-le-of-ble-eq-true omega-names) [])
                             a b hyp-proof)]
            (let [ble-expr (e/app* (e/const' (:nat-ble omega-names) []) a b)
                  not-ble (mk-not-eq-true-of-eq-false ble-expr hyp-proof)]
              [(e/app (e/const' (:not-name omega-names) []) le-prop)
               (e/app* (e/const' (:nat-not-le-of-not-ble omega-names) [])
                       a b not-ble)])))))))

(defn- reify-prop
  "Reify a Ansatz proposition into constraints added to the problem.
   hyp-proof is the Ansatz proof term for the hypothesis (an fvar or nil for backward compat).
   Returns [atom-table problem]."
  [st table problem prop hyp-proof]
  (let [matched (try-match-head st prop)]
    (if-not matched
      ;; No const head — try forall (implication)
      (reify-prop-forall st table problem prop hyp-proof)
      (let [[head-name head-levels args] matched
            ;; Eq Bool (Nat.ble a b) true/false (and Nat.blt) — the Bool→Prop bridge.
            ;; Taken BEFORE the general Eq case, which would try to reify `Nat.ble a b`
            ;; as an arithmetic term and reject it as an atom of non-arithmetic type.
            bridged (when (and (= head-name (:eq-name omega-names)) (= 3 (count args)))
                      (bool-cmp-bridge st args hyp-proof))]
        (cond
          bridged
          (reify-prop st table problem (first bridged) (second bridged))

          ;; A relation over a carrier omega does not handle is NOT a fact — Lean's frontend
          ;; (Elab/Tactic/Omega/Frontend.lean:441-478) matches the carrier against Int, Nat
          ;; and Fin, and for anything else `pure (p, 0)`: the hypothesis contributes nothing
          ;; and a goal over it fails as "could not prove". Reifying a Real relation as if it
          ;; were Int built `HSub Int … (x : Real)` — a proof the kernel rejected, but only
          ;; after the tactic had returned it, which stranded `positivity` and `linarith`
          ;; (both try omega inside a catch-and-fall-through chain).
          (and (#{(:eq-name omega-names) (:le-name omega-names) (:lt-name omega-names)
                  (:ge-name omega-names) (:gt-name omega-names)
                  (:ne-name omega-names) (:dvd-name omega-names)} head-name)
               (>= (count args) 3)
               (let [t (#'tc/cached-whnf st (nth args 0))]
                 (not (and (e/const? t)
                           (#{(:nat-name omega-names) (:int-name omega-names)} (e/const-name t))))))
          [table problem]

          ;; Eq _ a b → a - b = 0
          (and (= head-name (:eq-name omega-names)) (= 3 (count args)))
          (let [type-arg (nth args 0)
                type-whnf (#'tc/cached-whnf st type-arg)
                type-name (when (e/const? type-whnf) (e/const-name type-whnf))
                [table' lc-a prf-a] (reify-term st table (nth args 1))
                [table'' lc-b prf-b] (reify-term st table' (nth args 2))
                diff (lc-sub lc-a lc-b)
                diff-prf (mk-sub-eval-proof lc-a lc-b prf-a prf-b)
                proof-fn (mk-eq-proof-fn hyp-proof (nth args 1) (nth args 2)
                                         diff diff-prf type-name)]
            [table'' (add-equality problem (:const diff) (:coeffs diff) proof-fn)])

          ;; LE.le _ _ a b → b - a ≥ 0
          (and (= head-name (:le-name omega-names)) (= 4 (count args)))
          (let [type-arg (nth args 0)
                type-whnf (#'tc/cached-whnf st type-arg)
                type-name (when (e/const? type-whnf) (e/const-name type-whnf))
                a-arg (nth args 2) b-arg (nth args 3)
                [table' lc-a prf-a] (reify-term st table a-arg)
                [table'' lc-b prf-b] (reify-term st table' b-arg)
                diff (lc-sub lc-b lc-a)
                diff-prf (mk-sub-eval-proof lc-b lc-a prf-b prf-a)
                proof-fn (mk-ineq-proof-fn hyp-proof a-arg b-arg diff diff-prf type-name)]
            [table'' (add-inequality problem (:const diff) (:coeffs diff) proof-fn)])

          ;; Nat.le a b → b - a ≥ 0
          (and (= head-name (:nat-le omega-names)) (= 2 (count args)))
          (let [[table' lc-a prf-a] (reify-term st table (nth args 0))
                [table'' lc-b prf-b] (reify-term st table' (nth args 1))
                diff (lc-sub lc-b lc-a)
                diff-prf (mk-sub-eval-proof lc-b lc-a prf-b prf-a)
                proof-fn (mk-ineq-proof-fn hyp-proof (nth args 0) (nth args 1)
                                           diff diff-prf (:nat-name omega-names))]
            [table'' (add-inequality problem (:const diff) (:coeffs diff) proof-fn)])

          ;; LT.lt _ _ a b → b - a - 1 ≥ 0
          (and (= head-name (:lt-name omega-names)) (= 4 (count args)))
          (let [type-arg (nth args 0)
                type-whnf (#'tc/cached-whnf st type-arg)
                type-name (when (e/const? type-whnf) (e/const-name type-whnf))
                a-arg (nth args 2) b-arg (nth args 3)
                [table' lc-a prf-a] (reify-term st table a-arg)
                [table'' lc-b prf-b] (reify-term st table' b-arg)
                ;; a < b becomes a+1 ≤ b, so diff = b - (a+1)
                one-lc (mk-lc 1)
                lc-a-plus-1 (lc-add lc-a one-lc)
                prf-a-plus-1 (mk-add-eval-proof lc-a one-lc prf-a (mk-eval-rfl-proof one-lc))
                diff (lc-sub lc-b lc-a-plus-1)
                diff-prf (mk-sub-eval-proof lc-b lc-a-plus-1 prf-b prf-a-plus-1)
                proof-fn (mk-lt-proof-fn hyp-proof a-arg b-arg diff diff-prf type-name)]
            [table'' (add-inequality problem (:const diff) (:coeffs diff) proof-fn)])

          ;; GE.ge _ _ a b → a - b ≥ 0
          ;; GE.ge α inst a b means a ≥ b, i.e., b ≤ a, so a - b ≥ 0
          (and (= head-name (:ge-name omega-names)) (= 4 (count args)))
          (let [type-arg (nth args 0)
                type-whnf (#'tc/cached-whnf st type-arg)
                type-name (when (e/const? type-whnf) (e/const-name type-whnf))
                ;; GE.ge α inst a b: a=args[2], b=args[3]
                ;; Convert to LE.le b a via ge_iff_le, then treat as b ≤ a
                ge-a (nth args 2) ge-b (nth args 3)
                [table' lc-b prf-b] (reify-term st table ge-b)
                [table'' lc-a prf-a] (reify-term st table' ge-a)
                ;; diff = a - b ≥ 0
                diff (lc-sub lc-a lc-b)
                diff-prf (mk-sub-eval-proof lc-a lc-b prf-a prf-b)
                ;; Build proof: Iff.mp (ge_iff_le α inst a b) hyp : b ≤ a
                ;; Then use mk-ineq-proof-fn with b ≤ a (le-proof for b, a)
                le-inst (nth args 1) ;; LE instance (from GE args)
                ge-iff (when hyp-proof
                         (e/app* (e/const' (:ge-iff-le omega-names) head-levels)
                                 type-arg le-inst ge-a ge-b))
                le-proof (when hyp-proof
                           (e/app* (e/const' (:iff-mp omega-names) [])
                                   (e/app* (e/const' (:ge-name omega-names) [lvl/zero])
                                           type-arg le-inst ge-a ge-b)
                                   (e/app* (e/const' (:le-name omega-names) [lvl/zero])
                                           type-arg le-inst ge-b ge-a)
                                   ge-iff hyp-proof))
                ;; Now le-proof : b ≤ a, use mk-ineq-proof-fn with (b, a)
                proof-fn (mk-ineq-proof-fn le-proof ge-b ge-a diff diff-prf type-name)]
            [table'' (add-inequality problem (:const diff) (:coeffs diff) proof-fn)])

          ;; GT.gt _ _ a b → a - b - 1 ≥ 0
          ;; GT.gt α inst a b means a > b, i.e., b < a
          (and (= head-name (:gt-name omega-names)) (= 4 (count args)))
          (let [type-arg (nth args 0)
                type-whnf (#'tc/cached-whnf st type-arg)
                type-name (when (e/const? type-whnf) (e/const-name type-whnf))
                gt-a (nth args 2) gt-b (nth args 3)
                [table' lc-a prf-a] (reify-term st table gt-a)
                [table'' lc-b prf-b] (reify-term st table' gt-b)
                ;; a > b means b < a, i.e., b+1 ≤ a, i.e., a - b - 1 ≥ 0
                one-lc (mk-lc 1)
                lc-b-plus-1 (lc-add lc-b one-lc)
                prf-b-plus-1 (mk-add-eval-proof lc-b one-lc prf-b (mk-eval-rfl-proof one-lc))
                diff (lc-sub lc-a lc-b-plus-1)
                diff-prf (mk-sub-eval-proof lc-a lc-b-plus-1 prf-a prf-b-plus-1)
                ;; Build proof: Iff.mp (gt_iff_lt α lt-inst a b) hyp : b < a
                lt-inst (nth args 1) ;; LT instance
                gt-iff (when hyp-proof
                         (e/app* (e/const' (:gt-iff-lt omega-names) head-levels)
                                 type-arg lt-inst gt-a gt-b))
                lt-proof (when hyp-proof
                           (e/app* (e/const' (:iff-mp omega-names) [])
                                   (e/app* (e/const' (:gt-name omega-names) [lvl/zero])
                                           type-arg lt-inst gt-a gt-b)
                                   (e/app* (e/const' (:lt-name omega-names) [lvl/zero])
                                           type-arg lt-inst gt-b gt-a)
                                   gt-iff hyp-proof))
                ;; lt-proof : b < a, use mk-lt-proof-fn with (b, a)
                proof-fn (mk-lt-proof-fn lt-proof gt-b gt-a diff diff-prf type-name)]
            [table'' (add-inequality problem (:const diff) (:coeffs diff) proof-fn)])

          ;; And p q
          (and (= head-name (:and-name omega-names)) (= 2 (count args)))
          (let [;; And.left : And P Q → P
                left-proof (when hyp-proof
                             (e/app* (e/const' (name/from-string "And.left") [])
                                     (nth args 0) (nth args 1) hyp-proof))
                ;; And.right : And P Q → Q
                right-proof (when hyp-proof
                              (e/app* (e/const' (name/from-string "And.right") [])
                                      (nth args 0) (nth args 1) hyp-proof))
                [table' problem'] (reify-prop st table problem (nth args 0) left-proof)
                [table'' problem''] (reify-prop st table' problem' (nth args 1) right-proof)]
            [table'' problem''])

          ;; False → direct contradiction (short-circuit the solver)
          (= head-name (:false-name omega-names))
          (if hyp-proof
            ;; hyp-proof directly proves False — store it for short-circuit
            [table (assoc problem :direct-false hyp-proof)]
            ;; No proof available, add trivially unsat constraint
            [table (add-inequality problem -1 [] nil)])

          ;; True → no constraint
          (= head-name (:true-name omega-names))
          [table problem]

          ;; Ne.{u} α a b → same as Not (Eq α a b), i.e., a ≠ b
          (and (= head-name (:ne-name omega-names)) (= 3 (count args)))
          (let [eq-prop (e/app* (e/const' (:eq-name omega-names) head-levels)
                                (nth args 0) (nth args 1) (nth args 2))
                [table' negated] (negate-goal st table problem eq-prop hyp-proof)]
            (if (:disjunction negated)
              ;; Queue the disjunction for later processing
              [table' (queue-disjunction problem (:disjunction negated))]
              [table' negated]))

          ;; Or P Q → queue as disjunction for later case-splitting
          (and (= head-name (:or-name omega-names)) (= 2 (count args)))
          (if hyp-proof
            [table (queue-disjunction problem
                                      {:or-proof hyp-proof
                                       :left-type (nth args 0)
                                       :right-type (nth args 1)})]
            [table problem])

          ;; Not P → negate the inner proposition
          ;; Converts ¬(a ≤ b) → b < a, ¬(a < b) → b ≤ a, etc.
          (and (= head-name (:not-name omega-names)) (= 1 (count args)))
          (let [[table' negated] (negate-goal st table problem (nth args 0) hyp-proof)]
            (if (:disjunction negated)
              ;; Queue the disjunction for later processing
              [table' (queue-disjunction problem (:disjunction negated))]
              [table' negated]))

          ;; Dvd.dvd α inst k x → feed equality through reify-prop
          ;; Nat: Nat.div_mul_cancel h : (x / k) * k = x
          ;; Int: use emod_eq_zero_of_dvd + emod_def to get x - k*(x/k) = 0
          (and (= head-name (:dvd-name omega-names)) (= 4 (count args)))
          (let [type-arg (nth args 0)
                type-whnf (#'tc/cached-whnf st type-arg)
                type-name (when (e/const? type-whnf) (e/const-name type-whnf))
                k-arg (nth args 2)
                x-arg (nth args 3)
                k-whnf (#'tc/cached-whnf st k-arg)]
            (if (and (or (= type-name (:nat-name omega-names))
                         (= type-name (:int-name omega-names)))
                     (e/lit-nat? k-whnf)
                     (pos? (e/lit-nat-val k-whnf)))
              (if (= type-name (:nat-name omega-names))
                ;; Nat: Nat.div_mul_cancel {n m} (h : m ∣ n) : (n / m) * m = n
                ;; With n=x, m=k: (x / k) * k = x
                ;; Feed Eq Nat ((x/k)*k) x through reify-prop
                (let [nat-type (e/const' (:nat-name omega-names) [])
                      div-expr (e/app* (e/const' (:hdiv omega-names) [lvl/zero lvl/zero lvl/zero])
                                       nat-type nat-type nat-type
                                       (e/app* (e/const' (name/from-string "instHDiv") [lvl/zero])
                                               nat-type (e/const' (name/from-string "Nat.instDiv") []))
                                       x-arg k-arg)
                      mul-expr (e/app* (e/const' (:hmul omega-names) [lvl/zero lvl/zero lvl/zero])
                                       nat-type nat-type nat-type
                                       (e/app* (e/const' (name/from-string "instHMul") [lvl/zero])
                                               nat-type (e/const' (name/from-string "instMulNat") []))
                                       div-expr k-arg)
                      eq-proof (when hyp-proof
                                 (e/app* (e/const' (name/from-string "Nat.div_mul_cancel") [])
                                         x-arg k-arg hyp-proof))
                      eq-type (e/app* (e/const' (:eq-name omega-names) [u1])
                                      nat-type mul-expr x-arg)]
                  (reify-prop st table problem eq-type eq-proof))
                ;; Int: Eq.trans (Eq.symm (Int.emod_def x k)) (Int.emod_eq_zero_of_dvd k x h)
                ;; gives: x - k * (x / k) = 0
                ;; Feed Eq Int (x - k*(x/k)) 0 through reify-prop
                (let [emod-def-proof (e/app* (e/const' (name/from-string "Int.emod_def") [])
                                             x-arg k-arg)
                      emod-zero-proof (when hyp-proof
                                        (e/app* (e/const' (:int-emod-eq-zero-of-dvd omega-names) [])
                                                k-arg x-arg hyp-proof))
                      ;; emod_def : x % k = x - k * (x / k)
                      ;; emod_eq_zero : x % k = 0
                      ;; Eq.symm (emod_def) : x - k*(x/k) = x % k
                      ;; Eq.trans (Eq.symm emod_def) emod_zero : x - k*(x/k) = 0
                      int-div-expr (e/app* (e/const' (:hdiv omega-names) [lvl/zero lvl/zero lvl/zero])
                                           int-type int-type int-type
                                           (e/app* (e/const' (name/from-string "instHDiv") [lvl/zero])
                                                   int-type (e/const' (name/from-string "Int.instDiv") []))
                                           x-arg k-arg)
                      int-mul-expr (e/app* (e/const' (:hmul omega-names) [lvl/zero lvl/zero lvl/zero])
                                           int-type int-type int-type
                                           (e/app* (e/const' (name/from-string "instHMul") [lvl/zero])
                                                   int-type (e/const' (name/from-string "Int.instMul") []))
                                           k-arg int-div-expr)
                      sub-expr (e/app* (e/const' (:hsub omega-names) [lvl/zero lvl/zero lvl/zero])
                                       int-type int-type int-type
                                       (e/app* (e/const' (name/from-string "instHSub") [lvl/zero])
                                               int-type (e/const' (name/from-string "Int.instSub") []))
                                       x-arg int-mul-expr)
                      zero-int (e/app (e/const' (:int-ofnat omega-names) []) (e/lit-nat 0))
                      ;; Build Eq.trans proof
                      mod-type (e/app* (e/const' (:hmod omega-names) [lvl/zero lvl/zero lvl/zero])
                                       int-type int-type int-type
                                       (e/app* (e/const' (name/from-string "instHMod") [lvl/zero])
                                               int-type (e/const' (name/from-string "Int.instMod") []))
                                       x-arg k-arg)
                      eq-proof (when hyp-proof
                                 (e/app* (e/const' (:eq-trans omega-names) [u1])
                                         int-type sub-expr mod-type zero-int
                                         (e/app* (e/const' (:eq-symm omega-names) [u1])
                                                 int-type mod-type sub-expr
                                                 emod-def-proof)
                                         emod-zero-proof))
                      eq-type (e/app* (e/const' (:eq-name omega-names) [u1])
                                      int-type sub-expr zero-int)]
                  (reify-prop st table problem eq-type eq-proof)))
              [table problem]))

          :else
          ;; Try Iff (positive) and forall (implication) before giving up
          (let [[t p] (reify-prop-iff st table problem prop hyp-proof)]
            (if (not= p problem)
              [t p]
              (reify-prop-forall st table problem prop hyp-proof))))))))

(defn- reify-prop-forall
  "Handle forall-based propositions that try-match-head can't detect:
   - P → Q (implication): convert to ¬P ∨ Q via Decidable.not_or_of_imp
   - P ↔ Q (Iff): convert to (P ∧ Q) ∨ (¬P ∧ ¬Q) via
     Decidable.iff_iff_and_or_not_and_not"
  [st table problem prop hyp-proof]
  (let [whnf (#'tc/cached-whnf st prop)]
    (cond
      ;; Iff P Q is an application, handle it here since we need WHNF
      ;; After WHNF, Iff P Q remains as Iff P Q (it's a structure)
      ;; Actually Iff is matched by try-match-head. Check for forall (implication).
      (and (e/forall? whnf) (= :default (e/forall-info whnf)))
      ;; P → Q: convert to ¬P ∨ Q via Decidable.not_or_of_imp
      ;; Decidable.not_or_of_imp {P Q : Prop} [Decidable P] (h : P → Q) : ¬P ∨ Q
      (let [p-type (e/forall-type whnf)
            body-raw (e/forall-body whnf)
            fv-id (long (System/nanoTime))
            q-type (e/instantiate1 body-raw (e/fvar fv-id))
            ;; Check if body uses bvar 0 (dependent forall vs non-dependent arrow)
            is-dependent (pos? (e/bvar-range body-raw))]
        (if is-dependent
          ;; Dependent forall — not an implication, bail
          [table problem]
          (let [q-whnf (#'tc/cached-whnf st q-type)]
            (if (and (e/const? q-whnf) (= (e/const-name q-whnf) (:false-name omega-names)))
              ;; P → False  IS  ¬P. Route to the Not handler (negate P → lt_or_gt_of_ne / LT /
              ;; …), mirroring lean4's pushNot — NOT the generic implication path. This is how
              ;; ¬(a ≤ b) (negated goal) and ¬(a = b) (i.e. a ≠ b) get handled without
              ;; Decidable.not_or_of_imp.
              (reify-prop st table problem
                          (e/app (e/const' (:not-name omega-names) []) p-type)
                          hyp-proof)
              ;; Genuine implication P → Q (Q ≠ False): ¬P ∨ Q via Decidable.not_or_of_imp.
              (let [not-const (e/const' (:not-name omega-names) [])
                    not-p (e/app not-const p-type)
                    or-proof (when hyp-proof
                               (e/app* (e/const' (:not-or-of-imp omega-names) [])
                                       p-type q-type
                                       (e/app (e/const' (:classical-prop-dec omega-names) []) p-type)
                                       hyp-proof))]
                [table (queue-disjunction problem
                                          {:or-proof or-proof
                                           :left-type not-p
                                           :right-type q-type})])))))

      :else [table problem])))

(defn- reify-prop-iff
  "Handle positive Iff: (P ↔ Q) → (P ∧ Q) ∨ (¬P ∧ ¬Q)
   via Iff.mp Decidable.iff_iff_and_or_not_and_not"
  [st table problem prop hyp-proof]
  (let [matched (try-match-head st prop)
        [head-name _head-levels args] matched]
    (if (and matched (= head-name (:iff-name omega-names)) (= 2 (count args)))
      (let [p-arg (nth args 0) q-arg (nth args 1)
            not-const (e/const' (:not-name omega-names) [])
            not-p (e/app not-const p-arg)
            not-q (e/app not-const q-arg)
            ;; (P ∧ Q) ∨ (¬P ∧ ¬Q)
            left-type (e/app* (e/const' (:and-name omega-names) []) p-arg q-arg)
            right-type (e/app* (e/const' (:and-name omega-names) []) not-p not-q)
            ;; Decidable.iff_iff_and_or_not_and_not {P Q : Prop} [Decidable Q] :
            ;;   (P ↔ Q) ↔ ((P∧Q)∨(¬P∧¬Q))
            ;; Core carries only the Decidable form, so the instance is explicit here.
            ;; `Classical.propDecidable` is fine: the instance is consumed inside the
            ;; lemma's own proof, never under an `of_decide_eq_true` where its
            ;; noncomputability would leave `decide` stuck (see :classical-prop-dec).
            iff-prop (e/app* (e/const' (:iff-name omega-names) []) p-arg q-arg)
            or-type (e/app* (e/const' (:or-name omega-names) []) left-type right-type)
            or-proof (when hyp-proof
                       (e/app* (e/const' (:iff-mp omega-names) [])
                               iff-prop or-type
                               (e/app* (e/const' (:iff-iff-and-or omega-names) [])
                                       p-arg q-arg
                                       (e/app (e/const' (:classical-prop-dec omega-names) [])
                                              q-arg))
                               hyp-proof))]
        [table (queue-disjunction problem
                                  {:or-proof or-proof
                                   :left-type left-type
                                   :right-type right-type})])
      [table problem])))

(defn- negate-goal
  "Negate the goal and add constraints to the problem.
   hyp-proof is the proof of ¬P (from by_contra), or nil."
  [st table problem goal-type hyp-proof]
  (let [matched (try-match-head st goal-type)]
    (if-not matched
      ;; No const head — try forall (¬(P → Q))
      (negate-goal-forall st table problem goal-type hyp-proof)
      (let [[head-name head-levels args] matched]
        (cond
          ;; The negated GOAL is a relation over a carrier omega does not handle: no fact
          ;; (Lean's frontend, Frontend.lean:441-478 — `| _ => pure (p, 0)`), so the search
          ;; has nothing and reports "could not prove", instead of reifying the Real relation
          ;; as Int and handing back an ill-typed proof.
          (and (#{(:eq-name omega-names) (:le-name omega-names) (:lt-name omega-names)
                  (:ge-name omega-names) (:gt-name omega-names)
                  (:ne-name omega-names) (:dvd-name omega-names)} head-name)
               (>= (count args) 3)
               (let [t (#'tc/cached-whnf st (nth args 0))]
                 (not (and (e/const? t)
                           (#{(:nat-name omega-names) (:int-name omega-names)} (e/const-name t))))))
          [table problem]
          ;; Goal: Eq _ a b → ¬(a = b): split into a < b ∨ b < a
          (and (= head-name (:eq-name omega-names)) (= 3 (count args)))
          (let [type-arg (nth args 0)
                type-whnf (#'tc/cached-whnf st type-arg)
                type-name (when (e/const? type-whnf) (e/const-name type-whnf))
                a-arg (nth args 1) b-arg (nth args 2)
                [table' lc-a prf-a] (reify-term st table a-arg)
                [table'' lc-b prf-b] (reify-term st table' b-arg)
                ;; Branch 1: a < b → b - a - 1 ≥ 0
                one-lc (mk-lc 1)
                lc-a-plus-1 (lc-add lc-a one-lc)
                prf-a-plus-1 (mk-add-eval-proof lc-a one-lc prf-a (mk-eval-rfl-proof one-lc))
                diff-ab (lc-sub lc-b lc-a-plus-1)
                diff-prf-ab (mk-sub-eval-proof lc-b lc-a-plus-1 prf-b prf-a-plus-1)
                ;; Branch 2: b < a → a - b - 1 ≥ 0
                lc-b-plus-1 (lc-add lc-b one-lc)
                prf-b-plus-1 (mk-add-eval-proof lc-b one-lc prf-b (mk-eval-rfl-proof one-lc))
                diff-ba (lc-sub lc-a lc-b-plus-1)
                diff-prf-ba (mk-sub-eval-proof lc-a lc-b-plus-1 prf-a prf-b-plus-1)
                ;; Create fresh fvars for Or.elim branches
                left-fvar-id (long (System/nanoTime))
                right-fvar-id (long (+ 1 (System/nanoTime)))
                ;; Left type: a < b (Int) or a < b (Nat)
                left-type (if (= type-name (:nat-name omega-names))
                            (e/app* (e/const' (:lt-name omega-names) [lvl/zero])
                                    type-arg (e/const' (:inst-lt-nat omega-names) [])
                                    a-arg b-arg)
                            (e/app* (e/const' (:lt-name omega-names) [lvl/zero])
                                    int-type (e/const' (:int-inst-lt omega-names) [])
                                    a-arg b-arg))
                ;; Right type: b < a (Int) or a > b (Nat) — Nat version uses GT
                right-type (if (= type-name (:nat-name omega-names))
                             (e/app* (e/const' (:gt-name omega-names) [lvl/zero])
                                     type-arg (e/const' (:inst-lt-nat omega-names) [])
                                     a-arg b-arg)
                             (e/app* (e/const' (:lt-name omega-names) [lvl/zero])
                                     int-type (e/const' (:int-inst-lt omega-names) [])
                                     b-arg a-arg))
                left-hyp (e/fvar left-fvar-id)
                right-hyp (e/fvar right-fvar-id)
                ;; Build proof-fns using the fvar hypotheses
                left-proof-fn (mk-lt-proof-fn left-hyp a-arg b-arg
                                              diff-ab diff-prf-ab type-name)
                ;; For Int right branch: b < a; for Nat: a > b (which is b < a via gt_iff_lt)
                right-proof-fn (if (= type-name (:nat-name omega-names))
                                 ;; Nat: right is GT.gt a b, convert via gt_iff_lt to b < a
                                 ;; GT.gt.{0} for Nat, so gt_iff_lt.{0}
                                 (let [lt-inst (e/const' (:inst-lt-nat omega-names) [])
                                       gt-iff (e/app* (e/const' (:gt-iff-lt omega-names) [lvl/zero])
                                                      type-arg lt-inst a-arg b-arg)
                                       lt-proof (e/app* (e/const' (:iff-mp omega-names) [])
                                                        right-type
                                                        (e/app* (e/const' (:lt-name omega-names) [lvl/zero])
                                                                type-arg lt-inst b-arg a-arg)
                                                        gt-iff right-hyp)]
                                   (mk-lt-proof-fn lt-proof b-arg a-arg
                                                   diff-ba diff-prf-ba type-name))
                                 (mk-lt-proof-fn right-hyp b-arg a-arg
                                                 diff-ba diff-prf-ba type-name))
                ;; Build the two branch problems
                left-problem (add-inequality problem (:const diff-ab) (:coeffs diff-ab) left-proof-fn)
                right-problem (add-inequality problem (:const diff-ba) (:coeffs diff-ba) right-proof-fn)
                ;; Build the Or proof from hyp-proof (¬(a = b))
                ;; Int: Int.lt_or_gt_of_ne {a} {b} h : a < b ∨ b < a
                ;; Nat: Nat.lt_or_gt_of_ne {a} {b} h : a < b ∨ a > b
                or-proof-name (if (= type-name (:nat-name omega-names))
                                (:nat-lt-or-gt-of-ne omega-names)
                                (:int-lt-or-gt-of-ne omega-names))
                or-proof-fn (when hyp-proof
                              (e/app* (e/const' or-proof-name [])
                                      a-arg b-arg hyp-proof))]
            [table'' {:disjunction
                      {:branches [left-problem right-problem]
                       :left-type left-type :right-type right-type
                       :left-fvar-id left-fvar-id :right-fvar-id right-fvar-id
                       :or-proof or-proof-fn}}])

          ;; Goal: LE.le _ _ a b → ¬(a ≤ b): means b < a, i.e., a - b ≥ 1
          ;; pushNot: Nat.lt_of_not_le h : b < a
          (and (= head-name (:le-name omega-names)) (= 4 (count args)))
          (let [type-arg (nth args 0)
                type-whnf (#'tc/cached-whnf st type-arg)
                type-name (when (e/const? type-whnf) (e/const-name type-whnf))
                a-arg (nth args 2) b-arg (nth args 3)
                ;; ¬(a ≤ b) → b < a
                pushed-proof (when hyp-proof
                               (if (= type-name (:nat-name omega-names))
                                 (e/app* (e/const' (:nat-lt-of-not-le omega-names) [])
                                         a-arg b-arg hyp-proof)
                                 ;; Int: Iff.mp (Int.not_le a b) hyp : b < a
                                 (let [not-le-iff (e/app* (e/const' (:int-not-le omega-names) [])
                                                          a-arg b-arg)
                                       not-prop (e/app (e/const' (:not-name omega-names) [])
                                                       (e/app* (e/const' (:le-name omega-names) [lvl/zero])
                                                               int-type (e/const' (:int-inst-le omega-names) [])
                                                               a-arg b-arg))
                                       lt-prop (e/app* (e/const' (:lt-name omega-names) [lvl/zero])
                                                       int-type (e/const' (:int-inst-lt omega-names) [])
                                                       b-arg a-arg)]
                                   (e/app* (e/const' (:iff-mp omega-names) [])
                                           not-prop lt-prop not-le-iff hyp-proof))))
                [table' lc-a prf-a] (reify-term st table a-arg)
                [table'' lc-b prf-b] (reify-term st table' b-arg)
                ;; b < a means b+1 ≤ a, constraint: a - (b+1) ≥ 0
                one-lc (mk-lc 1)
                lc-b-plus-1 (lc-add lc-b one-lc)
                prf-b-plus-1 (mk-add-eval-proof lc-b one-lc prf-b (mk-eval-rfl-proof one-lc))
                diff (lc-sub lc-a lc-b-plus-1)
                diff-prf (mk-sub-eval-proof lc-a lc-b-plus-1 prf-a prf-b-plus-1)
                proof-fn (mk-lt-proof-fn pushed-proof b-arg a-arg diff diff-prf type-name)]
            [table'' (add-inequality problem (:const diff) (:coeffs diff) proof-fn)])

          ;; Goal: LT.lt _ _ a b → ¬(a < b): means b ≤ a
          ;; pushNot: Nat.le_of_not_lt h : b ≤ a
          (and (= head-name (:lt-name omega-names)) (= 4 (count args)))
          (let [type-arg (nth args 0)
                type-whnf (#'tc/cached-whnf st type-arg)
                type-name (when (e/const? type-whnf) (e/const-name type-whnf))
                a-arg (nth args 2) b-arg (nth args 3)
                pushed-proof (when hyp-proof
                               (if (= type-name (:nat-name omega-names))
                                 (e/app* (e/const' (:nat-le-of-not-lt omega-names) [])
                                         a-arg b-arg hyp-proof)
                                 ;; Int: Iff.mp (Int.not_lt a b) hyp : b ≤ a
                                 (let [not-lt-iff (e/app* (e/const' (:int-not-lt omega-names) [])
                                                          a-arg b-arg)
                                       not-prop (e/app (e/const' (:not-name omega-names) [])
                                                       (e/app* (e/const' (:lt-name omega-names) [lvl/zero])
                                                               int-type (e/const' (:int-inst-lt omega-names) [])
                                                               a-arg b-arg))
                                       le-prop (e/app* (e/const' (:le-name omega-names) [lvl/zero])
                                                       int-type (e/const' (:int-inst-le omega-names) [])
                                                       b-arg a-arg)]
                                   (e/app* (e/const' (:iff-mp omega-names) [])
                                           not-prop le-prop not-lt-iff hyp-proof))))
                [table' lc-a prf-a] (reify-term st table a-arg)
                [table'' lc-b prf-b] (reify-term st table' b-arg)
                ;; b ≤ a gives a - b ≥ 0
                diff (lc-sub lc-a lc-b)
                diff-prf (mk-sub-eval-proof lc-a lc-b prf-a prf-b)
                proof-fn (mk-ineq-proof-fn pushed-proof b-arg a-arg diff diff-prf type-name)]
            [table'' (add-inequality problem (:const diff) (:coeffs diff) proof-fn)])

          ;; Goal: GE.ge α inst a b → ¬(a ≥ b): means b > a, i.e., a < b
          ;; ¬(a ≥ b) → ¬(b ≤ a) → a < b via Int.lt_of_not_le / Nat.lt_of_not_le
          (and (= head-name (:ge-name omega-names)) (= 4 (count args)))
          (let [type-arg (nth args 0)
                type-whnf (#'tc/cached-whnf st type-arg)
                type-name (when (e/const? type-whnf) (e/const-name type-whnf))
                ge-a (nth args 2) ge-b (nth args 3)
                ;; ¬(a ≥ b) is definitionally ¬(b ≤ a)
                ;; Nat.lt_of_not_le : ¬(b ≤ a) → a < b
                ;; Int.lt_of_not_le : ¬(a ≤ b) → b < a  (swapped args)
                pushed-proof (when hyp-proof
                               (if (= type-name (:nat-name omega-names))
                                 ;; Nat: ¬(b ≤ a) → a < b (Nat.lt_of_not_le)
                                 (e/app* (e/const' (:nat-lt-of-not-le omega-names) [])
                                         ge-b ge-a hyp-proof)
                                 ;; Int: ¬(b ≤ a) → a < b via Iff.mp (Int.not_le b a)
                                 (let [not-le-iff (e/app* (e/const' (:int-not-le omega-names) [])
                                                          ge-b ge-a)
                                       not-prop (e/app (e/const' (:not-name omega-names) [])
                                                       (e/app* (e/const' (:le-name omega-names) [lvl/zero])
                                                               int-type (e/const' (:int-inst-le omega-names) [])
                                                               ge-b ge-a))
                                       lt-prop (e/app* (e/const' (:lt-name omega-names) [lvl/zero])
                                                       int-type (e/const' (:int-inst-lt omega-names) [])
                                                       ge-a ge-b)]
                                   (e/app* (e/const' (:iff-mp omega-names) [])
                                           not-prop lt-prop not-le-iff hyp-proof))))
                [table' lc-a prf-a] (reify-term st table ge-a)
                [table'' lc-b prf-b] (reify-term st table' ge-b)
                ;; a < b → b - a - 1 ≥ 0
                one-lc (mk-lc 1)
                lc-a-plus-1 (lc-add lc-a one-lc)
                prf-a-plus-1 (mk-add-eval-proof lc-a one-lc prf-a (mk-eval-rfl-proof one-lc))
                diff (lc-sub lc-b lc-a-plus-1)
                diff-prf (mk-sub-eval-proof lc-b lc-a-plus-1 prf-b prf-a-plus-1)
                proof-fn (mk-lt-proof-fn pushed-proof ge-a ge-b diff diff-prf type-name)]
            [table'' (add-inequality problem (:const diff) (:coeffs diff) proof-fn)])

          ;; Goal: GT.gt α inst a b → ¬(a > b): means a ≤ b
          ;; ¬(a > b) → ¬(b < a) → a ≤ b via Int.le_of_not_lt / Nat.le_of_not_lt
          (and (= head-name (:gt-name omega-names)) (= 4 (count args)))
          (let [type-arg (nth args 0)
                type-whnf (#'tc/cached-whnf st type-arg)
                type-name (when (e/const? type-whnf) (e/const-name type-whnf))
                gt-a (nth args 2) gt-b (nth args 3)
                ;; ¬(a > b) is definitionally ¬(b < a)
                ;; Nat.le_of_not_lt : ¬(b < a) → a ≤ b
                ;; Int.le_of_not_lt : ¬(a < b) → b ≤ a  (check arg order)
                pushed-proof (when hyp-proof
                               (if (= type-name (:nat-name omega-names))
                                 (e/app* (e/const' (:nat-le-of-not-lt omega-names) [])
                                         gt-b gt-a hyp-proof)
                                 ;; Int: ¬(b < a) → a ≤ b via Iff.mp (Int.not_lt b a)
                                 (let [not-lt-iff (e/app* (e/const' (:int-not-lt omega-names) [])
                                                          gt-b gt-a)
                                       not-prop (e/app (e/const' (:not-name omega-names) [])
                                                       (e/app* (e/const' (:lt-name omega-names) [lvl/zero])
                                                               int-type (e/const' (:int-inst-lt omega-names) [])
                                                               gt-b gt-a))
                                       le-prop (e/app* (e/const' (:le-name omega-names) [lvl/zero])
                                                       int-type (e/const' (:int-inst-le omega-names) [])
                                                       gt-a gt-b)]
                                   (e/app* (e/const' (:iff-mp omega-names) [])
                                           not-prop le-prop not-lt-iff hyp-proof))))
                [table' lc-a prf-a] (reify-term st table gt-a)
                [table'' lc-b prf-b] (reify-term st table' gt-b)
                ;; a ≤ b → b - a ≥ 0
                diff (lc-sub lc-b lc-a)
                diff-prf (mk-sub-eval-proof lc-b lc-a prf-b prf-a)
                proof-fn (mk-ineq-proof-fn pushed-proof gt-a gt-b diff diff-prf type-name)]
            [table'' (add-inequality problem (:const diff) (:coeffs diff) proof-fn)])

          ;; Goal: And P Q → ¬(P ∧ Q): split into ¬P ∨ ¬Q via
          ;; Classical.not_and_iff_not_or_not
          (and (= head-name (:and-name omega-names)) (= 2 (count args)))
          (let [p-arg (nth args 0) q-arg (nth args 1)
                not-const (e/const' (:not-name omega-names) [])
                ;; ¬P and ¬Q types (Not constant, matching the lemma's statement)
                not-p (e/app not-const p-arg)
                not-q (e/app not-const q-arg)
                ;; Iff.mp (@Classical.not_and_iff_not_or_not P Q) hyp-proof : ¬P ∨ ¬Q
                ;; (implicit {a b : Prop} only — no Decidable argument)
                and-pq (e/app* (e/const' (:and-name omega-names) []) p-arg q-arg)
                neg-and (e/app not-const and-pq)
                or-neg (e/app* (e/const' (:or-name omega-names) []) not-p not-q)
                or-proof (when hyp-proof
                           (e/app* (e/const' (:iff-mp omega-names) [])
                                   neg-and or-neg
                                   (e/app* (e/const' (:not-and-or omega-names) [])
                                           p-arg q-arg)
                                   hyp-proof))
                ;; Create fvars for Or.elim branches
                left-fvar-id (long (System/nanoTime))
                right-fvar-id (long (+ 1 (System/nanoTime)))
                left-hyp (e/fvar left-fvar-id)
                right-hyp (e/fvar right-fvar-id)
                ;; Each branch: negate the inner prop with the ¬P / ¬Q proof
                [table' left-result] (negate-goal st table problem p-arg left-hyp)
                [table'' right-result] (negate-goal st table' problem q-arg right-hyp)]
            ;; If either branch produces a nested disjunction, bail out
            (if (or (:disjunction left-result) (:disjunction right-result))
              [table problem]  ;; fall through to decide
              [table'' {:disjunction
                        {:branches [left-result right-result]
                         :left-type not-p :right-type not-q
                         :left-fvar-id left-fvar-id :right-fvar-id right-fvar-id
                         :or-proof or-proof}}]))

          ;; Goal: Or P Q → ¬(P ∨ Q): gives ¬P ∧ ¬Q, then negate both
          (and (= head-name (:or-name omega-names)) (= 2 (count args)))
          (let [p-arg (nth args 0) q-arg (nth args 1)
                not-const (e/const' (:not-name omega-names) [])
                not-p (e/app not-const p-arg)
                not-q (e/app not-const q-arg)
                ;; Iff.mp (@not_or P Q) hyp-proof : And (Not P) (Not Q)
                neg-or (e/app not-const (e/app* (e/const' (:or-name omega-names) []) p-arg q-arg))
                and-neg (e/app* (e/const' (:and-name omega-names) []) not-p not-q)
                and-proof (when hyp-proof
                            (e/app* (e/const' (:iff-mp omega-names) [])
                                    neg-or and-neg
                                    (e/app* (e/const' (:not-or omega-names) [])
                                            p-arg q-arg)
                                    hyp-proof))
                ;; Split into ¬P and ¬Q, then negate each
                left-proof (when and-proof
                             (e/app* (e/const' (:and-left omega-names) [])
                                     not-p not-q and-proof))
                right-proof (when and-proof
                              (e/app* (e/const' (:and-right omega-names) [])
                                      not-p not-q and-proof))
                [table' problem'] (negate-goal st table problem p-arg left-proof)
                [table'' problem''] (negate-goal st table' problem' q-arg right-proof)]
            ;; If either returns a disjunction, bail out
            (if (or (:disjunction problem') (:disjunction problem''))
              [table problem]
              [table'' problem'']))

          ;; Goal: Iff P Q → ¬(P ↔ Q): convert to (¬P ↔ Q) via Decidable.not_iff
          ;; then feed as positive Iff hypothesis.
          ;; Decidable.not_iff : {b : Prop} → {a : Prop} → [Decidable b] →
          ;;                     (¬(a ↔ b) ↔ (¬a ↔ b))
          ;; so applied as `@Decidable.not_iff Q P (inst : Decidable Q)` — note the
          ;; instance is on the SECOND-applied proposition (`b`, i.e. Q), not on P.
          ;; This used to pass `Decidable P` and had never been caught, because
          ;; `Decidable.not_iff` was absent from the previous bundled store and this
          ;; whole branch died at constant lookup before the kernel could object.
          (and (= head-name (:iff-name omega-names)) (= 2 (count args)))
          (let [p-arg (nth args 0) q-arg (nth args 1)
                not-const (e/const' (:not-name omega-names) [])
                ;; Build: Iff.mp (Decidable.not_iff Q P [dec P]) hyp : ¬P ↔ Q
                iff-pq (e/app* (e/const' (:iff-name omega-names) []) p-arg q-arg)
                neg-iff (e/app not-const iff-pq)
                not-p (e/app not-const p-arg)
                not-p-iff-q (e/app* (e/const' (:iff-name omega-names) []) not-p q-arg)
                not-p-iff-q-proof (when hyp-proof
                                    (e/app* (e/const' (:iff-mp omega-names) [])
                                            neg-iff not-p-iff-q
                                            (e/app* (e/const' (:dec-not-iff omega-names) [])
                                                    q-arg p-arg
                                                    (e/app (e/const' (:classical-prop-dec omega-names) []) q-arg))
                                            hyp-proof))]
            ;; Feed (¬P ↔ Q) as a positive Iff through reify-prop-iff
            (reify-prop-iff st table problem not-p-iff-q not-p-iff-q-proof))

          ;; Goal: Dvd.dvd α inst k x → ¬(k ∣ x)
          ;; For Nat: Nat.emod_pos_of_not_dvd h : 0 < x % k
          ;; For Int: Int.emod_pos_of_not_dvd h : k = 0 ∨ 0 < x % k
          (and (= head-name (:dvd-name omega-names)) (= 4 (count args)))
          (let [type-arg (nth args 0)
                type-whnf (#'tc/cached-whnf st type-arg)
                type-name (when (e/const? type-whnf) (e/const-name type-whnf))
                k-arg (nth args 2) x-arg (nth args 3)]
            (cond
              (= type-name (:nat-name omega-names))
              ;; Nat.emod_pos_of_not_dvd k x h : 0 < x % k
              ;; This is LT.lt Nat instLTNat 0 (HMod.hMod ... x k)
              (let [pushed-proof (when hyp-proof
                                   (e/app* (e/const' (:nat-emod-pos-of-not-dvd omega-names) [])
                                           k-arg x-arg hyp-proof))]
                ;; Feed as LT hypothesis: 0 < x % k
                (reify-prop st table problem
                            (e/app* (e/const' (:lt-name omega-names) [lvl/zero])
                                    type-arg (e/const' (:inst-lt-nat omega-names) [])
                                    (e/lit-nat 0)
                                    (e/app* (e/const' (:hmod omega-names) [lvl/zero lvl/zero lvl/zero])
                                            type-arg type-arg type-arg
                                            (e/app* (e/const' (name/from-string "instHMod") [lvl/zero])
                                                    type-arg (e/const' (name/from-string "Nat.instMod") []))
                                            x-arg k-arg))
                            pushed-proof))

              (= type-name (:int-name omega-names))
              ;; Int.emod_pos_of_not_dvd k x h : k = 0 ∨ 0 < x % k (disjunction)
              (let [pushed-proof (when hyp-proof
                                   (e/app* (e/const' (:int-emod-pos-of-not-dvd omega-names) [])
                                           k-arg x-arg hyp-proof))
                    zero-int (e/app (e/const' (:int-ofnat omega-names) []) (e/lit-nat 0))
                    left-type (e/app* (e/const' (:eq-name omega-names) [(lvl/succ lvl/zero)])
                                      int-type k-arg zero-int)
                    mod-expr (e/app* (e/const' (:hmod omega-names) [lvl/zero lvl/zero lvl/zero])
                                     int-type int-type int-type
                                     (e/app* (e/const' (name/from-string "instHMod") [lvl/zero])
                                             int-type (e/const' (name/from-string "Int.instMod") []))
                                     x-arg k-arg)
                    right-type (e/app* (e/const' (:lt-name omega-names) [lvl/zero])
                                       int-type (e/const' (:int-inst-lt omega-names) [])
                                       zero-int mod-expr)
                    left-fvar-id (long (System/nanoTime))
                    right-fvar-id (long (+ 1 (System/nanoTime)))
                    left-hyp (e/fvar left-fvar-id)
                    right-hyp (e/fvar right-fvar-id)
                    [table' left-problem'] (reify-prop st table problem left-type left-hyp)
                    [table'' right-problem'] (reify-prop st table' problem right-type right-hyp)]
                (if (or (:disjunction left-problem') (:disjunction right-problem'))
                  [table problem]
                  [table'' {:disjunction
                            {:branches [left-problem' right-problem']
                             :left-type left-type :right-type right-type
                             :left-fvar-id left-fvar-id :right-fvar-id right-fvar-id
                             :or-proof pushed-proof}}]))

              :else [table problem]))

          ;; Goal: Not P → assume P (hyp-proof proves ¬(¬P), i.e. P)
          (and (= head-name (:not-name omega-names)) (= 1 (count args)))
          (let [;; ¬(¬P) → P via Decidable.of_not_not
                inner-proof (when hyp-proof
                              (e/app* (e/const' (name/from-string "Decidable.of_not_not") [])
                                      (nth args 0)
                                      (e/app (e/const' (:classical-prop-dec omega-names) [])
                                             (nth args 0))
                                      hyp-proof))]
            (reify-prop st table problem (nth args 0) inner-proof))

          ;; Goal: False → no negation needed
          (= head-name (:false-name omega-names))
          [table problem]

          :else
          ;; Check for forall (¬(P → Q)) — try-match-head won't detect foralls
          (negate-goal-forall st table problem goal-type hyp-proof))))))

(defn- negate-goal-forall
  "Handle negation of forall-based goals that try-match-head can't detect:
   ¬(P → Q) → P ∧ ¬Q via Classical.not_imp"
  [st table problem goal-type hyp-proof]
  (let [whnf (#'tc/cached-whnf st goal-type)]
    (if (and (e/forall? whnf) (= :default (e/forall-info whnf)))
      ;; P → Q where P is the domain
      (let [p-type (e/forall-type whnf)
            body-raw (e/forall-body whnf)
            fv-id (long (System/nanoTime))
            q-type (e/instantiate1 body-raw (e/fvar fv-id))
            ;; Check if body uses bvar 0 (dependent forall vs non-dependent arrow)
            ;; A non-dependent arrow P → Q has body with bvar-range = 0 (no loose bvars after
            ;; stripping outer foralls replaced bvars with fvars). Only bvar 0 refers to
            ;; the forall's own bound var.
            is-dependent (pos? (e/bvar-range body-raw))]
        (if is-dependent
          ;; Dependent forall — not an implication, bail
          [table problem]
          ;; ¬(P → Q): gives P ∧ ¬Q via Iff.mp Classical.not_imp
          ;; Classical.not_imp {P Q : Prop} : ¬(P → Q) ↔ (P ∧ ¬Q) — no Decidable needed
          (let [not-const (e/const' (:not-name omega-names) [])
                not-q (e/app not-const q-type)
                imp-prop (e/forall' "_" p-type (e/abstract1 q-type fv-id) :default)
                neg-imp (e/app not-const imp-prop)
                and-type (e/app* (e/const' (:and-name omega-names) []) p-type not-q)
                ;; Iff.mp (Classical.not_imp) hyp : P ∧ ¬Q
                and-proof (when hyp-proof
                            (e/app* (e/const' (:iff-mp omega-names) [])
                                    neg-imp and-type
                                    (e/app* (e/const' (:not-imp omega-names) [])
                                            p-type q-type)
                                    hyp-proof))
                ;; Extract P and ¬Q from the conjunction
                p-proof (when and-proof
                          (e/app* (e/const' (:and-left omega-names) [])
                                  p-type not-q and-proof))
                nq-proof (when and-proof
                           (e/app* (e/const' (:and-right omega-names) [])
                                   p-type not-q and-proof))
                ;; Reify P as positive hypothesis, negate Q
                [table' problem'] (reify-prop st table problem p-type p-proof)
                [table'' problem''] (negate-goal st table' problem' q-type nq-proof)]
            (if (:disjunction problem'')
              [table problem]  ;; bail if nested disjunction
              [table'' problem'']))))
      ;; Not a forall
      [table problem])))

(defn- collect-hypotheses
  "Queue only proposition binders, as Frontend.omegaTactic/getLocalHyps does."
  [st table problem lctx]
  [table
   (reduce (fn [problem [id decl]]
             (if (and (= :local (:tag decl)) (#'tc/is-prop? st (:type decl)))
               (update problem :facts (fnil conj []) {:type (:type decl) :proof (e/fvar id)})
               problem))
           problem lctx)])

(defn- analyze-nonnegativity
  "Drain proof facts returned by OmegaM.lookup, preserving the branch snapshot."
  [st table problem]
  [(dissoc table :new-facts)
   (update problem :facts (fnil into [])
           (map (fn [h] {:type (tc/infer-type st h) :proof h}) (:new-facts table)))])

(defn- enqueue-fact [st table problem type proof]
  (let [actual (tc/infer-type st proof)]
    (when-not (tc/is-def-eq st actual type)
      (throw (ex-info "omega: atom analysis produced a fact of the wrong type"
                      {:kind :omega-implementation-error :operation :analyze-atom
                       :fact proof :expected type :actual actual})))
    [table (update problem :facts (fnil conj []) {:type type :proof proof})]))

(defn- add-div-bounds
  "OmegaM.analyzeAtom: enqueue proof facts for supported division and remainder.
   Applicability is established when tagging atoms: Nat ground zero/positive,
   Int positive only. Other divisors remain opaque; construction errors escape."
  [st table problem]
  (letfn
   [(add-mod-one [[table problem] [_idx {:keys [a b]}]]
      (let [nat-type (e/const' (:nat-name omega-names) [])
              hbin (fn [op inst x y]
                     (e/app* (e/const' (op omega-names) [lvl/zero lvl/zero lvl/zero])
                             nat-type nat-type nat-type
                             (e/app* (e/const' (name/from-string inst) [lvl/zero])
                                     nat-type (e/const' (name/from-string
                                                         (case inst
                                                           "instHMod" "Nat.instMod"
                                                           "instHMul" "instMulNat"
                                                           "instHAdd" "instAddNat")) []))
                             x y))
              mod-expr (hbin :hmod "instHMod" a b)
              div-expr (mk-hdiv-expr st nat-type nat-type nat-type a b)
              k-whnf (#'tc/cached-whnf st b)
              zero-divisor? (and (e/lit-nat? k-whnf) (zero? (e/lit-nat-val k-whnf)))
              ;; k = 0 : Nat.mod_zero a  : a % 0 = a
              ;;         (Nat.mod_add_div would state `a % 0 + 0 * (a / 0) = a`, whose
              ;;          `0 * (a / 0)` is STUCK — Nat.mul recurses on its second argument —
              ;;          so its eval proof cannot be bridged.)
              ;; k > 0 : Nat.mod_add_div a k : a % k + k * (a / k) = a
              eq-type (e/app* (e/const' (:eq-name omega-names) [u1])
                              nat-type
                              (if zero-divisor?
                                mod-expr
                                (hbin :hadd "instHAdd" mod-expr (hbin :hmul "instHMul" b div-expr)))
                              a)
              eq-proof (if zero-divisor?
                         (e/app (e/const' (:nat-mod-zero omega-names) []) a)
                         (e/app* (e/const' (:nat-mod-add-div omega-names) []) a b))]
          (enqueue-fact st table problem eq-type eq-proof)))
    (add-one [[table problem] [idx {:keys [a b type-name expr]}]]
      ;; Mark FIRST: reifying the bounds can itself intern atoms, and a re-entrant
      ;; visit of the same index would duplicate the constraints.
      (let [table (update table :div-bounds-added (fnil conj #{}) idx)
            carrier (#'tc/cached-whnf st (tc/infer-type st expr))
            k (if (= type-name (:nat-name omega-names))
                (ground-nat-val (#'tc/cached-whnf st b))
                (ground-int-val (#'tc/cached-whnf st b)))]
        (if-not (and (e/const? carrier)
                     (#{(:nat-name omega-names) (:int-name omega-names)} (e/const-name carrier))
                     k (pos? k))
          [table problem]
        (let [nat-type (e/const' (:nat-name omega-names) [])]
            (if (= type-name (:nat-name omega-names))
           ;; Nat: Nat.div_mul_le_self m n : m / n * n ≤ m
           ;; This is LE.le Nat instLENat (HMul ... (HDiv ... a b) b) a
              (let [div-mul (e/app* (e/const' (:hmul omega-names) [lvl/zero lvl/zero lvl/zero])
                                    nat-type nat-type nat-type
                                    (e/app* (e/const' (name/from-string "instHMul") [lvl/zero])
                                            nat-type (e/const' (name/from-string "instMulNat") []))
                                    expr b)
                    le-type (e/app* (e/const' (:le-name omega-names) [lvl/zero])
                                    nat-type (e/const' (:inst-le-nat omega-names) [])
                                    div-mul a)
                    le-proof (e/app* (e/const' (:nat-div-mul-le-self omega-names) []) a b)
                    [table' problem'] (enqueue-fact st table problem le-type le-proof)
                 ;; Also add the upper bound `a % k < k` via Nat.mod_lt. Reifying it interns
                 ;; the remainder atom r, which `add-mod-one` then ties to a and q with
                 ;; Nat.mod_add_div — together they say `a < k*q + k`.
                    mod-expr (e/app* (e/const' (:hmod omega-names) [lvl/zero lvl/zero lvl/zero])
                                     nat-type nat-type nat-type
                                     (e/app* (e/const' (name/from-string "instHMod") [lvl/zero])
                                             nat-type (e/const' (name/from-string "Nat.instMod") []))
                                     a b)
                    lt-type (e/app* (e/const' (:lt-name omega-names) [lvl/zero])
                                    nat-type (e/const' (:inst-lt-nat omega-names) [])
                                    mod-expr b)
                 ;; Proof: Nat.mod_lt a (pos : 0 < k).
                 ;; `k` is a literal here, so `0 < k` is proved by kernel evaluation:
                 ;;   of_decide_eq_true (0 < k) (Nat.decLt 0 k) (Eq.refl Bool Bool.true)
                 ;; The instance MUST be the computable `Nat.decLt` — with
                 ;; `Classical.propDecidable` the `decide` application is stuck on the
                 ;; `Classical.choice` axiom, never reduces to `Bool.true`, and the
                 ;; kernel rejects the `Eq.refl` (see :classical-prop-dec above).
                    pos-prop (e/app* (e/const' (:lt-name omega-names) [lvl/zero])
                                     nat-type (e/const' (:inst-lt-nat omega-names) [])
                                     (e/lit-nat 0) b)
                    pos-dec (e/app* (e/const' (:nat-dec-lt omega-names) []) (e/lit-nat 0) b)
                    pos-refl (e/app* (e/const' (:eq-refl omega-names) [(lvl/succ lvl/zero)])
                                     (e/const' (:bool-name omega-names) [])
                                     (e/const' (:bool-true omega-names) []))
                    pos-proof (e/app* (e/const' (:of-decide-eq-true omega-names) [])
                                      pos-prop pos-dec pos-refl)
                    lt-proof (e/app* (e/const' (:nat-mod-lt omega-names) []) a b pos-proof)]
                (enqueue-fact st table' problem' lt-type lt-proof))
           ;; Int: feed bounds through reify-prop
           ;; Int.mul_ediv_self_le {x k} (h : k ≠ 0) : k*(x/k) ≤ x
           ;; Int.lt_mul_ediv_self_add {x k} (h : 0 < k) : x < k*(x/k)+k
              (let [;; Use the divisor EXACTLY as the goal spells it. `reify-div-atom` only
                    ;; tags an atom when `ground-int-val b` is a positive literal, so `b` is
                    ;; ground here — but it may be `Int.ofNat 2`, `@OfNat.ofNat Int 2 _`, …,
                    ;; and only the goal's own spelling keeps `k * expr` reifying against the
                    ;; same atom as `expr`. The previous `(e/lit-nat-val k-whnf)` assumed a
                    ;; RAW Nat literal, which an Int divisor never is: it returned nil, the
                    k-int b
                 ;; ne-proof and pos-proof for the two side conditions, via decide
                    ne-zero-prop (e/app* (e/const' (:ne-name omega-names) [u1])
                                         int-type k-int
                                         (e/app (e/const' (:int-ofnat omega-names) []) (e/lit-nat 0)))
                 ;; Use of_decide_eq_true for ground propositions — again with a
                 ;; COMPUTABLE instance: Ne x y ≡ ¬(x = y), so
                 ;; instDecidableNot (Int.decEq k 0) : Decidable (k ≠ 0).
                    ne-dec (e/app* (e/const' (name/from-string "instDecidableNot") [])
                                   (e/app* (e/const' (:eq-name omega-names) [u1])
                                           int-type k-int
                                           (e/app (e/const' (:int-ofnat omega-names) []) (e/lit-nat 0)))
                                   (e/app* (e/const' (name/from-string "Int.decEq") [])
                                           k-int
                                           (e/app (e/const' (:int-ofnat omega-names) []) (e/lit-nat 0))))
                    ne-refl (e/app* (e/const' (:eq-refl omega-names) [(lvl/succ lvl/zero)])
                                    (e/const' (:bool-name omega-names) [])
                                    (e/const' (:bool-true omega-names) []))
                    ne-proof (e/app* (e/const' (:of-decide-eq-true omega-names) [])
                                     ne-zero-prop ne-dec ne-refl)
                 ;; k*(x/k) ≤ x
                    mul-div (e/app* (e/const' (:hmul omega-names) [lvl/zero lvl/zero lvl/zero])
                                    int-type int-type int-type
                                    (e/app* (e/const' (name/from-string "instHMul") [lvl/zero])
                                            int-type (e/const' (name/from-string "Int.instMul") []))
                                    k-int expr)
                    le-type (e/app* (e/const' (:le-name omega-names) [lvl/zero])
                                    int-type (e/const' (:int-inst-le omega-names) [])
                                    mul-div a)
                    le-proof (e/app* (e/const' (:int-mul-ediv-self-le omega-names) [])
                                     a k-int ne-proof)
                    [table' problem'] (enqueue-fact st table problem le-type le-proof)
                 ;; x < k*(x/k) + k
                    pos-prop (e/app* (e/const' (:lt-name omega-names) [lvl/zero])
                                     int-type (e/const' (:int-inst-lt omega-names) [])
                                     (e/app (e/const' (:int-ofnat omega-names) []) (e/lit-nat 0)) k-int)
                    pos-dec (e/app* (e/const' (name/from-string "Int.decLt") [])
                                    (e/app (e/const' (:int-ofnat omega-names) []) (e/lit-nat 0))
                                    k-int)
                    pos-proof (e/app* (e/const' (:of-decide-eq-true omega-names) [])
                                      pos-prop pos-dec ne-refl)
                    mul-div-plus-k (e/app* (e/const' (:hadd omega-names) [lvl/zero lvl/zero lvl/zero])
                                           int-type int-type int-type
                                           (e/app* (e/const' (name/from-string "instHAdd") [lvl/zero])
                                                   int-type (e/const' (name/from-string "Int.instAdd") []))
                                           mul-div k-int)
                    lt-type (e/app* (e/const' (:lt-name omega-names) [lvl/zero])
                                    int-type (e/const' (:int-inst-lt omega-names) [])
                                    a mul-div-plus-k)
                    lt-proof (e/app* (e/const' (:int-lt-mul-ediv-self-add omega-names) [])
                                     a k-int pos-proof)]
                (enqueue-fact st table' problem' lt-type lt-proof)))))))]
    (let [div-pending (remove (fn [[idx _]] (contains? (:div-bounds-added table) idx))
                              (:div-atoms table))
          mod-pending (remove (fn [[idx _]] (contains? (:mod-bounds-added table) idx))
                              (:mod-atoms table))
          table (reduce (fn [t [idx _]]
                          (update t :mod-bounds-added (fnil conj #{}) idx))
                        table mod-pending)
          [table problem] (reduce add-one [table problem] div-pending)]
      (reduce add-mod-one [table problem] mod-pending))))

(defn mk-meta-problem
  "Frontend.MetaProblem, separate from the core arithmetic Problem.
   The reifier's legacy flat return is unpacked only at this boundary."
  [p]
  {:problem (dissoc p :facts :disjunctions :processedFacts)
   :facts (vec (:facts p)) :disjunctions (vec (:disjunctions p))
   :processedFacts (or (:processedFacts p) #{})})

(defn- reifier-problem [m]
  (assoc (:problem m) :disjunctions (:disjunctions m)))

(defn add-fact
  "Frontend.addFact: unsupported propositions add zero facts; inference faults escape."
  [st table m {:keys [type proof]}]
  (let [p (reifier-problem m)
        [table p'] (reify-prop st table p type proof)
        n (+ (if (and (:direct-false p') (not (:direct-false p))) 1 0)
             (- (count (:assumptions p')) (count (:assumptions p)))
             (- (count (:disjunctions p')) (count (:disjunctions p))))]
    [table (assoc m :problem (dissoc p' :disjunctions) :disjunctions (vec (:disjunctions p'))) n]))

(defn process-facts
  "Frontend.processFacts: pop, mark, add, prepend generated proof facts.
   Atom analysis is once per index; new atoms feed the same queue without a sweep cap."
  [st table m]
  (loop [table table m m n 0]
    (om/charge!)
    (if-not (:possible (:problem m))
      [table m n]
      (if-let [fact (peek (:facts m))]
        (let [m (update m :facts pop) h (:proof fact)]
          (if (contains? (:processedFacts m) h)
            (recur table m n)
            (let [[table m k] (add-fact st table (update m :processedFacts conj h) fact)]
              (recur table m (+ n k)))))
        (let [[table' p] (analyze-nonnegativity st table (reifier-problem m))
              [table' p] (add-div-bounds st table' p)
              [table' p] (add-nat-sub-dichotomies table' p)
              [table' p] (add-minmax-dichotomies table' p)
              m' (assoc (mk-meta-problem p) :processedFacts (:processedFacts m))]
          (if (seq (:facts m'))
            (recur table' m' n)
            [table' m' n]))))))

(declare omega-impl)

(defn split-disjunction
  "Frontend.splitDisjunction: both alternatives start from the parent snapshots.
   Each continuation owns its atom list and local context for reconstruction."
  [st table problem depth]
  (loop [disjs (:disjunctions problem)]
    (when-let [{:keys [or-proof left-type right-type nat-sub-info] :as disj} (first disjs)]
      (om/charge!)
      (let [remaining (vec (rest disjs))
            parent (assoc problem :disjunctions remaining)
            left-id (or (:left-fvar-id disj) (long (System/nanoTime)))
            right-id (or (:right-fvar-id disj) (long (inc (System/nanoTime))))
            branch (fn [id type side]
                     (let [h (e/fvar id)
                           st' (tc/attach-lctx st (red/lctx-add-local (:lctx st) id "h" type))
                           [table' problem' n] (add-fact st' table parent {:type type :proof h})
                           [table' problem'] (if nat-sub-info
                                              (let [[t p] (add-nat-sub-equality st' table' (reifier-problem problem')
                                                                               nat-sub-info side h)]
                                                [t (assoc problem' :problem (dissoc p :disjunctions)
                                                          :disjunctions (:disjunctions p))])
                                              [table' problem'])]
                       {:st st' :table table' :problem problem'
                        :new-facts (+ n (if nat-sub-info 1 0))}))
            left (branch left-id left-type :left)]
        (if (zero? (:new-facts left))
          (recur (rest disjs))
          (when-let [left-result (omega-impl (:st left) (:table left) (:problem left) (inc depth))]
            (let [right (branch right-id right-type :right)]
              (when-let [right-result (omega-impl (:st right) (:table right) (:problem right) (inc depth))]
                {:status :contradiction :atom-table table
                 :disjunctions-proof [{:left-result left-result :right-result right-result
                                       :left-type left-type :right-type right-type
                                       :left-fvar-id left-id :right-fvar-id right-id
                                       :or-proof or-proof}]}))))))))

(defn- omega-impl
  "Frontend.omegaImpl: process facts, eliminate, then split. nil means stuck;
   contradiction results carry a certificate and their own atom context."
  [st table problem depth]
  (let [[table problem _] (process-facts st table problem)
        [table result] (run-omega-solver table (:problem problem))]
    (cond
      (:direct-false (:problem problem)) {:status :contradiction :direct-false (:direct-false (:problem problem)) :atom-table table}
      (not (:possible result)) (assoc result :status :contradiction :atom-table table)
      :else (split-disjunction st table problem depth))))

(defn- omega-check
  "Run the omega algorithm. Returns the solved problem with :atom-table metadata, or nil.
   neg-hyp-proof is the proof of ¬P for the negated goal (from by_contra), or nil."
  [st goal-type lctx neg-hyp-proof]
  (let [table (mk-atom-table)
        problem (mk-problem)
        ;; Collect from hypotheses
        [table problem] (collect-hypotheses st table problem lctx)
        ;; Check for direct False hypothesis short-circuit
        _ (when (:direct-false problem)
            ;; Found a direct False proof — return immediately
            (throw (ex-info "::direct-false::"
                            {:direct-false (:direct-false problem)
                             :atom-table table})))
        ;; Negate goal
        [table negated] (negate-goal st table problem goal-type neg-hyp-proof)]
    ;; Check for direct False in negated problem
    (when (:direct-false negated)
      (throw (ex-info "::direct-false::"
                      {:direct-false (:direct-false negated)
                       :atom-table table})))
    (let [base-problem (if (:disjunction negated)
                        ;; Goal negation produced a disjunction — queue it on the original problem
                         (queue-disjunction problem (:disjunction negated))
                        ;; No disjunction — negated IS the problem with constraints added
                         negated)
          [table ready-problem _] (process-facts st table (mk-meta-problem base-problem))]
      (omega-impl st table ready-problem 0))))

(declare build-false-proof-from-result)

(defn- build-false-proof-from-result
  "Build a proof of False from an omega result, handling nested disjunctions.
   atoms-expr is the Ansatz expression for the atoms list."
  [env result atoms-expr]
  (if (:direct-false result)
    (:direct-false result)
  (if-let [disj-proofs (seq (:disjunctions-proof result))]
    ;; Has disjunction proofs — build Or.elim chain
    (let [{:keys [left-result right-result left-type right-type
                  left-fvar-id right-fvar-id or-proof]} (first disj-proofs)
          false-type (e/const' (:false-name omega-names) [])
          left-false (build-false-proof-from-result env left-result
                                                     (build-atoms-expr (:atom-table left-result)))
          right-false (build-false-proof-from-result env right-result
                                                      (build-atoms-expr (:atom-table right-result)))
          left-lam (e/lam "h_left" left-type
                          (e/abstract1 left-false left-fvar-id) :default)
          right-lam (e/lam "h_right" right-type
                           (e/abstract1 right-false right-fvar-id) :default)]
      (e/app* (e/const' (:or-elim omega-names) [])
              left-type right-type false-type
              or-proof left-lam right-lam))
    ;; No disjunctions — direct proof from justification
    (prove-false-from-justification env result atoms-expr))))

(defn- strip-forall-binders
  "Strip leading forall binders from goal type, introducing fresh fvars.
   Returns [inner-type fvar-infos lctx'] where fvar-infos is a vec of
   {:id fvar-id :name str :type Expr} in introduction order."
  [st goal-type lctx]
  (loop [ty goal-type, lctx lctx, fvar-infos [], st st]
    (let [ty-whnf (#'tc/cached-whnf st ty)]
      (if (e/forall? ty-whnf)
        (let [fv-id (long (System/nanoTime))
              binder-name (or (e/forall-name ty-whnf) "x")
              ;; Use original ty's binder type when possible to preserve structure
              ;; (WHNF may unfold LE.le to Nat.le etc.)
              use-original (e/forall? ty)
              binder-type (if use-original (e/forall-type ty) (e/forall-type ty-whnf))
              body (e/instantiate1 (if use-original (e/forall-body ty) (e/forall-body ty-whnf))
                                   (e/fvar fv-id))
              lctx' (red/lctx-add-local lctx fv-id binder-name binder-type)
              st' (tc/attach-lctx st lctx')]
          (recur body lctx'
                 (conj fvar-infos {:id fv-id :name binder-name :type binder-type})
                 st'))
        ;; Return the non-WHNF type to preserve LE.le/LT.lt structure
        ;; (WHNF unfolds LE.le to Nat.le which omega doesn't recognize)
        [ty fvar-infos lctx]))))

(defn- wrap-proof-in-lambdas
  "Wrap a proof term in lambdas for the introduced fvars (reverse of strip-forall-binders).
   Abstracts each fvar and wraps in a lambda."
  [proof-term fvar-infos]
  (reduce (fn [term {:keys [id name type]}]
            (e/lam name type (e/abstract1 term id) :default))
          proof-term
          (reverse fvar-infos)))

(defn- reconstruction-available?
  "The full reconstruction references Lean.Omega.* constants (Init.Omega). On a
   reduced init they are absent and no proof can be built."
  [env]
  (some? (kenv/lookup env (name/from-string "Lean.Omega.LinearCombo.coordinate_eval"))))

(defn- prepare-goal
  "Shared front half of omega: strip ∀ binders, normalise bare `Nat.lt`/`Nat.le`,
   and set up the by_contra hypothesis. Returns the map both the proving entry point
   (`omega`) and the decide-only one (`decides?`) work from."
  [env goal-type lctx]
  (let [st (tc/attach-lctx (tc/mk-tc-state env) lctx)
        ;; Pass the UN-WHNF'd goal-type: strip-forall-binders WHNFs internally only to
        ;; find ∀ binders and deliberately returns the un-WHNF'd comparison, so
        ;; negate-goal sees `LE.le`/`LT.lt` (handled) rather than the unfolded
        ;; `Nat.le`/`Nat.lt` (not handled) — needed for succ goals.
        [inner-goal fvar-infos lctx-with-intros] (strip-forall-binders st goal-type lctx)
        ;; Bare `Nat.lt a b` / `Nat.le a b` goals (e.g. from instantiating a relation
        ;; variable with Nat.lt) → the LT.lt/LE.le instance spelling negate-goal handles.
        ;; Defeq, so the by_contra proof still checks against the original goal type.
        inner-goal
        (let [[h as] (e/get-app-fn-args inner-goal)
              nat-c (e/const' (name/from-string "Nat") [])]
          (if (and (e/const? h) (= 2 (count as)))
            (case (name/->string (e/const-name h))
              "Nat.lt" (e/app* (e/const' (:lt-name omega-names) [lvl/zero]) nat-c
                               (e/const' (name/from-string "instLTNat") [])
                               (nth as 0) (nth as 1))
              "Nat.le" (e/app* (e/const' (:le-name omega-names) [lvl/zero]) nat-c
                               (e/const' (name/from-string "instLENat") [])
                               (nth as 0) (nth as 1))
              inner-goal)
            inner-goal))
        st-intros (tc/attach-lctx st lctx-with-intros)
        inner-whnf (#'tc/cached-whnf st-intros inner-goal)
        is-false-goal (and (e/const? inner-whnf)
                           (= (e/const-name inner-whnf) (:false-name omega-names)))
        neg-hyp-fvar-id (when-not is-false-goal (long (System/nanoTime)))
        neg-hyp-proof (when neg-hyp-fvar-id (e/fvar neg-hyp-fvar-id))
        neg-type (when-not is-false-goal
                   (e/arrow inner-goal (e/const' (:false-name omega-names) [])))
        lctx' (if neg-hyp-fvar-id
                (red/lctx-add-local lctx-with-intros neg-hyp-fvar-id "h_neg" neg-type)
                lctx-with-intros)]
    {:st (tc/attach-lctx st lctx')
     :lctx lctx'
     :inner-goal inner-goal
     :fvar-infos fvar-infos
     :neg-hyp-fvar-id neg-hyp-fvar-id
     :neg-hyp-proof neg-hyp-proof
     :neg-type neg-type
     :is-false-goal is-false-goal}))

(defn- run-check
  "Run `omega-check` on a prepared goal, absorbing the ::direct-false:: short-circuit.
   Returns the solver result map, or nil when no contradiction was derivable."
  [{:keys [st inner-goal lctx neg-hyp-proof]}]
  (try
    (omega-check st inner-goal lctx neg-hyp-proof)
    (catch clojure.lang.ExceptionInfo ex
      (if (= "::direct-false::" (.getMessage ex))
        {:direct-false (:direct-false (ex-data ex))
         :atom-table (:atom-table (ex-data ex))}
        (throw ex)))))

(defn search
  "Proof-free search: contradiction or stuck. Inference/resource faults escape."
  [env goal-type lctx]
  (if-let [result (run-check (prepare-goal env goal-type lctx))]
    (assoc result :status :contradiction)
    {:status :stuck}))

(defn decides?
  "DECIDE-ONLY omega: reify the goal and hypotheses, build the constraint system and
   run the solver — but do NOT construct a proof term. True iff omega found the
   negated goal contradictory, i.e. iff `omega` would have something to certify.

   Cheap, because proof construction in this engine is LAZY: `reify-term` returns a
   thunk that is only applied once an atoms-expression is supplied, and the whole of
   `extract-proof` is skipped. Everything before that is shared with the real tactic,
   which is the point — a caller that only needs a yes/no gets exactly the answer the
   proving engine would give, instead of a second, weaker procedure's guess.

   This is what `ansatz.tactic.simp`'s discharger uses; it replaced the proof-free
   duplicate that used to live in `ansatz.tactic.omega`."
  [env goal-type lctx]
  (= :contradiction (:status (search env goal-type lctx))))

(defn try-decide
  "Only use the optional decide fast path on non-quantified goals. Lean's
   Frontend.omegaTactic introduces binders via falseOrByContra; quantified
   arithmetic belongs to that pipeline, not speculative forall instances."
  [ps]
  (when-let [goal (proof/current-goal ps)]
    (let [st (tc/attach-lctx (tc/mk-tc-state (:env ps)) (:lctx goal))]
      (when-not (e/forall? (#'tc/cached-whnf st (:type goal)))
        (try
          (decide-tac/decide ps)
          (catch clojure.lang.ExceptionInfo ex
            (if (= :tactic-error (:kind (ex-data ex))) nil (throw ex))))))))

(defn omega
  "Close the current goal using the omega decision procedure with proof term construction.

   Strategy:
   1. Try decide first (fast path for ground cases)
   2. Try rfl for def-eq equality goals
   3. Run FM solver with Justification tracking
   4. Construct proof term from Justification tree; invalid certificates escape"
  [ps]
  (or (try-decide ps)
      ;; Try rfl
      (let [goal (proof/current-goal ps)
            _ (when-not goal (tactic-error! "No goals" {}))
            env (:env ps)
            st (tc/mk-tc-state env)
            st (assoc st :lctx (:lctx goal))
            goal-type (:type goal)
            goal-whnf (#'tc/cached-whnf st goal-type)
            [head args] (e/get-app-fn-args goal-whnf)]
        ;; Try rfl
        (if (and (e/const? head)
                 (= (e/const-name head) (:eq-name omega-names))
                 (= 3 (count args))
                 (tc/is-def-eq st (nth args 1) (nth args 2)))
          (let [proof-term (e/app* (e/const' (:eq-refl omega-names) (e/const-levels head))
                                   (nth args 0) (nth args 1))]
            (-> (proof/assign-mvar ps (:id goal) {:kind :exact :term proof-term})
                (proof/record-tactic :omega [] (:id goal))))
          ;; If the env lacks Init.Omega, DECLINE rather than commit a proof that
          ;; fails at kernel check.
          (let [_ (when-not (reconstruction-available? env)
                    (tactic-error! "omega: Lean.Omega.* reconstruction constants unavailable" {}))
                prepared (prepare-goal env goal-type (:lctx goal))
                {:keys [inner-goal fvar-infos neg-hyp-fvar-id neg-type is-false-goal]} prepared]
            (let [result (run-check prepared)]
              (if-not result
                (tactic-error! "omega failed — could not derive contradiction"
                               {:goal goal-type})
                ;; Found contradiction. Try to construct proof term.
                (let [false-proof
                        (if (:direct-false result)
                          ;; Direct False hypothesis — already have proof of False
                          (:direct-false result)
                          ;; Build proof (handles simple and disjunction cases via omega-impl)
                          (let [atom-table (:atom-table result)
                                atoms-expr (if atom-table
                                             (build-atoms-expr atom-table)
                                             (e/app (e/const' (name/from-string "List.nil") [lvl/zero]) int-type))]
                            (build-false-proof-from-result env result atoms-expr)))
                        inner-proof (if is-false-goal
                                      false-proof
                                      (let [lam-body (e/abstract1 false-proof neg-hyp-fvar-id)
                                            lam-term (e/lam "h_neg" neg-type lam-body :default)]
                                        (e/app* (e/const' (:decidable-by-contra omega-names) [])
                                                inner-goal
                                                (e/app (e/const' (:classical-prop-dec omega-names) [])
                                                       inner-goal)
                                                lam-term)))
                        ;; Wrap in lambdas for the intro'd forall binders
                        proof-term (wrap-proof-in-lambdas inner-proof fvar-infos)]
                    (-> (proof/assign-mvar ps (:id goal) {:kind :exact :term proof-term})
                        (proof/record-tactic :omega [] (:id goal))))
)))))))

;; ============================================================
;; Interactive cross-level API
;; ============================================================
;;
;; Exposes the omega reification pipeline as separate steps.
;; Users can inspect the constraint system, try different solver
;; strategies, fork state, and navigate between levels.

(defn reify-goal
  "Reify a proof state goal into an omega problem.
   Returns {:st tc-state, :table atom-table, :problem constraint-problem,
            :inner-goal inner-goal-type, :fvar-infos intro-fvars,
            :neg-hyp-fvar-id by-contra-fvar, :neg-hyp-proof by-contra-proof}
   or throws on failure."
  [ps]
  (let [goal (proof/current-goal ps)
        _ (when-not goal (tactic-error! "No goals" {}))
        env (:env ps)
        {:keys [inner-goal fvar-infos neg-hyp-fvar-id neg-hyp-proof is-false-goal]
         st' :st lctx' :lctx}
        (prepare-goal env (:type goal) (:lctx goal))
        ;; Reify: collect hypotheses, negate goal, add bounds
        table (mk-atom-table)
        problem (mk-problem)
        [table problem] (collect-hypotheses st' table problem lctx')
        [table negated] (negate-goal st' table problem inner-goal neg-hyp-proof)
        base-problem (if (:disjunction negated)
                       (queue-disjunction problem (:disjunction negated))
                       negated)
        [table ready-problem _] (process-facts st' table (mk-meta-problem base-problem))]
    {:st st'
     :table table
     :problem (reifier-problem ready-problem)
     :meta-problem ready-problem
     :inner-goal inner-goal
     :fvar-infos fvar-infos
     :neg-hyp-fvar-id neg-hyp-fvar-id
     :neg-hyp-proof neg-hyp-proof
     :is-false-goal is-false-goal
     :ps ps}))

(defn- expr->named-string
  "Convert an expression to a human-readable string, resolving fvar IDs to names from lctx."
  ([st expr] (expr->named-string st expr 0))
  ([st expr depth]
   (if (> depth 15)
     "..."
     (let [d (inc depth)
           lctx (:lctx st)]
       (case (e/tag expr)
         :fvar (let [id (e/fvar-id expr)
                     decl (red/lctx-lookup lctx id)]
                 (or (:name decl) (str "?fv" id)))
         :app (let [[head args] (e/get-app-fn-args expr)]
                (if (e/const? head)
                  ;; Simplify well-known Nat ops
                  (let [cn (name/->string (e/const-name head))]
                    (case cn
                      "Nat.add" (if (= 2 (count args))
                                  (str "(" (expr->named-string st (nth args 0) d)
                                       " + " (expr->named-string st (nth args 1) d) ")")
                                  (str "(" cn " " (clojure.string/join " " (map #(expr->named-string st % d) args)) ")"))
                      "Nat.sub" (if (= 2 (count args))
                                  (str "(" (expr->named-string st (nth args 0) d)
                                       " - " (expr->named-string st (nth args 1) d) ")")
                                  (str "(" cn " " (clojure.string/join " " (map #(expr->named-string st % d) args)) ")"))
                      "Nat.mul" (if (= 2 (count args))
                                  (str "(" (expr->named-string st (nth args 0) d)
                                       " * " (expr->named-string st (nth args 1) d) ")")
                                  (str "(" cn " " (clojure.string/join " " (map #(expr->named-string st % d) args)) ")"))
                      "HAdd.hAdd" (if (= 6 (count args))
                                    (str "(" (expr->named-string st (nth args 4) d)
                                         " + " (expr->named-string st (nth args 5) d) ")")
                                    (str "(" cn " ...)"))
                      "HSub.hSub" (if (= 6 (count args))
                                    (str "(" (expr->named-string st (nth args 4) d)
                                         " - " (expr->named-string st (nth args 5) d) ")")
                                    (str "(" cn " ...)"))
                      "HMul.hMul" (if (= 6 (count args))
                                    (str "(" (expr->named-string st (nth args 4) d)
                                         " * " (expr->named-string st (nth args 5) d) ")")
                                    (str "(" cn " ...)"))
                      "LE.le" (if (>= (count args) 4)
                                (str "(" (expr->named-string st (nth args 2) d)
                                     " ≤ " (expr->named-string st (nth args 3) d) ")")
                                (str "(" cn " ...)"))
                      "LT.lt" (if (>= (count args) 4)
                                (str "(" (expr->named-string st (nth args 2) d)
                                     " < " (expr->named-string st (nth args 3) d) ")")
                                (str "(" cn " ...)"))
                      "Eq" (if (= 3 (count args))
                             (str "(" (expr->named-string st (nth args 1) d)
                                  " = " (expr->named-string st (nth args 2) d) ")")
                             (str "(" cn " ...)"))
                      "Not" (if (= 1 (count args))
                              (str "¬" (expr->named-string st (nth args 0) d))
                              (str "(" cn " ...)"))
                      "Nat.succ" (if (= 1 (count args))
                                   (str "(succ " (expr->named-string st (nth args 0) d) ")")
                                   (str "(" cn " ...)"))
                      ;; Default: abbreviated
                      (str "(" cn " " (clojure.string/join " " (map #(expr->named-string st % d) args)) ")")))
                  ;; Non-const head
                  (str "(" (expr->named-string st head d) " "
                       (clojure.string/join " " (map #(expr->named-string st % d) args)) ")")))
         :lit-nat (str (e/lit-nat-val expr))
         :const (name/->string (e/const-name expr))
         :bvar (str "#" (e/bvar-idx expr))
         ;; Fall through for other forms
         (e/->string expr))))))

(defn- fvar-name
  "Get a human-readable name for an expression (fvar name from lctx, or short string)."
  [st expr]
  (expr->named-string st expr))

(defn show-problem
  "Pretty-print the reified omega problem."
  [{:keys [st table problem]}]
  (println "Atoms:")
  (doseq [[idx expr] (sort-by key (:idx->expr table))]
    (let [sub-info (get (:nat-sub-atoms table) idx)
          display (if sub-info
                    (str (fvar-name st (:a sub-info)) " - "
                         (fvar-name st (:b sub-info)))
                    (fvar-name st expr))]
      (println (str "  x" idx " = " display))))
  (println (str "\nConstraints (" (count (:constraints problem)) "):"))
  (doseq [[k fact] (:constraints problem)]
    (let [{:keys [coeffs constraint]} fact
          {:keys [lower upper]} constraint
          terms (keep-indexed
                 (fn [i c]
                   (when-not (zero? c)
                     (str (when (pos? c) "+") c "*x" i)))
                 coeffs)
          lhs (if (empty? terms) "0" (clojure.string/join " " terms))]
      (println (str "  " lhs
                    (cond
                      (and lower upper (= lower upper)) (str " = " lower)
                      (and lower upper) (str " ∈ [" lower ", " upper "]")
                      lower (str " ≥ " lower)
                      upper (str " ≤ " upper)
                      :else " (unconstrained)")))))
  (when (seq (:equalities problem))
    (println (str "\nEqualities: " (count (:equalities problem)))))
  (when (seq (:disjunctions problem))
    (println (str "\nDisjunctions (" (count (:disjunctions problem)) "):")))
  (doseq [[i d] (map-indexed vector (:disjunctions problem))]
    (println (str "  [" i "] " (expr->named-string st (:left-type d))
                  " ∨ " (expr->named-string st (:right-type d))
                  (when (:nat-sub-info d) " (Nat.sub)")))))

(defn solve-fm
  "Run the Fourier-Motzkin solver on a reified problem.
   Returns the result map or nil."
  [{:keys [st table problem meta-problem] :as reified}]
  (omega-impl st table (or meta-problem (mk-meta-problem problem)) 0))

(defn certify
  "Reconstruct the full proof term from a solver result.
   Returns the solved proof state."
  [{:keys [st table problem inner-goal fvar-infos
           neg-hyp-fvar-id neg-hyp-proof is-false-goal ps] :as reified}
   result]
  (let [goal (proof/current-goal ps)
        env (:env ps)
        atom-table (:atom-table result)
        atoms-expr (if atom-table
                     (build-atoms-expr atom-table)
                     (e/app (e/const' (name/from-string "List.nil") [lvl/zero]) int-type))
        false-proof (if (:direct-false result)
                      (:direct-false result)
                      (build-false-proof-from-result env result atoms-expr))
        inner-proof (if is-false-goal
                      false-proof
                      (let [lam-body (e/abstract1 false-proof neg-hyp-fvar-id)
                            lam-term (e/lam "h_neg"
                                            (e/arrow inner-goal
                                                     (e/const' (:false-name omega-names) []))
                                            lam-body :default)]
                        (e/app* (e/const' (:decidable-by-contra omega-names) [])
                                inner-goal
                                (e/app (e/const' (:classical-prop-dec omega-names) [])
                                       inner-goal)
                                lam-term)))
        proof-term (wrap-proof-in-lambdas inner-proof fvar-infos)]
    (-> (proof/assign-mvar ps (:id goal) {:kind :exact :term proof-term})
        (proof/record-tactic :omega-interactive [] (:id goal)))))


;; Every recursive entry shares the host heartbeat; wrappers also cover delayed
;; certificate descent invoked after search. No exception is converted to stuck.
(doseq [v [#'reify-term #'reify-prop #'negate-goal
           #'build-false-proof-from-result #'omega-impl #'split-disjunction #'omega #'decides?
           #'reify-goal #'certify #'search]]
  (alter-var-root v om/guarded))
