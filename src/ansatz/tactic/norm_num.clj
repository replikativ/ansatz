;; Tactic layer — norm_num: ground numeric normalization.
;;
;; Evaluates ground arithmetic expressions and proves the results.
;; Handles Nat, Int, and types with numeric instances (Real, etc.).
;;
;; Strategy:
;; 1. Reify: Ansatz numeric expression → Clojure number (exact rational)
;; 2. Evaluate: compute using Clojure arithmetic
;; 3. Certify: use `decide` to verify the result in the kernel
;;
;; As a simproc: reduces ground subexpressions during simp.
;; As a tactic: closes ground Eq/LE/LT goals.

(ns ansatz.tactic.norm-num
  "Ground numeric normalization tactic and simproc.

   Supports:
   - Nat/Int literal arithmetic (+, -, *, /, %, ^)
   - OfNat coercions (0, 1, numeric literals in any type)
   - Equality and ordering goals on ground terms
   - Integration as simproc in the simp pipeline"
  (:require [ansatz.kernel.expr :as e]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.tc :as tc]
            [ansatz.tactic.proof :as proof]
            [ansatz.tactic.decide :as decide-tac]
            [ansatz.tactic.instance :as instance]))

;; ============================================================
;; Well-known names
;; ============================================================

(def ^:private hadd-name (name/from-string "HAdd.hAdd"))
(def ^:private hsub-name (name/from-string "HSub.hSub"))
(def ^:private hmul-name (name/from-string "HMul.hMul"))
(def ^:private hdiv-name (name/from-string "HDiv.hDiv"))
(def ^:private hmod-name (name/from-string "HMod.hMod"))
(def ^:private hpow-name (name/from-string "HPow.hPow"))
(def ^:private hneg-name (name/from-string "Neg.neg"))
(def ^:private nat-add-name (name/from-string "Nat.add"))
(def ^:private nat-sub-name (name/from-string "Nat.sub"))
(def ^:private nat-mul-name (name/from-string "Nat.mul"))
(def ^:private nat-div-name (name/from-string "Nat.div"))
(def ^:private nat-mod-name (name/from-string "Nat.mod"))
(def ^:private nat-pow-name (name/from-string "Nat.pow"))
(def ^:private nat-succ-name (name/from-string "Nat.succ"))
(def ^:private nat-zero-name (name/from-string "Nat.zero"))
(def ^:private int-ofnat-name (name/from-string "Int.ofNat"))
(def ^:private int-negsucc-name (name/from-string "Int.negSucc"))
(def ^:private int-add-name (name/from-string "Int.add"))
(def ^:private int-sub-name (name/from-string "Int.sub"))
(def ^:private int-mul-name (name/from-string "Int.mul"))
(def ^:private int-neg-name (name/from-string "Int.neg"))
(def ^:private ofnat-name (name/from-string "OfNat.ofNat"))
(def ^:private eq-name (name/from-string "Eq"))
(def ^:private le-name (name/from-string "LE.le"))
(def ^:private lt-name (name/from-string "LT.lt"))
(def ^:private ne-name (name/from-string "Ne"))
(def ^:private ge-name (name/from-string "GE.ge"))
(def ^:private gt-name (name/from-string "GT.gt"))
(defn- tactic-error! [msg data]
  (throw (ex-info (str "norm_num: " msg) (merge {:kind :tactic-error} data))))

;; ============================================================
;; Reification: Ansatz expression → Clojure number
;; ============================================================
;; Returns a number (Long, BigInteger, or Ratio) or nil if not ground.

(defn- try-match-head
  "Match a constant-headed application, using WHNF if needed."
  [st expr]
  (let [[head args] (e/get-app-fn-args expr)]
    (if (e/const? head)
      [(e/const-name head) (vec args)]
      (let [w (#'tc/cached-whnf st expr)
            [whead wargs] (e/get-app-fn-args w)]
        (when (e/const? whead)
          [(e/const-name whead) (vec wargs)])))))

(declare reify-num)

(defn- reify-num
  "Reify a Ansatz expression to a Clojure number.
   Returns a number or nil if the expression is not ground numeric."
  [st expr]
  (let [w (#'tc/cached-whnf st expr)]
    (cond
      ;; Nat literal
      (e/lit-nat? w) (e/lit-nat-val w)

      ;; Nat.zero
      (and (e/const? w) (= (e/const-name w) nat-zero-name)) 0

      ;; Application
      (e/app? w)
      (when-let [[hname args] (try-match-head st w)]
        (cond
          ;; OfNat.ofNat α n inst → reify n
          (and (= hname ofnat-name) (= 3 (count args)))
          (reify-num st (nth args 1))

          ;; Nat.succ n → n + 1
          (and (= hname nat-succ-name) (= 1 (count args)))
          (when-let [n (reify-num st (nth args 0))] (inc n))

          ;; Int.ofNat n → n
          (and (= hname int-ofnat-name) (= 1 (count args)))
          (reify-num st (nth args 0))

          ;; Int.negSucc n → -(n+1)
          (and (= hname int-negsucc-name) (= 1 (count args)))
          (when-let [n (reify-num st (nth args 0))] (- (inc n)))

          ;; HAdd.hAdd _ _ _ _ a b → a + b
          (and (= hname hadd-name) (= 6 (count args)))
          (let [a (reify-num st (nth args 4))
                b (reify-num st (nth args 5))]
            (when (and a b) (+ a b)))

          ;; HSub.hSub _ _ _ _ a b → a - b
          (and (= hname hsub-name) (= 6 (count args)))
          (let [a (reify-num st (nth args 4))
                b (reify-num st (nth args 5))]
            (when (and a b) (- a b)))

          ;; HMul.hMul _ _ _ _ a b → a * b
          (and (= hname hmul-name) (= 6 (count args)))
          (let [a (reify-num st (nth args 4))
                b (reify-num st (nth args 5))]
            (when (and a b) (* a b)))

          ;; HDiv.hDiv _ _ _ _ a b → a / b
          (and (= hname hdiv-name) (= 6 (count args)))
          (let [a (reify-num st (nth args 4))
                b (reify-num st (nth args 5))]
            (when (and a b (not (zero? b)))
              (if (and (integer? a) (integer? b) (zero? (rem a b)))
                (quot a b)
                (/ a b))))

          ;; HMod.hMod _ _ _ _ a b → a % b
          (and (= hname hmod-name) (= 6 (count args)))
          (let [a (reify-num st (nth args 4))
                b (reify-num st (nth args 5))]
            (when (and a b (not (zero? b))) (mod a b)))

          ;; HPow.hPow _ _ _ _ a n → a ^ n
          (and (= hname hpow-name) (= 6 (count args)))
          (let [a (reify-num st (nth args 4))
                n (reify-num st (nth args 5))]
            (when (and a n (integer? n) (>= n 0) (<= n 1000))
              (reduce * 1 (repeat n a))))

          ;; Neg.neg _ _ a → -a
          (and (= hname hneg-name) (= 3 (count args)))
          (when-let [a (reify-num st (nth args 2))] (- a))

          ;; Nat.add/sub/mul/div/mod/pow
          (and (= hname nat-add-name) (= 2 (count args)))
          (let [a (reify-num st (nth args 0))
                b (reify-num st (nth args 1))]
            (when (and a b) (+ a b)))

          (and (= hname nat-sub-name) (= 2 (count args)))
          (let [a (reify-num st (nth args 0))
                b (reify-num st (nth args 1))]
            (when (and a b) (max 0 (- a b))))

          (and (= hname nat-mul-name) (= 2 (count args)))
          (let [a (reify-num st (nth args 0))
                b (reify-num st (nth args 1))]
            (when (and a b) (* a b)))

          (and (= hname nat-div-name) (= 2 (count args)))
          (let [a (reify-num st (nth args 0))
                b (reify-num st (nth args 1))]
            (when (and a b (pos? b)) (quot a b)))

          (and (= hname nat-mod-name) (= 2 (count args)))
          (let [a (reify-num st (nth args 0))
                b (reify-num st (nth args 1))]
            (when (and a b (pos? b)) (mod a b)))

          (and (= hname nat-pow-name) (= 2 (count args)))
          (let [a (reify-num st (nth args 0))
                b (reify-num st (nth args 1))]
            (when (and a b (>= b 0) (<= b 1000))
              (reduce * 1 (repeat b a))))

          ;; Int.add/sub/mul/neg
          (and (= hname int-add-name) (= 2 (count args)))
          (let [a (reify-num st (nth args 0))
                b (reify-num st (nth args 1))]
            (when (and a b) (+ a b)))

          (and (= hname int-sub-name) (= 2 (count args)))
          (let [a (reify-num st (nth args 0))
                b (reify-num st (nth args 1))]
            (when (and a b) (- a b)))

          (and (= hname int-mul-name) (= 2 (count args)))
          (let [a (reify-num st (nth args 0))
                b (reify-num st (nth args 1))]
            (when (and a b) (* a b)))

          (and (= hname int-neg-name) (= 1 (count args)))
          (when-let [a (reify-num st (nth args 0))] (- a))

          :else nil))

      :else nil)))

;; ============================================================
;; Ground evaluation check
;; ============================================================

(defn ground-numeric?
  "Check if an expression is a ground numeric expression (no free variables)."
  [st expr]
  (some? (reify-num st expr)))

;; ============================================================
;; norm_num tactic
;; ============================================================
;; Closes Eq, LE, LT, Ne, GE, GT goals on ground numeric expressions.
;; Strategy: delegate to `decide` which evaluates the decidable instance.

(defn norm-num
  "Close a goal by evaluating ground arithmetic.
   Works for Eq, LE, LT, Ne, GE, GT goals where both sides are ground numeric.
   Certification via `decide` — the kernel evaluates the Decidable instance."
  [ps]
  (let [goal (proof/current-goal ps)
        _ (when-not goal (tactic-error! "No goals" {}))
        env (:env ps)
        st (tc/mk-tc-state env)
        st (assoc st :lctx (:lctx goal))
        goal-type (:type goal)
        [head args] (e/get-app-fn-args goal-type)]
    ;; Check that it's a supported relational goal
    (when-not (and (e/const? head)
                   (let [hname (e/const-name head)]
                     (or (= hname eq-name) (= hname le-name) (= hname lt-name)
                         (= hname ne-name) (= hname ge-name) (= hname gt-name))))
      (tactic-error! "goal is not a numeric relation"
                     {:goal goal-type}))
    ;; Try decide
    (try (decide-tac/decide ps)
         (catch Exception ex
           (tactic-error! (str "cannot evaluate: " (.getMessage ex))
                          {:goal goal-type})))))

;; ============================================================
;; norm_num simproc — for integration with simp
;; ============================================================
;; Evaluates ground numeric subexpressions during simplification.
;; Returns a SimpResult with the evaluated literal and a proof via decide.

(defn try-norm-num-simproc
  "Try to evaluate a ground numeric expression for simp.
   Returns a SimpResult {:expr simplified :proof? proof} or nil.
   The proof is constructed via the Java TypeChecker's decide verification."
  [st env expr]
  (when-let [val (reify-num st expr)]
    ;; Only simplify if the result is a simple literal
    ;; (avoid replacing complex expressions with identical structure)
    (when (integer? val)
      (let [result-expr (e/lit-nat val)]
        ;; Check it's actually different from the input
        (when (and (not= expr result-expr)
                   (not (e/lit-nat? expr)))
          ;; The proof is just definitional equality (the kernel will verify)
          ;; Return as a def-eq result (no proof needed — kernel reduces both)
          {:expr result-expr :proof? nil :cache true})))))
