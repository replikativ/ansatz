(ns ansatz.kernel-reduction-test
  "Reduction, inference and definitional equality against Lean v4.36.0's type_checker.cpp.
   The Lean outcomes are observed with `Lean.Kernel.whnf` / `Lean.Kernel.isDefEq` in
   test/lean-parity/kernel/Reduction.lean."
  (:require [clojure.test :refer [deftest testing is]]
            [ansatz.test-env :as te]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.reduce :as red])
  (:import [ansatz.kernel ConstantInfo Env Expr KernelAbort LeanExprKey Name Reducer TypeChecker]))

(def ^:private fuel 20000000)
(defn- n [s] (name/from-string s))
(defn- c ([s] (e/const' (n s) [])) ([s ls] (e/const' (n s) ls)))
(def ^:private l0 lvl/zero)
(def ^:private l1 (lvl/succ lvl/zero))
(def ^:private type0 (e/sort' l1))
(defn- pi [nm dom body] (e/forall' nm dom body :default))
(defn- lam [nm dom body] (e/lam nm dom body :default))
(defn- lit [k] (e/lit-nat (biginteger k)))

(def ^:private base (delay @te/bundled-init-env))

(defn- tc
  (^TypeChecker [env] (tc env fuel))
  (^TypeChecker [env f] (doto (TypeChecker. ^Env env) (.setFuel (long f)))))
(defn- whnf [env ex] (.whnf (.getReducer (tc env)) ex))
(defn- defeq? [env a b] (.isDefEq (tc env) a b))
(defn- kernel-error
  "The message of the kernel error `f` raises — a RuntimeException, never a JVM error such as
   StackOverflowError — or nil when `f` returns."
  [f]
  (try (f) nil (catch RuntimeException ex (str (.getMessage ex)))))
(defn- same? [^Expr a ^Expr b] (.equals (LeanExprKey. a) (LeanExprKey. b)))

(def ^:private st-env
  (delay
    (let [env (env/add-inductive @base (env/mk-inductive-decl [] 0 false [["KS" type0 [["KS.mk" (pi "x" (c "Nat") (c "KS"))]]]]) fuel)
          env (env/add-inductive env (env/mk-inductive-decl [] 0 false [["KT" type0 [["KT.mk" (pi "x" (c "Nat") (c "KT"))]]]]) fuel)]
      (env/check-constant env (env/mk-axiom (n "kax") [] (c "KS")) fuel))))

(deftest projections-are-owner-checked
  (testing "reduce_proj_core: a constructor of another structure is not projected"
    (let [term (e/proj (n "KS") 0 (e/app (c "KT.mk") (lit 1)))]
      (is (= (str term) (str (whnf @st-env term))))))
  (testing "projection congruence requires the same structure"
    (is (false? (defeq? @st-env (e/proj (n "KS") 0 (c "kax")) (e/proj (n "KT") 0 (c "kax")))))))

(deftest nat-primitives-match-complete-constants-and-limits
  (testing "Nat.add.{0} is not the primitive Nat.add"
    (let [term (e/app* (c "Nat.add" [l0]) (lit 2) (lit 3))]
      (is (= (str term) (str (whnf @base term))))))
  (testing "Nat.pow checks its 32-bit exponent before the base"
    (is (re-find #"does not fit in a 32-bit unsigned integer"
                 (str (kernel-error #(whnf @base (e/app* (c "Nat.pow") (lit 1) (lit 4294967296))))))))
  (testing "Nat.shiftRight has no count limit"
    (is (= (str (lit 0)) (str (whnf @base (e/app* (c "Nat.shiftRight") (lit 1) (lit 4294967296)))))))
  (testing "Nat.zero.{0} is not Nat.zero: proof irrelevance infers it and rejects the universe arity"
    (is (re-find #"Universe level mismatch for Nat.zero"
                 (str (kernel-error #(defeq? @base (c "Nat.zero" [l0]) (lit 0))))))))

(deftest int-reduces-through-its-definitions
  (testing "Int.neg on a bare Nat literal unfolds to Int.rec and sticks there (Lean prints
   `Int.rec (fun a => …) (fun a => …) 3`)"
    (let [r (whnf @base (e/app (c "Int.neg") (lit 3)))
          [head args] (e/get-app-fn-args r)]
      (is (= (n "Int.rec") (e/const-name head)))
      (is (= 4 (count args)))
      (is (= (str (lit 3)) (str (last args))))))
  (testing "Int arithmetic still computes"
    (let [i (fn [k] (e/app (c "Int.ofNat") (lit k)))]
      (is (defeq? @base (e/app* (c "Int.add") (i 2) (i 3)) (i 5)))
      (is (defeq? @base (e/app* (c "Int.mul") (e/app (c "Int.negSucc") (lit 6)) (i 3))
            (e/app (c "Int.negSucc") (lit 20)))))))

(deftest kernel-errors-propagate-out-of-proof-irrelevance
  ;; equivalent, structurally different universes: no quick answer, so is_def_eq_proof_irrel
  ;; infers the unknown constant and the error escapes
  (let [u (lvl/param (n "u")) v (lvl/param (n "v"))]
    (is (re-find #"Unknown constant: KUnknown"
                 (str (kernel-error #(defeq? @base (c "KUnknown" [(lvl/level-max (lvl/succ u) (lvl/succ v))])
                                       (c "KUnknown" [(lvl/level-max (lvl/succ v) (lvl/succ u))]))))))))

;; ------------------------------------------------------------------ lazy delta: bounds

(def ^:private alias-env
  (delay
    (reduce (fn [env i]
              (env/check-constant env (env/mk-def (n (str "kalias" i)) [] (c "Nat")
                                                  (if (zero? i) (c "Nat.zero") (c (str "kalias" (dec i))))
                                                  :hints {:regular (inc i)})
                                  fuel))
            @base (range 10002))))

(def ^:private proj-alias-env
  (delay
    (reduce (fn [env i]
              (env/check-constant env (env/mk-def (n (str "kpa" i)) [] (c "KS")
                                                  (if (zero? i) (e/app (c "KS.mk") (lit 1)) (c (str "kpa" (dec i))))
                                                  :hints {:regular (inc i)})
                                  fuel))
            @st-env (range 10002))))

(defn- proj0 [x] (e/proj (n "KS") 0 x))

(deftest lazy-delta-has-no-step-cutoff
  (testing "lazy_delta_reduction: a 10,001-alias chain"
    (is (defeq? @alias-env (c "kalias10001") (c "Nat.zero"))))
  (testing "lazy_delta_proj_reduction: a 10,001-alias chain under a projection"
    (is (defeq? @proj-alias-env (proj0 (c "kpa10001")) (proj0 (c "kpa0"))))))

;; ------------------------------------------------------------------ the nested-pair regression

(def ^:private nested-env
  ;; ka opaque; kb := ka; kh : ka = kb
  (delay
    (let [env (env/check-constant @base (env/mk-axiom (n "ka") [] (c "Nat")) fuel)
          env (env/check-constant env (env/mk-def (n "kb") [] (c "Nat") (c "ka") :hints {:regular 1}) fuel)]
      (env/check-constant env (env/mk-axiom (n "kh") [] (e/app* (c "Eq" [l1]) (c "Nat") (c "ka") (c "kb"))) fuel))))

(defn- eq-rec-levels
  "Eq.rec.{u, u_1}: u is the motive's universe, u_1 the carrier's."
  [env motive-level alpha-level]
  (let [^ConstantInfo ci (env/lookup env (n "Eq.rec"))]
    (assert (= ["u" "u_1"] (mapv str (.levelParams ci))))
    [motive-level alpha-level]))

(deftest a-nested-comparison-keeps-the-outer-pair
  ;; the audit's case: reducing `q` (K-like Eq.rec over kh : ka = kb) inside the Nat shortcut
  ;; compares `ka = kb` with `ka = ka`; that inner lazy delta must not replace the outer pair
  (let [env @nested-env
        motive (lam "x" (c "Nat") (lam "h" (e/app* (c "Eq" [l1]) (c "Nat") (c "ka") (e/bvar 0)) (c "Nat")))
        q (e/app* (c "Eq.rec" (eq-rec-levels env l1 l1)) (c "Nat") (c "ka") motive (c "ka") (c "kb") (c "kh"))]
    (is (defeq? env q (c "ka")))
    (is (false? (defeq? env (e/app (c "Nat.succ") q) (c "ka"))))))

;; ------------------------------------------------------------------ inference

(deftest inference-returns-the-declared-type
  ;; Lean's infer_type_core does not strip outParam / semiOutParam
  (let [env (env/check-constant @base (env/mk-axiom (n "kOut") [] (e/app (c "outParam" [l1]) (c "Nat"))) fuel)]
    (is (= (str (e/app (c "outParam" [l1]) (c "Nat"))) (str (.inferType (tc env) (c "kOut")))))))

(deftest inference-rejects-loose-bound-variables
  (is (re-find #"loose bound variables"
               (str (kernel-error #(.inferType (tc @base) (e/app (c "Nat.succ") (e/bvar 0)))))))
  (is (re-find #"bound variable index is too big" (str (kernel-error #(Expr/bvar 1048575)))))
  (is (some? (Expr/bvar 1048574)) "range 1048575 fits Lean's 20 bits"))

(deftest dead-lets-are-dropped-from-inferred-types
  ;; local_ctx::mk_binding keeps a let only when its own variable (#0) occurs:
  ;; let x : Type := Nat; let y : Nat := 0; fun z : x => z   :   let x : Type := Nat; x → x
  (let [term (e/let' (n "x") type0 (c "Nat")
                     (e/let' (n "y") (c "Nat") (lit 0)
                             (lam "z" (e/bvar 1) (e/bvar 0))))
        expected (e/let' (n "x") type0 (c "Nat") (pi "z" (e/bvar 0) (e/bvar 1)))
        ty (.inferType (tc @base) term)]
    (is (same? expected ty) (str ty))))

;; ------------------------------------------------------------------ string literals

(def ^:private string-env
  ;; a custom environment in which String.ofList ignores its argument
  (delay
    (let [u (n "u") tu (e/sort' (lvl/succ (lvl/param u)))
          list-u (fn [a] (e/app (c "List" [(lvl/param u)]) a))
          ax (fn [env nm lps ty] (env/add-constant env (env/mk-axiom (n nm) lps ty)))
          env (-> (Env.)
                  (ax "Nat" [] type0) (ax "String" [] type0) (ax "Char" [] type0)
                  (ax "Char.ofNat" [] (pi "n" (c "Nat") (c "Char")))
                  (ax "List" [u] (pi "a" tu tu))
                  (ax "List.nil" [u] (e/forall' (n "a") tu (list-u (e/bvar 0)) :implicit))
                  (ax "List.cons" [u] (e/forall' (n "a") tu (pi "h" (e/bvar 0) (pi "t" (list-u (e/bvar 1)) (list-u (e/bvar 2)))) :implicit))
                  (ax "s0" [] (c "String")))]
      (env/check-constant env (env/mk-def (n "String.ofList") [] (pi "l" (e/app (c "List" [l0]) (c "Char")) (c "String"))
                                          (lam "l" (e/app (c "List" [l0]) (c "Char")) (c "s0")) :hints {:regular 1})
                          fuel))))

(deftest string-literals-expand-only-against-string-of-list
  ;; try_string_lit_expansion_core: the other side must be `String.ofList xs`
  (is (false? (defeq? @string-env (e/lit-str "a") (c "s0")))))

(defn- char-list [cps]
  (reduce (fn [acc cp] (e/app* (c "List.cons" [l0]) (c "Char") (e/app (c "Char.ofNat") (lit cp)) acc))
          (e/app (c "List.nil" [l0]) (c "Char")) (reverse cps)))

(deftest string-literals-expand-by-code-point
  ;; U+1D538 (outside the BMP) is one Char, not two UTF-16 units
  (is (defeq? @base (e/lit-str "𝔸") (e/app (c "String.ofList") (char-list [120120]))))
  (is (false? (defeq? @base (e/lit-str "𝔸") (e/app (c "String.ofList") (char-list [55349 56632]))))))

;; ------------------------------------------------------------------ errors after unfolding

(deftest delta-candidates-have-the-right-universe-arity
  ;; is_delta: kg unfolds to kf.{0}, a wrong-arity application and so no delta candidate; the
  ;; comparison falls through to is_def_eq_unit_like, whose inference rejects it (Lean: error)
  (let [env (env/check-constant @base (env/mk-def (n "kf") [] (c "Nat") (c "Nat.zero") :hints {:regular 5}) fuel)
        env (env/add-constant env (env/mk-def (n "kg") [] (c "Nat") (c "kf" [l0]) :hints {:regular 1}))]
    (is (re-find #"Universe level mismatch for kf"
                 (str (kernel-error #(defeq? env (c "kg") (c "Nat.zero"))))))))

(deftest eta-struct-inference-errors-propagate
  ;; kgS unfolds to the wrong-arity kfS.{0}; against `KS.mk 1` the comparison reaches
  ;; try_eta_struct_core, whose inference of kfS.{0} fails (Lean: error)
  (let [env (env/check-constant @st-env (env/mk-def (n "kfS") [] (c "KS") (e/app (c "KS.mk") (lit 0)) :hints {:regular 5}) fuel)
        env (env/add-constant env (env/mk-def (n "kgS") [] (c "KS") (c "kfS" [l0]) :hints {:regular 1}))]
    (is (re-find #"Universe level mismatch for kfS"
                 (str (kernel-error #(defeq? env (c "kgS") (e/app (c "KS.mk") (lit 1)))))))))
