(ns ansatz.kernel-reduction-test
  "Reduction, inference and definitional equality against Lean v4.36.0's type_checker.cpp.
   The Lean outcomes are observed with `Lean.Kernel.whnf` / `Lean.Kernel.isDefEq` in
   test/lean-parity/kernel/Reduction.lean."
  (:require [clojure.test :refer [deftest testing is]]
            [ansatz.test-env :as te]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.name :as name])
  (:import [ansatz.kernel Env Expr TypeChecker]))

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

(defn- tc ^TypeChecker [env] (doto (TypeChecker. ^Env env) (.setFuel fuel)))
(defn- whnf [env ex] (.whnf (.getReducer (tc env)) ex))
(defn- defeq? [env a b] (.isDefEq (tc env) a b))
(defn- outcome
  "The result of `f`, or :kernel-error if the kernel throws."
  [f]
  (try (f) (catch Throwable _ :kernel-error)))

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
    (is (= :kernel-error (outcome #(whnf @base (e/app* (c "Nat.pow") (lit 1) (lit 4294967296)))))))
  (testing "Nat.shiftRight has no count limit"
    (is (= (str (lit 0)) (str (whnf @base (e/app* (c "Nat.shiftRight") (lit 1) (lit 4294967296)))))))
  (testing "Nat.zero.{0} is not Nat.zero"
    (is (= :kernel-error (outcome #(defeq? @base (c "Nat.zero" [l0]) (lit 0)))))))

(deftest int-reduces-through-its-definitions
  (testing "no native Int.neg on a bare Nat literal"
    (let [r (whnf @base (e/app (c "Int.neg") (lit 3)))]
      (is (not= (n "Int.negSucc") (e/const-name (e/get-app-fn r))))))
  (testing "Int arithmetic still computes"
    (let [i (fn [k] (e/app (c "Int.ofNat") (lit k)))]
      (is (defeq? @base (e/app* (c "Int.add") (i 2) (i 3)) (i 5)))
      (is (defeq? @base (e/app* (c "Int.mul") (e/app (c "Int.negSucc") (lit 6)) (i 3))
            (e/app (c "Int.negSucc") (lit 20)))))))

(deftest kernel-errors-propagate-out-of-proof-irrelevance
  (is (= :kernel-error (outcome #(defeq? @base (c "KUnknown" [l0]) (c "KUnknown" [(lvl/level-max l0 l0)]))))))

(deftest lazy-delta-has-no-step-cutoff
  (let [env (reduce (fn [env i]
                      (env/check-constant env (env/mk-def (n (str "kalias" i)) [] (c "Nat")
                                                          (if (zero? i) (c "Nat.zero") (c (str "kalias" (dec i))))
                                                          :hints {:regular (inc i)})
                                          fuel))
                    @base (range 10002))]
    (is (defeq? env (c "kalias10001") (c "Nat.zero")))))

(deftest inference-returns-the-declared-type
  ;; Lean's infer_type_core does not strip outParam / semiOutParam
  (let [env (env/check-constant @base (env/mk-axiom (n "kOut") [] (e/app (c "outParam" [l1]) (c "Nat"))) fuel)]
    (is (= (str (e/app (c "outParam" [l1]) (c "Nat"))) (str (.inferType (tc env) (c "kOut")))))))

(deftest inference-rejects-loose-bound-variables
  (is (= :kernel-error (outcome #(.inferType (tc @base) (e/app (c "Nat.succ") (e/bvar 0))))))
  (is (= :kernel-error (outcome #(Expr/bvar 1048575)))))

(deftest dead-lets-are-dropped-from-inferred-types
  ;; local_ctx::mk_binding keeps a let only when its own variable (#0) occurs
  (let [term (e/let' (n "x") type0 (c "Nat")
                     (e/let' (n "y") (c "Nat") (lit 0)
                             (lam "z" (e/bvar 1) (e/bvar 0))))
        ty (str (.inferType (tc @base) term))]
    (is (not (re-find #"\by\b" ty)) ty)))

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

(deftest delta-candidates-have-the-right-universe-arity
  ;; is_delta: a definition applied to the wrong number of universes is no candidate, so lazy
  ;; delta unfolds the other side instead of giving up
  (let [env (env/check-constant @base (env/mk-def (n "kf") [] (c "Nat") (c "Nat.zero") :hints {:regular 5}) fuel)
        env (env/add-constant env (env/mk-def (n "kg") [] (c "Nat") (c "kf" [l0]) :hints {:regular 1}))]
    (is (defeq? env (c "kf" [l0]) (c "kg")))))
