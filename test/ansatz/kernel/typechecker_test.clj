(ns ansatz.kernel.typechecker-test
  "Unit tests for TypeChecker: type inference, definitional equality, fuel stats."
  (:require [clojure.test :refer [deftest testing is]]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [ansatz.export.parser :refer [parse-ndjson-file]]
            [ansatz.export.replay :as replay])
  (:import [ansatz.kernel TypeChecker Reducer EquivManager Expr Env ConstantInfo Name Level]))

;; ============================================================
;; Helpers
;; ============================================================

(def prop (e/sort' lvl/zero))
(def type0 (e/sort' (lvl/succ lvl/zero)))
(def type1 (e/sort' (lvl/succ (lvl/succ lvl/zero))))
(def ^:private bi :default)

(defn- mk-const [s] (e/const' (name/from-string s) []))

(defn- mk-tc
  "Create a TypeChecker with empty env."
  ([] (TypeChecker. (Env.)))
  ([^Env env] (TypeChecker. env)))

;; ============================================================
;; Type inference: sorts
;; ============================================================

(deftest infer-sort-test
  (testing "inferType(Prop) = Type 0"
    (let [tc (mk-tc)]
      (is (= type0 (.inferType tc prop)))))

  (testing "inferType(Type 0) = Type 1"
    (let [tc (mk-tc)]
      (is (= type1 (.inferType tc type0))))))

;; ============================================================
;; Type inference: lambda
;; ============================================================

(deftest infer-lambda-test
  (testing "inferType(λ (x : Prop). x) = Prop → Prop"
    (let [tc (mk-tc)
          id-fn (e/lam "x" prop (e/bvar 0) bi)
          result (.inferType tc id-fn)]
      ;; Should be Π (x : Prop). Prop
      (is (= Expr/FORALL (.tag result)))
      ;; domain = Prop
      (is (= prop (.o1 result)))
      ;; codomain body = Prop (since x:Prop and body returns x which has type Prop)
      ;; Actually the body type is sort(0) = Prop
      (is (= prop (.o2 result))))))

;; ============================================================
;; Type inference: application
;; ============================================================

(deftest infer-app-test
  (testing "inferType((λ x:Prop. x) Prop) = Prop"
    (let [tc (mk-tc)
          id-fn (e/lam "x" type0 (e/bvar 0) bi)
          ;; (id Prop) : Type 0
          result (.inferType tc (e/app id-fn prop))]
      (is (= type0 result)))))

;; ============================================================
;; Type inference: forall
;; ============================================================

(deftest infer-forall-test
  (testing "inferType(Prop → Prop) = Sort(imax 1 1)"
    (let [tc (mk-tc)
          ;; Π (x : Prop). Prop
          arrow (e/forall' "x" prop prop bi)
          result (.inferType tc arrow)]
      ;; In Ansatz, Π (x : A). B has type Sort(imax(level(A), level(B)))
      ;; For Prop → Prop: imax(succ(zero), succ(zero)) = imax(1, 1)
      (is (= Expr/SORT (.tag result)))
      ;; Verify it simplifies correctly under isDefEq
      (is (.isDefEq tc result type0)))))

;; ============================================================
;; Type inference: let
;; ============================================================

(deftest infer-let-test
  (testing "inferType(let x : Prop := Prop in x) uses let value"
    ;; This is a bit of a cheat — Prop : Type 0, not Prop.
    ;; let x : Type 0 := Prop in x  should have type Type 0
    (let [tc (mk-tc)
          expr (e/let' "x" type0 prop (e/bvar 0))]
      (is (= type0 (.inferType tc expr))))))

;; ============================================================
;; Definitional equality
;; ============================================================

(deftest is-def-eq-test
  (testing "reflexivity: a =?= a"
    (let [tc (mk-tc)]
      (is (.isDefEq tc prop prop))))

  (testing "beta equivalence: (λx.x) a =?= a"
    (let [tc (mk-tc)
          a prop
          id-fn (e/lam "x" type0 (e/bvar 0) bi)
          app (e/app id-fn a)]
      (is (.isDefEq tc app a))))

  (testing "let equivalence: (let x := a in x) =?= a"
    (let [tc (mk-tc)
          a prop
          let-expr (e/let' "x" type0 a (e/bvar 0))]
      (is (.isDefEq tc let-expr a))))

  (testing "non-equal expressions"
    (let [tc (mk-tc)]
      (is (not (.isDefEq tc prop type0)))))

  (testing "eta equivalence for lambda: (λx. f x) =?= f"
    ;; In Ansatz, η-equivalence holds: λx. f x ≡ f  when x ∉ FV(f)
    ;; We test with a const
    ;; Actually, Lean's kernel uses eta for λ:
    ;; is_def_eq(λx.t, s) = is_def_eq(t, s x) when s is not lambda
    ;; So (λx. c x) =?= c should work via eta
    ;; But we need c to have a function type for this to work with inferType
    ;; Let's use a simpler test: (λx. (λy.y) x) =?= (λx. x)
    (let [tc (mk-tc)
          inner-id (e/lam "y" prop (e/bvar 0) bi)
          ;; λx. (λy.y) x
          lhs (e/lam "x" prop (e/app inner-id (e/bvar 0)) bi)
          ;; λx. x
          rhs (e/lam "x" prop (e/bvar 0) bi)]
      (is (.isDefEq tc lhs rhs)))))

(deftest native-nat-reduction-order-test
  (testing "binary Nat reduction short-circuits before normalizing the right operand"
    (let [reducer (Reducer. (Env.))
          add (Expr/mkConst Name/NAT_ADD clojure.lang.PersistentVector/EMPTY false)
          expr (Expr/app (Expr/app add (Expr/fvar 1)) (Expr/litNat 1))]
      (is (nil? (.tryReduceNatExpr reducer expr)))
      (is (= 1 (get (.getStats reducer) "whnf-calls"))))))

(deftest equiv-manager-lean-semantics-test
  (testing "equivalence uses syntactic level equality, not pointer identity"
    (let [u (name/from-string "u")
          l1 (lvl/param u)
          l2 (lvl/param u)
          em (EquivManager.)]
      (is (not (identical? l1 l2)))
      (is (.isEquiv em (Expr/sort l1 true) (Expr/sort l2 true)))))

  (testing "constant universe arguments are compared structurally"
    (let [u (name/from-string "u")
          cname (name/from-string "C")
          l1 (lvl/param u)
          l2 (lvl/param u)
          c1 (Expr/mkConst cname (object-array [l1]) true)
          c2 (Expr/mkConst cname (object-array [l2]) true)
          em (EquivManager.)]
      (is (.isEquiv em c1 c2))))

  (testing "equivalence ignores binder names and binder info"
    (let [lhs (e/forall' "x" prop prop :default)
          rhs (e/forall' "y" prop prop :implicit)
          em (EquivManager.)]
      (is (.isEquiv em lhs rhs))))

  (testing "equivalence ignores metadata payloads"
    (let [lhs (e/mdata {:source "left"} prop)
          rhs (e/mdata {:source "right"} prop)
          em (EquivManager.)]
      (is (.isEquiv em lhs rhs))))

  (testing "the core equivalence relation ignores projection structure names"
    (let [struct (e/fvar 1)
          lhs (e/proj (name/from-string "S1") 0 struct)
          rhs (e/proj (name/from-string "S2") 0 struct)
          em (EquivManager.)]
      ;; Lean's expression hash includes the projection structure name, so
      ;; callers that enable hash fast-rejection may reject this before core.
      (is (.isEquiv em lhs rhs false)))))

;; ============================================================
;; checkConstantFuelStats returns stats
;; ============================================================

(deftest check-constant-fuel-stats-test
  (testing "checkConstantFuelStats returns stats array"
    (let [env (Env.)
          ;; Add Prop as an axiom first (needed for type checking)
          ;; Actually, we need a well-typed constant.
          ;; An axiom: name, level-params, type
          ;; The simplest: an axiom a : Prop
          ci (env/mk-axiom (name/from-string "myAxiom") [] prop)
          ^objects result (TypeChecker/checkConstantFuelStats env ci 1000000)]
      (is (= 4 (alength result)))
      ;; fuel used
      (is (instance? Long (aget result 0)))
      ;; stats map
      (is (instance? java.util.HashMap (aget result 1)))
      ;; trace array
      (is (.isArray (class (aget result 2))))
      ;; error message (nil on success)
      (is (nil? (aget result 3))))))

;; ============================================================
;; Full replay with fuel stats
;; ============================================================

(deftest replay-with-stats-test
  (testing "Replay Nat.add_succ with checkConstantFuelStats"
    (let [f "test-data/Nat.add_succ.ndjson"]
      (when (.exists (java.io.File. f))
        (let [st (parse-ndjson-file f)
              env (atom (Env.))
              fuel 10000000
              errors (atom 0)]
          (doseq [ci (:decls st)]
            (try
              (if (.isQuot ci)
                (swap! env (fn [^Env current-env]
                             (.addConstant (.enableQuot current-env) ci)))
                (if (or (.isInduct ci) (.isCtor ci) (.isRecursor ci))
                  (do (TypeChecker/checkType ^Env @env ci fuel)
                      (swap! env (fn [^Env current-env]
                                   (.addConstant current-env ci))))
                  (let [^objects result (TypeChecker/checkConstantFuelStats ^Env @env ci fuel)]
                    (swap! env (fn [^Env current-env]
                                 (.addConstant current-env ci)))
                    (when (or (.isThm ci) (.isOpaq ci))
                      (set! (.value ci) nil)))))
              (catch Exception ex
                (swap! errors inc))))
          (is (zero? @errors)))))))

;; ============================================================
;; Admission regressions
;; ============================================================

(deftest reject-ill-typed-definition-test
  (testing "checkConstant rejects definitions whose body only typechecks in infer-only mode"
    (let [f "test-data/init-medium.ndjson"]
      (when (.exists (java.io.File. f))
        (let [st (parse-ndjson-file f)
              env (:env (replay/replay (:decls st)))
              nat (e/const' (name/from-string "Nat") [])
              body (e/app (e/const' (name/from-string "Nat.succ") [])
                          (e/const' (name/from-string "True.intro") []))
              ci (env/mk-def (name/from-string "bad") [] nat body)]
          (is (thrown? Exception
                       (TypeChecker/checkConstant env ci 1000000))))))))

(deftest reject-safe-use-of-unsafe-test
  (testing "safe declarations cannot depend on unsafe constants"
    (let [prop (e/sort' lvl/zero)
          unsafe-ax (env/mk-axiom (name/from-string "u") [] prop :unsafe? true)
          env (TypeChecker/checkConstant (Env.) unsafe-ax 1000000)
          safe-def (env/mk-def (name/from-string "d") [] prop
                               (e/const' (name/from-string "u") [])
                               :safety :safe)]
      (is (thrown? Exception
                   (TypeChecker/checkConstant env safe-def 1000000))))))

(deftest universe-parameter-admission-test
  (testing "checkConstant rejects declaration types that mention undeclared universe params"
    (let [u (name/from-string "u")
          bad-ax (env/mk-axiom (name/from-string "badU") []
                               (e/sort' (lvl/param u)))]
      (is (thrown? Exception
                   (TypeChecker/checkConstant (Env.) bad-ax 1000000)))))

  (testing "checkConstant accepts declaration types that only mention declared universe params"
    (let [u (name/from-string "u")
          good-ax (env/mk-axiom (name/from-string "goodU") [u]
                                (e/sort' (lvl/param u)))]
      (is (instance? Env
                     (TypeChecker/checkConstant (Env.) good-ax 1000000))))))

(deftest positivity-parameter-discipline-test
  (testing "constructors reject recursive occurrences with non-parameter arguments"
    (let [badp-name (name/from-string "BadP")
          ctor-name (name/from-string "BadP.mk")
          alpha-name (name/from-string "alpha")
          beta-name (name/from-string "beta")
          badp-app-alpha (e/app (e/const' badp-name []) (e/bvar 1))
          badp-app-beta (e/app (e/const' badp-name []) (e/bvar 0))
          ind-type (e/forall' alpha-name prop prop bi)
          ctor-type (e/forall' alpha-name prop
                               (e/forall' beta-name prop
                                          (e/forall' "_" badp-app-beta
                                                     badp-app-alpha
                                                     bi)
                                          bi)
                               bi)
          ind-ci (env/mk-induct badp-name [] ind-type
                                :num-params 1
                                :num-indices 0
                                :all [badp-name]
                                :ctors [ctor-name])
          env1 (TypeChecker/checkConstant (Env.) ind-ci 1000000)
          ctor-ci (env/mk-ctor ctor-name [] ctor-type badp-name 0 1 2)]
      (is (thrown? Exception
                   (TypeChecker/checkConstant env1 ctor-ci 1000000))))))
