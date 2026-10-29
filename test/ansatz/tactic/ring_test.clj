(ns ansatz.tactic.ring-test
  (:require [clojure.test :refer [deftest is testing]]
            [ansatz.core :as a]
            [ansatz.test-env :as test-env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]
            [ansatz.meta.constructions.util :as u]
            [ansatz.tactic.basic :as basic]
            [ansatz.tactic.extract :as extract]
            [ansatz.tactic.proof :as proof]
            [ansatz.tactic.ring :as ring]))

(defn- c [n] (e/const' (name/from-string n) []))
(defn- binary [n a b] (e/app* (c n) a b))
(defn- eq [type a b] (e/app* (e/const' (name/from-string "Eq") [(lvl/succ lvl/zero)]) type a b))
(defn- checked-proof [environment type names]
  (let [[ps _] (proof/start-proof environment type)
        ps (basic/intros ps names)
        ps (ring/ring ps)]
    (is (proof/solved? ps))
    (let [term (extract/extract ps)]
      (is (env/verifies? environment type term))
      term)))

(deftest klara-horner-reproduction-has-a-checked-semiring-certificate
  (let [saved @a/ansatz-env]
    (try
      (reset! a/ansatz-env @test-env/checked-bundled-init-env)
      (a/prove-theorem 'klaraRingProbe '[a :- Nat, b :- Nat, c :- Nat, x :- Nat]
                       '(= Nat (+ a (+ (* x b) (* (* x x) c))) (+ a (* x (+ b (* x c))))) '[(ring)])
      (let [ci (env/lookup! (a/env) (name/from-string "klaraRingProbe"))]
        (is (env/verifies? (a/env) (.type ci) (.value ci)))
        (is (.contains (e/->string (.value ci)) "Lean.Grind.CommRing.eq_normS")))
      (finally (reset! a/ansatz-env saved)))))

(deftest symbolic-coefficients-powers-and-opaque-nat-subtraction
  (let [environment @test-env/checked-bundled-init-env
        ctx (u/context environment)
        nat (c "Nat")
        x (u/local-decl ctx "x" nat)
        y (u/local-decl ctx "y" nat)
        add #(binary "Nat.add" %1 %2)
        mul #(binary "Nat.mul" %1 %2)
        pow #(binary "Nat.pow" %1 (e/lit-nat %2))
        sub #(binary "Nat.sub" %1 %2)
        claims [[(add x x) (mul (e/lit-nat 2) x)]
                [(mul (add x y) (add x y))
                 (add (add (pow x 2) (mul (e/lit-nat 2) (mul x y))) (pow y 2))]
                [(add (sub x y) x) (add x (sub x y))]
                [(mul (e/lit-nat 100000000000000000000N) (add x y))
                 (add (mul (e/lit-nat 100000000000000000000N) x)
                      (mul (e/lit-nat 100000000000000000000N) y))]
                [(e/let' "t" nat (add x y) (mul (e/bvar 0) x))
                 (add (mul x x) (mul y x))]]]
    (doseq [[lhs rhs] claims]
      (checked-proof environment (u/mk-forall-fvars ctx [x y] (eq nat lhs rhs)) ["x" "y"]))
    (testing "truncated Nat subtraction is never reified as ring subtraction"
      (let [type (u/mk-forall-fvars ctx [x y] (eq nat (sub x y) (e/lit-nat 0)))
            [ps _] (proof/start-proof environment type)
            ps (basic/intros ps ["x" "y"])]
        (is (thrown-with-msg? clojure.lang.ExceptionInfo #"could not certify" (ring/ring ps)))
        (is (= 1 (count (proof/goals ps))))))))

(deftest signed-integer-polynomial-certificate
  (let [environment @test-env/checked-bundled-init-env
        ctx (u/context environment)
        int (c "Int")
        x (u/local-decl ctx "x" int)
        y (u/local-decl ctx "y" int)
        add #(binary "Int.add" %1 %2)
        mul #(binary "Int.mul" %1 %2)
        neg #(e/app (c "Int.neg") %)
        lhs (mul (add x y) (add x (neg y)))
        rhs (add (mul x x) (neg (mul y y)))
        term (checked-proof environment
                            (u/mk-forall-fvars ctx [x y] (eq int lhs rhs)) ["x" "y"])]
    (is (.contains (e/->string term) "Lean.Grind.CommRing.Expr.eq_of_toPoly_eq"))))

(deftest generic-algebra-instances-and-universes
  (doseq [level [lvl/zero (lvl/succ lvl/zero)]
          ring? [false true]]
    (let [environment @test-env/checked-bundled-init-env
          ctx (u/context environment)
          call (fn [n & args]
                 (apply e/app* (e/const' (name/from-string n) [level]) args))
          R (u/local-decl ctx "R" (e/sort' (lvl/succ level)))
          s (u/local-decl ctx "s" (call (if ring? "Lean.Grind.CommRing"
                                            "Lean.Grind.CommSemiring") R))
          x (u/local-decl ctx "x" R) y (u/local-decl ctx "y" R) z (u/local-decl ctx "z" R)
          ring (when ring? (call "Lean.Grind.CommRing.toRing" R s))
          semiring (if ring? (call "Lean.Grind.Ring.toSemiring" R ring)
                       (call "Lean.Grind.CommSemiring.toSemiring" R s))
          op (fn [field cls operation]
               (let [instance (call cls R (call field R semiring))]
                 (e/app* (e/const' (name/from-string operation) [level level level]) R R R instance)))
          plus (op "Lean.Grind.Semiring.toAdd" "instHAdd" "HAdd.hAdd")
          times (op "Lean.Grind.Semiring.toMul" "instHMul" "HMul.hMul")
          add #(e/app* plus %1 %2) mul #(e/app* times %1 %2)
          neg (when ring? (call "Neg.neg" R (call "Lean.Grind.Ring.toNeg" R ring)))
          lhs (mul x (add y (if ring? (e/app neg z) z)))
          rhs (add (mul x y) (if ring? (e/app neg (mul x z)) (mul x z)))
          goal (e/app* (e/const' (name/from-string "Eq") [(lvl/succ level)]) R lhs rhs)]
      (checked-proof environment (u/mk-forall-fvars ctx [R s x y z] goal)
                     ["R" "s" "x" "y" "z"]))))

(deftest opaque-binary-functions-do-not-acquire-ring-laws
  (let [environment @test-env/checked-bundled-init-env
        ctx (u/context environment)
        nat (c "Nat")
        f (u/local-decl ctx "f" (e/forall' "x" nat (e/forall' "y" nat nat :default) :default))
        x (u/local-decl ctx "x" nat) y (u/local-decl ctx "y" nat)
        type (u/mk-forall-fvars ctx [f x y] (eq nat (e/app* f x y) (e/app* f y x)))
        [ps _] (proof/start-proof environment type)
        ps (basic/intros ps ["f" "x" "y"])]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"could not certify" (ring/ring ps)))
    (is (= 1 (count (proof/goals ps))))))

(deftest generic-carrier-with-max-universe
  (let [environment @test-env/checked-bundled-init-env
        ctx (u/context environment)
        un (name/from-string "u") vn (name/from-string "v")
        ul (lvl/param un) vl (lvl/param vn)
        level (lvl/level-max ul vl)
        raw-sort (lvl/level-max (lvl/succ ul) (lvl/succ vl))
        R (u/local-decl ctx "R" (e/sort' raw-sort))
        call (fn [n & args] (apply e/app* (e/const' (name/from-string n) [level]) args))
        s (u/local-decl ctx "s" (call "Lean.Grind.CommSemiring" R))
        x (u/local-decl ctx "x" R) y (u/local-decl ctx "y" R)
        semiring (call "Lean.Grind.CommSemiring.toSemiring" R s)
        add (e/app* (e/const' (name/from-string "HAdd.hAdd") [level level level]) R R R
                    (call "instHAdd" R (call "Lean.Grind.Semiring.toAdd" R semiring)))
        goal (e/app* (e/const' (name/from-string "Eq") [(lvl/succ level)]) R
                     (e/app* add x y) (e/app* add y x))
        type (u/mk-forall-fvars ctx [R s x y] goal)
        [ps _] (proof/start-proof environment type)
        ps (ring/ring (basic/intros ps ["R" "s" "x" "y"]))]
    (is (proof/solved? ps))
    (is (some? (env/check-constant environment
                                   (env/mk-thm (name/from-string "maxUniverseRingProof")
                                               [un vn] type (extract/extract ps)))))))
