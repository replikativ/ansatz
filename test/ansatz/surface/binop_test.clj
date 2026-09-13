(ns ansatz.surface.binop-test
  "Type-directed arithmetic (#78) — the Init-only half.

  Lean elaborates arithmetic through `binop%`: it reads the operand tree's type and emits the
  heterogeneous class operator, with numeric literals becoming `OfNat.ofNat T n inst`. The
  Mathlib half (`(mul Real …)`, `OfNat` at a field) is exercised by
  `ansatz.theory.convergence-test`; here we pin the parts a plain Init env can see — the
  Nat/Int fast path, n-ary folding, and the `apply` that has to bridge a goal carrying the
  concrete kernel op to a lemma stated with `+`."
  (:require [clojure.test :refer [deftest testing is use-fixtures]]
            [ansatz.core :as a]
            [ansatz.kernel.expr :as e]
            [ansatz.surface.elaborate :as el]
            [ansatz.kernel.env]
            [ansatz.kernel.name]))

(defn- init-once [f]
  (binding [a/*verbose* false] (a/load-init!) (f)))

(use-fixtures :once init-once)

(defn- elab-str [form]
  (e/->string (el/elaborate (a/env) form)))

(deftest explicit-type-arithmetic-on-nat
  (testing "(op T a b) takes the concrete kernel op for the types that have one"
    (is (re-find #"Nat\.mul" (elab-str '(forall [a Nat b Nat] (= Nat (mul Nat a b) a)))))
    (is (re-find #"Nat\.add" (elab-str '(forall [a Nat b Nat] (= Nat (add Nat a b) a)))))
    (is (re-find #"Nat\.sub" (elab-str '(forall [a Nat b Nat] (= Nat (sub Nat a b) a)))))
    (is (re-find #"Nat\.div" (elab-str '(forall [a Nat b Nat] (= Nat (div Nat a b) a)))))
    (is (re-find #"Nat\.pow" (elab-str '(forall [a Nat b Nat] (= Nat (pow Nat a b) a))))))
  (testing "and agrees with the operator spelling"
    (is (= (elab-str '(forall [a Nat b Nat] (= Nat (mul Nat a b) a)))
           (elab-str '(forall [a Nat b Nat] (= Nat (* a b) a)))))))

(deftest nary-arithmetic-folds-left
  (binding [a/*verbose* false]
    (a/defn sum3 [a Nat b Nat c Nat] Nat (+ a b c))
    (is (= 6 (sum3 1 2 3)))
    (a/defn diff3 [a Nat b Nat c Nat] Nat (- a b c))
    (is (= 5 (diff3 10 2 3)))))

(deftest explicit-type-forms-do-not-shadow-real-names
  (testing "`mul`/`add`/... are ordinary identifiers: a definition of that name still applies"
    ;; wandler's semiring surface defines several of these, so the (op T a b) forms fire only on
    ;; that exact shape and only when the name resolves to nothing. The env is restored
    ;; afterwards — these definitions would otherwise shadow `mul`/`add` for every later test.
    (let [saved @a/ansatz-env]
      (try
        (binding [a/*verbose* false]
          (a/defn mul [a Nat b Nat] Nat (* a b))
          (a/defn add [a Nat b Nat] Nat (+ a b))
          (is (= 12 (mul 3 4)))
          (is (= 7 (add 3 4)))
          (is (re-find #"mul" (elab-str '(forall [a Nat b Nat] (= Nat (mul a b) a))))))
        (finally (reset! a/ansatz-env saved))))))

(deftest apply-bridges-kernel-op-and-class-operator
  (testing "the goal carries Nat.add (our surface's Nat fast path), the Init lemma is stated
            with HAdd — lazy delta reduction has to walk them to a common head"
    (binding [a/*verbose* false]
      (a/prove-theorem 'le-add-one '[n :- Nat]
                       '(<= Nat n (+ n 1))
                       '[(apply Nat.le_add_right)])
      (is (some? (ansatz.kernel.env/lookup (a/env)
                                           (ansatz.kernel.name/from-string "le-add-one")))))))
