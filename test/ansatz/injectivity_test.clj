(ns ansatz.injectivity-test
  "Constructor injectivity theorems (Lean Meta/Injective.lean) for DSL inductives and structures.
   Lean parity: test/lean-parity/dsl/injectivity.lean (observed with Lean v4.36.0)."
  (:require [clojure.test :refer [deftest testing is use-fixtures]]
            [ansatz.test-env :as test-env]
            [ansatz.core :as a]
            [ansatz.inductive :as ind]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.tc :as tc]
            [ansatz.surface.elaborate :as elab]))

(defn- with-env [f]
  (let [saved @a/ansatz-env]
    (try (reset! a/ansatz-env @test-env/bundled-init-env)
         (binding [*ns* (the-ns 'ansatz.injectivity-test) a/*verbose* false]
           (run! eval '[(ansatz.core/inductive InjT [] (a [x Nat] [y Bool]) (b))
                        (ansatz.core/structure InjPos [] (n Nat) (h (< 0 n)))
                        (ansatz.core/inductive InjS [] (mk [n Nat] [f (Fin n)]))
                        (ansatz.core/inductive InjOnly [] (mk [h True]))])
           (reset! a/ansatz-env (ind/define-inductive (a/env) "InjV" '[α Type]
                                  [['nil [] [0]] ['cons '[n Nat x α xs (InjV α n)] ['(Nat.succ n)]]]
                                  :indices '[k Nat]))
           (a/derive-injectivity! "InjV")
           (f))
         (finally (reset! a/ansatz-env saved)))))

(use-fixtures :once with-env)

(defn- ci [n] (env/lookup (a/env) (name/from-string n)))
(defn- infos [t] (loop [t t acc []] (if (e/forall? t) (recur (e/forall-body t) (conj acc (e/forall-info t))) acc)))
(defn- defeq? [actual form] (tc/is-def-eq (tc/mk-tc-state (a/env)) actual (elab/elaborate (a/env) form)))

(deftest inj-and-inj-eq-shapes
  (testing "T.a: an implication with implicit binders, and an equation of propositions"
    (is (defeq? (.type (ci "InjT.a.inj"))
          '(forall [x :- Nat, y :- Bool, x1 :- Nat, y1 :- Bool, h :- (= InjT (InjT.a x y) (InjT.a x1 y1))]
                   (And (= Nat x x1) (= Bool y y1)))))
    (is (= [:implicit :implicit :implicit :implicit :default] (infos (.type (ci "InjT.a.inj")))))
    (is (defeq? (.type (ci "InjT.a.injEq"))
          '(forall [x :- Nat, y :- Bool, x1 :- Nat, y1 :- Bool]
                   (= Prop (= InjT (InjT.a x y) (InjT.a x1 y1)) (And (= Nat x x1) (= Bool y y1))))))
    (is (= [:default :default :default :default] (infos (.type (ci "InjT.a.injEq"))))))
  (testing "a fixed index is shared; the remaining fields are equated"
    (is (defeq? (.type (ci "InjV.cons.injEq"))
          '(forall [α :- Type, n :- Nat, x :- α, xs :- (InjV α n), x1 :- α, xs1 :- (InjV α n)]
                   (= Prop (= (InjV α (Nat.succ n)) (InjV.cons n x xs) (InjV.cons n x1 xs1))
                      (And (= α x x1) (= (InjV α n) xs xs1)))))))
  (testing "a proof field contributes no equation"
    (is (defeq? (.type (ci "InjPos.mk.injEq"))
          '(forall [n :- Nat, h :- (< 0 n), n1 :- Nat, h1 :- (< 0 n1)]
                   (= Prop (= InjPos (InjPos.mk n h) (InjPos.mk n1 h1)) (= Nat n n1))))))
  (testing "a field whose type differs gets HEq"
    (is (defeq? (.type (ci "InjS.mk.injEq"))
          '(forall [n :- Nat, f :- (Fin n), n1 :- Nat, f1 :- (Fin n1)]
                   (= Prop (= InjS (InjS.mk n f) (InjS.mk n1 f1)) (And (= Nat n n1) (HEq f f1)))))))
  (testing "only proof fields: no injectivity theorems; nullary constructors neither"
    (is (nil? (ci "InjOnly.mk.inj")))
    (is (nil? (ci "InjT.b.inj")))))

(deftest theorems-are-kernel-checked-and-inj-eq-is-simp
  (doseq [n ["InjT.a.inj" "InjT.a.injEq" "InjV.cons.inj" "InjV.cons.injEq" "InjPos.mk.inj" "InjPos.mk.injEq"
             "InjS.mk.inj" "InjS.mk.injEq"]]
    (is (.isThm (ci n)) n)
    (is (env/verifies? (a/env) (.type (ci n)) (.value (ci n))) n))
  (is (contains? (env/get-extension (a/env) :simp-lemmas #{}) "InjT.a.injEq"))
  (is (not (contains? (env/get-extension (a/env) :simp-lemmas #{}) "InjT.a.inj")))
  (binding [*ns* (the-ns 'ansatz.injectivity-test) a/*verbose* false]
    (eval '(ansatz.core/theorem inj-t-uses-inj [x :- Nat, y :- Nat, b :- Bool, c :- Bool,
                                                h :- (= InjT (InjT.a x b) (InjT.a y c))]
                                (= Nat x y)
                                (exact (And.left (InjT.a.inj h))))))
  (is (some? (ci "inj-t-uses-inj"))))
