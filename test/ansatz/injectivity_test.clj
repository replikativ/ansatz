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
            [ansatz.surface.elaborate :as elab]
            [ansatz.fixtures :as fixtures]
            [ansatz.deriving :as deriving]))

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

(use-fixtures :once fixtures/isolated-session with-env)

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

(deftest inj-eq-rewrites-in-simp
  (binding [*ns* (the-ns 'ansatz.injectivity-test) a/*verbose* false]
    (eval '(ansatz.core/theorem inj-t-simp [x :- Nat, y :- Nat, b :- Bool, c :- Bool,
                                            h :- (= InjT (InjT.a x b) (InjT.a y c))]
                                (= Nat x y)
                                (simp at h) (exact (And.left h)))))
  (is (some? (ci "inj-t-simp")) "Lean: simp at h; exact h.1"))

(deftest opt-param-defaults-do-not-fix-fields
  (testing "Lean elimOptParam: `i : optParam Nat n` is a Nat; only `i` is shared, `n` is equated"
    (let [out (ind/define-inductive (a/env) "InjD" [] [['mk '[n Nat i (optParam Nat n)] ['(Nat.succ i)]]]
                :indices '[k Nat])]
      (reset! a/ansatz-env out)
      (a/derive-injectivity! "InjD")
      (is (defeq? (.type (ci "InjD.mk.injEq"))
            '(forall [n :- Nat, i :- Nat, n1 :- Nat]
                     (= Prop (= (InjD (Nat.succ i)) (InjD.mk n i) (InjD.mk n1 i)) (= Nat n n1))))))))

(deftest absences-and-guards
  (testing "nullary and proof-only constructors have neither theorem"
    (doseq [n ["InjT.b.inj" "InjT.b.injEq" "InjOnly.mk.inj" "InjOnly.mk.injEq"]]
      (is (nil? (ci n)) n)))
  (binding [*ns* (the-ns 'ansatz.injectivity-test) a/*verbose* false]
    (eval '(ansatz.core/structure InjCls [α Type] :class true (val α)))
    (eval '(ansatz.core/inductive InjPred [n Nat] :in Prop (mk [h (= Nat n n)]))))
  (is (nil? (ci "InjCls.mk.inj")) "a class has none (MutualInductive.lean: unless isClass)")
  (is (nil? (ci "InjPred.mk.inj")) "an inductive predicate has none"))

(deftest a-failure-fails-the-declaration
  (let [before @a/ansatz-env]
    (reset! a/ansatz-env (env/check-constant (a/env) (env/mk-axiom (name/from-string "InjC.b.injEq") []
                                                                   (e/const' (name/from-string "True") []))))
    (try
      (binding [*ns* (the-ns 'ansatz.injectivity-test) a/*verbose* false]
        (is (thrown-with-msg? clojure.lang.ExceptionInfo #"injectivity theorems for InjC"
                              (eval '(ansatz.core/inductive InjC [] (a [x Nat]) (b [y Nat]))))))
      (is (nil? (ci "InjC")) "nothing of the declaration stays installed")
      (is (nil? (ci "InjC.a.inj")))
      (finally (reset! a/ansatz-env before)))))

(deftest deriving-handlers-see-the-theorems
  (let [seen (atom nil)]
    (deriving/register-handler! 'InjProbe (fn [env type-name _] (reset! seen (some? (env/lookup env (name/from-string (str type-name ".mk.inj"))))) env))
    (binding [*ns* (the-ns 'ansatz.injectivity-test) a/*verbose* false]
      (eval '(ansatz.core/inductive InjDer [] (mk [x Nat]) :deriving [InjProbe])))
    (is (true? @seen) "Lean installs injectivity before running deriving handlers")))
