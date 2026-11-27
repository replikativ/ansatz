(ns ansatz.universe-inference-test
  "The result universe of a DSL inductive (Lean Elab/MutualInductive.lean inferResultingUniverse,
   isPropCandidate). Lean parity: test/lean-parity/dsl/universe_inference.lean."
  (:require [clojure.test :refer [deftest testing is]]
            [ansatz.test-env :as test-env]
            [ansatz.core :as a]
            [ansatz.inductive :as ind]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.name :as name]))

(defn- define [n ps cs & opts]
  (let [saved @a/ansatz-env]
    (try (binding [a/*verbose* false]
           (let [out (apply ind/define-inductive @test-env/bundled-init-env n ps cs opts)]
             (env/lookup out (name/from-string n))))
         (finally (reset! a/ansatz-env saved)))))

(defn- result-level [ci]
  (loop [t (.type ci)] (if (e/forall? t) (recur (e/forall-body t)) (e/sort-level t))))

(defn- level= [a b] (lvl/level= (lvl/simplify a) (lvl/simplify b)))

(def ^:private u (lvl/param (name/from-string "u")))
(def ^:private v (lvl/param (name/from-string "v")))
(defn- type-of [l] (lvl/succ l))

(deftest inferred-from-the-fields
  (testing "a field `α : Type` needs `Type 1`"
    (let [ci (define "UCarrier" [] [['mk '[α Type]]])]
      (is (level= (type-of (lvl/succ lvl/zero)) (result-level ci)))))
  (testing "a parameter that no field uses does not raise the universe"
    (let [ci (define "UPhantom" '[α (Type u)] [['mk []]])]
      (is (level= (type-of lvl/zero) (result-level ci)))
      (is (= ["u"] (mapv str (.levelParams ci))))))
  (testing "a field `x : α` with `α : Type u` gives `Type u`; two give their max"
    (is (level= (type-of u) (result-level (define "UBox" '[α (Type u)] [['mk '[x α]]]))))
    (is (level= (type-of (lvl/level-max u v))
                (result-level (define "UMix" '[α (Type u) β (Type v)] [['mk '[a α b β]]])))))
  (testing "a recursive field imposes nothing"
    (is (level= (type-of u) (result-level (define "UList" '[α (Type u)] [['nil []] ['cons '[h α t (UList α)]]])))))
  (testing "a nested occurrence unifies with the result universe"
    (is (level= (type-of lvl/zero) (result-level (define "URose" [] [['node '[cs (List URose)]]]))))
    (is (level= (type-of u) (result-level (define "URoseP" '[α (Type u)] [['node '[a α cs (List (URoseP α))]]])))))
  (testing "a universe of a field type generalizes the declaration"
    (let [ci (define "UPick" [] [['mk '[α (Type u) x α]]])]
      (is (= ["u"] (mapv str (.levelParams ci))))
      (is (level= (type-of (lvl/succ u)) (result-level ci))))))

(deftest prop-candidates-and-exceptions
  (testing "one constructor whose fields are all proofs: Prop"
    (is (lvl/level-zero? (result-level (define "ULaw" '[p Prop] [['mk '[h p]]]))))
    (is (lvl/level-zero? (result-level (define "UPS" '[p Prop q Prop] [['mk '[hp p hq q]]])))))
  (testing "two constructors, an empty type, a fieldless type: Type"
    (is (level= (type-of lvl/zero) (result-level (define "UTwo" '[p Prop] [['a '[h p]] ['b '[h p]]]))))
    (is (level= (type-of lvl/zero) (result-level (define "UEmpty" [] []))))
    (is (level= (type-of lvl/zero) (result-level (define "UEnum" [] [['a []] ['b []]]))))
    (is (level= (type-of lvl/zero) (result-level (define "UUnit" [] [['mk []]])))))
  (testing "an explicit result sort is kept"
    (is (level= (type-of (lvl/succ lvl/zero)) (result-level (define "UExpl" [] [['mk '[n Nat]]] :in '(Type 1)))))
    (is (level= (type-of lvl/zero) (result-level (define "UExplType" '[p Prop] [['mk '[h p]]] :in 'Type))))))
