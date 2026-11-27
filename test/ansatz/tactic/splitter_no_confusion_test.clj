(ns ansatz.tactic.splitter-no-confusion-test
  "The equation simplification of the matcher splitter (basic/unify-eq, Lean injectionCore) goes
   through the shared AppBuilder.mkNoConfusion: indexed families, heterogeneous majors, and proof
   fields that contribute no equality. Lean parity: test/lean-parity/dsl/splitter_no_confusion.lean."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [ansatz.core :as a]
            [ansatz.config :as config]
            [ansatz.inductive :as ind]
            [ansatz.surface.elaborate :as elab]
            [ansatz.tactic.basic :as basic]
            [ansatz.tactic.extract :as extract]
            [ansatz.tactic.proof :as proof]
            [ansatz.test-env :as test-env]))

(def ^:private unify-log (atom []))

(defn- with-env [f]
  (let [saved @a/ansatz-env]
    (try
      (reset! a/ansatz-env @test-env/bundled-init-env)
      (binding [a/*verbose* false]
        ;; D α : Nat → Type with both constructors at index (n+1), as in the parity file
        (ind/define-inductive (a/env) "SplD" '[α Type]
          [['a '[n Nat x α] ['(Nat.succ n)]] ['b '[n Nat x α y α] ['(Nat.succ n)]]] :indices '[k Nat])
        (ind/define-inductive (a/env) "SplP" [] [['mk '[n Nat h (< 0 n)]]]))
      (a/register-tactic! 'unify-h
                          (fn [ps _]
                            (let [g (proof/current-goal ps)
                                  hid (some (fn [[id d]] (when (= "h" (str (:name d))) id)) (:lctx g))
                                  r (basic/unify-eq ps hid)]
                              (swap! unify-log conj (select-keys r [:status :num-new-eqs]))
                              (:ps r))))
      (f)
      (finally (reset! a/ansatz-env saved)))))

(use-fixtures :once with-env)

(defn- prove [params target tactics]
  (reset! unify-log [])
  (binding [a/*verbose* false]
    (a/prove-theorem (gensym "splitter_nc_") params target tactics))
  @unify-log)

(deftest different-constructors-of-an-indexed-family
  (testing "noConfusion_of_Nat over SplD.ctorIdx applied to the parameter AND the index"
    (is (= [{:status :solved :num-new-eqs 0}]
           (prove '[x :- Nat, y :- Nat, z :- Nat, h :- (= (SplD Nat 1) (SplD.a 0 x) (SplD.b 0 y z))]
                  'False '[(unify-h)])))))

(deftest same-constructor-of-an-indexed-family
  (testing "the per-constructor noConfusion takes the index equality and `heq_of_eq h`"
    (is (= [{:status :continue :num-new-eqs 2}]
           (prove '[x :- Nat, y :- Nat, h :- (= (SplD Nat 1) (SplD.a 0 x) (SplD.a 0 y))]
                  '(= Nat x y) '[(unify-h) (intro hn hx) (exact (eq_of_heq hx))])))))

(deftest proof-fields-contribute-no-equality
  (testing "Lean injectionCore: numFields - getCtorNumPropFields new equalities"
    (is (= [{:status :continue :num-new-eqs 1}]
           (prove '[n :- Nat, m :- Nat, hn :- (< 0 n), hm :- (< 0 m), h :- (= SplP (SplP.mk n hn) (SplP.mk m hm))]
                  '(= Nat n m) '[(unify-h) (intro e) (exact e)])))))

(deftest nat-constructors
  (is (= [{:status :continue :num-new-eqs 1}]
         (prove '[n :- Nat, m :- Nat, h :- (= Nat (Nat.succ n) (Nat.succ m))] '(= Nat n m)
                '[(unify-h) (intro e) (exact e)])))
  (is (= [{:status :solved :num-new-eqs 0}]
         (prove '[n :- Nat, h :- (= Nat (Nat.succ n) 0)] 'False '[(unify-h)]))))

(deftest split-on-an-indexed-family
  (testing "`split` on a match over SplD simplifies its branch equations and verifies"
    (binding [a/*verbose* false config/*lean-matchers* true]
      (a/define-verified 'spl-tag '[d :- (SplD Nat 1)] 'Nat '(match d (SplD.a n x) 0 (SplD.b n x y) x))
      (let [ty (elab/elaborate (a/env) '(forall [x :- Nat, y :- Nat, f :- (=> Nat Nat)]
                                                (= (spl-tag (SplD.b 0 (f x) y)) (spl-tag (SplD.b 0 (f x) y)))))
            [ps _] (proof/start-proof (a/env) ty)
            ps (-> ps (basic/intros ["x" "y" "f"]) (a/run-tactic '(unfold spl-tag)))
            ps (a/run-tactic ps '(split))]
        (is (= 1 (count (proof/goals ps))) "the SplD.a branch is impossible")
        (is (some? (extract/verify (basic/all-goals ps #(a/run-tactic % '(rfl))))))))))
