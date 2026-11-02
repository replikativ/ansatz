(ns ansatz.bundled-init-test
  "Zero-setup usability: `(a/init!)` with NO arguments loads the bundled medium Init tier
   (Lean 4.33.1 `Init` declarations) straight from the jar/classpath resource — no durable
   store to build — and that's enough for ordinary verified `defn` over Nat/List/Bool. This
   is what makes ansatz usable the moment you add the dependency. Fixture-free (the tier
   ships in the jar), so it belongs in the default CI unit suite."
  (:require [clojure.test :refer [deftest is testing]]
            [ansatz.core :as a]))

(deftest bundled-medium-init-is-usable
  (binding [a/*verbose* false]
    (testing "(init!) loads the bundled medium tier from the classpath"
      (is (= :medium (a/init!)))
      (is (<= 2900 (.size ^ansatz.kernel.Env @a/ansatz-env))
          "the bundled Init declarations are admitted (TRUST mode)"))
    (testing "an ordinary verified function over the bundled tier elaborates, certifies, and runs"
      (eval '(ansatz.core/defn ^{:- Nat} bundled-dbl [^{:- Nat} x] (Nat.add x x)))
      (is (= 42 (long ((resolve 'bundled-dbl) 21)))))))

(deftest bundled-public-reasoning-lemmas
  ;; Lean Init/Data/{Bool,Option/{Basic,Lemmas},List/Lemmas,Nat/Basic}.lean;
  ;; paired closed uses in test/lean/bundled_public_lemmas.lean.
  (binding [a/*verbose* false]
    (a/load-init!)
    (doseq [[nm params target term]
            [['bundled_false_ne_true '[] '(Not (= false true)) 'Bool.false_ne_true]
             ['bundled_bool_cases '[b :- Bool] '(Or (= b true) (= b false)) '(Bool.eq_false_or_eq_true b)]
             ['bundled_eq_false '[b :- Bool] '(Iff (= b false) (Not (= b true))) 'Bool.eq_false_iff]
             ['bundled_ne_false '[b :- Bool] '(Iff (Not (= b false)) (= b true)) 'Bool.ne_false_iff]
             ['bundled_some_ne_none '[x :- Nat] '(Not (= (Option.some x) (Option.none Nat))) '(Option.some_ne_none x)]
             ['bundled_cons_ne_nil '[x :- Nat, xs :- (List Nat)]
              '(Not (= (List.cons x xs) (List.nil Nat))) '(List.cons_ne_nil x xs)]
             ['bundled_zero_ne_add_one '[n :- Nat] '(Not (= 0 (+ n 1))) '(Nat.zero_ne_add_one n)]
             ['bundled_map_map '[f :- (=> Nat Nat), g :- (=> Nat Nat), xs :- (List Nat)]
              '(= (List.map g (List.map f xs)) (List.map (fn [x :- Nat] (g (f x))) xs)) 'List.map_map]
             ['bundled_map_some '[f :- (=> Nat Nat), x :- Nat]
              '(= (Option.map f (Option.some x)) (Option.some (f x))) '(Option.map_some x f)]
             ['bundled_map_none '[f :- (=> Nat Nat)]
              '(= (Option.map f (Option.none Nat)) (Option.none Nat)) '(Option.map_none f)]]]
      (a/prove-theorem nm params target [(list 'exact term)])
      (is true (str nm)))))
