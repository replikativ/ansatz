(ns ansatz.surface.inferred-forms-test
  "The inferred surface forms the README and tutorial teach — the Init-only half.

  As in Lean, a statement names no types its operands already carry:
  - a 2-arg comparison where a proposition is elaborated (a theorem statement, a
    hypothesis type, a forall body, an argument of type Prop) is the proposition, with
    its carrier read off the operands (binrel%); in code it stays the Bool comparison;
  - the pattern-form `match` infers the inductive type and the result type, and
    recursion is an ordinary call — structural, or with a guessed measure;
  - `(pow x n)` takes x's type (rightact% HPow.hPow).
  Before, `(forall [n Nat] (<= 0 n))` elaborated to `∀ n, Nat.ble 0 n` — a Bool
  computation where the proposition belongs — and tactics failed on it."
  (:require [clojure.test :refer [deftest testing is use-fixtures]]
            [ansatz.core :as a]
            [ansatz.kernel.expr :as e]
            [ansatz.surface.elaborate :as el]))

(defn- init-once [f]
  (binding [a/*verbose* false] (a/load-init!) (f)))

(use-fixtures :once init-once)

(deftest equality-in-proof-lambda-binder
  (is (a/deftheorem equality-lambda [b :- Bool, h :- (= b true)]
        (= b true) (exact ((fn [hh :- (= b true)] hh) h))))
  (is (a/deftheorem nested-equality-lambda [b :- Bool, h :- (= b true)]
        (= b true)
        (exact (((fn [x :- Bool] (fn [hh :- (= x true)] hh)) b) h))))
  (is (a/deftheorem equality-let-annotation [b :- Bool, h :- (= b true)]
        (= b true) (exact (let [hh :- (= b true) h] hh))))
  (is (a/deftheorem equality-forall-annotation [b :- Bool, h :- (= b true)]
        (forall [hh :- (= b true)] (= b true))
        (exact (fn [hh :- (= b true)] hh)))))

(deftest proof-local-let-aliases
  (is (a/deftheorem let-bool [b :- Bool, h :- (Eq Bool b true)]
        (Eq Bool b true)
        (exact (let [part b hp (Eq.trans (Eq.refl part) h)] hp))))
  (is (a/deftheorem let-in-proof-lambda [b :- Bool, h :- (= b true)]
        (= b true)
        (exact ((fn [x :- Bool, hx :- (= x true)]
                  (let [part x hp (Eq.trans (Eq.refl part) hx)] hp)) b h))))
  (is (a/deftheorem nested-proof-lets [b :- Bool, h :- (= b true)]
        (= b true)
        (exact (let [part b]
                 (let [alias part hp (Eq.trans (Eq.refl alias) h)] hp)))))
  (is (a/deftheorem typed-proof-lets [b :- Bool, h :- (= b true)]
        (= b true)
        (exact (let [part :- Bool b]
                 (let [hp :- (= part true) (Eq.trans (Eq.refl part) h)] hp))))))

(deftest local-type-aliases-in-proof-terms
  (is (a/deftheorem local-proposition-alias [b :- Bool, h :- (Eq Bool b true)]
        (Eq Bool b true)
        (exact (let [T (Eq Bool b true)] (let [hp T h] hp)))))
  (is (a/deftheorem local-list-type-alias [xs :- (List Bool)]
        (Eq (List Bool) xs xs)
        (exact (let [T (List Bool)] (Eq.refl ((fn [ys :- T] ys) xs))))))
  (is (thrown-with-msg? clojure.lang.ExceptionInfo #"let value type mismatch"
        (a/theorem incompatible-local-proposition-alias [b :- Bool, h :- (Eq Bool b true)]
          False
          (exact (let [T False] (let [hp T h] hp)))))))

(deftest computational-lambda-body-keeps-bool-comparisons
  (a/defn comparison-lambda [n :- Nat] Bool ((fn [x :- Nat] (= x 1)) n))
  (is (true? (comparison-lambda 1)))
  (is (false? (comparison-lambda 2)))
  (a/defn comparison-proof-binder [n :- Nat, h :- (= n 1)] Bool
    ((fn [hh :- (= n 1)] (= n 1)) h))
  (is (a/deftheorem comparison-proof-binder-true [n :- Nat, h :- (= n 1)]
        (= (comparison-proof-binder n h) true) (simp [comparison-proof-binder h]))))

(defn- elab-str [form]
  (e/->string (el/elaborate (a/env) form)))

(deftest comparison-in-a-statement-is-a-proposition
  (is (re-find #"LE\.le" (elab-str '(forall [n Nat] (<= 0 n)))))
  (is (not (re-find #"Nat\.ble" (elab-str '(forall [n Nat] (<= 0 n))))))
  (is (re-find #"Eq\.\{1\} Int" (elab-str '(forall [x Int] (= (+ x 0) x)))))
  (is (re-find #"LT\.lt" (elab-str '(forall [n Nat] (Not (< n 0))))))
  (a/theorem ifp-le [n :- Nat] (<= 0 n) (omega))
  (a/theorem ifp-hyp [n :- Nat, h :- (<= 1 n)] (<= 1 (+ n n)) (omega))
  (a/theorem ifp-int [x :- Int] (= (+ x 0) x) (simp))
  (a/theorem ifp-not [n :- Nat] (Not (< n 0)) (omega))
  (a/theorem ifp-numerals [] (<= (+ 1 1) 3) (decide)))

(deftest comparison-in-code-stays-bool
  (a/defn ifp-small? [n :- Nat] Bool (< n 3))
  (a/defn ifp-clamp [n :- Nat] Nat (if (< n 3) n 3))
  (is (true? (ifp-small? 2)))
  (is (= 3 (ifp-clamp 7)))
  (a/theorem ifp-small-2 [] (= (ifp-small? 2) true) (rfl)))

(deftest pattern-match-and-direct-recursion
  (a/defn ifp-len [l :- (List Nat)] Nat (match l [nil 0] [(cons hd tl) (+ 1 (ifp-len tl))]))
  (a/defn ifp-lappend [xs :- (List Nat), ys :- (List Nat)] (List Nat)
    (match xs [nil ys] [(cons hd tl) (cons hd (ifp-lappend tl ys))]))
  (is (= 3 (ifp-len '(1 2 3))))
  (is (= '(1 2 3 4) (ifp-lappend '(1 2) '(3 4))))
  (a/theorem ifp-len-nil [] (= (ifp-len nil) 0) (rfl))
  (a/theorem ifp-lappend-nil-right [xs :- (List Nat)]
             (= (ifp-lappend xs nil) xs)
             (induction xs)
             (all_goals (simp_all [ifp-lappend])))
  (a/theorem ifp-app-len [xs :- (List Nat), ys :- (List Nat)]
             (= (ifp-len (ifp-lappend xs ys)) (+ (ifp-len xs) (ifp-len ys)))
             (induction xs) (all_goals (grind "ifp-lappend" "ifp-len"))))

(deftest measure-guessed-for-the-pattern-form
  (testing "the rec-call collector reads the pattern form, so the sizeOf measure is found"
    (a/defn ifp-merge [xs :- (List Nat), ys :- (List Nat)] (List Nat)
      (match xs
        [nil ys]
        [(cons x xs') (match ys
                        [nil (cons x xs')]
                        [(cons y ys') (if (<= x y)
                                        (cons x (ifp-merge xs' (cons y ys')))
                                        (cons y (ifp-merge (cons x xs') ys')))])]))
    (is (= '(1 2 3 4 5 6) (ifp-merge '(1 3 5) '(2 4 6))))
    (a/defn ^Nat ifp-pairs [^{:- (List Nat)} xs]
      (match xs [nil 0] [(cons h t) (match t [nil 0] [(cons h2 t2) (+ 1 (ifp-pairs t2))])]))
    (is (= 2 (ifp-pairs '(1 2 3 4 5))))))

(deftest pow-takes-the-base-type
  (a/defn ifp-sq [n :- Nat] Nat (pow n 2))
  (is (= 49 (ifp-sq 7)))
  (is (re-find #"Nat\.pow" (elab-str '(forall [n Nat] (= (pow n 2) (* n n)))))))

(deftest tactic-types-are-propositions
  (testing "a type given to `have` is elaborated as a type, as in Lean"
    (a/theorem ifp-have [n :- Nat, h :- (<= 1 n)] (<= 1 n)
               (have h2 (<= 1 n) h)
               (exact h2))
    (a/theorem ifp-have-bool [b :- Bool, h :- (= b true)] (= b true)
               (have h2 (= b true) h)
               (exact h2))))
