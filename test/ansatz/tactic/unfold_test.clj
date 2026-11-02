(ns ansatz.tactic.unfold-test
  "`unfold` follows Lean `Meta.unfoldTarget` (Meta/Tactic/Unfold.lean): a non-recursive
   definition is delta-expanded (`deltaExpand`) at every occurrence and head-beta-reduced,
   and nothing else is unfolded, so calls to other definitions stay folded.
   Lean counterpart: test/lean/unfold.lean."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [ansatz.core :as a]))

(use-fixtures :once (fn [t]
                      (a/load-init!)
                      ;; eval resolves the a/ alias in *ns*, which is not this namespace at test time
                      (binding [a/*verbose* false *ns* (the-ns 'ansatz.tactic.unfold-test)] (t))))

(defn- proves? [form]
  (try (eval form) true
       (catch Throwable t (or (.getMessage t) (str (class t))))))

(deftest unfold-keeps-recursive-callees-folded
  (eval '(a/structure UnfoldSt [] (hs (List Nat)) (es (List Nat))))
  (eval '(a/defn unfold-hcov [hs :- (List Nat), es :- (List Nat)] Bool
           (match hs [nil true] [(cons h t) (Bool.and (Nat.beq h 0) (unfold-hcov t es))])))
  (eval '(a/defn unfold-wrap [s :- UnfoldSt] Bool (unfold-hcov (:hs s) (:es s))))
  (testing "after unfolding the wrapper the callee is still syntactically present: rw finds it"
    (is (true? (proves? '(a/theorem unfold-wrap-of-hcov
                           [f :- (=> UnfoldSt UnfoldSt), s :- UnfoldSt,
                            h :- (= Bool (unfold-hcov (:hs (f s)) (:es (f s))) true)]
                           (= Bool (unfold-wrap (f s)) true)
                           (unfold unfold-wrap) (rw [h]))))))
  (testing "exact with the folded callee's type closes the unfolded goal"
    (is (true? (proves? '(a/theorem unfold-wrap-exact [xs :- (List Nat), ys :- (List Nat),
                                                       h :- (= Bool (unfold-hcov xs ys) true)]
                           (= Bool (unfold-wrap (UnfoldSt.mk xs ys)) true)
                           (unfold unfold-wrap) (exact h)))))))

(deftest unfold-reaches-occurrences-under-binders
  (eval '(a/defn unfold-twice [n :- Nat] Nat (+ n n)))
  (is (true? (proves? '(a/theorem unfold-twice-forall []
                         (forall [n :- Nat] (= Nat (unfold-twice n) (+ n n)))
                         (unfold unfold-twice) (intro n) (rfl))))))

(deftest unfold-without-occurrence-fails
  (eval '(a/defn unfold-twice2 [n :- Nat] Nat (+ n n)))
  (let [r (proves? '(a/theorem unfold-nothing [n :- Nat] (= Nat n n) (unfold unfold-twice2) (rfl)))]
    (is (string? r))
    (is (re-find #"failed to unfold unfold-twice2" r))))

(deftest unfold-recursive-definition-still-reduces
  (eval '(a/defn unfold-rec [xs :- (List Nat)] Bool
           (match xs [nil true] [(cons h t) (unfold-rec t)])))
  (is (true? (proves? '(a/theorem unfold-rec-nil [] (= Bool (unfold-rec (List.nil Nat)) true)
                         (unfold unfold-rec) (rfl))))))
