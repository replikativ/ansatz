(ns ansatz.tactic.nat-equations-test
  "Nat constructor equations and offset keys; Lean pair: test/lean/nat_equations.lean."
  (:require [clojure.test :refer [deftest is use-fixtures]]
            [ansatz.core :as a]
            [ansatz.eqns :as eqns]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.tc :as tc]
            [ansatz.tactic.discr-tree :as dt]
            [ansatz.tactic.proof :as proof]
            [ansatz.tactic.basic :as basic]
            [ansatz.tactic.simp :as simp]))

(defn- c [n] (e/const' (name/from-string n) []))
(defn- add [n k] (#'dt/mk-add-nat n (e/lit-nat k)))

(use-fixtures :once
  (fn [t]
    (a/load-init!)
    (binding [a/*verbose* false *ns* (the-ns 'ansatz.tactic.nat-equations-test)]
      (eval '(a/defn offset-loop [n :- Nat, acc :- Nat] Nat
               (match n [zero acc] [(succ k) (offset-loop k (+ acc 1))])))
      (eval '(a/defn offset-count [n :- Nat] Nat
               (match n [zero 0] [(succ k) (Nat.succ (offset-count k))])))
      (eval '(a/defn offset-pair [n :- Nat, acc :- Nat] Nat
               (match n [zero acc]
                      [(succ k) (match k [zero (+ acc 1)]
                                       [(succ j) (offset-pair j (+ acc 2))])])))
      (eval '(a/defn offset-list [xs :- (List Nat), acc :- Nat] Nat
               (match xs [nil acc] [(cons x tail) (offset-list tail (+ acc x))])))
      (t))))

(defn- transformed-argument
  ([expr transform] (transformed-argument expr transform {}))
  ([expr transform extra-lctx]
  ;; Inspect P's argument: reflexivity cannot hide a missing equation rewrite.
   (let [nat (c "Nat")
         lctx {100 {:tag :local :id 100 :name "n" :type nat}
               101 {:tag :local :id 101 :name "a" :type nat}
               102 {:tag :local :id 102 :name "P" :type (e/arrow nat (e/sort' lvl/zero))}}
         lctx (merge lctx extra-lctx)
         [ps _] (proof/start-proof (a/env) (e/app (e/fvar 102) expr))
         goal (proof/current-goal ps)
         ps (assoc-in ps [:meta-mctx :decls (:id goal) :lctx] lctx)
         ps (transform ps)]
     (e/app-arg (:type (proof/current-goal ps))))))

(defn- normal-form [expr only? & [definition]]
  (transformed-argument expr #(simp/simp % [(or definition "offset-loop")] {:only? only?})))

(deftest explicit-definition-tactics-change-the-target
  (let [n (e/fvar 100) a (e/fvar 101)
        expr (e/app* (c "offset-loop") (add n 1) a)
        rewritten (transformed-argument expr #(a/run-tactic % '(rewrite [offset-loop])))
        unfolded (transformed-argument expr #(basic/unfold-in-goal % "offset-loop"))
        expanded (transformed-argument expr #(basic/delta-in-goal % "offset-loop"))]
    ;; The zero equation is tried before the applicable successor equation.
    (is (= (c "offset-loop") (e/get-app-fn rewritten)))
    (is (= n (first (e/get-app-args rewritten))))
    (is (not= expr unfolded))
    (is (not= (c "offset-loop") (e/get-app-fn expanded)))))

(deftest nat-offset-equations-rewrite-predicate-arguments
  (let [n (e/fvar 100) a (e/fvar 101)
        call #(e/app* (c "offset-loop") %1 %2)]
    (doseq [only? [true false]
            arg [(add n 1) (e/app (c "Nat.succ") n)
                 (e/app* (c "Nat.add") n (e/lit-nat 1))]]
      (let [result (normal-form (call arg a) only?)]
        (is (= (c "offset-loop") (e/get-app-fn result)))
        (is (= n (first (e/get-app-args result))))
        (is (tc/is-def-eq (tc/mk-tc-state (a/env))
                          (second (e/get-app-args result)) (add a 1)))))
    (doseq [only? [true false]]
      (let [result (normal-form (call (add n 2) a) only?)]
        (is (= n (first (e/get-app-args result))))
        (is (= (c "offset-loop") (e/get-app-fn result)))
        (is (tc/is-def-eq (tc/mk-tc-state (a/env))
                          (second (e/get-app-args result)) (add (add a 1) 1)))))
    (is (not= (call (e/lit-nat 3) a) (normal-form (call (e/lit-nat 3) a) true)))
    (is (not= (c "offset-loop")
              (e/get-app-fn (normal-form (call (e/lit-nat 3) a) true))))))

(deftest nullary-zero-equation-matches-literals
  (doseq [n [0 3]]
    (let [result (normal-form (e/app (c "offset-count") (e/lit-nat n)) true "offset-count")]
      (is (not= (c "offset-count") (e/get-app-fn result)))
      (is (tc/is-def-eq (tc/mk-tc-state (a/env)) result (e/lit-nat n))))))

(deftest nested-nat-constructor-pattern-reduces-at-two
  (let [n (e/fvar 100) a (e/fvar 101)
        expr (e/app* (c "offset-pair") (e/app (c "Nat.succ") (e/app (c "Nat.succ") n)) a)
        result (normal-form expr true "offset-pair")]
    (is (= (c "offset-pair") (e/get-app-fn result)))
    (is (= n (first (e/get-app-args result))))))

(deftest nested-nat-offset-pattern-reduces-at-two
  (let [n (e/fvar 100) a (e/fvar 101)
        expr (e/app* (c "offset-pair") (add n 2) a)
        result (normal-form expr true "offset-pair")]
    (is (= (c "offset-pair") (e/get-app-fn result)))
    (is (= n (first (e/get-app-args result))))
    (is (tc/is-def-eq (tc/mk-tc-state (a/env))
                      (second (e/get-app-args result)) (add a 2)))))

(deftest delta-selected-set-allows-absent-names
  (let [expr (e/app (c "offset-count") (e/fvar 100))
        expanded (transformed-argument expr #(a/run-tactic % '(delta offset-count)))]
    (doseq [tactic ['(delta offset-count offset-loop) '(delta offset-loop offset-count)]]
      (is (= expanded (transformed-argument expr #(a/run-tactic % tactic)))))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"did not delta reduce"
                          (transformed-argument (e/fvar 100)
                                                #(a/run-tactic % '(delta offset-count offset-loop)))))))

(deftest offset-keys-preserve-root-and-numeral-discrimination
  (let [n (e/bvar 0) wrap #(e/app (c "offset-loop") %)
        pattern (wrap (e/app (c "Nat.succ") n))
        tree (dt/trie-insert dt/empty-trie (dt/expr->keys pattern) :success)]
    (doseq [arg [(add (e/fvar 100) 1) (e/lit-nat 3) (e/app (c "Nat.succ") (e/fvar 100))]]
      (is (= [:success] (dt/lookup-simp-tree tree (wrap arg)))))
    (is (= :const (:tag (first (dt/expr->keys (e/app (c "Nat.succ") n))))))
    (is (= (dt/expr->keys (wrap (e/lit-nat 3)))
           (dt/expr->keys (wrap (e/app (c "Nat.succ") (e/lit-nat 2))))))
    (is (not= (dt/expr->keys (wrap (e/lit-nat 2)))
              (dt/expr->keys (wrap (e/lit-nat 3)))))))

(deftest list-constructor-equation-rewrites-predicate-argument
  (let [x (e/fvar 100) acc (e/fvar 101) xs (e/fvar 103)
        list-nat (e/app (e/const' (name/from-string "List") [lvl/zero]) (c "Nat"))
        cons-nat (e/app* (e/const' (name/from-string "List.cons") [lvl/zero]) (c "Nat") x xs)
        expr (e/app* (c "offset-list") cons-nat acc)
        lctx {103 {:tag :local :id 103 :name "xs" :type list-nat}}
        simplify (fn [names] (transformed-argument expr #(simp/simp % names {:only? true}) lctx))
        expected (e/app* (c "offset-list") xs (#'dt/mk-add-nat acc x))]
    (is (= expr (simplify [])))
    (is (= expected (simplify ["offset-list"])))))

(deftest offset-matching-respects-theorem-priority
  (let [environment (a/env) nat (c "Nat")
        succ #(e/app (c "Nat.succ") %)
        eq (fn [x y] (e/app* (e/const' (name/from-string "Eq") [(lvl/succ lvl/zero)]) nat x y))
        n (e/fvar 100) g (e/fvar 101)
        query-arg (add n 1)
        expr (e/app g query-arg)]
    (doseq [[opaque? high-priority low-priority offset expected-proof]
            [[false 2000 1000 1 102] [true 2000 1000 1 102]
             [true 1000 2000 1 103] [true 2000 1000 2 103]]]
      (let [high-pattern (nth (iterate succ (e/bvar 0)) offset)
            high-rhs (if opaque? (e/app (e/fvar 104) (e/bvar 0)) (succ (e/bvar 0)))
            low-rhs (if opaque? (e/app (e/fvar 105) (e/bvar 0)) (e/bvar 0))
            high-type (e/forall' "x" nat (eq (e/app g high-pattern) high-rhs) :default)
            low-type (e/forall' "x" nat (eq (e/app g (e/bvar 0)) low-rhs) :default)
            lctx {100 {:name "n" :type nat} 101 {:name "g" :type (e/arrow nat nat)}
                  102 {:name "high" :type high-type} 103 {:name "low" :type low-type}
                  104 {:name "highResult" :type (e/arrow nat nat)}
                  105 {:name "lowResult" :type (e/arrow nat nat)}}
            st (tc/mk-tc-state-with-locals environment lctx)
            high (first (#'simp/extract-simp-lemma-term environment high-type high-priority (e/fvar 102)))
            low (first (#'simp/extract-simp-lemma-term environment low-type low-priority (e/fvar 103)))
            index (simp/build-lemma-index st environment [low high])
            result (#'simp/try-rewrite-step st environment index expr {})
            expected (if (= expected-proof 102)
                       (if opaque? (e/app (e/fvar 104) n) (succ n))
                       (if opaque? (e/app (e/fvar 105) query-arg) query-arg))]
        (is (= expected (:expr result)))
        (is (= (e/fvar expected-proof) (e/get-app-fn (:proof? result))))))))

(deftest equation-inventory-and-surface-tactics
  (is (= ["offset-pair.eq_1" "offset-pair.eq_2" "offset-pair.eq_3"]
         (mapv name/->string (eqns/eqns-for (a/env) (name/from-string "offset-pair")))))
  (is (= ["offset-loop.eq_1" "offset-loop.eq_2"]
         (mapv name/->string (eqns/eqns-for (a/env) (name/from-string "offset-loop")))))
  (doseq [tactics ['((simp only [offset-loop])) '((simp [offset-loop]))
                   '((unfold offset-loop) (cases n) (all_goals (rfl))) '((rw [offset-loop]))
                   '((delta offset-loop) (cases n) (all_goals (rfl)))]
          arg ['(+ n 1) '(Nat.succ n) 3]]
    (let [rhs (if (= arg 3) '(offset-loop 2 (+ acc 1)) '(offset-loop n (+ acc 1)))]
      (is (true? (do (eval (list* 'a/theorem (gensym "offset-step-")
                                  '[n :- Nat, acc :- Nat]
                                  (list '= (list 'offset-loop arg 'acc) rhs) tactics)) true)))))
  (is (true? (do (eval '(a/theorem offset-pair-two [n :- Nat, acc :- Nat]
                                   (= (offset-pair (+ n 2) acc) (offset-pair n (+ acc 2)))
                                   (simp only [offset-pair]))) true)))
  (is (true? (do (eval '(a/theorem offset-list-control [x :- Nat, xs :- (List Nat), acc :- Nat]
                                   (= (offset-list (List.cons Nat x xs) acc) (offset-list xs (+ acc x)))
                                   (simp only [offset-list]))) true))))

(deftest only-nat-offsets-use-wildcard-keys
  (let [wrap #(e/app (c "offset-loop") %)
        n (e/bvar 0)
        one (e/lit-nat 1)
        add-at (fn [type]
                 (e/app* (e/const' (name/from-string "Add.add") [lvl/zero])
                         type (e/bvar 1) n one))]
    (doseq [arg [(e/app* (c "Nat.add") n one) (add n 1) (add-at (c "Nat"))]]
      (is (= [{:tag :const :name (name/from-string "offset-loop") :arity 1} {:tag :star}]
             (dt/expr->keys (wrap arg)))))
    (is (= :const (:tag (second (dt/expr->keys (wrap (add-at (c "Int"))))))))
    (is (= :const (:tag (second (dt/expr->keys (wrap (e/app* (c "Nat.add") n (e/bvar 1))))))))))
