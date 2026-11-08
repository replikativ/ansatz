(ns ansatz.tactic.nat-equations-test
  "Nat constructor equations and offset keys; Lean pair: test/lean/nat_equations.lean."
  (:require [clojure.test :refer [deftest is use-fixtures]]
            [ansatz.core :as a]
            [ansatz.fixtures :as fixtures]
            [ansatz.eqns :as eqns]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.env :as env]
            [ansatz.meta.constructions.util :as util]
            [ansatz.meta.rec-ext :as rec-ext]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.tc :as tc]
            [ansatz.tactic.discr-tree :as dt]
            [ansatz.tactic.proof :as proof]
            [ansatz.tactic.basic :as basic]
            [ansatz.tactic.simp :as simp]))

(defn- c [n] (e/const' (name/from-string n) []))
(defn- add [n k] (#'dt/mk-add-nat n (e/lit-nat k)))

(use-fixtures :once fixtures/isolated-session
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

(deftest delta-selected-set-allows-value-and-no-value-declarations
  (let [expr (e/app (c "offset-count") (e/fvar 100))
        expanded (transformed-argument expr #(basic/delta-in-goal % "offset-count"))]
    (is (not= expr expanded))
    (doseq [other ["Nat" "Nat.add_comm"]
            selected [["offset-count" other] [other "offset-count"]]]
      (is (= expanded (transformed-argument expr #(basic/delta-in-goal % selected))))
      (is (= expanded (transformed-argument expr #(a/run-tactic % (cons 'delta (map symbol selected)))))))
    ;; The selected inductive occurs in this target, but has no delta value.
    ;; No usable selected value changed the whole target, so collective progress fails.
    (let [[ps _] (proof/start-proof (a/env) (c "Nat"))]
      (doseq [selected [["Nat"] ["Nat" "Nat.add_comm"]]]
        (is (thrown-with-msg? clojure.lang.ExceptionInfo #"did not delta reduce"
                              (basic/delta-in-goal ps selected)))))))

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

(defn- imported-polymorphic-equations []
  ;; An imported inventory has no eager :eqns extension. Admit the definition and
  ;; its equations through the kernel, as the importer does for exported CIs.
  (let [un (name/from-string "u") u (lvl/param un)
        fn-name (name/from-string "polyOffset")
        ctx (util/context (a/env)) nat (c "Nat")
        alpha (util/local-decl ctx "α" (e/sort' (lvl/succ u)))
        n (util/local-decl ctx "n" nat)
        a (util/local-decl ctx "a" alpha)
        k (util/local-decl ctx "k" nat)
        ih (util/local-decl ctx "ih" alpha)
        motive (util/mk-lambda-fvars ctx [k] alpha)
        minor (util/mk-lambda-fvars ctx [k ih] ih)
        body (e/app* (e/const' (name/from-string "Nat.rec") [(lvl/succ u)]) motive a minor n)
        environment (env/check-constant (a/env)
                                        (env/mk-def fn-name [un]
                                                    (util/mk-forall-fvars ctx [alpha n a] alpha)
                                                    (util/mk-lambda-fvars ctx [alpha n a] body)))
        _ (util/set-env! ctx environment)
        call #(e/app* (e/const' fn-name [u]) alpha % a)
        environment (reduce (fn [environment [suffix params lhs rhs]]
                              (env/check-constant environment
                                                  (env/mk-thm (name/mk-str fn-name suffix) [un]
                                                              (util/mk-forall-fvars ctx params (util/mk-eq ctx lhs rhs))
                                                              (util/mk-lambda-fvars ctx params (util/mk-eq-refl ctx lhs)))))
                            environment
                            [["eq_1" [alpha a] (call (e/lit-nat 0)) a]
                             ["eq_2" [alpha n a] (call (e/app (c "Nat.succ") n)) (call n)]])]
    (rec-ext/mark-as-recursive environment fn-name)))

(deftest imported-polymorphic-offset-equations-infer-universes
  (let [environment (imported-polymorphic-equations)
        fn-name (name/from-string "polyOffset") n (e/fvar 100) a (e/fvar 101)]
    (is (nil? (eqns/eqns-for environment fn-name)))
    (is (= 2 (count (eqns/get-eqns-for? environment fn-name))))
    (doseq [[level alpha a-type] [[lvl/zero (c "Nat") (c "Nat")]
                                  [(lvl/succ lvl/zero)
                                   (e/app (e/const' (name/from-string "List") [(lvl/succ lvl/zero)])
                                          (e/sort' (lvl/succ lvl/zero)))
                                   (e/app (e/const' (name/from-string "List") [(lvl/succ lvl/zero)])
                                          (e/sort' (lvl/succ lvl/zero)))]]
            arg [(add n 1) (e/app (c "Nat.succ") n)]]
      (let [call #(e/app* (e/const' fn-name [level]) alpha % a)
            expr (call arg)
            lctx {100 {:tag :local :name "n" :type (c "Nat")}
                  101 {:tag :local :name "a" :type a-type}
                  102 {:tag :local :name "P" :type (e/arrow a-type (e/sort' lvl/zero))}}
            [ps _] (proof/start-proof environment (e/app (e/fvar 102) expr))
            ps (assoc-in ps [:meta-mctx :decls (:id (proof/current-goal ps)) :lctx] lctx)
            simplify (fn [names] (-> (simp/simp ps names {:only? true}) proof/current-goal :type e/app-arg))]
        (is (= expr (simplify [])))
        (is (= (call n) (simplify ["polyOffset"])))))))

(defn- checked-local-proof? [st ids goal value]
  (let [ctx (atom st) xs (mapv e/fvar ids)]
    (env/verifies? (:env st) (util/mk-forall-fvars ctx xs goal)
                   (util/mk-lambda-fvars ctx xs value))))

(deftest offset-conditions-are-discharged-before-priority-fallback
  (let [environment (a/env) nat (c "Nat") n (e/fvar 100) g (e/fvar 101) p (e/fvar 104)
        high-result (e/fvar 106) low-result (e/fvar 107)
        eq #(e/app* (e/const' (name/from-string "Eq") [(lvl/succ lvl/zero)]) nat %1 %2)
        high-type (e/forall' "x" nat
                             (e/arrow (e/app p (e/bvar 0))
                                      (eq (e/app g (e/app (c "Nat.succ") (e/bvar 1)))
                                          (e/app high-result (e/bvar 1)))) :default)
        low-type (e/forall' "x" nat (eq (e/app g (e/bvar 0)) (e/app low-result (e/bvar 0))) :default)
        locals {100 {:tag :local :name "n" :type nat}
                101 {:tag :local :name "g" :type (e/arrow nat nat)}
                102 {:tag :local :name "h" :type high-type}
                103 {:tag :local :name "low" :type low-type}
                104 {:tag :local :name "P" :type (e/arrow nat (e/sort' lvl/zero))}
                106 {:tag :local :name "highResult" :type (e/arrow nat nat)}
                107 {:tag :local :name "lowResult" :type (e/arrow nat nat)}}
        high (first (#'simp/extract-simp-lemma-term environment high-type 2000 (e/fvar 102)))
        low (first (#'simp/extract-simp-lemma-term environment low-type 1000 (e/fvar 103)))]
    (doseq [hp? [true false] arg [(add n 1) (e/app (c "Nat.succ") n)]]
      (let [lctx (cond-> locals hp? (assoc 105 {:tag :local :name "hp" :type (e/app p n)}))
            st (tc/mk-tc-state-with-locals environment lctx)
            index (simp/build-lemma-index st environment [low high])
            expr (e/app g arg)
            result (#'simp/try-rewrite-step st environment index expr {:max-depth 20})
            expected (if hp? (e/app high-result n) (e/app low-result arg))]
        (is (= expected (:expr result)))
        (is (= (if hp? (e/app* (e/fvar 102) n (e/fvar 105)) (e/app (e/fvar 103) arg))
               (:proof? result)))
        (is (checked-local-proof? st (cond-> [100 101 104 106 107 102 103] hp? (conj 105))
                                  (eq expr expected) (:proof? result)))))))

(deftest offset-theorems-synthesize-instances-absent-from-the-lhs
  (let [environment (a/env) nat (c "Nat") n (e/fvar 100) g (e/fvar 101)
        result-fn (e/fvar 104)
        eq #(e/app* (e/const' (name/from-string "Eq") [(lvl/succ lvl/zero)]) nat %1 %2)
        inst-type (e/app (e/const' (name/from-string "Inhabited") [(lvl/succ lvl/zero)]) nat)
        type (e/forall' "x" nat
                        (e/forall' "inst" inst-type
                                   (eq (e/app g (e/app (c "Nat.succ") (e/bvar 1)))
                                       (e/app result-fn (e/bvar 1))) :inst-implicit) :default)
        lctx {100 {:tag :local :name "n" :type nat}
              101 {:tag :local :name "g" :type (e/arrow nat nat)}
              102 {:tag :local :name "h" :type type}
              103 {:tag :local :name "inst" :info :inst-implicit :type inst-type}
              104 {:tag :local :name "result" :type (e/arrow nat nat)}}
        lemma (first (#'simp/extract-simp-lemma-term environment type 2000 (e/fvar 102)))]
    (doseq [local? [true false]
            arg [(add n 1) (e/app (c "Nat.succ") n)]]
      (let [st (tc/mk-tc-state-with-locals environment (if local? lctx (dissoc lctx 103)))
            index (simp/build-lemma-index st environment [lemma])
            expr (e/app g arg)
            result (#'simp/try-rewrite-step st environment index expr {:max-depth 20})
            instance (if local? (e/fvar 103) (c "instInhabitedNat"))]
        (is (= (e/app result-fn n) (:expr result)))
        (is (= (e/app* (e/fvar 102) n instance) (:proof? result)))
        (is (checked-local-proof? st (if local? [100 101 104 103 102] [100 101 104 102])
                                  (eq expr (:expr result)) (:proof? result)))))))
