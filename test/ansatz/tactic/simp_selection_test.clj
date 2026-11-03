(ns ansatz.tactic.simp-selection-test
  "Lean pairs: test/lean/simp_selection.lean. Check the actual simp normal form."
  (:require [clojure.test :refer [deftest is use-fixtures]]
            [ansatz.core :as a]
            [ansatz.config :as config]
            [ansatz.eqns :as eqns]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]
            [ansatz.meta.constructions.util :as construction]
            [ansatz.tactic.proof :as proof]
            [ansatz.tactic.simp :as simp]))

(use-fixtures :once
  (fn [t]
    (a/load-init!)
    (binding [a/*verbose* false *ns* (the-ns 'ansatz.tactic.simp-selection-test)]
      (eval '(a/defn selected-inner [b :- Bool] Nat (match b [false 13] [true 21])))
      (eval '(a/defn selected-outer [b :- Bool] Nat (selected-inner b)))
      (eval '(a/defn selected-rec [xs :- (List Nat)] Nat
               (match xs [nil 0] [(cons x tail) (selected-rec tail)])))
      (t))))

(defn- c [n] (e/const' (name/from-string n) []))
(defn- normal-form [expr names & [opts]]
  ;; An arbitrary predicate prevents goal closing by defeq/rfl from hiding the shape.
  (let [nat (or (:result-type opts) (c "Nat"))
        lctx {100 {:tag :local :id 100 :name "b" :type (c "Bool")}
              101 {:tag :local :id 101 :name "P" :type (e/forall' "n" nat (e/sort' lvl/zero) :default)}}
        lctx (merge lctx (:extra-lctx opts))
        target (e/app (e/fvar 101) expr)
        [ps _] (proof/start-proof (a/env) target)
        goal (proof/current-goal ps)
        ps (assoc-in ps [:meta-mctx :decls (:id goal) :lctx] lctx)
        ps (simp/simp ps names (merge {:only? true} opts))]
    (second (e/get-app-fn-args (:type (proof/current-goal ps))))))

(deftest selected-definitions-preserve-callees
  (doseq [b [(e/fvar 100) (c "Bool.true")]]
    (let [inner (e/app (c "selected-inner") b)]
      (is (= [inner] (normal-form inner [])))
      (is (= [inner] (normal-form (e/app (c "selected-outer") b) ["selected-outer"])))
      (is (= [(e/lit-nat 21)] (normal-form (e/app (c "selected-inner") (c "Bool.true"))
                                                     ["selected-inner"]))))))

(deftest equations-belong-to-their-declaration
  (doseq [n ["selected-inner" "selected-rec"]]
    (let [owner (name/from-string n)]
      (is (seq (eqns/eqns-for (a/env) owner)))
      (is (every? #(= owner (name/name-prefix %)) (eqns/eqns-for (a/env) owner)))))
  (let [nil-list (e/app (e/const' (name/from-string "List.nil") [lvl/zero]) (c "Nat"))]
    (is (= [(e/lit-nat 0)] (normal-form (e/app (c "selected-rec") nil-list) ["selected-rec"])))))

(deftest only-does-not-run-user-simprocs
  (let [called (atom 0)
        sp (fn [_ _] (swap! called inc) nil)
        expr (e/app (c "selected-inner") (e/fvar 100))]
    (binding [config/*simprocs* [sp]]
      (is (= [expr] (normal-form expr [])))
      (is (zero? @called))
      (normal-form expr [] {:only? false})
      (is (pos? @called)))))

(deftest constructor-contradictions-use-no-confusion
  (doseq [form ['(a/theorem option-constructor-contradiction
                  [x :- Nat, h :- (= (Option Nat) (Option.none Nat) (Option.some Nat x))]
                  False (simp at h))
                '(a/theorem selected-constructor-contradiction
                  [x :- Nat, h :- (= (Option Nat) (Option.none Nat) (Option.some Nat x))]
                  False (simp only [reduceCtorEq] at h))
                '(a/theorem list-constructor-contradiction
                  [x :- Nat, xs :- (List Nat), h :- (= (List Nat) (List.nil Nat) (List.cons Nat x xs))]
                  False (simp at h))]]
    (is (true? (do (eval form) true))))
  (eval '(a/inductive SelectedChoice [A Type] (left [x A]) (right [x A])))
  (is (true? (do (eval '(a/theorem custom-constructor-contradiction
                     [x :- Nat, h :- (= (SelectedChoice Nat) (SelectedChoice.left Nat x) (SelectedChoice.right Nat x))]
                     False (simp at h))) true))))

(deftest selected-spend-preserves-option-and-store-callees
  (eval '(a/structure SelectedStore [] (wallet Nat) (live Nat)))
  (eval '(a/defn selected-amount [x :- Nat] (Option Nat)
           (match x [zero (Option.none Nat)] [(succ n) (Option.some Nat n)])))
  (eval '(a/defn selected-held [c :- Bool, live :- Nat, i :- Nat] (Option Nat)
           (match c [false (Option.some Nat 0)] [true (Option.some Nat live)])))
  (eval '(a/defn selected-spendH [s :- SelectedStore, i :- Nat, n :- Nat, h :- (Option Nat)] Nat
           (match h [none 0] [(some m) (+ n m)])))
  (eval '(a/defn selected-spendN [c :- Bool, s :- SelectedStore, i :- Nat, x :- Nat] Nat
           (match (selected-amount x)
             [none 0]
             [(some n) (match s [(mk wallet live) (selected-spendH s i n (selected-held c live i))])])))
  (let [expr (e/app* (c "selected-spendN") (e/fvar 100) (e/fvar 102) (e/fvar 103) (e/fvar 104))
        [result] (normal-form expr ["selected-spendN"]
                              {:extra-lctx {102 {:tag :local :id 102 :name "s" :type (c "SelectedStore")}
                                            103 {:tag :local :id 103 :name "i" :type (c "Nat")}
                                            104 {:tag :local :id 104 :name "x" :type (c "Nat")}}})
        constants (construction/fold-constants conj #{} result)]
    (doseq [callee ["selected-amount" "selected-held" "selected-spendH"]]
      (is (contains? constants (name/from-string callee)))
      (is (not-any? #(.startsWith (str %) (str callee ".match_")) constants)))))

(deftest selected-sequence-preserves-pick-and-truthy
  (eval '(a/defn selected-truthy [x :- Nat] Bool (match x [zero false] [(succ n) true])))
  (eval '(a/defn selected-pick [b :- Bool, x :- Nat, y :- Nat] Nat (match b [false y] [true x])))
  (eval '(a/defn selected-seq1 [o :- Bool, fr :- (=> Nat Nat), done :- Nat] Nat
           (match o [true done] [false (fr done)])))
  (let [done (e/app* (c "selected-pick") (e/app (c "selected-truthy") (e/lit-nat 0))
                    (e/lit-nat 13) (e/lit-nat 21))
        fr (e/lam "x" (c "Nat") (e/bvar 0) :default)]
    (is (= [done] (normal-form (e/app* (c "selected-seq1") (c "Bool.true") fr done)
                              ["selected-seq1"])))))

(deftest only-empty-does-not-discriminate-constructors
  (let [nat (c "Nat")
        option (e/app (e/const' (name/from-string "Option") [lvl/zero]) nat)
        lhs (e/app (e/const' (name/from-string "Option.none") [lvl/zero]) nat)
        rhs (e/app* (e/const' (name/from-string "Option.some") [lvl/zero]) nat (e/fvar 100))
        eq (e/app* (e/const' (name/from-string "Eq") [(lvl/succ lvl/zero)]) option lhs rhs)
        [ps _] (proof/start-proof (a/env) (c "False"))
        id (:id (proof/current-goal ps))
        ps (assoc-in ps [:meta-mctx :decls id :lctx]
                     {100 {:tag :local :id 100 :name "x" :type nat}
                      101 {:tag :local :id 101 :name "h" :type eq}})]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"made no progress"
                         (simp/simp-at ps 101 [] {:only? true})))
    (is (empty? (:goals (simp/simp-at ps 101 ["reduceCtorEq"] {:only? true}))))))

(deftest only-preserves-partial-applications-and-structural-reductions
  (let [fn-type (e/forall' "b" (c "Bool") (c "Nat") :default)]
    (is (= [(c "selected-outer")]
           (normal-form (c "selected-outer") ["selected-outer"] {:result-type fn-type}))))
  (let [value (e/lit-nat 13)]
    (is (= [value] (normal-form (e/app (e/lam "n" (c "Nat") (e/bvar 0) :default) value) [])))
    (is (= [value] (normal-form (e/let' "n" (c "Nat") value (e/bvar 0)) [])))
    (is (= [value]
           (normal-form (e/app* (e/const' (name/from-string "Prod.fst") [lvl/zero lvl/zero])
                               (c "Nat") (c "Nat")
                               (e/app* (e/const' (name/from-string "Prod.mk") [lvl/zero lvl/zero])
                                       (c "Nat") (c "Nat") value (e/lit-nat 21))) [])))))

(deftest default-nat-predicate-simprocs-do-not-require-decide
  (let [le (fn [a b] (e/app* (e/const' (name/from-string "LE.le") [lvl/zero])
                            (c "Nat") (c "instLENat") (e/lit-nat a) (e/lit-nat b)))
        opts {:result-type (e/sort' lvl/zero)}]
    (doseq [[expr expected] [[(le 0 1) (c "True")] [(le 2 1) (c "False")]]]
      (is (= [expr] (normal-form expr [] opts)))
      (is (= [expected] (normal-form expr [] (assoc opts :only? false :decide? false))))
      (is (= [expected] (normal-form expr ["Nat.reduceLeDiff"] opts)))))
  (is (true? (do (eval '(a/theorem literal-nat-order-contradiction
                         [h :- (<= Nat 2 1)] False (simp at h))) true))))
