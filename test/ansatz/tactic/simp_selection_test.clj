(ns ansatz.tactic.simp-selection-test
  "Lean pairs: test/lean/simp_selection.lean. Check the actual simp normal form."
  (:require [clojure.test :refer [deftest is use-fixtures]]
            [ansatz.core :as a]
            [ansatz.attrs :as attrs]
            [ansatz.kernel.env :as env]
            [ansatz.meta.rec-ext :as rec-ext]
            [ansatz.tactic.simp.simp-theorems :as simp-theorems]
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
        constants (construction/fold-constants conj #{} result)
        option (e/app (e/const' (name/from-string "Option") [lvl/zero]) (c "Nat"))
        expected
        (e/app* (e/const' (name/from-string "selected-spendN.match_1") [(lvl/succ lvl/zero)])
                (e/lam "_x" option (c "Nat") :default)
                (e/app (c "selected-amount") (e/fvar 104))
                (e/lam "_" (c "Unit") (e/lit-nat 0) :default)
                (e/lam "n" (c "Nat")
                       (e/app* (c "selected-spendH")
                               (e/app* (c "SelectedStore.mk")
                                       (e/proj (name/from-string "SelectedStore") 0 (e/fvar 102))
                                       (e/proj (name/from-string "SelectedStore") 1 (e/fvar 102)))
                               (e/fvar 103) (e/bvar 0)
                               (e/app* (c "selected-held") (e/fvar 100)
                                       (e/proj (name/from-string "SelectedStore") 1 (e/fvar 102))
                                       (e/fvar 103))) :default))]
    (is (= expected result))
    (doseq [callee ["selected-amount" "selected-held" "selected-spendH"]]
      (is (contains? constants (name/from-string callee)))
      (is (not-any? #(.startsWith (str %) (str callee "._match_")) constants)))))

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

(deftest selected-imported-recursive-equations-preserve-the-induction-hypothesis
  (is (true?
       (do (eval '(a/theorem selected-foldl-filter
                             [A :- Type, G :- Type, f :- (=> G A G), p :- (=> A Bool), l :- (List A)]
                             (forall [b :- G]
                                     (= G (List.foldl f b (List.filter p l))
                                        (List.foldl (fn [acc :- G, x :- A]
                                                      (match (p x) [true (f acc x)] [false acc])) b l)))
                             (induction l)
                             (all_goals (intro b))
                             (all_goals (simp only [List.filter List.foldl]))
                             (rename_i head tail ih_tail)
                      (cases hp (p head))
                             (all_goals (simp only [hp List.foldl]))
                             (all_goals (exact (ih_tail _)))))
           true))))

(deftest literal-predicate-simprocs-are-default-and-selectable
  (let [opts {:result-type (e/sort' lvl/zero)}]
    (doseq [[carrier x y] [["String" (e/lit-str "alpha") (e/lit-str "beta")]
                           ["Int" (e/app (c "Int.ofNat") (e/lit-nat 2))
                            (e/app (c "Int.negSucc") (e/lit-nat 0))]
                           ["Char" (e/app (c "Char.ofNat") (e/lit-nat 97))
                            (e/app (c "Char.ofNat") (e/lit-nat 98))]]]
      (doseq [[head suffix expected] [["Eq" "Eq" "False"] ["Ne" "Ne" "True"]]]
        (let [expr (e/app* (e/const' (name/from-string head) [(lvl/succ lvl/zero)]) (c carrier) x y)]
          (is (= [expr] (normal-form expr [] opts)))
          (is (= [(c expected)] (normal-form expr [] (assoc opts :only? false :decide? false))))
          (is (= [(c expected)] (normal-form expr [(str carrier ".reduce" suffix)] opts)))))))
  (is (true? (do (eval '(a/theorem string-literal-contradiction
                                   [h :- (= String "alpha" "beta")] False (simp at h))) true))))

(deftest only-explicit-arithmetic-simprocs
  (let [expr (e/app* (e/const' (name/from-string "HAdd.hAdd") [lvl/zero lvl/zero lvl/zero])
                     (c "Nat") (c "Nat") (c "Nat")
                     (e/app* (e/const' (name/from-string "instHAdd") [lvl/zero]) (c "Nat") (c "instAddNat"))
                     (e/lit-nat 2) (e/lit-nat 3))]
    (is (= [expr] (normal-form expr [])))
    (is (= [expr] (normal-form expr ["Nat.reduceMul"])))
    (is (= [(e/lit-nat 5)] (normal-form expr ["Nat.reduceAdd"]))))
  (let [v (fn [n] (e/app (c "Int.ofNat") (e/lit-nat n)))
        expr (e/app* (c "Int.add") (v 2) (v 3))]
    (is (= [expr] (normal-form expr [] {:result-type (c "Int")})))
    (is (= [(v 5)] (normal-form expr ["Int.reduceAdd"] {:result-type (c "Int")})))))

(deftest int-division-simprocs-are-euclidean
  ;; Lean Int `/` and `%` are Int.ediv / Int.emod (Init/Data/Int/DivMod/Basic.lean): the
  ;; remainder is non-negative, so (-3) / 2 = -2 and 3 % (-2) = 1, x / 0 = 0, x % 0 = x.
  (let [int (c "Int")
        v (fn [n] (if (neg? n)
                    (e/app (c "Int.negSucc") (e/lit-nat (dec (- n))))
                    (e/app (c "Int.ofNat") (e/lit-nat n))))
        op (fn [h cls inst a b]
             (e/app* (e/const' (name/from-string h) [lvl/zero lvl/zero lvl/zero]) int int int
                     (e/app* (e/const' (name/from-string cls) [lvl/zero]) int (c inst))
                     (v a) (v b)))
        div (fn [a b] (op "HDiv.hDiv" "instHDiv" "Int.instDiv" a b))
        mod (fn [a b] (op "HMod.hMod" "instHMod" "Int.instMod" a b))
        nf (fn [expr proc] (normal-form expr [proc] {:result-type int}))]
    (doseq [[a b q r] [[-3 2 -2 1] [3 -2 -1 1] [-12 7 -2 2] [12 -7 -1 5] [-12 -7 2 2]
                       [7 2 3 1] [5 0 0 5] [-5 0 0 -5]]]
      (is (= [(v q)] (nf (div a b) "Int.reduceDiv")) (str a " / " b))
      (is (= [(v r)] (nf (mod a b) "Int.reduceMod")) (str a " % " b)))))

(deftest imported-equations-use-recursion-and-smart-unfolding-metadata
  (let [before (a/env) n (name/from-string "imported-bool-match")]
    (try
      ;; Checked declarations without a local inventory, as after kernel import.
      (swap! a/ansatz-env env/check-constant
             (env/mk-def n [] (e/forall' "b" (c "Bool") (c "Nat") :default)
                         (e/lam "b" (c "Bool")
                                (e/app* (e/const' (name/from-string "Bool.rec") [(lvl/succ lvl/zero)])
                                        (e/lam "b" (c "Bool") (c "Nat") :default)
                                        (e/lit-nat 13) (e/lit-nat 21) (e/bvar 0)) :default)))
      (doseq [[i b v] [[1 "Bool.false" 13] [2 "Bool.true" 21]]]
        (let [lhs (e/app (c "imported-bool-match") (c b))
              ty (e/app* (e/const' (name/from-string "Eq") [(lvl/succ lvl/zero)])
                         (c "Nat") lhs (e/lit-nat v))
              refl (e/app* (e/const' (name/from-string "Eq.refl") [(lvl/succ lvl/zero)]) (c "Nat") lhs)
              ci (env/mk-thm (name/mk-str n (str "eq_" i)) [] ty refl)]
          (swap! a/ansatz-env env/check-constant ci)))
      (swap! a/ansatz-env env/update-extension :eqns {} dissoc n)
      (let [expr (e/app (c "imported-bool-match") (e/fvar 100))
            expected (e/app* (e/const' (name/from-string "Bool.rec") [(lvl/succ lvl/zero)])
                             (e/lam "b" (c "Bool") (c "Nat") :default)
                             (e/lit-nat 13) (e/lit-nat 21) (e/fvar 100))]
        (is (= [expected] (normal-form expr ["imported-bool-match"]))))
      (let [[recursive _] (attrs/import-attr-tuples (a/env) [["recursive" "imported-bool-match" nil nil]] {})
            [smart _] (attrs/import-attr-tuples recursive [["smart-unfolding" "imported-bool-match" nil nil]] {})]
        (is (not (simp-theorems/unfold-even-with-eqns (env/fork recursive) n)))
        (is (simp-theorems/unfold-even-with-eqns (env/fork smart) n))
        (is (= [:thm :thm :to-unfold]
               (mapv :kind (simp-theorems/mk-simp-entry-of-decl-to-unfold smart n)))))
      (is (rec-ext/is-recursive-definition (a/env) (name/from-string "List.foldl")))
      (finally (reset! a/ansatz-env before)))))

(deftest failed-equation-inventories-are-diagnostic
  (let [before (a/env) n (name/from-string "selected-inner")
        equations (eqns/eqns-for before n)
        error (ex-info "injected equation admission failure" {:kind :test-failure})]
    (try
      (doseq [inventory [[] equations]]
        (reset! a/ansatz-env (eqns/register-eqn-thms before n inventory [error]))
        (is (thrown-with-msg? clojure.lang.ExceptionInfo #"equation generation errors"
                              (eqns/get-eqns-for? (a/env) n)))
        (is (thrown-with-msg? clojure.lang.ExceptionInfo #"equation generation errors"
                              (normal-form (e/app (c "selected-inner") (e/fvar 100)) ["selected-inner"]))))
      (reset! a/ansatz-env before)
      (is (= [(e/lit-nat 21)] (normal-form (e/app (c "selected-inner") (c "Bool.true")) ["selected-inner"])))
      (finally (reset! a/ansatz-env before)))))

(deftest only-explicit-dependent-if-simproc
  (let [expr (e/app* (e/const' (name/from-string "dite") [(lvl/succ lvl/zero)])
                     (c "Nat") (c "True")
                     (e/app* (c "Decidable.isTrue") (c "True") (c "True.intro"))
                     (e/lam "h" (c "True") (e/lit-nat 2) :default)
                     (e/lam "h" (e/app (c "Not") (c "True")) (e/lit-nat 3) :default))]
    (is (= [expr] (normal-form expr [])))
    (is (= [expr] (normal-form expr ["reduceIte"])))
    (is (= [(e/lit-nat 2)] (normal-form expr ["reduceDIte"])))))

(deftest literal-order-predicate-simprocs
  (let [opts {:result-type (e/sort' lvl/zero)}]
    (doseq [[carrier lt le x y]
            [["String" "String.instLT" "String.instLE" (e/lit-str "a") (e/lit-str "b")]
             ["Int" "Int.instLTInt" "Int.instLEInt" (e/app (c "Int.negSucc") (e/lit-nat 0))
              (e/app (c "Int.ofNat") (e/lit-nat 2))]
             ["Char" "Char.instLT" "Char.instLE" (e/app (c "Char.ofNat") (e/lit-nat 97))
              (e/app (c "Char.ofNat") (e/lit-nat 98))]]
            [op instance expected] [["LT" lt "True"] ["LE" le "True"]
                                    ["GT" lt "False"] ["GE" le "False"]]]
      (let [expr (e/app* (e/const' (name/from-string (str op "." (.toLowerCase op))) [lvl/zero])
                         (c carrier) (c instance) x y)]
        (is (= [expr] (normal-form expr [] opts)))
        (is (= [(c expected)] (normal-form expr [(str carrier ".reduce" op)] opts)))
        (is (= [(c expected)] (normal-form expr [] (assoc opts :only? false :decide? false))))))))
