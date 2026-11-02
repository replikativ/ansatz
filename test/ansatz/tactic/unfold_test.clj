(ns ansatz.tactic.unfold-test
  "`unfold` follows Lean `Meta.unfoldTarget` (Meta/Tactic/Unfold.lean): existing
   unfold equations rewrite the target; otherwise deltaExpand preserves folded callees.
   Lean counterpart: test/lean/unfold.lean."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [ansatz.core :as a]
            [ansatz.kernel.env :as env]
            [ansatz.meta.rec-ext :as rec-ext]
            [ansatz.meta.match.matcher-info :as matcher-info]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.tc :as tc]
            [ansatz.meta :as meta]
            [ansatz.tactic.basic :as basic]
            [ansatz.tactic.proof :as proof]
            [ansatz.tactic.simp :as simp]))

(use-fixtures :once (fn [t]
                      (a/load-init!)
                      ;; eval resolves the a/ alias in *ns*, which is not this namespace at test time
                      (binding [a/*verbose* false *ns* (the-ns 'ansatz.tactic.unfold-test)] (t))))

(defn- proves? [form]
  (try (eval form) true
       (catch clojure.lang.ExceptionInfo t
         (if (= :tactic-error (:kind (ex-data t))) (.getMessage t) (throw t)))))

(defn- c [n] (e/const' (name/from-string n) []))
(defn- unfolded [en target n]
  (proof/current-goal (basic/unfold-in-goal (first (proof/start-proof en target)) n)))

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
  (is (rec-ext/is-recursive-definition (a/env) (name/from-string "unfold-rec")))
  (let [true-expr (c "Bool.true")
        eq #(e/app* (e/const' (name/from-string "Eq") [(lvl/succ lvl/zero)])
                    (c "Bool") % true-expr)
        nil-expr (e/app (e/const' (name/from-string "List.nil") [lvl/zero]) (c "Nat"))]
    (is (= (eq true-expr)
           (:type (unfolded (a/env) (eq (e/app (c "unfold-rec") nil-expr)) "unfold-rec")))))
  (is (true? (proves? '(a/theorem unfold-rec-nil [] (= Bool (unfold-rec (List.nil Nat)) true)
                                  (unfold unfold-rec) (rfl))))))

(deftest dsimp-reduces-matcher-with-field-alternatives
  ;; Lean dsimp reduces a matcher on a constructor discriminant (Meta.reduceMatcher?) for
  ;; alternatives that bind fields, not only Unit thunks. unfold + cases + dsimp only.
  (eval '(a/inductive UnfoldOut [] (val) (stuck [n Nat])))
  (eval '(a/structure UnfoldStore [] (w Nat) (l (List Nat))))
  (eval '(a/defn unfold-amount [x :- Nat] (Option Nat)
           (match x [zero (Option.none Nat)] [(succ k) (Option.some Nat k)])))
  (eval '(a/defn unfold-spendH [s :- UnfoldStore, n :- Nat] UnfoldOut (UnfoldOut.stuck n)))
  (eval '(a/defn unfold-spendN [s :- UnfoldStore, x :- Nat] UnfoldOut
           (match (unfold-amount x) [none (UnfoldOut.stuck 0)]
                  [(some n) (match s [(mk w l) (unfold-spendH s n)])])))
  (is (true? (proves? '(a/theorem unfold-spendN-nv [s :- UnfoldStore, x :- Nat]
                                  (Not (= UnfoldOut (unfold-spendN s x) UnfoldOut.val))
                                  (cases s) (unfold unfold-spendN) (cases qa (unfold-amount x))
                                  (all_goals (dsimp only))
                                  (intro h) (cases h) (intro h) (cases h))))))

(defn- nat-eq [x y]
  (e/app* (e/const' (name/from-string "Eq") [(lvl/succ lvl/zero)]) (c "Nat") x y))

(deftest delta-target-shapes
  (let [nat (c "Nat")
        f (name/from-string "deltaWrap")
        callee (c "Nat.succ")
        ci (env/mk-def f [] (e/forall' "x" nat nat :default)
                       (e/lam "x" nat (e/app callee (e/bvar 0)) :default))
        en (env/check-constant (a/env) ci)
        call #(e/app (e/const' f []) %)
        arg (e/lit-nat 7)
        rhs (e/app callee arg)]
    (is (= (nat-eq rhs arg) (:type (unfolded en (nat-eq (call arg) arg) "deltaWrap"))))
    (doseq [[target expected]
            [[(e/forall' "x" nat (nat-eq (call (e/bvar 0)) (e/bvar 0)) :default)
              (e/forall' "x" nat (nat-eq (e/app callee (e/bvar 0)) (e/bvar 0)) :default)]
             [(e/let' "x" nat (call arg) (nat-eq (call (e/bvar 0)) (e/bvar 0)))
              (e/let' "x" nat rhs (nat-eq (e/app callee (e/bvar 0)) (e/bvar 0)))]]]
      (is (= expected (:type (unfolded en target "deltaWrap"))))))
  (eval '(a/structure DeltaBox [] (x Nat)))
  (eval '(a/defn delta-box [n :- Nat] DeltaBox (DeltaBox.mk n)))
  (let [en (a/env) arg (e/lit-nat 7)
        proj #(e/proj (name/from-string "DeltaBox") 0 %)]
    (is (= (nat-eq (proj (e/app (c "DeltaBox.mk") arg)) arg)
           (:type (unfolded en (nat-eq (proj (e/app (c "delta-box") arg)) arg) "delta-box"))))))

(deftest callee-name-does-not-classify-recursion
  (eval '(a/defn Innocent.brecOn [n :- Nat] Nat n))
  (eval '(a/defn innocent-wrap [n :- Nat] Nat (Innocent.brecOn n)))
  (let [nat (c "Nat") en (a/env)
        target (e/forall' "n" nat (nat-eq (e/app (c "innocent-wrap") (e/bvar 0)) (e/bvar 0)) :default)
        expected (e/forall' "n" nat (nat-eq (e/app (c "Innocent.brecOn") (e/bvar 0)) (e/bvar 0)) :default)]
    (is (not (rec-ext/is-recursive-definition en (name/from-string "innocent-wrap"))))
    (is (= expected (:type (unfolded en target "innocent-wrap"))))))

(deftest delta-beta-through-lets-and-many-arguments
  (let [nat (c "Nat") v (e/lit-nat 7)
        f (name/from-string "deltaLet")
        ci (env/mk-def f [] (e/forall' "x" nat nat :default)
                       (e/let' "y" nat v (e/lam "x" nat (e/bvar 1) :default)))
        en (env/check-constant (a/env) ci)]
    (is (= (nat-eq v v) (:type (unfolded en (nat-eq (e/app (e/const' f []) (e/lit-nat 0)) v) "deltaLet"))))
    (let [many (name/from-string "deltaMany")
          ty (reduce (fn [b _] (e/forall' "x" nat b :default)) nat (range 140))
          val (reduce (fn [b _] (e/lam "x" nat b :default)) v (range 140))
          en (env/check-constant en (env/mk-def many [] ty val))]
      (is (= (nat-eq v v) (:type (unfolded en (nat-eq (reduce e/app (e/const' many [])
                                                              (repeat 140 (e/lit-nat 0))) v) "deltaMany")))))))

(deftest delta-instantiates-universes-and-guards-depth
  (let [u (name/from-string "u") f (name/from-string "deltaUniverse")
        ci (env/mk-def f [u] (e/sort' (lvl/succ (lvl/param u))) (e/sort' (lvl/param u)))
        en (env/check-constant (a/env) ci)]
    (is (= (e/sort' (lvl/succ lvl/zero))
           (:type (unfolded en (e/const' f [(lvl/succ lvl/zero)]) "deltaUniverse"))))
    (binding [basic/*delta-max-rec-depth* 8]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"maximum recursion depth"
                            (unfolded en (reduce (fn [b _] (e/forall' "x" (c "Nat") b :default))
                                                 (e/const' f [lvl/zero]) (range 20)) "deltaUniverse"))))))

(deftest existing-unfold-equation-transports-proof
  ;; An axiom equation makes the rewrite non-definitional: dropping the equality
  ;; proof cannot prove the original target, even though delta expansion can run.
  (let [nat (c "Nat") f (name/from-string "equationConstant")
        zero (e/lit-nat 0) one (e/lit-nat 1)
        eq (fn [x y] (e/app* (e/const' (name/from-string "Eq") [(lvl/succ lvl/zero)]) nat x y))
        en (-> (a/env)
               (env/check-constant (env/mk-def f [] nat zero))
               (env/check-constant (env/mk-axiom (name/from-string "equationConstant.eq_def") []
                                                 (eq (e/const' f []) one))))
        ps (first (proof/start-proof en (eq (e/const' f []) one)))
        ps' (basic/unfold-in-goal ps "equationConstant")]
    (is (= (eq one one) (:type (proof/current-goal ps'))))
    (doseq [target [(e/forall' "n" nat (eq (e/const' f []) one) :default)
                    (e/let' "n" nat (e/const' f []) (eq (e/const' f []) one))]]
      (let [before (first (proof/start-proof en target))
            after (basic/unfold-in-goal before "equationConstant")
            expected (if (e/forall? target)
                       (e/forall' "n" nat (eq one one) :default)
                       (e/let' "n" nat one (eq one one)))]
        (is (= expected (:type (proof/current-goal after))))
        (let [solved (basic/rfl (if (e/forall? target) (basic/intro after "n") after))
              term (meta/zonk-expr (:meta-mctx solved) (e/mvar (:root-mvar solved)))]
          (is (env/verifies? en target term)))))
    (let [solved (basic/rfl ps')
          term (meta/zonk-expr (:meta-mctx solved) (e/mvar (:root-mvar solved)))]
      (is (env/verifies? en (eq (e/const' f []) one) term)))))

(deftest recursive-tags-follow-environment-branches
  (let [n (name/from-string "taggedRecursive") en (a/env)
        tagged (rec-ext/mark-as-recursive en n)]
    (is (not (rec-ext/is-recursive-definition en n)))
    (is (rec-ext/is-recursive-definition (env/fork tagged) n))))

(deftest matcher-selects-field-and-respects-transparency-and-local-lets
  (eval '(a/defn matcher-field [x :- (Option Nat)] Nat
           (match x [none 13] [(some n) n])))
  (eval '(a/defn matcher-bool [x :- Bool] Nat
           (match x [false 13] [true 21])))
  (eval '(a/defn hidden-bool [] Bool true))
  (let [en (a/env)
        expand (fn [n arg]
                 (#'basic/delta-expand (e/app (c n) arg) (name/from-string n)
                                       (env/lookup! en (name/from-string n))))
        field (e/fvar 41)
        st (tc/attach-lctx (tc/mk-tc-state en) {41 {:name "field" :type (c "Nat")}})
        expr (expand "matcher-field" (e/app* (c "Option.some") (c "Nat") field))]
    (is (= field (:expr (#'simp/try-reduce-matcher st expr))))
    (let [hidden (expand "matcher-bool" (c "hidden-bool"))]
      (is (nil? (#'simp/try-reduce-matcher st hidden)))
      (is (= hidden (#'simp/dsimp-expr en {} hidden 20))))
    (let [ty (e/forall' "u" (c "Unit") (c "Nat") :default)
          lctx {920000 {:name "f" :type ty :value (e/fvar 920001)}
                920001 {:name "g" :type ty}}
          st (tc/attach-lctx (tc/mk-tc-state en) lctx)]
      (is (= (e/lit-nat 13)
             (:expr (#'simp/try-reduce-matcher st (expand "matcher-bool" (c "Bool.false")))))))))

(deftest unfold-equations-on-type-valued-arrows
  (let [type0 (e/sort' (lvl/succ lvl/zero))
        eq (fn [x y] (e/app* (e/const' (name/from-string "Eq") [(lvl/succ (lvl/succ lvl/zero))])
                             type0 x y))
        type-name (name/from-string "unfoldType")
        eq-name (name/from-string "unfoldType.eq_def")
        en (-> (a/env)
               (env/check-constant (env/mk-def type-name [] type0 (c "Nat")))
               (env/check-constant (env/mk-axiom eq-name [] (eq (c "unfoldType") (c "Bool")))))
        arrow (e/arrow (c "Nat") (c "unfoldType"))
        expected (e/arrow (c "Nat") (c "Bool"))
        st (tc/mk-tc-state en)
        r (simp/unfold-expr st en arrow eq-name)
        target (eq arrow expected)
        ps (basic/unfold-in-goal (first (proof/start-proof en target)) "unfoldType")
        solved (basic/rfl ps)
        term (meta/zonk-expr (:meta-mctx solved) (e/mvar (:root-mvar solved)))]
    (is (= expected (:expr r)))
    (is (env/verifies? en (eq arrow expected) (:proof? r)))
    (is (= (eq expected expected) (:type (proof/current-goal ps))))
    (is (env/verifies? en target term))
    ;; A dependent type-valued Pi stays on dsimp; a non-rfl equation is inapplicable.
    (let [family (name/from-string "unfoldFamily")
          family-type (e/arrow (c "Nat") type0)
          value (e/lam "n" (c "Nat") (c "Nat") :default)
          lhs (e/app (e/const' family []) (e/bvar 0))
          equation (e/forall' "n" (c "Nat") (eq lhs (c "Bool")) :default)
          en (-> en
                 (env/check-constant (env/mk-def family [] family-type value))
                 (env/check-constant (env/mk-axiom (name/from-string "unfoldFamily.eq_def") [] equation)))
          pi (e/forall' "n" (c "Nat") lhs :default)
          r (simp/unfold-expr (tc/mk-tc-state en) en pi (name/from-string "unfoldFamily.eq_def"))]
      (is (= pi (:expr r)))
      (is (nil? (:proof? r))))))

(deftest matcher-unfolds-nested-dite-only-in-its-value
  (let [nat (c "Nat") bool (c "Bool") unit (c "Unit")
        unitnat (e/arrow unit nat)
        motive-type (e/arrow bool (e/sort' (lvl/succ lvl/zero)))
        ty (e/arrow motive-type (e/arrow bool (e/arrow unitnat (e/arrow unitnat nat))))
        body (e/app* (e/const' (name/from-string "Bool.rec") [(lvl/succ lvl/zero)])
                     (e/lam "b" bool nat :default)
                     (e/app (e/bvar 1) (c "Unit.unit"))
                     (e/app (e/bvar 0) (c "Unit.unit")) (e/bvar 2))
        value (e/lam "motive" motive-type
                     (e/lam "b" bool (e/lam "f" unitnat (e/lam "t" unitnat body :default) :default)
                            :default) :default)
        decide (e/app* (c "Decidable.isTrue") (c "True") (c "True.intro"))
        dite (fn [type level yes no]
               (e/app* (e/const' (name/from-string "dite") [level]) type (c "True") decide
                       (e/lam "h" (c "True") yes :default)
                       (e/lam "h" (e/app (c "Not") (c "True")) no :default)))
        level (e/sort-level (tc/infer-type (tc/mk-tc-state (a/env)) ty))
        value (dite ty level value value)
        n (name/from-string "nestedDiteMatcher")
        en (-> (a/env)
               (env/check-constant (env/mk-def n [] ty value))
               (matcher-info/add-matcher-info "nestedDiteMatcher"
                                              {:num-params 0 :num-discrs 1 :alts [{:unit-thunk true} {:unit-thunk true}]}))
        expr (fn [discr]
               (e/app* (e/const' n []) (e/lam "b" bool nat :default) discr
                       (e/lam "u" unit (e/lit-nat 13) :default)
                       (e/lam "u" unit (e/lit-nat 21) :default)))
        st (tc/mk-tc-state en)
        app (expr (c "Bool.false"))]
    (is (= nat (tc/infer-type st app)))
    (is (= (e/lit-nat 13) (:expr (#'simp/try-reduce-matcher st app))))
    (is (= (e/lit-nat 13) (#'simp/dsimp-expr en {} app 20)))
    (is (nil? (with-redefs-fn {#'simp/unfold-nested-dite (fn [_ value] value)}
                #(#'simp/try-reduce-matcher st app))))
    (is (nil? (#'simp/try-reduce-matcher st
                                         (expr (dite bool (lvl/succ lvl/zero) (c "Bool.false") (c "Bool.true"))))))))

(deftest bundled-literal-matcher-reduces-nested-dite
  (let [nat (c "Nat") unit (c "Unit") en (a/env)
        matcher (e/const' (name/from-string "Lean.Grind.CommRing.Power.denote.match_1")
                          [(lvl/succ lvl/zero)])
        expr (e/app* matcher (e/lam "k" nat nat :default) (e/lit-nat 2)
                     (e/lam "u" unit (e/lit-nat 13) :default)
                     (e/lam "u" unit (e/lit-nat 21) :default)
                     (e/lam "k" nat (e/bvar 0) :default))
        st (tc/mk-tc-state en)]
    (is (tc/is-def-eq st nat (tc/infer-type st expr)))
    (is (= (e/lit-nat 2) (:expr (#'simp/try-reduce-matcher st expr))))
    (is (= (e/lit-nat 2) (#'simp/dsimp-expr en {} expr 20)))))
