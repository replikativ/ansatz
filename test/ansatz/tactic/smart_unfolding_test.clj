(ns ansatz.tactic.smart-unfolding-test
  "Structural smart unfolding and eq_def (Lean Structural/SmartUnfolding.lean,
   Meta/WHNF.lean smartUnfoldingReduce?, Simp.unfoldEvenWithEqns, Meta/Tactic/Unfold.lean).
   Lean pair: test/lean/smart_unfolding.lean.

   Reported by spindel: after #407 split nested matches into leaf equations (as Lean does),
   `simp only [f]` could no longer unfold `f best (h :: t)` with `best` a variable, because
   no split equation matches and there was no smart-unfolding fallback."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [ansatz.core :as a]
            [ansatz.fixtures :as fixtures]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.elab.structural-smart-unfolding :as sunfold]
            [ansatz.tactic.proof :as proof]))

(use-fixtures :once fixtures/isolated-session
  (fn [t]
    (a/load-init!)
    (binding [a/*verbose* false *ns* (the-ns 'ansatz.tactic.smart-unfolding-test)]
      (eval '(a/defn su-pick [best :- (Option Nat), es :- (List Nat)] (Option Nat)
               (match es
                 [nil best]
                 [(cons h t) (su-pick (match best [none (Option.some Nat h)]
                                             [(some b) (if (Nat.blt h b) (Option.some Nat h) best)])
                                      t)])))
      (t))))

(defn- failure [form]
  (try (binding [*ns* (the-ns 'ansatz.tactic.smart-unfolding-test)] (eval form)) nil
       (catch clojure.lang.ExceptionInfo ex ex)))

(defn- hypothesis-after
  "The type of `hh` after `tactics`, from `(=> (= (su-pick ...) (some e)) True)`."
  [binders lhs tactics]
  (let [seen (atom nil)
        form (list* 'a/theorem (gensym "su-probe-") binders
                    (list '=> (list '= lhs '(Option.some Nat e)) 'True)
                    '(intro hh)
                    (concat tactics
                            [(list 'exact 'True.intro)]))]
    (with-redefs [a/*verbose* false]
      (binding [*ns* (the-ns 'ansatz.tactic.smart-unfolding-test)]
        (let [orig proof/assign-mvar]
          (with-redefs [proof/assign-mvar (fn [ps id assignment]
                                            (when (= :exact (:kind assignment))
                                              (when-let [g (proof/current-goal ps)]
                                                (reset! seen (some (fn [[_ d]] (when (= "hh" (str (:name d))) (:type d)))
                                                                   (:lctx g)))))
                                            (orig ps id assignment))]
            (eval form)))))
    @seen))

(defn- lhs-of [eq-type] (nth (e/get-app-args eq-type) 1))
(defn- head-name [x] (let [h (e/get-app-fn x)] (when (e/const? h) (name/->string (e/const-name h)))))

(deftest smart-unfolding-definition-is-annotated
  (let [environment (a/env)
        aux (env/lookup environment (name/from-string "su-pick._sunfold"))]
    (is (some? aux))
    (is (sunfold/contains-smart-unfolding-match? (.value aux)))
    (is (= 1 (sunfold/structural-rec-arg-pos environment (name/from-string "su-pick"))))
    (is (some? (env/lookup environment (name/from-string "su-pick.eq_def"))))
    (testing "the equations stay split per constructor of the nested match, as in Lean"
      (is (= ["su-pick.eq_1" "su-pick.eq_2" "su-pick.eq_3"]
             (mapv name/->string ((requiring-resolve 'ansatz.eqns/eqns-for)
                                  environment (name/from-string "su-pick"))))))))

(deftest simp-only-unfolds-through-the-smart-unfolding-definition
  (let [hh (hypothesis-after '[best :- (Option Nat), h :- Nat, t :- (List Nat), e :- Nat]
                             '(su-pick best (List.cons Nat h t))
                             '[(simp only [su-pick] at hh)])
        lhs (lhs-of hh)]
    ;; su-pick (match best ...) t: one step, the nested match on `best` kept
    (is (= "su-pick" (head-name lhs)))
    (is (= "su-pick.match_2" (head-name (first (e/get-app-args lhs))))))
  (is (nil? (failure '(a/theorem su-goal [best :- (Option Nat), h :- Nat, t :- (List Nat)]
                                 (= (su-pick best (List.cons Nat h t))
                                    (su-pick (match best [none (Option.some Nat h)]
                                                    [(some b) (if (Nat.blt h b) (Option.some Nat h) best)]) t))
                                 (simp only [su-pick])))))
  (testing "the applicable split equation is still used"
    (is (nil? (failure '(a/theorem su-none [h :- Nat, t :- (List Nat)]
                                   (= (su-pick (Option.none Nat) (List.cons Nat h t)) (su-pick (Option.some Nat h) t))
                                   (simp only [su-pick]))))))
  (testing "a stuck structural argument: no progress, as in Lean"
    (is (re-find #"simp made no progress"
                 (str (ex-message (failure '(a/theorem su-stuck [best :- (Option Nat), es :- (List Nat), e :- Nat]
                                                       (=> (= (su-pick best es) (Option.some Nat e)) True)
                                                       (intro hh) (simp only [su-pick] at hh) (exact True.intro))))))))
  (testing "rw has no unfold fallback, as in Lean"
    (is (some? (failure '(a/theorem su-rw [best :- (Option Nat), h :- Nat, t :- (List Nat), e :- Nat]
                                    (=> (= (su-pick best (List.cons Nat h t)) (Option.some Nat e)) True)
                                    (intro hh) (rw [su-pick] at hh) (exact True.intro)))))))

(deftest unfold-rewrites-with-eq-def-at-locations
  (let [hh (hypothesis-after '[best :- (Option Nat), h :- Nat, t :- (List Nat), e :- Nat]
                             '(su-pick best (List.cons Nat h t))
                             '[(unfold su-pick at hh)])]
    (is (= "su-pick" (head-name (lhs-of hh)))))
  (testing "a variable structural argument leaves `match es with ...`"
    (let [hh (hypothesis-after '[best :- (Option Nat), es :- (List Nat), e :- Nat]
                               '(su-pick best es)
                               '[(unfold su-pick at hh)])]
      (is (= "su-pick.match_1" (head-name (lhs-of hh))))))
  (testing "at * and at the goal"
    (is (nil? (failure '(a/theorem su-star [best :- (Option Nat), h :- Nat, t :- (List Nat), e :- Nat,
                                            hh :- (= (su-pick best (List.cons Nat h t)) (Option.some Nat e))]
                                   True (unfold su-pick at *) (exact True.intro)))))
    (is (nil? (failure '(a/theorem su-nil [best :- (Option Nat)] (= (su-pick best (List.nil Nat)) best)
                                   (unfold su-pick) (rfl))))))
  (testing "a hypothesis without the constant is an error naming it"
    (is (re-find #"failed to unfold `su-pick` in"
                 (str (ex-message (failure '(a/theorem su-none-there [x :- Nat, hx :- (= x 1)] True
                                                       (unfold su-pick at hx) (exact True.intro)))))))))
