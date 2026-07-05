(ns ansatz.tactic.basic-tactics-test
  "Tests for new core tactics: induction, have, revert, exfalso, subst, clear,
   and tactic combinators."
  (:require [clojure.test :refer [deftest testing is]]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.env :as env]
            [ansatz.tactic.proof :as proof]
            [ansatz.tactic.basic :as basic]
            [ansatz.tactic.extract :as extract]
            [ansatz.export.parser :as parser]
            [ansatz.export.replay :as replay]))

(def ^:private init-medium-env
  (delay
    (let [f "test-data/init-medium.ndjson"]
      (when (.exists (java.io.File. f))
        (let [st (parser/parse-ndjson-file f)
              result (replay/replay (:decls st))]
          (:env result))))))

(defn- require-env []
  (or @init-medium-env
      (throw (ex-info "init-medium.ndjson not found" {}))))

(def ^:private nat (e/const' (name/from-string "Nat") []))
(def ^:private u1 (lvl/succ lvl/zero))
(def ^:private prop (e/sort' lvl/zero))
(defn- mk-eq [a b]
  (e/app* (e/const' (name/from-string "Eq") [u1]) nat a b))

(defn- find-hyp [ps hyp-name]
  (let [g (proof/current-goal ps)]
    (some (fn [[id d]] (when (= hyp-name (:name d)) id)) (:lctx g))))

;; ============================================================
;; exact
;; ============================================================

(deftest test-exact-form-closes-goal
  (testing "exact elaborates a surface term against the current target"
    (let [env (env/empty-env)
          goal-type (e/forall' "p" prop
                               (e/forall' "h" (e/bvar 0) (e/bvar 1) :default)
                               :default)
          [ps _] (proof/start-proof env goal-type)
          ps (-> ps
                 (basic/intro "p")
                 (basic/intro "h")
                 (basic/exact-form 'h))]
      (is (proof/solved? ps))
      (is (not (e/has-fvar-flag (extract/verify ps)))))))

(deftest test-exact-form-rejects-holes
  (testing "exact rejects fresh unassigned holes instead of creating goals"
    (let [env (env/empty-env)
          goal-type (e/forall' "p" prop (e/bvar 0) :default)
          [ps _] (proof/start-proof env goal-type)
          ps (basic/intro ps "p")]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"exact: unresolved natural holes"
                            (basic/exact-form ps '_)))
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"exact: unresolved holes"
                            (basic/exact-form ps '?goal))))))

;; ============================================================
;; induction
;; ============================================================

(deftest test-induction-nat-rfl
  (testing "Induction on Nat with rfl in both cases"
    (let [env (require-env)
          goal (e/forall' "n" nat (mk-eq (e/bvar 0) (e/bvar 0)) :default)
          [ps _] (proof/start-proof env goal)
          ps (basic/intro ps "n")
          n-id (find-hyp ps "n")
          ps (basic/induction ps n-id)]
      ;; Should have 2 goals: base + step
      (is (= 2 (count (:goals ps))))
      ;; Close both with rfl
      (let [ps (basic/rfl ps)
            ps (basic/rfl ps)]
        (is (proof/solved? ps))))))

(deftest test-induction-creates-ih
  (testing "Induction step case has induction hypothesis in context"
    (let [env (require-env)
          goal (e/forall' "n" nat (mk-eq (e/bvar 0) (e/bvar 0)) :default)
          [ps _] (proof/start-proof env goal)
          ps (basic/intro ps "n")
          n-id (find-hyp ps "n")
          ps (basic/induction ps n-id)
          ;; Skip base case
          ps (basic/rfl ps)
          ;; Check step case has IH
          g (proof/current-goal ps)
          has-ih (some (fn [[_ d]] (.startsWith (str (:name d)) "ih_")) (:lctx g))]
      (is has-ih "Induction step should have IH in context"))))

;; ============================================================
;; have
;; ============================================================

(deftest test-have-creates-two-goals
  (testing "have creates proof goal and body goal"
    (let [env (require-env)
          goal (e/forall' "n" nat (mk-eq (e/bvar 0) (e/bvar 0)) :default)
          [ps _] (proof/start-proof env goal)
          ps (basic/intro ps "n")
          ;; have h : True := ...
          true-type (e/const' (name/from-string "True") [])
          ps (basic/have-tac ps "h" true-type)]
      (is (= 2 (count (:goals ps)))))))

;; ============================================================
;; revert
;; ============================================================

(deftest test-revert-adds-forall
  (testing "revert moves hypothesis back into goal"
    (let [env (require-env)
          goal (e/forall' "n" nat (mk-eq (e/bvar 0) (e/bvar 0)) :default)
          [ps _] (proof/start-proof env goal)
          ps (basic/intro ps "n")
          n-id (find-hyp ps "n")
          ps (basic/revert ps n-id)
          g (proof/current-goal ps)]
      ;; Goal should be a forall again
      (is (e/forall? (:type g)))
      ;; Close with intro + rfl
      (let [ps (basic/intro ps "m")
            ps (basic/rfl ps)]
        (is (proof/solved? ps))))))

;; ============================================================
;; exfalso
;; ============================================================

(deftest test-exfalso-changes-goal-to-false
  (testing "exfalso changes goal to False"
    (let [env (require-env)
          false-type (e/const' (name/from-string "False") [])
          goal (e/forall' "h" false-type (mk-eq (e/lit-nat 0) (e/lit-nat 1)) :default)
          [ps _] (proof/start-proof env goal)
          ps (basic/intro ps "h")
          ps (basic/exfalso ps)
          g (proof/current-goal ps)]
      ;; Goal should be False
      (is (e/const? (:type g)))
      (is (= "False" (name/->string (e/const-name (:type g)))))
      ;; Close with assumption (h : False)
      (let [ps (basic/assumption ps)]
        (is (proof/solved? ps))))))

;; ============================================================
;; change
;; ============================================================

(deftest test-change-solves-natural-holes
  (testing "change solves natural placeholders by defeq against the current target"
    (let [env (env/empty-env)
          goal-type (e/forall' "p" prop
                               (e/forall' "h" (e/bvar 0) (e/bvar 1) :default)
                               :default)
          [ps _] (proof/start-proof env goal-type)
          ps (-> ps
                 (basic/intro "p")
                 (basic/intro "h")
                 (basic/change '_))]
      (is (= 1 (count (:goals ps))))
      (let [ps (basic/assumption ps)]
        (is (proof/solved? ps))
        (is (not (e/has-fvar-flag (extract/verify ps))))))))

(deftest test-change-rejects-non-defeq-target
  (testing "change rejects a replacement target that is not definitionally equal"
    (let [env (env/empty-env)
          goal-type (e/forall' "p" prop (e/bvar 0) :default)
          [ps _] (proof/start-proof env goal-type)
          ps (basic/intro ps "p")]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"change.*failed"
                            (basic/change ps '(arrow p p)))))))

;; ============================================================
;; show
;; ============================================================

(deftest test-show-current-goal
  (testing "show changes the current matching goal"
    (let [env (env/empty-env)
          goal-type (e/forall' "p" prop
                               (e/forall' "h" (e/bvar 0) (e/bvar 1) :default)
                               :default)
          [ps _] (proof/start-proof env goal-type)
          ps (-> ps
                 (basic/intro "p")
                 (basic/intro "h")
                 (basic/show '_))]
      (is (= 1 (count (:goals ps))))
      (let [ps (basic/assumption ps)]
        (is (proof/solved? ps))
        (is (not (e/has-fvar-flag (extract/verify ps))))))))

(deftest test-show-finds-later-goal
  (testing "show focuses the first later goal whose target matches"
    (let [env (env/empty-env)
          goal-type (e/forall' "p" prop
                               (e/forall' "h" (e/bvar 0) (e/bvar 1) :default)
                               :default)
          [ps _] (proof/start-proof env goal-type)
          ps (-> ps
                 (basic/intro "p")
                 (basic/intro "h"))
          p-id (find-hyp ps "p")
          p-expr (e/fvar p-id)
          ps (basic/have-tac ps "k" (e/forall' "hp" p-expr p-expr :default))
          ps (basic/show ps 'p)
          current (proof/current-goal ps)]
      (is (some (fn [[_ d]] (= "k" (:name d))) (:lctx current))
          "the body goal introduced by have should be focused")
      (let [ps (basic/assumption ps)
            ps (basic/intro ps "hp")
            ps (basic/assumption ps)]
        (is (proof/solved? ps))
        (is (not (e/has-fvar-flag (extract/verify ps))))))))

;; ============================================================
;; clear
;; ============================================================

(deftest test-clear-removes-hypothesis
  (testing "clear removes hypothesis from context"
    (let [env (require-env)
          goal (e/forall' "n" nat
                          (e/forall' "m" nat
                                     (mk-eq (e/bvar 1) (e/bvar 1)) :default) :default)
          [ps _] (proof/start-proof env goal)
          ps (basic/intros ps ["n" "m"])
          m-id (find-hyp ps "m")]
      (is (= 2 (count (:lctx (proof/current-goal ps)))))
      (let [ps (basic/clear ps m-id)]
        (is (= 1 (count (:lctx (proof/current-goal ps)))))
        (let [ps (basic/rfl ps)]
          (is (proof/solved? ps)))))))

(deftest test-clear-rejects-dependent-hypothesis
  (testing "clear rejects hypotheses used by later declarations or the target"
    (let [env (env/empty-env)
          goal-type (e/forall' "p" prop
                               (e/forall' "h" (e/bvar 0) (e/bvar 1) :default)
                               :default)
          [ps _] (proof/start-proof env goal-type)
          ps (-> ps
                 (basic/intro "p")
                 (basic/intro "h"))
          p-id (find-hyp ps "p")]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"clear: local declaration depends"
                            (basic/clear ps p-id))))))

;; ============================================================
;; specialize
;; ============================================================

(deftest test-specialize-local-hypothesis
  (testing "specialize replaces a quantified local hypothesis with an applied one"
    (let [env (env/empty-env)
          goal-type (e/forall' "p" prop
                               (e/forall' "q" prop
                                          (e/forall' "h" (e/forall' "hp" (e/bvar 1) (e/bvar 1) :default)
                                                     (e/forall' "hp" (e/bvar 2) (e/bvar 2) :default)
                                                     :default)
                                          :default)
                               :default)
          [ps _] (proof/start-proof env goal-type)
          ps (-> ps
                 (basic/intro "p")
                 (basic/intro "q")
                 (basic/intro "h")
                 (basic/intro "hp")
                 (basic/specialize '(h hp))
                 (basic/assumption))]
      (is (proof/solved? ps))
      (is (not (e/has-fvar-flag (extract/verify ps)))))))

(deftest test-specialize-promotes-argument-holes
  (testing "specialize puts elaboration holes before the body goal"
    (let [env (env/empty-env)
          goal-type (e/forall' "p" prop
                               (e/forall' "q" prop
                                          (e/forall' "h" (e/forall' "hp" (e/bvar 1) (e/bvar 1) :default)
                                                     (e/forall' "hp" (e/bvar 2) (e/bvar 2) :default)
                                                     :default)
                                          :default)
                               :default)
          [ps _] (proof/start-proof env goal-type)
          ps (-> ps
                 (basic/intro "p")
                 (basic/intro "q")
                 (basic/intro "h")
                 (basic/intro "hp")
                 (basic/specialize '(h _)))]
      (is (= 2 (count (:goals ps))))
      (let [ps (basic/assumption ps)
            ps (basic/assumption ps)]
        (is (proof/solved? ps))
        (is (not (e/has-fvar-flag (extract/verify ps))))))))

;; ============================================================
;; Tactic combinators
;; ============================================================

(deftest test-try-tac-success
  (testing "try-tac returns result on success"
    (let [env (require-env)
          goal (e/forall' "n" nat (mk-eq (e/bvar 0) (e/bvar 0)) :default)
          [ps _] (proof/start-proof env goal)
          ps (basic/intro ps "n")
          ps (basic/try-tac ps basic/rfl)]
      (is (proof/solved? ps)))))

(deftest test-try-tac-failure
  (testing "try-tac returns unchanged on failure"
    (let [env (require-env)
          goal (e/forall' "n" nat (mk-eq (e/bvar 0) (e/bvar 0)) :default)
          [ps _] (proof/start-proof env goal)
          ps (basic/intro ps "n")
          ps2 (basic/try-tac ps basic/assumption)]
      (is (not (proof/solved? ps2))))))

(deftest test-or-else
  (testing "or-else tries second on first failure"
    (let [env (require-env)
          goal (e/forall' "n" nat (mk-eq (e/bvar 0) (e/bvar 0)) :default)
          [ps _] (proof/start-proof env goal)
          ps (basic/intro ps "n")
          ps (basic/or-else ps basic/assumption basic/rfl)]
      (is (proof/solved? ps)))))

(deftest test-first-tac
  (testing "first-tac tries each in order"
    (let [env (require-env)
          goal (e/forall' "n" nat (mk-eq (e/bvar 0) (e/bvar 0)) :default)
          [ps _] (proof/start-proof env goal)
          ps (basic/intro ps "n")
          ps (basic/first-tac ps basic/assumption basic/rfl)]
      (is (proof/solved? ps)))))

(deftest test-all-goals
  (testing "all-goals applies tactic to every open goal"
    (let [env (require-env)
          goal (e/forall' "n" nat (mk-eq (e/bvar 0) (e/bvar 0)) :default)
          [ps _] (proof/start-proof env goal)
          ps (basic/intro ps "n")
          n-id (find-hyp ps "n")
          ;; induction creates 2 goals, both solvable by rfl
          ps (basic/induction ps n-id)
          ps (basic/all-goals ps basic/rfl)]
      (is (proof/solved? ps)))))

(deftest test-clear-replaces-goal-in-position
  (testing "clear (and thus replace) keeps focus on the current branch even
   with background goals — the replacement goal takes the cleared goal's slot"
    (let [env (require-env)
          ;; p → q → p ∧ p : two And subgoals after constructor, then clear q
          ;; on the FIRST; the current goal must stay the first branch.
          goal-type (e/forall' "p" prop
                               (e/forall' "hp" (e/bvar 0)
                                          (e/forall' "hq" (e/bvar 1)
                                                     (e/app* (e/const' (name/from-string "And") [])
                                                             (e/bvar 2) (e/bvar 2))
                                                     :default)
                                          :default)
                               :default)
          [ps _] (proof/start-proof env goal-type)
          ps (-> ps (basic/intro "p") (basic/intro "hp") (basic/intro "hq"))
          hq-id (some (fn [[id d]] (when (= "hq" (:name d)) id))
                      (:lctx (proof/current-goal ps)))
          ps (basic/constructor ps)
          n-goals (count (:goals ps))
          first-goal-type (:type (proof/current-goal ps))
          ps' (basic/clear ps hq-id)]
      (is (= 2 n-goals))
      ;; same number of goals, same current target, hq gone from its context
      (is (= n-goals (count (:goals ps'))))
      (is (= first-goal-type (:type (proof/current-goal ps'))))
      (is (nil? (get (:lctx (proof/current-goal ps')) hq-id)))
      ;; and the state still closes
      (let [done (-> ps' basic/assumption basic/assumption)]
        (is (proof/solved? done))
        (is (some? (extract/verify done)))))))
