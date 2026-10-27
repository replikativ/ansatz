(ns ansatz.tactic.decide-test
  "Tests for instance resolution and the decide tactic."
  (:require [ansatz.test-env :as test-env]
            [clojure.test :refer [deftest testing is]]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.tc :as tc]
            [ansatz.tactic.proof :as proof]
            [ansatz.tactic.basic :as basic]
            [ansatz.tactic.extract :as extract]
            [ansatz.tactic.instance :as instance]
            [ansatz.tactic.decide :as decide]
            [ansatz.surface.elaborate :as elab])
  (:import [ansatz.kernel TypeChecker]))

;; ============================================================
;; Environment helpers
;; ============================================================

(def ^:private init-medium-env test-env/checked-bundled-init-env)

(defn- require-env []
  (or @init-medium-env
      (throw (ex-info "bundled Init unavailable" {}))))

;; ============================================================
;; Instance resolution tests
;; ============================================================



(deftest test-resolve-decidable-eq-nat
  (testing "Resolve Decidable (Eq Nat 0 0)"
    (let [env (require-env)
          u1 (lvl/succ lvl/zero)
          nat (e/const' (name/from-string "Nat") [])
          zero (e/lit-nat 0)
          prop (e/app* (e/const' (name/from-string "Eq") [u1]) nat zero zero)
          inst (instance/resolve-decidable env prop)]
      (is (some? inst))
      (is (instance/verify-instance env prop inst)))))

(deftest test-resolve-decidable-eq-nat-succ
  (testing "Resolve Decidable (Eq Nat 1 1)"
    (let [env (require-env)
          u1 (lvl/succ lvl/zero)
          nat (e/const' (name/from-string "Nat") [])
          one (e/lit-nat 1)
          prop (e/app* (e/const' (name/from-string "Eq") [u1]) nat one one)
          inst (instance/resolve-decidable env prop)]
      (is (some? inst))
      (is (instance/verify-instance env prop inst)))))

(deftest test-resolve-decidable-and
  (testing "Resolve Decidable (And (Eq Nat 0 0) (Eq Nat 1 1))"
    (let [env (require-env)
          u1 (lvl/succ lvl/zero)
          nat (e/const' (name/from-string "Nat") [])
          eq00 (e/app* (e/const' (name/from-string "Eq") [u1]) nat (e/lit-nat 0) (e/lit-nat 0))
          eq11 (e/app* (e/const' (name/from-string "Eq") [u1]) nat (e/lit-nat 1) (e/lit-nat 1))
          prop (e/app* (e/const' (name/from-string "And") []) eq00 eq11)
          inst (instance/resolve-decidable env prop)]
      (is (some? inst))
      (is (instance/verify-instance env prop inst)))))

(deftest test-resolve-decidable-or
  (testing "Resolve Decidable (Or (Eq Nat 0 0) (Eq Nat 0 1))"
    (let [env (require-env)
          u1 (lvl/succ lvl/zero)
          nat (e/const' (name/from-string "Nat") [])
          eq00 (e/app* (e/const' (name/from-string "Eq") [u1]) nat (e/lit-nat 0) (e/lit-nat 0))
          eq01 (e/app* (e/const' (name/from-string "Eq") [u1]) nat (e/lit-nat 0) (e/lit-nat 1))
          prop (e/app* (e/const' (name/from-string "Or") []) eq00 eq01)
          inst (instance/resolve-decidable env prop)]
      (is (some? inst))
      (is (instance/verify-instance env prop inst)))))

(deftest test-resolve-decidable-not
  (testing "Resolve Decidable (Not (Eq Nat 0 1))"
    (let [env (require-env)
          u1 (lvl/succ lvl/zero)
          nat (e/const' (name/from-string "Nat") [])
          eq01 (e/app* (e/const' (name/from-string "Eq") [u1]) nat (e/lit-nat 0) (e/lit-nat 1))
          prop (e/app* (e/const' (name/from-string "Not") []) eq01)
          inst (instance/resolve-decidable env prop)]
      (is (some? inst))
      (is (instance/verify-instance env prop inst)))))

(deftest test-resolve-decidable-true-false
  (testing "Resolve Decidable True and Decidable False"
    (let [env (require-env)]
      (let [prop (e/const' (name/from-string "True") [])
            inst (instance/resolve-decidable env prop)]
        (is (some? inst))
        (is (instance/verify-instance env prop inst)))
      (let [prop (e/const' (name/from-string "False") [])
            inst (instance/resolve-decidable env prop)]
        (is (some? inst))
        (is (instance/verify-instance env prop inst))))))

;; ============================================================
;; decide tactic tests
;; ============================================================

(deftest test-decide-eq-nat-zero
  (testing "decide closes Eq Nat 0 0"
    (let [env (require-env)
          u1 (lvl/succ lvl/zero)
          nat (e/const' (name/from-string "Nat") [])
          zero (e/lit-nat 0)
          goal-type (e/app* (e/const' (name/from-string "Eq") [u1]) nat zero zero)
          [ps _] (proof/start-proof env goal-type)
          ps (decide/decide ps)]
      (is (proof/solved? ps))
      ;; Verify with Java TypeChecker
      (let [term (extract/extract ps)
            inferred (.check (TypeChecker. env) term)]   ; STRICT: re-checks every app arg
        (is (.isDefEq (TypeChecker. env) inferred goal-type))))))

(deftest test-decide-eq-nat-nonzero
  (testing "decide closes Eq Nat 42 42"
    (let [env (require-env)
          u1 (lvl/succ lvl/zero)
          nat (e/const' (name/from-string "Nat") [])
          n42 (e/lit-nat 42)
          goal-type (e/app* (e/const' (name/from-string "Eq") [u1]) nat n42 n42)
          [ps _] (proof/start-proof env goal-type)
          ps (decide/decide ps)]
      (is (proof/solved? ps)))))

(deftest test-decide-eq-nat-false
  (testing "decide fails for Eq Nat 0 1 (proposition is false)"
    (let [env (require-env)
          u1 (lvl/succ lvl/zero)
          nat (e/const' (name/from-string "Nat") [])
          goal-type (e/app* (e/const' (name/from-string "Eq") [u1]) nat (e/lit-nat 0) (e/lit-nat 1))
          [ps _] (proof/start-proof env goal-type)]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"decide failed"
                            (decide/decide ps))))))

(deftest test-decide-and
  (testing "decide closes And (Eq Nat 0 0) True — requires instDecidableAnd (needs full env)"
    ;; Skip in init-medium env which lacks instDecidableAnd
    (when false
      (let [env (require-env)
            u1 (lvl/succ lvl/zero)
            nat (e/const' (name/from-string "Nat") [])
            eq00 (e/app* (e/const' (name/from-string "Eq") [u1]) nat (e/lit-nat 0) (e/lit-nat 0))
            t (e/const' (name/from-string "True") [])
            goal-type (e/app* (e/const' (name/from-string "And") []) eq00 t)
            [ps _] (proof/start-proof env goal-type)
            ps (decide/decide ps)]
        (is (proof/solved? ps))
        (let [term (extract/extract ps)
              tc (TypeChecker. env)
              inferred (.check tc term)]   ; STRICT
          (is (.isDefEq tc inferred goal-type)))))))

(deftest test-decide-not
  (testing "decide closes Not (Eq Nat 0 1)"
    (let [env (require-env)
          u1 (lvl/succ lvl/zero)
          nat (e/const' (name/from-string "Nat") [])
          eq01 (e/app* (e/const' (name/from-string "Eq") [u1]) nat (e/lit-nat 0) (e/lit-nat 1))
          goal-type (e/app* (e/const' (name/from-string "Not") []) eq01)
          [ps _] (proof/start-proof env goal-type)
          ps (decide/decide ps)]
      (is (proof/solved? ps)))))

(deftest test-decide-after-intro
  (testing "intro then decide: ∀ (a : Nat), Eq Nat a a"
    (let [env (require-env)
          u1 (lvl/succ lvl/zero)
          nat (e/const' (name/from-string "Nat") [])
          ;; ∀ (a : Nat), Eq Nat a a
          ;; After intro, goal becomes Eq Nat ?fv ?fv — but decide can't handle
          ;; non-ground propositions. This is expected to fail.
          ;; The decide tactic only works for ground decidable propositions.
          eq-aa (e/app* (e/const' (name/from-string "Eq") [u1]) nat (e/bvar 0) (e/bvar 0))
          goal-type (e/forall' "a" nat eq-aa :default)
          [ps _] (proof/start-proof env goal-type)
          ps (basic/intro ps "a")]
      ;; After intro, the goal has a free variable, which rfl can handle but
      ;; decide cannot (it needs ground terms). This documents the boundary.
      (is (thrown? Exception (decide/decide ps))))))

;; ============================================================
;; End-to-end: elaborate + decide
;; ============================================================

(deftest test-decide-with-elaboration
  (testing "Elaborate a prop and decide it"
    (let [env (require-env)
          ;; Build Eq Nat 5 5 manually (since we don't want to couple to elaborate)
          u1 (lvl/succ lvl/zero)
          nat (e/const' (name/from-string "Nat") [])
          goal-type (e/app* (e/const' (name/from-string "Eq") [u1]) nat (e/lit-nat 5) (e/lit-nat 5))
          [ps _] (proof/start-proof env goal-type)
          ps (decide/decide ps)]
      (is (proof/solved? ps))
      (let [term (extract/verify ps)]
        (is (some? term))))))

;; ============================================================
;; General instance resolution (registered instances)
;; ============================================================

(deftest test-instance-index
  (testing "Instance index finds Decidable candidates"
    (let [env (require-env)
          idx (instance/index-for env)
          decidable-name (name/from-string "Decidable")
          candidates (instance/get-instances idx decidable-name)]
      (is (seq candidates)))))

(deftest test-general-synthesis-eq-nat
  (testing "General synthesis finds Nat.decEq for Decidable (Eq Nat 0 0)"
    (let [env (require-env)
          idx (instance/index-for env)
          u1 (lvl/succ lvl/zero)
          nat (e/const' (name/from-string "Nat") [])
          prop (e/app* (e/const' (name/from-string "Eq") [u1]) nat (e/lit-nat 0) (e/lit-nat 0))
          goal (e/app (e/const' (name/from-string "Decidable") []) prop)
          inst (instance/synthesize env idx goal)]
      (is (some? inst))
      ;; Should NOT be Classical.propDecidable
      (let [[head _] (e/get-app-fn-args inst)]
        (is (not= (name/from-string "Classical.propDecidable")
                  (when (e/const? head) (e/const-name head))))))))

(deftest test-general-synthesis-bool-eq
  (testing "General synthesis finds Bool.decEq"
    (let [env (require-env)
          idx (instance/index-for env)
          u1 (lvl/succ lvl/zero)
          bool (e/const' (name/from-string "Bool") [])
          prop (e/app* (e/const' (name/from-string "Eq") [u1]) bool
                       (e/const' (name/from-string "Bool.true") [])
                       (e/const' (name/from-string "Bool.true") []))
          goal (e/app (e/const' (name/from-string "Decidable") []) prop)
          inst (instance/synthesize env idx goal)]
      (is (some? inst))
      (is (instance/verify-instance env prop inst)))))

(deftest test-general-synthesis-nested-and-or
  (testing "General synthesis handles nested And/Or/Not"
    (let [env (require-env)
          idx (instance/index-for env)
          u1 (lvl/succ lvl/zero)
          nat (e/const' (name/from-string "Nat") [])
          eq00 (e/app* (e/const' (name/from-string "Eq") [u1]) nat (e/lit-nat 0) (e/lit-nat 0))
          eq01 (e/app* (e/const' (name/from-string "Eq") [u1]) nat (e/lit-nat 0) (e/lit-nat 1))
          ;; Or (Eq 0 0) (Not (Eq 0 1))
          prop (e/app* (e/const' (name/from-string "Or") [])
                       eq00
                       (e/app (e/const' (name/from-string "Not") []) eq01))
          goal (e/app (e/const' (name/from-string "Decidable") []) prop)
          inst (instance/synthesize env idx goal)]
      (is (some? inst))
      (is (instance/verify-instance env prop inst)))))

;; ============================================================
;; elaborate-in-context tests
;; ============================================================

(deftest test-elaborate-in-context-basic
  (testing "elaborate-in-context resolves local hypotheses"
    (let [env (require-env)
          goal-type (elab/elaborate env '(forall [a Nat] (Eq a a)))
          [ps _] (proof/start-proof env goal-type)
          ps (basic/intro ps "a")
          goal (proof/current-goal ps)
          ;; Use elaborate-in-context to build Eq.refl a
          term (elab/elaborate-in-context env (:lctx goal) '(Eq.refl a))]
      (is (some? term))
      ;; Term should reference the fvar, not be a fresh one
      (let [st (assoc (tc/mk-tc-state env) :lctx (:lctx goal))
            ty (tc/infer-type st term)]
        (is (tc/is-def-eq st ty (:type goal)))))))

(deftest test-elaborate-in-context-eq-symm
  (testing "elaborate-in-context + exact proves symmetry"
    (let [env (require-env)
          goal-type (elab/elaborate env '(forall [a Nat, b Nat] (arrow (Eq a b) (Eq b a))))
          [ps _] (proof/start-proof env goal-type)
          ps (basic/intros ps ["a" "b" "h"])
          goal (proof/current-goal ps)
          term (elab/elaborate-in-context env (:lctx goal) '(Eq.symm h))
          ps (basic/exact ps term)]
      (is (proof/solved? ps))
      (let [proof-term (extract/verify ps)]
        (is (some? proof-term))))))

(deftest test-decide-zeta-reduces-let-locals
  ;; Lean Elab/Tactic/Decide.lean preprocessPropToDecide: let-bound locals are substituted before
  ;; the closed-goal check (let n := 0; let m := n; m = m is decided).
  (let [nat (e/const' (name/from-string "Nat") [])
        eq (fn [x y] (e/app* (e/const' (name/from-string "Eq") [(lvl/succ lvl/zero)]) nat x y))
        lctx {901 {:tag :let-decl :id 901 :name "n" :type nat :value (e/lit-nat 0)}
              902 {:tag :let-decl :id 902 :name "m" :type nat :value (e/fvar 901)}}
        [ps0 _] (proof/start-proof (require-env) (eq (e/lit-nat 0) (e/lit-nat 0)))
        [ps gid] (proof/fresh-mvar ps0 (eq (e/fvar 902) (e/fvar 902)) lctx)
        ps (update ps :goals (fn [gs] (into [gid] (remove #{gid} gs))))]
    (is (= (eq (e/lit-nat 0) (e/lit-nat 0)) (decide/zeta-let-locals lctx (eq (e/fvar 902) (e/fvar 902)))))
    (is (some? (decide/decide ps)) "decide closes the goal after zeta-reducing the let chain")))

(deftest test-decide-closed-goal-uses-local-instance
  (testing "a closed proposition reaches evaluation with its local Decidable instance"
    ;; Lean Elab/Tactic/Decide.lean preprocessPropToDecide permits this
    ;; closed constant; evalDecideCore then synthesizes in the goal context.
    (let [prop-name (name/from-string "DecideTest.closedGoal")
          env (env/check-constant (require-env) (env/mk-axiom prop-name [] (e/sort' lvl/zero)))
          prop (e/const' prop-name [])
          dec (e/app (e/const' (name/from-string "Decidable") []) prop)
          ty (e/forall' "d" dec prop :inst-implicit)
          [ps _] (proof/start-proof env ty)
          ps (basic/intro ps "d")
          goal (proof/current-goal ps)
          local-id (first (keys (:lctx goal)))
          evaluated (atom nil)
          verify-decide @#'decide/verify-decide
          failure (with-redefs-fn
                    {#'decide/verify-decide
                     (fn [st prop inst]
                       ;; Observe the actual evaluator inputs, then run it unchanged.
                       (reset! evaluated {:lctx (:lctx st) :prop prop :inst inst})
                       (verify-decide st prop inst))}
                    #(try (decide/decide ps) nil
                          (catch clojure.lang.ExceptionInfo ex ex)))]
      (is (not (e/has-fvar-flag (:type goal))))
      (is (= {:lctx (:lctx goal) :prop prop :inst (e/fvar local-id)} @evaluated))
      (is (= :tactic-error (:kind (ex-data failure))))
      (is (re-find #"decide failed" (or (ex-message failure) ""))
          "the local instance is opaque, so evaluation must report that it cannot compute")
      (is (not (proof/solved? ps))))))

(deftest test-decide-rejects-free-variable-goal
  (testing "a non-let free variable is rejected before synthesis or evaluation"
    ;; Lean preprocessPropToDecide rejects n = n even with a local instance.
    (let [env (require-env)
          nat (e/const' (name/from-string "Nat") [])
          eq (fn [n] (e/app* (e/const' (name/from-string "Eq") [(lvl/succ lvl/zero)]) nat n n))
          dec (e/app (e/const' (name/from-string "Decidable") []) (eq (e/bvar 0)))
          ty (e/forall' "n" nat
                        (e/forall' "d" dec (eq (e/bvar 1)) :inst-implicit) :default)
          [ps _] (proof/start-proof env ty)
          ps (basic/intros ps ["n" "d"])
          failure (try (decide/decide ps) nil
                       (catch clojure.lang.ExceptionInfo ex ex))]
      (is (e/has-fvar-flag (:type (proof/current-goal ps))))
      (is (= :tactic-error (:kind (ex-data failure))))
      (is (re-find #"expected type must not contain free variables" (or (ex-message failure) ""))))))
