(ns ansatz.tactic.smoke-test
  "REPL smoke test for the tactic layer with init-medium env."
  (:require [clojure.test :refer [deftest testing is]]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]
            [ansatz.tactic.proof :as proof]
            [ansatz.tactic.repl :as r]
            [ansatz.tactic.search :as search]
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

(deftest smoke-test-repl-workflow
  (testing "Full REPL workflow: prove, intro, rfl, qed"
    (let [env (require-env)
          nat (e/const' (name/from-string "Nat") [])
          u1 (lvl/succ lvl/zero)
          eq-aa (e/app* (e/const' (name/from-string "Eq") [u1]) nat (e/bvar 0) (e/bvar 0))
          goal (e/forall' "a" nat eq-aa :default)
          ps (r/prove env goal)
          ps (r/intro ps "a")
          ps (r/rfl ps)]
      (is (proof/solved? ps))
      (let [term (r/qed ps)]
        (is (some? term))
        (is (not (e/has-fvar-flag term)))))))

(deftest smoke-test-auto-solve
  (testing "Auto-solve for Prop identity"
    (let [env (require-env)
          prop (e/sort' lvl/zero)
          goal (e/forall' "a" prop
                          (e/forall' "h" (e/bvar 0) (e/bvar 1) :default) :default)
          ps (r/prove env goal)
          result (r/auto ps)]
      (is (some? result))
      (is (proof/solved? result))
      (is (pos? (count (:trace result)))))))

(deftest smoke-test-apply-with-unification
  (testing "apply Eq.symm with implicit arg unification + assumption"
    (let [env (require-env)
          nat (e/const' (name/from-string "Nat") [])
          u1 (lvl/succ lvl/zero)
          eq-name (name/from-string "Eq")
          eq-ab (e/app* (e/const' eq-name [u1]) nat (e/bvar 1) (e/bvar 0))
          eq-ba (e/app* (e/const' eq-name [u1]) nat (e/bvar 1) (e/bvar 2))
          goal-type (e/forall' "a" nat
                               (e/forall' "b" nat
                                          (e/forall' "h" eq-ab eq-ba :default) :default) :default)
          ps (r/prove env goal-type)
          ps (r/intros ps ["a" "b" "h"])
          eq-symm (e/const' (name/from-string "Eq.symm") [u1])
          ps (r/apply-tac ps eq-symm)
          ;; The remaining goal should be the eq proof
          ps (r/assumption ps)]
      (is (proof/solved? ps)))))

(deftest smoke-test-suggest
  (testing "suggest returns applicable tactics"
    (let [env (require-env)
          prop (e/sort' lvl/zero)
          goal (e/forall' "a" prop (e/bvar 0) :default)
          ps (r/prove env goal)
          tactics (search/enumerate-tactics ps)]
      (is (seq tactics))
      (is (some #(= :intro (:name %)) tactics)))))

(deftest smoke-test-beam-search
  (testing "beam search closes Prop identity"
    (let [env (require-env)
          prop (e/sort' lvl/zero)
          goal (e/forall' "a" prop
                          (e/forall' "h" (e/bvar 0) (e/bvar 1) :default) :default)
          ps (r/prove env goal)
          result (r/beam ps 3 20)]
      (is (some? result))
      (is (proof/solved? result)))))

(deftest smoke-test-trace-and-weight
  (testing "Trace and weight are tracked correctly"
    (let [env (require-env)
          prop (e/sort' lvl/zero)
          goal (e/forall' "a" prop
                          (e/forall' "h" (e/bvar 0) (e/bvar 1) :default) :default)
          ps (r/prove env goal)
          ps (r/intro ps "a")
          ps (r/intro ps "h")
          ps (r/assumption ps)
          summary (search/trace-summary ps)]
      (is (= 3 (:num-steps summary)))
      (is (:solved summary))
      (is (= 0 (:open-goals summary)))
      (is (= 1.0 (:weight summary))))))

;; ============================================================
;; Rewrite test
;; ============================================================

(deftest smoke-test-rewrite
  (testing "rewrite with equality hypothesis"
    ;; Goal: ∀ (a b : Nat), a = b → b = b
    ;; Strategy: intro a, intro b, intro h, rewrite h (replaces a with b), rfl
    (let [env (require-env)
          nat (e/const' (name/from-string "Nat") [])
          u1 (lvl/succ lvl/zero)
          eq-name (name/from-string "Eq")
          ;; In ∀ (a : Nat), ∀ (b : Nat), ∀ (h : a=b), b=b:
          ;; eq-ab is type of h: bvar 0=b, bvar 1=a → @Eq Nat a b
          eq-ab (e/app* (e/const' eq-name [u1]) nat (e/bvar 1) (e/bvar 0))
          ;; body: bvar 0=h, bvar 1=b, bvar 2=a → @Eq Nat b b
          eq-bb (e/app* (e/const' eq-name [u1]) nat (e/bvar 1) (e/bvar 1))
          goal-type (e/forall' "a" nat
                               (e/forall' "b" nat
                                          (e/forall' "h" eq-ab eq-bb :default)
                                          :default)
                               :default)
          [ps _] (proof/start-proof env goal-type)
          ps (r/intros ps ["a" "b" "h"])]
      ;; Get fvar for h
      (let [goal (proof/current-goal ps)
            h-fvar-id (some (fn [[id decl]]
                              (when (and (= :local (:tag decl))
                                         (= "h" (:name decl)))
                                id))
                            (:lctx goal))
            h-fvar (e/fvar h-fvar-id)]
        ;; Goal is @Eq Nat b b — this is already rfl-provable without rewrite
        ;; Let's verify rfl works directly
        (let [ps-rfl (r/rfl ps)]
          (is (proof/solved? ps-rfl))))))

  (testing "rewrite changes goal type"
    ;; Goal: ∀ (a b : Nat), a = b → a = a
    ;; After rewrite with h (a=b), goal becomes b = b (replacing first a with b? No — replacing a with b)
    ;; Actually rewrite replaces lhs with rhs, so with h : a = b, it replaces a→b in goal
    ;; Goal a = a becomes b = a (replacing leftmost a), then we can't rfl.
    ;; Better test: rewrite ← h to go from b = b to a = a... or just test that rewrite produces a subgoal.
    (let [env (require-env)
          nat (e/const' (name/from-string "Nat") [])
          u1 (lvl/succ lvl/zero)
          eq-name (name/from-string "Eq")
          ;; ∀ (a b : Nat), a = b → b = a
          eq-ab (e/app* (e/const' eq-name [u1]) nat (e/bvar 1) (e/bvar 0))
          eq-ba (e/app* (e/const' eq-name [u1]) nat (e/bvar 1) (e/bvar 2))
          goal-type (e/forall' "a" nat
                               (e/forall' "b" nat
                                          (e/forall' "h" eq-ab eq-ba :default)
                                          :default)
                               :default)
          [ps _] (proof/start-proof env goal-type)
          ps (r/intros ps ["a" "b" "h"])]
      (let [goal (proof/current-goal ps)
            h-fvar-id (some (fn [[id decl]]
                              (when (and (= :local (:tag decl))
                                         (= "h" (:name decl)))
                                id))
                            (:lctx goal))]
        ;; Rewrite with h (a=b) in goal (b=a) → replaces a with b → goal becomes (b=b)
        (let [ps (r/rewrite ps (e/fvar h-fvar-id))
              ;; After rewrite, the new goal should be rfl-provable
              ps (r/rfl ps)]
          (is (proof/solved? ps))
          ;; Verify extracted proof term with Java TypeChecker
          (let [term (extract/verify ps)]
            (is (some? term))
            (is (not (e/has-fvar-flag term)))))))))

;; ============================================================
;; Cases test
;; ============================================================

(deftest smoke-test-cases
  (testing "case analysis on Bool produces two subgoals"
    (let [env (require-env)
          bool-t (e/const' (name/from-string "Bool") [])
          u1 (lvl/succ lvl/zero)
          eq-name (name/from-string "Eq")
          ;; ∀ (b : Bool), @Eq Bool b b
          eq-bb (e/app* (e/const' eq-name [u1]) bool-t (e/bvar 0) (e/bvar 0))
          goal-type (e/forall' "b" bool-t eq-bb :default)
          [ps _] (proof/start-proof env goal-type)
          ps (basic/intro ps "b")]
      ;; Find fvar for b
      (let [goal (proof/current-goal ps)
            b-fvar-id (some (fn [[id decl]]
                              (when (and (= :local (:tag decl))
                                         (= "b" (:name decl)))
                                id))
                            (:lctx goal))]
        ;; Case split on b
        (let [ps (basic/cases ps b-fvar-id)]
          ;; Should have 2 goals (true and false branches)
          (is (= 2 (count (:goals ps))))
          ;; Close both goals with rfl
          (let [ps (basic/rfl ps)
                ps (basic/rfl ps)]
            (is (proof/solved? ps))
            (let [term (extract/verify ps)]
              (is (some? term))
              (is (not (e/has-fvar-flag term))))))))))
