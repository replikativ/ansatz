(ns ansatz.tactic.tactic-test
  "Tests for the tactic layer: proof states, tactics, extraction, verification."
  (:require [clojure.test :refer [deftest testing is use-fixtures]]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.reduce :as red]
            [ansatz.kernel.tc :as tc]
            [ansatz.meta :as meta]
            [ansatz.tactic.proof :as proof]
            [ansatz.tactic.basic :as basic]
            [ansatz.tactic.extract :as extract]
            [ansatz.tactic.search :as search]
            [ansatz.export.parser :as parser]
            [ansatz.export.replay :as replay])
  (:import [ansatz.kernel Env TypeChecker ConstantInfo Name]))

;; ============================================================
;; Test environment setup
;; ============================================================

(def prop (e/sort' lvl/zero))
(def type0 (e/sort' (lvl/succ lvl/zero)))

(defn- minimal-env
  "Create an environment with just Prop available (empty env suffices)."
  []
  (env/empty-env))

(def ^:private init-medium-env
  "Lazily loaded init-medium environment."
  (delay
    (let [f "test-data/init-medium.ndjson"]
      (when (.exists (java.io.File. f))
        (let [st (parser/parse-ndjson-file f)
              result (replay/replay (:decls st))]
          (:env result))))))

(defn- require-init-medium []
  (let [env @init-medium-env]
    (when-not env
      (throw (ex-info "init-medium.ndjson not found" {})))
    env))

;; ============================================================
;; Test 1: ∀ (a : Prop), a → a — intro + intro + assumption
;; ============================================================

(deftest test-prop-identity
  (testing "∀ (a : Prop), a → a via intro + intro + assumption"
    (let [env (minimal-env)
          ;; ∀ (a : Prop), a → a
          ;; = ∀ (a : Prop), ∀ (_ : a), a
          goal-type (e/forall' "a" prop (e/forall' "h" (e/bvar 0) (e/bvar 1) :default) :default)
          [ps _] (proof/start-proof env goal-type)
          ps (basic/intro ps "a")
          ps (basic/intro ps "h")
          ps (basic/assumption ps)]
      (is (proof/solved? ps))
      (let [term (extract/extract ps)]
        (is (not (e/has-fvar-flag term)))
        ;; Should be λ (a : Prop) (h : a). h
        (is (e/lam? term))
        ;; Verify with Clojure TC
        (let [st (tc/mk-tc-state env)
              inferred (tc/infer-type st term)]
          (is (tc/is-def-eq st inferred goal-type)))))))

;; ============================================================
;; Test 2: ∀ (a : Nat), a = a — intro + rfl
;; ============================================================

(deftest test-nat-refl
  (testing "∀ (a : Nat), a = a via intro + rfl"
    (let [env (require-init-medium)
          nat (e/const' (name/from-string "Nat") [])
          u1 (lvl/succ lvl/zero)
          eq-name (name/from-string "Eq")
          ;; @Eq Nat (bvar 0) (bvar 0)
          eq-aa (e/app* (e/const' eq-name [u1]) nat (e/bvar 0) (e/bvar 0))
          ;; ∀ (a : Nat), a = a
          goal-type (e/forall' "a" nat eq-aa :default)
          [ps _] (proof/start-proof env goal-type)
          ps (basic/intro ps "a")
          ps (basic/rfl ps)]
      (is (proof/solved? ps))
      (let [term (extract/verify ps)]
        (is (not (e/has-fvar-flag term)))))))

;; ============================================================
;; Test 3: ∀ (a b : Nat), a = b → b = a — intro + apply Eq.symm
;; ============================================================

(deftest test-eq-symm
  (testing "∀ (a b : Nat), a = b → b = a via intros + exact with Eq.symm applied"
    (let [env (require-init-medium)
          nat (e/const' (name/from-string "Nat") [])
          u1 (lvl/succ lvl/zero)
          eq-name (name/from-string "Eq")
          ;; ∀ (a b : Nat), a = b → b = a
          ;; In ∀ (a : Nat), ∀ (b : Nat), ∀ (h : a=b), b=a:
          ;; eq-ab is the type of h, where bvar 0=b, bvar 1=a
          eq-ab (e/app* (e/const' eq-name [u1]) nat (e/bvar 1) (e/bvar 0))
          ;; eq-ba is the body, where bvar 0=h, bvar 1=b, bvar 2=a
          eq-ba (e/app* (e/const' eq-name [u1]) nat (e/bvar 1) (e/bvar 2))
          goal-type (e/forall' "a" nat
                               (e/forall' "b" nat
                                          (e/forall' "h" eq-ab eq-ba :default)
                                          :default)
                               :default)
          [ps _] (proof/start-proof env goal-type)
          ps (basic/intros ps ["a" "b" "h"])]
      ;; Build the proof term manually: @Eq.symm Nat a b h
      ;; After intros, we have fvars for a (id 2), b (id 4), h (id 6)
      ;; Use exact with a fully applied Eq.symm
      (let [goal (proof/current-goal ps)
            ;; Find fvars from the lctx
            fvars (->> (:lctx goal)
                       (filter (fn [[_ d]] (= :local (:tag d))))
                       (sort-by first)
                       (mapv (fn [[id _]] (e/fvar id))))
            [a-fv b-fv h-fv] fvars
            eq-symm-term (e/app* (e/const' (name/from-string "Eq.symm") [u1])
                                 nat a-fv b-fv h-fv)
            ps (basic/exact ps eq-symm-term)]
        (is (proof/solved? ps))
        (let [term (extract/verify ps)]
          (is (not (e/has-fvar-flag term))))))))

;; ============================================================
;; Test 4: ∀ (a : Prop), a → a — intros shorthand
;; ============================================================

(deftest test-intros
  (testing "intros introduces all forall binders at once"
    (let [env (minimal-env)
          goal-type (e/forall' "a" prop (e/forall' "h" (e/bvar 0) (e/bvar 1) :default) :default)
          [ps _] (proof/start-proof env goal-type)
          ps (basic/intros ps)]
      ;; After intros, goal should no longer be a forall
      (let [goal (proof/current-goal ps)]
        (is (some? goal))
        ;; The goal type should be a fvar (the 'a' we introduced)
        (is (e/fvar? (:type goal)))))))

;; ============================================================
;; Test 5: Fork test — immutability
;; ============================================================

(deftest test-fork
  (testing "Forking proof states preserves independence"
    (let [env (minimal-env)
          goal-type (e/forall' "a" prop (e/forall' "h" (e/bvar 0) (e/bvar 1) :default) :default)
          [ps _] (proof/start-proof env goal-type)
          ;; Fork: both branches start from the same state
          branch-a (basic/intro ps "x")
          branch-b (basic/intro ps "y")]
      ;; Both branches should have one goal remaining
      (is (= 1 (count (:goals branch-a))))
      (is (= 1 (count (:goals branch-b))))
      ;; Original ps should be unchanged (1 goal, the root)
      (is (= 1 (count (:goals ps))))
      ;; Modifying branch-a further doesn't affect branch-b
      (let [branch-a2 (basic/intro branch-a "ha")
            _ (basic/assumption branch-a2)]
        ;; branch-b still has 1 goal
        (is (= 1 (count (:goals branch-b))))
        ;; branch-a2 has 1 goal (after second intro, before assumption solved it)
        ;; actually assumption returns a solved state, let's verify branch-b is unaffected
        (is (= 1 (count (:goals (basic/intro branch-b "hb")))))))))

;; ============================================================
;; Test 6: Extraction roundtrip — extract + verify with Java TC
;; ============================================================

(deftest test-extraction-roundtrip
  (testing "Extracted proof term is verified by Java TypeChecker"
    (let [env (minimal-env)
          goal-type (e/forall' "a" prop (e/forall' "h" (e/bvar 0) (e/bvar 1) :default) :default)
          [ps _] (proof/start-proof env goal-type)
          ps (-> ps
                 (basic/intro "a")
                 (basic/intro "h")
                 basic/assumption)
          term (extract/extract ps)]
      ;; Verify with Java TypeChecker
      (let [tc (TypeChecker. env)
            inferred (.inferType tc term)]
        (is (.isDefEq tc inferred goal-type))))))

;; ============================================================
;; Test 7: exact tactic
;; ============================================================

(deftest test-exact
  (testing "exact closes goal with a specific term"
    (let [env (minimal-env)
          ;; Goal: Prop → Prop
          goal-type (e/arrow prop prop)
          [ps _] (proof/start-proof env goal-type)
          ;; Provide λ (x : Prop). x as exact term
          id-fn (e/lam "x" prop (e/bvar 0) :default)
          ps (basic/exact ps id-fn)]
      (is (proof/solved? ps))
      (let [term (extract/extract ps)]
        (is (= id-fn term))))))

;; ============================================================
;; Test 8: Error cases
;; ============================================================

(deftest test-error-cases
  (testing "intro on non-forall goal throws"
    (let [env (minimal-env)
          [ps _] (proof/start-proof env prop)]
      (is (thrown? Exception (basic/intro ps)))))

  (testing "rfl on non-Eq goal throws"
    (let [env (minimal-env)
          [ps _] (proof/start-proof env prop)]
      (is (thrown? Exception (basic/rfl ps)))))

  (testing "assumption with no matching hyp throws"
    (let [env (minimal-env)
          [ps _] (proof/start-proof env prop)]
      (is (thrown? Exception (basic/assumption ps)))))

  (testing "extract on unsolved proof throws"
    (let [env (minimal-env)
          [ps _] (proof/start-proof env prop)]
      (is (thrown? Exception (extract/extract ps))))))

;; ============================================================
;; Test 9: proof state API
;; ============================================================

(deftest test-proof-state-api
  (testing "start-proof creates one goal"
    (let [env (minimal-env)
          [ps root-id] (proof/start-proof env prop)]
      (is (= 1 (count (:goals ps))))
      (is (= root-id (:root-mvar ps)))
      (is (= :syntheticOpaque (:kind (proof/mvar-decl ps root-id))))
      (is (not (proof/solved? ps)))))

  (testing "goals returns goal info"
    (let [env (minimal-env)
          [ps _] (proof/start-proof env prop)
          gs (proof/goals ps)]
      (is (= 1 (count gs)))
      (is (= prop (:type (first gs)))))))

(deftest test-tactic-goals-are-synthetic-opaque
  (testing "ordinary defeq cannot close the current tactic goal"
    (let [env (minimal-env)
          goal-type (e/forall' "p" prop
                               (e/forall' "h" (e/bvar 0) (e/bvar 1) :default)
                               :default)
          [ps _] (proof/start-proof env goal-type)
          ps (-> ps
                 (basic/intro "p")
                 (basic/intro "h"))
          goal (proof/current-goal ps)
          h-id (some (fn [[id d]] (when (= "h" (:name d)) id)) (:lctx goal))
          st (tc/mk-tc-state-with-locals env (:lctx goal))]
      (is (= :syntheticOpaque (:kind (proof/mvar-decl ps (:id goal)))))
      (is (nil? (meta/is-def-eq (:meta-mctx ps) st
                                (e/mvar (:id goal))
                                (e/fvar h-id)))))))

(deftest test-auxiliary-proof-mvars-can-be-natural
  (testing "the proof allocator can still create Lean-style assignable auxiliary mvars"
    (let [env (minimal-env)
          [ps _] (proof/start-proof env prop)
          [ps aux-id] (proof/fresh-mvar ps prop (red/empty-lctx) {:kind :natural})]
      (is (= :natural (:kind (proof/mvar-decl ps aux-id)))))))

;; ============================================================
;; Test 10: refine with surface holes
;; ============================================================

(deftest test-refine-surface-term
  (testing "refine closes a goal with a surface term in the local context"
    (let [env (minimal-env)
          goal-type (e/forall' "p" prop
                               (e/forall' "h" (e/bvar 0) (e/bvar 1) :default)
                               :default)
          [ps _] (proof/start-proof env goal-type)
          ps (-> ps
                 (basic/intro "p")
                 (basic/intro "h")
                 (basic/refine 'h))]
      (is (proof/solved? ps))
      (is (not (e/has-fvar-flag (extract/verify ps)))))))

(deftest test-refine-named-hole-becomes-goal
  (testing "named holes are synthetic-opaque goals under refine"
    (let [env (minimal-env)
          goal-type (e/forall' "p" prop
                               (e/forall' "h" (e/bvar 0) (e/bvar 1) :default)
                               :default)
          [ps _] (proof/start-proof env goal-type)
          ps (-> ps
                 (basic/intro "p")
                 (basic/intro "h")
                 (basic/refine '?goal))
          goal (proof/current-goal ps)]
      (is (= 1 (count (:goals ps))))
      (is (= :syntheticOpaque (:kind (proof/mvar-decl ps (:id goal)))))
      (let [ps (basic/assumption ps)]
        (is (proof/solved? ps))
        (is (not (e/has-fvar-flag (extract/verify ps))))))))

(deftest test-refine-rejects-natural-holes
  (testing "refine rejects unsolved natural holes by default"
    (let [env (minimal-env)
          goal-type (e/forall' "p" prop (e/bvar 0) :default)
          [ps _] (proof/start-proof env goal-type)
          ps (basic/intro ps "p")
          expected-type-str (e/->string (:type (proof/current-goal ps)))]
      (try
        (basic/refine ps '_)
        (is false "expected refine to reject natural holes")
        (catch clojure.lang.ExceptionInfo ex
          (let [data (ex-data ex)
                diagnostics (:hole-diagnostics data)
                first-hole (first diagnostics)]
            (is (re-find #"natural holes" (.getMessage ex)))
            (is (re-find #"use refine'" (.getMessage ex)))
            (is (= 1 (:hole-count data)))
            (is (= 1 (count diagnostics)))
            (is (= :natural (:kind first-hole)))
            (is (= "?m." (subs (:display-name first-hole) 0 3)))
            (is (= expected-type-str (:type-str first-hole)))))))))

(deftest test-refine-prime-allows-natural-holes-under-binders
  (testing "refine-prime turns lambda-body holes into subgoals with delayed abstraction"
    (let [env (minimal-env)
          goal-type (e/forall' "p" prop
                               (e/forall' "h" (e/bvar 0) (e/bvar 1) :default)
                               :default)
          [ps _] (proof/start-proof env goal-type)
          ps (basic/intro ps "p")
          ps (basic/refine-prime ps '(lam [h p] _))]
      (is (= 1 (count (:goals ps))))
      (is (= :syntheticOpaque (:kind (proof/mvar-decl ps (first (:goals ps))))))
      (let [ps (basic/assumption ps)]
        (is (proof/solved? ps))
        (is (not (e/has-fvar-flag (extract/verify ps))))))))

(deftest test-refine-prime-stores-instantiated-assignment
  (testing "refine-prime assigns the zonked elaborated value to the main goal"
    (let [env (require-init-medium)
          goal-type (e/forall' "p" prop
                               (e/forall' "h" (e/bvar 0) (e/bvar 1) :default)
                               :default)
          [ps _] (proof/start-proof env goal-type)
          ps (-> ps
                 (basic/intro "p")
                 (basic/intro "h"))
          goal-id (:id (proof/current-goal ps))
          lctx (:lctx (proof/current-goal ps))
          p-id (some (fn [[id d]] (when (= "p" (:name d)) id)) lctx)
          h-id (some (fn [[id d]] (when (= "h" (:name d)) id)) lctx)
          ps (basic/refine-prime ps (list (symbol "@id") '_ 'h))
          term (:term (proof/mvar-assignment ps goal-id))
          [head args] (e/get-app-fn-args term)]
      (is (proof/solved? ps))
      (is (e/const? head))
      (is (= (name/from-string "id") (e/const-name head)))
      (is (= [(e/fvar p-id) (e/fvar h-id)] args))
      (is (empty? (meta/collect-expr-mvars term)))
      (is (not (e/has-fvar-flag (extract/verify ps)))))))

(deftest test-refine-tags-single-unnamed-hole
  (testing "a single unnamed refine-prime hole inherits the parent goal tag"
    (let [env (minimal-env)
          parent-tag (name/from-string "main")
          [ps root] (proof/start-proof env prop)
          ps (proof/set-mvar-user-name ps root parent-tag)
          ps (basic/refine-prime ps '_)
          goal (proof/current-goal ps)]
      (is (= 1 (count (:goals ps))))
      (is (= parent-tag (:user-name goal)))
      (is (= parent-tag (:user-name (proof/mvar-decl ps (:id goal)))))
      (is (re-find #"Goal 1 \(main\)" (proof/format-goals ps))))))

(deftest test-refine-main-goal-named-hole-keeps-goal
  (testing "refining with the main goal mvar preserves the current goal"
    (let [env (minimal-env)
          main-tag (name/from-string "main")
          [ps root] (proof/start-proof env prop)
          ps (proof/set-mvar-user-name ps root main-tag)
          ps (basic/refine ps '?main)]
      (is (= [root] (:goals ps)))
      (is (proof/mvar-open? ps root))
      (is (= main-tag (:user-name (proof/current-goal ps)))))))

(deftest test-refine-rejects-main-goal-dependency
  (testing "refine rejects values that contain the main goal mvar"
    (let [env (minimal-env)
          main-tag (name/from-string "main")
          ;; forall (p : Prop), (p -> p) -> p
          p-to-p (e/forall' "_" (e/bvar 0) (e/bvar 1) :default)
          goal-type (e/forall' "p" prop
                               (e/forall' "f" p-to-p (e/bvar 1) :default)
                               :default)
          [ps _] (proof/start-proof env goal-type)
          ps (-> ps
                 (basic/intro "p")
                 (basic/intro "f"))
          goal-id (:id (proof/current-goal ps))
          ps (proof/set-mvar-user-name ps goal-id main-tag)]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"depends on the main goal"
                            (basic/refine ps '(f ?main)))))))

(deftest test-refine-tags-multiple-unnamed-holes
  (testing "multiple unnamed refine-prime holes receive stable suffix tags"
    (let [env (minimal-env)
          ;; forall (p : Prop), (p -> p -> p) -> p
          p-to-p-to-p (e/forall' "_" (e/bvar 0)
                                 (e/forall' "_" (e/bvar 1) (e/bvar 2) :default)
                                 :default)
          goal-type (e/forall' "p" prop
                               (e/forall' "f" p-to-p-to-p (e/bvar 1) :default)
                               :default)
          [ps _] (proof/start-proof env goal-type)
          ps (-> ps
                 (basic/intro "p")
                 (basic/intro "f")
                 (basic/refine-prime '(f _ _)))
          goals (vec (proof/goals ps))
          tags (mapv #(some-> (:user-name %) name/->string) goals)
          kinds (mapv #(->> (:id %) (proof/mvar-decl ps) :kind) goals)]
      (is (= 2 (count (:goals ps))))
      (is (= ["refine'_1" "refine'_2"] tags))
      (is (= [:syntheticOpaque :syntheticOpaque] kinds)))))

;; ============================================================
;; Test 11: apply with unification (implicit args)
;; ============================================================

(deftest test-apply-unification
  (testing "apply Eq.symm resolves implicit args via unification"
    (let [env (require-init-medium)
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
          ps (basic/intros ps ["a" "b" "h"])
          ;; Now apply Eq.symm — should unify implicit args automatically
          eq-symm (e/const' (name/from-string "Eq.symm") [u1])
          ps (basic/apply-tac ps eq-symm)]
      ;; After apply, some implicit args should be solved, leaving the eq proof as subgoal
      ;; Try assumption for remaining goals
      (let [ps (loop [ps ps attempts 0]
                 (if (or (proof/solved? ps) (> attempts 10))
                   ps
                   (recur (try (basic/assumption ps)
                               (catch Exception _ ps))
                          (inc attempts))))]
        (is (proof/solved? ps))))))

;; ============================================================
;; Test 11: trace recording
;; ============================================================

(deftest test-trace
  (testing "Tactic trace is recorded"
    (let [env (minimal-env)
          goal-type (e/forall' "a" prop (e/forall' "h" (e/bvar 0) (e/bvar 1) :default) :default)
          [ps _] (proof/start-proof env goal-type)
          ps (-> ps (basic/intro "a") (basic/intro "h") basic/assumption)]
      (is (= 3 (count (:trace ps))))
      (is (= [:intro :intro :assumption] (mapv :tactic (:trace ps)))))))

;; ============================================================
;; Test 12: search — enumerate-tactics
;; ============================================================

(deftest test-enumerate-tactics
  (testing "enumerate-tactics finds applicable tactics"
    (let [env (minimal-env)
          goal-type (e/forall' "a" prop (e/forall' "h" (e/bvar 0) (e/bvar 1) :default) :default)
          [ps _] (proof/start-proof env goal-type)
          tactics (search/enumerate-tactics ps)]
      ;; At least intro should be applicable
      (is (some #(= :intro (:name %)) tactics)))))

;; ============================================================
;; Test 13: search — auto-solve for simple proofs
;; ============================================================

(deftest test-auto-solve
  (testing "auto-solve closes ∀ (a : Prop), a → a"
    (let [env (minimal-env)
          goal-type (e/forall' "a" prop (e/forall' "h" (e/bvar 0) (e/bvar 1) :default) :default)
          [ps _] (proof/start-proof env goal-type)
          result (search/auto-solve ps 10)]
      (is (some? result))
      (is (proof/solved? result)))))

;; ============================================================
;; Test 14: search — beam-search
;; ============================================================

(deftest test-beam-search
  (testing "beam-search closes ∀ (a : Prop), a → a"
    (let [env (minimal-env)
          goal-type (e/forall' "a" prop (e/forall' "h" (e/bvar 0) (e/bvar 1) :default) :default)
          [ps _] (proof/start-proof env goal-type)
          result (search/beam-search ps 3 20)]
      (is (some? result))
      (is (proof/solved? result)))))

;; ============================================================
;; Test 15: weight and scoring
;; ============================================================

(deftest test-weight
  (testing "proof state weight tracking"
    (let [env (minimal-env)
          [ps _] (proof/start-proof env prop)]
      (is (= 1.0 (:weight ps)))
      (let [ps' (proof/adjust-weight ps 0.5)]
        (is (= 0.5 (:weight ps')))
        (let [ps'' (proof/adjust-weight ps' 0.3)]
          (is (< (Math/abs (- 0.15 (:weight ps''))) 1e-10)))))))
