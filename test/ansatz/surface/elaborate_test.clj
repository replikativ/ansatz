(ns ansatz.surface.elaborate-test
  "Tests for the elaboration function."
  (:require [clojure.test :refer [deftest testing is]]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.reduce :as red]
            [ansatz.kernel.tc :as tc]
            [ansatz.meta :as meta]
            [ansatz.surface.elaborate :as elab]
            [ansatz.export.parser :as parser]
            [ansatz.export.replay :as replay]))

;; ============================================================
;; Environment helpers
;; ============================================================

(def ^:private init-medium-env
  (delay
    (let [f "test-data/init-medium.ndjson"]
      (when (.exists (java.io.File. f))
        (let [st (parser/parse-ndjson-file f)
              result (replay/replay (:decls st))]
          (:env result))))))

(defn- require-init-medium []
  (or @init-medium-env
      (throw (ex-info "init-medium.ndjson not found" {}))))

;; ============================================================
;; Basic elaboration (no implicits needed)
;; ============================================================

(deftest test-elab-sort-shortcuts
  (testing "Prop and Type elaborate correctly"
    (let [env (env/empty-env)]
      (is (e/sort? (elab/elaborate env 'Prop)))
      (is (e/sort? (elab/elaborate env 'Type))))))

(deftest test-elab-literal
  (testing "Literals elaborate correctly"
    (let [env (env/empty-env)]
      (is (e/lit-nat? (elab/elaborate env 42)))
      (is (e/lit-str? (elab/elaborate env "hello"))))))

(deftest test-elab-constant
  (testing "Constant lookup with explicit levels"
    (let [env (require-init-medium)
          result (elab/elaborate env 'Nat)]
      (is (e/const? result))
      (is (= (name/from-string "Nat") (e/const-name result))))))

(deftest test-elab-forall-simple
  (testing "forall with no implicits"
    (let [env (env/empty-env)
          ;; ∀ (a : Prop), a → a -- no env constants needed
          result (elab/elaborate env '(forall [a Prop] (arrow a a)))]
      (is (e/forall? result))
      ;; Verify it type-checks
      (let [st (tc/mk-tc-state env)]
        (is (e/sort? (tc/infer-type st result)))))))

(deftest test-elab-lam-simple
  (testing "Lambda with Prop"
    (let [env (env/empty-env)
          result (elab/elaborate env '(lam [a Prop, h a] h))]
      ;; Should be λ (a : Prop) (h : a) => h
      (is (e/lam? result))
      (let [st (tc/mk-tc-state env)
            ty (tc/infer-type st result)]
        (is (e/forall? ty))))))

;; ============================================================
;; Implicit argument insertion
;; ============================================================

(deftest test-elab-eq-implicits
  (testing "Eq inserts implicit type argument and universe level"
    (let [env (require-init-medium)
          ;; Eq a a — Eq has one implicit arg {α : Sort u} plus universe level
          result (elab/elaborate env '(forall [a Nat] (Eq a a)))]
      ;; Should elaborate to: forall (a : Nat), @Eq.{1} Nat a a
      (is (e/forall? result))
      (let [body (e/forall-body result)
            ;; body should be @Eq.{1} Nat (bvar 0) (bvar 0) after abstraction
            [head args] (e/get-app-fn-args body)]
        (is (e/const? head))
        (is (= (name/from-string "Eq") (e/const-name head)))
        ;; 3 args: type, lhs, rhs
        (is (= 3 (count args)))
        ;; First arg should be Nat (the implicit type arg)
        (is (e/const? (first args)))
        (is (= (name/from-string "Nat") (e/const-name (first args))))))))

(deftest test-elab-eq-type-checks
  (testing "Elaborated Eq term type-checks"
    (let [env (require-init-medium)
          result (elab/elaborate env '(forall [a Nat] (Eq a a)))
          st (tc/mk-tc-state env)
          ty (tc/infer-type st result)]
      (is (e/sort? ty)))))

(deftest test-elab-eq-refl-implicits
  (testing "Eq.refl inserts implicit type and value arguments"
    (let [env (require-init-medium)
          ;; λ (a : Nat) => Eq.refl a
          ;; Eq.refl has type: {α : Sort u} → (a : α) → @Eq α a a
          ;; So Eq.refl a should elaborate to @Eq.refl.{1} Nat a
          result (elab/elaborate env '(lam [a Nat] (Eq.refl a)))
          st (tc/mk-tc-state env)
          ty (tc/infer-type st result)]
      ;; Type should be: ∀ (a : Nat), @Eq Nat a a
      (is (e/forall? ty)))))

(deftest test-elab-nat-succ
  (testing "Nat.succ application"
    (let [env (require-init-medium)
          result (elab/elaborate env '(Nat.succ 0))
          st (tc/mk-tc-state env)
          ty (tc/infer-type st result)]
      ;; Type should be Nat
      (is (e/const? ty))
      (is (= (name/from-string "Nat") (e/const-name ty))))))

;; ============================================================
;; Explicit levels still work
;; ============================================================

(deftest test-elab-explicit-levels
  (testing "Explicit levels override inference"
    (let [env (require-init-medium)
          ;; Use symbol with .{} for explicit levels — must construct manually
          ;; since Clojure reader chokes on {1} in symbols.
          ;; Eq.{1} still auto-inserts the implicit Nat arg, so just provide a a
          result (elab/elaborate env (list 'forall ['a 'Nat]
                                           (list (symbol "Eq.{1}") 'a 'a)))]
      (is (e/forall? result))
      (let [st (tc/mk-tc-state env)]
        (is (e/sort? (tc/infer-type st result)))))))

(deftest test-elab-at-explicit
  (testing "@-prefixed constants suppress implicit insertion"
    (let [env (require-init-medium)
          ;; @Eq.{1} Nat a a — fully explicit, no implicit insertion
          result (elab/elaborate env (list 'forall ['a 'Nat]
                                           (list (symbol "@Eq.{1}") 'Nat 'a 'a)))]
      (is (e/forall? result))
      (let [st (tc/mk-tc-state env)]
        (is (e/sort? (tc/infer-type st result)))))))

;; ============================================================
;; Error cases
;; ============================================================

(deftest test-elab-unknown-constant
  (testing "Unknown constant throws"
    (let [env (env/empty-env)]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Unknown constant"
                            (elab/elaborate env 'NonexistentThing))))))

(deftest test-elab-type-mismatch
  (testing "Type mismatch with expected type"
    (let [env (require-init-medium)
          nat (e/const' (name/from-string "Nat") [])]
      ;; Prop is Sort 0, not Nat
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"mismatch|error"
                            (elab/elaborate env 'Prop nat))))))

;; ============================================================
;; Collecting holes
;; ============================================================

(deftest test-elab-collecting-top-hole
  (testing "collecting elaboration returns real mvars instead of failing"
    (let [env (env/empty-env)
          expected (e/sort' lvl/zero)
          {:keys [expr holes meta-mctx level-holes]} (elab/elaborate-collecting env '_ expected)]
      (is (e/mvar? expr))
      (is (= 1 (count holes)))
      (is (= expr (:expr (first holes))))
      (is (= expected (:type (first holes))))
      (is (= :natural (:kind (first holes))))
      (is (nil? (:user-name (first holes))))
      (is (map? meta-mctx))
      ;; The hole's type was determined by expected, so the synthetic type
      ;; and universe mvars should have been solved away.
      (is (empty? level-holes)))))

(deftest test-elab-collecting-named-hole
  (testing "named holes preserve user-name metadata in the metacontext"
    (let [env (env/empty-env)
          expected (e/sort' lvl/zero)
          {:keys [holes meta-mctx]} (elab/elaborate-collecting env '?goal expected)
          hole (first holes)
          user-name (:user-name hole)]
      (is (= 1 (count holes)))
      (is (= "goal" (name/->string user-name)))
      (is (= :syntheticOpaque (:kind hole)))
      (is (= (:id hole) (get-in meta-mctx [:user-names user-name]))))))

(deftest test-elab-collecting-reuses-existing-named-hole
  (testing "named holes reuse an existing user-name entry in the metacontext"
    (let [env (env/empty-env)
          expected (e/sort' lvl/zero)
          hole-name (name/from-string "goal")
          initial-mctx (meta/add-expr-mvar-decl meta/empty-context 7 expected
                                                (red/empty-lctx)
                                                {:kind :syntheticOpaque
                                                 :user-name hole-name})
          {:keys [expr holes meta-mctx]} (elab/elaborate-collecting env '?goal expected
                                                                    {:initial-meta-mctx initial-mctx})]
      (is (= (e/mvar 7) expr))
      (is (empty? holes))
      (is (= 7 (get-in meta-mctx [:user-names hole-name]))))))

(deftest test-elab-collecting-hole-as-synthetic-opaque
  (testing "collecting elaboration can mirror Lean refine' holesAsSyntheticOpaque mode"
    (let [env (env/empty-env)
          expected (e/sort' lvl/zero)
          {:keys [holes]} (elab/elaborate-collecting env '_ expected
                                                    {:holes-as-synthetic-opaque? true})]
      (is (= 1 (count holes)))
      (is (= :syntheticOpaque (:kind (first holes))))
      (is (nil? (:user-name (first holes)))))))

(deftest test-elab-collecting-refine-prime-assigns-synthetic-opaque
  (testing "refine' mode lets later arguments solve synthetic-opaque placeholders"
    (let [env (require-init-medium)
          prop (e/sort' lvl/zero)
          lctx (red/lctx-add-local (red/empty-lctx) 10 "h" prop)
          {:keys [expr holes level-holes meta-mctx]}
          (elab/elaborate-in-context-collecting env lctx (list (symbol "@id") '_ 'h) prop
                                                {:holes-as-synthetic-opaque? true})
          [head args] (e/get-app-fn-args expr)]
      (is (e/const? head))
      (is (= (name/from-string "id") (e/const-name head)))
      (is (= [prop (e/fvar 10)] args))
      (is (empty? holes))
      (is (empty? level-holes))
      (is (not (:assign-synthetic-opaque? meta-mctx))))))

(deftest test-elab-strict-top-hole-fails
  (testing "strict elaboration still rejects unsolved holes"
    (let [env (env/empty-env)]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Unsolved metavariables"
                            (elab/elaborate env '_ (e/sort' lvl/zero)))))))

(deftest test-elab-collecting-context-hole
  (testing "contextual collecting keeps local fvars and records hole type"
    (let [env (env/empty-env)
          prop (e/sort' lvl/zero)
          lctx (red/lctx-add-local (red/empty-lctx) 7 "p" prop)
          {:keys [expr holes]} (elab/elaborate-in-context-collecting env lctx '_ (e/fvar 7))]
      (is (e/mvar? expr))
      (is (= 1 (count holes)))
      (is (= (e/fvar 7) (:type (first holes)))))))

(deftest test-elab-solver-mirrors-through-checked-metacontext-assignment
  (testing "expression mvar mirror assignment rejects cycles before mutating legacy state"
    (let [st (#'elab/mk-elab-state (env/empty-env))
          hole (#'elab/fresh-mvar! st (e/sort' lvl/zero))
          id (e/mvar-id hole)]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"cyclic"
                            (#'elab/solve-mvar! st id hole)))
      (is (nil? (get-in @(:mctx st) [id :solution])))
      (is (nil? (get-in @(:meta-mctx st) [:expr-assignment id])))))

  (testing "level mvar mirror assignment rejects cycles before mutating legacy state"
    (let [st (#'elab/mk-elab-state (env/empty-env))
          u (#'elab/fresh-level-mvar! st)
          id (lvl/mvar-id u)]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"cyclic"
                            (#'elab/solve-level-mvar! st id (lvl/succ u))))
      (is (nil? (get-in @(:level-mctx st) [id :solution])))
      (is (nil? (get-in @(:meta-mctx st) [:level-assignment id]))))))

(deftest test-elab-level-unification-uses-metacontext
  (testing "surface level unification solves in :meta-mctx and syncs legacy state"
    (let [st (#'elab/mk-elab-state (env/empty-env))
          u (#'elab/fresh-level-mvar! st)
          id (lvl/mvar-id u)]
      (is (#'elab/unify-levels! st (lvl/succ u) (lvl/succ lvl/zero)))
      (is (= lvl/zero (get-in @(:level-mctx st) [id :solution])))
      (is (= lvl/zero (meta/level-assignment @(:meta-mctx st) id))))))

(deftest test-elab-expression-unification-uses-metacontext
  (testing "surface expression unification solves in :meta-mctx and syncs legacy state"
    (let [prop (e/sort' lvl/zero)
          st (-> (#'elab/mk-elab-state (env/empty-env))
                 (update :tc update :lctx red/lctx-add-local 42 "h" prop))
          hole (#'elab/fresh-mvar! st prop)
          id (e/mvar-id hole)]
      (is (#'elab/unify! st hole (e/fvar 42)))
      (is (= (e/fvar 42) (get-in @(:mctx st) [id :solution])))
      (is (= (e/fvar 42) (meta/expr-assignment @(:meta-mctx st) id))))))

(deftest test-elab-infer-with-mvars-uses-mirrored-metacontext
  (testing "dependent surface holes are typed through real mvars in :meta-mctx"
    (let [st (#'elab/mk-elab-state (env/empty-env))
          alpha (#'elab/fresh-mvar! st (e/sort' lvl/zero))
          term (#'elab/fresh-mvar! st alpha)
          alpha-id (e/mvar-id alpha)
          term-id (e/mvar-id term)
          term-decl (meta/expr-decl @(:meta-mctx st) term-id)]
      (is (= (e/mvar alpha-id) (:type term-decl)))
      (is (not (contains? (get @(:mctx st) term-id) :type)))
      (is (= alpha (#'elab/infer-with-mvars st term))))))

(deftest test-elab-unsolved-scans-read-metacontext
  (testing "expression holes are reported from :meta-mctx even without compatibility entries"
    (let [st (#'elab/mk-elab-state (env/empty-env))
          hole (#'elab/fresh-mvar! st (e/sort' lvl/zero))
          id (e/mvar-id hole)
          _ (reset! (:mctx st) {})
          result (#'elab/collecting-finalize st hole)]
      (is (= [id] (mapv :id (:holes result))))))

  (testing "level holes are reported from :meta-mctx even without compatibility entries"
    (let [st (#'elab/mk-elab-state (env/empty-env))
          u (#'elab/fresh-level-mvar! st)
          id (lvl/mvar-id u)
          _ (reset! (:level-mctx st) {})
          result (#'elab/collecting-finalize st (e/sort' u))]
      (is (= [id] (mapv :id (:level-holes result))))))

  (testing "instance-hole metadata is reported from :meta-mctx without compatibility entries"
    (let [st (#'elab/mk-elab-state (env/empty-env))
          hole (#'elab/fresh-mvar! st (e/sort' lvl/zero)
                                    {:kind :synthetic :inst-implicit? true})
          id (e/mvar-id hole)
          _ (reset! (:mctx st) {})
          result (#'elab/collecting-finalize st hole)
          reported (first (:holes result))]
      (is (= id (:id reported)))
      (is (:inst-implicit? reported)))))

(deftest test-elab-collecting-only-reports-result-mvars
  (testing "unused fresh expression mvars are not collected as holes"
    (let [st (#'elab/mk-elab-state (env/empty-env))
          live (#'elab/fresh-mvar! st (e/sort' lvl/zero))
          live-id (e/mvar-id live)
          stale (#'elab/fresh-mvar! st (e/sort' lvl/zero))
          stale-id (e/mvar-id stale)
          result (#'elab/collecting-finalize st live)]
      (is (= [live-id] (mapv :id (:holes result))))
      (is (not (some #{stale-id} (mapv :id (:holes result)))))))

  (testing "unused fresh level mvars are not collected as level holes"
    (let [st (#'elab/mk-elab-state (env/empty-env))
          live (#'elab/fresh-level-mvar! st)
          live-id (lvl/mvar-id live)
          stale (#'elab/fresh-level-mvar! st)
          stale-id (lvl/mvar-id stale)
          result (#'elab/collecting-finalize st (e/sort' live))]
      (is (= [live-id] (mapv :id (:level-holes result))))
      (is (not (some #{stale-id} (mapv :id (:level-holes result)))))))

  (testing "assigned fresh mvars are followed before collecting"
    (let [st (#'elab/mk-elab-state (env/empty-env))
          source (#'elab/fresh-mvar! st (e/sort' lvl/zero))
          source-id (e/mvar-id source)
          target (#'elab/fresh-mvar! st (e/sort' lvl/zero))
          target-id (e/mvar-id target)]
      (is (#'elab/solve-mvar! st source-id target))
      (let [result (#'elab/collecting-finalize st source)]
        (is (= [target-id] (mapv :id (:holes result))))
        (is (not (some #{source-id} (mapv :id (:holes result)))))))))

(deftest test-elab-assignment-writes-metacontext-without-compatibility-entry
  (testing "expression assignment does not require a compatibility mctx entry"
    (let [st (#'elab/mk-elab-state (env/empty-env))
          hole (#'elab/fresh-mvar! st (e/sort' lvl/zero))
          id (e/mvar-id hole)
          solution (e/sort' lvl/zero)
          _ (reset! (:mctx st) {})]
      (is (#'elab/solve-mvar! st id solution))
      (is (= solution (meta/expr-assignment @(:meta-mctx st) id)))
      (is (nil? (get @(:mctx st) id)))))

  (testing "level assignment does not require a compatibility level entry"
    (let [st (#'elab/mk-elab-state (env/empty-env))
          u (#'elab/fresh-level-mvar! st)
          id (lvl/mvar-id u)
          _ (reset! (:level-mctx st) {})]
      (is (#'elab/solve-level-mvar! st id lvl/zero))
      (is (= lvl/zero (meta/level-assignment @(:meta-mctx st) id)))
      (is (nil? (get @(:level-mctx st) id))))))

;; ============================================================
;; elaborate-check (full verification)
;; ============================================================

(deftest test-elaborate-check
  (testing "elaborate-check verifies via kernel"
    (let [env (require-init-medium)
          result (elab/elaborate-check env '(forall [a Nat] (Eq a a)))]
      (is (e/forall? result)))))

(deftest test-elaborate-check-lambda
  (testing "elaborate-check on lambda with implicits"
    (let [env (require-init-medium)
          result (elab/elaborate-check env '(lam [a Nat] (Eq.refl a)))]
      (is (e/lam? result)))))
