(ns ansatz.meta-test
  (:require [clojure.test :refer [deftest is testing]]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.name :as name]
            [ansatz.meta :as meta]
            [ansatz.export.parser :as parser]
            [ansatz.export.replay :as replay]
            [ansatz.tactic.basic :as basic]
            [ansatz.tactic.extract :as extract]
            [ansatz.tactic.proof :as proof]))

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

(defn- local-id [ps local-name]
  (some (fn [[id d]]
          (when (and (= :local (:tag d))
                     (= local-name (:name d)))
            id))
        (:lctx (proof/current-goal ps))))

(defn- assert-meta-extract-parity [ps]
  (let [legacy-term (extract/extract-legacy ps)
        meta-term (extract/extract-meta ps)
        default-term (extract/extract ps)]
    (is (proof/solved? ps))
    (is (= legacy-term meta-term))
    (is (= meta-term default-term))
    (is (meta/closed-expr? (:meta-mctx ps) meta-term))))

(deftest zonk-instantiates-expression-and-level-mvars
  (testing "direct expression and level assignments are chased together"
    (let [u (lvl/mvar 10)
          ty (e/sort' u)
          value (e/const' (name/from-string "Nat") [u])
          mctx (-> meta/empty-context
                   (meta/add-level-mvar-decl 10)
                   (meta/add-expr-mvar-decl 1 ty {})
                   (meta/assign-level 10 lvl/zero)
                   (meta/assign-expr 1 value))
          zonked (meta/zonk-expr mctx (e/mvar 1))]
      (is (= (e/const' (name/from-string "Nat") [lvl/zero])
             zonked))
      (is (meta/closed-expr? mctx zonked)))))

(deftest delayed-assignment-expands-when-pending-is-ground
  (testing "a delayed assignment rebinds its fvars once the pending mvar is solved"
    (let [mctx (-> meta/empty-context
                   (meta/add-expr-mvar-decl 1 (e/sort' lvl/zero) {})
                   (meta/add-expr-mvar-decl 2 (e/sort' lvl/zero) {})
                   (meta/assign-delayed 1 [(e/fvar 42)] 2)
                   (meta/assign-expr 2 (e/fvar 42)))
          expr (e/app (e/mvar 1) (e/lit-nat 7))]
      (is (= (e/lit-nat 7) (meta/zonk-expr mctx expr))))))

(deftest lean-shaped-metacontext-queries
  (testing "depth gates expression and universe mvar assignability"
    (let [mctx (-> meta/empty-context
                   (meta/add-level-mvar-decl 10)
                   (meta/add-expr-mvar-decl 1 (e/sort' lvl/zero) {}))]
      (is (meta/expr-assignable? mctx 1))
      (is (meta/level-assignable? mctx 10))
      (is (not (meta/expr-assignable? (meta/inc-depth mctx) 1)))
      (is (not (meta/level-assignable? (meta/with-level-assign-depth mctx 1) 10)))))

  (testing "assigned and assignable scans see expression and level mvars"
    (let [u (lvl/mvar 10)
          expr (e/app (e/mvar 1) (e/sort' u))
          mctx (-> meta/empty-context
                   (meta/add-level-mvar-decl 10)
                   (meta/add-expr-mvar-decl 1 (e/sort' lvl/zero) {})
                   (meta/assign-expr 1 (e/lit-nat 3)))]
      (is (meta/has-assigned-mvar? mctx expr))
      (is (meta/has-assignable-mvar? mctx expr))
      (is (not (meta/has-assignable-mvar? (meta/inc-depth mctx) (e/mvar 1)))))))

(deftest checked-expression-assignment-accepts-well-typed-local-values
  (let [prop (e/sort' lvl/zero)
        lctx {42 {:tag :local :id 42 :name "h" :type prop}}
        mctx (-> meta/empty-context
                 (meta/add-expr-mvar-decl 1 prop lctx)
                 (meta/checked-assign-expr 1 (e/fvar 42) {:env (env/empty-env)}))]
    (is (= (e/fvar 42) (meta/expr-assignment mctx 1)))))

(deftest checked-expression-assignment-rejects-cycles-and-escaping-fvars
  (let [prop (e/sort' lvl/zero)
        mctx (meta/add-expr-mvar-decl meta/empty-context 1 prop {})]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"cyclic"
                          (meta/checked-assign-expr mctx 1 (e/mvar 1))))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"outside"
                          (meta/checked-assign-expr mctx 1 (e/fvar 99))))))

(deftest checked-expression-assignment-respects-depth-and-unification-kind
  (let [prop (e/sort' lvl/zero)
        mctx (meta/add-expr-mvar-decl meta/empty-context 1 prop {})
        nested (meta/inc-depth mctx)]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"current depth"
                          (meta/checked-assign-expr nested 1 prop))))
  (let [prop (e/sort' lvl/zero)
        mctx (meta/add-expr-mvar-decl meta/empty-context 1 prop {}
                                      {:kind :syntheticOpaque})]
    (is (meta/checked-assign-expr mctx 1 prop))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"unification"
                          (meta/checked-assign-expr mctx 1 prop {:unification? true})))))

(deftest checked-universe-assignment-respects-depth-and-occurs-check
  (let [mctx (meta/add-level-mvar-decl meta/empty-context 10)]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"cyclic"
                          (meta/checked-assign-level mctx 10 (lvl/succ (lvl/mvar 10)))))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"current depth"
                          (meta/checked-assign-level
                           (meta/with-level-assign-depth mctx 1) 10 lvl/zero)))))

(deftest instantiate-mvar-declaration-mvars
  (testing "assigned mvars are instantiated inside declaration types and local contexts"
    (let [u (lvl/mvar 10)
          prop (e/sort' lvl/zero)
          lctx {42 {:tag :local :id 42 :name "h" :type (e/mvar 2)}}
          mctx (-> meta/empty-context
                   (meta/add-level-mvar-decl 10)
                   (meta/add-expr-mvar-decl 1 (e/sort' u) lctx)
                   (meta/add-expr-mvar-decl 2 prop {})
                   (meta/assign-level 10 lvl/zero)
                   (meta/assign-expr 2 prop)
                   (meta/instantiate-mvar-decl-mvars 1))
          decl (meta/expr-decl mctx 1)]
      (is (= prop (:type decl)))
      (is (= prop (get-in decl [:lctx 42 :type]))))))

(deftest expr-dependency-is-conservative-over-unassigned-mvars
  (testing "assigned mvars are followed and unassigned mvars may depend on their local context"
    (let [prop (e/sort' lvl/zero)
          mctx (-> meta/empty-context
                   (meta/add-expr-mvar-decl 1 prop {42 {:tag :local :id 42 :name "x" :type prop}})
                   (meta/add-expr-mvar-decl 2 prop {})
                   (meta/assign-expr 2 (e/fvar 7)))]
      (is (meta/expr-depends-on? mctx (e/mvar 1) 42))
      (is (meta/expr-depends-on? mctx (e/mvar 2) 7))
      (is (not (meta/expr-depends-on? mctx (e/mvar 1) 99))))))

(deftest collect-mvars-and-dependencies
  (testing "expr-mvars instantiates direct assignments and follows delayed assignments"
    (let [prop (e/sort' lvl/zero)
          mctx (-> meta/empty-context
                   (meta/add-expr-mvar-decl 1 prop {})
                   (meta/add-expr-mvar-decl 2 prop {})
                   (meta/add-expr-mvar-decl 3 prop {})
                   (meta/assign-expr 1 (e/mvar 2))
                   (meta/assign-delayed 2 [(e/fvar 42)] 3))]
      (is (= [2 3] (meta/expr-mvars mctx (e/mvar 1))))
      (is (= [3] (meta/expr-mvars-no-delayed mctx (e/mvar 1))))))

  (testing "mvar dependencies inspect declaration types and local contexts"
    (let [prop (e/sort' lvl/zero)
          lctx {42 {:tag :local :id 42 :name "x" :type (e/mvar 3)}}
          mctx (-> meta/empty-context
                   (meta/add-expr-mvar-decl 1 (e/mvar 2) lctx)
                   (meta/add-expr-mvar-decl 2 prop {})
                   (meta/add-expr-mvar-decl 3 prop {}))]
      (is (= [2 3] (meta/mvar-dependencies mctx 1)))
      (is (= [1 2 3] (meta/expr-mvar-dependencies mctx (e/mvar 1)))))))

(deftest proof-state-mirrors-legacy-assignments-into-meta-mctx
  (testing "a solved tactic proof can be read as a zonked root mvar"
    (let [prop (e/sort' lvl/zero)
          ;; ∀ (p : Prop), p -> p
          goal-type (e/forall' "p" prop
                               (e/forall' "h" (e/bvar 0) (e/bvar 1) :default)
                               :default)
          [ps root] (proof/start-proof (env/empty-env) goal-type)
          ps (-> ps
                 (basic/intro "p")
                 (basic/intro "h")
                 (basic/assumption))
          meta-term (extract/extract-meta ps)]
      (assert-meta-extract-parity ps)
      (is (= meta-term (meta/zonk-expr (:meta-mctx ps) (e/mvar root))))
      (is (meta/closed-expr? (:meta-mctx ps) meta-term)))))

(deftest verify-rejects-raw-metavariables-at-kernel-boundary
  (testing "legacy extraction cannot pass raw mvars to the kernel checker"
    (let [prop (e/sort' lvl/zero)
          [ps root] (proof/start-proof (env/empty-env) prop)
          ps (proof/assign-mvar ps root {:kind :exact :term (e/mvar 999)})]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"metavariables"
                            (extract/verify ps))))))

(deftest proof-assignment-mirror-rejects-cyclic-meta-assignment
  (testing "tactic assignment cannot write a self-referential term into :meta-mctx"
    (let [prop (e/sort' lvl/zero)
          [ps root] (proof/start-proof (env/empty-env) prop)]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"cyclic"
                            (proof/assign-mvar ps root {:kind :exact :term (e/mvar root)})))
      (is (nil? (meta/expr-assignment (:meta-mctx ps) root))))))

(deftest extract-meta-parity-for-apply
  (testing "apply assignments are mirrored as an mvar application spine"
    (let [prop (e/sort' lvl/zero)
          ;; ∀ (p q : Prop), (p -> q) -> p -> q
          goal-type (e/forall' "p" prop
                               (e/forall' "q" prop
                                          (e/forall' "h" (e/forall' "_" (e/bvar 1) (e/bvar 1) :default)
                                                     (e/forall' "hp" (e/bvar 2) (e/bvar 2) :default)
                                                     :default)
                                          :default)
                               :default)
          [ps _] (proof/start-proof (env/empty-env) goal-type)
          ps (basic/intros ps ["p" "q" "h" "hp"])
          goal (proof/current-goal ps)
          h-id (some (fn [[id d]] (when (= "h" (:name d)) id)) (:lctx goal))
          ps (basic/apply-tac ps (e/fvar h-id))
          ps (basic/assumption ps)]
      (assert-meta-extract-parity ps))))

(deftest extract-meta-parity-for-have
  (testing "have assignments are mirrored with delayed abstraction over the new hypothesis"
    (let [prop (e/sort' lvl/zero)
          ;; ∀ (p : Prop), p -> p
          goal-type (e/forall' "p" prop
                               (e/forall' "h" (e/bvar 0) (e/bvar 1) :default)
                               :default)
          [ps _] (proof/start-proof (env/empty-env) goal-type)
          ps (basic/intros ps ["p" "h"])
          goal (proof/current-goal ps)
          p-id (some (fn [[id d]] (when (= "p" (:name d)) id)) (:lctx goal))
          ps (basic/have-tac ps "k" (e/fvar p-id))
          ps (basic/assumption ps)
          ps (basic/assumption ps)]
      (assert-meta-extract-parity ps))))

(deftest extract-meta-parity-for-simp-reduce-child
  (testing "whnf-goal delegates through a child mvar that meta extraction can zonk"
    (let [prop (e/sort' lvl/zero)
          type1 (e/sort' (lvl/succ lvl/zero))
          reduced (e/forall' "h" prop prop :default)
          goal-type (e/let' "P" type1 prop reduced)
          [ps _] (proof/start-proof (env/empty-env) goal-type)
          ps (basic/whnf-goal ps)
          ps (basic/intro ps "h")
          ps (basic/assumption ps)]
      (assert-meta-extract-parity ps))))

(deftest extract-meta-parity-for-cases
  (testing "case split branches are mirrored with delayed abstraction"
    (let [env (require-init-medium)
          bool-t (e/const' (name/from-string "Bool") [])
          u1 (lvl/succ lvl/zero)
          eq-name (name/from-string "Eq")
          eq-bb (e/app* (e/const' eq-name [u1]) bool-t (e/bvar 0) (e/bvar 0))
          goal-type (e/forall' "b" bool-t eq-bb :default)
          [ps _] (proof/start-proof env goal-type)
          ps (basic/intro ps "b")
          goal (proof/current-goal ps)
          b-id (some (fn [[id d]] (when (= "b" (:name d)) id)) (:lctx goal))
          ps (basic/cases ps b-id)
          ps (basic/rfl ps)
          ps (basic/rfl ps)]
      (assert-meta-extract-parity ps))))

(deftest extract-meta-parity-for-rewrite
  (testing "rewrite assignments are mirrored through Eq.ndrec transport"
    (let [env (require-init-medium)
          nat (e/const' (name/from-string "Nat") [])
          u1 (lvl/succ lvl/zero)
          eq-name (name/from-string "Eq")
          eq-ab (e/app* (e/const' eq-name [u1]) nat (e/bvar 1) (e/bvar 0))
          eq-ba (e/app* (e/const' eq-name [u1]) nat (e/bvar 1) (e/bvar 2))
          goal-type (e/forall' "a" nat
                               (e/forall' "b" nat
                                          (e/forall' "h" eq-ab eq-ba :default)
                                          :default)
                               :default)
          [ps _] (proof/start-proof env goal-type)
          ps (basic/intros ps ["a" "b" "h"])
          ps (basic/rewrite ps (e/fvar (local-id ps "h")))
          ps (basic/rfl ps)]
      (assert-meta-extract-parity ps))))

(deftest extract-meta-parity-for-generalize
  (testing "generalize assignments are mirrored as child application to the original term and rfl"
    (let [env (require-init-medium)
          nat (e/const' (name/from-string "Nat") [])
          u1 (lvl/succ lvl/zero)
          eq-name (name/from-string "Eq")
          eq-nn (e/app* (e/const' eq-name [u1]) nat (e/bvar 0) (e/bvar 0))
          goal-type (e/forall' "n" nat eq-nn :default)
          [ps _] (proof/start-proof env goal-type)
          ps (basic/intro ps "n")
          ps (basic/generalize ps (e/fvar (local-id ps "n")) "x" "h")
          ps (basic/intro ps "x")
          ps (basic/intro ps "h")
          ps (basic/rfl ps)]
      (assert-meta-extract-parity ps))))

(deftest extract-meta-parity-for-revert
  (testing "revert assignments are mirrored as child application to the reverted hypothesis"
    (let [prop (e/sort' lvl/zero)
          goal-type (e/forall' "p" prop
                               (e/forall' "h" (e/bvar 0) (e/bvar 1) :default)
                               :default)
          [ps _] (proof/start-proof (env/empty-env) goal-type)
          ps (basic/intros ps ["p" "h"])
          ps (basic/revert ps (local-id ps "h"))
          ps (basic/intro ps "h")
          ps (basic/assumption ps)]
      (assert-meta-extract-parity ps))))

(deftest extract-meta-parity-for-exfalso
  (testing "exfalso assignments are mirrored through False.elim"
    (let [prop (e/sort' lvl/zero)
          false-type (e/const' (name/from-string "False") [])
          goal-type (e/forall' "p" prop
                               (e/forall' "h" false-type (e/bvar 1) :default)
                               :default)
          [ps _] (proof/start-proof (env/empty-env) goal-type)
          ps (basic/intros ps ["p" "h"])
          ps (basic/exfalso ps)
          ps (basic/assumption ps)]
      (assert-meta-extract-parity ps))))

(deftest extract-meta-parity-for-subst
  (testing "subst assignments are mirrored by replacing the child mvar in the prebuilt ndrec term"
    (let [env (require-init-medium)
          nat (e/const' (name/from-string "Nat") [])
          u1 (lvl/succ lvl/zero)
          eq-name (name/from-string "Eq")
          eq-ab (e/app* (e/const' eq-name [u1]) nat (e/bvar 1) (e/bvar 0))
          eq-bb (e/app* (e/const' eq-name [u1]) nat (e/bvar 1) (e/bvar 1))
          goal-type (e/forall' "a" nat
                               (e/forall' "b" nat
                                          (e/forall' "h" eq-ab eq-bb :default)
                                          :default)
                               :default)
          [ps _] (proof/start-proof env goal-type)
          ps (basic/intros ps ["a" "b" "h"])
          ps (basic/subst ps (local-id ps "h"))
          ps (basic/rfl ps)]
      (assert-meta-extract-parity ps))))

(deftest extract-meta-parity-for-clear
  (testing "clear assignments are mirrored as a transparent child proof"
    (let [env (require-init-medium)
          nat (e/const' (name/from-string "Nat") [])
          u1 (lvl/succ lvl/zero)
          eq-name (name/from-string "Eq")
          eq-nn (e/app* (e/const' eq-name [u1]) nat (e/bvar 1) (e/bvar 1))
          goal-type (e/forall' "n" nat
                               (e/forall' "m" nat eq-nn :default)
                               :default)
          [ps _] (proof/start-proof env goal-type)
          ps (basic/intros ps ["n" "m"])
          ps (basic/clear ps (local-id ps "m"))
          ps (basic/rfl ps)]
      (assert-meta-extract-parity ps))))

(deftest extract-meta-parity-for-by-cases
  (testing "Bool by-cases assignments are mirrored as Bool.rec over branch subgoals"
    (let [env (require-init-medium)
          bool-t (e/const' (name/from-string "Bool") [])
          u1 (lvl/succ lvl/zero)
          eq-name (name/from-string "Eq")
          eq-bb (e/app* (e/const' eq-name [u1]) bool-t (e/bvar 0) (e/bvar 0))
          goal-type (e/forall' "b" bool-t eq-bb :default)
          [ps _] (proof/start-proof env goal-type)
          ps (basic/intro ps "b")
          ps (basic/by-cases ps (e/fvar (local-id ps "b")))
          ps (basic/rfl ps)
          ps (basic/rfl ps)]
      (assert-meta-extract-parity ps))))

(deftest extract-meta-parity-for-by-cases-dec
  (testing "Decidable by-cases assignments are mirrored as Decidable.casesOn"
    (let [env (require-init-medium)
          prop (e/sort' lvl/zero)
          dec-name (name/from-string "Decidable")
          goal-type (e/forall' "p" prop
                               (e/forall' "dec" (e/app* (e/const' dec-name []) (e/bvar 0))
                                          (e/forall' "hp" (e/bvar 1) (e/bvar 2) :default)
                                          :default)
                               :default)
          [ps _] (proof/start-proof env goal-type)
          ps (basic/intros ps ["p" "dec" "hp"])
          ps (basic/by-cases-dec ps (e/fvar (local-id ps "p")) (e/fvar (local-id ps "dec")))
          ps (basic/assumption ps)
          ps (basic/assumption ps)]
      (assert-meta-extract-parity ps))))
