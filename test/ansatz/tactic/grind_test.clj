(ns ansatz.tactic.grind-test
  "Tests for grind tactic and E-graph."
  (:require [clojure.test :refer [deftest testing is]]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.tc :as tc]
            [ansatz.tactic.proof :as proof]
            [ansatz.tactic.basic :as basic]
            [ansatz.tactic.grind :as grind]
            [ansatz.tactic.grind.egraph :as eg]
            [ansatz.tactic.grind.proof :as egproof]
            [ansatz.tactic.grind.ematch :as ematch]
            [ansatz.tactic.grind.solver :as solver]
            [ansatz.tactic.extract :as extract]
            [ansatz.export.parser :as parser]
            [ansatz.export.replay :as replay])
  (:import [ansatz.kernel TypeChecker]))

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
(defn- mk-eq [a b]
  (e/app* (e/const' (name/from-string "Eq") [u1]) nat a b))

;; ============================================================
;; Grind via rfl
;; ============================================================

(deftest test-grind-rfl
  (testing "grind solves a = a via rfl"
    (let [env (require-env)
          goal (e/forall' "a" nat (mk-eq (e/bvar 0) (e/bvar 0)) :default)
          [ps _] (proof/start-proof env goal)
          ps (basic/intro ps "a")
          ps (grind/grind ps)]
      (is (proof/solved? ps))
      (let [term (extract/extract ps)]
        (is (some? term))
        (is (not (e/has-fvar-flag term)))))))

;; ============================================================
;; Grind via assumption
;; ============================================================

(deftest test-grind-assumption
  (testing "grind solves a = b from h : a = b via assumption"
    (let [env (require-env)
          h-type (mk-eq (e/bvar 2) (e/bvar 1))
          concl (mk-eq (e/bvar 3) (e/bvar 2))
          goal (e/forall' "a" nat
                          (e/forall' "b" nat
                                     (e/forall' "h" h-type concl :default) :default) :default)
          [ps _] (proof/start-proof env goal)
          ps (basic/intros ps ["a" "b" "h"])
          ps (grind/grind ps)]
      (is (proof/solved? ps)))))

;; ============================================================
;; Grind via congruence closure
;; ============================================================

(deftest test-grind-congruence
  (testing "grind solves f(a) = f(b) from h : a = b via congruence closure"
      (let [env (require-env)
            nat-to-nat (e/arrow nat nat)
          ;; forall a b : Nat, forall f : Nat -> Nat, h : a = b |- f a = f b
            h-type (mk-eq (e/bvar 2) (e/bvar 1))
            concl (mk-eq (e/app (e/bvar 1) (e/bvar 3))
                         (e/app (e/bvar 1) (e/bvar 2)))
            goal (e/forall' "a" nat
                            (e/forall' "b" nat
                                       (e/forall' "f" nat-to-nat
                                                  (e/forall' "h" h-type concl :default) :default) :default) :default)
            [ps _] (proof/start-proof env goal)
            ps (basic/intros ps ["a" "b" "f" "h"])
            ps (grind/grind ps)]
        (is (proof/solved? ps)))))

(deftest test-grind-transitivity
  (testing "grind solves a = c from h1 : a = b, h2 : b = c via CC"
      (let [env (require-env)
          ;; forall a b c : Nat, h1 : a = b, h2 : b = c |- a = c
            h1-type (mk-eq (e/bvar 2) (e/bvar 1))
            h2-type (mk-eq (e/bvar 2) (e/bvar 1))
            concl (mk-eq (e/bvar 4) (e/bvar 2))
            goal (e/forall' "a" nat
                            (e/forall' "b" nat
                                       (e/forall' "c" nat
                                                  (e/forall' "h1" h1-type
                                                             (e/forall' "h2" h2-type concl :default) :default) :default) :default) :default)
            [ps _] (proof/start-proof env goal)
            ps (basic/intros ps ["a" "b" "c" "h1" "h2"])
            ps (grind/grind ps)]
        (is (proof/solved? ps))))

(deftest test-grind-deep-congruence
  (testing "grind solves g(f(a)) = g(f(b)) from h : a = b via deep CC"
      (let [env (require-env)
            nat-to-nat (e/arrow nat nat)
          ;; forall a b : Nat, f g : Nat -> Nat, h : a = b |- g(f(a)) = g(f(b))
          ;; h binder (depth 4): a=#3, b=#2, f=#1, g=#0
            h-type (mk-eq (e/bvar 3) (e/bvar 2))
          ;; concl (depth 5): a=#4, b=#3, f=#2, g=#1
            concl (mk-eq (e/app (e/bvar 1) (e/app (e/bvar 2) (e/bvar 4)))
                         (e/app (e/bvar 1) (e/app (e/bvar 2) (e/bvar 3))))
            goal (e/forall' "a" nat
                            (e/forall' "b" nat
                                       (e/forall' "f" nat-to-nat
                                                  (e/forall' "g" nat-to-nat
                                                             (e/forall' "h" h-type concl :default) :default) :default) :default) :default)
            [ps _] (proof/start-proof env goal)
            ps (basic/intros ps ["a" "b" "f" "g" "h"])
            ps (grind/grind ps)]
        (is (proof/solved? ps))))))

;; ============================================================
;; E-Graph unit tests (Phase 2)
;; ============================================================

;; Helpers for E-graph tests — use fvars as simple distinct terms
(defn- fv [n] (e/fvar n))
(def ^:private true-expr (e/const' (name/from-string "True") []))
(def ^:private false-expr (e/const' (name/from-string "False") []))
(def ^:private and-const (e/const' (name/from-string "And") []))
(def ^:private or-const (e/const' (name/from-string "Or") []))
(def ^:private not-const (e/const' (name/from-string "Not") []))
(defn- mk-and [a b] (e/app* and-const a b))
(defn- mk-or [a b] (e/app* or-const a b))
(defn- mk-not [a] (e/app not-const a))

(deftest test-egraph-internalize
  (testing "Internalize creates ENodes and tracks parents"
    (let [env (require-env)
          gs (eg/mk-grind-state env)
          a (fv 100) b (fv 101)
          ;; Internalize two distinct fvars
          gs (-> gs (eg/internalize a 0) (eg/internalize b 0))]
      (is (some? (eg/get-enode gs a)) "a is internalized")
      (is (some? (eg/get-enode gs b)) "b is internalized")
      ;; Each is its own root
      (is (identical? a (eg/get-root gs a)) "a is its own root")
      (is (identical? b (eg/get-root gs b)) "b is its own root")
      ;; Not equivalent
      (is (not (eg/is-eqv gs a b)) "a and b not equivalent"))))

(deftest test-egraph-merge-basic
  (testing "Merging two fvars makes them equivalent"
    (let [env (require-env)
          gs (eg/mk-grind-state env)
          a (fv 200) b (fv 201)
          gs (-> gs (eg/internalize a 0) (eg/internalize b 0))
          gs (eg/assert-eq gs a b :test-proof)]
      (is (eg/is-eqv gs a b) "a and b are now equivalent")
      ;; They share the same root
      (is (identical? (eg/get-root gs a) (eg/get-root gs b)) "same root"))))

(deftest test-egraph-transitivity
  (testing "a=b, b=c implies a=c via merge"
    (let [env (require-env)
          gs (eg/mk-grind-state env)
          a (fv 300) b (fv 301) c (fv 302)
          gs (-> gs (eg/internalize a 0) (eg/internalize b 0) (eg/internalize c 0))
          gs (eg/assert-eq gs a b :proof-ab)
          gs (eg/assert-eq gs b c :proof-bc)]
      (is (eg/is-eqv gs a c) "a=c by transitivity")
      (is (eg/is-eqv gs a b) "a=b still holds")
      (is (eg/is-eqv gs b c) "b=c still holds"))))

(deftest test-egraph-congruence
  (testing "f(a)=f(b) detected after merging a=b"
    (let [env (require-env)
          gs (eg/mk-grind-state env)
          a (fv 400) b (fv 401)
          f (e/const' (name/from-string "f_test") [])
          fa (e/app f a)
          fb (e/app f b)
          gs (-> gs
                 (eg/internalize fa 0)
                 (eg/internalize fb 0))
          ;; Before merge: f(a) and f(b) are different
          _ (is (not (eg/is-eqv gs fa fb)) "f(a)!=f(b) before merge")
          ;; Merge a=b
          gs (eg/assert-eq gs a b :proof-ab)]
      ;; After merge: congruence closure should detect f(a)=f(b)
      (is (eg/is-eqv gs fa fb) "f(a)=f(b) by congruence"))))

(deftest test-egraph-deep-congruence
  (testing "g(f(a))=g(f(b)) detected after merging a=b"
    (let [env (require-env)
          gs (eg/mk-grind-state env)
          a (fv 500) b (fv 501)
          f (e/const' (name/from-string "f_test2") [])
          g (e/const' (name/from-string "g_test2") [])
          gfa (e/app g (e/app f a))
          gfb (e/app g (e/app f b))
          gs (-> gs
                 (eg/internalize gfa 0)
                 (eg/internalize gfb 0))
          gs (eg/assert-eq gs a b :proof-ab)]
      (is (eg/is-eqv gs gfa gfb) "g(f(a))=g(f(b)) by deep congruence"))))

(deftest test-egraph-true-false-inconsistency
  (testing "Merging True=False marks inconsistent"
    (let [env (require-env)
          gs (eg/mk-grind-state env)
          gs (eg/assert-eq gs (:true-expr gs) (:false-expr gs) :absurd)]
      (is (:inconsistent gs) "True=False is inconsistent"))))

(deftest test-egraph-eqc-traversal
  (testing "Equivalence class traversal returns all members"
    (let [env (require-env)
          gs (eg/mk-grind-state env)
          a (fv 600) b (fv 601) c (fv 602)
          gs (-> gs
                 (eg/internalize a 0) (eg/internalize b 0) (eg/internalize c 0))
          gs (-> gs
                 (eg/assert-eq a b :p1)
                 (eg/assert-eq b c :p2))
          members (set (eg/collect-eqc gs (eg/get-root gs a)))]
      (is (contains? members a) "a in eqc")
      (is (contains? members b) "b in eqc")
      (is (contains? members c) "c in eqc"))))

;; ============================================================
;; Propagator tests (Phase 2)
;; ============================================================

(deftest test-propagator-and-up
  (testing "And propagator UP: a=True → (a∧b)=b"
    (let [env (require-env)
          gs (eg/mk-grind-state env)
          a (fv 700) b (fv 701)
          ab (mk-and a b)
          gs (-> gs (eg/internalize ab 0))
          ;; Assert a=True
          gs (eg/assert-true gs a :proof-a-true)]
      (is (eg/is-eqv gs ab b) "(a∧b)=b when a=True"))))

(deftest test-propagator-and-down
  (testing "And propagator DOWN: (a∧b)=True → a=True, b=True"
    (let [env (require-env)
          gs (eg/mk-grind-state env)
          a (fv 710) b (fv 711)
          ab (mk-and a b)
          gs (-> gs (eg/internalize ab 0))
          ;; Assert (a∧b)=True
          gs (eg/assert-true gs ab :proof-and-true)]
      (is (eg/is-eq-true gs a) "a=True from (a∧b)=True")
      (is (eg/is-eq-true gs b) "b=True from (a∧b)=True"))))

(deftest test-propagator-or-up
  (testing "Or propagator UP: a=False → (a∨b)=b"
    (let [env (require-env)
          gs (eg/mk-grind-state env)
          a (fv 720) b (fv 721)
          ab (mk-or a b)
          gs (-> gs (eg/internalize ab 0))
          ;; Assert a=False
          gs (eg/assert-false gs a :proof-a-false)]
      (is (eg/is-eqv gs ab b) "(a∨b)=b when a=False"))))

(deftest test-propagator-or-down
  (testing "Or propagator DOWN: (a∨b)=False → a=False, b=False"
    (let [env (require-env)
          gs (eg/mk-grind-state env)
          a (fv 730) b (fv 731)
          ab (mk-or a b)
          gs (-> gs (eg/internalize ab 0))
          ;; Assert (a∨b)=False
          gs (eg/assert-false gs ab :proof-or-false)]
      (is (eg/is-eq-false gs a) "a=False from (a∨b)=False")
      (is (eg/is-eq-false gs b) "b=False from (a∨b)=False"))))

(deftest test-propagator-not-up
  (testing "Not propagator UP: a=False → ¬a=True"
    (let [env (require-env)
          gs (eg/mk-grind-state env)
          a (fv 740)
          not-a (mk-not a)
          gs (-> gs (eg/internalize not-a 0))
          gs (eg/assert-false gs a :proof-a-false)]
      (is (eg/is-eq-true gs not-a) "¬a=True when a=False"))))

(deftest test-propagator-not-down
  (testing "Not propagator DOWN: ¬a=True → a=False"
    (let [env (require-env)
          gs (eg/mk-grind-state env)
          a (fv 750)
          not-a (mk-not a)
          gs (-> gs (eg/internalize not-a 0))
          gs (eg/assert-true gs not-a :proof-not-true)]
      (is (eg/is-eq-false gs a) "a=False from ¬a=True"))))

(deftest test-propagator-and-false
  (testing "And propagator UP: a=False → (a∧b)=False"
    (let [env (require-env)
          gs (eg/mk-grind-state env)
          a (fv 760) b (fv 761)
          ab (mk-and a b)
          gs (-> gs (eg/internalize ab 0))
          gs (eg/assert-false gs a :proof-a-false)]
      (is (eg/is-eq-false gs ab) "(a∧b)=False when a=False"))))

(deftest test-propagator-or-true
  (testing "Or propagator UP: a=True → (a∨b)=True"
    (let [env (require-env)
          gs (eg/mk-grind-state env)
          a (fv 770) b (fv 771)
          ab (mk-or a b)
          gs (-> gs (eg/internalize ab 0))
          gs (eg/assert-true gs a :proof-a-true)]
      (is (eg/is-eq-true gs ab) "(a∨b)=True when a=True"))))

;; ============================================================
;; Proof reconstruction tests (Phase 2.4)
;; These build CIC proof terms from E-graph paths and verify
;; them with the Java kernel TypeChecker.
;; ============================================================

(defn- verify-with-lctx
  "Verify a proof term using the Java TypeChecker with local context bindings."
  [env lctx proof-term]
  (let [tc (TypeChecker. env)]
    (.setFuel tc 5000000)
    ;; Add all local context entries so TC can resolve fvars
    (doseq [[id decl] lctx]
      (.addLocal tc (long id) (str (:name decl)) (:type decl)))
    (.inferType tc proof-term)))

(deftest test-egraph-proof-single-hyp
  (testing "E-graph proof: a=b from hypothesis, kernel-verified"
    (let [env (require-env)
          ;; forall a b : Nat, h : a = b |- a = b
          ;; Build proof via E-graph path
          goal (e/forall' "a" nat
                 (e/forall' "b" nat
                   (e/forall' "h" (mk-eq (e/bvar 1) (e/bvar 0))
                     (mk-eq (e/bvar 2) (e/bvar 1)) :default) :default) :default)
          [ps _] (proof/start-proof env goal)
          ps (basic/intros ps ["a" "b" "h"])
          g (proof/current-goal ps)
          st (assoc (tc/mk-tc-state env) :lctx (:lctx g))
          ;; Get the fvars from the context
          lctx-entries (vec (sort-by first (:lctx g)))
          a-fvar (e/fvar (first (nth lctx-entries 0)))
          b-fvar (e/fvar (first (nth lctx-entries 1)))
          h-fvar (e/fvar (first (nth lctx-entries 2)))
          ;; Build E-graph and internalize
          gs (eg/mk-grind-state env)
          gs (-> gs (eg/internalize a-fvar 0) (eg/internalize b-fvar 0))
          ;; Assert a=b with h as proof
          gs (eg/assert-eq gs a-fvar b-fvar h-fvar)
          ;; Build proof term from E-graph
          proof-term (egproof/mk-eq-proof gs st a-fvar b-fvar)]
      (is (some? proof-term) "proof term built")
      ;; Verify with kernel TypeChecker
      (is (try (verify-with-lctx env (:lctx g) proof-term) true
                 (catch Exception e
                   (println "Kernel error:" (.getMessage e))
                   false))
            "proof term passes kernel type check"))))

(deftest test-egraph-proof-transitivity
  (testing "E-graph proof: a=c from a=b, b=c, kernel-verified"
    (let [env (require-env)
          ;; forall a b c : Nat, h1 : a = b, h2 : b = c |- a = c
          h1-type (mk-eq (e/bvar 2) (e/bvar 1))
          h2-type (mk-eq (e/bvar 2) (e/bvar 1))
          concl (mk-eq (e/bvar 4) (e/bvar 2))
          goal (e/forall' "a" nat
                 (e/forall' "b" nat
                   (e/forall' "c" nat
                     (e/forall' "h1" h1-type
                       (e/forall' "h2" h2-type concl :default) :default) :default) :default) :default)
          [ps _] (proof/start-proof env goal)
          ps (basic/intros ps ["a" "b" "c" "h1" "h2"])
          g (proof/current-goal ps)
          st (assoc (tc/mk-tc-state env) :lctx (:lctx g))
          lctx-entries (vec (sort-by first (:lctx g)))
          a-fvar (e/fvar (first (nth lctx-entries 0)))
          b-fvar (e/fvar (first (nth lctx-entries 1)))
          c-fvar (e/fvar (first (nth lctx-entries 2)))
          h1-fvar (e/fvar (first (nth lctx-entries 3)))
          h2-fvar (e/fvar (first (nth lctx-entries 4)))
          ;; Build E-graph
          gs (eg/mk-grind-state env)
          gs (-> gs
                 (eg/internalize a-fvar 0)
                 (eg/internalize b-fvar 0)
                 (eg/internalize c-fvar 0))
          gs (eg/assert-eq gs a-fvar b-fvar h1-fvar)
          gs (eg/assert-eq gs b-fvar c-fvar h2-fvar)
          ;; Verify a=c in E-graph
          _ (is (eg/is-eqv gs a-fvar c-fvar) "a=c in E-graph")
          ;; Build proof
          proof-term (egproof/mk-eq-proof gs st a-fvar c-fvar)]
      (is (some? proof-term) "proof term built")
      (is (try (verify-with-lctx env (:lctx g) proof-term) true
               (catch Exception e
                 (println "Kernel error:" (.getMessage e))
                 false))
          "transitivity proof passes kernel"))))

(deftest test-egraph-proof-congruence
  (testing "E-graph proof: f(a)=f(b) from a=b, kernel-verified"
    (let [env (require-env)
          nat-to-nat (e/arrow nat nat)
          ;; forall a b : Nat, f : Nat -> Nat, h : a = b |- f a = f b
          h-type (mk-eq (e/bvar 2) (e/bvar 1))
          concl (mk-eq (e/app (e/bvar 1) (e/bvar 3))
                       (e/app (e/bvar 1) (e/bvar 2)))
          goal (e/forall' "a" nat
                 (e/forall' "b" nat
                   (e/forall' "f" nat-to-nat
                     (e/forall' "h" h-type concl :default) :default) :default) :default)
          [ps _] (proof/start-proof env goal)
          ps (basic/intros ps ["a" "b" "f" "h"])
          g (proof/current-goal ps)
          st (assoc (tc/mk-tc-state env) :lctx (:lctx g))
          lctx-entries (vec (sort-by first (:lctx g)))
          a-fvar (e/fvar (first (nth lctx-entries 0)))
          b-fvar (e/fvar (first (nth lctx-entries 1)))
          f-fvar (e/fvar (first (nth lctx-entries 2)))
          h-fvar (e/fvar (first (nth lctx-entries 3)))
          fa (e/app f-fvar a-fvar)
          fb (e/app f-fvar b-fvar)
          ;; Build E-graph — internalize f(a) and f(b)
          gs (eg/mk-grind-state env)
          gs (-> gs (eg/internalize fa 0) (eg/internalize fb 0))
          ;; Assert a=b
          gs (eg/assert-eq gs a-fvar b-fvar h-fvar)
          ;; Congruence should give f(a)=f(b)
          _ (is (eg/is-eqv gs fa fb) "f(a)=f(b) in E-graph")
          ;; Build proof
          proof-term (egproof/mk-eq-proof gs st fa fb)]
      (is (some? proof-term) "proof term built")
      (is (try (verify-with-lctx env (:lctx g) proof-term) true
               (catch Exception e
                 (println "Kernel error:" (.getMessage e))
                 false))
            "congruence proof passes kernel"))))

;; ============================================================
;; E-matching tests (Phase 3)
;; ============================================================

(deftest test-ematch-theorem-creation
  (testing "Create EMatchTheorem from Nat.add_zero"
    (let [env (require-env)
          thm (ematch/mk-ematch-theorem env (name/from-string "Nat.add_zero"))]
      (is (some? thm) "theorem created")
      (when thm
        (is (pos? (:num-params thm)) "has parameters")
        (is (seq (:patterns thm)) "has patterns")
        (is (= :eq-lhs (:kind thm)) "is equality theorem")))))

(deftest test-ematch-basic-matching
  (testing "E-matching: pattern f(x) matches f(3) in E-graph"
    (let [env (require-env)
          gs (eg/mk-grind-state env)
          ;; Create f and terms
          f (e/const' (name/from-string "f_em_test") [])
          three (e/lit-nat 3)
          f3 (e/app f three)
          ;; Internalize
          gs (eg/internalize gs f3 0)
          ;; Pattern: f(bvar0) — matches f(3) with bvar0 → 3
          pat (e/app f (e/bvar 0))
          matches (ematch/match-in-eqclass gs pat f3)]
      (is (seq matches) "found at least one match")
      (when (seq matches)
        (is (= three (get (:assignment (first matches)) 0))
            "bvar 0 assigned to 3")))))

(deftest test-ematch-eqclass-matching
  (testing "E-matching finds match via equivalence class"
    (let [env (require-env)
          gs (eg/mk-grind-state env)
          f (e/const' (name/from-string "f_em_test2") [])
          a (e/fvar 900) b (e/fvar 901)
          fa (e/app f a) fb (e/app f b)
          gs (-> gs (eg/internalize fa 0) (eg/internalize fb 0))
          ;; Merge a=b
          gs (eg/assert-eq gs a b :proof-ab)
          ;; Pattern: f(bvar0) — should match both f(a) and f(b)
          pat (e/app f (e/bvar 0))
          matches (ematch/match-in-eqclass gs pat fa)]
      ;; Should find matches for both a and b in the eq class
      (is (seq matches) "found matches"))))

(deftest test-ematch-instance-dedup
  (testing "E-matching deduplicates instances"
    (let [env (require-env)
          gs (eg/mk-grind-state env)
          f (e/const' (name/from-string "f_em_test3") [])
          three (e/lit-nat 3)
          f3 (e/app f three)
          gs (eg/internalize gs f3 0)
          ;; Create a mock theorem
          thm {:origin (name/from-string "test_thm")
               :proof (e/const' (name/from-string "test_thm") [])
               :type (e/sort' lvl/zero)
               :num-params 1
               :patterns [(e/app f (e/bvar 0))]
               :symbols [(name/from-string "f_em_test3")]
               :kind :eq-lhs}
          ;; Run two rounds — second should find no new instances
          r1 (ematch/ematch-round gs [thm] #{})
          r2 (ematch/ematch-round gs [thm] (:seen r1))]
      ;; First round finds instance, second round deduplicates
      (is (>= (count (:seen r1)) 1) "first round finds instances")
      (is (empty? (:new-facts r2)) "second round deduplicates"))))

;; ============================================================
;; Theory solver tests (Phase 4)
;; ============================================================

(deftest test-solver-protocol
  (testing "Solver registry initialization and protocol"
    (let [env (require-env)
          gs (eg/mk-grind-state env)
          registry (solver/mk-solver-registry)
          registry (solver/init-solvers registry gs)]
      (is (= 3 (count (:solvers registry))) "3 solvers registered")
      (is (= 3 (count (:states registry))) "3 states initialized")
      ;; All consistent initially
      (is (solver/check-all registry gs) "all consistent"))))

(deftest test-solver-merge-notify
  (testing "Solver registry notifies all solvers on merge"
    (let [env (require-env)
          gs (eg/mk-grind-state env)
          a (fv 800) b (fv 801)
          gs (-> gs (eg/internalize a 0) (eg/internalize b 0))
          registry (solver/mk-solver-registry)
          registry (solver/init-solvers registry gs)
          {:keys [gs registry]} (solver/notify-merge registry gs a b :proof-ab)]
      ;; After merge notification, still consistent
      (is (solver/check-all registry gs) "still consistent after merge"))))

(deftest test-solver-propagate
  (testing "Solver propagation runs without error"
    (let [env (require-env)
          gs (eg/mk-grind-state env)
          registry (solver/mk-solver-registry)
          registry (solver/init-solvers registry gs)
          {:keys [gs registry]} (solver/propagate-all registry gs)]
      (is (some? gs) "propagation returns state")
      (is (solver/check-all registry gs) "still consistent"))))
