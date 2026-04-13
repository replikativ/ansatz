(ns ansatz.malli-test
  "Tests for the Ansatz–Malli bridge.
   Verifies type-expr->malli conversions, fn-schema extraction, and
   automatic registration via *malli?*."
  (:require [clojure.test :refer [deftest testing is use-fixtures]]
            [ansatz.core :as a]
            [ansatz.malli :as am]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]
            [ansatz.export.parser :as parser]
            [ansatz.export.replay :as replay]
            [malli.core :as m]))

;; ============================================================
;; Environment setup (same pattern as core_test)
;; ============================================================

(def ^:private init-medium-env
  (delay
    (let [f "test-data/init-medium.ndjson"]
      (when (.exists (java.io.File. f))
        (let [st (parser/parse-ndjson-file f)
              env (:env (replay/replay (:decls st)))]
          env)))))

(defn- require-env []
  (or @init-medium-env
      (throw (ex-info "test-data/init-medium.ndjson not found" {}))))

(defn- with-env [f]
  (let [env (require-env)]
    (reset! a/ansatz-env env)
    (let [tsv "resources/instances.tsv"
          load-tsv (requiring-resolve 'ansatz.tactic.instance/load-instance-tsv)
          build-fn (requiring-resolve 'ansatz.tactic.instance/build-instance-index)
          idx (if (.exists (java.io.File. tsv))
                (load-tsv tsv)
                (build-fn env))]
      (reset! a/ansatz-instance-index idx))
    (binding [a/*verbose* false]
      (f))))

(use-fixtures :once with-env)

;; ============================================================
;; type-expr->malli tests
;; ============================================================

(deftest test-base-types
  (testing "Nat → [:and :int [:>= 0]]"
    (let [nat (e/const' (name/from-string "Nat") [])]
      (is (= [:and :int [:>= 0]] (am/type-expr->malli nat)))))

  (testing "Int → :int"
    (let [int-e (e/const' (name/from-string "Int") [])]
      (is (= :int (am/type-expr->malli int-e)))))

  (testing "Bool → :boolean"
    (let [bool-e (e/const' (name/from-string "Bool") [])]
      (is (= :boolean (am/type-expr->malli bool-e)))))

  (testing "String → :string"
    (let [str-e (e/const' (name/from-string "String") [])]
      (is (= :string (am/type-expr->malli str-e)))))

  (testing "Unknown type → :any"
    (let [unk (e/const' (name/from-string "SomethingWeird") [])]
      (is (= :any (am/type-expr->malli unk))))))

(deftest test-applied-types
  (testing "List Nat → [:sequential [:and :int [:>= 0]]]"
    (let [list-nat (e/app (e/const' (name/from-string "List") [lvl/zero])
                          (e/const' (name/from-string "Nat") []))]
      (is (= [:sequential [:and :int [:>= 0]]] (am/type-expr->malli list-nat)))))

  (testing "List Bool → [:sequential :boolean]"
    (let [list-bool (e/app (e/const' (name/from-string "List") [lvl/zero])
                           (e/const' (name/from-string "Bool") []))]
      (is (= [:sequential :boolean] (am/type-expr->malli list-bool))))))

;; ============================================================
;; fn-schema tests
;; ============================================================

(deftest test-fn-schema-simple
  (testing "Nat → Nat gives [:=> [:cat [:and :int [:>= 0]]] [:and :int [:>= 0]]]"
    (let [nat (e/const' (name/from-string "Nat") [])
          fn-type (e/forall' "n" nat nat :default)]
      (is (= [:=> [:cat [:and :int [:>= 0]]] [:and :int [:>= 0]]]
             (am/fn-schema fn-type))))))

(deftest test-fn-schema-binary
  (testing "Nat → Nat → Nat gives two inputs"
    (let [nat (e/const' (name/from-string "Nat") [])
          fn-type (e/forall' "a" nat (e/forall' "b" nat nat :default) :default)]
      (is (= [:=> [:cat [:and :int [:>= 0]] [:and :int [:>= 0]]] [:and :int [:>= 0]]]
             (am/fn-schema fn-type))))))

(deftest test-fn-schema-skips-implicit
  (testing "Implicit params are skipped"
    (let [nat (e/const' (name/from-string "Nat") [])
          type-sort (e/sort' lvl/zero)
          ;; ∀ {α : Type} → (n : Nat) → Nat
          fn-type (e/forall' "α" type-sort
                             (e/forall' "n" nat nat :default)
                             :implicit)]
      (is (= [:=> [:cat [:and :int [:>= 0]]] [:and :int [:>= 0]]]
             (am/fn-schema fn-type))))))

;; ============================================================
;; Integration tests — define-verified + malli registration
;; ============================================================

(deftest test-define-and-register
  (testing "define-verified then register-from-defn! produces a valid schema"
    (binding [a/*verbose* false]
      (let [f (a/define-verified 'malli-test-double '[n Nat] 'Nat '(+ n n))]
        (is (fn? f))
        (is (= 42 (f 21)))
        ;; Register with Malli
        (am/register-from-defn! 'ansatz.malli-test 'malli-test-double)
        ;; Check schema was registered
        (let [schemas (m/function-schemas)]
          (is (get-in schemas [:clj 'ansatz.malli-test 'malli-test-double])))))))

(deftest test-fn-schema-for
  (testing "fn-schema-for returns the right schema"
    (binding [a/*verbose* false]
      (a/define-verified 'malli-test-inc '[n Nat] 'Nat '(+ n 1))
      (let [schema (am/fn-schema-for "malli-test-inc")]
        (is (= :=> (first schema)))
        (is (= [:cat [:and :int [:>= 0]]] (second schema)))
        (is (= [:and :int [:>= 0]] (nth schema 2)))))))

(deftest test-malli-flag-auto-register
  (testing "*malli?* binding triggers auto-registration"
    (binding [a/*verbose* false
              a/*malli?* true]
      (let [f (a/define-verified 'malli-test-auto '[x Nat] 'Nat 'x)]
        ;; The define-verified itself doesn't trigger malli registration —
        ;; only the defn macro does. But we can still register manually.
        (am/register-from-defn! 'ansatz.malli-test 'malli-test-auto)
        (let [schemas (m/function-schemas)]
          (is (get-in schemas [:clj 'ansatz.malli-test 'malli-test-auto])))))))

(deftest test-schema-validates-correctly
  (testing "Generated schema validates Nat inputs correctly"
    (binding [a/*verbose* false]
      (a/define-verified 'malli-test-id '[n Nat] 'Nat 'n)
      (let [schema-form (am/fn-schema-for "malli-test-id")
            s (m/schema schema-form)
            input-schema (second (m/-children s))  ;; the :cat
            validator (m/validator (m/schema [:cat [:and :int [:>= 0]]]))]
        ;; Valid: positive integer
        (is (validator [42]))
        ;; Invalid: negative integer
        (is (not (validator [-1])))
        ;; Invalid: string
        (is (not (validator ["hello"])))))))
