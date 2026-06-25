(ns ansatz.malli-surface-test
  "The gradual dependently-typed on-ramp: malli function schemas as a/defn signatures.
   The porting story under test is a one-token diff — `defn` → `a/defn`, schemas unchanged."
  (:require [clojure.test :refer [deftest testing is]]
            [malli.core :as m]
            [ansatz.core :as a]
            [ansatz.malli]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]))

(defonce ^:private booted (delay (binding [a/*verbose* false] (a/load-init!))))

;; ordinary malli-instrumented Clojure style: schema FIRST, then the definition
(m/=> msf-add2 [:=> [:cat :int :int] :int])
(m/=> msf-len  [:=> [:cat [:sequential :int]] :int])

(deftest test-malli-schema-as-signature
  (testing "a/defn with a PLAIN param vector reads the m/=> registry: params/ret from the
            schema, body kernel-verified, runtime compiled"
    @booted
    (binding [a/*verbose* false]
      (when-not (env/lookup (a/env) (name/from-string "msf-add2"))
        ;; eval in THIS ns — the m/=> registry is namespace-keyed, like instrumentation
        (binding [*ns* (find-ns 'ansatz.malli-surface-test)]
          (eval '(ansatz.core/defn msf-add2 [x y]
                   (match x Nat Nat (zero y) (succ [k] (+ 1 (msf-add2 k y))))))))
      (is (some? (env/lookup (a/env) (name/from-string "msf-add2")))
          "schema-signed recursive function kernel-verified")
      ;; the kernel type came from the schema: ∀ (x y : Nat), Nat
      (let [ty (e/->string (.type (env/lookup (a/env) (name/from-string "msf-add2"))))]
        (is (re-find #"Nat" ty) "Nat signature from :int schema"))
      ;; and it runs
      (is (= 7 (clojure.core/long ((deref (ns-resolve 'ansatz.malli-surface-test 'msf-add2)) 3 4))) "runtime agrees")))
  (testing "collection schemas: [:sequential :int] → List Nat"
    @booted
    (binding [a/*verbose* false]
      (when-not (env/lookup (a/env) (name/from-string "msf-len"))
        (binding [*ns* (find-ns 'ansatz.malli-surface-test)]
          (eval '(ansatz.core/defn msf-len [xs]
                   (match xs (List Nat) Nat (nil 0) (cons [h t] (+ 1 (msf-len t))))))))
      (is (some? (env/lookup (a/env) (name/from-string "msf-len"))) "List-typed via schema")
      (is (= 3 (clojure.core/long ((deref (ns-resolve 'ansatz.malli-surface-test 'msf-len)) (list 1 2 3)))) "runtime agrees"))))

(m/=> msf-rec [:=> [:cat [:map [:a :int] [:b :boolean]]] :int])
(m/=> msf-ref [:=> [:cat [:int {:min 2}]] :int])

(deftest test-malli-comprehensive-shapes
  (testing "[:map …] params land as synthesized named-field records"
    @booted
    (binding [a/*verbose* false]
      (when-not (env/lookup (a/env) (name/from-string "msf-rec"))
        (binding [*ns* (find-ns 'ansatz.malli-surface-test)]
          (eval '(ansatz.core/defn msf-rec [r] 7))))
      (let [ty (e/->string (.type (env/lookup (a/env) (name/from-string "msf-rec"))))]
        (is (re-find #"MalliRec_a_b" ty) "record schema became a named record signature"))))
  (testing "[:int {:min 2}] params land as Subtype refinements"
    @booted
    (binding [a/*verbose* false]
      (when-not (env/lookup (a/env) (name/from-string "msf-ref"))
        (binding [*ns* (find-ns 'ansatz.malli-surface-test)]
          (eval '(ansatz.core/defn msf-ref [n] 7))))
      (let [ty (e/->string (.type (env/lookup (a/env) (name/from-string "msf-ref"))))]
        (is (re-find #"Subtype" ty) "bounded int became a Subtype refinement")
        (is (re-find #"LE\.le" ty) "the bound is carried as a Prop"))))
  (testing "domain-type registry: register once, reference by keyword (ansatz-side registry)"
    @booted
    ((requiring-resolve 'ansatz.malli/register-type!) :msf/age [:int {:min 0}])
    (let [t ((requiring-resolve 'ansatz.malli/schema->type-expr) :msf/age)]
      (is (re-find #"Nat" (e/->string t)) "registered :msf/age resolves through to Nat"))))

(deftest test-malli-schema-honest-errors
  (testing "a registered but untranslatable schema THROWS (no approximate lifting)"
    @booted
    (m/=> msf-bad [:=> [:cat [:or :int :string]] :int])
    (is (thrown? Exception
                 (binding [*ns* (find-ns 'ansatz.malli-surface-test)]
                   (eval '(ansatz.core/defn msf-bad [m] 0))))
        "[:or …] sum schemas are rejected (no kernel sum mapping yet)")))

(deftest test-differential-lane
  (testing "the generative differential check: compiled runtime ≡ kernel evaluation on
            schema-generated inputs (the guard for well-typed-but-source-unfaithful bugs)"
    @booted
    (binding [a/*verbose* false]
      (when-not (env/lookup (a/env) (name/from-string "msf-add2"))
        (binding [*ns* (find-ns 'ansatz.malli-surface-test)]
          (eval '(ansatz.core/defn msf-add2 [x y]
                   (match x Nat Nat (zero y) (succ [k] (+ 1 (msf-add2 k y))))))))
      (let [r ((requiring-resolve 'ansatz.malli/check-verified!)
               'ansatz.malli-surface-test 'msf-add2 :runs 15)]
        (is (= 15 (:ok r)) "15/15 generated inputs agree runtime vs kernel")))))

(m/=> msf-bump [:=> [:cat [:int {:min 1}]] :int])

(deftest test-subtype-param-ergonomics
  (testing "a refined param ([:int {:min 1}] → Subtype) is used directly as its carrier:
            body references auto-coerce to .val, the refinement erases at runtime"
    @booted
    (binding [a/*verbose* false]
      (when-not (env/lookup (a/env) (name/from-string "msf-bump"))
        (binding [*ns* (find-ns 'ansatz.malli-surface-test)]
          (eval '(ansatz.core/defn msf-bump [n] (+ n 1)))))
      (let [ci (env/lookup (a/env) (name/from-string "msf-bump"))]
        (is (some? ci) "arithmetic over the refined param verifies")
        (is (re-find #"Subtype" (e/->string (.type ci))) "the binder keeps the refinement")
        (is (= 6 (clojure.core/long ((deref (ns-resolve 'ansatz.malli-surface-test 'msf-bump)) 5)))
            "runtime takes the raw carrier value")))))

(m/=> msf-dot [:=> [:cat [:map [:x :int] [:y :int]]] :int])

(deftest test-named-field-records
  (testing "[:map [:x :int] [:y :int]] synthesizes a named-field structure: keyword access
            elaborates to kernel projections, runtime values are plain Clojure maps"
    @booted
    (binding [a/*verbose* false]
      (when-not (env/lookup (a/env) (name/from-string "msf-dot"))
        (binding [*ns* (find-ns 'ansatz.malli-surface-test)]
          (eval '(ansatz.core/defn msf-dot [p] (+ (:x p) (:y p))))))
      (let [ci (env/lookup (a/env) (name/from-string "msf-dot"))]
        (is (some? ci) "keyword access over the schema'd record param verifies")
        (is (re-find #"MalliRec_x_y" (e/->string (.type ci)))
            "the binder is the synthesized named record type")
        (is (= 5 (clojure.core/long ((deref (ns-resolve 'ansatz.malli-surface-test 'msf-dot))
                                     {:x 2 :y 3})))
            "runtime takes a plain Clojure map")))))

(deftest test-opaque-gradual-scalars
  ;; The general (total) functor: opaque scalars with no sharp native rep route to the gradual `Opaque`
  ;; carrier instead of throwing — so a realistic event record (timestamp/status/uuid) can be MODELED,
  ;; carried, and keyed (group-by/join) while precise fields keep the full optimizer algebra.
  @booted
  (binding [a/*verbose* false]
    (let [opq? (fn [t] (= "Opaque" (let [[h _] (e/get-app-fn-args t)]
                                     (and (e/const? h) (name/->string (e/const-name h))))))]
      (testing "opaque scalars -> Opaque (was: throw 'unsupported scalar schema')"
        (doseq [s [:keyword :uuid :symbol :any :some 'keyword? 'uuid? 'any?]]
          (is (opq? (ansatz.malli/schema->type-expr s)) (str s " -> Opaque"))))
      (testing "ensure-opaque! installs the axioms (idempotent)"
        (ansatz.malli/ensure-opaque!)
        (is (some? (env/lookup (a/env) (name/from-string "Opaque"))) "Opaque : Type")
        (is (some? (env/lookup (a/env) (name/from-string "instDecidableEqOpaque"))) "DecidableEq Opaque"))
      (testing "[:enum ...] maps to its members' type (string->String, int->Nat, keyword->Opaque)"
        (is (re-find #"String" (e/->string (ansatz.malli/schema->type-expr [:enum "x" "y"]))))
        (is (re-find #"Nat"    (e/->string (ansatz.malli/schema->type-expr [:enum 1 2]))))
        (is (opq? (ansatz.malli/schema->type-expr [:enum :a :b]))))
      (testing "precise scalars unchanged (still sharp native types)"
        (is (re-find #"Nat"    (e/->string (ansatz.malli/schema->type-expr [:int {:min 0}]))))
        (is (re-find #"String" (e/->string (ansatz.malli/schema->type-expr :string))))))))
