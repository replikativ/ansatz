(ns ansatz.malli-surface-test
  "The gradual dependently-typed on-ramp: malli function schemas as a/defn signatures.
   The porting story under test is a one-token diff — `defn` → `a/defn`, schemas unchanged."
  (:require [clojure.test :refer [deftest testing is]]
            [malli.core :as m]
            [ansatz.core :as a]
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

(deftest test-malli-schema-honest-errors
  (testing "a registered but untranslatable schema THROWS (no approximate lifting)"
    @booted
    (m/=> msf-bad [:=> [:cat [:map [:a :int]]] :int])
    (is (thrown? Exception
                 (binding [*ns* (find-ns 'ansatz.malli-surface-test)]
                   (eval '(ansatz.core/defn msf-bad [m] 0))))
        "[:map …] schemas are rejected until record translation lands")))
