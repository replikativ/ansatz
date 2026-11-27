(ns ansatz.deriving-test
  "Tests for the deriving framework — DecidableEq for simple enums."
  (:require [ansatz.test-env :as test-env]
            [clojure.test :refer [deftest testing is use-fixtures]]
            [ansatz.core :as a]
            [ansatz.deriving :as deriving]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.tc :as tc]
            [ansatz.tactic.instance :as instance]))

;; ============================================================
;; Environment setup (same pattern as core_test)
;; ============================================================

(def ^:private init-medium-env test-env/checked-bundled-init-env)

(defn- require-env []
  (or @init-medium-env
      (throw (ex-info "bundled Init unavailable" {}))))

(defn- with-env [f]
  (let [env (require-env)]
    (reset! a/ansatz-env env)
    (let [idx (env/get-extension env :instances nil)]
      ;; the registry rides on the env (Lean's instance table is part of the environment)
      (swap! a/ansatz-env (fn [e] (env/with-extension e :instances idx)))
      (reset! a/ansatz-instance-index idx))
    (binding [a/*verbose* false]
      (f))))

(clojure.test/use-fixtures :once with-env)

;; ============================================================
;; Direct API tests — derive-decidable-eq!
;; ============================================================

(deftest test-derive-decidable-eq-color
  (testing "Derive DecidableEq for 3-constructor enum"
    (binding [a/*verbose* false]
      ;; Define Color inductive
      (a/inductive DColor [] (red) (green) (blue))

      ;; Derive DecidableEq programmatically
      (let [env @a/ansatz-env
            env' (deriving/derive-decidable-eq!
                  env "DColor"
                  [["red" []] ["green" []] ["blue" []]])]
        (reset! a/ansatz-env env')

        ;; Verify the instance exists in the env
        (is (some? (env/lookup env' (name/from-string "instDecidableEqDColor")))
            "instDecidableEqDColor should be in the environment")))))

(deftest test-derive-decidable-eq-5-ctors
  (testing "Derive DecidableEq for 5-constructor enum (integrant scale)"
    (binding [a/*verbose* false]
      (a/inductive DState5 [] (s1) (s2) (s3) (s4) (s5))

      (let [env @a/ansatz-env
            env' (deriving/derive-decidable-eq!
                  env "DState5"
                  [["s1" []] ["s2" []] ["s3" []] ["s4" []] ["s5" []]])]
        (reset! a/ansatz-env env')

        (is (some? (env/lookup env' (name/from-string "instDecidableEqDState5")))
            "instDecidableEqDState5 should be in the environment")))))

;; ============================================================
;; Macro integration — :deriving [DecidableEq]
;; ============================================================

(deftest test-inductive-deriving-macro
  (testing ":deriving [DecidableEq] on a/inductive"
    (binding [a/*verbose* false]
      (a/inductive DDirection [] (north) (south) (east) (west)
                   :deriving [DecidableEq])

      (is (some? (env/lookup @a/ansatz-env
                             (name/from-string "instDecidableEqDDirection")))
          "instDecidableEqDDirection should exist after :deriving"))))

;; ============================================================
;; decide tactic tests — prove equality/inequality using derived instance
;; ============================================================

(deftest test-decide-equality
  (testing "decide closes equality goal on derived type"
    (binding [a/*verbose* false]
      ;; Fresh type to avoid conflicts
      (a/inductive DEqTest [] (alpha) (beta) (gamma)
                   :deriving [DecidableEq])

      ;; Prove alpha = alpha using decide
      (is (nil? (a/theorem deq-test-eq []
                           (= DEqTest (DEqTest.alpha) (DEqTest.alpha))
                           (decide)))
          "decide should close alpha = alpha"))))

(deftest test-decide-inequality
  (testing "decide closes inequality goal on derived type"
    (binding [a/*verbose* false]
      (a/inductive DNeqTest [] (x1) (x2) (x3)
                   :deriving [DecidableEq])

      ;; Prove Not (x1 = x2) using decide
      (is (nil? (a/theorem dneq-test []
                           (Not (= DNeqTest (DNeqTest.x1) (DNeqTest.x2)))
                           (decide)))
          "decide should close Not (x1 = x2)"))))

;; Lean parity: test/lean-parity/dsl/deriving_names.lean (Lean v4.36.0)
(deftest deriving-names-and-parameters
  (binding [*ns* (the-ns 'ansatz.deriving-test) a/*verbose* false]
    (eval '(ansatz.core/inductive DerN.Color [] (red) (green) (blue) :deriving [DecidableEq]))
    (eval '(ansatz.core/inductive DerP [α Type] (a) (b) :deriving [DecidableEq])))
  (let [env (a/env)
        lookup #(env/lookup env (name/from-string %))
        c #(e/const' (name/from-string %) [])
        st (tc/mk-tc-state env)]
    (testing "the instance lives in the type's namespace"
      (is (some? (lookup "DerN.instDecidableEqColor")))
      (is (nil? (lookup "instDecidableEqDerN.Color"))))
    (testing "an enum gets ofNat (a bif chain over Nat.ble) and ofNat_ctorIdx"
      (is (tc/is-def-eq st (e/app (c "DerN.Color.ofNat") (e/lit-nat 1)) (c "DerN.Color.green")))
      (is (tc/is-def-eq st (e/app (c "DerN.Color.ofNat") (e/lit-nat 7)) (c "DerN.Color.blue")))
      (is (.isThm (lookup "DerN.Color.ofNat_ctorIdx")))
      (is (env/verifies? env (.type (lookup "DerN.Color.ofNat_ctorIdx")) (.value (lookup "DerN.Color.ofNat_ctorIdx")))))
    (testing "a parameterized fieldless type derives at its applied parameter, with [DecidableEq α]"
      (let [t (.type (lookup "instDecidableEqDerP"))]
        (is (= [:implicit :inst-implicit] [(e/forall-info t) (e/forall-info (e/forall-body t))]))
        (is (re-find #"instDecidableEqDerP"
                     (e/->string (instance/synthesize env (instance/index-for env)
                                                      (e/app (e/const' (name/from-string "DecidableEq") [(ansatz.kernel.level/succ ansatz.kernel.level/zero)])
                                                             (e/app (c "DerP") (c "Nat")))))))
        (is (nil? (lookup "DerP.ofNat")) "ofNat is for enumerations only")))
    (testing "decide evaluates through the derived instances"
      (binding [*ns* (the-ns 'ansatz.deriving-test) a/*verbose* false]
        (eval '(ansatz.core/theorem der-color-ne [] (= Bool (Decidable.decide (= DerN.Color DerN.Color.red DerN.Color.blue)) false) (rfl)))
        (eval '(ansatz.core/theorem der-p-ne [] (= Bool (Decidable.decide (= (DerP Nat) DerP.a DerP.b)) false) (rfl))))
      (is (some? (env/lookup (a/env) (name/from-string "der-color-ne"))))
      (is (some? (env/lookup (a/env) (name/from-string "der-p-ne")))))))

(deftest deriving-review-cases
  (binding [*ns* (the-ns 'ansatz.deriving-test) a/*verbose* false]
    (eval '(ansatz.core/inductive DerFour [] (a) (b) (c) (d) :deriving [DecidableEq]))
    (eval '(ansatz.core/inductive DerEmpty [] :deriving [DecidableEq]))
    (eval '(ansatz.core/inductive DerLow.color [] (x) (y) :deriving [DecidableEq]))
    (eval '(ansatz.core/inductive DerQ [α (Type u)] (a) (b) :deriving [DecidableEq])))
  (let [env (a/env)
        lookup #(env/lookup env (name/from-string %))
        c #(e/const' (name/from-string %) [])
        st (tc/mk-tc-state env)]
    (testing "ofNat is Lean's balanced lookup tree (four constructors: n.ble 1 first)"
      (let [l1 (ansatz.kernel.level/succ ansatz.kernel.level/zero)
            t (c "DerFour")
            bif (fn [i x y] (e/app* (e/const' (name/from-string "cond") [l1]) t
                                    (e/app* (c "Nat.ble") (e/bvar 0) (e/lit-nat i)) x y))]
        (is (= (e/lam-body (.value (lookup "DerFour.ofNat")))
               (bif 1 (bif 0 (c "DerFour.a") (c "DerFour.b")) (bif 2 (c "DerFour.c") (c "DerFour.d"))))
            "bif n.ble 1 then (bif n.ble 0 then a else b) else (bif n.ble 2 then c else d)"))
      (is (= :abbrev (let [h (.getHints (lookup "DerFour.ofNat"))] (if (= h ansatz.kernel.ConstantInfo/HINTS_ABBREV) :abbrev h)))))
    (testing "ofNat_ctorIdx states ∀ x, T.ofNat (T.ctorIdx x) = x"
      (is (tc/is-def-eq st (.type (lookup "DerFour.ofNat_ctorIdx"))
                        (ansatz.surface.elaborate/elaborate
                         env '(forall [x :- DerFour] (= DerFour (DerFour.ofNat (DerFour.ctorIdx x)) x))))))
    (testing "an empty type derives DecidableEq but is not an enumeration"
      (is (some? (lookup "instDecidableEqDerEmpty")))
      (is (nil? (lookup "DerEmpty.ofNat")))
      (is (nil? (lookup "DerEmpty.ofNat_ctorIdx"))))
    (testing "the type's last component is capitalized in the instance name"
      (is (some? (lookup "DerLow.instDecidableEqColor"))))
    (testing "a universe-polymorphic family keeps the type's universe parameter"
      (let [ci (lookup "instDecidableEqDerQ")]
        (is (= 1 (count (.levelParams ci))))
        (is (re-find #"instDecidableEqDerQ"
                     (e/->string (instance/synthesize env (instance/index-for env)
                                                      (e/app (e/const' (name/from-string "DecidableEq") [(ansatz.kernel.level/succ ansatz.kernel.level/zero)])
                                                             (e/app (e/const' (name/from-string "DerQ") [ansatz.kernel.level/zero]) (c "Nat")))))))))))

(deftest an-occupied-instance-name-gets-a-suffix
  (let [before @a/ansatz-env]
    (try
      (reset! a/ansatz-env (env/check-constant (a/env) (env/mk-axiom (name/from-string "instDecidableEqDerOcc") []
                                                                     (e/const' (name/from-string "True") []))))
      (binding [*ns* (the-ns 'ansatz.deriving-test) a/*verbose* false]
        (eval '(ansatz.core/inductive DerOcc [] (p) (q) :deriving [DecidableEq])))
      (is (some? (env/lookup (a/env) (name/from-string "instDecidableEqDerOcc_1"))))
      (finally (reset! a/ansatz-env before)))))
