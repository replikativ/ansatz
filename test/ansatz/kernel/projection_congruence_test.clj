(ns ansatz.kernel.projection-congruence-test
  "Safety and fallback checks for the opt-in projection congruence experiment."
  (:require [clojure.test :refer [deftest is use-fixtures]]
            [ansatz.test-env :as test-env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.name :as nm]
            [ansatz.kernel.env :as env])
  (:import [ansatz.kernel TypeChecker Reducer ExprPairSet KernelAbort]))

(def ^:private enabled-property "ansatz.kernel.experiment.congruence")
(def ^:private budget-property "ansatz.kernel.experiment.congruenceBudget")
(defn- with-properties [properties f]
  (let [saved (into {} (map (fn [[k _]] [k (System/getProperty k)]) properties))]
    (try
      (doseq [[k v] properties] (System/setProperty k (str v)))
      (f)
      (finally
        (doseq [[k v] saved]
          (if v (System/setProperty k v) (System/clearProperty k)))))))
(use-fixtures :each #(with-properties {enabled-property true budget-property 4096} %))

(defn- c [n & [us]] (e/const' (nm/from-string n) (or us [])))
(def ^:private nat (c "Nat"))
(def ^:private prod-name (nm/from-string "Prod"))
(defn- pair-type [a b] (e/app* (c "Prod" [lvl/zero lvl/zero]) a b))
(defn- pair [a b x y] (e/app* (c "Prod.mk" [lvl/zero lvl/zero]) a b x y))
(defn- nat-rec [type base step n]
  (e/app* (c "Nat.rec" [(lvl/succ lvl/zero)]) (e/lam "_" nat type :default) base step n))

(defn- model-theorem [n wrong?]
  (let [fn-type (e/forall' "x" nat nat :default)
        product (pair-type fn-type nat)
        first-of #(e/proj prod-name 0 %)
        base (pair fn-type nat (e/lam "x" nat (e/bvar 0) :default) (e/lit-nat 0))
        previous (first-of (e/bvar 1))
        step (e/lam "k" nat
                    (e/lam "prev" product
                           (pair fn-type nat
                                 (e/lam "x" nat (e/app previous (e/app previous (e/bvar 0))) :default)
                                 (e/lit-nat 0)) :default) :default)
        iter #(nat-rec product base step %)
        x (e/fvar 900)
        lhs (e/app (first-of (iter (e/lit-nat n))) x)
        rhs (e/app (first-of (iter (e/app* (c "Nat.add") (e/lit-nat n) (e/lit-nat 0))))
                   (if wrong? (e/app (c "Nat.succ") x) x))
        goal (e/app* (c "Eq" [(lvl/succ lvl/zero)]) nat lhs rhs)
        proof (e/app* (c "Eq.refl" [(lvl/succ lvl/zero)]) nat lhs)]
    (env/mk-thm (nm/from-string "ProjectionCongruence.model") []
                (e/forall' "x" nat (Reducer/abstract1 goal 900) :default)
                (e/lam "x" nat (Reducer/abstract1 proof 900) :default))))

(deftest checked-projection-model
  (let [environment @test-env/checked-bundled-init-env
        ci (model-theorem 20 false)]
    (with-properties {enabled-property false}
      #(is (thrown-with-msg? KernelAbort #"fuel exhausted"
                             (TypeChecker/checkConstant environment ci 5000))))
    (is (some? (TypeChecker/checkConstant environment ci 5000)))
    (is (thrown-with-msg? RuntimeException #"does not match declared type"
                          (TypeChecker/checkConstant environment (model-theorem 3 true) 10000)))))

(defn- ignored-arguments []
  (let [child-left (e/app* (c "Nat.add") (e/lit-nat 2) (e/lit-nat 2))
        child-right (e/lit-nat 4)
        expensive (nat-rec nat (e/lit-nat 0)
                           (e/lam "k" nat (e/lam "r" nat (e/app (c "Nat.succ") (e/bvar 0)) :default) :default)
                           (e/lit-nat 10000))
        inner-type (pair-type nat nat)
        left (pair inner-type nat (pair nat nat child-left expensive) (e/lit-nat 0))
        right (pair inner-type nat (pair nat nat child-right (e/lit-nat 0)) (e/lit-nat 0))]
    {:left (e/proj prod-name 1 left) :right (e/proj prod-name 1 right)
     :child-left child-left :child-right child-right}))

(defn- success-cached? [tc a b]
  (let [field (doto (.getDeclaredField TypeChecker "success") (.setAccessible true))
        cache ^ExprPairSet (.get field tc)]
    (or (.contains cache a b) (.contains cache b a))))

(deftest bounded-fallback-discards-child-cache
  (let [{:keys [left right child-left child-right]} (ignored-arguments)
        tc (TypeChecker. @test-env/checked-bundled-init-env)]
    (.setFuel tc 10000)
    ;; Establish that the adversarial inputs themselves are well typed.
    (.check tc left)
    (.check tc right)
    (is (not (success-cached? tc child-left child-right)))
    (is (.isDefEq tc left right))
    (is (pos? (get (.getReducerStats tc) "congruence-probe-aborts")))
    ;; The probe solved this child before exhausting its budget on the next one.
    ;; Normal reduction discards both children, so their speculative equality
    ;; must not appear in the parent's positive cache (#14806).
    (is (not (success-cached? tc child-left child-right)))
    (let [probes (get (.getReducerStats tc) "congruence-probes")]
      (is (.isDefEq tc child-left child-right))
      (is (= probes (get (.getReducerStats tc) "congruence-probes"))))
    (is (success-cached? tc child-left child-right))))

(deftest global-resource-aborts-are-not-probe-fallback
  (let [{:keys [left right]} (ignored-arguments)
        environment @test-env/checked-bundled-init-env
        tc (TypeChecker. environment)]
    (.setFuel tc 50)
    (is (thrown-with-msg? KernelAbort #"fuel exhausted" (.isDefEq tc left right)))
    (let [tc (TypeChecker. environment)]
      (.setFuel tc 10000)
      (try
        (.interrupt (Thread/currentThread))
        (is (thrown-with-msg? KernelAbort #"interrupted" (.isDefEq tc left right)))
        (finally (Thread/interrupted))))))

(deftest probe-copies-reduction-mode-and-allow-list
  (let [alias-name (nm/from-string "ProjectionCongruence.alias")
        environment (TypeChecker/checkConstant
                     @test-env/checked-bundled-init-env
                     (env/mk-def alias-name [] nat (e/lit-nat 0) :hints {:regular 1}))
        fn-type (e/forall' "x" nat nat :default)
        head (e/proj prod-name 0
                     (pair fn-type nat (e/lam "x" nat (e/bvar 0) :default) (e/lit-nat 0)))
        lhs (e/app head (e/const' alias-name []))
        rhs (e/app head (e/lit-nat 0))]
    (doseq [allow? [false true]]
      (let [tc (TypeChecker. environment)
            reducer (.getReducer tc)]
        (.setTransparency reducer 0)
        (when allow? (.setDeltaAllowSet reducer (java.util.HashSet. [alias-name])))
        (is (= allow? (.isDefEq tc lhs rhs)))
        (is (= 0 (.getTransparency reducer)))))))
