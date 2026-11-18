(ns ansatz.surface.binop-coercion-test
  "Lean's binop%/binrel% (Elab/Extra.lean): the max type of an arithmetic tree starts from the
   expected type and takes the maximum of the leaf types over the coercion order; Nat leaves
   in an Int tree are coerced, `↑n = @Nat.cast Int instNatCastInt n`. Ansatz implements the
   Nat < Int part of the order."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [ansatz.core :as a]
            [ansatz.fixtures :as fixtures]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]))

(defn- init-once [f]
  (binding [a/*verbose* false] (a/load-init!) (f)))

(use-fixtures :once fixtures/isolated-session init-once)

(defn- define! [form]
  (binding [*ns* (the-ns 'ansatz.surface.binop-coercion-test) a/*verbose* false]
    (eval form)))

(defn- run [sym & args]
  (apply (ns-resolve 'ansatz.surface.binop-coercion-test sym) args))

(defn- body-string [nm]
  (e/->string (.value ^ansatz.kernel.ConstantInfo (env/lookup (a/env) (name/from-string nm)))))

(deftest the-declared-type-is-the-expected-type
  (testing "def f (n : Nat) : Int := n - 1 is ↑n - 1 at Int, as in Lean"
    (define! '(ansatz.core/defn ^Int bc-pred [^Nat n] (- n 1)))
    (let [s (body-string "bc-pred")]
      (is (re-find #"HSub\.hSub\.\{0, 0, 0\} Int Int Int" s))
      (is (re-find #"Nat\.cast\.\{0\} Int instNatCastInt" s)))
    (is (= [-1 4] [(run 'bc-pred 0) (run 'bc-pred 5)])))
  (testing "a Nat-valued subterm in an Int body: Int subtraction, so no Nat obligation"
    (define! '(ansatz.core/defn ^Int bc-len [^{:- (List Nat)} xs] (- (List.length xs) 1)))
    (is (= [-1 1] [(run 'bc-len []) (run 'bc-len [1 2])])))
  (testing "through let, if and macroexpansion"
    (define! '(ansatz.core/defn ^Int bc-let [^Nat n] (let [m (+ n 1)] (- m 5))))
    (is (= -3 (run 'bc-let 1)))
    (define! '(ansatz.core/defn ^Int bc-if [^Bool p ^Nat n] (if p (- n 1) 0)))
    (is (= -1 (run 'bc-if true 0)))))

(deftest a-nat-leaf-meets-an-int-leaf
  (define! '(ansatz.core/defn ^Int bc-mix [^Nat n ^Int i] (+ n i)))
  (is (= -3 (run 'bc-mix 2 -5)))
  (testing "argument position: the parameter type is the expected type"
    (define! '(ansatz.core/defn ^Int bc-id [^Int i] i))
    (define! '(ansatz.core/defn ^Int bc-arg [^Nat n] (bc-id (- n 1))))
    (is (= -1 (run 'bc-arg 0)))))

(deftest relations-analyse-both-operands
  (define! '(ansatz.core/defn ^Bool bc-lt [^Nat n ^Int i] (< n i)))
  (is (= [false true] [(run 'bc-lt 2 -5) (run 'bc-lt 2 5)]))
  (define! '(ansatz.core/defn ^Int bc-max [^Nat n ^Int i] (if (< n i) i 0)))
  (is (= [0 5] [(run 'bc-max 2 -5) (run 'bc-max 2 5)]))
  (testing "in a proposition, (<= 0 (+ n i)) is at Int with n coerced"
    (define! '(ansatz.core/theorem bc-prop [n :- Nat, i :- Int, h :- (= i 3)] (<= 0 (+ n i)) (omega)))
    (is (some? (env/lookup (a/env) (name/from-string "bc-prop"))))))

(deftest nat-trees-are-unchanged
  (define! '(ansatz.core/defn ^Nat bc-nat [^Nat a ^Nat b] (+ a (* 2 b))))
  (is (re-find #"HAdd\.hAdd\.\{0, 0, 0\} Nat Nat Nat" (body-string "bc-nat")))
  (is (not (re-find #"Nat\.cast" (body-string "bc-nat")))))
