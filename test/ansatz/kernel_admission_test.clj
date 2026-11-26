(ns ansatz.kernel-admission-test
  "Declaration admission follows Lean's environment.cpp and quot.cpp: a definition, theorem or
   opaque needs a value; declarations are closed and free of metavariables; a name is declared
   once; an unsafe definition may refer to itself; theorems and opaques are checked as safe; and
   a quotient primitive is admitted only as exactly what add_quot generates, with reduction
   enabled once all four are present."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [ansatz.core :as a]
            [ansatz.fixtures :as fixtures]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.name :as name])
  (:import [ansatz.kernel ConstantInfo Env Expr Level TypeChecker]))

(defn- setup [f]
  (binding [a/*verbose* false]
    (a/load-init!)
    (f)))

(use-fixtures :once fixtures/isolated-session setup)

(defn- n [s] (name/from-string s))
(defn- c [s & ls] (e/const' (n s) (vec ls)))
(def ^:private nat (c "Nat"))
(def ^:private false-ty (c "False"))

(defn- refused? [re ci]
  (try (env/check-constant (a/env) ci) false
       (catch Exception ex (boolean (re-find re (str (ex-message ex)))))))

(deftest a-value-is-required
  (doseq [ci [(env/mk-thm (n "adm-no-proof") [] false-ty nil)
              (env/mk-def (n "adm-no-body") [] nat nil)
              (env/mk-opaque (n "adm-no-opaque-body") [] nat nil)]]
    (is (refused? #"has no value" ci) (str (.name ^ConstantInfo ci)))))

(deftest declarations-are-closed
  (testing "a free variable, here as a let's own value, is refused before anything is checked"
    (let [self (Expr/fvar (bit-shift-left 1 62))
          v (e/let' (n "x") false-ty self (e/bvar 0))]
      (is (refused? #"has free variables" (env/mk-def (n "adm-fvar") [] false-ty v)))))
  (testing "a universe metavariable in a header is refused"
    (is (refused? #"has metavariables"
                  (env/mk-axiom (n "adm-level-mvar") [] (e/sort' (Level/mvar 7)))))))

(deftest a-name-is-declared-once
  (is (refused? #"Constant already declared" (env/mk-axiom (n "Nat.add") [] nat))))

(deftest safety-follows-lean
  (let [env0 (env/check-constant (a/env) (env/mk-axiom (n "adm-unsafe-ax") [] nat :unsafe? true))]
    (testing "an unsafe definition may refer to itself (checked after it is added)"
      (is (some? (env/check-constant env0 (env/mk-def (n "adm-loop") [] nat (c "adm-loop") :safety :unsafe)))))
    (testing "an opaque is checked as safe, even when it is unsafe itself"
      (is (thrown-with-msg? Exception #"unsafe"
                            (env/check-constant env0 (env/mk-opaque (n "adm-opaque") [] nat (c "adm-unsafe-ax")
                                                                    :unsafe? true)))))))

(defn- quot-free-env
  "An Env holding only what the quotient bootstrap needs: Eq and Eq.refl."
  []
  (reduce (fn [^Env acc nm] (.addConstant acc (env/lookup! (a/env) (n nm))))
          (Env.) ["Eq" "Eq.refl"]))

(deftest quotient-primitives-are-what-add-quot-generates
  (let [prims (mapv #(env/lookup! (a/env) (n %)) ["Quot" "Quot.mk" "Quot.lift" "Quot.ind"])]
    (testing "the four canonical primitives are admitted; reduction is on only after the fourth"
      (let [envs (reductions (fn [^Env acc ci] (TypeChecker/checkConstant acc ci)) (quot-free-env) prims)]
        (is (= [false false false false true] (mapv #(.isQuotEnabled ^Env %) envs)))))
    (testing "a quotient-tagged declaration of another name is refused, on every entry point"
      (let [bogus (ConstantInfo/mkQuot (n "BogusQuot") (object-array []) false-ty (keyword "type"))]
        (is (thrown-with-msg? Exception #"not a canonical quotient primitive"
                              (TypeChecker/checkConstant (quot-free-env) bogus)))
        (is (thrown-with-msg? Exception #"not a canonical quotient primitive"
                              (TypeChecker/checkConstantFuel (quot-free-env) bogus 1000)))))
    (testing "a type that is only definitionally equal to the generated one is refused"
      (let [^ConstantInfo q (first prims)
            wrapped (e/let' (n "z") nat (e/lit-nat 0) (.type q))
            q' (ConstantInfo/mkQuot (.name q) (.levelParams q) wrapped (.quotKind q))]
        (is (thrown-with-msg? Exception #"not the one the kernel generates"
                              (TypeChecker/checkConstant (quot-free-env) q')))))
    (testing "a primitive with the wrong kind is refused"
      (let [^ConstantInfo q (first prims)
            q' (ConstantInfo/mkQuot (.name q) (.levelParams q) (.type q) (keyword "lift"))]
        (is (thrown-with-msg? Exception #"of its kind"
                              (TypeChecker/checkConstant (quot-free-env) q')))))))

(deftest a-quotient-primitive-only-mentions-admitted-primitives
  (let [[quot mk] (mapv #(env/lookup! (a/env) (n %)) ["Quot" "Quot.mk"])]
    (testing "an ordinary Quot (here an axiom of the same type) cannot stand in for the quotient type under the genuine Quot.mk"
      (let [fake (env/mk-axiom (n "Quot") [(n "u")] (.type ^ConstantInfo quot))
            env' (TypeChecker/checkConstant (quot-free-env) fake)]
        (is (thrown-with-msg? Exception #"refers to Quot, which is not an admitted quotient primitive"
                              (TypeChecker/checkConstant env' mk)))))
    (testing "the genuine Quot.mk is admitted after the genuine Quot"
      (is (some? (TypeChecker/checkConstant (TypeChecker/checkConstant (quot-free-env) quot) mk))))))

(deftest quotient-reduction-needs-the-four-primitives
  (let [prims (mapv #(env/lookup! (a/env) (n %)) ["Quot" "Quot.mk" "Quot.lift" "Quot.ind"])
        [quot _ lift ind] prims
        fake-mk (env/mk-axiom (n "Quot.mk") [] (e/sort' lvl/zero))]
    (testing "an ordinary declaration in the Quot.mk slot: Quot.ind (which mentions it) is refused"
      (let [env' (reduce (fn [^Env acc ci] (TypeChecker/checkConstant acc ci))
                         (quot-free-env) [quot fake-mk lift])]
        (is (thrown-with-msg? Exception #"refers to Quot.mk"
                              (TypeChecker/checkConstant env' ind)))
        (is (not (.isQuotEnabled ^Env env')))))
    (testing "the package is judged by its declarations, not by the flag that says it is loaded"
      (let [loaded (fn [cis] (.enableQuot ^Env (reduce (fn [^Env acc ci] (.addConstant acc ci)) (quot-free-env) cis)))]
        (is (.isQuotEnabled ^Env (loaded prims)))
        (is (not (.isQuotEnabled ^Env (loaded [quot fake-mk lift ind]))))
        (is (not (.isQuotEnabled ^Env (loaded [quot lift ind]))))))
    (testing "in a staged view quotients are initialized only once all four are visible"
      (let [staged (fn [hidden]
                     (.withExternalLookupFiltered (.enableQuot (Env.))
                                                  (fn [nm] (env/lookup (a/env) nm)) 1000000
                                                  (fn [nm] (not (contains? hidden nm)))))]
        (is (not (.isQuotEnabled ^Env (staged #{(n "Quot.ind")}))))
        (is (.isQuotEnabled ^Env (staged #{})))))))

(deftest one-fuel-budget-for-header-and-body
  (let [env0 (env/check-constant (a/env) (env/mk-axiom (n "adm-fuel-ax") [] nat :unsafe? true))
        ;; a header that needs reduction: (fun x => x) Nat
        ty (e/app (e/lam-default (n "x") (e/sort' (lvl/succ lvl/zero)) (e/bvar 0)) nat)
        header (TypeChecker/checkConstantFuel env0 (env/mk-axiom (n "adm-fuel-h") [] ty :unsafe? true) 1000000000)
        d (env/mk-def (n "adm-fuel-d") [] ty (e/app (e/lam-default (n "y") nat (e/bvar 0)) (c "adm-fuel-ax"))
                      :safety :unsafe)
        total (TypeChecker/checkConstantFuel env0 d 1000000000)]
    (is (pos? header))
    (testing "usage covers both phases"
      (is (> total header)))
    (testing "a header that spends the whole budget leaves the body none (not an unlimited budget)"
      (is (thrown-with-msg? Exception #"fuel exhausted" (TypeChecker/checkConstantFuel env0 d header))))
    (is (= total (TypeChecker/checkConstantFuel env0 d total)))))
