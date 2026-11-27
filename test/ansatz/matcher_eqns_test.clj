(ns ansatz.matcher-eqns-test
  "Matcher equations keep the matcher's binders, and congruence equations (Lean
   Meta/Match/MatchEqs.lean). Lean parity: test/lean-parity/dsl/matcher_eqns.lean."
  (:require [clojure.test :refer [deftest testing is use-fixtures]]
            [ansatz.test-env :as test-env]
            [ansatz.fixtures :as fixtures]
            [ansatz.core :as a]
            [ansatz.config :as config]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.tactic.match-eqns :as match-eqns]))

(defn- with-env [f]
  (reset! a/ansatz-env @test-env/bundled-init-env)
  (binding [a/*verbose* false config/*lean-matchers* true *ns* (the-ns 'ansatz.matcher-eqns-test)]
    (eval '(ansatz.core/inductive MeT [] (a [n Nat]) (b)))
    (eval '(ansatz.core/defn me-f [t :- MeT] Nat (match t (a n) n _ 0)))
    (eval '(ansatz.core/defn me-b [b :- Bool] Nat (match b (Bool.true) 1 (Bool.false) 0)))
    (f)))

(use-fixtures :once fixtures/isolated-session with-env)

(defn- ci [n] (env/lookup (a/env) (name/from-string n)))
(defn- binders [t] (loop [t t acc []] (if (e/forall? t) (recur (e/forall-body t) (conj acc [(str (e/forall-name t)) (e/forall-info t)])) acc)))

(defn- matcher [] (str "me-f.match_1"))

(defn- checks? [n]
  (let [c (ci n)]
    (some? (try (env/check-constant (a/env) (env/mk-thm (name/from-string (str n "_chk")) (vec (.levelParams c))
                                                        (.type c) (.value c)))
                (catch Exception _ nil)))))

(deftest equations-keep-the-matchers-binders
  (let [{:keys [eqn-names]} (match-eqns/get-equations-for (matcher))
        eq1 (ci (first eqn-names))]
    (testing "motive, the pattern variable, the alternatives h_1 h_2 (Lean's names)"
      (is (= ["motive" "n" "h_1" "h_2"] (mapv first (binders (.type eq1))))))
    (is (checks? (first eqn-names)))))

(deftest congruence-equations
  (let [{:keys [congr-eqn-names]} (match-eqns/get-equations-for (matcher))]
    (is (= ["me-f.match_1.congr_eq_1" "me-f.match_1.congr_eq_2"] congr-eqn-names))
    (doseq [n congr-eqn-names]
      (is (checks? n) n))
    (testing "congr_eq_1 : ∀ motive x h_1 h_2 n, x = MeT.a n → HEq (match x …) (h_1 n)"
      (let [t (.type (ci "me-f.match_1.congr_eq_1"))
            bs (binders t)
            concl (loop [t t] (if (e/forall? t) (recur (e/forall-body t)) t))]
        (is (= (conj (subvec (binders (.type (ci (matcher)))) 0 4) ["n" :default]) (vec (take 5 bs)))
            "the matcher's own binders (motive, discriminant, h_1, h_2), then the pattern variable")
        (is (= 6 (count bs)) "the discriminant equation")
        (is (= "HEq" (str (e/const-name (e/get-app-fn concl)))))))
    (testing "congr_eq_2 carries the precedence hypothesis"
      (is (= 7 (count (binders (.type (ci "me-f.match_1.congr_eq_2")))))))))

(deftest nullary-arms-get-congruence-equations
  (let [m "me-b.match_1"
        {:keys [congr-eqn-names]} (match-eqns/get-equations-for m)]
    (is (= [(str m ".congr_eq_1") (str m ".congr_eq_2")] congr-eqn-names))
    (doseq [n congr-eqn-names] (is (checks? n) n))
    (testing "no field binder; the alternative is applied to Unit.unit"
      (let [t (.type (ci (str m ".congr_eq_1")))
            concl (loop [t t] (if (e/forall? t) (recur (e/forall-body t)) t))
            rhs (last (e/get-app-args concl))]
        (is (= ["Unit.unit"] (mapv #(str (e/const-name %)) (e/get-app-args rhs))))))))
