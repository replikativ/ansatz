(ns ansatz.prelude.algebra-test
  "Phase 1 of the wandler reimpl: the owned algebraic spine verifies end-to-end."
  (:require [clojure.test :refer [deftest testing is use-fixtures]]
            [ansatz.core :as a]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.expr :as e]
            [ansatz.codegen :as cg]
            [ansatz.export.parser :as parser]
            [ansatz.export.replay :as replay]
            [ansatz.prelude.algebra :as alg]))

(def ^:private init-medium-env
  (delay
    (let [f "test-data/init-medium.ndjson"]
      (when (.exists (java.io.File. f))
        (:env (replay/replay (:decls (parser/parse-ndjson-file f))))))))

(defn- with-env [t]
  (when-let [e @init-medium-env] (reset! a/ansatz-env e))
  (t))
(use-fixtures :once with-env)
(defn- ready? [] (some? @init-medium-env))
(defn- has? [s] (some? (env/lookup (a/env) (name/from-string s))))

(deftest classes-install
  (when (ready?)
    (testing "WAddMonoid ⊂ WSemiring define into the env"
      (alg/install-classes!)
      (is (has? "WAddMonoid"))
      (is (has? "WSemiring"))
      (is (has? "WSemiring.mul"))
      (is (has? "WSemiring.add") "inherited accessor (subobject)")
      (is (has? "WSemiring.toWAddMonoid") "packed parent projection"))))

(deftest nat-instance-verifies
  (when (ready?)
    (testing "the Nat WSemiring instance kernel-verifies through the subobject"
      (let [r (alg/install-instance! "Nat" alg/nat-row)]
        (is (= :verified (:status r)) (str "expected :verified, got " r))
        (is (has? "instWAddMonoid_Nat"))
        (is (has? "instWSemiring_Nat"))))))

(deftest named-instance-monomorphizes
  ;; Codegen faithful to the kernel's `reduce_proj` (whnf the major premise — delta included — before
  ;; matching the constructor): a class projection over a NAMED instance const reduces to the carrier op,
  ;; not just over an inline `{Struct}.mk` literal. This is what lets the optimizer emit instance terms by
  ;; name (one-instance-per-carrier) and still have codegen lower them.
  (when (ready?)
    (alg/install-instance! "Nat" alg/nat-row)
    (let [env  (a/env)
          natC (e/const' (name/from-string "Nat") [])
          z    (e/const' (name/from-string "Nat.zero") [])
          amN  (e/const' (name/from-string "instWAddMonoid_Nat") [])
          wsN  (e/const' (name/from-string "instWSemiring_Nat") [])
          add  (e/app* (e/const' (name/from-string "WAddMonoid.add") []) natC amN z z)
          ;; WSemiring.mul exercises the OWN field; WSemiring.add exercises the INHERITED field, which
          ;; routes through the parent instance referenced BY NAME (instWAddMonoid_Nat) — the nested chain.
          mul  (e/app* (e/const' (name/from-string "WSemiring.mul") []) natC wsN z z)
          addI (e/app* (e/const' (name/from-string "WSemiring.add") []) natC wsN z z)
          s-of #(e/->string (cg/collapse-instance-projections env %))]
      (testing "WAddMonoid.add over a named instance ⇝ Nat.add"
        (is (.contains ^String (s-of add) "Nat.add"))
        (is (not (.contains ^String (s-of add) "WAddMonoid")) "no class projection survives"))
      (testing "WSemiring.mul (own field) over a named instance ⇝ Nat.mul"
        (is (.contains ^String (s-of mul) "Nat.mul"))
        (is (not (.contains ^String (s-of mul) "WSemiring")) "no class projection survives"))
      (testing "WSemiring.add (inherited field, named-parent chain) ⇝ Nat.add"
        (is (.contains ^String (s-of addI) "Nat.add"))
        (is (not (.contains ^String (s-of addI) "WSemiring")))
        (is (not (.contains ^String (s-of addI) "WAddMonoid")))))))
