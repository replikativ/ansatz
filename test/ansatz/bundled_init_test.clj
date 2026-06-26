(ns ansatz.bundled-init-test
  "Zero-setup usability: `(a/init!)` with NO arguments loads the bundled medium Init tier
   (~2997 Lean `Init` declarations) straight from the jar/classpath resource — no durable
   store to build — and that's enough for ordinary verified `defn` over Nat/List/Bool. This
   is what makes ansatz usable the moment you add the dependency. Fixture-free (the tier
   ships in the jar), so it belongs in the default CI unit suite."
  (:require [clojure.test :refer [deftest is testing]]
            [ansatz.core :as a]))

(deftest bundled-medium-init-is-usable
  (binding [a/*verbose* false]
    (testing "(init!) loads the bundled medium tier from the classpath"
      (is (= :medium (a/init!)))
      (is (<= 2900 (.size ^ansatz.kernel.Env @a/ansatz-env))
          "≈2997 Init declarations admitted (TRUST mode)"))
    (testing "an ordinary verified function over the bundled tier elaborates, certifies, and runs"
      (eval '(ansatz.core/defn ^{:- Nat} bundled-dbl [^{:- Nat} x] (Nat.add x x)))
      (is (= 42 (long ((resolve 'bundled-dbl) 21)))))))
