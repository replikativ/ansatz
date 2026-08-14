(ns ansatz.tactic.omega-quorum-test
  "The motivating theorem, pinned.

   `quorum-intersection` is why symbolic Nat division had to work at all: a BFT quorum
   is `2n/3 + 1` and the Byzantine tolerance is `(n-1)/3`, so the safety argument is a
   linear-arithmetic fact about two floors of the SAME symbolic dividend. It is stated
   through the ordinary surface API (`a/defn` + `a/theorem`), so it exercises the whole
   path a user sees: delta-unfolding a user definition down to `Nat.div`, the
   truncated-subtraction dichotomy for `n - 1`, the division bounds for both
   quotients, and the kernel check of the resulting proof term.

   This used to be decided by two different procedures that could disagree — the
   proof-free pre-filter in `ansatz.tactic.omega` answered `:sat` here and vetoed the
   engine that could prove it. There is one engine now; this test is the guard that it
   stays that way."
  (:require [clojure.test :refer [deftest testing is]]
            [ansatz.core :as a]
            [ansatz.test-env :as test-env]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]))

(defn- with-fresh-env
  "Run `f` against a private fork of the SHIPPED Init tier, restoring the globals
   afterwards. `a/defn` mutates `a/ansatz-env`, so it must not leak into the rest of
   the suite.

   This used to read `test-data/init-medium.ndjson` and skip when it was absent — i.e.
   the motivating theorem was not actually checked anywhere a fresh clone or CI could
   see. `bundled-init-env` is on the classpath by construction, so there is nothing
   left to skip."
  [f]
  (let [base @test-env/bundled-init-env
        saved-env @a/ansatz-env
        saved-idx @a/ansatz-instance-index
        idx (or saved-idx
                ((requiring-resolve 'ansatz.tactic.instance/build-instance-index) base))]
    (try
      (reset! a/ansatz-env (env/fork base))
      (reset! a/ansatz-instance-index idx)
      (binding [a/*verbose* false] (f))
      (finally
        (reset! a/ansatz-env saved-env)
        (reset! a/ansatz-instance-index saved-idx)))))

(deftest quorum-intersection
  (testing "n + (n-1)/3 < 2*(2n/3 + 1) — BFT quorum intersection, via (omega)"
    (with-fresh-env
      (fn []
        (eval '(ansatz.core/defn quorum-size [n :- Nat] Nat
                 (+ (Nat.div (* 2 n) 3) 1)))
        (eval '(ansatz.core/defn byz-tolerance [n :- Nat] Nat
                 (Nat.div (- n 1) 3)))
        (is (some? (env/lookup (a/env) (name/from-string "quorum-size"))))
        (is (some? (env/lookup (a/env) (name/from-string "byz-tolerance"))))
        (eval '(ansatz.core/theorem quorum-intersection [n :- Nat]
                                    (< Nat (+ n (byz-tolerance n)) (* 2 (quorum-size n)))
                                    (omega)))
        (is (some? (env/lookup (a/env) (name/from-string "quorum-intersection")))
            "quorum-intersection must stay provable by omega alone")))))

(deftest quorum-from-equation
  (testing "n = 3f+1 ⊢ n + f < 2*(2f+1) — the other half of the consensus idiom"
    ;; Quorum arithmetic states its sizes as EQUATIONS (`n = 3f+1`, `q = 2f+1`) at least
    ;; as often as it states them as floors, so this shape has to work through the
    ;; surface API too. Here the equality has a ±1 coefficient and so is eliminated by
    ;; substitution; `corpus-nat-integrality` covers the non-unit-coefficient case that
    ;; forces the bmod route instead.
    (with-fresh-env
      (fn []
        (eval '(ansatz.core/theorem quorum-from-equation
                                    [f :- Nat, n :- Nat, h :- (Eq Nat n (+ (* 3 f) 1))]
                                    (< Nat (+ n f) (* 2 (+ (* 2 f) 1)))
                                    (omega)))
        (is (some? (env/lookup (a/env) (name/from-string "quorum-from-equation")))
            "an equation-stated quorum bound must be provable by omega alone")))))
