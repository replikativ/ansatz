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
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [ansatz.export.parser :as parser]
            [ansatz.export.replay :as replay]))

(def ^:private init-env
  (delay
    (let [f "test-data/init-medium.ndjson"]
      (when (.exists (java.io.File. f))
        (:env (replay/replay (:decls (parser/parse-ndjson-file f))))))))

(defn- with-fresh-env
  "Run `f` against a private fork of init-medium, restoring the globals afterwards.
   `a/defn` mutates `a/ansatz-env`, so it must not leak into the rest of the suite."
  [f]
  (when-let [base @init-env]
    (let [saved-env @a/ansatz-env
          saved-idx @a/ansatz-instance-index
          idx (or saved-idx
                  ((requiring-resolve 'ansatz.tactic.instance/build-instance-index) base))]
      (try
        (reset! a/ansatz-env (env/fork base))
        (reset! a/ansatz-instance-index idx)
        (binding [a/*verbose* false] (f))
        (finally
          (reset! a/ansatz-env saved-env)
          (reset! a/ansatz-instance-index saved-idx))))))

(deftest quorum-intersection
  (testing "n + (n-1)/3 < 2*(2n/3 + 1) — BFT quorum intersection, via (omega)"
    (if-not @init-env
      (println "  (skipping omega-quorum-test — test-data/init-medium.ndjson not present)")
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
              "quorum-intersection must stay provable by omega alone"))))))
