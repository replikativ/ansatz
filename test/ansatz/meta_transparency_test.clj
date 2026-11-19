(ns ansatz.meta-transparency-test
  "Closed comparisons at a restricted transparency (Lean's isDefEq under withReducible) never
   unfold a semireducible definition, and simp's own comparisons and reductions run at that
   transparency. Before, a metavariable-free comparison always went to the kernel's unrestricted
   defeq, so simp's matching unfolded any definition: comparing the two branches of an `if` for
   the equal-branches check of an `if` reduced `↑k ≤ 9223372036854775807` down to `Nat.sub` on
   the literal, one step per unit, and overflowed the stack (found on the recursive models of
   ansatz.clj-model, whose overflow checks are such bounds)."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [ansatz.core :as a]
            [ansatz.fixtures :as fixtures]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.tc :as tc]
            [ansatz.meta :as meta]))

(defn- setup [f]
  (binding [a/*verbose* false]
    (a/load-init!)
    (a/defn mt-in-range [i :- Int] Bool (<= i 9223372036854775807))
    (a/defn mt-succ [n :- Nat] Nat (+ n 1))
    (f)))

(use-fixtures :once fixtures/isolated-session setup)

(defn- c [s] (e/const' (name/from-string s) []))
(defn- nat [n] (e/app* (e/const' (name/from-string "OfNat.ofNat") [ansatz.kernel.level/zero]) (c "Nat") (e/lit-nat n)
                       (e/app (c "instOfNatNat") (e/lit-nat n))))

(defn- defeq-at [mode x y]
  (some? (binding [meta/*transparency* mode]
           (meta/is-def-eq meta/empty-context (tc/mk-tc-state (a/env)) x y))))

(deftest closed-comparison-respects-transparency
  (let [lhs (e/app (c "mt-succ") (nat 1))]
    (testing "default transparency unfolds a definition"
      (is (defeq-at :default lhs (nat 2))))
    (testing "reducible transparency does not unfold a semireducible definition"
      (is (not (defeq-at :reducible lhs (nat 2))))
      (is (not (defeq-at :instances lhs (nat 2)))))
    (testing "but compares instances, as Lean's implicit arguments at `.implicit` do"
      ;; @HAdd.hAdd Nat Nat Nat (instHAdd Nat instAddNat) 1 1  =?=  Nat.add 1 1
      (let [hadd (e/app* (e/const' (name/from-string "HAdd.hAdd") [ansatz.kernel.level/zero ansatz.kernel.level/zero ansatz.kernel.level/zero])
                         (c "Nat") (c "Nat") (c "Nat")
                         (e/app* (e/const' (name/from-string "instHAdd") [ansatz.kernel.level/zero]) (c "Nat") (c "instAddNat"))
                         (nat 1) (nat 1))]
        (is (defeq-at :reducible hadd (e/app* (c "Nat.add") (nat 1) (nat 1))))))
    (testing "Nat offsets need no unfolding (Lean's isDefEqOffsetNat)"
      (is (defeq-at :reducible (e/app (c "Nat.succ") (nat 4)) (nat 5))))))

(defn- run-simp
  "Prove `prop` over `params` with `tactics` on a 4 MB stack; :proved, or the exception's class."
  [params prop tactics]
  (let [p (promise)
        t (Thread. nil (bound-fn []
                         (deliver p (try (binding [a/*verbose* false]
                                           (a/prove-theorem (gensym "mt-fact") params prop tactics))
                                         :proved
                                         (catch Throwable x (class x)))))
                   "mt-simp" (long (* 4 1024 1024)))]
    (.start t)
    (deref p 120000 :timeout)))

(deftest simp-does-not-unfold-when-comparing
  (testing "simp's equal-branches check on `if k = 0 then mt-in-range ↑(k + 1) else mt-in-range ↑k`"
    ;; with the kernel's unrestricted defeq this overflowed a 4 MB stack; it now fails at once,
    ;; and simp ends with the goal open (a proof-incomplete error, not a StackOverflowError)
    (is (= clojure.lang.ExceptionInfo
           (run-simp '[k :- Nat]
                     '(= Bool (if (= k 0) (mt-in-range (Int.ofNat (+ k 1))) (mt-in-range (Int.ofNat k))) true)
                     '[(simp)])))))
