(ns ansatz.simp-index-test
  "The persistent @[simp] index (ansatz.simp-index): dump a store's @[simp] LHS keys once, load
   the `key → name` trie on first demand, and let simp serve the inherited corpus lazily —
   candidate names by disc-tree key, rules resolved+extracted only for the handful that match —
   instead of hydrating every name on every call. Exercised on the bundled Init tier with a
   temp artifact so the test needs no Mathlib store."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [ansatz.core :as a]
            [ansatz.simp-index :as si]
            [ansatz.state :as state]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.tc :as tc]
            [ansatz.tactic.simp :as simp]))

(use-fixtures :once (fn [f] (a/load-init!) (binding [a/*verbose* false] (f))))

(defn- dump-inherited-set!
  "Dump the loaded env's whole inherited @[simp] set (a few hundred names on the bundled tier)
   to a fresh temp artifact; returns [path key-count]."
  []
  (let [env (a/env)
        names (sort (env/get-extension env :simp-lemmas #{}))
        f (java.io.File/createTempFile "simp-keys" ".ndjson.gz")]
    (.deleteOnExit f)
    [(.getPath f) (si/dump-simp-keys! names env #(env/lookup env (name/from-string %)) (.getPath f))]))

(defn- lhs-of [env lemma]
  (:lhs-pattern (first (@#'simp/extract-simp-lemma env (env/lookup env (name/from-string lemma)) 1000))))

(deftest dump-load-and-candidates
  (testing "stored LHS keys round-trip through EDN and match the query keying"
    (let [[path n] (dump-inherited-set!)
          env (a/env)
          st (tc/mk-tc-state env)
          trie (si/load-simp-trie path)]
      (is (> n 100) "the inherited corpus, not the hand-curated core")
      (is (some #{"Nat.add_zero"} (si/candidate-names trie st env (lhs-of env "Nat.add_zero")))
          "a lemma's own LHS finds it (keys agree between dump and query)")
      (is (some #{"Option.some.injEq"} (si/candidate-names trie st env (lhs-of env "Option.some.injEq")))
          "and one outside the hand-curated set")
      (is (not-any? #{"Option.some.injEq"} (si/candidate-names trie st env (lhs-of env "Nat.add_zero")))
          "the trie discriminates")
      (testing "rules resolve lazily, at the lemma's inherited priority, and memoize"
        (si/reset-index! path)
        (try
          (let [rules (si/rules-for env "Option.some.injEq")]
            (is (seq rules))
            (is (= "Option.some.injEq" (name/->string (:name (first rules)))))
            (is (= simp/default-simp-priority (:priority (first rules))))
            (is (identical? rules (si/rules-for env "Option.some.injEq")) "memoized"))
          (is (= [] (si/rules-for env "No.Such.Lemma")) "a bad name is tolerated (and memoized as empty)")
          (finally (si/reset-index! nil)))))))

(deftest simp-serves-the-inherited-set-lazily
  (testing "with the index recorded, (simp) closes a goal that only the inherited set can, and the
            trie was loaded on that first call — not at init"
    (let [[path _] (dump-inherited-set!)]
      (si/reset-index! path)
      (try
        (is (nil? @state/ansatz-simp-trie) "nothing loaded before the first simp")
        ;; Option.some.injEq is @[simp] in Lean but NOT hand-curated (see attrs-test); with the
        ;; extension excluded from the eager set this closes ONLY through the lazy path.
        (a/prove-theorem 'opt-inj-lazy '[a :- Nat, b :- Nat]
                         '(= Prop (= (Option Nat) (Option.some a) (Option.some b)) (= Nat a b)) '[(simp)])
        (is (some? (env/lookup (a/env) (name/from-string "opt-inj-lazy"))))
        (is (some? @state/ansatz-simp-trie) "the trie was built on demand by simp")
        (finally (si/reset-index! nil))))))

(deftest a-missing-artifact-keeps-the-eager-path
  (testing "no path recorded → no trie, and the extension is still on by default (eager)"
    (si/reset-index! nil)
    (is (nil? (si/ensure-simp-trie!)))
    (a/prove-theorem 'opt-inj-eager '[a :- Nat, b :- Nat]
                     '(= Prop (= (Option Nat) (Option.some a) (Option.some b)) (= Nat a b)) '[(simp)])
    (is (some? (env/lookup (a/env) (name/from-string "opt-inj-eager"))))
    (is (nil? @state/ansatz-simp-trie))))
