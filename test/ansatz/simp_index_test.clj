(ns ansatz.simp-index-test
  "The @[simp] LHS index (ansatz.simp-index) at the unit level: keying agrees between the
   stored and query sides, rules resolve lazily at their inherited priority and memoize, and
   the index source rides on the Env — an env built without `init!` has none. The store-backed
   path (trie blob loaded on first simp) is exercised end to end in ansatz.import-test."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [ansatz.core :as a]
            [ansatz.simp-index :as si]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.tc :as tc]
            [ansatz.tactic.simp :as simp]))

(use-fixtures :once (fn [f] (a/load-init!) (binding [a/*verbose* false] (f))))

(defn- inherited-entries
  "Key the loaded env's whole inherited @[simp] set in-process (what the importer does)."
  []
  (let [env (a/env)
        names (sort (env/get-extension env :simp-lemmas #{}))]
    (si/lemma-keys names env #(env/lookup env (name/from-string %)))))

(defn- lhs-of [env lemma]
  (:lhs-pattern (first (@#'simp/extract-simp-lemma env (env/lookup env (name/from-string lemma)) 1000))))

(deftest keys-and-candidates
  (testing "stored LHS keys match the query keying"
    (let [entries (inherited-entries)
          env (a/env)
          st (tc/mk-tc-state env)
          trie (si/build-simp-trie entries)]
      (is (> (count entries) 100) "the inherited corpus, not the hand-curated core")
      (is (some #{"Nat.add_zero"} (si/candidate-names trie st env (lhs-of env "Nat.add_zero")))
          "a lemma's own LHS finds it")
      (is (some #{"Option.some.injEq"} (si/candidate-names trie st env (lhs-of env "Option.some.injEq"))))
      (is (not-any? #{"Option.some.injEq"} (si/candidate-names trie st env (lhs-of env "Nat.add_zero")))
          "the trie discriminates"))))

(deftest rules-resolve-lazily-at-inherited-priority
  (let [env (si/with-index-source (a/env) {:store-path "/nowhere" :branch "x"})]
    (let [rules (si/rules-for env "Option.some.injEq")]
      (is (seq rules))
      (is (= "Option.some.injEq" (name/->string (:name (first rules)))))
      (is (= simp/default-simp-priority (:priority (first rules))))
      (is (identical? rules (si/rules-for env "Option.some.injEq")) "memoized"))
    (is (= [] (si/rules-for env "No.Such.Lemma")) "a bad name is tolerated (and memoized as empty)")))

(deftest the-index-source-rides-on-the-env
  (testing "an env built without init! has no source and no trie; a source naming a store that
            is not the current one yields no trie either (no leak across stores)"
    (is (nil? (si/index-source (a/env))))
    (is (nil? (si/ensure-simp-trie! (a/env))))
    (let [indexed (si/with-index-source (a/env) {:store-path "/nowhere" :branch "x"})]
      (is (= {:store-path "/nowhere" :branch "x"} (si/index-source indexed)))
      (is (nil? (si/index-source (a/env))) "the original env is untouched (immutable)")
      (is (nil? (si/ensure-simp-trie! indexed)) "not the current store → no trie"))))
