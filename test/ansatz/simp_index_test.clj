(ns ansatz.simp-index-test
  "The @[simp] LHS index (ansatz.simp-index) at the unit level: keying agrees between the
   stored and query sides, rules resolve lazily at their inherited priority and memoize, and
   the index source rides on the Env — an env built without `init!` has none. The store-backed
   path (captured trie with rules resolved on demand) is exercised end to end in ansatz.import-test."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [ansatz.core :as a]
            [ansatz.simp-index :as si]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]
            [ansatz.tactic.discr-tree :as dt]
            [ansatz.export.storage :as storage]
            [ansatz.state :as state]
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
          trie (si/build-simp-trie (si/key-entries-artifact entries))]
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

(defn- c [n] (e/const' (name/from-string n) []))
(defn- legacy-keys [st environment expr]
  ;; Frozen pre-offset generator (encoding 1), independent of the current default.
  (mapv #(if (:name %) (update % :name name/->string) %)
        (dt/expr->keys st environment expr {:key-encoding 1})))

(deftest old-index-new-query-retains-successor-candidates
  (let [environment (a/env)
        st (tc/mk-tc-state-with-locals environment
                                       {100 {:name "n" :type (c "Nat")}
                                        101 {:name "m" :type (c "Nat")}})
        succ #(e/app (c "Nat.succ") %)
        pred #(e/app (c "Nat.pred") %)
        eq (fn [x y] (e/app* (e/const' (name/from-string "Eq") [(lvl/succ lvl/zero)])
                             (c "Nat") x y))
        inj-ci (env/lookup! environment (name/from-string "Nat.succ.injEq"))
        inj-pattern (:lhs-pattern (first (@#'simp/extract-simp-lemma environment inj-ci 1000)))
        fixtures [["Nat.pred_succ" (pred (succ (e/bvar 0))) (pred (succ (e/fvar 100)))]
                  ["literal-pred" (pred (succ (e/lit-nat 2))) (pred (succ (e/lit-nat 2)))]
                  ["Nat.succ.injEq" inj-pattern (eq (succ (e/fvar 100)) (succ (e/fvar 101)))]]]
    ;; Golden paths from the old generator: do not rebuild these with current keys.
    (is (= [{:tag :const :name "Nat.pred" :arity 1}
            {:tag :const :name "Nat.succ" :arity 1} {:tag :star}]
           (legacy-keys st environment (pred (succ (e/bvar 0))))))
    (is (= ["Eq" "Nat" "Nat.succ" nil "Nat.succ" nil]
           (mapv :name (legacy-keys st environment inj-pattern))))
    (doseq [[lemma pattern query] fixtures]
      (let [entries [[lemma (pr-str (legacy-keys st environment pattern))]]
            legacy (dissoc (si/build-simp-trie entries) :key-encoding)
            tagged (si/read-simp-trie legacy)
            current (si/build-simp-trie
                     (si/key-entries-artifact
                      [[lemma (pr-str (#'si/edn-safe-keys (dt/expr->keys st environment pattern)))]]))]
        (doseq [trie [legacy tagged current]]
          (is (= [lemma] (vec (si/candidate-names trie st environment query)))))
        (is (= 1 (si/key-encoding tagged)))
        (is (= si/write-key-encoding (si/key-encoding current)))))))

(deftest captured-and-legacy-derived-artifacts-check-encoding
  (let [environment (a/env)
        source {:store-path "/legacy" :branch "main"}
        legacy {:values [] :children {}}
        captured (si/with-captured-index environment source legacy)]
    (is (= 1 (:key-encoding (si/ensure-simp-trie! captured))))
    (with-redefs [state/ansatz-store (atom (assoc source :store-map {:store :fixture}))
                  state/ansatz-simp-trie (atom nil)
                  storage/read-derived (fn [store branch kind]
                                         (is (= [:fixture "main" :simp-trie] [store branch kind])) legacy)]
      (is (= 1 (:key-encoding (si/ensure-simp-trie! (si/with-index-source environment source))))))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Unsupported persisted simp key encoding"
                          (si/with-captured-index environment source (assoc legacy :key-encoding 999))))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Unsupported persisted simp key encoding"
                          (si/build-simp-trie {:key-encoding 999 :entries []})))))
