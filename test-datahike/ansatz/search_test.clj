(ns ansatz.search-test
  "The library-as-database layer (ansatz.search) over a real, if small, store: init-medium
   imported with facts, then the queries a prover actually asks — what uses this lemma, what
   mentions it, what is in this module's simp set — and `suggest`, which recalls by conclusion
   shape, ranks by specificity and vocabulary, and confirms with the kernel."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [ansatz.core :as a]
            [ansatz.import :as imp]
            [ansatz.search :as s]
            [ansatz.catalogue :as cat]
            [ansatz.tactic.proof :as proof]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as nm]))

(def ^:private store (atom nil))

(use-fixtures :once
  (fn [f]
    (let [dir (doto (java.io.File/createTempFile "ansatz-search" "") .delete .getPath)]
      (imp/import! dir {:ndjson "test-data/init-medium.ndjson"
                        :attrs "resources/ansatz/init-attrs.ndjson.gz"
                        :branch "init" :verbose? false :parallelism 2})
      (cat/build! dir {:branch "init" :log (constantly nil)})
      (reset! store dir)
      (binding [a/*verbose* false] (a/init! dir "init"))
      (f))))

(defn- db [] (s/db))

(deftest facts-are-queryable
  (testing "kind, binders, conclusion head and the statement's vocabulary"
    (let [d (s/describe (db) "Nat.add_comm")]
      (is (= :thm (:decl/kind d)))
      (is (= "Eq" (:decl/concl-head d)))
      (is (= 2 (:decl/num-binders d)))
      (is (contains? (set (:decl/mentions d)) "HAdd.hAdd") "the statement's constants")
      (is (contains? (set (:decl/depends-on d)) "Nat.succ_add") "the PROOF's constants")))
  (testing "a declaration that is not there"
    (is (nil? (s/describe (db) "No.Such.Lemma")))
    (is (nil? (s/eid (db) "No.Such.Lemma")))))

(deftest the-ref-edges-are-joins
  (let [d (db)]
    (testing "users-of is the reverse of depends-on"
      (let [users (set (s/users-of d "Nat.add_comm"))]
        (is (seq users))
        (is (every? #(contains? (set (:decl/depends-on (s/describe d %))) "Nat.add_comm") users))))
    (testing "mentioned-by is the reverse of mentions"
      (let [ms (set (s/mentioned-by d "Nat.succ"))]
        (is (seq ms))
        (is (every? #(contains? (set (:decl/mentions (s/describe d %))) "Nat.succ") ms))))
    (testing "find-decls intersects vocabulary with the other facts"
      (let [r (set (s/find-decls d {:mentions ["Nat.succ"] :kind :thm :limit 1000}))]
        (is (seq r))
        (is (every? #(= :thm (:decl/kind (s/describe d %))) r))
        (is (clojure.set/subset? r (set (s/mentioned-by d "Nat.succ")))))
      (is (empty? (s/find-decls d {:mentions ["No.Such.Lemma"]})) "an unknown constant matches nothing"))))

(deftest suggest-finds-and-confirms
  (testing "a goal whose proof is one lemma application: recalled by shape, confirmed by apply"
    (let [ps (s/goal-state "Nat.succ_le_of_lt")
          hits (s/suggest ps :limit 5 :try 40)]
      (is (seq hits))
      (is (every? #(contains? #{:apply :exact} (first (:tactic %))) hits))
      (is (some #(= "Nat.succ_le_of_lt" (:name %)) hits)
          "the lemma itself is among the confirmed suggestions")
      (testing "every suggestion really applies to the goal"
        (is (every? (fn [{:keys [name]}]
                      (some? (#'s/try-apply ps name)))
                    hits)))))
  (testing "candidates carry specificity and are ordered by it"
    (let [ps (s/goal-state "Nat.succ_le_of_lt")
          cs (s/candidates (db) (:type (proof/current-goal ps)) :limit 50)]
      (is (seq cs))
      (is (= (map :specificity cs) (reverse (sort (map :specificity cs))))
          "most specific first")
      (is (some #(= "Nat.succ_le_of_lt" (:name %)) cs) "the goal's own lemma is recalled"))))

(deftest search-degrades-without-a-catalogue
  (testing "the bundled tier has no catalogue: db is nil and suggest says so, it does not throw
            something opaque"
    ;; This one MUTATES the global env, and clojure.test runs vars in hash order — so it puts
    ;; the store back before any other test observes it.
    (try
      (binding [a/*verbose* false] (a/load-init!))
      (is (nil? (s/db)) "load-init! clears the store a previous init! installed")
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"no catalogue"
                            (s/suggest (first (proof/start-proof
                                               (a/env)
                                               (:type (env/lookup (a/env) (nm/from-string "Nat.add_comm"))))))))
      (finally (binding [a/*verbose* false] (a/init! @store "init"))))))
