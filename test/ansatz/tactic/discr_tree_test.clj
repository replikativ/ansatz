(ns ansatz.tactic.discr-tree-test
  "Tests for discrimination tree."
  (:require [clojure.test :refer [deftest testing is]]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.tc :as tc]
            [ansatz.tactic.discr-tree :as dt]
            [ansatz.tactic.simp :as simp]
            [ansatz.export.parser :as parser]
            [ansatz.export.replay :as replay]))

(def ^:private init-medium-env
  (delay
    (let [f "test-data/init-medium.ndjson"]
      (when (.exists (java.io.File. f))
        (let [st (parser/parse-ndjson-file f)
              result (replay/replay (:decls st))]
          (:env result))))))

(defn- require-env []
  (or @init-medium-env
      (throw (ex-info "init-medium.ndjson not found" {}))))

;; ============================================================
;; Key encoding tests
;; ============================================================

(deftest test-expr-to-keys-const
  (testing "Bare constant encodes to single const key"
    (let [keys (dt/expr->keys (e/const' (name/from-string "Nat") []))]
      (is (= 1 (count keys)))
      (is (= :const (:tag (first keys))))
      (is (= 0 (:arity (first keys)))))))

(deftest test-expr-to-keys-app
  (testing "Application encodes head + args"
    (let [f (e/const' (name/from-string "Nat.add") [])
          expr (e/app* f (e/lit-nat 3) (e/lit-nat 5))
          keys (dt/expr->keys expr)]
      (is (= 3 (count keys)))
      (is (= :const (:tag (first keys))))
      (is (= 2 (:arity (first keys))))
      (is (= :lit (:tag (second keys))))
      (is (= 3 (:val (second keys))))
      (is (= :lit (:tag (nth keys 2))))
      (is (= 5 (:val (nth keys 2)))))))

(deftest test-expr-to-keys-bvar-is-star
  (testing "BVar encodes as star (wildcard)"
    (let [keys (dt/expr->keys (e/bvar 0))]
      (is (= 1 (count keys)))
      (is (= :star (:tag (first keys)))))))

(deftest test-expr-to-keys-forall
  (testing "Forall encodes as arrow + domain"
    (let [nat (e/const' (name/from-string "Nat") [])
          expr (e/forall' "x" nat nat :default)
          keys (dt/expr->keys expr)]
      (is (= 2 (count keys)))
      (is (= :arrow (:tag (first keys))))
      (is (= :const (:tag (second keys)))))))

;; ============================================================
;; Trie insertion and lookup
;; ============================================================

(deftest test-trie-insert-and-lookup
  (testing "Insert and retrieve from trie"
    (let [keys1 [{:tag :const :name "f" :arity 1} {:tag :lit :val 0}]
          keys2 [{:tag :const :name "f" :arity 1} {:tag :lit :val 1}]
          tree (-> dt/empty-trie
                   (dt/trie-insert keys1 :lemma-a)
                   (dt/trie-insert keys2 :lemma-b))]
      ;; Lookup f(0) → only lemma-a
      (is (= [:lemma-a] (dt/trie-match tree keys1)))
      ;; Lookup f(1) → only lemma-b
      (is (= [:lemma-b] (dt/trie-match tree keys2))))))

(deftest test-trie-star-matching
  (testing "Star keys match anything during lookup"
    (let [;; Insert f(star) — matches any arg
          keys-pattern [{:tag :const :name "f" :arity 1} {:tag :star}]
          ;; Query f(0)
          keys-query [{:tag :const :name "f" :arity 1} {:tag :lit :val 0}]
          tree (dt/trie-insert dt/empty-trie keys-pattern :wildcard-lemma)]
      ;; Star in tree matches lit in query
      (is (= [:wildcard-lemma] (dt/trie-match tree keys-query))))))

(deftest test-trie-star-query-matches-all
  (testing "Star in query matches all tree entries"
    (let [keys1 [{:tag :const :name "f" :arity 1} {:tag :lit :val 0}]
          keys2 [{:tag :const :name "f" :arity 1} {:tag :lit :val 1}]
          keys-query [{:tag :const :name "f" :arity 1} {:tag :star}]
          tree (-> dt/empty-trie
                   (dt/trie-insert keys1 :a)
                   (dt/trie-insert keys2 :b))]
      ;; Star in query should match both
      (let [results (set (dt/trie-match tree keys-query))]
        (is (contains? results :a))
        (is (contains? results :b))))))

(deftest test-trie-no-false-positives
  (testing "Distinct heads don't cross-match"
    (let [keys1 [{:tag :const :name "f" :arity 1} {:tag :lit :val 0}]
          keys2 [{:tag :const :name "g" :arity 1} {:tag :lit :val 0}]
          tree (-> dt/empty-trie
                   (dt/trie-insert keys1 :f-lemma)
                   (dt/trie-insert keys2 :g-lemma))]
      (is (= [:f-lemma] (dt/trie-match tree keys1)))
      (is (= [:g-lemma] (dt/trie-match tree keys2))))))

;; ============================================================
;; Integration with simp lemmas
;; ============================================================

(deftest test-simp-tree-precision
  (testing "Discrimination tree returns candidates for matching"
    (let [env (require-env)
          lemmas (simp/make-simp-lemmas env ["Nat.add_zero" "Nat.zero_add"])
          tree (simp/build-lemma-index lemmas)]
      (is (= 2 (dt/tree-size tree)))
      ;; Each LHS should retrieve at least its own lemma as a candidate
      ;; (OfNat literal folding may cause both to share some key prefixes)
      (doseq [l lemmas]
        (let [results (dt/lookup-simp-tree tree (:lhs-pattern l))]
          (is (>= (count results) 1)
              (str "Expected ≥1 result for " (name/->string (:name l))
                   " but got " (count results))))))))

(deftest test-simp-tree-multi-head
  (testing "Tree handles multiple head constants"
    (let [env (require-env)
          lemmas (simp/make-simp-lemmas env
                                        ["Nat.add_zero" "Nat.mul_one" "ite_true" "Bool.true_and"])
          tree (simp/build-lemma-index lemmas)
          n (count lemmas)]
      (is (= n (dt/tree-size tree)))
      ;; At least 2 distinct heads (HAdd.hAdd, HMul.hMul)
      (is (>= (count (:children tree {})) 2)))))

(deftest test-tree-size-and-depth
  (testing "Tree statistics are correct"
    (let [tree (-> dt/empty-trie
                   (dt/trie-insert [{:tag :const :name "a" :arity 0}] :v1)
                   (dt/trie-insert [{:tag :const :name "b" :arity 0}] :v2)
                   (dt/trie-insert [{:tag :const :name "c" :arity 1}
                                    {:tag :lit :val 0}] :v3))]
      (is (= 3 (dt/tree-size tree)))
      (is (= 2 (dt/tree-depth tree))))))

;; ============================================================
;; Scaling and performance tests
;; ============================================================

(defn- make-bench-lemmas
  "Create n synthetic simp lemmas: s_i : f(g_{i+1}(x)) = f(g_i(x)).
   Replicates Lean 4's tests/simpperf/simp500.lean pattern."
  [n]
  (let [f-name (name/from-string "f")]
    (mapv (fn [i]
            (let [gi (name/from-string (str "g" i))
                  gi1 (name/from-string (str "g" (inc i)))]
              {:name (name/from-string (str "s" i))
               :level-params [] :num-params 1
               :lhs-pattern (e/app (e/const' f-name [])
                                   (e/app (e/const' gi1 []) (e/bvar 0)))
               :rhs (e/app (e/const' f-name [])
                           (e/app (e/const' gi []) (e/bvar 0)))
               :eq-type nil :kind :eq :priority 1000 :perm false
               :head-name f-name :lhs-nargs 1}))
          (range n))))

(deftest test-scaling-build
  (testing "Tree build time scales linearly"
    (let [l500  (make-bench-lemmas 500)
          l1000 (make-bench-lemmas 1000)
          t0 (System/nanoTime)
          _ (dt/make-simp-tree l500)
          t1 (System/nanoTime)
          _ (dt/make-simp-tree l1000)
          t2 (System/nanoTime)
          ms500  (/ (- t1 t0) 1e6)
          ms1000 (/ (- t2 t1) 1e6)]
      ;; 1000 should take roughly 2x as long as 500
      (is (< ms1000 (* 4 ms500))
          (str "1000-lemma build (" ms1000 "ms) should be <4x 500-lemma build (" ms500 "ms)")))))

(deftest test-scaling-lookup-selectivity
  (testing "Lookup returns exactly 1 result from N lemmas (all same head)"
    (doseq [n [100 500 1000]]
      (let [lemmas (make-bench-lemmas n)
            tree (dt/make-simp-tree lemmas)
            ;; Query for g_{n/2} — should match exactly s_{n/2-1}
            query (e/app (e/const' (name/from-string "f") [])
                         (e/app (e/const' (name/from-string (str "g" (quot n 2))) [])
                                (e/bvar 0)))
            results (dt/lookup-simp-tree tree query)]
        (is (= 1 (count results))
            (str "Expected 1 result for n=" n " but got " (count results)))))))

(deftest test-scaling-lookup-constant-time
  (testing "Lookup time is roughly constant regardless of tree size"
    (let [t500  (dt/make-simp-tree (make-bench-lemmas 500))
          t3000 (dt/make-simp-tree (make-bench-lemmas 3000))
          q (e/app (e/const' (name/from-string "f") [])
                   (e/app (e/const' (name/from-string "g250") []) (e/bvar 0)))
          ;; Warm up JIT on BOTH trees
          _ (dotimes [_ 20000] (dt/lookup-simp-tree t500 q))
          _ (dotimes [_ 20000] (dt/lookup-simp-tree t3000 q))
          measure (fn [tree]
                    (let [t0 (System/nanoTime)
                          _ (dotimes [_ 10000] (dt/lookup-simp-tree tree q))
                          t1 (System/nanoTime)]
                      (/ (- t1 t0) 10000.0)))
          ns500  (measure t500)
          ns3000 (measure t3000)]
      ;; 3000 should not be more than 10x slower than 500
      ;; (generous bound to avoid flaky failures from GC/JIT)
      (is (< ns3000 (* 10 ns500))
          (str "3000-lookup (" ns3000 "ns) should be <10x 500-lookup (" ns500 "ns)")))))

(deftest test-identical-patterns-worst-case
  (testing "Identical key patterns return all N results (worst case)"
    (let [n 100
          f-name (name/from-string "f")
          lemmas (mapv (fn [i]
                         {:name (name/from-string (str "id" i))
                          :level-params [] :num-params 1
                          :lhs-pattern (e/app (e/const' f-name []) (e/bvar 0))
                          :rhs (e/bvar 0) :eq-type nil
                          :kind :eq :priority (- 1000 i) :perm false
                          :head-name f-name :lhs-nargs 1})
                       (range n))
          tree (dt/make-simp-tree lemmas)
          query (e/app (e/const' f-name []) (e/bvar 0))
          results (dt/lookup-simp-tree tree query)]
      ;; All N lemmas should be returned (degenerate case)
      (is (= n (count results))))))
