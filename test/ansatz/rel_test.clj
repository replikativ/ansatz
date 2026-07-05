;; Tests for ansatz.rel — measurable relational proof search.

(ns ansatz.rel-test
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [ansatz.rel :as r]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.name :as nm]
            [ansatz.kernel.reduce :as red]
            [ansatz.export.parser :as parser]
            [ansatz.export.replay :as replay]))

(def ^:private init-medium-env
  (delay
    (let [f "test-data/init-medium.ndjson"]
      (when (.exists (java.io.File. f))
        (:env (replay/replay (:decls (parser/parse-ndjson-file f))))))))

(def ^:dynamic *env* nil)

(use-fixtures :once
  (fn [f]
    (binding [*env* (or @init-medium-env
                        (throw (ex-info "init-medium.ndjson not found" {})))]
      (f))))

(def Nat* (delay (e/const' (nm/from-string "Nat") [])))

(defn- nle [a b]
  (reduce e/app (e/const' (nm/from-string "LE.le") [lvl/zero])
          [@Nat* (e/const' (nm/from-string "instLENat") []) a b]))

(deftest fresh-unify-reify
  (testing "a hole unifies and reifies"
    (let [res (r/run 1 (r/state *env*)
                     (r/fresh @Nat*
                              (fn [x]
                                (r/all (r/=== x (e/lit-nat 5))
                                       (fn [s] (r/unit (assoc s ::x (r/zonk s x))))))))]
      (is (= 1 (count res)))
      (is (= (e/lit-nat 5) (::x (first res)))))))

(deftest condw-weights-order-and-measure
  (testing "condw acts as branch prior: order + measure"
    (let [res (r/run 2 (r/state *env*)
                     (r/fresh @Nat*
                              (fn [x]
                                (r/condw
                                 [1 (r/=== x (e/lit-nat 1))]
                                 [9 (r/=== x (e/lit-nat 2))]))))]
      (is (= 2 (count res)))
      ;; heavier branch first, and its weight is larger
      (is (> (:logw (first res)) (:logw (second res)))))))

(def base-lctx*
  (delay (-> (red/empty-lctx)
             (red/lctx-add-local 10 "n" @Nat*)
             (red/lctx-add-local 11 "m" @Nat*)
             (red/lctx-add-local 12 "k" @Nat*))))

(deftest omnidirectional-infer-the-assumption
  (testing "hypothesis TYPE is a hole; proveo infers it through le_trans"
    (let [n (e/fvar 10) m (e/fvar 11) k (e/fvar 12)
          demo (r/fresh-ty
                (fn [A]
                  (fn [s]
                    (let [s (update s :lctx
                                    #(-> %
                                         (red/lctx-add-local 20 "h1" (nle n m))
                                         (red/lctx-add-local 21 "h2" A)))]
                      ((r/fresh (nle n k)
                                (fn [g]
                                  (r/all (r/proveo g [[1 "Nat.le_trans"]] 3)
                                         (fn [st]
                                           (r/unit (assoc st ::A (r/zonk st A) ::g g))))))
                       s)))))
          res (r/run 3 (r/state *env* :lctx @base-lctx*) demo)
          answers (set (map #(e/->string (::A %)) res))]
      ;; the trivial solution (?A := goal) and the inferred one (?A := m ≤ k)
      (is (contains? answers (e/->string (nle n k))) "trivial: h2 is the goal")
      (is (contains? answers (e/->string (nle m k))) "inferred THROUGH le_trans")
      ;; every solution survives strict kernel checking
      (doseq [st res]
        (is (:ok? (r/certify st (::g st)))
            (str "kernel rejects " (e/->string (r/zonk st (::g st)))))))))

(deftest higher-order-assumption-inference
  (testing "hyp himp : ?A, NO lemmas — the search infers the IMPLICATION
            ?A := (n ≤ m) → (n ≤ k) and proves the goal by himp hp"
    (let [n (e/fvar 10) m (e/fvar 11) k (e/fvar 12)
          demo (r/fresh-ty
                (fn [A]
                  (fn [s]
                    (let [s (update s :lctx
                                    #(-> %
                                         (red/lctx-add-local 20 "hp" (nle n m))
                                         (red/lctx-add-local 21 "himp" A)))]
                      ((r/fresh (nle n k)
                                (fn [g]
                                  (r/all (r/proveo g [] 2 {:hyp-arities [1]})
                                         (fn [st]
                                           (r/unit (assoc st ::A (r/zonk st A) ::g g))))))
                       s)))))
          res (r/run 4 (r/state *env* :lctx @base-lctx*) demo)
          answers (set (map #(e/->string (::A %)) res))]
      (is (contains? answers (e/->string (e/arrow (nle n m) (nle n k))))
          "inferred the implication (modus ponens run backwards)")
      (doseq [st res]
        (is (:ok? (r/certify st (::g st))))))))

(deftest generative-direction-enumerates-consequences
  (testing "goal is a hole; the same relation enumerates provable propositions"
    (let [n (e/fvar 10) m (e/fvar 11) k (e/fvar 12)
          gen (fn [s]
                (let [s (update s :lctx
                                #(-> %
                                     (red/lctx-add-local 20 "h1" (nle n m))
                                     (red/lctx-add-local 21 "h2" (nle m k))))]
                  ((r/fresh-ty
                    (fn [G]
                      (r/fresh G
                               (fn [g]
                                 (r/all (r/proveo g [[1 "Nat.le_trans"]] 2)
                                        (fn [st]
                                          (r/unit (assoc st ::what (r/zonk st G)))))))))
                   s)))
          res (r/run 8 (r/state *env* :lctx @base-lctx*) gen)
          props (set (map #(e/->string (::what %)) res))]
      ;; the derived consequence n ≤ k is found generatively
      (is (contains? props (e/->string (nle n k)))))))
