(ns ansatz.tactic.grind-resource-test
  "Init-only recursive coverage regression; paired with grind_coverage.lean."
  (:require [clojure.test :refer [deftest is use-fixtures]]
            [ansatz.core :as a]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.tc :as tc]
            [ansatz.kernel.reduce :as red]
            [ansatz.tactic.grind.egraph :as eg]
            [ansatz.tactic.grind.simp :as gs]
            [ansatz.tactic.grind.action :as action]))

(use-fixtures :once
  (fn [f]
    (let [before @a/ansatz-env]
      (try
        (a/load-init!)
        (binding [a/*verbose* false
                  *ns* (the-ns 'ansatz.tactic.grind-resource-test)]
          (f))
        (finally (reset! a/ansatz-env before))))))

(deftest recursive-coverage-closes-with-shared-record-terms
  ;; Reconstructing a record from projections can multiply the traversal cost
  ;; even when E-matching generates only a few hundred graph nodes.
  (a/structure CovHandle [] (id Nat) (spin Nat) (reachable Bool) (touched Bool) (dropped Bool))
  (a/structure CovEntity [] (id Nat) (tokens (List Nat)))
  (a/defn covmem [x :- Nat, xs :- (List Nat)] Bool
    (match xs [nil false]
      [(cons h t) (if (Nat.beq x h) true (covmem x t))]))
  (a/defn covone [h :- CovHandle, e :- CovEntity] Bool
    (if (Nat.beq (:spin h) (:id e))
        (Bool.and
          (if (:dropped h) (Bool.not (covmem (:id h) (:tokens e))) true)
          (if (Bool.and (:reachable h) (Bool.and (:touched h) (Bool.not (:dropped h))))
              (covmem (:id h) (:tokens e)) true))
        true))
  (a/defn covall [h :- CovHandle, es :- (List CovEntity)] Bool
    (match es [nil true]
      [(cons e t) (Bool.and (covone h e) (covall h t))]))
  (a/deftheorem cov-one-loss [h :- CovHandle, e :- CovEntity]
    (=> (= (covone h e) true)
        (= (covone (CovHandle.mk (:id h) (:spin h) false (:touched h) (:dropped h)) e) true))
    (grind [covone]))
  (let [result (try
                 (a/prove-theorem
                  'cov-loss
                  '[h :- CovHandle, es :- (List CovEntity)]
                  '(=> (= (covall h es) true)
                       (= (covall (CovHandle.mk (:id h) (:spin h) false (:touched h) (:dropped h)) es) true))
                  '[(induction es) (simp [covall]) (intro hc) (grind [covall cov-one-loss])])
                 :proved
                 (catch clojure.lang.ExceptionInfo ex
                   (if (= :tactic-error (:kind (ex-data ex))) (ex-data ex) (throw ex))))]
    (is (= :proved result) (str result))))

(defn- nat-state []
  (tc/attach-lctx (tc/mk-tc-state (a/env))
                  (-> {} (red/lctx-add-local 7 "x" (e/const' (name/from-string "Nat") []))
                      (red/lctx-add-local 8 "y" (e/const' (name/from-string "Nat") [])))))

(deftest shared-addition-preprocessing-is-linear
  (doseq [depth [16 40]]
    (let [st (nat-state) state (gs/mk-state)
          term (reduce (fn [t _] (e/app* (e/const' (name/from-string "Nat.add") []) t t))
                       (e/fvar 7) (range depth))
          visits (atom 0) post @#'gs/unfold-reducible-step]
      (binding [action/*config* (action/configure {:max-steps 100}) gs/*state* state]
        (let [graph (assoc (eg/internalize (eg/mk-grind-state (a/env)) term 0)
                           :simp-context (gs/mk-context st))
              result (with-redefs [gs/unfold-reducible-step
                                  (fn [expr] (swap! visits inc) (post expr))]
                       (gs/preprocess graph st))]
          (is (contains? (:simp-done result) term) "the real preprocessing path completed")
          (is (= (+ 2 (* 2 depth)) @(:num-steps state)) "one uncached simp visit per shared app node")
          (is (<= @visits (inc (* 2 depth))) "reducible unfolding visits each shared node once")
          (is (<= (count (:enodes result)) (+ depth 10)) "preprocessing preserves the graph's sharing"))))))

(deftest simplification-budget-persists-across-preprocessing-calls
  (let [st (nat-state) state (gs/mk-state)
        add (e/const' (name/from-string "Nat.add") [])
        term (e/app* add (e/fvar 7) (e/fvar 7))]
    (binding [action/*config* (action/configure {:max-steps 4}) gs/*state* state]
      (let [index (gs/mk-context st)
            graph (fn [term] (assoc (eg/internalize (eg/mk-grind-state (a/env)) term 0) :simp-context index))]
        (gs/preprocess (graph term) st)
        (is (= 4 @(:num-steps state)))
        (gs/preprocess (graph term) st)
        (is (= 4 @(:num-steps state)) "cache hits do not charge simplification steps")
        (let [error (try (gs/preprocess (graph (e/app* add (e/fvar 7) (e/fvar 8))) st)
                         (catch clojure.lang.ExceptionInfo ex ex))]
          (is (= :tactic-error (:kind (ex-data error))))
          (is (= :max-steps (:limit (ex-data error))))
          (is (= 5 (:used (ex-data error)))))))))

(deftest internalization-bounds-recursion-without-limiting-arity
  (let [wide (reduce (fn [t _] (e/app t (e/fvar 1))) (e/fvar 0) (range 1000))
        deep (reduce (fn [t _] (e/app (e/fvar 0) t)) (e/fvar 1) (range 600))
        opaque (e/lam "x" (e/fvar 2) deep :default)]
    (binding [action/*config* (action/configure {:max-rec-depth 2 :max-steps 0})]
      (is (some? (eg/get-enode (eg/internalize (eg/mk-grind-state (env/empty-env)) wide 0) wide)))
      (is (some? (eg/get-enode (eg/internalize (eg/mk-grind-state (env/empty-env)) opaque 0) opaque))))
    (doseq [limit [16 512]]
      (binding [action/*config* (action/configure {:max-rec-depth limit})]
        (let [error (try (eg/internalize (eg/mk-grind-state (env/empty-env)) deep 0)
                         (catch clojure.lang.ExceptionInfo ex ex))]
          (is (= :tactic-error (:kind (ex-data error))))
          (is (= :maxRecDepth (:limit (ex-data error))))
          (is (= limit (:value (ex-data error))))
          (is (= (inc limit) (:used (ex-data error)))))))))

(deftest arithmetic-receives-congruence-equalities
  (is (= :proved
         (do (a/prove-theorem
              'arithmetic-congruence
              '[f :- (=> Nat Nat), a :- Nat, b :- Nat, x :- Nat, y :- Nat, h :- (= a b)]
              '(= (+ (+ (f a) x) y) (+ (f b) (+ x y)))
              '[(grind)])
             :proved))))
