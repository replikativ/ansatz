(ns ansatz.kernel.sharing-test
  "Lean kernel/{abstract,instantiate,replace_fn}.cpp and Meta/InferType.lean caches."
  (:require [clojure.test :refer [deftest is]]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.reduce :as red]
            [ansatz.kernel.tc :as tc]))

(defn- shared-term [leaf n]
  (reduce (fn [t _] (e/app* (e/fvar 100) t t)) leaf (range n)))

(defn- shared-depth [term]
  (loop [t term depth 0]
    (if (e/app? t)
      (let [[_ [left right]] (e/get-app-fn-args t)]
        (is (identical? left right) "rewriting retains both edges to the same node")
        (recur left (inc depth)))
      [depth t])))

(deftest deeply-shared-abstraction-and-instantiation
  ;; A tree traversal would visit over 2^40 nodes. Check the result DAG itself,
  ;; rather than an elapsed-time threshold sensitive to machine contention.
  (let [term (shared-term (e/fvar 7) 40)
        abstracted (e/abstract1 term 7)
        many (e/abstract-many term [7])
        instantiated (e/instantiate1 abstracted (e/fvar 8))
        batched (e/instantiate abstracted [(e/fvar 9)])]
    (is (= [40 (e/bvar 0)] (shared-depth abstracted)))
    (is (= [40 (e/bvar 0)] (shared-depth many)))
    (is (= [40 (e/fvar 8)] (shared-depth instantiated)))
    (is (= [40 (e/fvar 9)] (shared-depth batched)))))

(deftest simultaneous-substitution-and-binder-depth
  (is (= (e/app (e/bvar 0) (e/fvar 9))
         (e/instantiate (e/app (e/bvar 1) (e/bvar 0)) [(e/bvar 0) (e/fvar 9)]))
      "substitution never rewrites the arguments themselves")
  (let [shared (e/fvar 7)
        term (e/forall' "x" shared shared :default)
        result (e/abstract1 term 7)]
    (is (= (e/bvar 0) (e/forall-type result)))
    (is (= (e/bvar 1) (e/forall-body result))))
  (let [term (e/app (e/fvar 7) (e/fvar 8))]
    (is (= (e/app (e/bvar 1) (e/bvar 0)) (e/abstract-many term [7 8])))))

(deftest deeply-shared-inference-is-linear
  (let [prop (e/sort' lvl/zero)
        st (tc/attach-lctx (tc/mk-tc-state (env/empty-env))
                           (-> (red/empty-lctx)
                               (red/lctx-add-local 100 "f" (e/arrow prop (e/arrow prop prop)))
                               (red/lctx-add-local 7 "x" prop)))
        term (shared-term (e/fvar 7) 40)
        calls (atom 0)
        infer tc/infer-type]
    (with-redefs [tc/infer-type (fn [st term] (swap! calls inc) (infer st term))]
      (is (= prop (tc/infer-type st term))))
    (is (< @calls 200) "each shared application is inferred once")
    ;; Infer a dependent binder whose inferred type contains the shared term.
    ;; This exercises instantiate1 -> infer-type -> abstract1 together.
    (let [body (shared-term (e/bvar 0) 40)
          term (e/lam "p" prop (e/lam "h" body (e/bvar 0) :default) :default)
          result (tc/infer-type st term)]
      (is (= [40 (e/bvar 0)] (shared-depth (e/forall-type (e/forall-body result))))))))

(deftest inference-cache-follows-context-and-expression-equality
  (let [prop (e/sort' lvl/zero)
        st (tc/attach-lctx (tc/mk-tc-state (env/empty-env))
                           (red/lctx-add-local {} 7 "p" prop))
        a (e/lam "x" prop (e/bvar 0) :default)
        b (e/lam "y" prop (e/bvar 0) :implicit)
        inferred (tc/infer-type st a)]
    (is (identical? inferred (tc/infer-type st b)) "Lean cache equality ignores binder names/info")
    (is (= prop (tc/infer-type st (e/fvar 7))))
    (let [other (assoc st :lctx (red/lctx-add-local {} 7 "p" (e/sort' (lvl/succ lvl/zero))))]
      (is (= (e/sort' (lvl/succ lvl/zero)) (tc/infer-type other (e/fvar 7)))))))
