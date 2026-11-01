(ns prototype.runtime-expr-replace-test
  (:require [clojure.test :refer [deftest is]] [clojure.data.json :as json] [clojure.string :as str]
            [prototype.machine :as m] [prototype.raw-interop :as raw] [prototype.runtime-prim :as prim]
            [prototype.runtime-expr-replace :as replace] [prototype.runtime-expr-transform :as transform]
            [prototype.scalar :as scalar] [clojure.walk :as walk]
            [prototype.runtime-expr-transform-test :as transform-test]))
(def ops {:ref? m/ref? :node m/node :allocate m/allocate :retain m/retain :release m/release :replace-node m/replace-node})
(defn app [w a b]
  ;; A fresh prototype with deliberately different fields forces real cache construction.
  (let [[w seed] (m/scalar-constructor w 5 [0 0] {:objects 2 :usize 0 :ssize 8})
        [w result] (transform/rebuild ops w seed [a b])]
    [(m/release w seed 1) result]))
(defn graph []
  (let [[w b] (transform/make-bvar ops (m/world {}) 0)
        [w replacement] (transform/make-bvar ops w 1)
        [w a] (app w b b) [w root] (app w a a)]
    {:world w :root root :app a :bound b :replacement replacement}))
(defn execute [backend fixture wanted]
  (let [visits (atom [])
        signature {:params [{:ty "object" :borrow false}] :return-type "object"}
        binding {:signature signature :handler
                 (fn [_ w [value]]
                   (swap! visits conj value)
                   (let [w (m/release w value 1)]
                     (if (= value wanted)
                       (m/allocate (m/retain w (:replacement fixture) 1) :ctor 1 [(:replacement fixture)]) [w 0])))}
        functions {:replace {:params [1 2] :body (replace/body [1 2] 3)}
                   :callback {:params [1] :raw-extern {:symbol "replace_test_callback" :signature signature}
                              :body [:host "replace_test_callback" [[:var 1]] 2 [:return [:var 2]]]}}
        w (assoc (:world fixture) :functions functions)
        [w callback] (m/allocate w :closure 0 []) w (assoc-in w [:heap (:id callback) :function] :callback)
        session (raw/open-functions functions {"replace_test_callback" binding} {:backend backend}) original prim/evaluate
        result (with-redefs [prim/evaluate (fn [ops w symbol args]
                                            (if (contains? replace/internal-symbols symbol) (replace/evaluate ops w symbol args)
                                              (original ops w symbol args)))]
                 (raw/call session w :replace [callback (:root fixture)]))]
    {:world w :result result :visits @visits}))
(deftest callback-preorder-cache-and-stop-match-native-oracle
  (let [rows (mapv #(json/read-str % :key-fn keyword) (str/split-lines (slurp "fixtures/runtime-expr-replace.jsonl")))]
    (doseq [backend [:reference :mutable :jvm] row rows]
      (let [fixture (graph) wanted (get fixture ({"root" :root "app" :app "bound" :bound} (:case row)))
            {:keys [world result visits]} (execute backend fixture wanted)
            w (:state result) value (:value result)
            labels (zipmap (map fixture [:root :app :bound]) ["root" "app" "bound"])
            n (m/node w value)
            cache (scalar/read-bytes (:layout n) (:scalar-bytes n) {:index (count (:fields n)) :offset 0 :type "uint64" :region :scalar})]
        (is (= (:visits row) (mapv labels visits)) [backend (:case row)])
        (is (= (:unchanged row) (= value (:root fixture))))
        (is (= (bigint (:data row)) cache))
        (when (= "bound" (:case row)) (is (apply = (:fields n))))
        (is (= (:heap world) (:heap (m/release w value 1))))))))
(deftest pending-callback-state-forks-with-owned-results
  (let [f (graph) [w callback] (m/allocate (:world f) :closure 0 [])
        [w state] (replace/evaluate ops w "prototype_expr_replace_begin" [callback (:root f)])
        [w status] (replace/evaluate ops w "prototype_expr_replace_advance" [state])
        [branch option] (m/allocate (m/retain w (:replacement f) 1) :ctor 1 [(:replacement f)])
        [branch _] (replace/evaluate ops branch "prototype_expr_replace_got" [state option])
        [branch _] (replace/evaluate ops branch "prototype_expr_replace_advance" [state])
        [branch result] (replace/evaluate ops branch "prototype_expr_replace_finish" [state])]
    (is (= 1 status)) (is (= (:replacement f) result))
    (is (some? (get-in (m/node w state) [:expr-replace :request])))
    (is (not (contains? (:heap branch) (:id state))))
    (is (= (:heap (:world f)) (:heap (-> branch (m/release result 1) (m/release callback 1)))))))
(deftest deep-no-op-traversal-is-stack-safe
  (let [[w b] (transform/make-bvar ops (m/world {}) 0)
        [w root] (loop [w w r b n 3000]
                   (if (zero? n) [w r]
                     (let [[w a] (app w r b)] (recur w a (dec n)))))
        [w callback] (m/allocate w :closure 0 []) before w
        [w state] (replace/evaluate ops w "prototype_expr_replace_begin" [callback root])
        [w result calls]
        (loop [w w calls 0]
          (let [[w status] (replace/evaluate ops w "prototype_expr_replace_advance" [state])]
            (if (zero? status)
              (let [[w result] (replace/evaluate ops w "prototype_expr_replace_finish" [state])] [w result calls])
              (let [[w candidate] (replace/evaluate ops w "prototype_expr_replace_candidate" [state])
                    w (m/release w candidate 1)
                    [w _] (replace/evaluate ops w "prototype_expr_replace_got" [state 0])]
                (recur w (inc calls))))))]
    (is (= 3001 calls)) (is (= root result))
    (is (= (:heap before) (:heap (m/release w result 1))))))
(deftest generated-guest-loop-resumes-from-identical-paused-forks
  (let [f (graph)
        functions {:replace {:params [1 2] :body (replace/body [1 2] 3)}
                   :callback {:params [1] :body [:dec [:var 1] 1 [:return [:imm 0]]]}}
        [w callback] (m/allocate (assoc (:world f) :functions functions) :closure 0 [])
        w (assoc-in w [:heap (:id callback) :function] :callback) original prim/evaluate]
    (with-redefs [prim/evaluate (fn [ops w symbol args]
                                (if (contains? replace/internal-symbols symbol) (replace/evaluate ops w symbol args)
                                  (original ops w symbol args)))]
      (let [paused (m/run (m/start w :replace [callback (:root f)]) 8)
            finish (fn [s] (loop [s s]
                             (if (= :paused (:status s)) (recur (m/run (m/resume s 0) 7)) s)))
            left (finish paused) right (finish paused)]
        (is (= :paused (:status paused)))
        (is (= :done (:status left)))
        (is (= (:root f) (:result left)))
        (is (= left right))
        (is (= (:heap w) (:heap (m/release left (:result left) 1))))))))
(defn assert-native-sharing [w value descriptor identities]
  (when (= "expr" (:kind descriptor))
    (if-let [expected (get @identities (:nodeId descriptor))]
      (is (= expected value) [:native-node (:nodeId descriptor)])
      (swap! identities assoc (:nodeId descriptor) value))
    (doseq [i (case (:tag descriptor) 5 [0 1] (6 7) [1 2] 8 [1 2 3] 10 [1] 11 [2] [])]
      (assert-native-sharing w (nth (:fields (m/node w value)) i) (nth (:fields descriptor) i) identities))))
(deftest native-binders-let-metadata-projection-and-returned-descendant-aliases
  (let [rows (mapv #(json/read-str % :key-fn keyword)
                   (str/split-lines (slurp "fixtures/runtime-expr-replace-structures.jsonl")))]
    (is (= 7 (count rows)))
    (doseq [row rows backend [:reference :mutable :jvm]]
      (let [cache (atom {})
            [w root target replacement]
            (with-bindings {#'transform-test/*build-cache* cache}
              (let [[w root] (transform-test/build (m/world {}) (:input row))
                    [w target] (transform-test/build w (:target row))
                    [w replacement] (transform-test/build w (:replacement row))]
                [w root target replacement]))
            {:keys [world result visits]} (execute backend {:world w :root root :replacement replacement} target)
            w (:state result) value (:value result)
            expected-visits (mapv #(get @cache (:nodeId %)) (:visits row))]
        (is (= expected-visits visits) [backend (:label row)])
        (is (= (:sameRoot row) (= root value)))
        (is (= (walk/postwalk #(if (map? %) (dissoc % :nodeId) %) (:output row))
               (transform-test/normalized w value)) [backend (:label row)])
        (assert-native-sharing w value (:output row) (atom @cache))
        (is (= (:heap world) (:heap (m/release w value 1))))))))
