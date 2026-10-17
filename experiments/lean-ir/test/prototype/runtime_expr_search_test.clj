(ns prototype.runtime-expr-search-test
  (:require [clojure.test :refer [deftest is]] [clojure.data.json :as json] [clojure.string :as str] [prototype.machine :as m]
            [prototype.raw-interop :as raw] [prototype.runtime-prim :as prim]
            [prototype.runtime-expr-search :as search]))
(def ops {:ref? m/ref? :node m/node :allocate m/allocate :retain m/retain :release m/release :replace-node m/replace-node})
(defn- ctor [world tag fields]
  (m/allocate (reduce #(m/retain %1 %2 1) world fields) :ctor tag fields))
(defn graph []
  (let [[w b] (ctor (m/world {}) 0 [0])
        [w f] (ctor w 1 [0]) [w sort] (ctor w 3 [0]) [w const] (ctor w 4 [0 0])
        [w app] (ctor w 5 [f b]) [w shared] (ctor w 5 [app app])
        [w lam] (ctor w 6 [0 sort shared])
        [w proj] (ctor w 11 [0 0 b]) [w data] (ctor w 0 [0])
        [w metadata] (ctor w 10 [data proj]) [w root] (ctor w 8 [0 const lam metadata])]
    {:world w :root root :bound b :free f :app app
     :order [root const lam sort shared app f b metadata proj b]}))
(defn execute
  ([backend fixture hit] (execute backend fixture hit {}))
  ([backend fixture hit {:keys [extended?] :as options}]
  (let [visits (atom [])
        signature {:params [{:ty "object" :borrow false}] :return-type "uint8"}
        binding {:signature signature
                 :handler (fn [_ world [value]]
                            (swap! visits conj value)
                            [(m/release world value 1) (if extended? (hit value) (if (hit value) 1 0))])}
        functions {:find {:params [1 2] :body (search/body [1 2] 3 options)}
                   :predicate {:params [1] :raw-extern {:symbol "search_test_predicate" :signature signature}
                               :body [:host "search_test_predicate" [[:var 1]] 2 [:return [:var 2]]]}}
        world (assoc (:world fixture) :functions functions)
        [world predicate] (m/allocate world :closure 0 [])
        world (assoc-in world [:heap (:id predicate) :function] :predicate)
        session (raw/open-functions functions {"search_test_predicate" binding} {:backend backend})
        original prim/evaluate
        ;; New generated operations can be tested independently of the shared
        ;; dispatcher owner; every predicate is still a genuine guest call.
        result (with-redefs [prim/evaluate (fn [ops world symbol args]
                                            (if (contains? search/internal-symbols symbol)
                                              (search/evaluate ops world symbol args)
                                              (original ops world symbol args)))]
                 (raw/call session world :find [predicate (:root fixture)]))]
    {:world world :predicate predicate :result result :visits @visits})))

(deftest preorder-native-sharing-exceptions-and-borrowed-owners
  (doseq [backend [:reference :mutable :jvm]]
    (let [fixture (graph) {:keys [world predicate result visits]} (execute backend fixture (constantly false))
          final (:state result)]
      (is (= (:order fixture) visits))
      (is (= 0 (:value result)))
      (is (= (:heap world) (:heap final)))
      (is (= 1 (:rc (m/node final predicate)))))))

(deftest first-match-stops-before-siblings-and-retains-option-field
  (doseq [backend [:reference :mutable :jvm]
          selector [:root :free :bound]]
    (let [fixture (graph) target (get fixture selector)
          {:keys [world result visits]} (execute backend fixture #(= target %))
          final (:state result) option (:value result) node (m/node final option)
          prefix (vec (take-while #(not= target %) (:order fixture)))]
      (is (= (conj prefix target) visits))
      (is (= 1 (:tag node)))
      (is (= [target] (:fields node)))
      (is (= (inc (:rc (m/node world target))) (:rc (m/node final target))))
      (is (= (:heap world) (:heap (m/release final option 1)))))))

(deftest persistent-nonleaf-nodes-are-deduplicated-but-leaves-are-not
  (let [fixture (graph) world (m/mark-persistent (:world fixture) (:root fixture))
        {:keys [result visits]} (execute :reference (assoc fixture :world world) (constantly false))]
    (is (= (:order fixture) visits))
    (is (= 0 (:value result)))
    (is (= 0 (:rc (m/node (:state result) (:app fixture)))))))

(deftest pending-search-state-is-owned-and-forkable
  (let [fixture (graph) world (:world fixture)
        [world predicate] (m/allocate world :closure 0 [])
        [world state] (search/evaluate ops world "prototype_expr_find_begin" [predicate (:root fixture)])
        [world status] (search/evaluate ops world "prototype_expr_find_advance" [state])
        [branch _] (search/evaluate ops world "prototype_expr_find_got" [state 1])
        [branch result] (search/evaluate ops branch "prototype_expr_find_finish" [state])]
    (is (= 1 status))
    (is (= (:root fixture) (first (:fields (m/node branch result)))))
    (is (contains? (:expr-search (m/node world state)) :request))
    (is (not (contains? (:heap branch) (:id state))))
    (is (= 2 (:rc (m/node world predicate))))
    (is (= 1 (:rc (m/node branch predicate))))))

(deftest extended-search-skips-partial-spines-without-caching-them
  (doseq [backend [:reference :mutable :jvm]]
    (let [fixture (graph) [root constant lambda sort shared app free bound metadata projection _] (:order fixture)
          expected [root constant lambda sort shared free bound app bound metadata projection bound]
          {:keys [world result visits]} (execute backend fixture (constantly 1) {:extended? true})]
      (is (= expected visits))
      (is (= 0 (:value result)))
      (is (= (:heap world) (:heap (:state result)))))))

(deftest extended-found-and-prune-have-distinct-native-meanings
  (doseq [backend [:reference :mutable :jvm]]
    (let [fixture (graph) [root constant lambda sort shared app free bound metadata projection _] (:order fixture)
          {:keys [result visits]} (execute backend fixture #(cond (= % shared) 2 (= % bound) 0 :else 1) {:extended? true})
          final (:state result)]
      (is (= [root constant lambda sort shared metadata projection bound] visits))
      (is (= [bound] (:fields (m/node final (:value result))))))))

(deftest native-callback-traces-and-returned-pointer-match-all-backends
  (let [cases (mapv #(json/read-str % :key-fn keyword) (str/split-lines (slurp "fixtures/runtime-expr-search.jsonl")))]
    (is (= 8 (count cases)))
    (doseq [case cases backend [:reference :mutable :jvm]]
      (let [fixture (graph)
            labels (zipmap (:order fixture) ["let" "const" "lambda" "sort" "shared-app" "app" "free" "bound" "metadata" "projection" "bound"])
            target (get fixture ({"root" :root "free" :free "bound" :bound "bound-prune" :bound} (:case case)))
            prune (when (= "bound-prune" (:case case)) (nth (:order fixture) 4))
            predicate (if (:extended case) #(cond (= % target) 0 (= % prune) 2 :else 1) #(= % target))
            {:keys [world result visits]} (execute backend fixture predicate {:extended? (:extended case)})
            final (:state result) option (:value result)
            found (when (m/ref? option) (first (:fields (m/node final option))))]
        (is (= (:visits case) (mapv labels visits)) [backend (:case case) (:extended case)])
        (is (= (:found case) (get labels found)))
        (is (= (:heap world) (:heap (m/release final option 1))))))))
