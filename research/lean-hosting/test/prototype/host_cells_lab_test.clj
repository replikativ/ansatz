(ns prototype.host-cells-lab-test
  (:require [clojure.test :refer [deftest is]]
            [prototype.branch-lab :as lab]
            [prototype.branch-lab-test :refer [rejected?]]
            [prototype.host-cells-lab :as cells]
            [prototype.machine :as m]
            [prototype.mutable :as u]))

(defn fixture []
  (let [[store cell] (cells/allocate (cells/store) 0)
        ;; Pass handles as runtime values, so code/cache identity never embeds
        ;; the store's opaque allocation tokens.
        functions {:entry {:params [4]
                           :body [:suspend 0
                                  [:host :lab/cell-write [[:var 4] [:var 0]] 1
                                   [:host :lab/cell-read [[:var 4]] 2
                                    [:host :lab/emit [[:var 2]] 3 [:return [:var 2]]]]]]}}]
    {:world (m/run (m/start (m/world functions) :entry [cell]))
     :functions functions :store store :cell cell}))

(defn run-pair
  ([fixture backend scoped?] (run-pair fixture backend scoped? 10 20))
  ([fixture backend scoped? left right]
  (let [{:keys [world functions store]} fixture
        session (lab/session world {:version 1} store)
        [a b] (lab/fork! session (:initial session))
        run ((if scoped? lab/scoped-runner lab/runner) backend functions)
        advance! (if scoped? lab/advance-scoped! lab/advance!)
        a (advance! session a run left) b (advance! session b run right)]
    [(lab/snapshot session a) (lab/snapshot session b)])))

(deftest host-cells-and-captured-identities-are-branch-local
  (let [{:keys [store cell] :as f} (fixture)
        captured (fn [packet] (cells/read (:host-store packet) cell))
        results (for [backend [:persistent :mutable :compiled] scoped? [false true]]
                  (run-pair f backend scoped?))]
    (is (apply = results))
    (doseq [pair results]
      (is (= [10 20] (mapv captured pair)))
      (is (= [10 20] (mapv #(get-in % [:world :result]) pair)))
      (is (= [[10] [20]] (mapv :outbox pair))))
    (is (= 0 (cells/read store cell)))))

(deftest private-execution-does-not-freeze-at-internal-cell-requests
  (let [{:keys [world functions store]} (fixture)
        freeze u/freeze]
    (doseq [backend [:mutable :compiled] scoped? [false true]]
      (let [session (lab/session world {} store)
            run ((if scoped? lab/scoped-runner lab/runner) backend functions)
            calls (atom 0)]
        (with-redefs [u/freeze (fn [machine] (swap! calls inc) (freeze machine))]
          ((if scoped? lab/advance-scoped! lab/advance!) session (:initial session) run 10))
        (is (= (if scoped? 1 4) @calls))))))

(deftest cells-reject-foreign-identities-and-mutable-host-payloads
  (let [[store cell] (cells/allocate (cells/store) 1)
        [foreign other] (cells/allocate (cells/store) 2)]
    (is (rejected? #(cells/read store other)))
    (is (rejected? #(cells/write foreign cell 3)))
    (is (rejected? #(cells/allocate store (atom 0))))
    (is (rejected? #(cells/write store cell (Object.))))
    (is (= 1 (cells/read store cell)))))

(deftest sibling-allocations-cannot-alias-by-reusing-a-local-index
  (let [[parent inherited] (cells/allocate (cells/store) 0)
        [left a] (cells/allocate parent 10)
        [right b] (cells/allocate parent 20)]
    (is (= (:id a) (:id b)))
    (is (not= a b))
    (is (= [10 20] [(cells/read left a) (cells/read right b)]))
    (is (rejected? #(cells/read left b)))
    (is (rejected? #(cells/write right a 99)))
    (is (= [0 0 0] (mapv #(cells/read % inherited) [parent left right])))))

(deftest scoped-execution-still-materializes-a-forkable-suspension
  (let [{:keys [world functions store cell]} (fixture)
        ;; Same 3 requests, but expose a suspension before returning the result.
        functions (assoc-in functions [:entry :body 2 4 4 4]
                            [:suspend 4 [:return [:var 2]]])
        world (m/run (m/start (assoc world :functions functions) :entry [cell]))]
    (doseq [backend [:persistent :mutable :compiled]]
      (let [session (lab/session world {} store)
            run (lab/scoped-runner backend functions)
            h (lab/advance-scoped! session (:initial session) run 10)
            captured (lab/snapshot session h)
            [a b] (lab/fork! session h)
            a (lab/advance-scoped! session a run nil)
            b (lab/advance-scoped! session b run nil)]
        (is (= :suspended (get-in captured [:world :status])))
        (is (= 10 (cells/read (:host-store captured) cell)))
        (is (= captured (assoc (lab/snapshot session a) :world (:world captured))))
        (is (= (lab/snapshot session a) (lab/snapshot session b)))))))

(deftest scoped-adapter-does-not-fallback-on-an-unknown-effect
  (let [{:keys [world functions store cell]} (fixture)
        functions (assoc-in functions [:entry :body 2 1] :unknown)
        world (m/run (m/start (assoc world :functions functions) :entry [cell]))]
    (doseq [backend [:persistent :mutable :compiled]]
      (let [session (lab/session world {} store)]
        (is (rejected? #(lab/advance-scoped! session (:initial session)
                                           (lab/scoped-runner backend functions) 10)))
        (is (= :incomplete (:family @(:ledger session))))))))
