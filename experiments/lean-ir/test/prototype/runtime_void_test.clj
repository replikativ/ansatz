(ns prototype.runtime-void-test
  (:require [clojure.test :refer [deftest is]]
            [prototype.machine :as m] [prototype.raw-interop :as raw]
            [prototype.runtime-abi :as abi]))

(def root ["str" ["str" ["anonymous"] "Void"] "mk"])
(def row
  ;; Exact pinned Init.System.ST extern; C erases the first type parameter.
  {:name root :ir {:extern {:f root :xs [{:x {:idx 1} :ty "erased" :borrow false}
                                        {:x {:idx 2} :ty "tobject" :borrow false}]
                            :type "void" :ext {:entries [{:standard {:backend ["str" ["anonymous"] "all"]
                                                                 :fn "lean_void_mk"}}]}}}})

(deftest void-consumes-only-its-owned-payload-and-preserves-forks
  (doseq [backend [:reference :mutable :jvm] rc [0 1 2]]
    (let [functions (into {} [(abi/lower row)])
          [world child] (m/allocate (m/world functions) :ctor 0 [])
          [world payload] (m/allocate world :ctor 1 [child])
          world (case rc 0 (m/mark-persistent world payload) 1 world 2 (m/retain world payload 1))
          session (raw/open-functions functions {} {:backend backend})
          a (raw/call session world root [m/erased payload])
          b (raw/call session world root [m/erased payload])]
      (is (= m/erased (:value a) (:value b)))
      (is (= (:state a) (:state b)))
      (is (= rc (:rc (m/node world payload))))
      (if (= 1 rc)
        (do (is (not (contains? (:heap (:state a)) (:id payload))))
            (is (not (contains? (:heap (:state a)) (:id child)))))
        (is (= (max 0 (dec rc)) (:rc (m/node (:state a) payload))))))))

(deftest void-also-accepts-the-immediate-unit-state
  (doseq [backend [:reference :mutable :jvm]]
    (let [functions (into {} [(abi/lower row)])
          world (m/world functions)
          result (raw/call (raw/open-functions functions {} {:backend backend}) world root [m/erased (m/->Tag 0)])]
      (is (= m/erased (:value result)))
      (is (empty? (get-in result [:state :heap]))))))
