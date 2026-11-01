(ns ansatz.research.ir.bootstrap.source4-models
  "Pure retirement checks; factory latching and real engine disposal are NOT
   simulated as runtime acceptance. No engine/source/store is opened."
  (:require [clojure.test :refer [deftest is run-tests]]
            [ansatz.research.ir.bootstrap.source4 :as source4]))
(deftest a-caller-journal-is-never-child-retirement-authority
  (let [source (Object.) engine (Object.) child {:driver {:engine engine :source source}}
        journal (atom {:retirement {:status :disposed-and-closed}})
        child-slot (object-array [child]) engine-slot (object-array [engine])
        record {:journal journal :child-slot child-slot :engine-slot engine-slot}
        s {:parent {:driver {:source source}}}
        flags (atom {"disposed" false "closed" false})]
    (with-redefs-fn {#'source4/field (fn [_ name] (get @flags name))}
      (fn []
        (is (thrown? Exception (#'source4/retired-child! s record)))
        (swap! flags assoc "disposed" true)
        (is (thrown? Exception (#'source4/retired-child! s record)))
        (swap! flags assoc "closed" true)
        (is (nil? (#'source4/retired-child! s record)))
        (reset! journal {:retirement {:status :not-retired}})
        (is (thrown? Exception (#'source4/retired-child! s record)))
        (reset! journal {:retirement {:status :disposed-and-closed} :child {:driver {:engine (Object.)}}})
        (is (nil? (#'source4/retired-child! s record)))
        (aset engine-slot 0 (Object.))
        (is (thrown? Exception (#'source4/retired-child! s record)))
        (aset engine-slot 0 engine) (aset child-slot 0 nil)
        (is (thrown? Exception (#'source4/retired-child! s record)))
        (aset child-slot 0 (assoc-in child [:driver :source] (Object.)))
        (is (thrown? Exception (#'source4/retired-child! s record)))))))
(deftest diagnostic-packet-does-not-expose-private-retirement-latches
  (let [e (Object.) record {:journal (atom {:stage :prepared})
                            :child-slot (object-array [{:driver {:engine e}}])
                            :engine-slot (object-array [e])}
        holder (atom {:status :ready :journal (atom {}) :children [record]})
        token (source4/->Bootstrap)]
    (locking @#'source4/bootstraps (.put ^java.util.WeakHashMap @#'source4/bootstraps token holder))
    (let [packet (source4/owner-packet token) child (first (:children packet))]
      (is (= #{:journal :engine} (set (keys child))))
      (is (identical? e (:engine child)))
      (is (not (contains? child :child-slot)))
      (is (not (contains? child :engine-slot))))))

(defn check! [] (run-tests 'ansatz.research.ir.bootstrap.source4-models))
