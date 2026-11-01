(ns prototype.persistent-snapshot-test
  (:require [clojure.test :refer [deftest is]]
            [prototype.machine :as m]
            [prototype.mutable :as u]
            [prototype.raw-interop :as raw]))

(deftest authenticated-import-prefix-survives-execution-and-remains-fork-local
  (doseq [backend [:reference :mutable :jvm]]
    (let [functions {"read" {:params [] :body [:return [:imm 42]]}
                     "drop" {:params [] :body [:host "drop_prefix" [] 0 [:return [:var 0]]]}}
          [seed root] (m/allocate (m/world functions) :ctor 0 [])
          prefix {:state root :token (Object.)}
          ledger {(:id root) prefix}
          seed (assoc seed :source-import-prefixes ledger)
          binding {:signature {:params [] :return-type "object"}
                   :handler (fn [_ world _]
                              (is (identical? prefix (get-in world [:source-import-prefixes (:id root)])))
                              [(-> world (update :source-import-prefixes dissoc (:id root))
                                         (m/release root 1)) 42])}
          session (raw/open-functions functions {"drop_prefix" binding} {:backend backend :fuel 100})
          read-result (raw/call session seed "read" [])
          dropped (raw/call (:session read-result) (:state read-result) "drop" [])]
      (is (= 42 (:value read-result) (:value dropped)))
      (is (identical? ledger (get-in read-result [:state :source-import-prefixes])))
      (is (empty? (get-in dropped [:state :source-import-prefixes])))
      (is (thrown? clojure.lang.ExceptionInfo (m/node (:state dropped) root)))
      (is (identical? prefix (get-in seed [:source-import-prefixes (:id root)])))
      (is (= :ctor (:kind (m/node seed root)))))))

(deftest persistent-storage-is-shared-without-copying-writable-fields
  (let [[world persistent] (m/allocate (m/world {}) :ctor 0 [42])
        world (m/mark-persistent world persistent)
        [world unique] (m/allocate world :ctor 0 [7])
        left (u/thaw world) right (u/thaw world)
        frozen (u/freeze left)]
    (is (identical? (m/node world persistent) (m/node frozen persistent)))
    (u/store! left unique 0 8)
    (is (= [8] (:fields (m/node (u/freeze left) unique))))
    (is (= world (select-keys (u/freeze right) (keys world))))
    (is (= [7] (:fields (m/node frozen unique))))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Invalid unique field store"
          (u/store! left persistent 0 9)))
    (is (= [42] (:fields (m/node world persistent))))))

(deftest persistent-reference-updates-replace-storage-in-each-fork
  (let [[world old] (m/allocate (m/world {}) :ctor 0 [1])
        [world ref] (m/allocate world :ref 253 [old])
        world (m/mark-persistent world ref)
        [world replacement] (m/allocate world :ctor 0 [2])
        left (u/thaw world) right (u/thaw world)]
    (u/runtime-value! left "lean_st_ref_set" [m/erased m/erased ref replacement m/erased])
    (let [frozen (u/freeze left)]
      (is (= [replacement] (:fields (m/node frozen ref))))
      (is (= [old] (:fields (m/node world ref))))
      (is (= world (select-keys (u/freeze right) (keys world))))
      (is (= 0 (:rc (m/node frozen ref))))
      (is (= 1 (:rc (m/node frozen replacement))))
      ;; A later write in the same child cannot alter its earlier snapshot.
      (u/runtime-value! left "lean_st_ref_set" [m/erased m/erased ref 17 m/erased])
      (is (= [replacement] (:fields (m/node frozen ref))))
      (is (= [17] (:fields (m/node (u/freeze left) ref)))))
    (is (= [old] (:fields (m/node (u/freeze right) ref))))))

(deftest newly-persistent-arrays-are-copied-when-first-frozen
  (let [[world child] (m/allocate (m/world {}) :ctor 0 [1])
        state (u/thaw world)]
    (u/mark-persistent! state child)
    (let [frozen (u/freeze state)]
      (is (= 0 (:rc (m/node frozen child))))
      (is (vector? (:fields (m/node frozen child))))
      (is (= frozen (u/freeze (u/thaw frozen)))))))

(deftest initialized-io-result-can-use-immutable-persistent-fields
  (let [[world value] (m/allocate (m/world {}) :ctor 0 [42])
        [world result] (m/allocate world :ctor 0 [value])
        world (m/mark-persistent world result)
        state (u/thaw world)]
    (u/publish-io-global! state ["value"] "object" result)
    (is (= {:status :ready :value value}
           (get-in (u/freeze state) [:globals ["value"]])))
    (is (= [value] (:fields (m/node world result))))))

(deftest sparse-snapshot-updates-preserve-old-world-and-reuse-unchanged-heap
  (let [[world refs] (reduce (fn [[world refs] i]
                              (let [[world ref] (m/allocate world :ctor 0 [i])]
                                [world (conj refs ref)])) [(m/world {}) []] (range 1000))
        machine (u/thaw world)
        old-heap (:heap world)]
    (is (identical? old-heap (:heap (u/freeze machine))))
    (u/store! machine (refs 17) 0 42)
    (u/release! machine (refs 18) 1)
    (let [first-snapshot (u/freeze machine)]
      (is (= [42] (:fields (m/node first-snapshot (refs 17)))))
      (is (not (contains? (:heap first-snapshot) (:id (refs 18)))))
      (is (= [17] (:fields (m/node world (refs 17)))))
      (is (contains? old-heap (:id (refs 18))))
      (is (identical? (m/node world (refs 19)) (m/node first-snapshot (refs 19))))
      (u/store! machine (refs 17) 0 43)
      (let [second-snapshot (u/freeze machine)]
        (is (= [42] (:fields (m/node first-snapshot (refs 17)))))
        (is (= [43] (:fields (m/node second-snapshot (refs 17)))))
        (is (= (:heap second-snapshot)
               (:heap (u/freeze (dissoc machine :heap-base :heap-dirty)))))))))
