(ns prototype.heap-snapshot-test
  (:require [clojure.test :refer [deftest is]]
            [prototype.heap-snapshot :as hints]
            [prototype.machine :as m] [prototype.mutable :as u] [prototype.raw-interop])
  (:import [java.lang.ref WeakReference] [java.util Map HashMap]))

(defn- sample [n]
  (reduce (fn [world _] (first (m/allocate world :ctor 0 [1]))) (m/world {}) (range n)))

(deftest exact-canonical-identity-skips-validation-after-first-thaw
  (hints/clear-cache!)
  (let [world (sample 100) scans (atom 0) canonical? hints/storage-node?]
    (with-redefs [hints/storage-node? (fn [node] (swap! scans inc) (canonical? node))]
      (let [first-state (u/thaw world)]
        (is (= 100 @scans))
        (is (= {:long-keys? true} (hints/proof (:heap world))))
        (reset! scans 0)
        (let [other (u/thaw world)]
          (is (zero? @scans))
          (is (identical? (:heap world) (:heap (u/freeze other))))
          (is (= (u/freeze first-state) (u/freeze other)))))
      ;; Equal data with a new persistent root identity is NOT a hint hit.
      (let [different (with-meta (:heap world) {:new-root true})]
        (is (= (:heap world) different))
        (is (nil? (hints/proof different)))
        (u/thaw (assoc world :heap different))
        (is (= 100 @scans))))))

(deftest dirty-freeze-attests-only-changed-nodes-and-preserves-forks
  (hints/clear-cache!)
  (let [world (sample 100) left (u/thaw world) right (u/thaw world)
        calls (atom 0) canonical? hints/storage-node?]
    (u/store! left (m/->Ref 0) 0 42)
    (with-redefs [hints/storage-node? (fn [node] (swap! calls inc) (canonical? node))]
      (let [frozen (u/freeze left)]
        (is (= 1 @calls))
        (is (= {:long-keys? true} (hints/proof (:heap frozen))))
        (is (= [42] (:fields (m/node frozen (m/->Ref 0)))))
        (reset! calls 0)
        (is (= frozen (u/freeze (u/thaw frozen))))
        (is (zero? @calls))
        (u/store! left (m/->Ref 0) 0 43)
        (u/store! right (m/->Ref 0) 0 44)
        (is (= [42] (:fields (m/node frozen (m/->Ref 0)))))
        (is (= [1] (:fields (m/node world (m/->Ref 0)))))
        (is (= [43] (:fields (m/node (u/freeze left) (m/->Ref 0)))))
        (is (= [44] (:fields (m/node (u/freeze right) (m/->Ref 0)))))))))

(deftest full-reconstruction-attests-during-existing-pass
  (hints/clear-cache!)
  (let [world (sample 2) state (u/thaw world)]
    (u/store! state (m/->Ref 0) 0 2)
    (u/store! state (m/->Ref 1) 0 3)
    (let [frozen (u/freeze state)]
      (is (some? (hints/proof (:heap frozen))))
      (with-redefs [hints/storage-node? (fn [_] (throw (Exception. "unexpected rescan")))]
        (is (= frozen (u/freeze (u/thaw frozen))))))))

(deftest external-array-fields-and-custom-maps-never-gain-unsafe-hints
  (hints/clear-cache!)
  (let [world (sample 1) array (object-array [1])
        external (assoc-in world [:heap 0 :fields] array)
        left (u/thaw external) right (u/thaw external) captured (u/freeze left)]
    (is (nil? (hints/proof (:heap external))))
    (is (some? (hints/proof (:heap captured))))
    (aset array 0 9)
    (is (= 1 (u/project right (m/->Ref 0) 0)))
    (is (= [1] (:fields (m/node captured (m/->Ref 0)))))
    (is (= 9 (u/project (u/thaw external) (m/->Ref 0) 0))))
  (let [heap (into (sorted-map) (:heap (sample 2)))]
    (u/thaw (assoc (sample 2) :heap heap))
    (is (nil? (hints/proof heap)))))

(deftest nonlong-key-proof-does-not-change-java-map-key-equality
  (hints/clear-cache!)
  (let [integer-key (Integer/valueOf 1)
        heap (assoc {} integer-key {:kind :ctor :tag 0 :fields [] :rc 1})
        world (assoc (m/world {}) :heap heap)
        first-state (u/thaw world) second-state (u/thaw world)]
    (is (= {:long-keys? false} (hints/proof heap)))
    (doseq [state [first-state second-state]]
      (is (.containsKey ^Map (:heap state) integer-key))
      (is (not (.containsKey ^Map (:heap state) (Long/valueOf 1)))))
    (is (identical? heap (:heap (u/freeze second-state))))))

(deftest cache-is-bounded-and-holds-only-weak-root-identities-and-scalar-proofs
  (hints/clear-cache!)
  (let [heap (:heap (sample 1))]
    (u/thaw (assoc (m/world {}) :heap heap))
    (let [table @#'prototype.heap-snapshot/hints
          entries (mapcat seq (.values ^HashMap (:buckets table)))]
      (is (= 1 (count entries)))
      (doseq [[reference proof] entries]
        (is (instance? WeakReference reference))
        (is (instance? Boolean proof))
        (is (identical? heap (.get ^WeakReference reference)))
        ;; Model weak collection without timing-dependent GC assertions.
        (.clear ^WeakReference reference))
      (is (nil? (hints/proof heap)))))
  (dotimes [i 300]
    (let [heap {(long i) {:kind :ctor :tag 0 :fields [] :rc 1}}]
      (hints/remember! heap true)))
  (is (<= (:entries (hints/cache-summary)) (:limit (hints/cache-summary)))))

(deftest immutable-boolean-false-literals-and-task-flags-qualify
  (hints/clear-cache!)
  (let [node {:kind :task :tag 252 :rc 1 :fields [false true]
              :cancelled? false :keep-alive? false :queued? false :sync? false}
        heap {0 node} world (assoc (m/world {}) :heap heap)]
    (is (hints/canonical-node? node))
    (u/thaw world)
    (is (= {:long-keys? true} (hints/proof heap)))
    (with-redefs [hints/storage-node? (fn [_] (throw (Exception. "unexpected boolean heap rescan")))]
      (is (identical? heap (:heap (u/freeze (u/thaw world)))))))
  ;; The correction admits only the existing exact immutable scalar whitelist.
  (doseq [value [(atom false) (object-array [false]) (java.util.concurrent.atomic.AtomicInteger. 0)]]
    (is (not (hints/canonical-node? {:kind :task :tag 252 :rc 1 :fields [] :flag value}))))
)

(deftest storage-proof-is-not-deep-payload-immutability
  (let [opaque (atom 1) node {:kind :ctor :tag 0 :fields [opaque] :rc 1}]
    (is (not (hints/canonical-node? node)))
    ;; Old COW already shared elements of a fixed persistent vector. The runtime
    ;; storage hint only proves it need not defensively copy an Object[] shell.
    (is (hints/storage-node? node))))

(deftest reference-cell-operations-propagate-storage-proof-without-full-scans
  (hints/clear-cache!)
  (let [world (sample 30) _ (u/thaw world)
        check (fn [state] (is (some? (hints/proof (:heap state)))) state)
        resource (m/->Ref 0)
        world (check (m/retain world resource 1))
        world (check (m/release world resource 1))
        [world ref] (m/allocate world :ctor 0 [42]) world (check world)
        world (check (m/replace-node world ref (assoc (m/node world ref) :tag 1)))
        world (check (m/set-constructor-tag world ref 2))
        [world scalar] (m/scalar-constructor world 0 [] {:objects 0 :usize 0 :ssize 8})
        world (check world)
        [world boxed] (m/box-value world "uint64" 42)
        world (check world)
        [world closure] (m/expr world [:closure ["str" ["anonymous"] "f"] []])
        world (check world)
        world (check (m/mark-persistent world ref))
        world (check (m/delete-shell world (m/->Ref 1)))]
    (with-redefs [hints/storage-node? (fn [_] (throw (Exception. "reference cleanup lost storage proof")))]
      (is (identical? (:heap world) (:heap (u/freeze (u/thaw world))))))))

(deftest real-raw-host-cleanup-preserves-warm-heap-proof-on-all-backends
  (doseq [backend [:reference :mutable :jvm]]
    (hints/clear-cache!)
    (let [symbol "heap_hint_host_cleanup"
          name ["str" ["anonymous"] "hostCleanup"]
          signature {:params [{:ty "object" :borrow false}] :return-type "object"}
          check (fn [world] (is (some? (hints/proof (:heap world)))) world)
          binding {:signature signature
                   :handler (fn [_ world [value]]
                              (let [world (check (m/retain world value 1))
                                    [world scratch] (m/allocate world :ctor 0 [value])
                                    world (check world)
                                    world (check (m/replace-node world scratch (m/node world scratch)))
                                    world (check (m/release world scratch 1))
                                    world (check (m/release world value 1))
                                    [world result] (m/allocate world :ctor 0 [42])]
                                [(check world) result]))}
          functions {name {:params [1] :raw-extern {:symbol symbol :signature signature}
                           :body [:host symbol [[:var 1]] 2 [:return [:var 2]]]}}
          [world input] (m/resource (m/world functions) "owned")
          _ (u/thaw world)
          session (prototype.raw-interop/open-functions functions {symbol binding} {:backend backend})
          scans (atom 0) storage? hints/storage-node?
          result (with-redefs [hints/storage-node? (fn [node] (swap! scans inc) (storage? node))]
                   (prototype.raw-interop/call session world name [input]))]
      (is (zero? @scans))
      (is (= [42] (:fields (m/node (:state result) (:value result)))))
      (is (= [[:released "owned"]] (:events (:state result))))
      (is (= 1 (:rc (m/node (:state result) (:value result)))))
      (is (= 1 (:rc (m/node world input)))))))

(deftest nil-association-is-not-a-deletion-proof
  (hints/clear-cache!)
  (let [world (sample 1) _ (u/thaw world)
        invalid (m/replace-node world (m/->Ref 0) nil)
        scans (atom 0) storage? hints/storage-node?]
    (is (contains? (:heap invalid) 0))
    (is (nil? (get (:heap invalid) 0)))
    (is (nil? (hints/proof (:heap invalid))))
    ;; The legacy defensive path sees nonvector nil fields, materializes private
    ;; empty Object[] storage, and freezes that normalized node. Hinting the nil
    ;; association as a deletion would incorrectly skip that conversion.
    (let [frozen (with-redefs [hints/storage-node? (fn [node] (swap! scans inc) (storage? node))]
                   (u/freeze (u/thaw invalid)))]
      (is (pos? @scans))
      (is (= {0 {:fields []}} (:heap frozen))))
    (is (= [1] (:fields (m/node world (m/->Ref 0)))))))
