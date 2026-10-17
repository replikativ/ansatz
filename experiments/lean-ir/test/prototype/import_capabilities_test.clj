(ns prototype.import-capabilities-test
  (:require [clojure.test :refer [deftest is]] [prototype.import-capabilities :as capability]
            [prototype.module-import :as module-import] [prototype.module-data :as data]
            [prototype.module-store :as store] [prototype.import-ir :as ir]
            [prototype.scalar :as scalar] [prototype.raw-interop :as raw] [prototype.machine :as m])
  (:import [java.io Closeable]))

(def backends [:reference :mutable :jvm])
(def read-name ["str" ["str" ["str" ["anonymous"] "Lean"] "CompactedRegion"] "read"])
(def free-name ["str" ["str" ["str" ["anonymous"] "Lean"] "CompactedRegion"] "free"])
(def mark-name ["str" ["str" ["anonymous"] "Runtime"] "markPersistent"])
(defn row [name symbol signature]
  {:name name :ir {:extern {:f name :xs (mapv #(assoc %1 :x {:idx %2}) (:params signature) (range 1 10))
                            :type (:return-type signature)
                            :ext {:entries [{:standard {:backend ["str" ["anonymous"] "all"] :fn symbol}}]}}}})
(defn loaded [] (data/load-file (m/world {}) "fixtures/imported-kernel-native.jsonl"))
(defn program [bindings]
  (merge (ir/load-bundle "fixtures/import-capability-helpers.jsonl")
         (into {} (for [[name symbol] [[read-name "lean_compacted_region_read"] [free-name "lean_compacted_region_free"] [mark-name "lean_runtime_mark_persistent"]]]
                    (raw/lower bindings (row name symbol (get capability/signatures symbol)))))))
(defn session [loaded backend]
  (let [bindings (capability/make-bindings loaded) functions (program bindings)]
    [(assoc (:world loaded) :functions functions) (raw/open-functions functions bindings {:backend backend :fuel 10000})]))
(defn read-part [loaded backend]
  (let [[world session] (session loaded backend)
        path (get-in loaded [:modules 0 :parts 0 :artifact :filePath])
        [world deps] (m/allocate world :array 246 [])
        result (raw/call session world read-name [m/erased path deps m/erased])
        world (:state result) io-result (:value result)
        pair (first (:fields (m/node world io-result)))
        region (second (:fields (m/node world pair)))]
    {:world world :session session :deps deps :io-result io-result :pair pair :region region}))

(deftest reads-execute-the-real-exported-guest-constructor-with-owned-result
  ;; mkVirtualPart IR is copied unchanged from the pinned local-source exporter;
  ;; this nested callback runs its real scalar stores and RC operations.
  (doseq [backend backends]
    (let [loaded (loaded) before (:world loaded)
          {:keys [world deps io-result pair region]} (read-part loaded backend)
          node (m/node world region)
          released (-> world (m/release io-result 1) (m/release deps 1))]
      (is (= (first (:roots loaded)) (first (:fields (m/node world pair)))))
      (is (= {:objects 2 :usize 3 :ssize 1} (:layout node)))
      (is (= 1 (:rc node)))
      (is (= 0 (m/read-scalar-node node {:index 3 :offset 0 :type "usize" :region :usize})))
      (is (= 0 (m/read-scalar-node node {:index 5 :offset 0 :type "uint8" :region :scalar})))
      (is (> (get-in world [:stats :steps]) 10))
      (is (= (:heap before) (:heap released))))))

(deftest virtual-free-consumes-only-metadata-and-invalidates-aliases-in-this-fork
  (doseq [backend backends]
    (let [loaded (loaded)
          {:keys [world session deps io-result region]} (read-part loaded backend)
          ;; Pair keeps one region owner, extra owner transfers to free.
          world (m/retain world region 1)
          freed (raw/call session world free-name [region m/erased])
          after (:state freed) unit (:value freed)
          released (-> after (m/release unit 1) (m/release io-result 1) (m/release deps 1))]
      (is (= [0] (:fields (m/node after unit))))
      (is (= 0 (second (:fields (m/node after region)))))
      (is (= 1 (:rc (m/node after region))))
      (is (= (first (:roots loaded)) (second (:fields (m/node world region)))))
      (is (= (:heap (:world loaded)) (:heap released)))
      (is (thrown-with-msg? Exception #"Unregistered, freed"
            (raw/call session after free-name [region m/erased]))))))

(deftest unregistered-paths-dependencies-and-native-addresses-fail-explicitly
  (doseq [backend backends]
    (let [loaded (loaded)
          {:keys [world session deps region]} (read-part loaded backend)
          path (get-in loaded [:modules 0 :parts 0 :artifact :filePath])
          [world wrong-deps] (m/allocate (m/retain world region 1) :array 246 [region])
          node (m/node world region)
          bad (assoc-in world [:heap (:id region)]
                (assoc node :scalar-bytes (scalar/write-bytes (:layout node) (:scalar-bytes node) {:index 3 :offset 0 :type "usize" :region :usize} 4096)))]
      (is (thrown-with-msg? Exception #"Unregistered module region read"
            (raw/call session world read-name [m/erased "not-exposed.olean" deps m/erased])))
      (is (thrown-with-msg? Exception #"dependency chain mismatch"
            (raw/call session world read-name [m/erased path wrong-deps m/erased])))
      (is (thrown-with-msg? Exception #"native-address"
            (raw/call session bad free-name [region m/erased]))))))

(deftest freeing-virtual-metadata-never-closes-a-shared-lazy-native-source
  (let [loaded (store/load-file (m/world {}) "fixtures/imported-kernel-native.jsonl" {:cache-size 0})
        source (:source loaded)]
    (try
      (let [{:keys [world session region io-result deps]} (read-part loaded :mutable)
            freed (raw/call session (m/retain world region 1) free-name [region m/erased])
            after (:state freed)]
        (is (identical? (:native-imports world) (:native-imports after)))
        (is (= :ctor (:kind (m/node after (first (:roots loaded))))))
        (is (= (second (:fields (m/node world region))) (first (:roots loaded))))
        (is (empty? (:heap (-> after (m/release (:value freed) 1) (m/release io-result 1) (m/release deps 1))))))
      (finally (.close ^Closeable source)))))

(deftest raw-abi-and-region-provenance-remain-strict
  (let [loaded (loaded) bindings (capability/make-bindings loaded)
        signature (get capability/signatures "lean_compacted_region_read")]
    (is (thrown-with-msg? Exception #"ABI mismatch"
          (raw/lower bindings (row read-name "lean_compacted_region_read" (assoc-in signature [:params 1 :borrow] false)))))
    (is (thrown-with-msg? Exception #"pinned verified transport"
          (capability/make-bindings (assoc-in loaded [:manifest :input :leanCommit] "wrong"))))
    (is (not (contains? bindings "lean_compacted_region_save")))
    (is (not (contains? bindings "lean_enable_initializer_execution")))))

(deftest mark-persistent-validates-the-whole-graph-and-preserves-forks
  (doseq [backend backends]
    (let [loaded (loaded) [world session] (session loaded backend)
          [world child] (m/allocate world :array 246 [42])
          [world root] (m/allocate world :ctor 0 [child])
          result (raw/call session world mark-name [m/erased root m/erased])
          after (:state result)]
      (is (= root (:value result)))
      (is (= 0 (:rc (m/node after root))))
      (is (= 0 (:rc (m/node after child))))
      (is (= 1 (:rc (m/node world root))))
      (is (= 1 (:rc (m/node world child))))
      (is (= after (m/release after root 100))))
    (let [loaded (loaded) [world session] (session loaded backend)
          [world external] (m/resource world "unsupported-native-external")
          [world root] (m/allocate world :ctor 0 [external])]
      (is (thrown-with-msg? Exception #"Unsupported persistent object kind"
            (raw/call session world mark-name [m/erased root m/erased])))
      (is (= 1 (:rc (m/node world root))))
      (is (= 1 (:rc (m/node world external)))))))

(deftest persistent-region-free-is-an-explicit-lifetime-limit
  (doseq [backend backends]
    (let [loaded (loaded)
          {:keys [world session region]} (read-part loaded backend)
          marked (raw/call session (m/retain world region 1) mark-name [m/erased region m/erased])]
      (is (= 0 (:rc (m/node (:state marked) region))))
      (is (thrown-with-msg? Exception #"Persistent virtual regions"
            (raw/call session (:state marked) free-name [region m/erased]))))))
