(ns prototype.sharecommon-layout-test
  (:require [clojure.test :refer [deftest is]] [clojure.data.json :as json] [clojure.string :as str]
            [prototype.machine :as m] [prototype.scalar :as scalar] [prototype.module-data :as data]
            [prototype.runtime-sharecommon :as share] [prototype.kernel-bridge :as kernel]
            [prototype.constructor-layout :as layout] [prototype.interop-codec :as codec]
            [prototype.runtime-expr-transform-test :as transform-test]
            [prototype.runtime-sharecommon-test :as share-test]))
(defn imported-node [id node]
  ;; Feed actual pinned native ABI/cache fixtures through the production raw
  ;; native constructor validator, including the complete physical scalar tail.
  (let [fields (:fields node) n (count fields) l (:layout node)
        extent (* 8 (quot (+ (if l (+ (* 8 (:usize l)) (:ssize l)) 0) 7) 8))
        bytes (mapv #(get (:scalar-bytes node) (+ (* 8 n) %) 0) (range extent))]
    (data/node! {:id id :kind "ctor" :tag (:tag node) :fields fields
                 :objectBytes (+ 8 (* 8 n) extent) :scalarBytesIncludePadding true
                 :bytesHex (apply str (map #(format "%02x" (long %)) bytes))}
                identity 1048576)))
(defn import-heap [w]
  (update w :heap #(into {} (map (fn [[id node]] [id (if (= :ctor (:kind node)) (imported-node id node) node)]) %))))
(deftest native-padded-lambda-clone-remains-strictly-projectable
  (let [row (first (filter #(= "closed-layout" (:label %))
                           (map #(json/read-str % :key-fn keyword)
                                (str/split-lines (slurp "fixtures/runtime-expr-replace-structures.jsonl")))))
        [w root] (transform-test/build (m/world {}) (:input row))
        w (assoc (import-heap w) :sharecommon-profile :immutable-text-v1)
        expected (kernel/project-expr w root)]
    (is (= 16 (get-in (m/node w root) [:layout :ssize])))
    (doseq [backend [:reference :mutable :jvm]]
      (let [{:keys [state value]} (share-test/run-share backend w root) clone (m/node state value)]
        (is (= expected (kernel/project-expr state value)))
        (is (kernel/constructor-layout? clone 3 9))
        (is (layout/physical-layout? clone 3 9))
        (is (not (contains? clone :native-source-id)))
        (is (not (contains? clone :native-object-bytes)))
        (is (= (:scalar-bytes (m/node w root)) (:scalar-bytes clone)))
        (is (= (:heap w) (:heap (m/release state value 1))))))))
(deftest local-and-imported-scalar-boxes-retain-native-bits-and-owned-results
  (doseq [[descriptor type value] [[:usize "usize" 18446744073709551615N]
                                    [:float32 "float32" (scalar/float-from-bytes "float32" [1 0 128 127])]
                                    [:float "float" (scalar/float-from-bytes "float" [1 0 0 0 0 0 240 127])]
                                    [:float32 "float32" -0.0] [:float "float" -0.0]]
          imported? [false true] backend [:reference :mutable :jvm]]
    (let [[w option] (codec/encode (m/world {}) [:option descriptor] {:some value})
          w (if imported? (import-heap w) w)
          ;; Exercise arbitrary nonzero native Float32 padding as well.
          box (first (:fields (m/node w option)))
          w (if (and imported? (= type "float32"))
              (update-in w [:heap (:id box) :scalar-bytes] merge {4 19 5 20 6 21 7 22}) w)
          before w {:keys [state value]} (share-test/run-share backend w option)
          actual (:some (codec/decode state [:option descriptor] value))
          clone (first (:fields (m/node state value))) node (m/node state clone)
          expected (:some (codec/decode before [:option descriptor] option))]
      (is (= (if (scalar/float-type? type) (scalar/float-bytes type expected) expected)
             (if (scalar/float-type? type) (scalar/float-bytes type actual) actual)))
      (is (layout/physical-layout? node 0 (scalar/width type)))
      (is (= 8 (get-in node [:layout :ssize])))
      (is (not (contains? node :native-source-id)))
      (when (and imported? (= type "float32"))
        (is (= [19 20 21 22] (mapv (:scalar-bytes node) (range 4 8)))))
      (is (= (:heap before) (:heap (m/release state value 1)))))))
(deftest storage-witness-does-not-admit-forged-or-truncated-layouts
  (let [[w box] (m/box-value (m/world {}) "float32" -0.0)
        [w clone] (share/evaluate share-test/ops w "lean_sharecommon_quick" [0 box])
        node (m/node w clone)]
    (is (kernel/constructor-layout? node 0 4))
    (is (not (kernel/constructor-layout? (update node :scalar-bytes dissoc 7) 0 4)))
    (is (not (kernel/constructor-layout? (assoc node :raw-clone-layout {:objects 0 :scalar-size 8}) 0 4)))
    (is (not (kernel/constructor-layout? (assoc-in node [:layout :ssize] 16) 0 4)))
    (is (not (kernel/constructor-layout? (assoc-in node [:scalar-bytes 7] 256) 0 4)))
    (is (nil? (:native-source-id node)))
    (is (nil? (:native-object-bytes node)))))
