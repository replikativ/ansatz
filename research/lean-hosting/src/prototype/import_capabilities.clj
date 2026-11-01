(ns prototype.import-capabilities
  "Explicit virtual-region FFI over already verified transported ModuleData.
   No native addresses, mmap/unmap, filesystem reads or OS region deallocation.
   Exported Lean initialization/attribute helpers must run their real guest bodies.
   Binds foreign CompactedRegion.read/free and Runtime.markPersistent operations."
  (:require [prototype.machine :as m] [prototype.runtime-string :as string]
            [prototype.module-import :as module-import] [prototype.runtime-prim :as prim]))

(def signatures
  {"lean_runtime_mark_persistent"
   {:params [{:ty "erased" :borrow false} {:ty "tobject" :borrow false}
             {:ty "void" :borrow false}] :return-type "tobject"}
   "lean_compacted_region_read"
   {:params [{:ty "erased" :borrow false} {:ty "object" :borrow true}
             {:ty "object" :borrow true} {:ty "void" :borrow false}] :return-type "object"}
   "lean_compacted_region_free"
   {:params [{:ty "object" :borrow false} {:ty "void" :borrow false}] :return-type "object"}})
(def ^:private ops {:ref? m/ref? :node m/node})
(def ^:private region-layout {:objects 2 :usize 3 :ssize 1})
(defn- fail [message data] (throw (ex-info message data)))
(defn- array! [world value]
  (when-not (and (m/ref? value) (= :array (:kind (m/node world value))))
    (fail "Expected borrowed virtual region dependency array" {:value value}))
  (:fields (m/node world value)))

(defn- registry [loaded]
  (let [world (:world loaded)
        commit (get-in loaded [:manifest :input :leanCommit])]
    (when-not (= (get prim/pinned-build "lean_get_githash") commit)
      (fail "Virtual region capability requires pinned verified transport" {}))
    (reduce
      (fn [out part-list]
        (loop [parts (seq part-list) previous [] out out]
          (if-not parts out
            (let [part (first parts) value (:value part) node (m/node world value)
                  {:keys [filePath mappedBytes oleanVersion leanCommit]} (:artifact part)
                  entry {:value value :file-path filePath :bytes mappedBytes :dependencies previous}]
              (when-not (and (= :ctor (:kind node)) (= 0 (:tag node)) (= 5 (count (:fields node)))
                             (= 0 (:rc node)) (integer? (:native-source-id node))
                             (string? filePath) (seq filePath) (not (.contains ^String filePath "\u0000"))
                             (integer? mappedBytes) (<= 0 mappedBytes Long/MAX_VALUE)
                             (= 2 oleanVersion) (= commit leanCommit))
                (fail "Virtual region capability contains an unverified ModuleData part" {:part part}))
              (when-let [old (get out filePath)]
                (when-not (= old entry) (fail "Conflicting virtual region artifact" {:path filePath})))
              (recur (next parts) (conj previous filePath) (assoc out filePath entry))))))
      {} (mapcat (juxt :parts :irParts) (:modules loaded)))))

(defn- region! [world regions region]
  (when-not (m/ref? region) (fail "Expected guest virtual CompactedRegion" {:region region}))
  (let [node (m/node world region)]
    (when-not (and (= :ctor (:kind node)) (= 0 (:tag node)) (= region-layout (:layout node))
                   (= 2 (count (:fields node))))
      (fail "Unsupported CompactedRegion representation; native regions are never freed" {:region region}))
    (let [[path root] (:fields node) path (string/string-value ops world path)
          entry (get regions path)
          scalar #(m/read-scalar-node node %)
          size (scalar {:index 2 :offset 0 :type "usize" :region :usize})
          base (scalar {:index 3 :offset 0 :type "usize" :region :usize})
          offset (scalar {:index 4 :offset 0 :type "usize" :region :usize})
          mapped (scalar {:index 5 :offset 0 :type "uint8" :region :scalar})]
      (when-not (and entry (= root (:value entry)) (= size (:bytes entry))
                     (zero? base) (zero? offset) (zero? mapped))
        (fail "Unregistered, freed or native-address CompactedRegion" {:region region :path path}))
      ;; Revalidate against this world, rather than trusting a captured Ref ID.
      (let [root-node (m/node world root)]
        (when-not (and (= :ctor (:kind root-node)) (= 0 (:rc root-node))
                       (integer? (:native-source-id root-node)))
          (fail "Virtual region root is no longer a verified imported value" {:root root})))
      entry)))

(defn make-bindings
  "Create raw ABI bindings from an eager/lazy receiver result.
   markPersistent validates/marks the reachable local graph in this world and
   returns the same owned value (BaseIO direct result). Reads expose only the
   verified parts and exact prior-part dependency chain.
   The read handler invokes the real guest mkVirtualPart helper visibly.
   Free zeroes the virtual region root then consumes its owner, as pinned native
   free does; no native mapping exists to unmap. The immutable DAG source remains
   alive for other environments/forks and must be closed by its host owner only
   after ALL worlds using it are finished. Persistent/leakEnv regions cannot be
   freed by this capability. CompactedRegion.save is not implemented."
  ([loaded] (make-bindings loaded {}))
  ([loaded {:keys [part-helper] :or {part-helper (:part module-import/helpers)}}]
   (when-not (vector? part-helper) (fail "Missing virtual region guest constructor" {}))
   (let [regions (registry loaded)]
     {"lean_runtime_mark_persistent"
      {:signature (get signatures "lean_runtime_mark_persistent")
       :handler (fn [_ world [_ value _]] [(m/mark-persistent world value) value])}
      "lean_compacted_region_read"
      {:signature (get signatures "lean_compacted_region_read")
       :handler
       (fn [{:keys [invoke]} world [_ path dependencies _]]
         (let [path (string/string-value ops world path) entry (get regions path)]
           (when-not entry
             (fail "Unregistered module region read capability" {:path path :runtime-limit :unregistered-module-region}))
           (let [actual (mapv #(:file-path (region! world regions %)) (array! world dependencies))]
             (when-not (= actual (:dependencies entry))
               (fail "Virtual module region dependency chain mismatch" {:path path :expected (:dependencies entry) :actual actual})))
           (let [data (:value entry) node (m/node world data)
                 _ (when-not (and (= 0 (:rc node)) (= :ctor (:kind node)) (integer? (:native-source-id node)))
                     (fail "Virtual read root is no longer a verified imported value" {}))
                 [world pair] (invoke (m/retain world data 1) part-helper [data path (:bytes entry)])
                 pair-node (when (m/ref? pair) (m/node world pair))]
             (when-not (and (= :ctor (:kind pair-node)) (= 0 (:tag pair-node)) (= 2 (count (:fields pair-node)))
                            (= data (first (:fields pair-node))))
               (fail "Guest virtual region constructor returned an invalid pair" {}))
             (region! world regions (second (:fields pair-node)))
             (m/allocate world :ctor 0 [pair]))))}
      "lean_compacted_region_free"
      {:signature (get signatures "lean_compacted_region_free")
       :handler
       (fn [_ world [region _]]
         (region! world regions region)
         (let [node (m/node world region)]
           (when (zero? (:rc node))
             (fail "Persistent virtual regions outlive initializer references and cannot be freed"
                   {:region region :runtime-limit :persistent-region-free}))
           ;; Native module.cpp:582-587 overwrites root before decrementing even
           ;; when aliases survive. Immutable replacement makes this fork-local.
           (let [world (m/replace-node world region (assoc node :fields (assoc (:fields node) 1 0)))
                 world (m/release world region 1)]
             (m/allocate world :ctor 0 [0]))))}})))
