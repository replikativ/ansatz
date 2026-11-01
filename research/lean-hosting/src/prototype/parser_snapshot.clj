(ns prototype.parser-snapshot
  "Experimental process-to-process reuse of pure initialized parser worlds.
   Not durable runtime storage. Executable code is supplied by the receiver and
   must exactly preserve every saved function and its ABI metadata; additions are
   allowed. Opaque host state, native resources and nested code metadata are
   rejected. EDN records are streamed individually, without a whole-world string."
  (:refer-clojure :exclude [read!])
  (:require [clojure.edn :as edn]
            [clojure.java.io :as io]
            [prototype.machine :as m]
            [prototype.fingerprint :as fingerprint])
  (:import [java.io PushbackReader]
           [java.nio.file Files StandardCopyOption]))

(def format-id "ansatz-parser-world/1")
(defn- fail [message data] (throw (ex-info message data)))
(defn- provenance! [p]
  (when-not (and (map? p) (every? #(some? (get p %))
                                       [:lean-version :lean-commit :runtime-profile :runtime-abi]))
    (fail "Snapshot requires explicit producer and runtime ABI provenance" {:provenance p})) p)

(defn- plain!
  "Explicit traversal stack, without rebuilding the input tree. Records other
   than guest carriers and lossy native floating carriers are rejected."
  [value world code?]
  (let [todo (java.util.ArrayDeque.)]
    (.addLast todo [value true])
    (loop []
      (when-let [[v root?] (.pollLast todo)]
        (when (and code? (not root?) (seq (meta v)))
          (fail "Nested executable metadata is outside snapshot format" {}))
        (cond
          (m/ref? v) (do (when-not (and (= #{:id} (set (keys v)))
                                        (integer? (:id v)) (not (neg? (:id v))))
                          (fail "Invalid snapshot guest reference" {}))
                        (m/node world v))
          (instance? prototype.machine.Tag v)
          (when-not (and (= #{:tag} (set (keys v))) (integer? (:tag v)) (not (neg? (:tag v))))
            (fail "Invalid snapshot guest tag" {}))
          (instance? prototype.machine.Builtin v)
          (when-not (and (= #{:name} (set (keys v))) (keyword? (:name v)))
            (fail "Invalid snapshot guest builtin" {}))
          (record? v) (fail "Opaque record is outside parser snapshot" {:class (str (class v))})
          (or (map? v) (vector? v) (set? v) (list? v) (seq? v))
          (do (doseq [child (if (map? v) (mapcat identity v) v)]
                (.addLast todo [child false]))
              (when (seq (meta v)) (.addLast todo [(meta v) false])))
          (instance? Float v) (fail "Raw Float carrier is outside parser snapshot" {})
          (instance? Double v)
          (when (Double/isNaN v) (fail "Raw NaN carrier is outside parser snapshot" {}))
          (or (nil? v) (boolean? v) (string? v) (keyword? v) (symbol? v)
              (char? v) (integer? v) (ratio? v) (decimal? v)) nil
          :else (fail "Opaque value is outside parser snapshot" {:class (str (class v))}))
        (recur)))))

(defn- world! [world]
  (when-not (and (map? (:functions world)) (map? (:heap world)) (map? (:globals world))
                 (= :done (:status world)))
    (fail "Parser snapshot requires a completed immutable world" {:status (:status world)}))
  (when (seq (:kernel-environments world))
    (fail "Kernel associations are outside parser snapshot" {}))
  (when-not (and (integer? (:next-id world)) (not (neg? (:next-id world))))
    (fail "Invalid snapshot allocation counter" {}))
  (doseq [[id node] (:heap world)]
    (when-not (and (integer? id) (<= 0 id) (< id (:next-id world))
                   (map? node) (integer? (:rc node)) (not (neg? (:rc node))))
      (fail "Invalid snapshot heap node" {:id id}))
    (when (= :resource (:kind node)) (fail "Native resources are outside parser snapshot" {:id id}))
    (when (and (= :closure (:kind node)) (not (contains? (:functions world) (:function node))))
      (fail "Snapshot closure has no executable target" {:id id :target (:function node)})))
  world)

(defn- function-key [function]
  ;; fingerprint deliberately ignores metadata; ABI metadata is an explicit part
  ;; of this key. Nested metadata is rejected above rather than silently ignored.
  ;; Executable code cannot embed process-local heap pointers. Both sides must
  ;; enforce this restriction, including nested metadata rejection.
  (plain! function {:heap {}} true)
  (let [[digest opaque] (fingerprint/key [function (meta function)])]
    (when (seq opaque) (fail "Opaque executable data is outside parser snapshot" {})) digest))

(defn write!
  "Atomically stream a completed parser world to path. `provenance` must identify
   :lean-version, :lean-commit, :runtime-profile and :runtime-abi. Returns counts.
   Receiver must supply matching provenance and an exact executable superset."
  [path world provenance]
  (provenance! provenance) (world! world) (plain! provenance world false)
  (let [file (.getAbsoluteFile (io/file path)) parent (.getParentFile file)
        temp (java.io.File/createTempFile ".parser-world-" ".edn" parent)
        counts {:functions (count (:functions world)) :heap (count (:heap world)) :globals (count (:globals world))}
        state (dissoc world :functions :heap :globals)]
    (try
      (with-open [writer (io/writer temp)]
        (binding [*out* writer *print-meta* true *print-length* nil *print-level* nil]
          (prn {:format format-id :provenance provenance :counts counts})
          (doseq [[name function] (:functions world)]
            (plain! name world false)
            (prn [:function name (function-key function)]))
          (doseq [[id node] (:heap world)] (plain! node world false) (prn [:heap id node]))
          (doseq [[name entry] (:globals world)] (plain! name world false) (plain! entry world false) (prn [:global name entry]))
          (plain! state world false) (prn [:state state]) (prn [:end counts])))
      (Files/move (.toPath temp) (.toPath file)
                  (into-array StandardCopyOption [StandardCopyOption/ATOMIC_MOVE StandardCopyOption/REPLACE_EXISTING]))
      counts
      (finally (.delete temp)))))

(def readers {'prototype.machine.Ref m/map->Ref
              'prototype.machine.Tag m/map->Tag
              'prototype.machine.Builtin m/map->Builtin})

(defn read!
  "Read a streamed parser checkpoint using an explicitly supplied function table.
   Changed/missing original functions or ABI metadata fail; new helpers are fine.
   No automatic program upgrades, kernel-state restore or native reattachment."
  [path functions expected-provenance]
  (provenance! expected-provenance)
  (with-open [reader (PushbackReader. (io/reader path))]
    (let [eof (Object.) read-row #(edn/read {:eof eof :readers readers} reader)
          header (read-row)]
      (when-not (and (= format-id (:format header)) (= expected-provenance (:provenance header)))
        (fail "Parser snapshot provenance mismatch" {:header header}))
      (loop [heap (transient {}) globals (transient {}) names #{} state nil]
        (let [row (read-row)]
          (when (identical? eof row) (fail "Truncated parser snapshot" {}))
          (when-not (vector? row) (fail "Invalid parser snapshot record" {}))
          (case (first row)
            :function
            (let [[_ name expected] row function (get functions name)]
              (when (contains? names name) (fail "Duplicate snapshot function" {:name name}))
              (when-not (and function (= expected (function-key function)))
                (fail "Parser snapshot executable or ABI mismatch" {:name name}))
              (recur heap globals (conj names name) state))
            :heap (let [[_ id node] row]
                    (when (contains? heap id) (fail "Duplicate snapshot heap node" {:id id}))
                    (recur (assoc! heap id node) globals names state))
            :global (let [[_ name entry] row]
                      (when (contains? globals name) (fail "Duplicate snapshot global" {:name name}))
                      (recur heap (assoc! globals name entry) names state))
            :state (do (when state (fail "Duplicate snapshot state" {}))
                       (when (some #(contains? (second row) %) [:functions :heap :globals])
                         (fail "Invalid snapshot state fields" {}))
                       (recur heap globals names (second row)))
            :end (let [heap (persistent! heap) globals (persistent! globals)
                       actual {:functions (count names) :heap (count heap) :globals (count globals)}
                       world (assoc state :functions functions :heap heap :globals globals)]
                   (when-not (and state (= actual (:counts header) (second row)) (identical? eof (read-row)))
                     (fail "Parser snapshot counts or trailer mismatch" {}))
                   (world! world) (plain! (dissoc world :functions) world false)
                   world)
            (fail "Unknown parser snapshot record" {:record (first row)})))))))
