(ns ansatz.research.ir.bootstrap.captured-runtime
  "Outer caller-pinned capture validation and the existing production importer.
   No copied image importer, automatic fork or cleanup on uncertain failure."
  (:require [ansatz.research.ir.bootstrap.artifacts :as artifacts]
            [ansatz.research.ir.bootstrap.definitions :as definitions]
            [ansatz.research.ir.source-setup :as source]
            [allocation-heartbeat-cohort-v1 :as cohort]
            [java-ir-baseline :as j])
  (:import [java.util IdentityHashMap ArrayDeque WeakHashMap]))
(deftype Capture [])
(defonce ^:private captures (WeakHashMap.))
(defn- need [ok message] (when-not ok (throw (ex-info message {:component :source4-captured-runtime}))))
(defn- entry [token]
  (locking captures (or (.get captures token) (throw (ex-info "Actual preflight Capture required" {})))))
(defn selected-heap-census
  "Bounded identity walk of the actual installed roots. No checks namespace,
   Java World, owner mutation, callback or full heap restore is used."
  [ctx roots]
  (let [seen (IdentityHashMap.) queue (ArrayDeque.)
        cls (Class/forName "ansatz.research.ir.Interpreter$Node" false (:loader ctx))
        rc-field (.getField cls "rc") fields-field (.getField cls "fields") scalars-field (.getField cls "scalars")]
    (need (and (sequential? roots) (<= (count roots) 4096)) "Bounded actual root occurrence list required")
    (doseq [x roots] (when (.isInstance cls x) (.add queue x)))
    (loop [counts {:nodes 0 :positive 0 :persistent 0 :rc-sum 0 :scalar-bytes 0} edges 0]
      (need (and (<= (:nodes counts) 100000) (<= edges 1000000) (<= (.size queue) 1000000)
                 (<= (:scalar-bytes counts) (* 32 1024 1024))) "Actual capture census budget")
      (if (.isEmpty queue) counts
        (let [node (.removeFirst queue)]
          (if (.containsKey seen node) (recur counts edges)
            (let [rc (.getInt rc-field node) fields ^objects (.get fields-field node)
                  scalars ^bytes (.get scalars-field node)]
              (need (<= 0 rc) "Invalid actual captured RC")
              (.put seen node true)
              (doseq [x fields] (when (.isInstance cls x) (.add queue x)))
              (recur (-> counts (update :nodes inc)
                         (update (if (pos? rc) :positive :persistent) inc)
                         (update :rc-sum + rc) (update :scalar-bytes + (alength scalars)))
                     (+ edges (alength fields))))))))))
(defn- header-row [row]
  (let [[kind declaration] (first (get row "ir"))]
    (need (and (= 1 (count (get row "ir"))) (contains? #{"fdecl" "extern"} kind)) "Unsupported captured Header kind")
    (assoc (dissoc row "pretty") "ir" {kind (dissoc declaration "body")})))
(defn- headers! [profile receipt capture]
  (let [headers (artifacts/json! profile (get capture "headers") (* 8 1024 1024))
        entries (get headers "entries")]
    (need (and (vector? entries) (<= 1 (count entries) 20000)
               (= (get headers "source_index_sha256") (get (source/code-profile receipt) "code_index_sha256")))
          "Captured Header inventory/index differs")
    (loop [xs entries seen #{} names #{}]
      (when-let [h (first xs)]
        (let [sha (get h "original_sha256") name (get h "name") row (get h "header_row")
              actual (source/lookup-entry receipt name)]
          (need (and (= sha (:sha256 actual)) (= row (header-row (:row actual)))
                     (= name (get row "name")) (not (contains? seen sha)) (not (contains? names name)))
                "Captured Header differs from actual original CAS/full declaration")
          (recur (rest xs) (conj seen sha) (conj names name)))))
    (count entries)))
(defn- capsule! [profile capture expected source-description]
  (let [capsule (artifacts/json! profile (get capture "capsule") (* 24 1024 1024))
        nodes (get capsule "nodes") globals (get capsule "globals") roots (get capsule "owned_roots")]
    (need (and (= "java-prepared-selected-graph-candidate/1" (get capsule "schema"))
               (= "SELECTED_OWNERS" (get capsule "accounting"))
               (= {"triple" "x86_64-unknown-linux-gnu" "word_bits" 64 "scalar_byte_order" "little-endian"}
                  (get capsule "target"))
               (= source-description (get capsule "source"))
               (vector? nodes) (= (:nodes expected) (count nodes)) (<= (count nodes) 100000)
               (vector? globals) (= 534 (count globals)) (vector? roots) (<= (count roots) 4096))
          "Captured source/node/global/root envelope differs")
    ;; The production recipe still validates every target kind, edge, ledger and
    ;; raw lane. This bounded shape pass happens before any SourceBinding/engine.
    (loop [xs nodes ids #{} edges 0 scalar-bytes 0]
      (need (and (<= edges 1000000) (<= scalar-bytes (* 32 1024 1024))) "Captured shape budget")
      (if-not (seq xs)
        (need (= (:scalar-bytes expected) scalar-bytes) "Captured scalar extent census differs")
        (let [n (first xs) id (get n "id") fields (get n "fields") hex (get n "scalar_hex" "")]
          (need (and (integer? id) (<= 0 id Integer/MAX_VALUE) (not (contains? ids id))
                     (contains? #{"ctor" "array" "ref" "closure" "byte-array"} (get n "kind"))
                     (integer? (get n "source_rc")) (<= 0 (get n "source_rc") Integer/MAX_VALUE)
                     (vector? fields) (<= (count fields) 100000)
                     (string? hex) (even? (count hex)) (re-matches #"[0-9a-f]*" hex))
                "Unsupported captured node storage")
          (recur (rest xs) (conj ids id) (+ edges (count fields)) (+ scalar-bytes (quot (count hex) 2))))))
    {:globals (count globals) :roots (count roots)}))
(defn preflight!
  "Authenticate outer capture manifest AND every original Header under the new
   receipt before image construction. Discards parsed capsule/Header maps after
   this stage; the existing importer reparses once without double retained heaps."
  [profile receipt]
  (let [p (artifacts/description profile) c (get p "capture")
        manifest (artifacts/json! profile (get c "manifest") 1048576)
        captured (artifacts/json! profile (get c "source") 1048576)
        expected (into {} (map (fn [[k v]] [(keyword k) v])) (get c "census"))
        directory (artifacts/directory! profile (get c "directory"))
        _ (need (= captured (get (source/code-profile receipt) "captured_graph_source")) "Capture is not this CodeReceipt's state description")
        _ (need (= cohort/census expected) "Only the selected 534-global capture profile is supported")
        _ (doseq [[key filename] [["capsule" "graph-capsule.json"] ["headers" "header-candidates.json"]]]
            (let [id (get c key) descriptor (get-in p ["artifacts" id]) actual (artifacts/file! profile id)]
              (need (and (= filename (.getName actual)) (= directory (.getParentFile actual))
                         (= (get descriptor "sha256") (get-in manifest ["files" filename "sha256"]))
                         (= (get descriptor "bytes") (get-in manifest ["files" filename "bytes"])))
                    "Capture manifest is not bound to the exact importer inputs")))
        headers (headers! profile receipt c)
        shape (capsule! profile c expected captured)
        _ (need (and (= "java-finalizer-companion-candidate/1" (get manifest "schema"))
                     (= 534 (get manifest "globals")) (= (:nodes expected) (get manifest "nodes"))
                     (= headers (get manifest "headers"))) "Capture manifest census differs")
        token (Capture.)]
    (locking captures (.put captures token {:profile profile :receipt receipt :expected expected :source captured
                                            :directory directory :headers headers :shape shape}))
    token))
(defn open!
  "Called by the cohort's explicit importer seam. Uses the identical production
   graph construction/install/configuration path; external journal exists FIRST."
  [capture basis directory expected census! journal]
  (let [s (entry capture) profile (:profile s)
        _ (artifacts/guard! profile)
        p (artifacts/description profile) jar (artifacts/file! profile (get-in p ["runtime" "jar"]))]
    (need (and (instance? clojure.lang.IAtom journal) (map? @journal)
               (= (:directory s) (clojure.java.io/file directory)) (= expected (:expected s))
               (identical? census! selected-heap-census)
               (true? (:explicit basis))
               (identical? (:task-runtime basis) (j/logical-sync-task-runtime basis))
               (identical? (:build-identity basis) (j/supported-build-identity basis))
               (= :persistent-ref-payload-mt (:graph-import-profile basis))) "Captured importer profile/journal differs")
    (definitions/assert-basis! basis jar)
    (swap! journal assoc :stage :captured-import-preflight :capture capture)
    (let [live (cohort/open-companion! basis
                 (str (.getPath ^java.io.File (:directory s)) java.io.File/separator)
                 expected census! journal)]
      (need (and (= 534 (:globals live)) (= (:headers s) (:companion-headers live))
                 (= expected (:census live))) "Actual captured install census differs")
      live)))
(defn description [capture]
  (let [s (entry capture)] (artifacts/guard! (:profile s)) (select-keys s [:expected :source :headers :shape])))
