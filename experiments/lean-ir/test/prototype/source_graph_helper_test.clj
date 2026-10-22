(ns prototype.source-graph-helper-test
  "Actual pinned G1 IR on synthetic guest records. No native Source, checking,
   graph capability, initializer action, finalizer, or native region FFI."
  (:require [clojure.test :refer [deftest is]]
            [clojure.java.io :as io] [clojure.data.json :as json]
            [prototype.import-ir :as ir] [prototype.runtime-abi :as abi]
            [prototype.raw-interop :as raw] [prototype.machine :as m]
            [prototype.guest-encoding :as encoding]
            [prototype.guest-encoding-test :as name-fixture]
            [prototype.kernel-bridge :as bridge]
            [prototype.kernel-bridge-test :as record-fixture]
            [prototype.resident-init-prefix :as graph])
  (:import [ansatz.kernel Name] [java.util.zip GZIPInputStream]
           [java.security MessageDigest]))

(defn sha256 [bytes]
  (apply str (map #(format "%02x" (bit-and 255 %)) (.digest (MessageDigest/getInstance "SHA-256") bytes))))
(def bundle
  (delay
    (let [packed (java.nio.file.Files/readAllBytes (.toPath (io/file "fixtures/source-graph-assembly.jsonl.gz")))
          _ (assert (= "5d54b8e5f7c5165fa001ece86301d6eb348e236c8b4740092fb23e050e6527db" (sha256 packed)))
          bytes (with-open [in (GZIPInputStream. (java.io.ByteArrayInputStream. packed))] (.readAllBytes in))
          _ (assert (= "d20d2a2a12d503acbb292ca52116542dac50fb6ca02ffcd6f0ee8e392f89a40d" (sha256 bytes)))
          rows (mapv #(json/read-str % :key-fn keyword) (.split (String. bytes java.nio.charset.StandardCharsets/UTF_8) "\n"))]
      {:manifests [(first rows)] :declarations (into {} (map (juxt :name identity)) (rest rows))})))
(def linked
  (delay
    (let [catalogue @bundle roots (vec (keys (:declarations catalogue)))
          ;; ALL rows must lower strictly, even if the tiny inputs never reach
          ;; their branches. No deferred lowering or raw host bindings.
          strict (ir/load-closure catalogue roots #(abi/lower-catalogue catalogue %))
          existing @name-fixture/functions
          linked (merge existing (ir/load-closure catalogue roots #(abi/lower-catalogue catalogue %)
                                                   {:existing-functions existing}))]
      {:strict strict :functions linked :existing existing})))
(def insert-helper
  (delay (let [expected "Std.DHashMap.Internal.Raw₀.insert._at_._private.Lean.Compiler.LCNF.EmitC.0.Lean.Compiler.LCNF.Arg.toCString.spec_1._redArg"
               matches (filter #(= expected (ir/name-label %)) (keys (:declarations @bundle)))]
           (assert (= 1 (count matches))) (first matches))))
(def owned-part ["str" ["str" ["anonymous"] "SourceModuleImport"] "mkOwnedPart"])
(def native-name (Name/fromString "Init"))
(def a-name (Name/fromString "GraphTinyA"))
(def b-name (Name/fromString "GraphTinyB"))

(defn call-recorded! [state label session world target args]
  (try
    (let [result (raw/call session world target args)]
      ;; Store the actual packet before decoding, adoption, or assertions.
      (swap! state assoc-in [:packets label] result)
      result)
    (catch Throwable cause
      (swap! state assoc-in [:failures label]
             {:cause cause :checkpoint (:checkpoint (ex-data cause))
              :session (:checkpoint-session (ex-data cause))})
      ;; clojure.test must not serialize a World's exception data on failure.
      ;; Exact cause/checkpoint remain in the private test diagnostic state.
      (throw (ex-info "Actual helper invocation failed; packet escrowed"
                      {:phase label :message (subs (or (.getMessage cause) "")
                                                  0 (min 256 (count (or (.getMessage cause) ""))))})))))

(defn fixture [backend]
  (let [functions (:functions @linked)
        state (atom {:world (m/world functions)
                     :session (raw/open-functions functions {} {:backend backend :fuel 2000000})
                     :owners [] :packets {} :failures {}})
        own! (fn [value] (swap! state update :owners conj value) value)
        invoke! (fn [target args]
                  (let [result (call-recorded! state :fixture-helper (:session @state) (:world @state) target args)]
                    (swap! state assoc :world (:state result) :session (:session result))
                    (own! (:value result))))
        retain! (fn [value] (swap! state update :world m/retain value 1) value)
        allocate! (fn [kind fields]
                    ;; Builders borrow their arguments and keep explicit owners
                    ;; for every allocated object. Parent edges retain separately.
                    (swap! state update :world #(reduce (fn [world value] (m/retain world value 1)) % fields))
                    (let [[world value] (m/allocate (:world @state) kind (if (= kind :array) 246 0) fields)]
                      (swap! state assoc :world world) (own! value)))
        ctor! (fn [fields bytes]
                (if (zero? bytes) (allocate! :ctor fields)
                  (do (swap! state update :world #(reduce (fn [world value] (m/retain world value 1)) % fields))
                      (let [[world value] (record-fixture/ctor (:world @state) 0 fields bytes)]
                        (swap! state assoc :world world) (own! value)))))
        scalar! (fn [value offset byte]
                  (swap! state update :world record-fixture/scalar! value offset "uint8" byte) value)
        name! (fn [value]
                (let [[world reference] (encoding/encode-name (:world @state)
                                          (fn [world target args]
                                            (let [result (call-recorded! state :name-encoder (:session @state) world target args)]
                                              (swap! state assoc :session (:session result))
                                              [(:state result) (:value result)])) value)]
                  (swap! state assoc :world world) (own! reference)))
        ;; Pure closed/ground/value wrappers lazily own persistent globals.
        ;; Force exactly the actual G1 closure's pure value rows before the
        ;; ownership baseline, so released heap equality has no hidden allowance
        ;; for newly allocated result descendants or unaccounted global roots.
        _ (doseq [[name row] (sort-by (comp pr-str key) (:declarations @bundle))
                  :when (contains? #{"closed" "ground" "value"} (get-in row [:runtime :role]))]
            (invoke! name []))
        names (into {} (map #(vector % (name! %))) [native-name a-name b-name])
        request! (fn [name meta?]
                   ;; Actual Lean.Import.mk: object[0]=Name; three packed Bool
                   ;; bytes at scalar offsets0,1,2 = importAll,isExported,isMeta.
                   (let [request (ctor! [(names name)] 3)]
                     (scalar! request 1 1) (scalar! request 2 (if meta? 1 0)) request))
        init-requests [(request! native-name false) (request! native-name true)]
        data! (fn [requests]
                ;; ModuleData: five object fields, isModule byte at index5/0.
                ;; Empty CI arrays keep this a shape/assembly transport test.
                (ctor! [(allocate! :array requests) (allocate! :array []) (allocate! :array [])
                        (allocate! :array []) (allocate! :array [])] 1))
        init-data (data! [])
        a-data (data! init-requests)
        b-data (data! (conj init-requests (request! a-name false)))
        init-part (invoke! owned-part [(retain! init-data) "synthetic-init"])
        native-request (ctor! [(names native-name)] 3)
        _ (scalar! native-request 0 1) ; private classic native importAll
        effective-import (ctor! [native-request] 2)
        _ (scalar! effective-import 0 2) ; actual IRPhases.all tag2
        _ (scalar! effective-import 1 1) ; hasData
        imported (ctor! [effective-import (allocate! :array [init-part]) (allocate! :array [])] 1)
        empty-map (ctor! [0 (allocate! :array (vec (repeat 16 (m/->Tag 0))))] 0)
        ;; Actual exported Name→Object insertion computes all Name hash/bucket
        ;; choices. The valid power-of-two empty Raw map has no forged hashes.
        module-map (invoke! @insert-helper [(retain! empty-map) (retain! (names native-name)) (retain! imported)])
        prefix (ctor! [module-map (allocate! :array [(names native-name)])] 0)
        a (ctor! [(names a-name) a-data "synthetic-a"] 0)
        b (ctor! [(names b-name) b-data "synthetic-b"] 0)
        parts (allocate! :array [a b])
        reversed (allocate! :array [b a])
        requests (allocate! :array (conj init-requests (request! b-name false)))
        limits (ctor! [16 4 16 8 64 16 128 4096 64 256] 0)]
    {:state state :args [prefix parts requests limits] :reversed [prefix reversed requests limits]
     :imported imported :prefix prefix :data {a-name a-data b-name b-data}}))
(defn release-fixture! [{:keys [state]}]
  (swap! state update :world #(reduce (fn [world value] (m/release world value 1)) % (rseq (:owners @state)))))
(defn array-values [world reference] (:fields (m/node world reference)))
(defn imported-records [world]
  ;; Structural observation only, not an authority lookup or Name hash table.
  (into {}
    (keep (fn [[id node]]
            (when (and (= :ctor (:kind node)) (= {:objects 3 :usize 0 :ssize 1} (:layout node)))
              (let [effective (m/node world (first (:fields node)))
                    request (m/node world (first (:fields effective)))
                    name (bridge/project-name world (first (:fields request)))]
                [name {:node node :reference (m/->Ref id) :effective effective :request request}]))))
    (:heap world)))

(deftest every-actual-export-row-strictly-lowers-without-host-binding-delta
  (let [{:keys [strict functions existing]} @linked catalogue @bundle]
    (is (= 246 (count (:declarations catalogue))))
    (is (= 210 (count (filter #(get-in % [:ir :fdecl]) (vals (:declarations catalogue))))))
    (is (= 36 (count (filter #(get-in % [:ir :extern]) (vals (:declarations catalogue))))))
    (is (= 173 (count (filter :sourceLocal (vals (:declarations catalogue))))))
    (is (= [] (get-in catalogue [:manifests 0 :initializationPlan :actions])))
    (is (not-any? :raw-extern (vals strict)))
    (is (every? #(not (contains? % :deferred-extern)) (vals strict)))
    (is (every? (fn [[name body]] (identical? body (get functions name))) existing))
    (is (true? (contains? functions graph/graph-assemble-helper)))))

(deftest actual-assembler-preserves-borrowed-chain-and-owned-result-on-every-backend
  (doseq [backend [:reference :mutable :jvm]]
    (let [{:keys [state args reversed prefix imported data] :as fixture} (fixture backend)
          before (:world @state) before-heap (:heap before)
          session (:session @state)]
      (try
        (let [result (call-recorded! state :success session before graph/graph-assemble-helper args)
              world (:state result) value (:value result) except (m/node world value)
              _ (when-not (= 1 (:tag except))
                  (throw (ex-info "Actual graph helper did not return Except.ok" {:except-tag (:tag except)})))
              assembly (m/node world (first (:fields except)))
              [output-state output-requests regions] (:fields assembly)
              output (m/node world output-state)
              names (mapv #(bridge/project-name world %) (array-values world (second (:fields output))))
              records (imported-records world)]
          (is (= 1 (:tag except)))
          (is (= [native-name a-name b-name] names))
          (is (= (nth args 2) output-requests))
          (is (= 2 (count (array-values world regions))))
          (is (= imported (get-in records [native-name :reference])))
          (doseq [name [a-name b-name]
                  :let [{:keys [node effective request]} (get records name)]]
            (is (= [1 0 0] (mapv #(m/read-scalar-node request {:index 1 :offset % :type "uint8" :region :scalar}) [0 1 2])))
            (is (= [2 1] (mapv #(m/read-scalar-node effective {:index 1 :offset % :type "uint8" :region :scalar}) [0 1])))
            (is (= 0 (m/read-scalar-node node {:index 3 :offset 0 :type "uint8" :region :scalar})))
            (is (= 1 (count (array-values world (second (:fields node))))))
            (is (empty? (array-values world (nth (:fields node) 2))))
            (let [part (m/node world (first (array-values world (second (:fields node)))))]
              (is (= (get data name) (first (:fields part))))))
          (let [released (m/release world value 1)]
            (is (true? (= before-heap (:heap released)))))
          (is (true? (= before-heap (:heap before))))
          (is (> (get-in world [:stats :steps]) (get-in before [:stats :steps]))))
        ;; Independent operation from retained pristine inputs; never resume the
        ;; previous result/failure. Invalid order returns an owned Except.error.
        (let [result (call-recorded! state :invalid-order session before graph/graph-assemble-helper reversed)
              value (:value result) world (:state result)]
          (is (= 0 (:tag (m/node world value))))
          (let [released (m/release world value 1)]
            (is (true? (= before-heap (:heap released))))))
        (let [cause (try (raw/call (assoc session :fuel 1) before graph/graph-assemble-helper args)
                         (catch clojure.lang.ExceptionInfo cause
                           (swap! state assoc-in [:failures :fuel]
                                  {:cause cause :checkpoint (:checkpoint (ex-data cause))
                                   :session (:checkpoint-session (ex-data cause))})
                           cause))
              checkpoint (:checkpoint (ex-data cause))]
          (is (true? (instance? clojure.lang.ExceptionInfo cause)))
          (is (map? checkpoint))
          (is (= backend (get-in (ex-data cause) [:checkpoint-session :backend])))
          (is (= 1 (get-in (ex-data cause) [:checkpoint-session :fuel])))
          (is (<= (- (get-in checkpoint [:stats :steps]) (get-in before [:stats :steps])) 1))
          (is (= (m/node before prefix) (m/node checkpoint prefix)))
          (is (true? (= before-heap (:heap before)))))
        ;; Cleanup only the retained pristine fixture branch. Fuel-failure
        ;; checkpoint and all returned diagnostic packets are never resumed or
        ;; released by this path.
        (finally (release-fixture! fixture))))))
