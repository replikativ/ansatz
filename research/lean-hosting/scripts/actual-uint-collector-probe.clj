(ns prototype.actual-uint-collector-probe
  "Definitions-only. Actual selected native body + actual guest collectors.
   No load-time IO/index/native/JVM/bootstrap/guest call. Explicit caller pins required."
  (:require [clojure.java.io :as io]
            [clojure.data.json :as json]
            [clojure.set :as set]
            [prototype.machine :as m]
            [prototype.raw-interop :as raw]
            [prototype.runtime-abi :as abi]
            [prototype.declaration-store :as store]
            [prototype.import-ir :as ir]
            [prototype.preparation :as preparation]
            [prototype.eval-const :as eval]
            [prototype.module-store :as modules]
            [prototype.ir-value :as ir-value]
            [prototype.guest-json :as guest-json])
  (:import [java.nio ByteBuffer]
           [java.nio.charset StandardCharsets CodingErrorAction]
           [java.security MessageDigest]))
(def index-sha256 "74d833d577923821b982e8a9e872a38b5cad011513eb18870b51417e13397f0e")
(def commit "819816b2e0a3bf405af45ae5c7af2491d8f5bee6")
(def culprit ["str" ["anonymous"] "_aux_Init_Data_UInt_Lemmas___macroRules_commandDeclare_uint_theorems___1"])
(def source-module ["str" ["str" ["str" ["anonymous"] "Init"] "Data"] "UInt"])
(def expected-source ["str" source-module "Lemmas"])
(def targets
  {:original ["str" ["str" ["anonymous"] "RuntimeCompileShim"] "bodyDepsOriginalOnlyProbe"]
   :linear ["str" ["str" ["anonymous"] "RuntimeCompileShim"] "bodyDepsLinearOnlyProbe"]})
(def root-kinds {:body "Array IR.FnBody" :decl "Array IR.Decl"
                 :expected "Array Lean.Json [IR.Decl, Array Name]"})
(def fuel 20000000)
(defn- check! [ok message] (when-not ok (throw (ex-info message {}))))
(defn- hash? [x] (and (string? x) (boolean (re-matches #"[0-9a-f]{64}" x))))
(defn- sha [bytes] (.formatHex (java.util.HexFormat/of) (.digest (MessageDigest/getInstance "SHA-256") ^bytes bytes)))
(defn- nat? [x] (and (integer? x) (<= 0 x Long/MAX_VALUE)))
(defn- exact! [x keys label] (check! (and (map? x) (= keys (set (clojure.core/keys x)))) (str "Invalid " label)))
(defn- worker [f]
  ;; json/read is recursive; typed projection and equality below are iterative.
  (let [result (promise) thread (Thread. nil (reify Runnable
                                             (run [_] (try (deliver result [:ok (f)])
                                                           (catch Throwable e (deliver result [:error e])))))
                                        "actual-body-canary" (* 16 1024 1024))]
    (.start thread) (let [[kind value] @result] (if (= :ok kind) value (throw value)))))
(defn- bytes! [path expected]
  (check! (and (string? path) (hash? expected)) "Explicit artifact path/SHA required")
  (let [limit (* 64 1024 1024)
        bytes (with-open [input (io/input-stream path)] (.readNBytes input (inc limit)))]
    (check! (and (<= (alength bytes) limit) (= expected (sha bytes))) "Artifact digest/size mismatch") bytes))
(defn- utf8 [bytes]
  (str (.decode (doto (.newDecoder StandardCharsets/UTF_8)
                  (.onMalformedInput CodingErrorAction/REPORT) (.onUnmappableCharacter CodingErrorAction/REPORT))
                (ByteBuffer/wrap bytes))))
(defn- pinned-catalogue [artifact]
  (exact! artifact #{:path :sha256} "catalogue artifact")
  (ir/index-bundles [(java.io.StringReader. (utf8 (bytes! (:path artifact) (:sha256 artifact))))]))
(defn- row [catalogue name]
  (if-let [read! (:read-declaration catalogue)] (read! name) (get-in catalogue [:declarations name])))
(defn- index-hash [^java.io.RandomAccessFile index]
  (locking index
    (let [position (.getFilePointer index) digest (MessageDigest/getInstance "SHA-256") buffer (byte-array 65536)]
      (try (.seek index 0)
           (loop [] (let [n (.read index buffer)] (when (pos? n) (.update digest buffer 0 n) (recur))))
           (.formatHex (java.util.HexFormat/of) (.digest digest))
           (finally (.seek index position))))))
(defn- provenance! [role descriptor]
  (let [input (get-in descriptor [:manifest :input])]
    (check! (and (= "lean-module-verified-index/1" (:schema descriptor))
                 (= "lean-module-data-input/1" (:schema input)) (= "4.33.1" (:leanVersion input))
                 (= commit (:leanCommit input)) (= [] (:modules input))
                 (false? (:nativeEnvironmentFinalized input)) (true? (:nativeSelectionEnvironmentFinalized input))
                 (false? (:nativeEnvironmentTransported input)) (false? (:regionAddressesTransported input))
                 (= "actual-interpreter-selected-FnBody/1" (:oracle input)) (true? (:canary input))
                 (= (get root-kinds role) (:rootValueKind input)) (= culprit (:selectedName input))
                 (= expected-source (:sourceModule input)) (false? (:sourceLocal input))
                 (= "RuntimeCompileShim.exportEvalConstWitnessIRSharedNamesLinear" (:selection input))
                 (= "private" (:selectionLevel input)) (false? (:selectionModuleSystem input))
                 (= [{:module ["str" ["anonymous"] "Init"] :importAll false :isExported true :isMeta false}
                     {:module ["str" ["anonymous"] "Init"] :importAll false :isExported true :isMeta true}]
                    (:selectionImports input))
                 (= [] (:missingDependencies input)) (nil? (:sorryDep input))
                 (nat? (:dependencyCount input))
                 (true? (get-in descriptor [:manifest :inventory :nativeRoundtripVerified])))
            "Actual native canary provenance mismatch")))
(defn- open-one! [world role input]
  (exact! input #{:descriptor :descriptor-sha256 :source} "native input")
  (let [d (json/read-str (utf8 (bytes! (:descriptor input) (:descriptor-sha256 input))) :key-fn keyword)
        _ (provenance! role d)
        result (modules/open-verified world (:descriptor input) (:descriptor-sha256 input)
                                      {:source-path (:source input) :cache-size 1024})
        source (:source result)]
    (try
      ;; Revalidate the returned object against OUR authenticated descriptor,
      ;; including its private index, closing locally before lease publication.
      (check! (and (= "prototype.module_store.Store" (.getName (class source)))
                   (false? @(:closed source)) (= (:next-id world) (:base source))
                   (= (:nodes d) (:size source)) (= (:manifest d) (:manifest source))
                   (= (:sourceSha256 d) (:digest source))
                   (= (:sourceBytes d) (:maximum-bytes source) (.size ^java.nio.channels.FileChannel (:channel source)))
                   (= (:indexBytes d) (.length ^java.io.RandomAccessFile (:index source)))
                   (= (:indexSha256 d) (index-hash (:index source)))) "Returned Store differs from authenticated native input")
      (assoc result :descriptor d)
      (catch Throwable e
        (try (.close ^java.io.Closeable source)
             (catch Throwable cleanup (when-not (identical? e cleanup) (.addSuppressed e cleanup))))
        (throw e)))))
(deftype Runner [state])
(defn checkpoint
  "BORROW diagnostic record only. Never print/serialize/transfer owners or keep
   this graph after close!. This is not a resumable callback/checkpoint API."
  [^Runner runner] @(.-state runner))
(defn summary [^Runner runner]
  (let [s @(.-state runner)]
    {:phase (:phase s) :functions (count (get-in s [:entry :functions]))
     :native-sources (count (:sources s)) :samples (:samples s)
     :failure-message (when-let [e (:failure s)]
                        (let [message (or (.getMessage ^Throwable e) "")]
                          (subs message 0 (min 700 (count message)))))}))
(defn- close-sources! [sources primary]
  (let [failures (reduce (fn [out source]
                           (try (.close ^java.io.Closeable source) out
                                (catch Throwable e (conj out e)))) [] sources)]
    (when-let [error (or primary (first failures))]
      (doseq [failure failures :when (not (identical? error failure))]
        (.addSuppressed ^Throwable error failure))
      (when-not primary (throw error)))))
(defn prepare!
  "Explicit IO/projection/linking only. One verified index, two ACTUAL collector
   wrapper roots, no bootstrap restore or plan-wide initialization. All descriptor
   pins and new shim/alias pins are independently supplied by trusted caller."
  [{:keys [store-root shim aliases descriptors] :as options}]
  (exact! options #{:store-root :shim :aliases :descriptors} "runner preparation")
  (exact! descriptors #{:body :decl :expected} "descriptor roles")
  (check! (string? store-root) "Explicit declaration store root required")
  (worker
    (fn []
      (let [opened (atom [])]
        (try
          (let [open-index (ns-resolve 'prototype.declaration-store 'open-index-verified-stream)
                _ (check! (some? open-index) "Load reviewed same-stream index opener; no unsafe fallback")
                backing (open-index store-root index-sha256)
                shim-catalogue (pinned-catalogue shim)
                _ (doseq [manifest (:manifests shim-catalogue)]
                    (check! (and (= [] (get-in manifest [:initializationPlan :actions]))
                                 (= {:target "x86_64-unknown-linux-gnu" :wordBits 64} (:runtimeProfile manifest)))
                            "Collector helper profile/initializer drift"))
                catalogue (abi/with-export-aliases (store/overlay backing shim-catalogue) (pinned-catalogue aliases))
                functions (preparation/complete-functions catalogue {} (vec (vals targets))
                            #(abi/lower-deferred-catalogue catalogue %))
                root-abis (into {}
                            (for [[label name] targets]
                              (let [f (get-in (row catalogue name) [:ir :fdecl])]
                                (check! (and (= name (:f f)) (= 1 (count (:xs f)))
                                             (contains? #{"object" "tobject"} (:type f))
                                             (every? #(and (contains? #{"object" "tobject"} (:ty %)) (boolean? (:borrow %))) (:xs f)))
                                        "Collector root is not the actual single-body object ABI")
                                [label (select-keys (first (:xs f)) [:ty :borrow])])))
                loaded (reduce (fn [out role]
                                 (let [r (open-one! (:world out) role (get descriptors role))]
                                   (swap! opened conj (:source r))
                                   (-> out (assoc :world (:world r)) (assoc-in [:roles role] r))))
                               {:world (assoc (m/world functions) :status :done) :roles {}} [:body :decl :expected])
                world (:world loaded) roles (:roles loaded)
                _ (doseq [[role count] [[:body 1] [:decl 1] [:expected 2]]]
                    (check! (= count (clojure.core/count (get-in roles [role :roots]))) "Canary root count mismatch"))
                _ (check! (= 3 (count (set (map :base @opened)))) "Native source bases collide")
                body (first (get-in roles [:body :roots]))
                _ (check! (and (m/ref? body) (= :ctor (:kind (m/node world body)))
                               (= 0 (:rc (m/node world body)))) "Actual macro body must be native persistent constructor data")
                decl (ir-value/project-decl world (first (get-in roles [:decl :roots])))
                native-json (guest-json/project world (first (get-in roles [:expected :roots])) {:key-fn keyword})
                deps (guest-json/project world (second (get-in roles [:expected :roots])) {:key-fn keyword})
                saved (row catalogue culprit)
                _ (check! (and (map? (:fdecl decl)) (= culprit (get-in decl [:fdecl :f]))
                               (= "decl" (:kind saved)) (= culprit (:name saved))
                               (nil? (get-in decl [:fdecl :info :sorryDep]))) "Missing/extern/nonculprit root is not acceptance")
                _ (check! (eval/ir-equal? decl native-json) "Actual Decl/native Json mismatch")
                _ (check! (eval/ir-equal? (:ir saved) native-json) "Actual interpreter selection differs from authenticated saved catalogue IR")
                _ (check! (eval/ir-equal? (get-in decl [:fdecl :body]) (ir-value/project world :body body))
                          "Primary native body differs from actual selected declaration")
                _ (check! (and (vector? deps)
                               (= (count deps) (get-in roles [:body :descriptor :manifest :input :dependencyCount])
                                  (get-in roles [:decl :descriptor :manifest :input :dependencyCount])
                                  (get-in roles [:expected :descriptor :manifest :input :dependencyCount]))) "Native dependency oracle count mismatch")
                ;; Validate every native expected Name using the actual typed
                ;; Name structure projected in deps; equality remains ordered.
                _ (check! (every? vector? deps) "Malformed native Name sequence")
                entry {:world world :functions functions :body body :root-abis root-abis :expected-deps deps
                       :catalogue catalogue :provenance {:index-sha256 index-sha256
                                                        :shim-sha256 (:sha256 shim) :aliases-sha256 (:sha256 aliases)
                                                        :descriptors (into {} (map (fn [[k v]] [k (:descriptor-sha256 v)])) descriptors)}}]
            ;; Full host body/Decl/Json projections are not retained here.
            (Runner. (atom {:phase :prepared :entry entry :sources @opened :samples []})))
          (catch Throwable e (close-sources! @opened e) (throw e)))))))

(defn- one! [^Runner runner entry backend label]
  (let [state (.-state runner) world (:world entry) target (get targets label)
        session (raw/open-functions (:functions entry) {} {:backend backend :fuel fuel :compile-threshold 64})
        started (System/nanoTime)
        _ (swap! state assoc :current-entry {:session session :world world :target target})
        ;; Transfer an owned argument only when the actual ABI requires it.
        ;; For this verified native RC0 body retain is intentionally a no-op;
        ;; the host Store lease supplies its lifetime in both independent forks.
        input-world (if (get-in entry [:root-abis label :borrow]) world (m/retain world (:body entry) 1))
        result (try (raw/call session input-world target [(:body entry)])
                    (catch Throwable e
                      (let [d (ex-data e) paused (:checkpoint d)]
                        (if (and (= :original label) (= "Raw runtime instruction budget exhausted" (.getMessage e))
                                 (= :paused (:status paused)) (empty? (:host-boundaries d))
                                 (identical? (:functions entry) (:functions paused)))
                          ;; Recognized PURE outer budget result; never resumed.
                          {:budget-exhausted true :state paused :session (:checkpoint-session d)}
                          (do (swap! state assoc :failure e :phase :failed) (throw e))))))
        after (:state result)
        _ (swap! state assoc :current-result result)
        _ (check! (and (identical? (:functions entry) (:functions after))
                      (empty? (:kernel-environments after)) (empty? (:source-modules after))
                      (empty? (:source-regions after)) (empty? (:source-import-prefixes after))
                      (empty? (:eval-const-authorizations after))
                      (identical? (:native-imports world) (:native-imports after)))
                  "Pure collector published unexpected authority")
        exhausted? (:budget-exhausted result)
        released (when-not exhausted?
                   (let [value (:value result)]
                     (check! (and (= :done (:status after)) (empty? (:frames after)) (nil? (:host-request after)))
                             "Collector did not return idle done")
                     (check! (eval/ir-equal? (:expected-deps entry) (ir-value/project after [:array :name] value))
                             "Actual guest collector output/order/multiplicity differs from native oracle")
                     (assoc (m/release after value 1) :result 0)))
        record {:collector label :backend backend :fuel fuel :status (if exhausted? :budget-exhausted :done)
                :guest-steps (- (get-in after [:stats :steps]) (get-in world [:stats :steps]))
                :elapsed-ms (/ (- (System/nanoTime) started) 1e6)
                :dependency-count (count (:expected-deps entry)) :result-owner-released (boolean released)
                :native-output-parity (boolean released) :host-bindings 0
                :paused-frames (if exhausted? (count (:frames after)) 0)
                :local-heap (count (:heap after)) :source-bases (mapv :base (:native-imports world))}]
    (check! (= (:events world) (:events (or released after))) "Collector produced unexpected external events")
    ;; Retire successful result and any paused pure branch WHOLE, preserving
    ;; only scalar diagnostics. No release of aliases inside paused frames.
    (swap! state #(-> % (dissoc :current-entry :current-result) (update :samples conj record)))
    record))
(defn run!
  "Explicit ONCE per handle. Original and linear share exact input world/body,
   source and code table; each gets fresh session/cache and 20M fuel. Cache-local
   native source lookups are shared across queries; no cold-time fairness claim."
  [^Runner runner {:keys [backend observe!] :or {backend :mutable observe! (fn [_])} :as options}]
  (check! (and (map? options) (every? #{:backend :observe!} (keys options))
               (contains? #{:reference :mutable :jvm} backend) (fn? observe!)) "Invalid runner options")
  (locking runner
    (let [state (.-state runner) before @state entry (:entry before)]
      (check! (= :prepared (:phase before)) "Runner already started/closed; no retry")
      (check! (every? #(false? @(:closed %)) (:sources before)) "Runner native source closed")
      (check! (identical? (:functions entry) (get-in entry [:world :functions])) "Input world/function mismatch")
      (m/node (:world entry) (:body entry))
      (check! (compare-and-set! state before (assoc before :phase :running)) "Runner concurrently claimed")
      (try
        (let [old (one! runner entry backend :original)
              _ (observe! old)
              linear (one! runner entry backend :linear)
              _ (observe! linear)
              result {:scope :actual-native-selected-UInt-body-guest-collectors
                      :backend backend :source (:provenance entry) :samples [old linear]
                      :full-init-replayed false :whole-witness-measured false
                      :old-new-guest-parity (= :done (:status old))
                      :linear-native-parity true
                      :regression-reproduced (and (= :budget-exhausted (:status old)) (= :done (:status linear)))}]
          (swap! state assoc :phase :done :summary result) result)
        (catch Throwable e
          ;; Keep exact current input/result/session when validation/observer
          ;; fails; preserve resources until deliberate terminal close!.
          (swap! state assoc :phase :failed :failure e) (throw e))))))
(defn close!
  "Terminal process-owner cleanup. Reject while running. Discard all branch/code/
   catalogue references in this handle BEFORE closing shared native sources.
   Borrowed checkpoints held externally must also be discarded by caller."
  [^Runner runner]
  (locking runner
    (let [state (.-state runner) before @state]
      (check! (not= :running (:phase before)) "Cannot close during guest execution")
      (check! (not= :close-failed (:phase before)) "Cleanup previously failed; no implicit retry; terminate owned process")
      (when-not (= :closed (:phase before))
        (reset! state {:phase :closed :samples (:samples before)})
        (try (close-sources! (:sources before) nil)
             (catch Throwable e
               ;; Keep failed resource handles for deliberate diagnostics only;
               ;; no world/code references or repeat-close permission survives.
               (reset! state {:phase :close-failed :samples (:samples before)
                              :sources (:sources before) :failure e})
               (throw e))))))
  nil)
