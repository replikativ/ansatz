(ns java-matched-artifact-base-v1
  "Private lazy Java checking view anchored to actual fixed ModuleData and sealed
   original finalizer lineage. open-base! alone is not a checked guest association;
   first real ELAB map/quot helper lineage is still required by the authority."
  (:require [clojure.edn :as edn] [clojure.java.io :as io]
            [java-matched-prelude-module-v4 :as module] [java-prelude-finalizer-lineage-v1 :as finalizer]
            [prototype.guarded-kernel-view :as view] [prototype.imported-kernel :as imported]
            [ansatz.research.ir.kernel-projection :as projection]
            [ansatz.research.ir.source-setup :as source])
  (:import [ansatz.kernel Env Name ConstantInfo] [java.util WeakHashMap]
           [java.lang.reflect InvocationTargetException]))
(deftype Base [])
(defonce ^:private bases (WeakHashMap.))
(def kinds {"axiom" 0 "def" 1 "thm" 2 "opaque" 3 "quot" 4 "inductive" 5 "ctor" 6 "rec" 7})
(def name-limits {:max-nodes 256 :max-chars 4096})
(def per-ci {:declarations 1 :shell-items 20000 :expr-nodes 60000 :expr-edges 180000 :expr-depth 256 :raw-bytes 8388608
             :name-nodes 20000 :name-chars 2097152 :name-depth 256 :level-nodes 20000 :level-depth 256 :level-visits 2000000})
(def total-usage {:declarations 2314 :shell-items 200000 :expr-nodes 200000 :expr-edges 600000 :expr-depth 592384 :raw-bytes 33554432
                  :name-nodes 100000 :name-chars 8388608 :name-depth 592384 :level-nodes 100000 :level-depth 592384 :level-visits 8000000})
(defn- need [condition message] (when-not condition (throw (ex-info message {:profile :matched-artifact-base-v1}))))
(defn- cell [token] (locking bases (or (.get bases token) (throw (ex-info "Actual issued matched Base required" {})))))
(defn- native-name [tree]
  (loop [node tree pending []]
    (need (< (count pending) 256) "Producer typed Name exceeds bound")
    (if (= ["anonymous"] node)
      (reduce (fn [^Name prefix [tag value]]
                (case tag "str" (do (need (and (string? value) (<= (count value) 4096)) "Producer Name String exceeds bound") (Name/mkStr prefix value))
                  "num" (do (need (and (string? value) (re-matches #"0|[1-9][0-9]*" value) (<= 0 (bigint value) Long/MAX_VALUE)) "Producer numeric Name unsupported")
                            (Name/mkNum prefix (long (bigint value))))
                  (throw (ex-info "Unknown producer Name tag" {})))) Name/ANONYMOUS_NAME (rseq pending))
      (do (need (and (vector? node) (= 3 (count node)) (contains? #{"str" "num"} (first node))) "Malformed producer typed Name")
          (recur (second node) (conj pending [(first node) (nth node 2)]))))))
(defn- field [value key] (.get (doto (.getDeclaredField (class value) key) (.setAccessible true)) value))
(defn- guard-node [engine method value]
  (try (.invoke (doto (.getDeclaredMethod (class engine) method (into-array Class [Object])) (.setAccessible true)) engine (object-array [value]))
       (catch InvocationTargetException error (throw (.getCause error)))))
(defn- root-fields [s node] (.get ^java.lang.reflect.Field (:fields (:basis s)) node))
(defn- array-fields [s node]
  (let [array (guard-node (:engine s) "array" node) size (.arraySize array) fields ^objects (root-fields s node)]
    (need (= size (alength fields)) "Unexpected imported Array capacity/logical-size representation") fields))
(defn- live-source! [holder]
  ;; This lower guard deliberately NEVER calls view/guard!: it is also the view's
  ;; own lease callback, so doing so would recurse. No closure captures Base key.
  (let [s @holder]
    (need (= :open (:status s)) "Matched base is revoked or failed")
    (need (identical? (:thread s) (Thread/currentThread)) "Matched base is thread confined")
    (let [m (module/inspect! (:module-lease s)) r (finalizer/inspect! (:finalizer-run s))]
      (need (and (identical? (:engine s) (:engine m)) (identical? (:engine s) (:engine r))
                 (identical? (:code-source m) (:source r))
                 (identical? (:aggregate s) (:aggregate m)) (identical? (:kernel s) (:kernel-root r))
                 (identical? (:map s) (:constant-map r)) (= 1 (:quot r)) (= 2314 (:constant-count r))) "Actual module/finalizer lineage changed"))
    ((:store-lease! s))
    s))
(defn- close-scope! [scope projector]
  (when projector ((:prototype.kernel-bridge/clear-memo! (meta projector))))
  ((:close! scope)))
(defn- scoped [s f]
  (let [scope (projection/open-projector (:basis s) (:engine s) {:max-nodes 100000 :deadline-nanos (+ (System/nanoTime) 10000000000)})]
    (try (f scope) (finally ((:close! scope))))))
(defn- payload [ops world info]
  (let [wrapper ((:node ops) world info)]
    (need (= 1 (count (:fields wrapper))) "ConstantInfo wrapper has wrong arity")
    (first (:fields wrapper))))
(defn- expected-domain [correspondence]
  (reduce (fn [out row]
            (let [name (native-name (get row "typedName")) kind (get kinds (get-in row ["shape" "kind"])) index (get row "sourceCIIndex")]
              (need (and kind (= 2 (get row "sourcePartRoot")) (integer? index) (<= 0 index 2313)
                         (not (contains? out name))) "Producer CI domain/index/kind differs")
              (assoc out name {:kind kind :source-index index}))) {} (get correspondence "constants")))
(defn- build-index [s domain m r]
  (scoped s
    (fn [scope]
      (let [ops (:carrier-ops scope) world (:world scope)
            roots ^objects (array-fields s (:aggregate m)) private-part (aget roots 2)
            part ((:node ops) world private-part)
            _ (need (and (= 0 (:tag part)) (= 5 (count (:fields part)))) "Private ModuleData layout differs")
            source-infos ^objects (array-fields s (nth (:fields part) 2))
            _ (need (= 2314 (alength source-infos) (count domain)) "Private ModuleData domain count differs")
            by-index (into {} (map (fn [[name info]] [(:source-index info) [name info]])) domain)
            _ (need (= 2314 (count by-index)) "Producer CI source indices are not complete")
            index (reduce (fn [out i]
                            (let [info (aget source-infos i) actual (imported/project-constant-name-kind world info name-limits ops)
                                  [name expected] (get by-index i)]
                              (need (= {:name name :kind (:kind expected)} actual) "Actual private source CI differs from native typed inventory")
                              (assoc out name {:kind (:kind actual) :payload (payload ops world info) :info info}))) {} (range 2314))
            checked ^objects (array-fields s (:constants r))]
        (need (= 2314 (alength checked)) "Actual finalized checked map has wrong domain size")
        (loop [i 0 seen #{}]
          (if (= i 2314) (do (need (= (set (keys index)) seen) "Finalized checked map domain differs") index)
            (let [info (aget checked i) {:keys [name kind]} (imported/project-constant-name-kind world info name-limits ops)
                  expected (get index name)]
              (need (and expected (not (contains? seen name)) (= kind (:kind expected))
                         (identical? (:payload expected) (payload ops world info))) "Finalized map changed an imported Name/kind/payload")
              (recur (inc i) (conj seen name)))))))))
(defn- actual-manifest [store manifest]
  (let [root (:path store) root (if (instance? java.nio.file.Path root) (.toFile ^java.nio.file.Path root) root)
        path (io/file root "manifest.edn")]
    (need (and (.isFile path) (<= (.length path) 65536)) "Actual bounded store manifest required")
    (with-open [input (io/input-stream path)]
      (let [raw (.readNBytes input 65537)
            _ (need (<= (alength raw) 65536) "Actual store manifest grew past bound")
            actual (edn/read-string (String. ^bytes raw java.nio.charset.StandardCharsets/UTF_8))]
        (need (= actual manifest) "Supplied store manifest differs from actual borrowed store") actual))))
(defn- manifest-policy! [manifest audit]
  (need (and (= 2 (:store/format manifest)) (= module/audit-pin (:artifact/cohort manifest))
             (= module/audit-pin (get-in manifest [:provenance :producer/pair-audit-sha256]))
             (= :trusted-artifact (get-in manifest [:provenance :basis]))
             (= :full (get-in manifest [:provenance :projection/body-policy]))
             (= source/lean-pin (get-in manifest [:provenance :lean/commit]))
             (= "4.33.1" (get-in manifest [:provenance :lean/version]))
             (false? (get-in manifest [:provenance :proof-replay]))
             (false? (:guest-finalization-accepted manifest)) (true? (:quot-enabled manifest))
             (= "prelude" (:branch manifest))
             (= {:declarations 2314 :expressions 59369 :names 8250 :levels 116} (:artifacts manifest))
             (= (into {} (map (fn [[name info]] [(keyword name) (into {} (map (fn [[k v]] [(keyword k) v])) info)])) (get audit "files"))
                (get-in manifest [:provenance :producer/files]))) "Borrowed store is not the fixed full paired Prelude")
  (merge (:captured-branch-roots manifest)
         {:env-count 2314 :names-count 8250 :levels-count 116 :exprs-count 59369 :dag-storage? true :quot-enabled true}))
(defn open-base!
  "Data+actual finalized-map linkage and a lazy private view only. Real ELAB
   helper-token/map/quot authority still must claim the first checked association.
   BORROWED-STORE must include :lease! (a host-owned revocation/source guard)."
  [module-lease finalized-run borrowed-store manifest]
  (need (and (fn? (:lease! borrowed-store)) (= 2 (:write-format borrowed-store)))
        "Independent borrowed-store lease guard and actual format2 handle required")
  ((:lease! borrowed-store))
  (let [m (module/inspect! module-lease) r (finalizer/inspect! finalized-run)
        _ (need (and (identical? (:engine m) (:engine r)) (identical? (:code-source m) (:source r)) (= 1 (:quot r))) "Module/finalizer actual engine/source differs")
        actual (actual-manifest borrowed-store manifest)
        roots (manifest-policy! actual (:audit m))
        domain (expected-domain (:correspondence m))
        s {:status :open :thread (Thread/currentThread) :module-lease module-lease :finalizer-run finalized-run
           :engine (:engine r) :code-source (:code-source m) :basis (:basis m) :aggregate (:aggregate m) :kernel (:kernel-root r) :map (:constant-map r)
           :store-lease! (:lease! borrowed-store)}
        holder (atom s)
        _ (live-source! holder)
        index (build-index s domain m r)
        _ (swap! holder assoc :index index :domain (set (keys index)))
        authenticate! (fn [name ^ConstantInfo ci]
                        (let [current (live-source! holder) expected (get (:index current) name)]
                          (need (pos? (:borrow-depth current 0)) "Hydration requires a private checked Env borrow")
                          (need expected "Hydrated Name is outside authentic module domain")
                          (let [scope (projection/open-projector (:basis current) (:engine current)
                                        {:max-nodes 100000 :deadline-nanos (+ (System/nanoTime) 10000000000)})
                                projector (imported/make-constant-projector (:world scope) (:carrier-ops scope)
                                            {:max-visits 1000000 :max-rule-nodes 10000})]
                            (try
                              (let [projected (projector (:world scope) (:info expected))]
                                (need (= (imported/checking-shape ci) (imported/checking-shape projected))
                                      "Hydrated CI differs from actual native guest checking shape"))
                              (finally (close-scope! scope projector))))))
        java-view (view/open-view! borrowed-store (:branch actual)
                    {:expected-roots roots :domain (set (keys index)) :lease! #(live-source! holder)
                     :authenticate-ci! authenticate! :evidence-limits per-ci :max-materialized 2314 :max-total-usage total-usage})
        _ (swap! holder assoc :view java-view)
        token (Base.)]
    (locking bases (.put bases token holder)) token))
(defn guard! [token]
  (let [holder (cell token) before @holder]
    (when (= :open (:status before))
      (need (identical? (:thread before) (Thread/currentThread)) "Matched base is thread confined"))
    (try (let [s (live-source! holder)] (view/guard! (:view s)) token)
         (catch Throwable cause
           (swap! holder #(if (= :open (:status %)) (assoc % :status :failed) %))
           (throw cause)))))
(defn with-env! [token f]
  (guard! token)
  (let [holder (cell token)]
    (swap! holder update :borrow-depth (fnil inc 0))
    (try
      (let [result (view/with-view! (:view @holder) f)] (guard! token) result)
      (catch Throwable cause
        (try (guard! token) (catch Throwable other (when-not (identical? cause other) (.addSuppressed cause other))))
        (throw cause))
      (finally (swap! holder #(if (= :open (:status %)) (update % :borrow-depth dec) %))))))
(defn with-version! [token ^Env environment f]
  (with-env! token
    (fn [^Env seed]
      (let [validate! (fn []
                        (need (and (instance? Env environment) (.sameExternalView seed environment)
                                   (.isQuotEnabled environment)) "Version changed authentic external view or quotient"))]
        (validate!)
        (try
          (let [result (f environment)] (validate!) result)
          (catch Throwable cause
            (try (validate!) (catch Throwable other (when-not (identical? cause other) (.addSuppressed cause other))))
            (throw cause)))))))
(defn domain-names [token] (guard! token) (:domain @(cell token)))
(defn base-count [token] (guard! token) (count (:domain @(cell token))))
(defn validate-base-info!
  "Cheap actual Name/kind/original-payload check. Caller owns this short Node
   scope and closes it before advance. Returns {:name :kind :payload}; rejects
   an entry outside the fixed native base. No CI proof hydration."
  [token world carrier-ops info]
  (let [holder (cell token) s (live-source! holder)
        _ (need (pos? (:borrow-depth s 0)) "Base info validation requires a private Env borrow")
        _ (need (fn? (:check! carrier-ops)) "Actual scoped carrier check required")
        _ ((:check! carrier-ops))
        {:keys [name kind]} (imported/project-constant-name-kind world info name-limits carrier-ops)
        actual-payload (payload carrier-ops world info) expected (get (:index s) name)]
    (need (and expected (= kind (:kind expected)) (identical? actual-payload (:payload expected)))
          "Readback changed a base Name/kind/original payload")
    ((:check! carrier-ops))
    (live-source! holder)
    {:name name :kind kind :payload actual-payload}))
(defn revoke!
  "Revoke this view only. Actual Run/ModuleLease/store/source/region owner
   occurrences remain with their existing controllers through real cleanup."
  [token]
  (let [holder (cell token) s @holder]
    (when-not (= :revoked (:status s))
      (need (identical? (:thread s) (Thread/currentThread)) "Matched base is thread confined")
      (reset! holder (assoc s :status :revoked))
      (view/close! (:view s))
      (reset! holder {:status :revoked})))
  nil)

(defn assert-session!
  "Bind a real adapter/authority to this exact base before any Java check or
   publisher. A separately valid base from another driver or Run is insufficient."
  [token engine source finalized-run]
  (guard! token)
  (let [s @(cell token)]
    (need (and (identical? engine (:engine s)) (identical? source (:code-source s))
               (identical? finalized-run (:finalizer-run s))) "Base belongs to another engine/source/finalized Run"))
  token)
