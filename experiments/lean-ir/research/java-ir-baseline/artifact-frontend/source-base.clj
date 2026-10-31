(ns java-source-module-base-v1
  "Private guarded composite checking view over an issued source closure and its
   actual fresh finalizer Run. No caller Env/CI map or proof replay admission."
  (:require [java-matched-artifact-base-v1 :as fixed]
            [ansatz.research.ir.source-setup :as source]
            [java-source-module-exchange-v1 :as exchange]
            [prototype.imported-kernel :as imported]
            [prototype.kernel-projection-snapshot :as snapshot]
            [ansatz.research.ir.kernel-projection :as projection])
  (:import [ansatz.kernel Env Name ConstantInfo] [java.util WeakHashMap]
           [java.lang.reflect InvocationTargetException]))
(deftype SourceBase [])
(defonce ^:private bases (WeakHashMap.))
(defn- need [ok message] (when-not ok (throw (ex-info message {:profile :source-module-base-v1}))))
(defn- cell [token] (locking bases (or (.get bases token) (throw (ex-info "Actual issued source Base required" {})))))
(defn- field [value key] (.get (doto (.getDeclaredField (class value) key) (.setAccessible true)) value))
(defn- guard-node [engine method value]
  (try (.invoke (doto (.getDeclaredMethod (class engine) method (into-array Class [Object])) (.setAccessible true))
                engine (object-array [value]))
       (catch InvocationTargetException error (throw (.getCause error)))))
(defn- array-values [s value]
  (let [node (guard-node (:engine s) "array" value) n (.arraySize node)
        fields ^objects (.get ^java.lang.reflect.Field (:fields (:basis s)) node)]
    (need (and (<= 0 n 6410) (<= n (alength fields))) "Finalized Array live extent exceeds source union bound")
    (vec (take n fields))))
(defn- cheap-live! [holder]
  ;; Valid only as a per-CI/lookup guard inside a private outer metadata borrow.
  ;; Full issued closure/Run graph and CI checks bracket the entire operation.
  (let [s @holder]
    (need (= :open (:status s)) "Source Base is revoked or failed")
    (need (identical? (:thread s) (Thread/currentThread)) "Source Base is thread confined")
    (let [d (:driver s) ctx @(:current-ctx d) e (:engine s)]
      (need (and (identical? e (:engine d)) (identical? (:source s) (:source d))
                 (identical? (:class ctx) (class e))
                 (identical? (:program ctx) (field e "program"))) "Source Base driver/current Program changed")
      (doseq [key ["closed" "disposed" "untrackedFailure" "advancing"]]
        (need (false? (field e key)) "Source Base engine lifecycle changed")))
    (source/guard-source! (:receipt s) (:source s))
    (fixed/guard! (:prelude-base s))
    s))
(defn- borrow-views! [holder callback]
  (let [s (cheap-live! holder)]
    (exchange/with-closure! (:closure s)
      (fn [c]
        (need (and (identical? (:prelude-base s) (:prelude-base c))
                   (identical? (:engine s) (:engine c)) (identical? (:source s) (:source c))
                   (identical? (:receipt s) (:code-receipt c))
                   (identical? (:index s) (:source-index c))
                   (identical? (:segments s) (:snapshot-segments c))) "Source closure identity changed")
        (exchange/with-finalized! (:finalized-run s)
          (fn [r]
            (need (and (= :actual-source-closure-finalizer-only (:basis r))
                       (identical? (:closure s) (:closure r)) (identical? (:engine s) (:engine r))
                       (identical? (:source s) (:source r)) (identical? (:receipt s) (:code-receipt r))
                       (= 1 (:quot r)) (= 0 (:empty r)) (= (count (:domain s)) (:constant-count r))
                       (every? #(identical? (get s %) (get r %)) [:environment :kernel-root :constant-map :constants]))
                  "Source finalized Run changed protected occurrences")
            (try (callback s) (finally (cheap-live! holder)))))))))
(defn- live-source! [holder] (borrow-views! holder identity))
(defn guard! [token]
  (let [holder (cell token)]
    (try (live-source! holder) token
      (catch Throwable cause (swap! holder #(if (= :open (:status %)) (assoc % :status :failed) %)) (throw cause)))))
(defn- source-info! [s world ops info]
  (let [{:keys [name kind]} (imported/project-constant-name-kind world info fixed/name-limits ops)
        wrapper ((:node ops) world info) fields (:fields wrapper) expected (get (:index s) name)]
    (need (and expected (= 1 (count fields)) (= kind (:kind expected))
               (identical? (first fields) (:payload expected))) "Source CI Name/kind/payload differs from checked index")
    {:name name :kind kind :payload (first fields)}))
(defn- validate-index! [prelude index segments]
  (need (and (map? index) (<= 0 (count index) 4096) (vector? segments) (<= (count segments) 512))
        "Bounded actual source checking index/segments required")
  (let [domain (fixed/domain-names prelude)
        captured (reduce (fn [out segment]
                           (snapshot/validate-segment-values segment)
                           (reduce-kv (fn [m n ci]
                                        (need (and (< (count m) 4096) (not (contains? m n)))
                                              "Source snapshot segments overlap or exceed aggregate bound")
                                        (assoc m n ci)) out (:projected segment))) {} segments)]
    (need (= (set (keys captured)) (set (keys index))) "Source index does not cover exact checked snapshot domain")
    (doseq [[name {:keys [ci kind payload info]}] index]
      (need (and (instance? Name name) (instance? ConstantInfo ci) (= name (.-name ^ConstantInfo ci))
                 (= kind (.-tag ^ConstantInfo ci)) (identical? ci (get captured name)) payload info
                 (not (contains? domain name))) "Source index contains unchecked/overlapping/mismatched CI"))
    (need (= (+ (count domain) (count index)) (count (set (map str (concat domain (keys index))))))
          "Composite domain has ambiguous display names")
    (need (<= (+ (count domain) (count index)) 6410) "Composite constant domain exceeds bound")
    (into domain (keys index))))
(defn- validate-finalized! [s]
  (let [scope (projection/open-projector (:basis s) (:engine s)
                {:max-nodes 100000 :deadline-nanos (+ (System/nanoTime) 10000000000)})]
    (try
      (let [values (array-values s (:constants s)) ops (:carrier-ops scope) world (:world scope)]
        (need (= (count (:domain s)) (count values)) "Actual source finalizer has wrong CI count")
        (fixed/with-env! (:prelude-base s)
          (fn [_]
            (let [seen (reduce (fn [seen info]
                                 (let [{:keys [name]} (imported/project-constant-name-kind world info fixed/name-limits ops)]
                                   (need (and (contains? (:domain s) name) (not (contains? seen name))) "Finalized source domain differs")
                                   (if (contains? (:index s) name) (source-info! s world ops info)
                                     (fixed/validate-base-info! (:prelude-base s) world ops info))
                                   (conj seen name))) #{} values)]
              (need (= seen (:domain s)) "Finalized source domain is incomplete")))))
      (finally ((:close! scope))))))
(defn open-base!
  "Issue only from actual guarded exchange tokens and a separately live strict
   Prelude Base. Reopening a fresh strict Base after old adapter retirement is
   required; a revoked token is never revived. This grants no guest association."
  [prelude-base closure finalized-run]
  (fixed/guard! prelude-base)
  (exchange/with-closure! closure
    (fn [c]
      (exchange/with-finalized! finalized-run
        (fn [r]
          (need (and (identical? prelude-base (:prelude-base c)) (identical? closure (:closure r))
                     (identical? (:engine c) (:engine r)) (identical? (:source c) (:source r))
                     (identical? (:code-receipt c) (:code-receipt r))) "Actual source closure/Run/Prelude Base differ")
          (let [domain (validate-index! prelude-base (:source-index c) (:snapshot-segments c))
                driver (:driver c) basis @(:current-ctx driver)
                holder (atom {:status :open :thread (Thread/currentThread) :prelude-base prelude-base
                              :closure closure :finalized-run finalized-run :engine (:engine c) :source (:source c)
                              :receipt (:code-receipt c) :driver driver :basis basis :index (:source-index c)
                              :segments (:snapshot-segments c) :domain domain :borrow-depth 0
                              :environment (:environment r) :kernel-root (:kernel-root r)
                              :constant-map (:constant-map r) :constants (:constants r)})
                _ (live-source! holder) _ (validate-finalized! @holder)
                resolver (fn [name]
                           (let [s (cheap-live! holder)]
                             (need (pos? (:borrow-depth s)) "Composite lookup requires guarded Env borrow")
                             (if-let [entry (get (:index s) name)] (:ci entry)
                               (fixed/with-env! (:prelude-base s) (fn [^Env env] (.lookup env name))))))
                env (.withExternalLookupUncached (.enableQuot (Env.)) resolver (int (count domain)))
                token (SourceBase.)]
            (swap! holder assoc :env env)
            (locking bases (.put bases token holder)) token))))))
(defn with-env! [token callback]
  (let [holder (cell token)]
    (borrow-views! holder
      (fn [s]
        (swap! holder update :borrow-depth inc)
        (try
          (fixed/with-env! (:prelude-base s) (fn [_] (callback (:env s))))
          ;; An issuer failure may quarantine the view inside the callback.
          ;; Unwinding still ends this borrow; it must not leave a stale depth
          ;; that permanently prevents metadata-only revocation.
          (finally (swap! holder #(if (pos? (:borrow-depth % 0)) (update % :borrow-depth dec) %))))))))
(defn with-version! [token ^Env env callback]
  (with-env! token
    (fn [^Env seed]
      (let [check! #(need (and (instance? Env env) (.sameExternalView seed env) (.isQuotEnabled env))
                         "Version changed actual composite external view/quotient")]
        (check!)
        (try (let [result (callback env)] (check!) result)
          (catch Throwable cause (try (check!) (catch Throwable other (when-not (identical? cause other) (.addSuppressed cause other))))
            (throw cause)))))))
(defn domain-names [token] (guard! token) (:domain @(cell token)))
(defn base-count [token] (count (domain-names token)))
(defn validate-base-info! [token world ops info]
  (let [holder (cell token) s (cheap-live! holder)]
    (need (pos? (:borrow-depth s)) "Composite CI readback requires private Env borrow")
    (need (fn? (:check! ops)) "Actual scoped carrier guard required")
    ((:check! ops))
    (let [name (:name (imported/project-constant-name-kind world info fixed/name-limits ops))
          result (if (contains? (:index s) name) (source-info! s world ops info)
                   (fixed/validate-base-info! (:prelude-base s) world ops info))]
      ((:check! ops)) (cheap-live! holder) result)))
(defn assert-session! [token engine source run]
  (guard! token)
  (let [s @(cell token)]
    (need (and (identical? engine (:engine s)) (identical? source (:source s)) (identical? run (:finalized-run s)))
          "Source Base belongs to another engine/source/finalized Run")) token)
(defn revoke!
  "Revoke only this composite view. Fixed Prelude Base, module/closure/finalizer
   and guest owners remain with their explicit controllers."
  [token]
  (let [holder (cell token) s @holder]
    (need (identical? (:thread s) (Thread/currentThread)) "Source Base is thread confined")
    (need (zero? (:borrow-depth s 0)) "Cannot revoke during composite Env borrow")
    (reset! holder {:status :revoked :thread (:thread s)})) nil)
