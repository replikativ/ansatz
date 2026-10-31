(ns general-generated-batch-v1
  "Canonical generated fdecls from live original-compiler CommandReceipts only.
   No source receipt, kernel admission, entry codec, host policy or guest owner is
   issued here. Unexecutable code leaves the successful checked command intact."
  (:require [clojure.data.json :as json]
            [java-ir-baseline :as j]
            [ansatz.research.ir.source-setup :as source]
            [ansatz.research.ir.authenticated-demand :as demand]
            [general-command-receipt-v1 :as command])
  (:import [java.util WeakHashMap]))

(deftype Scope [])
(deftype Batch [])
(defonce ^:private scopes (WeakHashMap.))
(defonce ^:private batches (WeakHashMap.))
(defn- need [ok message] (when-not ok (throw (ex-info message {:profile :general-generated-batch-v1}))))
(defn- unsupported! [message] (throw (ex-info message {:unsupported-generated-code true})))
(defn- field [x k] (.get (doto (.getDeclaredField (class x) k) (.setAccessible true)) x))
(defn- issued [registry token]
  (locking registry (or (.get ^WeakHashMap registry token) (throw (ex-info "Actual issued generated-code capability required" {})))))
(defn- context [s] @(:current-ctx (:driver s)))
(defn- binding-of [s]
  {:engine (:engine s) :source (:source s) :adapter (:adapter s) :current-ctx (:current-ctx (:driver s))})
(defn- live! [holder]
  (let [s @holder]
    (need (= :active (:status s)) "Generated scope is closed or failed")
    (need (identical? (:thread s) (Thread/currentThread)) "Generated scope is thread confined")
    (let [d (:driver s) c (context s) e (:engine s)]
      (need (and (identical? e (:engine d)) (identical? (:source s) (:source d))
                 (identical? (:program c) (field e "program"))) "Generated scope engine/source/Program changed")
      (doseq [k ["closed" "disposed" "untrackedFailure" "advancing"]]
        (need (false? (field e k)) "Generated scope requires live idle custody"))
      (need (= "idle" (j/phase c e)) "Generated scope requires idle engine")
      (let [policy (:authenticated-demand d)]
        (need (fn? (:check-source! policy)) "Authenticated original-source resolver required")
        ((:check-source! policy) d))
      s)))
(defn- operation! [holder f]
  (live! holder)
  (need (nil? (:operation @holder)) "Reentrant generated scope operation")
  (let [prior (:next-command @holder)]
    (swap! holder assoc :operation :active)
    (try (f)
      (catch Throwable cause
        ;; An issuer post-check can fail after our callback recorded an interval.
        ;; Never expose that partially acknowledged scope as a fresh next command.
        (when (not= prior (:next-command @holder)) (swap! holder assoc :status :failed))
        (throw cause))
      (finally (swap! holder assoc :operation nil)))))
(defn- program-index [program binding]
  (reduce (fn [out function]
            (let [h (field function "header")]
              (need h "Headerless inherited Program is outside the general generated route")
              (need (identical? binding (j/request-value h "source")) "Inherited Header belongs to a foreign SourceBinding")
              (let [n (j/lean-name-data (j/request-value h "name")) label (source/label n)]
                (need (not (contains? out label)) "Inherited Program has ambiguous runtime labels")
                (assoc out label {:name n :header h})))) {} (seq (field program "functions"))))
(defn- typed-name! [name]
  (loop [n name depth 0 characters 0]
    (need (and (<= depth 256) (<= characters 65536)) "Generated typed Name exceeds depth/text bound")
    (if (= ["anonymous"] n) name
      (do
        (need (and (vector? n) (= 3 (count n)) (contains? #{"str" "num"} (first n))) "Malformed generated typed Name")
        (let [[kind _ leaf] n]
          (need (if (= kind "str") (and (string? leaf) (<= (count leaf) 65536))
                  (or (and (string? leaf) (boolean (re-matches #"0|[1-9][0-9]*" leaf))
                           (<= (count leaf) 20) (<= (bigint leaf) 18446744073709551615N))
                      (and (contains? #{Long Integer Short Byte java.math.BigInteger} (class leaf))
                           (<= 0 leaf 18446744073709551615N)))) "Malformed generated typed Name component"))
        (recur (second n) (inc depth) (+ characters (if (string? (nth n 2)) (count (nth n 2)) 20)))))))
(defn- key-of [name] (source/name-key (typed-name! name)))
(defn- ir-inventory! [rows]
  (need (and (map? rows) (<= (count rows) 2048)) "Bounded complete command IR map required")
  (reduce-kv (fn [out name row]
               (typed-name! name)
               (need (and (map? row) (string? (:kind row)) (map? (:declaration row))
                          (= name (get (:declaration row) "f"))) "Command IR declaration identity differs")
               (let [label (source/label name)]
                 (need (and (seq label) (not (contains? out label))) "Generated typed Names collide at runtime display label")
                 (assoc out label name))) {} rows))
(defn- frontier! [raw]
  ;; Walk only the complete FnBody, including every nested Expr. AP paths are
  ;; observations, never a claim that the dynamic closure graph is closed.
  (loop [todo [[(get raw "body") []]] visits 0 targets {} aps []]
    (need (and (< visits 1000000) (<= (count todo) 100000) (<= (count targets) 20000)
               (<= (count aps) 16384)) "Generated structural frontier exceeds bounds")
    (if (empty? todo)
      {:static (mapv val (sort-by key targets)) :dynamic-ap aps}
      (let [[x path] (peek todo) tail (pop todo)]
        (need (<= (count path) 512) "Generated structural depth exceeds bounds")
        (cond
          (map? x)
          (let [targets (reduce (fn [out kind]
                                 (if (contains? x kind)
                                   (let [name (get-in x [kind "c"])] (assoc out (key-of name) name)) out))
                               targets ["fap" "pap"])
                aps (if (contains? x "ap") (conj aps (conj path "ap")) aps)]
            (recur (into tail (map (fn [k] [(get x k) (conj path k)]) (sort (keys x)))) (inc visits) targets aps))
          (vector? x) (recur (into tail (map-indexed (fn [i v] [v (conj path i)]) x)) (inc visits) targets aps)
          :else (recur tail (inc visits) targets aps))))))
(defn- bounded-row! [row]
  ;; Metadata outside FnBody also reaches recursive JSON/Header freezing. Bound
  ;; the complete immutable row before invoking either recursive consumer.
  (loop [todo [[row 0]] visits 0 characters 0]
    (need (and (< visits 1000000) (<= (count todo) 100000) (<= characters 4000000))
          "Generated row exceeds work/text bounds")
    (when-let [[value depth] (peek todo)]
      (need (<= depth 512) "Generated row exceeds serialization depth bound")
      (let [tail (pop todo) next-depth (inc depth)]
        (cond
          (map? value) (recur (into tail (map (fn [x] [x next-depth]) (concat (keys value) (vals value)))) (inc visits) characters)
          (vector? value) (recur (into tail (map (fn [x] [x next-depth]) value)) (inc visits) characters)
          :else (recur tail (inc visits) (+ characters (if (string? value) (count value) 0))))))))
(defn- digest [row] (source/bytes-sha (.getBytes (json/write-str row) java.nio.charset.StandardCharsets/UTF_8)))
(defn- generated-row [name ir]
  ;; This digest identifies captured compiler output, not a catalogue CAS file.
  ;; Do not invent runtime/redirect/sourceLocal metadata from an fdecl's shape.
  {"kind" "decl" "name" name "ir" {"fdecl" (:declaration ir)}})
(defn- same-header! [s expected actual]
  (need (and (identical? expected actual) (identical? (:source s) (j/request-value actual "source")))
        "Static dependency canonical Header/source changed") actual)
(defn- resolve-original! [s name]
  (let [h (demand/ensure-header! (:driver s) name)]
    (need (identical? (:source s) (j/request-value h "source")) "Original dependency belongs to foreign source") h))
(defn- source-policy! [view]
  (let [p (:source-policy view)]
    (need (and (= :observed-classic-prelude-command-v1 (:profile p))
               (contains? #{:command :eoi :exit} (:kind p))
               (= :no-local-initializers-exports-externs-redirects-v1 (:requirements-policy p))) "Actual reviewed structural source-policy witness required")))
(defn- receipt-view! [s view]
  (need (and (identical? (:engine s) (:engine view)) (identical? (:source s) (:source view))
             (identical? (:driver s) (:driver view)) (identical? (:adapter s) (:adapter view)))
        "CommandReceipt belongs to another generated scope branch")
  (source-policy! view)
  (need (and (:file-marker view) (integer? (:command-index view))
             (<= 0 (:command-index view) 127)
             (= (:next-command s) (:command-index view))
             (or (nil? (:file-marker s)) (identical? (:file-marker s) (:file-marker view))))
        "Replayed/skipped command or foreign captured file")
  (ir-inventory! (:before-ir view)) (ir-inventory! (:after-ir view))
  (need (= (:observed-ir s) (:before-ir view)) "CommandReceipt is not the next complete local IR interval")
  (doseq [[n row] (:before-ir view)]
    (need (= row (get (:after-ir view) n)) "Compiler changed an old generated IR declaration"))
  (need (= (:delta view) (apply dissoc (:after-ir view) (keys (:before-ir view)))) "CommandReceipt delta is incomplete")
  (need (:version-marker view) "Actual checked version marker required"))
(defn open-scope!
  "One fresh generic file on one actual driver/adapter. Receipts independently
   cross-bind these identities; an empty initial IR interval is required at first
   prepare. Borrows all runtime/source resources and owns host metadata only."
  [driver adapter]
  (let [holder (atom {:status :active :thread (Thread/currentThread) :driver driver :adapter adapter
                      :engine (:engine driver) :source (:source driver) :file-marker nil :next-command 0
                      :observed-ir {} :locals {} :pending nil})
        token (Scope.)]
    (live! holder) (program-index (:program (context @holder)) (:source @holder))
    (locking scopes (.put scopes token holder)) token))
(defn prepare-batch!
  "Read complete compiler IR exclusively through a live CommandReceipt lease.
   Returns :empty, :unsupported, or an opaque :prepared Batch. Successful command
   custody/checking remains separate in every case. No Program is installed."
  [scope receipt]
  (let [holder (issued scopes scope)]
    (operation! holder
      #(let [s (live! holder)]
         (need (nil? (:pending s)) "Link the pending batch before another command")
         (command/with-command! receipt (binding-of s)
           (fn [view]
             (receipt-view! s view)
             (let [delta (:delta view)]
               (if (empty? delta)
                 (do (swap! holder assoc :observed-ir (:after-ir view) :file-marker (:file-marker view)
                                     :next-command (inc (:command-index view))) {:status :empty :row-count 0})
                 (let [result
                       (try
                         (when-not (= :command (get-in view [:source-policy :kind]))
                           (unsupported! "Terminal source command unexpectedly emitted executable code"))
                         (doseq [[_ ir] delta]
                           (when-not (= "fdecl" (:kind ir)) (unsupported! "Generated delta includes an unadmitted declaration kind")))
                         (let [base (context (live! holder)) index (program-index (:program base) (:source s))
                               ordered (sort-by (comp key-of key) delta)
                               rows (into {} (map (fn [[n ir]] [n (generated-row n ir)]) ordered))
                               _ (doseq [[n _] ordered]
                                   (when (contains? index (source/label n)) (unsupported! "Generated Name overlaps inherited Program label"))
                                   ;; A local may not steal even an unregistered original Name.
                                   (when (source/lookup-entry (:source-receipt view) n)
                                     (unsupported! "Generated Name overlaps authenticated source domain")))
                               frontiers (into {} (map (fn [[n ir]] [n (frontier! (:declaration ir))]) ordered))
                               _ (doseq [[_ row] rows] (bounded-row! row))
                               headers (into {} (map (fn [[n row]] [n (j/declaration-header (:source s) row (digest row))]) rows))
                               originals (atom {})
                               resolve! (fn [n]
                                          (or (get headers n) (get-in s [:locals n :header])
                                              (do
                                                (when (contains? (:observed-ir s) n)
                                                  (unsupported! "Earlier local IR dependency was never linked"))
                                                (or (get @originals n)
                                                    (let [h (resolve-original! s n)] (swap! originals assoc n h) h)))))
                               deps (into {} (map (fn [[n f]] [n (mapv resolve! (remove #{n} (:static f)))]) frontiers))
                               ;; All SCC/local/dependency shells precede every body.
                               registered (j/register-headers base (vec (concat (vals headers) (vals @originals)
                                                                                (map :header (vals (:locals s))))))
                               prepared (reduce (fn [ctx [n _]] (j/materialize-body ctx (get headers n) (get rows n) (get deps n)))
                                                registered ordered)
                               _ (live! holder)
                               _ (need (identical? (:program base) (:program (context @holder))) "Program changed during generated staging")
                               token (Batch.) marker (Object.) b (atom {:status :prepared :scope-holder holder :receipt receipt :marker marker
                                                      :version-marker (:version-marker view) :version-id (:version-id view)
                                                      :base-program (:program base) :prepared prepared :rows rows :headers headers
                                                      :originals @originals :frontiers frontiers})]
                           (locking batches (.put batches token b))
                           {:status :prepared :batch token :row-count (count rows)
                            :pending-marker marker :frontiers frontiers :version-id (:version-id view) :dynamic-ap-count (reduce + (map (fn [frontier] (count (:dynamic-ap frontier))) (vals frontiers)))})
                         (catch Exception cause
                           {:status :unsupported :row-count (count delta)
                            :reason (subs (or (.getMessage cause) "Generated preparation failed") 0
                                          (min 800 (count (or (.getMessage cause) "Generated preparation failed"))))}))]
                   (live! holder)
                   (swap! holder assoc :observed-ir (:after-ir view) :file-marker (:file-marker view)
                          :next-command (inc (:command-index view)) :pending (when (= :prepared (:status result)) (:pending-marker result)))
                   (dissoc result :pending-marker))))))))))
(defn link-batch!
  "Atomically publish the staged descendant once on its unchanged actual branch.
   A thrown install quarantines the scope; this API never retries uncertain work."
  [batch]
  (let [bh (issued batches batch) b @bh holder (:scope-holder b)]
    (operation! holder
      #(let [s (live! holder)]
         (need (and (= :prepared (:status @bh)) (identical? (:marker b) (:pending s))
                    (identical? (:base-program b) (:program (context s)))) "Stale/linked/foreign generated batch")
         (try
           (command/with-command! (:receipt b) (binding-of s)
             (fn [view]
               (need (and (identical? (:version-marker b) (:version-marker view)) (= (:version-id b) (:version-id view))
                          (identical? (:file-marker s) (:file-marker view))
                          (= (dec (:next-command s)) (:command-index view)))
                     "Checked version advanced after generated preparation")
               (source-policy! view)
               (let [index (program-index (:program (context s)) (:source s))]
                 (doseq [[n {:keys [header]}] (:locals s)]
                   (same-header! s header (get-in index [(source/label n) :header])))
                 (doseq [[n h] (:originals b)] (same-header! s h (resolve-original! s n))))
               (live! holder)
               (need (identical? (:base-program b) (:program (context s))) "Dependency check changed actual base Program")
               ;; Original resolution is callback-capable. Reborrow AFTER those
               ;; callbacks, immediately before the non-callback install step.
               (command/with-command! (:receipt b) (binding-of s)
                 (fn [current]
                   (need (identical? (:version-marker b) (:version-marker current)) "Dependency check changed checked version")))
               (swap! bh assoc :status :install-pending)
               (j/install-program! (:prepared b) (:engine s))
               (reset! (:current-ctx (:driver s)) (:prepared b))
               (live! holder)
               (swap! holder assoc :pending nil :locals
                      (reduce-kv (fn [m n h] (assoc m n {:header h :row (get (:rows b) n)})) (:locals s) (:headers b)))
               (swap! bh (fn [state] (-> state (assoc :status :linked) (dissoc :receipt :prepared :base-program :originals))))
               {:status :linked :row-count (count (:rows b))}))
           (catch Throwable cause
             ;; Includes a failed issuer post-check AFTER a real installation.
             (when (contains? #{:install-pending :linked} (:status @bh))
               (swap! bh assoc :status :failed) (swap! holder assoc :status :failed))
             (throw cause)))))))
(defn close!
  "Revoke resolution/linkage and drop host metadata only. Never closes borrowed
   source/adapter resources or releases command/module/Run guest occurrences."
  [scope]
  (let [holder (issued scopes scope)]
    (need (identical? (:thread @holder) (Thread/currentThread)) "Generated scope is thread confined")
    (need (nil? (:operation @holder)) "Cannot close active generated operation")
    (locking batches
      (doseq [entry (.entrySet batches)
              :let [bh (.getValue ^java.util.Map$Entry entry)]
              :when (identical? holder (:scope-holder @bh))]
        (reset! bh {:status :closed :scope-holder holder})))
    (reset! holder {:status :closed :thread (:thread @holder)})) nil)
