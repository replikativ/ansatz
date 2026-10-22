(ns prototype.bootstrap-archive
  "Experimental streamed completed-world archives, compatible with the original
   ansatz-frontend-bootstrap-archive/1 rows. Not general durable runtime storage:
   native sources, Java kernel associations, executable identity authorizations,
   opaque resources and raw lossy float
   carriers are excluded. SHA and pinned commit are explicit restore authority;
   serialized executable code is data, never evaluated by the reader."
  (:require [clojure.edn :as edn] [clojure.java.io :as io] [prototype.machine :as m])
  (:import [java.io BufferedWriter OutputStreamWriter PushbackReader]
           [java.nio.file Files StandardCopyOption]
           [java.security MessageDigest DigestInputStream DigestOutputStream]))
(def format-id "ansatz-frontend-bootstrap-archive/1")
(def lean-version "4.33.1")
(def lean-commit "819816b2e0a3bf405af45ae5c7af2491d8f5bee6")
(def ^:private stack-bytes (* 16 1024 1024))
(defn- fail [message data] (throw (ex-info message data)))
(defn- sha [bytes] (apply str (map #(format "%02x" (bit-and 255 %)) bytes)))
(defn- worker [f]
  (let [result (promise)
        thread (Thread. nil (reify Runnable
                              (run [_] (try (deliver result [:ok (f)])
                                            (catch Throwable e (deliver result [:error e])))))
                        "ansatz-bootstrap-archive" stack-bytes)]
    (.start thread)
    (let [[status value] @result] (if (= :ok status) value (throw value)))))
(defn- counts [world] (into {} (map (fn [k] [k (count (get world k))]) [:functions :heap :globals])))
(defn- counts! [value]
  (when-not (and (map? value) (= #{:functions :heap :globals} (set (keys value)))
                 (every? #(and (integer? %) (<= 0 % Long/MAX_VALUE)) (vals value)))
    (fail "Invalid bootstrap archive counts" {})) value)
(defn- header! [header expected-commit]
  (when-not (and (map? header) (= format-id (:format header))
                 (= lean-version (:lean-version header)) (= lean-commit expected-commit (:lean-commit header))
                 (= :done (:status header)))
    (fail "Bootstrap archive header/provenance mismatch" {}))
  (counts! (:counts header)) header)
(defn- state! [state]
  (when-not (and (map? state) (= :done (:status state))
                 (not-any? #(contains? state %) [:functions :heap :globals])
                 (integer? (:next-id state)) (<= 0 (:next-id state) Long/MAX_VALUE))
    (fail "Bootstrap archive requires completed immutable state" {}))
  (when (or (seq (:native-imports state)) (seq (:kernel-environments state)))
    (fail "Native sources/kernel associations are outside bootstrap archive" {}))
  ;; These capability maps require object identity with :functions. EDN can
  ;; preserve equal code but cannot preserve that shared object identity. A
  ;; future reattachment format must explicitly validate and canonicalize it.
  (when (or (seq (:source-modules state)) (seq (:source-regions state)) (seq (:source-import-prefixes state)))
    (fail "Owned source module capabilities are outside bootstrap archive" {}))
  (when (seq (:eval-const-authorizations state))
    (fail "Executable identity authorizations are outside bootstrap archive" {})) state)
(defn- plain!
  ([root world] (plain! root world true))
  ([root world check-references?]
   (let [pending (java.util.ArrayDeque.)]
    ;; Wrapped values allow nil without putting nil into ArrayDeque.
     (.push pending [root])
     (while (not (.isEmpty pending))
       (let [[v] (.pop pending)]
         (when-let [metadata (meta v)] (.push pending [metadata]))
         (cond
           (m/ref? v)
           (when-not (and (= #{:id} (set (keys v))) (integer? (:id v))
                          (<= 0 (:id v) Long/MAX_VALUE)
                          (or (not check-references?) (contains? (:heap world) (:id v))))
             (fail "Invalid/dangling bootstrap guest reference" {:ref v}))
           (instance? prototype.machine.Tag v)
           (when-not (and (= #{:tag} (set (keys v))) (integer? (:tag v)) (<= 0 (:tag v) 255))
             (fail "Invalid bootstrap guest Tag" {}))
           (instance? prototype.machine.Builtin v)
           (when-not (and (= #{:name} (set (keys v))) (keyword? (:name v)))
             (fail "Invalid bootstrap guest Builtin" {}))
           (record? v) (fail "Opaque record is outside bootstrap archive" {:class (str (class v))})
           (map? v) (doseq [[k value] v] (.push pending [k]) (.push pending [value]))
           (or (vector? v) (set? v) (list? v)) (doseq [child v] (.push pending [child]))
           (instance? Float v) (fail "Raw Float carrier is outside bootstrap archive" {})
           (instance? Double v) (when (Double/isNaN v) (fail "Raw NaN carrier is outside bootstrap archive" {}))
           (or (nil? v) (boolean? v) (string? v) (keyword? v) (symbol? v) (char? v)
               (integer? v) (ratio? v) (decimal? v)) nil
           :else (fail "Opaque value is outside bootstrap archive" {:class (str (class v))})))))))
(def ^:private inactive-control-keys [:body :locals :joins :frames :result :resume-var :host-request])
(defn- plain-state! [state world]
  ;; Explicit RC drops do not clear dead registers. In a completed world these
  ;; slots are inert data, never owners; m/start replaces them before execution.
  (plain! (apply dissoc state inactive-control-keys) world)
  (plain! (select-keys state inactive-control-keys) world false))
(defn- world! [world]
  (doseq [k [:functions :heap :globals]]
    (when-not (map? (get world k)) (fail "Invalid bootstrap world map" {:key k})))
  (state! (dissoc world :functions :heap :globals))
  (doseq [[name function] (:functions world)]
    (when-not (and (map? function) (vector? (:params function)) (vector? (:body function)))
      (fail "Invalid bootstrap executable declaration" {:name name})))
  (doseq [[id node] (:heap world)]
    (when-not (and (integer? id) (<= 0 id) (< id (:next-id world)) (map? node)
                   (keyword? (:kind node)) (not= :resource (:kind node))
                   (vector? (:fields node)) (integer? (:rc node)) (<= 0 (:rc node) Long/MAX_VALUE))
      (fail "Invalid/unsupported bootstrap heap node" {:id id}))
    (when (and (= :closure (:kind node)) (not (contains? (:functions world) (:function node))))
      (fail "Bootstrap closure lacks executable target" {:id id})))
  world)
(defn- same-data? [a b]
  ;; = ignores metadata and recursively compares deep bodies. Compare one row
  ;; iteratively, including nested metadata, without constructing a second world.
  (loop [todo [[a b false]]]
    (if (empty? todo) true
        (let [[a b metadata?] (peek todo) todo (pop todo)]
          (cond
            (and (not metadata?) (not (identical? (meta a) (meta b))))
            (recur (conj todo [a b true] [(meta a) (meta b) false]))
            (identical? a b) (recur todo)
            (map? a)
            (if (and (map? b) (= (count a) (count b)) (= (record? a) (record? b))
                     (or (not (record? a)) (= (class a) (class b))))
              (let [entries (map (fn [[k v]] (when-let [e (find b k)] [[k (key e) false] [v (val e) false]])) a)]
                (if (every? some? entries) (recur (into todo (mapcat identity entries))) false)) false)
            (or (vector? a) (list? a))
            (if (and (if (vector? a) (vector? b) (list? b)) (= (count a) (count b)))
              (recur (into todo (map #(vector %1 %2 false) a b))) false)
            (set? a) (if (and (set? b) (= (count a) (count b)) (every? #(contains? b %) a))
                       (recur (into todo (map #(vector % (get b %) false) a))) false)
            (or (map? b) (vector? b) (list? b) (set? b)) false
            (= a b) (recur todo)
            :else false)))))
(defn- tagged [tag constructor]
  (fn [value]
    (when-not (map? value) (fail "Malformed bootstrap record tag" {:tag tag})) (constructor value)))
(def ^:private readers
  {'prototype.machine.Ref (tagged 'prototype.machine.Ref m/map->Ref)
   'prototype.machine.Tag (tagged 'prototype.machine.Tag m/map->Tag)
   'prototype.machine.Builtin (tagged 'prototype.machine.Builtin m/map->Builtin)
   'inst (fn [_] (fail "Non-guest EDN tag is outside bootstrap archive" {:tag 'inst}))
   'uuid (fn [_] (fail "Non-guest EDN tag is outside bootstrap archive" {:tag 'uuid}))})
(defn- read-row [reader eof]
  (edn/read {:eof eof :readers readers
             :default (fn [tag _] (fail "Unknown bootstrap archive tag" {:tag tag}))} reader))
(defn- record! [row kind n]
  (when-not (and (vector? row) (= n (count row)) (= kind (first row)))
    (fail "Malformed/truncated bootstrap archive row" {:expected kind})) row)
(defn- scan [path consume]
  (let [digest (MessageDigest/getInstance "SHA-256") eof (Object.)]
    (with-open [input (DigestInputStream. (io/input-stream path) digest)
                reader (PushbackReader. (io/reader input :encoding "UTF-8"))]
      (let [result (consume #(read-row reader eof) eof)]
        (assoc result :sha256 (sha (.digest digest)) :bytes (.length (io/file path)))))))

(defn- share-name-prefixes
  "Share exact metadata-free Name trees within one restore. The map contains
   ONLY canonical Name vectors, never functions, arbitrary vectors or records."
  [^java.util.HashMap names root]
  (letfn [(visit [value]
            (let [changed
                  (cond
                    (vector? value)
                    (reduce-kv (fn [out index child]
                                 (let [next-child (visit child)]
                                   (if (identical? child next-child) out (assoc out index next-child))))
                               value value)
                    (map? value)
                    ;; Starting from the original also preserves Ref/Tag/Builtin
                    ;; record types. Fixed record keys are unchanged keywords.
                    (reduce-kv (fn [out key child]
                                 (let [next-key (visit key) next-child (visit child)]
                                   (cond
                                     (and (identical? key next-key) (identical? child next-child)) out
                                     (identical? key next-key) (assoc out key next-child)
                                     :else (assoc (dissoc out key) next-key next-child))))
                               value value)
                    (list? value)
                    (let [children (mapv visit value)]
                      (if (every? true? (map identical? value children)) value
                          (with-meta (apply list children) (meta value))))
                    (set? value)
                    (reduce (fn [out child]
                              (let [next-child (visit child)]
                                (if (identical? child next-child) out
                                    (conj (disj out child) next-child)))) value value)
                    :else value)
                  metadata (meta value)
                  next-metadata (when metadata (visit metadata))
                  changed (if (identical? metadata next-metadata) changed
                              (with-meta changed next-metadata))]
              (if (and (vector? changed) (nil? (meta changed))
                       (or (and (= 1 (count changed)) (= "anonymous" (first changed)))
                           (and (= 3 (count changed))
                                (let [[kind prefix component] changed]
                                  (and (string? component)
                                       (or (= "str" kind)
                                           (and (= "num" kind) (re-matches #"[0-9]+" component)))
                                       (vector? prefix)
                                       ;; Equality ignores metadata. Identity with
                                       ;; a previously canonical prefix proves the
                                       ;; ENTIRE prefix chain was metadata-free.
                                       (identical? prefix (.get names prefix)))))))
                (or (.get names changed)
                    (do (.put names changed changed) changed))
                changed)))]
    (visit root)))

(defn restore
  "Restore the original streamed format. Both expected SHA256 and pinned commit
   are mandatory; no code is evaluated, substituted or automatically upgraded.
   Returns {:world :header :sha256 :bytes}. :share-names? defaults to true:
   a restore-local pool shares exact metadata-free serialized Name prefixes,
   without changing bytes, metadata, guest ownership or executable authority.
   False retains the unshared baseline. Memory is one restored world plus the
   current EDN record and temporary Name pool; a fixed worker stack accommodates
   nested IR bodies. The pool is cleared before whole-world validation."
  [path {:keys [expected-sha256 expected-lean-commit share-names?]
         :or {share-names? true}}]
  (when-not (and (string? expected-sha256) (re-matches #"[0-9a-f]{64}" expected-sha256)
                 (= lean-commit expected-lean-commit))
    (fail "Bootstrap restore requires explicit SHA256 and pinned commit" {}))
  (when-not (boolean? share-names?)
    (fail "Bootstrap name sharing option must be boolean" {}))
  (worker
   #(let [names (when share-names? (java.util.HashMap.))
          result
          (scan path
                (fn [read-next-row eof]
                  (let [next-row (if names
                                   (fn [] (share-name-prefixes names (read-next-row)))
                                   read-next-row)
                        header (second (record! (next-row) :header 2))]
                    (header! header expected-lean-commit)
                    (loop [functions (transient {}) heap (transient {}) globals (transient {}) state nil
                           actual {:functions 0 :heap 0 :globals 0}]
                      (let [row (next-row)]
                        (when-not (vector? row) (fail "Malformed/truncated bootstrap archive" {}))
                        (case (first row)
                          (:function :heap :global)
                          (let [[kind k v] (record! row (first row) 3)
                                _ (when state (fail "Bootstrap data row follows state" {}))
                                table (case kind :function functions :heap heap :global globals)
                                key (case kind :function :functions :heap :heap :global :globals)]
                            (when (contains? table k) (fail "Duplicate bootstrap archive entry" {:kind kind :key k}))
                            (when (>= (get actual key) (get-in header [:counts key]))
                              (fail "Bootstrap archive exceeds declared counts" {:kind kind}))
                            (recur (if (= kind :function) (assoc! functions k v) functions)
                                   (if (= kind :heap) (assoc! heap k v) heap)
                                   (if (= kind :global) (assoc! globals k v) globals) state (update actual key inc)))
                          :state (do (record! row :state 2)
                                     (when state (fail "Duplicate bootstrap state" {}))
                                     (state! (second row)) (recur functions heap globals (second row) actual))
                          :end (do (record! row :end 2)
                                   (when-not (and state (= actual (:counts header) (second row)) (identical? eof (next-row)))
                                     (fail "Bootstrap archive counts/trailer mismatch" {}))
                                   (let [world (assoc state :functions (persistent! functions) :heap (persistent! heap)
                                                      :globals (persistent! globals))]
                                     (when names (.clear ^java.util.HashMap names))
                                     (world! world)
                                     (plain! header world)
                                     (doseq [[k table] (select-keys world [:functions :heap :globals]) [key value] table]
                                       (plain! key world) (plain! value world))
                                     (plain-state! state world)
                                     {:header header :world world}))
                          (fail "Unknown bootstrap archive record" {:kind (first row)})))))))]
      (when-not (= expected-sha256 (:sha256 result)) (fail "Bootstrap archive SHA256 mismatch" {})) result)))

(defn write!
  "Atomically stream/verify a completed world in the old format. Header must
   explicitly supply pinned :lean-version/:lean-commit; computed fields cannot
   conflict. Verification compares rows in emission order against the original
   world, including metadata, without restoring a second heap/function table."
  [path world header]
  (worker
   #(do
      (world! world)
      (let [actual (counts world)
            computed {:format format-id :counts actual :status (:status world)}
            _ (doseq [[k value] computed :when (contains? header k)]
                (when-not (= value (get header k)) (fail "Conflicting bootstrap archive header" {:key k})))
            header (merge header computed)
            _ (header! header lean-commit)
            _ (plain! header world)
            file (.getAbsoluteFile (io/file path))
            temp (java.io.File/createTempFile ".bootstrap-archive-" ".edn" (.getParentFile file))]
        (try
          (let [digest (MessageDigest/getInstance "SHA-256")
                state (dissoc world :functions :heap :globals)]
            (with-open [output (DigestOutputStream. (io/output-stream temp) digest)
                        writer (BufferedWriter. (OutputStreamWriter. output "UTF-8") 65536)]
              (binding [*out* writer *print-meta* true *print-level* nil *print-length* nil]
                (prn [:header header])
                (doseq [[kind key] [[:function :functions] [:heap :heap] [:global :globals]]
                        [name value] (get world key)]
                  (plain! name world) (plain! value world) (prn [kind name value]))
                (plain-state! state world) (prn [:state state]) (prn [:end actual])))
            (let [expected-sha (sha (.digest digest))
                  verified (scan temp
                                 (fn [next-row eof]
                                   (let [match! (fn [expected]
                                                  (when-not (same-data? expected (next-row))
                                                    (fail "Bootstrap archive verification mismatch" {})))]
                                     (match! [:header header])
                                     (doseq [[kind key] [[:function :functions] [:heap :heap] [:global :globals]]
                                             [name value] (get world key)] (match! [kind name value]))
                                     (match! [:state state]) (match! [:end actual])
                                     (when-not (identical? eof (next-row)) (fail "Trailing bootstrap archive data" {}))
                                     {:counts actual})))]
              (when-not (= expected-sha (:sha256 verified)) (fail "Bootstrap archive verification digest mismatch" {}))
              (Files/move (.toPath temp) (.toPath file)
                          (into-array StandardCopyOption [StandardCopyOption/ATOMIC_MOVE StandardCopyOption/REPLACE_EXISTING]))
              (assoc verified :path (str path) :header header :verified true)))
          (finally (.delete temp)))))))

;; Append inside prototype.bootstrap-archive. DRAFT, no existing API changes.
(defn verify-function-rows
  "Authenticate a pinned bootstrap archive without retaining its function/heap
   graph. VERIFY-FUNCTION receives each original [name function] as two arguments
   and returns [canonical-name canonical-function] from a caller-owned table.
   The trusted callback may refresh archived ABI externs from independently pinned
   declaration rows; it must verify every resulting candidate exactly. No callback
   effect is authorized: all results remain private until the full-stream digest,
   structure, counts and trailer pass. Returns canonical references only.
   This is not restore or a second whole-world heap/reference validity proof."
  [path {:keys [expected-sha256 expected-lean-commit verify-function]}]
  (when-not (and (string? expected-sha256) (re-matches #"[0-9a-f]{64}" expected-sha256)
                 (= lean-commit expected-lean-commit) (fn? verify-function))
    (fail "Bootstrap function verification requires explicit pinned authority/callback" {}))
  (worker
    (fn []
      (let [result
            (scan path
              (fn [next-row eof]
                (let [header (second (record! (next-row) :header 2))
                      _ (header! header expected-lean-commit)
                      heap-ids (java.util.HashSet.) global-names (java.util.HashSet.)]
                  (loop [functions (transient {}) state-next-id nil actual {:functions 0 :heap 0 :globals 0}]
                    (let [row (next-row)]
                      (when-not (vector? row) (fail "Malformed/truncated bootstrap archive" {}))
                      (case (first row)
                        (:function :heap :global)
                        (let [[kind name value] (record! row (first row) 3)
                              counter (case kind :function :functions :heap :heap :global :globals)]
                          (when (or (some? state-next-id) (>= (get actual counter) (get-in header [:counts counter])))
                            (fail "Bootstrap function scan exceeds declared table/order" {:kind kind}))
                          (if (= :function kind)
                            (let [[canonical-name function :as admitted] (verify-function name value)]
                              (when-not (and (vector? admitted) (= 2 (count admitted))
                                             (= name canonical-name) (map? function)
                                             (vector? (:params function)) (vector? (:body function)))
                                (fail "Function verifier returned invalid canonical entry" {:name name}))
                              (when (contains? functions canonical-name) (fail "Duplicate bootstrap function" {:name name}))
                              (recur (assoc! functions canonical-name function) state-next-id (update actual counter inc)))
                            (do
                              (when-not (.add ^java.util.HashSet (if (= kind :heap) heap-ids global-names) name)
                                (fail "Duplicate bootstrap table entry" {:kind kind}))
                              ;; Header digest authenticates all skipped heap and
                              ;; global bytes. Do not pretend they were restored.
                              (recur functions state-next-id (update actual counter inc)))))
                        :state (do (record! row :state 2)
                                   (when (some? state-next-id) (fail "Duplicate bootstrap state" {}))
                                   (state! (second row))
                                   (recur functions (:next-id (second row)) actual))
                        :end (do (record! row :end 2)
                                 (when-not (and (some? state-next-id) (= actual (:counts header) (second row))
                                                (identical? eof (next-row)))
                                   (fail "Bootstrap function scan counts/trailer mismatch" {}))
                                 {:functions (persistent! functions) :header header :next-id state-next-id})
                        (fail "Unknown bootstrap archive record" {:kind (first row)})))))))]
        (when-not (= expected-sha256 (:sha256 result)) (fail "Bootstrap archive SHA256 mismatch" {}))
        result))))
