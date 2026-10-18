(ns ansatz.bundle-metadata
  "Strict companion-row validation and name selection. This leaf preserves
   captured fields and order; it neither installs metadata nor grants kernel trust."
  (:require [clojure.data.json :as json]
            [clojure.string :as str])
  (:import [java.io ByteArrayInputStream]
           [java.nio ByteBuffer]
           [java.nio.charset CodingErrorAction StandardCharsets]
           [java.util.zip GZIPInputStream]))

(def roles #{:attrs :matchers :instances})
(def max-priority 4294967295)
(defn- fail [message data] (throw (ex-info message data)))
(defn- name? [value] (and (string? value) (not (str/blank? value))))
(defn- nat? [value] (and (integer? value) (<= 0 value Integer/MAX_VALUE)))
(defn- priority? [value] (and (integer? value) (<= 0 value max-priority)))
(defn- keys? [row required optional]
  (and (map? row) (every? #(contains? row %) required)
       (every? (into required optional) (keys row))))

(defn- valid-attr? [{:keys [kind name target prio theorems] :as row}]
  (and (name? name)
       (case kind
         "simp" (and (keys? row #{:kind :name :prio} #{:post :inv}) (priority? prio)
                     (= (contains? row :post) (contains? row :inv))
                     (or (not (contains? row :post))
                         (and (boolean? (:post row)) (boolean? (:inv row)))))
         ("unfold" "extern") (keys? row #{:kind :name} #{})
         ("csimp" "impl") (and (keys? row #{:kind :name :target} #{}) (name? target))
         "unfold-thms" (and (keys? row #{:kind :name :theorems} #{})
                            (vector? theorems) (every? name? theorems))
         false)))

(defn- valid-matcher? [{:keys [name numParams numDiscrs uElimPos discrs overlaps alts] :as row}]
  (and (keys? row #{:name :numParams :numDiscrs :uElimPos :discrs :overlaps :alts} #{})
       (name? name) (nat? numParams) (nat? numDiscrs) (or (nil? uElimPos) (nat? uElimPos))
       (vector? discrs) (= numDiscrs (count discrs))
       (every? #(or (nil? %) (name? %)) discrs)
       (vector? alts)
       (every? #(and (keys? % #{:numFields :numOverlaps :unitThunk} #{})
                     (nat? (:numFields %)) (nat? (:numOverlaps %)) (boolean? (:unitThunk %))) alts)
       (vector? overlaps) (= (count overlaps) (count (set overlaps)))
       (every? #(and (vector? %) (= 2 (count %)) (every? nat? %)
                     (not= (first %) (second %)) (every? (fn [idx] (< idx (count alts))) %)) overlaps)))

(defn- valid-instance? [{:keys [class name priority] :as row}]
  (and (keys? row #{:class :name :priority} #{}) (name? class) (name? name)
       (not (re-find #"[\t\r\n]" class)) (not (re-find #"[\t\r\n]" name))
       (priority? priority)))

(defn- row! [role row line]
  (when-not (and (map? row)
                 (case role :attrs (valid-attr? row) :matchers (valid-matcher? row)
                       :instances (valid-instance? row) false))
    (fail "Invalid bundled companion row" {:role role :line line :row row}))
  row)

(defn- lines [text]
  (when-not (string? text) (fail "Companion text must be a string" {}))
  (if (empty? text) []
      (let [rows (str/split text #"\r?\n" -1)]
        (if (= "" (peek rows)) (pop rows) rows))))

(defn- json-row [^String text]
  ;; data.json deliberately overwrites duplicate object keys. Detect them in
  ;; their own container before delegating complete syntax/number parsing.
  (loop [index 0 stack []]
    (when (< index (.length text))
      (let [ch (.charAt text index)]
        (cond
          (= ch \{) (recur (inc index) (conj stack #{}))
          (= ch \[) (recur (inc index) (conj stack nil))
          (or (= ch \}) (= ch \])) (recur (inc index) (if (seq stack) (pop stack) stack))
          (= ch \")
          (let [end (loop [i (inc index)]
                      (when (>= i (.length text)) (fail "Unterminated JSON string" {}))
                      (case (.charAt text i) \\ (recur (+ i 2)) \" i (recur (inc i))))
                next-index (loop [i (inc end)]
                             (if (and (< i (.length text)) (Character/isWhitespace (.charAt text i)))
                               (recur (inc i)) i))
                key? (and (set? (peek stack)) (< next-index (.length text)) (= \: (.charAt text next-index)))
                key (when key? (json/read-str (.substring text index (inc end))))]
            (when (and key? (contains? (peek stack) key)) (fail "Duplicate JSON companion key" {:key key}))
            (recur (inc end) (if key? (conj (pop stack) (conj (peek stack) key)) stack)))
          :else (recur (inc index) stack)))))
  (json/read-str text :key-fn keyword :extra-data-fn json/on-extra-throw))

(defn parse-attribute-row
  "Decode and validate one attribute JSON row, preserving escaped strings and
   all native fields. Explicit :legacy-priority? permits an absent simp priority
   without inventing one; strict schema-2 parsing keeps its required priority."
  ([text] (parse-attribute-row text {}))
  ([text {:keys [legacy-priority?]}]
   (let [row (json-row text)]
     (row! :attrs (if (and legacy-priority? (= "simp" (:kind row)) (not (contains? row :prio)))
                    (assoc row :prio 0) row) 1)
     row)))

(defn unsupported-attribute?
  "Whether the current attribute consumer cannot preserve this native row."
  [row]
  (or (= "unfold-thms" (:kind row))
      (and (= "simp" (:kind row)) (or (true? (:inv row)) (false? (:post row))))))

(defn parse
  "Parse every row, rejecting blank/malformed/unknown fields without defaults.
   JSON rows use keyword keys. Instance TSV has exactly class/name/UInt32-priority
   fields and becomes {:class :name :priority}. Input order and duplicates remain.
   Matcher discr names are local binder annotations, not global references."
  [role text]
  (when-not (roles role) (fail "Unknown companion role" {:role role}))
  (mapv (fn [index line]
          (when (str/blank? line) (fail "Blank bundled companion row" {:role role :line (inc index)}))
          (let [row (try
                      (if (= :instances role)
                        (let [parts (str/split line #"\t" -1)]
                          (when-not (and (= 3 (count parts)) (re-matches #"[0-9]+" (nth parts 2)))
                            (fail "Instance TSV requires exactly three explicit fields" {}))
                          {:class (nth parts 0) :name (nth parts 1) :priority (bigint (nth parts 2))})
                        (json-row line))
                      (catch Exception cause
                        (throw (ex-info "Malformed bundled companion row" {:role role :line (inc index)} cause))))]
            (row! role row (inc index))))
        (range) (lines text)))

(defn- checked-rows [role rows]
  (when-not (and (roles role) (sequential? rows)) (fail "Invalid companion rows" {:role role}))
  (mapv #(row! role %1 (inc %2)) rows (range)))

(defn select-for-names
  "Select by each row's declaration :name, preserving order. Every selected
   csimp/impl target, unfolding theorem, and instance class must also exist.
   Unselected rows remain valid input but are intentionally excluded."
  [role rows names]
  (when-not (and (set? names) (every? name? names)) (fail "Expected exported declaration-name set" {}))
  (let [selected (filterv #(contains? names (:name %)) (checked-rows role rows))]
    (doseq [row selected
            referenced (case role
                         :attrs (case (:kind row) ("csimp" "impl") [(:target row)]
                                      "unfold-thms" (:theorems row) [])
                         :instances [(:class row)] :matchers [])]
      (when-not (contains? names referenced)
        (fail "Selected companion row references a missing declaration"
              {:role role :name (:name row) :missing referenced})))
    selected))

(defn select-and-report [role rows names]
  (let [rows (checked-rows role rows)
        selected (select-for-names role rows names)]
    {:rows selected :report {:input (count rows) :selected (count selected)
                             :excluded (- (count rows) (count selected))
                             :excluded-names (mapv :name (remove #(contains? names (:name %)) rows))}}))

(defn- ordered-json [value]
  (cond (map? value) (into (sorted-map) (map (fn [[k v]] [k (ordered-json v)])) value)
        (vector? value) (mapv ordered-json value) :else value))

(defn render
  "Render validated rows deterministically, preserving row/instance priority order.
   JSON keys are sorted; nonempty outputs end with LF. No gzip/IO is performed."
  [role rows]
  (let [rows (checked-rows role rows)]
    (if (empty? rows) ""
        (str (str/join "\n" (map #(if (= :instances role)
                                    (str (:class %) "\t" (:name %) "\t" (:priority %))
                                    (json/write-str (ordered-json %))) rows)) "\n"))))

(defn validate-resources!
  "Strictly validate the three gzip companion payloads in a role->bytes map.
   Returns role->parsed rows. Does not validate kernel declarations or activate
   any metadata; schema-1 legacy inventories can retain their separate policy."
  [resources]
  (into {}
        (for [role (sort roles)]
          (let [payload (get resources role)]
            (when-not (bytes? payload) (fail "Missing companion gzip bytes" {:role role}))
            (let [decoded (with-open [in (GZIPInputStream. (ByteArrayInputStream. payload))]
                            (.readAllBytes in))
                  decoder (doto (.newDecoder StandardCharsets/UTF_8)
                            (.onMalformedInput CodingErrorAction/REPORT)
                            (.onUnmappableCharacter CodingErrorAction/REPORT))]
              [role (parse role (str (.decode decoder (ByteBuffer/wrap decoded))))])))))
