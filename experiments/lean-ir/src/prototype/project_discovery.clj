(ns prototype.project-discovery
  "Bounded descriptive discovery over captured source and a threaded raw packet.
   No import, publication, adoption, checked module or native-base authority."
  (:require [prototype.project-source :as source]
            [prototype.resident-init-prefix :as header]
            [prototype.resident-frontend :as resident])
  (:import [java.nio.file Path]
           [java.nio.charset StandardCharsets]))

(defn- fail [message data] (throw (ex-info message data)))
(defn- exact! [value keys label]
  (when-not (and (map? value) (= (count keys) (count value))
                 (every? #(contains? value %) keys))
    (fail (str "Project discovery requires closed " label) {})))
(defn- positive! [n]
  (when-not (and (integer? n) (<= 1 n Long/MAX_VALUE))
    (fail "Project discovery requires positive Long bounds" {})))
(def ^:private limit-keys
  [:max-roots :max-native-modules :max-modules :max-depth :max-edges
   :max-source-bytes :max-header-output-bytes :max-name-nodes :max-name-bytes :max-total-name-bytes])
(def ^:private header-limit-keys
  [:max-source-bytes :max-file-name-bytes :max-output-bytes :max-json-depth
   :max-imports :max-diagnostics :max-name-nodes :max-name-bytes :max-total-name-bytes])

(defn- name! [wire limits remaining]
  ;; Literal-first comparisons and count gates precede content scans/hash/set.
  (loop [part wire segments () nodes 0 bytes 0]
    (when-not (vector? part) (fail "Project module Name must be a bounded wire vector" {}))
    (cond
      (and (= 1 (count part)) (= "anonymous" (first part)))
      (if (seq segments) {:segments (vec segments) :bytes bytes}
          (fail "Project module Name must be nonanonymous" {}))
      (and (= 3 (count part)) (= "str" (first part)))
      (let [s (nth part 2) next-nodes (inc nodes)
            available (min (- (:max-name-bytes limits) bytes) (- remaining bytes))]
        (when-not (and (<= next-nodes (:max-name-nodes limits)) (string? s)
                       (<= 1 (count s) available))
          (fail "Project module Name exceeds bounds" {}))
        (when (re-find #"[.\\/\u0000]" s)
          (fail "Project module Name is outside the string-segment subset" {}))
        (let [encoded (.getBytes ^String s StandardCharsets/UTF_8) size (alength encoded)]
          (when-not (and (<= size available)
                         (= s (String. encoded StandardCharsets/UTF_8)))
            (fail "Project module Name exceeds UTF-8 bounds" {}))
          (recur (nth part 1) (conj segments s) next-nodes (+ bytes size))))
      :else (fail "Project module Name is outside the string-segment subset" {}))))

(defn- names! [values limits count-limit remaining]
  (when-not (and (vector? values) (<= (count values) count-limit))
    (fail "Project module Name inventory exceeds count bound" {}))
  (reduce (fn [{:keys [names bytes]} wire]
            (let [checked (name! wire limits (- remaining bytes))]
              {:names (conj names (:segments checked)) :bytes (+ bytes (:bytes checked))}))
          {:names [] :bytes 0} values))

(defn- provider! [provider]
  (exact! provider [:roots :max-bytes] "provider")
  (let [roots (:roots provider) n (:max-bytes provider)]
    (when-not (and (vector? roots) (<= 1 (count roots) 256)
                   (integer? n) (<= 1 n 67108864))
      (fail "Project discovery requires bounded provider roots/bytes" {}))
    ;; Preserve supplied canonical Path identities. Never silently recanonicalize
    ;; roots or derive module identity from a canonical leaf filename.
    (doseq [p roots]
      (when-not (and (instance? Path p) (.isAbsolute ^Path p)
                     (<= 1 (.getNameCount ^Path p) 256)
                     (<= (count (str p)) 16384)
                     (= p (.normalize ^Path p)))
        (fail "Project provider roots must be bounded absolute normalized Paths" {}))))
  provider)

(defn- progress [s]
  (select-keys s [:phase :modules :edges :source-bytes :name-bytes
                 :header-output-reserved :helper-calls :used :reserved]))

(defn- call-header! [state capture configuration header-limits budgets limits]
  (let [s @state remaining (- (:attempt-fuel budgets) (:used s))
        bound (min (:helper-fuel budgets) remaining)
        output (:max-output-bytes header-limits)]
    (when (zero? bound) (fail "Project discovery exhausted helper fuel" {}))
    (when (> output (- (:max-header-output-bytes limits) (:header-output-reserved s)))
      (fail "Project discovery cannot reserve next header output" {}))
    (swap! state #(-> % (assoc :reserved bound :phase :header-call)
                       (update :helper-calls inc) (update :header-output-reserved + output)))
    (let [result
          (try
            (header/discover-classic-source-header (:packet @state)
              {:text (:text capture) :file-name (str (:path capture))}
              {:configuration configuration :limits header-limits
               :budgets {:helper-fuel bound :attempt-fuel bound}})
            (catch Throwable cause
              (let [data (ex-data cause) child (:classic-header-discovery-state data)
                    packet (:packet @state)]
                ;; Preserve the child ledger, not a guessed charge from its
                ;; fallback checkpoint. Unknown work keeps the full reservation.
                (swap! state
                  (fn [s]
                    (cond-> (assoc s :phase :header-failed :failed-header cause
                                     :packet (assoc packet
                                               :world (or (:checkpoint data) (:world child) (:world packet))
                                               :session (or (:checkpoint-session data) (:session child) (:session packet))))
                      child (-> (update :used + (:used child)) (assoc :reserved (:reserved child))))))
                (throw cause))))]
      ;; Packet/result escrow precedes every Project-only postcondition.
      (swap! state #(-> % (assoc :packet (:packet result) :last-header result
                                 :reserved 0 :phase :header-returned)
                         (update :used + (get-in result [:progress :guest-steps]))))
      result)))

(defn discover-project
  "Capture and parse an ordinary classic source DAG, returning the actual last
   packet and a descriptive dependency-first graph. Caller owns one scratch
   branch and adopts ONCE after success. This operation never adopts/imports.

   REQUEST exactly {:roots ordered-wire-Names :native-modules vector-wire-Names
   :provider project-source/provider}. Native names only stop descriptive walks;
   they do not assert a checked native base. OPTIONS exactly {:configuration
   captured :header-limits nine-explicit-bounds :limits ten-project-bounds
   :budgets {:helper-fuel n :attempt-fuel n}}. Roots must be nonempty.

   Depth counts source nodes only. Edges count ALL raw requestedImports,
   including implicit Init/meta and duplicates, before scheduling deduplication.
   Each module is captured once; edits do not change earlier immutable captures.
   Header output accounting conservatively reserves max-output-bytes per call,
   not measured actual output. All-native requests still validate packet readiness.
   Failure retains latest packet/owned child evidence and partial graph, never
   retries or closes borrowed resources. Filesystem capture is cooperative, not
   a project-wide transaction or I/O deadline."
  [packet request {:keys [configuration header-limits limits budgets] :as options}]
  (let [state (atom {:entry packet :packet packet :phase :entry :nodes {} :order []
                     :stack [] :modules 0 :edges 0 :source-bytes 0 :name-bytes 0
                     :header-output-reserved 0 :helper-calls 0 :used 0 :reserved 0})]
    (try
      (exact! options [:configuration :header-limits :limits :budgets] "options")
      (exact! limits limit-keys "project limits")
      (doseq [k limit-keys] (positive! (get limits k)))
      (exact! header-limits header-limit-keys "header limits")
      (doseq [k header-limit-keys] (positive! (get header-limits k)))
      (when-not (<= 2 (:max-imports header-limits) 1026)
        (fail "Project header limits require 2..1026 imports" {}))
      (exact! budgets [:helper-fuel :attempt-fuel] "budgets")
      (doseq [k [:helper-fuel :attempt-fuel]] (positive! (get budgets k)))
      (exact! request [:roots :native-modules :provider] "request")
      (provider! (:provider request))
      (let [root-names (names! (:roots request) limits (:max-roots limits) (:max-total-name-bytes limits))
            _ (when (empty? (:names root-names)) (fail "Project discovery requires nonempty roots" {}))
            native-names (names! (:native-modules request) limits (:max-native-modules limits)
                                 (- (:max-total-name-bytes limits) (:bytes root-names)))
            native (set (:names native-names)) roots (:names root-names)]
        (swap! state assoc :roots roots :native-modules native
               :name-bytes (+ (:bytes root-names) (:bytes native-names)) :phase :readiness)
        (resident/adoption-readiness! packet configuration)
        ;; Explicit enter/exit frames avoid recursion and preserve root/import
        ;; order. Heights additionally check longer paths through black nodes.
        (swap! state assoc :stack (mapv #(vector :enter % 1) (reverse roots)))
        (loop []
          (if (empty? (:stack @state))
            (let [s @state]
              {:packet (:packet s)
               :graph {:roots roots :native-modules native :nodes (:nodes s) :order (:order s)}
               :progress (assoc (progress s) :phase :completed)})
            (let [[action module depth] (peek (:stack @state))]
              (swap! state update :stack pop)
              (if (= :exit action)
                (let [deps (get-in @state [:nodes module :dependencies])
                      height (inc (reduce max 0 (map #(get-in @state [:nodes % :height] 0) deps)))]
                  (when (> height (:max-depth limits))
                    (fail "Project source dependency depth exceeds bound" {:module module}))
                  (swap! state #(-> % (assoc-in [:nodes module :status] :black)
                                     (assoc-in [:nodes module :height] height)
                                     (update :order conj module)))
                  (recur))
                (cond
                  (contains? native module) (recur)
                  (= :gray (get-in @state [:nodes module :status]))
                  (fail "Project source dependency cycle" {:module module})
                  (= :black (get-in @state [:nodes module :status])) (recur)
                  :else
                  (do
                    (when (> depth (:max-depth limits))
                      (fail "Project source dependency depth exceeds bound" {:module module}))
                    (when (>= (:modules @state) (:max-modules limits))
                      (fail "Project source module count exceeds bound" {:module module}))
                    (let [remaining (- (:max-source-bytes limits) (:source-bytes @state))
                          cap (min remaining (get-in request [:provider :max-bytes]) (:max-source-bytes header-limits))]
                      (when (zero? cap) (fail "Project aggregate source bytes exhausted" {}))
                      (swap! state #(-> % (assoc :phase :capture :current-module module)
                                         (update :modules inc) (assoc-in [:nodes module] {:status :capturing})))
                      (let [captured (source/capture-source (assoc (:provider request) :max-bytes cap) module)]
                        (swap! state #(-> % (assoc-in [:nodes module :capture] captured)
                                           (update :source-bytes + (:byte-count captured))))
                        (let [result (call-header! state captured configuration header-limits budgets limits)
                              parsed (:header result)]
                          (swap! state assoc-in [:nodes module :header] parsed)
                          (when-not (= :ok (:status result))
                            (fail "Project source header contains parser errors" {:module module}))
                          (let [imports (:requestedImports parsed) count-edges (count imports)]
                            (when (> count-edges (- (:max-edges limits) (:edges @state)))
                              (fail "Project import occurrence count exceeds bound" {:module module}))
                            (let [checked (names! (mapv :module imports) limits count-edges
                                                (- (:max-total-name-bytes limits) (:name-bytes @state)))
                                  dependencies (vec (distinct (:names checked)))
                                  tasks (mapv #(vector :enter % (inc depth)) (reverse dependencies))]
                              (swap! state #(-> % (update :edges + count-edges)
                                                 (update :name-bytes + (:bytes checked))
                                                 (assoc-in [:nodes module :dependencies] dependencies)
                                                 (assoc-in [:nodes module :status] :gray)
                                                 (update :stack into (into [[:exit module depth]] tasks))))
                              (recur)))))))))))))
      (catch Throwable cause
        (let [s @state data (ex-data cause)]
          (throw (ex-info (or (.getMessage cause) "Project discovery failed")
                   (merge data {:checkpoint (or (:checkpoint data) (get-in s [:packet :world]))
                                :checkpoint-session (or (:checkpoint-session data) (get-in s [:packet :session]))
                                :project-discovery-state s}) cause)))))))
