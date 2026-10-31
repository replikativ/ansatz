(ns ansatz.research.ir.authenticated-demand
  "Demand loading over an explicit authenticated resolver. No artifact discovery,
   source issuance, overlay authorization or native implementation policy."
  (:require [clojure.data.json :as json] [java-ir-baseline :as j]))
(defn- need [ok message] (when-not ok (throw (ex-info message {:profile :authenticated-demand}))))
(defn exact-name-key [name] (json/write-str (j/lean-name-data name)))
(defn attach
  "Return DRIVER with a trusted adapter policy; no engine or memo mutation.
   resolve-row! receives [actual-driver typed-name] and MUST authenticate bounded
   original raw bytes/SHA/name against the actual accepted catalogue/code receipt,
   including authorized overlays. Returns {:row string-keyed-map :sha256 hex
   :source-binding actual-SourceBinding}. check-source! receives the actual driver
   and MUST enforce live source/resource/receipt authority on every operation.
   These injected callbacks are authority, not caller-supplied verification flags."
  [driver {:keys [resolve-row! check-source!] :as policy}]
  (need (and (map? driver) (:engine driver) (:source driver)
             (instance? clojure.lang.IAtom (:current-ctx driver))
             (instance? clojure.lang.IAtom (:headers-by-name driver))
             (instance? clojure.lang.IAtom (:requests driver))) "Actual demand driver/memos required")
  (need (and (fn? resolve-row!) (fn? check-source!)) "Explicit authenticated resolver/source guard required")
  (need (nil? (:authenticated-demand driver)) "Demand policy already attached")
  (check-source! driver)
  (need (= "idle" (j/phase @(:current-ctx driver) (:engine driver))) "Attach only at idle boundary")
  (assoc driver :authenticated-demand policy))
(defn- policy! [driver]
  (let [p (:authenticated-demand driver)]
    (need (and (fn? (:resolve-row! p)) (fn? (:check-source! p))) "Attach an authenticated demand resolver first")
    ((:check-source! p) driver) p))
(defn original-row! [driver name]
  (let [policy (policy! driver) resolved ((:resolve-row! policy) driver name)
        {:keys [row sha256 source-binding]} resolved]
    (need (identical? source-binding (:source driver)) "Resolver returned a foreign SourceBinding")
    (need (and (map? row) (string? sha256) (re-matches #"[0-9a-f]{64}" sha256)
               (= (j/lean-name-data name) (get row "name"))) "Resolver returned wrong typed Name/CAS identity")
    resolved))
(defn- header-row [row]
  (let [ir (get row "ir") [kind declaration] (first ir)]
    (need (and (= 1 (count ir)) (contains? #{"extern" "fdecl"} kind)) "Unsupported original declaration")
    (assoc (dissoc row "pretty") "ir" {kind (dissoc declaration "body")})))
(defn- check-header! [driver row sha header]
  (let [[kind raw] (first (get row "ir"))
        field (doto (.getDeclaredField (class header) "declaration") (.setAccessible true))]
    (need (and (identical? (:source driver) (j/request-value header "source"))
               (= sha (j/request-value header "originalSha256"))
               (= (get row "name") (j/lean-name-data (j/request-value header "name")))
               (= kind (j/request-value header "kind"))
               (= raw (.get field header))
               (= (select-keys row ["runtime" "dependencies" "redirect" "sourceLocal" "sourceModule"])
                  (j/request-value header "metadata"))) "Canonical Header differs from authenticated original row")
    header))
(defn ensure-header! [driver name]
  ;; Resolve even cached entries: a memo is not current source/row authority.
  (let [{:keys [row sha256]} (original-row! driver name)
        expected (header-row row) key (exact-name-key name) memo (:headers-by-name driver)]
    (locking memo
      (if-let [entry (get @memo key)]
        (do (need (= sha256 (:sha256 entry)) "Canonical Header memo SHA differs")
            (check-header! driver expected sha256 (:header entry)))
        (let [header (j/declaration-header (:source driver) expected sha256)]
          (check-header! driver expected sha256 header)
          (swap! memo assoc key {:header header :sha256 sha256}) header)))))
(defn direct-names [row]
  ;; Iterative traversal bounds malformed resolver outputs before loading deps.
  (let [self (exact-name-key (get row "name"))]
    (loop [pending [(get-in row ["ir" "fdecl" "body"])] visits 0 found {}]
      (need (<= visits 1000000) "Original body traversal exceeds bound")
      (need (<= (count pending) 1000000) "Original body traversal frontier exceeds bound")
      (need (<= (count found) 20000) "Original direct dependencies exceed bound")
      (if (empty? pending) (mapv val (sort-by key found))
        (let [x (peek pending) rest (pop pending)]
          (cond
            (map? x) (let [call (or (get x "fap") (get x "pap"))
                           n (when call (get call "c")) k (when n (exact-name-key n))]
                       (recur (into rest (vals x)) (inc visits)
                              (if (and k (not= self k)) (assoc found k n) found)))
            (sequential? x) (recur (into rest x) (inc visits) found)
            :else (recur rest (inc visits) found)))))))
(defn service-code! [driver]
  (policy! driver)
  (let [ctx @(:current-ctx driver) engine (:engine driver) request (j/code-request ctx engine)]
    (need request "Actual outstanding CodeRequest required")
    (let [header (j/request-value request "header") name (j/request-value header "name")
          {:keys [row sha256]} (original-row! driver name)
          canonical (ensure-header! driver name)]
      (need (identical? header canonical) "CodeRequest is not the canonical authenticated Header")
      (need (= sha256 (j/request-value header "originalSha256")) "Requested original body SHA differs")
      (let [deps (mapv #(ensure-header! driver %) (direct-names row))
            ready (j/materialize-body ctx header row deps)]
        ;; Engine resume validates actual request/program lineage before publication.
        (j/resume-code! ready engine request)
        (reset! (:current-ctx driver) ready)
        (swap! (:requests driver) conj {:name (j/lean-name-data name) :sha256 sha256})
        (count @(:requests driver))))))
