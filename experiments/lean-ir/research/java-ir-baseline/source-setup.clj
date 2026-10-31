(ns ansatz.research.ir.source-setup
  "Authenticated local-source overlays and common Header/ABI setup only.
   No engine execution, bootstrap lineage, guest association or kernel authority."
  (:require [clojure.data.json :as json] [clojure.java.io :as io] [clojure.string :as str]
            [java-ir-baseline :as j] [ansatz.research.ir.catalogue :as cat])
  (:import [java.util WeakHashMap] [java.security MessageDigest]))
(def lean-pin "819816b2e0a3bf405af45ae5c7af2491d8f5bee6")
(deftype Overlay [])
(deftype CodeReceipt [])
(defonce ^:private overlays (WeakHashMap.))
(defonce ^:private composites (WeakHashMap.))
(defn require! [ok message] (when-not ok (throw (ex-info message {}))))
(defn bytes-sha [bytes]
  (apply str (map #(format "%02x" (bit-and 255 %)) (.digest (MessageDigest/getInstance "SHA-256") bytes))))
(defn file-sha [file]
  (let [digest (MessageDigest/getInstance "SHA-256") buffer (byte-array 65536)]
    (with-open [input (io/input-stream file)]
      (loop [] (let [n (.read input buffer)] (when (pos? n) (.update digest buffer 0 n) (recur)))))
    (apply str (map #(format "%02x" (bit-and 255 %)) (.digest digest)))))
(defn checked-bytes [file expected maximum]
  (require! (and (string? expected) (re-matches #"[0-9a-f]{64}" expected)
                 (<= (.length (io/file file)) maximum)) "Missing pin or oversized source evidence")
  (let [bytes (java.nio.file.Files/readAllBytes (.toPath (io/file file)))]
    (require! (and (<= (alength bytes) maximum) (= expected (bytes-sha bytes))) "Source evidence digest mismatch") bytes))
(defn checked-json [file pin maximum]
  (json/read-str (String. ^bytes (checked-bytes file pin maximum) java.nio.charset.StandardCharsets/UTF_8)))
(defn name-key [name] (json/write-str (j/lean-name-data name)))
(defn label [name]
  (loop [n name result ()]
    (if (= ["anonymous"] n) (str/join "." result)
      (do (require! (and (vector? n) (= 3 (count n)) (contains? #{"str" "num"} (first n))) "Malformed typed source Name")
          (recur (second n) (conj result (nth n 2)))))))
(defn- registered [registry token message]
  (locking registry (or (.get ^WeakHashMap registry token) (throw (ex-info message {})))))
(defn overlay-info [token]
  (select-keys (registered overlays token "Actual authenticated Overlay required") [:pins :manifest :module :row-count]))
(defn authenticate-overlay!
  "External expected pins are trusted source-adapter inputs, never caller flags.
   Verify actual source/exporter/receipt/stream bytes before publishing a token.
   SPEC fixes exact module, row count, complete actions and supported roles."
  [catalogue directory {:keys [source-file producer-file module row-count pins actions] :as spec}]
  (require! (= (get pins "base_index_sha256") (get (cat/descriptor catalogue) "source-index-sha256")) "Wrong accepted base catalogue")
  (checked-bytes source-file (get pins "source_sha256") (* 1024 1024))
  (require! (and (<= (.length (io/file producer-file)) (* 256 1024 1024))
                 (= (get pins "producer_sha256") (file-sha producer-file))) "Producer binary digest/extent differs")
  (require! (and (integer? row-count) (<= 1 row-count 10000)) "Explicit bounded local row count required")
  (checked-bytes (io/file directory (str (label module) ".lean")) (get pins "source_sha256") (* 1024 1024))
  (let [receipt (checked-json (io/file directory "export-receipt.json") (get pins "export_receipt_sha256") 65536)
        _ (require! (= ["native-source-local-ir-export/1" 0 nil 0 true true true]
                        (mapv #(get receipt %) ["schema" "exit" "stop" "stderr-bytes" "no-source-main-execution"
                                                "no-checkpoint-restore" "no-imported-closure-export"])) "Unsupported producer receipt")
        _ (require! (= [(get pins "source_sha256") (get pins "producer_sha256") lean-pin (get pins "local_ir_sha256")]
                        (mapv #(get receipt %) ["source-sha256" "exporter-binary-sha256" "lean-commit" "raw-output-sha256"])) "Producer receipt pins differ")
        raw (checked-bytes (io/file directory "local-ir.jsonl") (get pins "local_ir_sha256") (* 16 1024 1024))
        _ (require! (= (alength raw) (get receipt "raw-output-bytes")) "Producer output extent differs")
        lines (str/split-lines (String. ^bytes raw java.nio.charset.StandardCharsets/UTF_8))
        manifest (json/read-str (first lines))
        _ (require! (= ["manifest" "lean-ir-probe/1" "4.33.1"] (mapv #(get manifest %) ["kind" "schema" "leanVersion"])) "Unsupported local IR manifest")
        _ (require! (= {"target" "x86_64-unknown-linux-gnu" "wordBits" 64} (get manifest "runtimeProfile")) "Unsupported local runtime ABI")
        plan (get manifest "initializationPlan")
        _ (require! (and (= module (get plan "module")) (= "lean-init-plan/1" (get plan "schema"))
                          (= "initialization-plan" (get plan "kind")) (= actions (get plan "actions"))) "Local initialization plan differs")
        _ (require! (= row-count (dec (count lines))) "Local row inventory differs")
        rows (reduce (fn [out line]
                       (let [row (json/read-str line) name (get row "name") row-key (name-key name)
                             ir (get row "ir") declaration (val (first ir))]
                         (label name)
                         (require! (and (= "decl" (get row "kind")) (= module (get row "sourceModule"))
                                        (true? (get row "sourceLocal")) (= 1 (count ir))
                                        (contains? #{"fdecl" "extern"} (key (first ir)))
                                        (= name (get declaration "f"))
                                        (contains? #{"ordinary" "closed" "value"} (get-in row ["runtime" "role"]))
                                        (nil? (get-in row ["runtime" "initializer"]))) "Unlisted module or unsupported local row")
                         (require! (and (not (contains? out row-key)) (nil? (cat/lookup catalogue name))) "Overlay shadows an existing typed Name")
                         (assoc out row-key {:row row :sha256 (bytes-sha (.getBytes ^String line java.nio.charset.StandardCharsets/UTF_8))}))) {} (rest lines))
        value-names (set (map (comp name-key #(get % "name") :row) (filter #(= "value" (get-in % [:row "runtime" "role"])) (vals rows))))]
    (require! (= value-names (set (map #(name-key (get-in % ["action" "name"])) actions))) "Missing or unlisted local value action")
    (doseq [action actions]
      (require! (and (false? (get action "meta")) (= "value" (get-in action ["action" "kind"]))
                     (= (get-in action ["action" "name"]) (get-in action ["action" "target"]))) "Unsupported local startup action"))
    (let [token (Overlay.) entry {:catalogue catalogue :pins pins :module module :manifest manifest
                                   :rows rows :row-count row-count :spec spec}]
      (locking overlays (.put overlays token entry)) token)))
(defn compose!
  "Issue source-code-only identity for ordered authenticated overlays/setup rules.
   Captured runtime state stays a separate descriptive fact; this does not admit it."
  [catalogue captured-source tokens setup]
  (require! (and (vector? tokens) (<= 1 (count tokens) 8) (map? captured-source)) "Bounded ordered source overlays required")
  (let [captured-source (json/read-str (json/write-str captured-source))
        entries (mapv #(registered overlays % "Actual authenticated Overlay required") tokens)
        _ (require! (and (seq entries) (every? #(identical? catalogue (:catalogue %)) entries)) "Overlay catalogue identity differs")
        index (get (cat/descriptor catalogue) "source-index-sha256")
        _ (require! (= index (get captured-source "code_index_sha256")) "Captured code index differs")
        rows (reduce (fn [out entry]
                       (require! (empty? (filter #(contains? out %) (keys (:rows entry)))) "Overlays overlap in typed Names")
                       (into out (:rows entry))) {} entries)
        labels (map #(label (get-in % [:row "name"])) (vals rows))
        modules (map #(label (:module %)) entries)
        _ (require! (= (count labels) (count (set labels))) "Overlay rendered Name ambiguity")
        _ (require! (not-any? true? (for [a modules b modules :when (not= a b)] (str/starts-with? b (str a ".")))) "Overlapping overlay namespaces")
        _ (require! (= (count entries) (count (set (map :module entries)))) "Duplicate overlay namespace")
        actions (vec (mapcat #(get-in % [:manifest "initializationPlan" "actions"]) entries))
        profile {"schema" "captured-base-plus-ordered-source-overlays/4" "code_index_sha256" index
                 "captured_graph_source" captured-source
                 "overlays" (mapv #(assoc (:pins %) "module" (:module %) "initializationPlan" (get-in % [:manifest "initializationPlan"])) entries)
                 "setup_evidence" (:evidence-pins setup)
                 "helper_labels" (:helpers setup) "checked_host_symbols" (:host-symbols setup)
                 "local_initialization_actions" actions
                 "local_action_rows" (mapv #(get-in rows [(name-key (get-in % ["action" "name"])) :sha256]) actions)
                 "startup_policy" "captured-imported-state-and-executed-authenticated-local-values"}
        token (CodeReceipt.)]
    (locking composites (.put composites token {:catalogue catalogue :profile profile :rows rows :setup setup})) token))
(defn code-profile [receipt]
  (:profile (registered composites receipt "Actual verified composite source receipt required")))
(defn source-binding! [basis receipt]
  (locking composites
    (let [entry (registered composites receipt "Actual verified composite source receipt required")]
      (require! (nil? (:source entry)) "Composite SourceBinding already minted")
      (let [source (j/source-binding basis (:profile entry))]
        (.put composites receipt (assoc entry :source source)) source))))
(defn lookup-entry [receipt name]
  (let [entry (registered composites receipt "Actual verified composite source receipt required")]
    (or (get (:rows entry) (name-key name)) (cat/lookup (:catalogue entry) name))))
(defn authenticate-canonical-header! [source row sha256 header]
  (require! (and (identical? source (j/request-value header "source"))
                 (= sha256 (j/request-value header "originalSha256"))
                 (= (get row "name") (j/lean-name-data (j/request-value header "name")))) "Header source or identity differs")
  (let [[kind declaration] (first (get row "ir")) field (doto (.getDeclaredField (class header) "declaration") (.setAccessible true))]
    (require! (and (= 1 (count (get row "ir"))) (= kind (j/request-value header "kind"))
                   (= (dissoc declaration "body") (.get field header))) "Canonical Header complete declaration differs"))
  (require! (= (select-keys row ["runtime" "dependencies" "redirect" "sourceLocal" "sourceModule"])
               (j/request-value header "metadata")) "Canonical Header metadata differs") header)
(defn configure-context
  "Common v4 setup only. Authenticate every reused Header before Program setup;
   mint all overlays once under the receipt's actual shared SourceBinding."
  ([receipt catalogue ctx source] (configure-context receipt catalogue ctx source {}))
  ([receipt catalogue ctx source existing-by-sha]
   (let [{:keys [profile rows setup] :as accepted} (registered composites receipt "Actual verified composite source receipt required")
         _ (require! (and (identical? catalogue (:catalogue accepted)) (identical? source (:source accepted))
                          (identical? profile (j/request-value source "acceptedCatalogueSnapshot"))) "Composite source binding differs")
         _ (require! (and (map? existing-by-sha) (<= (count existing-by-sha) 10000)) "Bounded existing Header memo required")
         minted (atom {})
         header! (fn [{:keys [row sha256] :as entry}]
                   (require! entry "Missing authenticated source row")
                   (or (get @minted sha256)
                       (let [_ (require! (< (count @minted) 10000) "Composite Header limit exceeded")
                             h (or (get existing-by-sha sha256) (j/declaration-header source row sha256))]
                         (authenticate-canonical-header! source row sha256 h) (swap! minted assoc sha256 h) h)))
         _ (doseq [[sha h] existing-by-sha]
             (let [entry (lookup-entry receipt (j/lean-name-data (j/request-value h "name")))]
               (require! (= sha (:sha256 entry)) "Unlisted reused Header") (header! entry)))
         _ (doseq [entry (vals rows)] (header! entry))
         by-label (into {} (map (fn [[_ e]] [(label (get-in e [:row "name"])) e])) rows)
         base-row! (fn [original]
                     (let [actual (cat/lookup catalogue (get original "name"))]
                       (require! (and actual (= (get original "sha256") (:sha256 actual))) "Original source row differs") actual))
         helper-headers (mapv (fn [name]
                               (let [entry (get by-label name) fdecl (get-in entry [:row "ir" "fdecl"])]
                                 (require! (and fdecl (<= 1 (count (get fdecl "xs")) 64)
                                                (contains? #{"object" "tobject" "tagged"} (get fdecl "type"))
                                                (every? #(and (false? (get % "borrow")) (contains? #{"object" "tobject" "tagged"} (get % "ty"))) (get fdecl "xs"))) "Invalid helper ABI")
                                 (header! entry))) (:helpers setup))
         pairs (mapv (fn [alias]
                       (let [origin (get rows (name-key (get alias "overlay-name")))
                             target (base-row! {"name" (get alias "target-name") "sha256" (get alias "target-sha256")})
                             a (get-in origin [:row "ir" "extern"]) b (get-in target [:row "ir" "fdecl"])]
                         (require! (and a b (= (get alias "overlay-sha256") (:sha256 origin))
                                        (= (get alias "symbol") (get-in a ["ext" "entries" 0 "standard" "fn"]))
                                        (= (get a "type") (get b "type"))
                                        (= (mapv #(select-keys % ["ty" "borrow"]) (get a "xs"))
                                           (mapv #(select-keys % ["ty" "borrow"]) (get b "xs")))) "Alias ABI or source differs")
                         [(header! origin) (header! target)])) (:aliases setup))
         checked (mapv #(base-row! %) (:checked setup))
         outer (mapv header! checked)
         specs (mapv (fn [entry symbol]
                       (let [abi (get-in entry [:row "ir" "extern"])]
                         (require! (= symbol (get-in abi ["ext" "entries" 0 "standard" "fn"])) "Checked Host ABI symbol differs")
                         {:symbol symbol :parameters (mapv #(get % "ty") (get abi "xs"))
                          :borrowed (mapv #(get % "borrow") (get abi "xs")) :result (get abi "type")})) checked (:host-symbols setup))
         registered (j/register-headers ctx (vec (vals @minted)) specs)
         bound (j/bind-guest-exports registered pairs)
         policy (j/host-guest-policy bound outer helper-headers)]
     {:ctx bound :headers-by-sha @minted :extra-by-sha (apply dissoc @minted (keys existing-by-sha))
      :helper-headers (zipmap (:helpers setup) helper-headers) :outer-headers outer :alias-pairs pairs
      :configure-engine! (fn [ctx engine] (j/configure-host-guest! ctx engine policy))
      :overlay-rows rows :checked-host-specs specs :local-initialization-actions (get profile "local_initialization_actions")
      :local-action-headers (mapv #(get @minted %) (get profile "local_action_rows"))})))

(defn guard-source!
  "Check issued source identity and the actual open catalogue lease. Runtime
   graph/state, Program ancestry and imported-base guards remain separate."
  [receipt source]
  (let [entry (registered composites receipt "Actual verified composite source receipt required")]
    (require! (and (identical? source (:source entry))
                   (identical? (:profile entry) (j/request-value source "acceptedCatalogueSnapshot")))
              "Composite source binding differs")
    (cat/lookup (:catalogue entry) ["anonymous"])
    receipt))
(defn configuration-callback [receipt catalogue]
  (fn
    ([ctx source] (configure-context receipt catalogue ctx source))
    ([ctx source existing-by-sha] (configure-context receipt catalogue ctx source existing-by-sha))))
