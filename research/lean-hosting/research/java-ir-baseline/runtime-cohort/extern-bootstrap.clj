(ns original-extern-bootstrap-v1
  "Descriptor-only bootstrap for authenticated ORIGINAL externs. No handler,
   effect permission, Native implementation, source issuance or Program mutation."
  (:require [clojure.data.json :as json] [clojure.java.io :as io]
            [java-ir-baseline :as j]
            [ansatz.research.ir.source-setup :as source]))
(def index-pin "74d833d577923821b982e8a9e872a38b5cad011513eb18870b51417e13397f0e")
(def lanes #{"object" "tobject" "tagged" "erased" "void" "uint8" "uint16" "uint32" "uint64" "usize" "float"})
(defn- need [ok message] (when-not ok (throw (ex-info message {:scope :original-extern-bootstrap-v1}))))
(defn- field [x k] (.get (doto (.getDeclaredField (class x) k) (.setAccessible true)) x))
(defn- static-field [^Class c k] (.get (doto (.getDeclaredField c k) (.setAccessible true)) nil))
(defn- sha-file [file]
  (let [d (java.security.MessageDigest/getInstance "SHA-256") buffer (byte-array 65536)]
    (with-open [in (io/input-stream file)]
      (loop [] (let [n (.read in buffer)] (when (pos? n) (.update d buffer 0 n) (recur)))))
    (apply str (map #(format "%02x" (bit-and 255 %)) (.digest d)))))
(defn- spec-data [spec]
  {:symbol (field spec "symbol") :parameters (vec (field spec "paramTypes"))
   :borrowed (vec (field spec "borrowed")) :result (field spec "resultType")})
(defn- abi-key [s] [(:symbol s) (:parameters s) (:borrowed s) (:result s)])
(defn- symbol! [symbol]
  (need (and (string? symbol) (<= 1 (count symbol) 4096) (not (.contains ^String symbol "\u0000"))) "Invalid extern symbol") symbol)
(defn- selected-extern [row]
  ;; Match Interpreter.externSymbol exactly: first all/c backend, inline at that
  ;; position rejects; later standard entries cannot silently override it.
  (loop [entries (get-in row ["ir" "extern" "ext" "entries"])]
    (if (empty? entries) {:status :unsupported-backend}
      (let [entry (first entries)]
        (need (and (map? entry) (= 1 (count entry))) "Malformed original extern entry")
        (let [[kind data] (first entry) backend (j/lean-name-data (get data "backend"))
              cpp? (contains? #{["str" ["anonymous"] "all"] ["str" ["anonymous"] "c"]} backend)]
          (if-not cpp? (recur (rest entries))
            (if (= kind "standard") {:status :standard :symbol (symbol! (get data "fn"))}
              {:status :inline-backend})))))))
(defn- actual-exclusions! [parent future]
  (let [d (:driver parent) c @(:current-ctx d) e (:engine d) program (:program c)
        receipt (:code-receipt parent) src (:source d)]
    (source/guard-source! receipt src)
    (need (= index-pin (get (j/request-value src "acceptedCatalogueSnapshot") "code_index_sha256"))
          "Actual parent Source original index differs")
    (need (and (identical? (:class c) (class e)) (identical? program (field e "program"))
               (= "idle" (j/phase c e))) "Actual idle parent Program/source required")
    (doseq [k ["closed" "disposed" "untrackedFailure" "advancing"]]
      (need (false? (field e k)) "Invalid parent lifecycle for descriptor snapshot"))
    (let [native-registry ^java.util.Map (static-field (:class c) "EXTERNS")
          host-registry ^java.util.Map (field program "hostRegistry")
          functions ^objects (field program "functions") targets ^objects (field program "guestExports")
          _ (need (and (= (alength functions) (alength targets)) (<= (alength functions) 500000)) "Program binding inventory bound")
          natives (vec (mapcat (fn [entry] (map spec-data (.getValue ^java.util.Map$Entry entry))) native-registry))
          hosts (vec (mapcat (fn [entry] (map spec-data (.getValue ^java.util.Map$Entry entry))) host-registry))
          guests (vec (for [i (range (alength targets)) :when (aget targets i)
                            :let [origin (field (aget functions i) "header")
                                  target (field (aget targets i) "header")
                                  name (j/lean-name-data (j/request-value origin "name"))
                                  entry (source/lookup-entry receipt name)
                                  _ (source/authenticate-canonical-header! src (:row entry) (:sha256 entry) origin)
                                  selected (selected-extern (:row entry))]]
                        (do (need (= :standard (:status selected)) "Guest export origin lacks supported standard symbol")
                            {:symbol (:symbol selected) :origin-name name :origin-sha256 (:sha256 entry)
                             :target-name (j/lean-name-data (j/request-value target "name"))
                             :target-sha256 (j/request-value target "originalSha256")})))
          reserved (set (:symbols future))]
      (need (and (map? future) (contains? future :symbols) (every? #(= % (symbol! %)) reserved)
                 (map? (:policy-pins future))) "Declare explicit future guest-export reservations/policy pins")
      (doseq [[label sha] (:policy-pins future)]
        (need (and (string? label) (string? sha) (re-matches #"[0-9a-f]{64}" sha)) "Malformed future guest policy pin"))
      ;; Output contains scalar/immutable metadata only. No Class/Program/Header,
      ;; engine, source, descriptor object, private registry or lease is retained.
      {:native-specifications (vec (sort-by (comp pr-str abi-key) natives))
       :existing-host-specifications (vec (sort-by (comp pr-str abi-key) hosts))
       :actual-guest-origins guests :future-guest-symbols (vec (sort reserved)) :future-policy-pins (:policy-pins future)})))
(defn build!
  "Read pinned complete extern metadata, authenticate EVERY selected original row
   again via actual CodeReceipt, and derive additional EARLY descriptors. Call
   before reconstructing a seed; this does NOT upgrade existing Functions.
   FUTURE is {:symbols #{...} :policy-pins {artifact-label sha256,...}}. Reservations
   are conservative exclusions only, never authority to bind guest implementations.
   Existing host policies must still be installed by the caller as before."
  [parent directory expected-manifest-sha future]
  (let [mf (io/file directory "manifest.json") rf (io/file directory "extern-rows.jsonl")
        _ (need (and (re-matches #"[0-9a-f]{64}" expected-manifest-sha) (<= (.length mf) 65536)
                     (= expected-manifest-sha (sha-file mf))) "Extern manifest pin differs")
        manifest (json/read-str (slurp mf))
        _ (need (and (= "complete-original-extern-metadata/1" (get manifest "schema"))
                     (= index-pin (get manifest "source-index-sha256"))
                     (= 375258 (get manifest "declarations"))
                     (= 961 (get manifest "extern-row-count"))
                     (= 120853740 (get manifest "source-index-bytes"))) "Wrong complete original extern source envelope")
        _ (need (and (<= (.length rf) (* 16 1024 1024))
                     (= (get manifest "extern-rows-sha256") (sha-file rf))) "Extern fixture bytes differ")
        exclusions (actual-exclusions! parent future)
        native-symbols (set (map :symbol (:native-specifications exclusions)))
        native-abis (set (map abi-key (:native-specifications exclusions)))
        host-abis (set (map abi-key (:existing-host-specifications exclusions)))
        guests (into (set (:future-guest-symbols exclusions)) (map :symbol (:actual-guest-origins exclusions)))
        receipt (:code-receipt parent) coverage (atom []) specs (atom {})
        rows (with-open [r (io/reader rf)]
               (reduce (fn [n line]
                         (need (<= (count line) (* 8 1024 1024)) "Extern row line exceeds bound")
                         (let [record (json/read-str line) name (get record "name") sha (get record "sha256")
                               row (get record "row") entry (source/lookup-entry receipt name)
                               _ (need (and (= sha (:sha256 entry)) (= row (dissoc (:row entry) "pretty"))
                                            (= name (get row "name")) (= #{"extern"} (set (keys (get row "ir")))))
                                       "Original extern index/CAS/CodeReceipt row differs")
                               decl (get-in row ["ir" "extern"]) chosen (selected-extern row)
                               spec {:symbol (:symbol chosen) :parameters (mapv #(get % "ty") (get decl "xs"))
                                     :borrowed (mapv #(get % "borrow") (get decl "xs")) :result (get decl "type")}
                               _ (need (and (every? boolean? (:borrowed spec))
                                            (= name (get decl "f"))) "Malformed original extern raw shape")
                               supported? (and (every? lanes (:parameters spec)) (lanes (:result spec)))
                               k (abi-key spec)
                               status (cond
                                        (not= :standard (:status chosen)) (:status chosen)
                                        (contains? native-symbols (:symbol spec)) (if (contains? native-abis k) :native-supported :native-symbol-ABI-mismatch)
                                        (contains? guests (:symbol spec)) :reserved-guest-export
                                        (not supported?) :unsupported-lane
                                        (contains? host-abis k) :existing-host-ABI
                                        :else :additional-host-ABI)]
                           (when (= status :additional-host-ABI) (swap! specs assoc k spec))
                           (swap! coverage conj {:name name :sha256 sha :symbol (:symbol spec) :ABI k :status status})
                           (inc n))) 0 (line-seq r)))]
    (need (= rows (get manifest "extern-row-count")) "Incomplete original extern fixture")
    {:schema :additional-original-early-host-specifications-v1
     :additional-early-host-specifications (vec (sort-by (comp pr-str abi-key) (vals @specs)))
     :census {:original-extern-rows rows :status-counts (frequencies (map :status @coverage))
              :additional-distinct-ABIs (count @specs)}
     :coverage @coverage :exclusions exclusions
     :pins {:manifest-sha256 expected-manifest-sha :source-index-sha256 index-pin
            :extern-rows-sha256 (get manifest "extern-rows-sha256")}
     :handler-authority false :Program-mutated false :guest-calls 0}))
