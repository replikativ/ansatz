(ns ansatz.research.ir.bootstrap.policies-early
  "Early extern descriptors from authenticated rows and metadata-only Program
   registries. No SourceBinding mint, engine, image, implementation or guest call."
  (:require [clojure.java.io :as io] [clojure.data.json :as json]
            [java-ir-baseline :as j] [ansatz.research.ir.source-setup :as source]
            [ansatz.research.ir.catalogue :as cat]
            [ansatz.research.ir.bootstrap.policies :as policies]
            [original-extern-bootstrap-v1 :as extern]
            [allocation-heartbeat-lab-v1 :as heartbeat]
            [java-prelude-no-native-init :as native-init]))
(def manifest-pin "225d3d9e506730ffa4f6a6319ca91e6d52b46145cd6058422748b93424b5fd11")
(defn- need [ok message] (when-not ok (throw (ex-info message {:profile :source4-early-descriptors-v1}))))
(defn- field [x k] (.get (doto (.getDeclaredField (class x) k) (.setAccessible true)) x))
(defn- static-field [^Class c k] (.get (doto (.getDeclaredField c k) (.setAccessible true)) nil))
(defn- abi-key [spec] (#'extern/abi-key spec))
(defn- spec-data [spec] (#'extern/spec-data spec))
(defn- selected [row] (#'extern/selected-extern row))
(defn- actual-entry! [receipt name sha]
  (let [entry (source/lookup-entry receipt name)]
    (need (and entry (= sha (:sha256 entry)) (= name (get-in entry [:row "name"])))
          "Early policy original Name/SHA differs") entry))
(defn- specification [row]
  (let [choice (selected row) decl (get-in row ["ir" "extern"])]
    (need (and (= :standard (:status choice)) decl (= (get row "name") (get decl "f")))
          "Known early policy needs an actual standard original extern")
    {:symbol (:symbol choice) :parameters (mapv #(get % "ty") (get decl "xs"))
     :borrowed (mapv #(get % "borrow") (get decl "xs")) :result (get decl "type")}))
(defn- wire [parts]
  (reduce (fn [p x] [(if (integer? x) "num" "str") p (if (integer? x) (str x) x)]) ["anonymous"] parts))
(def gate-name ["str" ["str" ["anonymous"] "ObservedFrontendCommand"] "beforeElaboration"])
(def gate-sha "bf96d5878e30e9e49eaf2b451742599e044afaaaea7f16423a9653fe6f49ecb9")
(defn derive!
  "Opts {:catalogue :extern-directory :extern-manifest-sha256}. Authenticate
   every original extern through the actual receipt BEFORE its one SourceBinding
   is minted. Exclusions use this basis's real static Native specifications and
   a metadata-only empty Program host registry, plus exact planned policies."
  [bundle basis receipt {:keys [catalogue extern-directory extern-manifest-sha256]}]
  (let [_ (need (= policies/index-pin (get (source/code-profile receipt) "code_index_sha256")
                     (:source-index-sha256 (cat/source-token catalogue))) "Early receipt/catalogue original index differs")
        reservations (policies/reservation-origins bundle catalogue)
        setup (policies/setup-evidence! catalogue {:policies bundle})
        empty-context (j/prepare-host-program basis [] (get basis :early-host-specifications []))
        program (:program empty-context)
        natives (vec (mapcat (fn [entry] (map spec-data (.getValue ^java.util.Map$Entry entry)))
                            ^java.util.Map (static-field (:class empty-context) "EXTERNS")))
        existing (vec (mapcat (fn [entry] (map spec-data (.getValue ^java.util.Map$Entry entry)))
                             ^java.util.Map (field program "hostRegistry")))
        heartbeat-hosts
        (mapv (fn [[_ expected]]
                (let [entry (actual-entry! receipt (:name expected) (:sha expected)) spec (specification (:row entry))]
                  (need (= spec (select-keys expected [:symbol :parameters :borrowed :result])) "Known heartbeat early ABI differs") spec))
              heartbeat/specifications)
        checked-hosts (mapv (fn [row symbol]
                             (let [entry (actual-entry! receipt (get row "name") (get row "sha256"))
                                   spec (specification (:row entry))]
                               (need (= symbol (:symbol spec)) "Checked seam early symbol differs") spec))
                           (:checked setup) (:host-symbols setup))
        init-row (actual-entry! receipt policies/native-init-name native-init/original-sha)
        init-spec (specification (:row init-row))
        _ (need (= init-spec native-init/spec) "Empty-native-symbol early ABI differs")
        known-hosts (into (vec existing) (concat heartbeat-hosts checked-hosts [init-spec]))
        original-symbols
        (set (for [record (:original-origins reservations)
                   :let [row (get record "header-row") entry (actual-entry! receipt (get row "name") (get record "sha256"))]]
               (:symbol (specification (:row entry)))))
        ir-rows (mapv (fn [leaf]
                        (let [name (wire ["_private" "Lean" "Environment" 0 "Lean" leaf])
                              entry (source/lookup-entry receipt name)]
                          (need entry "Required genuine IR export origin absent")
                          {:name name :sha256 (:sha256 entry) :symbol (:symbol (specification (:row entry)))}))
                      ["exportIREntries" "getIRExtraConstNames"])
        guest-symbols (into (into original-symbols (:overlay-symbols reservations)) (map :symbol ir-rows))
        gate (actual-entry! receipt gate-name gate-sha) gate-spec (specification (:row gate))
        _ (need (= {:symbol "ansatz_observed_frontend_gate_v1"
                    :parameters ["object" "object" "tobject" "object" "object" "void"]
                    :borrowed [true true true true true false] :result "tagged"} gate-spec)
                "Actual observer gate early ABI differs")
        known-hosts (conj known-hosts gate-spec)
        native-symbols (set (map :symbol natives)) native-abis (set (map abi-key natives))
        host-abis (set (map abi-key known-hosts))
        mf (io/file extern-directory "manifest.json") rf (io/file extern-directory "extern-rows.jsonl")
        _ (need (= manifest-pin extern-manifest-sha256) "Independently accepted extern manifest pin required")
        manifest (source/checked-json mf manifest-pin 65536)
        _ (need (and (= "complete-original-extern-metadata/1" (get manifest "schema"))
                     (= policies/index-pin (get manifest "source-index-sha256"))
                     (= 375258 (get manifest "declarations")) (= 961 (get manifest "extern-row-count"))
                     (= 120853740 (get manifest "source-index-bytes"))) "Complete original extern envelope differs")
        row-bytes (source/checked-bytes rf (get manifest "extern-rows-sha256") (* 16 1024 1024))
        coverage (atom []) specs (atom {})
        rows (with-open [reader (java.io.BufferedReader. (java.io.StringReader. (String. ^bytes row-bytes java.nio.charset.StandardCharsets/UTF_8)))]
               (reduce (fn [n line]
                         (need (and (< n 961) (<= (count line) (* 8 1024 1024))) "Original extern scan bound")
                         (let [record (json/read-str line) name (get record "name") sha (get record "sha256")
                               row (get record "row") entry (actual-entry! receipt name sha)
                               _ (need (and (= row (dissoc (:row entry) "pretty"))
                                            (= name (get row "name")) (= #{"extern"} (set (keys (get row "ir")))))
                                       "Early original index/CAS/raw extern row differs")
                               decl (get-in row ["ir" "extern"]) choice (selected row)
                               spec {:symbol (:symbol choice) :parameters (mapv #(get % "ty") (get decl "xs"))
                                     :borrowed (mapv #(get % "borrow") (get decl "xs")) :result (get decl "type")}
                               _ (need (and (every? boolean? (:borrowed spec)) (= name (get decl "f"))) "Malformed original extern ABI")
                               supported? (and (every? extern/lanes (:parameters spec)) (extern/lanes (:result spec)))
                               key (abi-key spec)
                               status (cond
                                        (not= :standard (:status choice)) (:status choice)
                                        (contains? native-symbols (:symbol spec)) (if (contains? native-abis key) :native-supported :native-symbol-ABI-mismatch)
                                        (contains? guest-symbols (:symbol spec)) :reserved-guest-export
                                        (not supported?) :unsupported-lane
                                        (contains? host-abis key) :existing-host-ABI
                                        :else :additional-host-ABI)]
                           (when (= status :additional-host-ABI) (swap! specs assoc key spec))
                           (swap! coverage conj {:name name :sha256 sha :symbol (:symbol spec) :ABI key :status status})
                           (inc n))) 0 (line-seq reader)))]
    (need (= 961 rows) "Incomplete original extern source domain")
    (cat/source-token catalogue)
    {:schema :source4-additional-early-host-specifications-v1
     :additional-early-host-specifications (vec (sort-by (comp pr-str abi-key) (vals @specs)))
     :gate-specification gate-spec
     :coverage @coverage :census {:original-extern-rows rows :status-counts (frequencies (map :status @coverage))
                                :additional-distinct-ABIs (count @specs)}
     :exclusions {:native-specifications natives :existing-and-planned-host-specifications known-hosts
                  :reserved-guest-symbols (vec (sort guest-symbols)) :original-policy-pins (:policy-pins reservations)
                  :required-IR-export-origins ir-rows}
     :pins {:manifest-sha256 manifest-pin :source-index-sha256 policies/index-pin
            :extern-rows-sha256 (get manifest "extern-rows-sha256")}
     :handler-authority false :SourceBinding-minted false :engine-created false :guest-work 0}))
