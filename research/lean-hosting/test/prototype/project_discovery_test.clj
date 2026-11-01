(ns prototype.project-discovery-test
  "Real filesystem captures with fixed header transport MODEL; no parser IR or import authority."
  (:require [clojure.test :refer [deftest is]]
            [clojure.data.json :as json]
            [clojure.java.io :as io]
            [prototype.project-discovery :as project]
            [prototype.project-source :as source]
            [prototype.classic-header-discovery-test :as header-model]
            [prototype.source-graph-runtime-test :as fixture]
            [prototype.source-import :as imports]
            [prototype.resident-frontend :as resident]
            [prototype.raw-interop :as raw])
  (:import [java.nio.file Files Path]
           [java.nio.charset StandardCharsets]))

(def limits {:max-roots 16 :max-native-modules 32 :max-modules 32 :max-depth 16 :max-edges 128
             :max-source-bytes 32768 :max-header-output-bytes 262144
             :max-name-nodes 32 :max-name-bytes 256 :max-total-name-bytes 32768})
(defn wire [segments] (reduce #(vector "str" %1 %2) ["anonymous"] segments))
(defn request [provider roots] {:provider provider :roots (mapv wire roots) :native-modules [(wire ["Init"])]})
(defn options [f] {:configuration (:configuration f) :header-limits header-model/limits
                  :limits limits :budgets {:helper-fuel 1000 :attempt-fuel 16000}})
(defn thrown [f] (try (f) nil (catch Throwable cause cause)))
(defn text [n] (str "-- modeled header for " n "\n"))
(defn write! [^Path root segments value]
  (let [p (reduce (fn [^Path p s] (.resolve p ^String s)) root
                  (conj (pop segments) (str (peek segments) ".lean")))]
    (Files/createDirectories (.getParent p) (make-array java.nio.file.attribute.FileAttribute 0))
    (Files/write p (.getBytes ^String value StandardCharsets/UTF_8) (make-array java.nio.file.OpenOption 0))
    p))
(defn with-files [files f]
  (let [root (Files/createTempDirectory "ansatz-project-discovery-" (make-array java.nio.file.attribute.FileAttribute 0))]
    (try (doseq [[segments value] files] (write! root segments value))
         (f root (source/provider [root] 4096))
         (finally
           (doseq [file (reverse (file-seq (.toFile root)))] (io/delete-file file true))))))
(defn configure [specs]
  (fn [input]
    (let [transport (header-model/configure input)
          symbol "classic_header_discovery_model"
          base-handler (get-in transport [:bindings symbol :handler])]
      (assoc-in transport [:bindings symbol :handler]
        (fn [context world args]
          (let [spec (get @specs (first args))
                parsed (assoc (header-model/header) :fileName (second args)
                              :hasErrors (boolean (:error? spec))
                              :diagnostics (if (:error? spec) [{:severity "error" :data "modeled parse error"}] [])
                              :requestedImports (if (:error? spec) []
                                                  (into imports/init-requests
                                                    (map #(assoc imports/init-request :module (wire %)) (:deps spec)))))]
            (reset! (:output transport) {:text (json/write-str parsed) :tag 0 :throw? (:throw? spec)})
            (base-handler context world args)))))))

(deftest real-captures-ordered-diamond-thread-one-scratch-packet-on-all-backends
  (doseq [backend [:reference :mutable :jvm]]
    (let [specs (atom {(text "D") {:deps [["B"] ["C"] ["B"]]}
                      (text "B") {:deps [["A"]]} (text "C") {:deps [["A"]]}
                      (text "A") {:deps []}})]
      (with-files (into {} (map #(vector [%] (text %)) ["A" "B" "C" "D"]))
        (fn [root provider]
          (fixture/with-empty-publication backend
            (fn [{:keys [context transport captured] :as f}]
              (let [entry (resident/snapshot context) captures (atom []) original source/capture-source
                    result (with-redefs [source/capture-source
                                         (fn [p module]
                                           (let [capture (original p module)]
                                             (swap! captures conj module)
                                             (when (= ["A"] module) (write! root ["A"] "-- edited after capture\n"))
                                             capture))]
                             (project/discover-project entry (request provider [["D"] ["D"]]) (options f)))
                    adopted (resident/adopt-prepared (:packet result) (:configuration f))]
                (swap! captured conj adopted)
                (is (= [["D"] ["B"] ["A"] ["C"]] @captures))
                (is (= [["A"] ["B"] ["C"] ["D"]] (get-in result [:graph :order])))
                (is (= [["D"] ["D"]] (get-in result [:graph :roots])))
                (is (= 13 (get-in result [:progress :edges])))
                (is (= 4 (get-in result [:progress :helper-calls])))
                (is (= (* 4 (:max-output-bytes header-model/limits)) (get-in result [:progress :header-output-reserved])))
                (is (= (text "A") (get-in result [:graph :nodes ["A"] :capture :text])))
                (is (= (text "A") (first (nth @(:calls transport) 2))))
                (is (= 4 (get-in (resident/snapshot adopted) [:world :globals header-model/marker :value])))
                (is (true? (identical? entry (resident/snapshot context))))
                (is (true? (= (get-in entry [:world :heap]) (get-in result [:packet :world :heap]))))
                (resident/close! adopted)))
            :configure (configure specs)))))))

(deftest terminal-cycle-missing-and-parser-errors-retain-latest-packet-and-graph
  (doseq [[case specs expected-calls]
          [[:cycle {(text "A") {:deps [["B"]]} (text "B") {:deps [["A"]]}} 2]
           [:missing {(text "A") {:deps [["Missing"]]}} 1]
           [:parser {(text "A") {:error? true}} 1]]]
    (with-files {["A"] (text "A") ["B"] (text "B")}
      (fn [_ provider]
        (fixture/with-empty-publication :reference
          (fn [{:keys [context] :as f}]
            (let [cause (thrown #(project/discover-project (resident/snapshot context) (request provider [["A"]]) (options f)))
                  state (:project-discovery-state (ex-data cause))]
              (is (some? cause) (name case))
              (is (= expected-calls (:helper-calls state)))
              (is (= expected-calls (get-in state [:packet :world :globals header-model/marker :value])))
              (is (true? (identical? (get-in state [:packet :world]) (:checkpoint (ex-data cause)))))
              (is (contains? (:nodes state) ["A"]))
              (when (= :parser case)
                (is (= "Project source header contains parser errors" (.getMessage cause)))
                (is (true? (identical? (:packet state) (get-in state [:last-header :packet]))))
                (is (= :header-error (get-in state [:last-header :status])))
                (is (zero? (:reserved state))))))
          :configure (configure (atom specs)))))))

(deftest independent-aggregate-bounds-and-longest-shared-path
  (let [specs (atom {(text "A") {:deps []} (text "B") {:deps [["A"]]}
                    (text "C") {:deps [["B"]]}})]
    (with-files {["A"] (text "A") ["B"] (text "B") ["C"] (text "C")}
      (fn [_ provider]
        (fixture/with-empty-publication :reference
          (fn [{:keys [context transport] :as f}]
            (doseq [[changed roots label]
                    [[{:limits (assoc limits :max-depth 2)} [["A"] ["C"]] :longest-black-path]
                     [{:limits (assoc limits :max-modules 1)} [["B"]] :modules]
                     [{:limits (assoc limits :max-edges 2)} [["B"]] :edges]
                     [{:limits (assoc limits :max-source-bytes 1)} [["B"]] :source]
                     [{:limits (assoc limits :max-header-output-bytes 8192)} [["B"]] :output]
                     [{:budgets {:helper-fuel 1 :attempt-fuel 1}} [["A"]] :fuel]]]
              (let [cause (thrown #(project/discover-project (resident/snapshot context)
                                    (request provider roots) (merge (options f) changed)))
                    state (:project-discovery-state (ex-data cause))]
                (is (some? cause) (name label))
                (is (<= (:source-bytes state) (get-in (merge (options f) changed) [:limits :max-source-bytes])))
                (is (<= (:used state) (get-in (merge (options f) changed) [:budgets :attempt-fuel])))))
            (is (seq @(:calls transport))))
          :configure (configure specs))))))

(deftest native-data-leaves-and-pre-guest-validation
  (fixture/with-empty-publication :reference
    (fn [{:keys [context transport] :as f}]
      (with-files {}
        (fn [_ provider]
          (let [entry (resident/snapshot context)
                native-request (request provider [["Init"]])
                result (project/discover-project entry native-request (options f))]
            (is (true? (identical? entry (:packet result))))
            (is (empty? (get-in result [:graph :nodes])))
            (is (empty? @(:calls transport)))
            (doseq [bad [(assoc native-request :roots [])
                         (assoc native-request :roots [["str" ["anonymous"] "Bad.Module"]])
                         (assoc native-request :roots [["num" ["anonymous"] "2"]])
                         (assoc-in native-request [:provider :unknown] true)]]
              (is (some? (thrown #(project/discover-project entry bad (options f))))))
            (is (some? (thrown #(project/discover-project entry native-request (assoc (options f) :configuration {})))))
            (let [captures (atom 0)
                  cause (with-redefs [source/capture-source (fn [& _] (swap! captures inc))]
                          (thrown #(project/discover-project entry (request provider [["A"]])
                                    (assoc-in (options f) [:header-limits :max-imports] 1))))]
              (is (.contains (.getMessage cause) "require 2..1026 imports"))
              (is (zero? @captures)))
            (is (empty? @(:calls transport)))))))
    :configure (configure (atom {}))))

(deftest nested-known-and-unknown-failures-keep-owner-and-reservation-evidence
  (with-files {["A"] (text "A")}
    (fn [_ provider]
      (fixture/with-empty-publication :reference
        (fn [{:keys [context transport] :as f}]
          (let [entry (resident/snapshot context)
                known (thrown #(project/discover-project entry (request provider [["A"]]) (options f)))
                state (:project-discovery-state (ex-data known))]
            (is (some? known))
            (is (pos? (:used state)))
            (is (zero? (:reserved state)))
            (is (true? (identical? (:checkpoint (ex-data known)) (get-in state [:packet :world]))))
            (is (= 1 (get-in state [:packet :world :globals header-model/marker :value]))))
          (let [selected (ex-info "selected unknown project transport failure" {})
                unknown (with-redefs [raw/call (fn [& _] (throw selected))]
                          (thrown #(project/discover-project (resident/snapshot context) (request provider [["A"]]) (options f))))
                state (:project-discovery-state (ex-data unknown))]
            (is (zero? (:used state)))
            (is (= 1000 (:reserved state)))
            (is (true? (identical? (:checkpoint-session (ex-data unknown)) (get-in state [:packet :session]))))))
        :configure (configure (atom {(text "A") {:throw? true}}))))))

(deftest two-root-header-output-reservation-matches-capture-boundary
  ;; Actual failed campaign limits: aggregate16KiB and per-header16KiB permit
  ;; one source only. Model transport makes this host budget boundary cheap to
  ;; reproduce; it is not another real frontend run or proof of the lost cause.
  (let [specs (atom {(text "A") {:deps []} (text "D") {:deps []}})]
    (with-files {["A"] (text "A") ["D"] (text "D")}
      (fn [_ provider]
        (fixture/with-empty-publication :reference
          (fn [{:keys [context transport captured] :as f}]
            (let [entry (resident/snapshot context)
                  header-bytes 16384
                  policy (-> (options f)
                             (assoc-in [:header-limits :max-output-bytes] header-bytes)
                             (assoc-in [:limits :max-roots] 2)
                             (assoc-in [:limits :max-modules] 4)
                             (assoc-in [:limits :max-header-output-bytes] header-bytes))
                  before (count @(:calls transport))
                  cause (thrown #(project/discover-project entry
                                  (request provider [["A"] ["D"]]) policy))
                  data (ex-data cause) failed (:project-discovery-state data)]
              (is (= "Project discovery cannot reserve next header output" (.getMessage cause)))
              (is (= 1 (- (count @(:calls transport)) before)))
              (is (= 1 (:helper-calls failed)))
              (is (= header-bytes (:header-output-reserved failed)))
              (is (= :capture (:phase failed)))
              (is (= (text "A") (get-in failed [:nodes ["A"] :capture :text])))
              (is (= (text "D") (get-in failed [:nodes ["D"] :capture :text])))
              (is (identical? (:packet failed) (get-in failed [:last-header :packet])))
              (is (identical? (:checkpoint data) (get-in failed [:packet :world])))
              (is (identical? (:checkpoint-session data) (get-in failed [:packet :session])))
              (is (= 1 (get-in failed [:packet :world :globals header-model/marker :value])))
              (is (zero? (:reserved failed)))
              (is (identical? entry (resident/snapshot context)))
              ;; A separate discovery on the unchanged input, not a retry of its
              ;; failed state. Four declared modules receive four reservations.
              (let [before (count @(:calls transport))
                    result (project/discover-project entry
                             (request provider [["A"] ["D"]])
                             (assoc-in policy [:limits :max-header-output-bytes] 65536))
                    adopted (resident/adopt-prepared (:packet result) (:configuration f))]
                (swap! captured conj adopted)
                (is (= 2 (- (count @(:calls transport)) before)))
                (is (= 2 (get-in result [:progress :helper-calls])))
                (is (= 32768 (get-in result [:progress :header-output-reserved])))
                (is (= [["A"] ["D"]] (get-in result [:graph :roots])))
                (is (= [["A"] ["D"]] (get-in result [:graph :order])))
                (is (= 2 (get-in result [:packet :world :globals header-model/marker :value])))
                (is (identical? entry (resident/snapshot context))))))
          :configure (configure specs))))))

(deftest aggregate-reservations-after-success-and-project-only-post-header-refusals
  (let [specs (atom {(text "A") {:deps []} (text "B") {:deps []}})]
    (with-files {["A"] (text "A") ["B"] (text "B")}
      (fn [_ provider]
        (fixture/with-empty-publication :reference
          (fn [{:keys [context transport] :as f}]
            (let [entry (resident/snapshot context)
                  first-result (project/discover-project entry (request provider [["A"]]) (options f))
                  first-charge (get-in first-result [:progress :used])]
              (is (pos? first-charge))
              (doseq [[changed message]
                      [[{:limits (assoc limits :max-source-bytes (inc (count (text "A"))))} "Source exceeds byte limit"]
                       [{:limits (assoc limits :max-header-output-bytes 8192)} "cannot reserve next header output"]
                       [{:budgets {:helper-fuel 1000 :attempt-fuel first-charge}} "exhausted helper fuel"]]]
                (let [before (count @(:calls transport))
                      cause (thrown #(project/discover-project entry (request provider [["A"] ["B"]]) (merge (options f) changed)))
                      state (:project-discovery-state (ex-data cause))]
                  (is (and (some? cause) (.contains (.getMessage cause) message)))
                  (is (= :capture (:phase state)))
                  (is (= 1 (- (count @(:calls transport)) before)))
                  (is (= 1 (:helper-calls state)))
                  (is (= first-charge (:used state)))
                  (is (zero? (:reserved state)))
                  (is (<= (+ (:used state) (:reserved state)) (get-in (merge (options f) changed) [:budgets :attempt-fuel])))
                  (is (= (text "A") (get-in state [:nodes ["A"] :capture :text])))
                  (is (= 1 (get-in state [:packet :world :globals header-model/marker :value])))
                  (is (true? (identical? (get-in state [:last-header :packet]) (:packet state))))))
              ;; All raw Name occurrences (implicit Init twice and B twice) are
              ;; charged before dedup. 5 input bytes + 10 header bytes >14.
              (reset! specs {(text "A") {:deps [["B"] ["B"]]}})
              (let [cause (thrown #(project/discover-project entry (request provider [["A"]])
                                    (assoc (options f) :limits (assoc limits :max-total-name-bytes 14))))
                    state (:project-discovery-state (ex-data cause))]
                (is (.contains (.getMessage cause) "Project module Name exceeds bounds"))
                (is (= :header-returned (:phase state)))
                (is (= 1 (:helper-calls state)))
                (is (= 4 (count (get-in state [:last-header :header :requestedImports])))))
              ;; Slash segments are valid descriptive Lean header Names but are
              ;; outside this filesystem provider's Project module subset.
              (reset! specs {(text "A") {:deps [["Bad/Path"]]}})
              (let [cause (thrown #(project/discover-project entry (request provider [["A"]]) (options f)))
                    state (:project-discovery-state (ex-data cause))]
                (is (.contains (.getMessage cause) "outside the string-segment subset"))
                (is (= :ok (get-in state [:last-header :status])))
                (is (= :header-returned (:phase state)))
                (is (true? (identical? (:packet state) (get-in state [:last-header :packet]))))
                (is (true? (= (get-in entry [:world :heap]) (get-in state [:packet :world :heap]))))
                (is (= 1 (get-in state [:packet :world :globals header-model/marker :value]))))))
          :configure (configure specs))))))
