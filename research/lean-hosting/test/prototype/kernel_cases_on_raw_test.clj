(ns prototype.kernel-cases-on-raw-test)
;; Actual native-CI fixture + actual compiled Lean/CAS code. The six-field
;; Kernel.Environment below is constructor STORAGE ONLY, never admission authority.
(require '[clojure.test :as t] '[clojure.data.json :as json]
         '[clojure.string :as str] '[clojure.java.io :as io] '[prototype.machine :as m]
         '[prototype.raw-interop :as raw] '[prototype.runtime-abi :as abi]
         '[prototype.import-ir :as ir] '[prototype.module-store :as store]
         '[prototype.native-scalar :as native] '[prototype.runtime-string :as runtime-string]
         '[prototype.checkpoint-wire :as wire]
         '[prototype.raw-cases-on-panic-support :as panic-support] '[prototype.lazy-runtime :as lazy])
(def fixture-prefix "fixtures/raw-cases-on/")
(defn resource-bytes [name limit]
  (with-open [input (io/input-stream (or (io/resource (str fixture-prefix name))
                                       (throw (ex-info "Missing RAW fixture resource" {:name name}))))
              output (java.io.ByteArrayOutputStream.)]
    (let [buffer (byte-array 65536)]
      (loop [total 0]
        (let [n (.read input buffer)]
          (if (neg? n) (.toByteArray output)
            (let [next (+ total n)]
              (when (> next limit) (throw (ex-info "RAW fixture resource bound" {:name name})))
              (.write output buffer 0 n)
              (recur next))))))))
(def fixture-manifest (json/read-str (String. ^bytes (resource-bytes "manifest.json" 65536) "UTF-8")))
(defn fixture-bytes [name]
  (let [bytes (resource-bytes name 1048576)
        expected (get-in fixture-manifest ["files" name])]
    (when-not (and (string? expected) (= expected (wire/sha256 bytes)))
      (throw (ex-info "RAW fixture resource digest" {:name name}))) bytes))
(def fixture-directory (.toFile (java.nio.file.Files/createTempDirectory
                                  "ansatz-raw-cases-on-" (make-array java.nio.file.attribute.FileAttribute 0))))
(.deleteOnExit fixture-directory)
(defn materialize [name bytes]
  (let [file (io/file fixture-directory name)]
    (.deleteOnExit file)
    (java.nio.file.Files/write (.toPath file) ^bytes bytes (make-array java.nio.file.OpenOption 0))
    (.getPath file)))
(defn fixture-file [name] (materialize name (fixture-bytes name)))
(defn dataset-file [kind]
  (let [info (get-in fixture-manifest ["datasets" (name kind)])
        encoded (fixture-bytes (get info "file"))
        file (io/file fixture-directory (str (name kind) "-module-data.jsonl"))]
    (.deleteOnExit file)
    (with-open [input (java.util.zip.GZIPInputStream. (java.io.ByteArrayInputStream. encoded))
                output (io/output-stream file)]
      (let [buffer (byte-array 65536)]
        (loop [total 0]
          (let [n (.read input buffer)]
            (when-not (neg? n)
              (let [next (+ total n)]
                (when (> next 8388608) (throw (ex-info "RAW fixture decompression bound" {})))
                (.write output buffer 0 n)
                (recur next)))))))
    (when-not (and (= (.length file) (get info "sourceBytes"))
                   (= (wire/sha256 (wire/read-file-bytes (.getPath file) 8388608)) (get info "sourceSha256")))
      (throw (ex-info "RAW fixture decoded digest" {})))
    (.getPath file)))
(defn nm [& parts] (reduce (fn [parent part] ["str" parent part]) ["anonymous"] parts))
(def helper-root (nm "KernelCasesOnRaw" "construct"))
(def construct (nm "Lean" "mkCasesOnImp"))
(declare compiled-executions)
(def map-root (nm "KernelCasesOnProbe" "constantMap"))
(def equal-root (nm "KernelCasesOnProbe" "sameDefinition"))
(def profile-root (nm "KernelCasesOnFingerprint" "profileType"))
(def roots [construct map-root equal-root profile-root])
(def locals (mapv fixture-file ["constructor-ir.jsonl" "probe-ir.jsonl" "fingerprint-ir.jsonl"]))
(def cas-path (fixture-file "imported-ir.jsonl"))
(defn rows [path] (mapv #(json/read-str % :key-fn keyword) (str/split-lines (slurp path))))
(defn check! [ok message] (when-not ok (throw (ex-info message {}))))
;; Reuse the already three-backend tested bounded faithful panic controller.
;; The exact captured prefix is inert provenance for the ordinary test-support
;; namespace; no broad preseal/controller model is needed for this program.
(def panic-source-record (json/read-str (String. ^bytes (fixture-bytes "panic-factory.json") "UTF-8")))
(def panic-prefix (get panic-source-record "source"))
(check! (= (get panic-source-record "sha256") (wire/sha256 (.getBytes ^String panic-prefix "UTF-8")))
        "Captured host source text digest")
;; The captured text is inert provenance. Execute only the standard support
;; namespace, whose exact implementation body is checked against that capture.
(def support-source (slurp (io/resource "prototype/raw_cases_on_panic_support.clj")))
(check! (= (str/replace panic-prefix #"\n+\z" "\n")
           (second (str/split support-source #";; BEGIN EXACT CAPTURED FACTORY\n" 2)))
        "Portable panic support must match the reviewed captured source")
(def panic-symbol panic-support/panic-symbol)
(def original-row-bytes (fixture-bytes "original-extern.json"))
(check! (= "d7a54765268331ebe9afdfa4695a7702b8d53c95cd1a8c51da8ef41d1468e43d" (wire/sha256 original-row-bytes)) "Actual original extern CAS bytes")
(def original-row (json/read-str (wire/utf8-string original-row-bytes) :key-fn keyword))
(def catalogue
  (let [base (ir/index-bundles locals) cas (rest (rows cas-path))]
    (check! (= 252 (count cas) (count (set (map :name cas)))) "Exact independently captured CAS inventory")
    (check! (not-any? #(contains? (:declarations base) (:name %)) cas) "CAS/local overlap")
    (let [producer (update base :declarations into (map (juxt :name identity) cas))
          _ (check! (not (contains? (:declarations producer) construct)) "No pre-existing original extern")
          producer (assoc-in producer [:declarations construct] original-row)
          _ (check! (= {} (get fixture-manifest "usedExportAliases")) "No required export alias omitted")
          aliased producer
          consumer (abi/with-consumer-redirects aliased
                     {"lean_mk_cases_on" {:original-row original-row :target helper-root}})]
      (check! (= original-row (get-in consumer [:declarations construct])) "Producer CAS row stays unmodified")
      consumer)))
(def fingerprint-inputs (json/read-str (String. ^bytes (fixture-bytes "expected-profiles.json") "UTF-8") :key-fn keyword))
(def datasets
  [{:kind :annotated :count 16 :prefix "RawCasesOnPayload" :source (dataset-file :annotated)}
   {:kind :ordinary :count 255 :prefix "RawCasesOnOracle" :source (dataset-file :ordinary)}])
(def observations (atom []))
(def failure-escrow (atom nil))
(defn field [world value index] (nth (:fields (m/node world value)) index))
(defn type-ref [world ci] (field world (field world (field world ci 0) 0) 2))
(defn ci-name [world ci] (field world (field world (field world ci 0) 0) 0))
;; Source-only extension draft, independent of frozen annotated gate.
;; Preserve Name.num components in structured form; never flatten private names.
(defn bounded-name-value [world value]
  (let [ops {:node m/node :ref? m/ref?}]
    (loop [value value parts [] depth 0 characters 0 seen #{}]
      (check! (and (< depth 64) (<= characters 4096)) "Fixture Name bounds")
      (if-not (m/ref? value)
        (do
          (check! (= 0 (native/nat-value value)) "Fixture anonymous Name")
          (reduce (fn [parent [kind payload]] [kind parent payload]) ["anonymous"] (reverse parts)))
        (let [node (m/node world value) [parent payload] (:fields node)]
          (check! (and (= :ctor (:kind node)) (contains? #{1 2} (:tag node))
                       (= 2 (count (:fields node))) (not (contains? seen (:id value))))
                  "Fixture acyclic Name.str/Name.num")
          (let [[kind text]
                (case (:tag node)
                  1 (let [string-node (m/node world payload)]
                      (check! (and (= :string (:kind string-node)) (string? (:text string-node))
                                   (<= (count (:text string-node)) (- 4096 characters)))
                              "Fixture Name string bound before traversal")
                      ["str" (runtime-string/string-value ops world payload)])
                  2 (let [number (biginteger (native/nat-value ops world payload))]
                      ;; bitLength is O(1), checked BEFORE decimal formatting.
                      (check! (and (not (neg? (.signum number))) (<= (.bitLength number) 2048))
                              "Fixture numeric Name payload bound")
                      ["num" (str number)]))
                next-characters (+ characters (count text))]
            (check! (<= next-characters 4096) "Fixture Name aggregate character bound")
            (recur parent (conj parts [kind text]) (inc depth) next-characters
                   (conj seen (:id value)))))))))
(def ordinary-suffixes ["Colour" "Pair" "Box" "Sized" "Ping" "Pong" "Rose" "ChoiceProp" "UnsafeBox" "Tree"])
(def ordinary-expected-names
  (set (map #(nm "RawCasesOnOracle" % "casesOn") ordinary-suffixes)))
(defn ordinary-input-partition [world constants]
  (let [by-name (into {} (map (fn [ci] [(bounded-name-value world (ci-name world ci)) ci]) constants))
        _ (check! (= (count constants) (count by-name)) "Actual unique CI names")
        expected (select-keys by-name ordinary-expected-names)
        _ (check! (= ordinary-expected-names (set (keys expected))) "Actual ten native casesOn answers")
        _ (check! (every? #(= 1 (:tag (m/node world %))) (vals expected)) "Native expected answers are definitions")
        expected-refs (set (vals expected))
        inputs (filterv #(not (contains? expected-refs %)) constants)]
    (check! (= (- (count constants) 10) (count inputs)) "Exclude only selected native answers")
    ;; Retain EVERY other actual CI, including mutual/nested auxiliary families,
    ;; their recursors, constructors, generated helpers and private numeric names.
    {:by-name by-name :expected expected :inputs inputs}))

(def name-value bounded-name-value)
(defn finite-call [session world target arguments]
  (try
    (let [packet (raw/call session world target arguments)]
      (reset! failure-escrow {:state (:state packet) :session (:session packet) :stage target})
      packet)
    (catch Throwable cause
      (reset! failure-escrow {:cause cause :stage target})
      (throw cause))))
(defn except-ok [world value]
  (let [node (m/node world value)]
    (check! (and (= :ctor (:kind node)) (= 1 (:tag node)) (= 1 (count (:fields node)))) "Actual Except.ok required")
    (first (:fields node))))
(defn array-nats [world array]
  (let [node (m/node world array)]
    (check! (and (= :array (:kind node)) (= 9 (count (:fields node)))) "Bounded nine-scalar fingerprint")
    (mapv #(native/nat-value {:node m/node :ref? m/ref?} world %) (:fields node))))
(defn profile! [session world expression expected]
  (let [packet (finite-call session world profile-root [expression])
        w (:state packet) array (except-ok w (:value packet))]
    (t/is (= expected (array-nats w array)))
    (m/release w (:value packet) 1)))
(defn fixture [backend dataset]
  (let [data-source (:source dataset)]
  (let [reports (atom []) panic (panic-support/make-panic-controller
                                {:policy {:mode :return :messages? true :backtrace? false
                                          :max-message-bytes 4096 :max-output-bytes 65536 :max-events 16}
                                 :diagnostic-sink (fn [text] (swap! reports conj text) nil)})
        bindings {panic-symbol (:binding panic)}
        lower (fn [row]
                (if (= panic-symbol (some-> row :ir :extern abi/symbol-for))
                  (raw/lower bindings row) (abi/lower-catalogue catalogue row)))
        functions (ir/load-closure catalogue roots lower)
        _ (check! (not-any? #(or (:deferred-extern %) (:deferred-declaration %) (:runtime-initializer %)) (vals functions))
                  "No deferred or effectful initializer frontier")
        _ (t/is (= {:params [1 2] :export-redirect helper-root
                       :body [:tail [:direct helper-root] [[:var 1] [:var 2]]]}
                    (get functions construct)))
        session (raw/open-functions functions bindings {:backend backend :fuel 20000000})
        _ (when (= :jvm backend)
            (t/is (= 0 (:cached-blocks (lazy/summary (:program session))))))
        opened (store/load-file (m/world functions) data-source
                         {:sha256 (get-in fixture-manifest ["datasets" (name (:kind dataset)) "sourceSha256"])
                          :max-nodes 40000 :max-bytes 8388608 :max-row-bytes 1048576 :cache-size 256})]
    (try
      (let [w (:world opened) module (-> opened :modules first :parts first :value)
            constants (:fields (m/node w (field w module 2)))
            _ (check! (= (:count dataset) (count constants)) "Exact actual native CI inventory")
            by-name (into {} (map (fn [ci] [(name-value w (ci-name w ci)) ci]) constants))
            _ (check! (= (:count dataset) (count by-name)) "Unique actual CI names")
            selected-suffixes (if (= :ordinary (:kind dataset)) ordinary-suffixes
                                 ["Metadata" "DependentLet" "NondependentLet" "IMax"])
            expected-names (set (map #(nm (:prefix dataset) % "casesOn") selected-suffixes))
            expected (select-keys by-name expected-names)
            _ (check! (= expected-names (set (keys expected))) "Exact selected native answers")
            _ (check! (every? #(= 1 (:tag (m/node w %))) (vals expected)) "Native expected definition variants")
            expected-refs (set (vals expected))
            inputs (filterv #(not (contains? expected-refs %)) constants)
            _ (check! (= (- (:count dataset) (count selected-suffixes)) (count inputs)) "Only selected expected answers excluded")
            _ (when (= :annotated (:kind dataset))
                (check! (= {5 4 6 4 7 4} (frequencies (map #(:tag (m/node w %)) inputs)))
                        "Actual annotated inductive/constructor/recursor variants"))
            [w array] (m/allocate w :array 0 inputs)
            packet (finite-call session w map-root [array])
            w (m/release (:state packet) array 1) constants-map (:value packet)
            ;; EXACT pinned six object slots + quotient byte. Only constants is
            ;; semantically used by this pure constructor. No checker sees this.
            [w environment] (m/scalar-constructor w 0 [constants-map 0 0 0 0 0] {:objects 6 :usize 0 :ssize 1})
            w (m/replace-node w environment (m/write-scalar-node (m/node w environment)
                {:index 6 :offset 0 :type "uint8" :region :scalar} 0))
            _ (check! (= 1 (:rc (m/node w environment))) "Owned constructor-only carrier")]
        {:opened opened :world w :session session :environment environment :by-name by-name
         :expected expected :reports reports :functions functions :bindings bindings
         :constants constants :dataset dataset})
      (catch Throwable cause
        ;; Keep its Source owner with the canonical failure packet until this
        ;; terminal standalone process is disposed. No failed-control retry.
        (swap! failure-escrow assoc :cause cause :source (:source opened)
               :source-lifecycle :open-until-process-disposal)
        (throw cause))))))
(defn annotated-round! [f world]
  (reduce
    (fn [world suffix]
      (let [base-name (nm "RawCasesOnPayload" suffix)
            inductive (get (:by-name f) base-name)
            recursor (get (:by-name f) (nm "RawCasesOnPayload" suffix "rec"))
            expected (get (:expected f) (nm "RawCasesOnPayload" suffix "casesOn"))
            profiles (get-in fingerprint-inputs [:expected (keyword suffix)])
            _ (check! (and inductive recursor expected profiles) "Exact fixture member")
            world (profile! (:session f) world (type-ref world recursor) (:input profiles))
            world (profile! (:session f) world (type-ref world expected) (:output profiles))
            entry (m/retain world (:environment f) 1)
            start-steps (get-in entry [:stats :steps])
            before-compiled @compiled-executions
            packet (finite-call (:session f) entry construct [(:environment f) (ci-name entry inductive)])
            constructor-compiled-delta (- @compiled-executions before-compiled)
            w (:state packet) declaration (except-ok w (:value packet))
            _ (when (= :jvm (get-in f [:session :backend]))
                (t/is (pos? constructor-compiled-delta)))
            _ (t/is (= 1 (:tag (m/node w declaration))))
            _ (t/is (= 1 (:rc (m/node w (:environment f)))))
            cmp (finite-call (:session f) w equal-root [declaration expected])
            w (:state cmp)
            _ (t/is (= 1 (native/unsigned-value 8 (:value cmp))))
            w (profile! (:session f) w (type-ref w declaration) (:output profiles))
            w (m/release w (:value packet) 1)]
        (t/is (= 1 (:rc (m/node w (:environment f)))))
        (swap! observations conj {:kind :raw-annotated-constructor :suffix suffix
                                  :steps (- (get-in w [:stats :steps]) start-steps)
                                  :compiled-executor-delta constructor-compiled-delta
                                  :backend (get-in f [:session :backend]) :dataset (get-in f [:dataset :kind]) :entry construct})
        w))
    world ["Metadata" "DependentLet" "NondependentLet" "IMax"]))
(def name-str-root (nm "Lean" "Name" "str" "_override"))
(defn local-name-error! [f world]
  (let [row (get-in catalogue [:declarations name-str-root])
        function (get-in row [:ir :fdecl])
        _ (check! (= {:params [{:ty "tobject" :borrow false} {:ty "object" :borrow false}]
                     :type "tobject"}
                    {:params (mapv #(select-keys % [:ty :borrow]) (:xs function)) :type (:type function)})
                  "Actual Name.str ownership ABI")
        [world text] (m/allocate world :string 0 [])
        world (m/replace-node world text (assoc (m/node world text) :text "MissingLocalλ🦉"))
        made (finite-call (:session f) world name-str-root [(m/->Tag 0) text])
        world (:state made) local-name (:value made)
        _ (t/is (= 1 (:rc (m/node world local-name))))
        packet (finite-call (:session f) (m/retain world (:environment f) 1) construct
                            [(:environment f) local-name])
        w (:state packet) result (m/node w (:value packet)) error (m/node w (first (:fields result)))]
    (t/is (= [0 0] [(:tag result) (:tag error)]))
    (t/is (= [(:environment f) local-name] (:fields error)))
    (t/is (= 2 (:rc (m/node w local-name))))
    (let [w (m/release w (:value packet) 1)]
      (t/is (= 1 (:rc (m/node w local-name))))
      (t/is (= 1 (:rc (m/node w (:environment f)))))
      (let [w (m/release w local-name 1)]
        (t/is (not (contains? (:heap w) (:id local-name))))
        (t/is (not (contains? (:heap w) (:id text))))
        w))))
(defn typed-errors! [f world]
  ;; The native expected casesOn Name exists in the data, but was intentionally
  ;; excluded from this input map. This proves lookup uses the real input map.
  (let [expected (get (:expected f) (nm "RawCasesOnPayload" "Metadata" "casesOn"))
        missing (ci-name world expected)
        packet (finite-call (:session f) (m/retain world (:environment f) 1) construct [(:environment f) missing])
        w (:state packet) result (m/node w (:value packet)) error (m/node w (first (:fields result)))]
    (t/is (= [0 0] [(:tag result) (:tag error)]))
    (t/is (= [(:environment f) missing] (:fields error)))
    (t/is (= 2 (:rc (m/node w (:environment f)))))
    (let [w (m/release w (:value packet) 1)
          ctor (get (:by-name f) (nm "RawCasesOnPayload" "Metadata" "wrap"))
          packet (finite-call (:session f) (m/retain w (:environment f) 1) construct [(:environment f) (ci-name w ctor)])
          w (:state packet) result (m/node w (:value packet)) error (m/node w (first (:fields result)))]
      (t/is (= [0 12] [(:tag result) (:tag error)]))
      (t/is (= "error in 'casesOn' generation, 'RawCasesOnPayload.Metadata.wrap' is not an inductive datatype"
               (runtime-string/string-value {:node m/node :ref? m/ref?} w (first (:fields error)))))
      (t/is (= 1 (:rc (m/node w (:environment f)))))
      (local-name-error! f (m/release w (:value packet) 1)))))
(defn ordinary-round! [f world]
  (reduce
    (fn [world suffix]
      (let [inductive (get (:by-name f) (nm "RawCasesOnOracle" suffix))
            expected (get (:expected f) (nm "RawCasesOnOracle" suffix "casesOn"))
            _ (check! (and inductive expected (= 5 (:tag (m/node world inductive)))) "Actual selected ordinary family")
            entry (m/retain world (:environment f) 1)
            before-compiled @compiled-executions start-steps (get-in entry [:stats :steps])
            packet (finite-call (:session f) entry construct [(:environment f) (ci-name entry inductive)])
            constructor-compiled-delta (- @compiled-executions before-compiled)
            w (:state packet) declaration (except-ok w (:value packet))
            _ (t/is (= 1 (:tag (m/node w declaration))))
            _ (t/is (= 1 (:rc (m/node w (:environment f)))))
            cmp (finite-call (:session f) w equal-root [declaration expected])
            w (:state cmp)
            _ (t/is (= 1 (native/unsigned-value 8 (:value cmp))))
            _ (when (= :jvm (get-in f [:session :backend]))
                (t/is (pos? constructor-compiled-delta)))
            w (m/release w (:value packet) 1)]
        (t/is (= 1 (:rc (m/node w (:environment f)))))
        (swap! observations conj {:kind :raw-ordinary-constructor :suffix suffix
                                  :steps (- (get-in w [:stats :steps]) start-steps)
                                  :compiled-executor-delta constructor-compiled-delta
                                  :backend (get-in f [:session :backend]) :dataset (get-in f [:dataset :kind]) :entry construct})
        w)) world ordinary-suffixes))
(defn whole-round! [f world]
  (if (= :ordinary (get-in f [:dataset :kind])) (ordinary-round! f world)
      (typed-errors! f (annotated-round! f world))))
(defn source-snapshot [f world]
  ;; Every actual CI (including expected answers and all auxiliary families),
  ;; transitively. Unused serialized IR/extension payloads are not walked.
  (let [source (:source (:opened f)) base (:base source) end (+ base (:size source))]
    (loop [pending (:constants f) seen {}]
      (if (empty? pending) seen
        (let [value (peek pending) pending (pop pending)]
          (if-not (m/ref? value) (recur pending seen)
            (let [id (:id value)]
              (check! (<= base id (dec end)) "CI graph stays in actual native Source")
              (if (contains? seen id) (recur pending seen)
                (let [_ (check! (< (count seen) 20000) "Unchanged20k CI snapshot bound")
                      node (m/node world value)]
                  (recur (into pending (:fields node)) (assoc seen id node)))))))))))
(defn assert-source-preserved! [world snapshot]
  (let [source (first (:native-imports world)) base (:base source) end (+ base (:size source))]
    (t/is (not-any? #(<= base % (dec end)) (keys (:heap world)))))
  (t/is (every? (fn [[id before]] (= before (m/node world (m/->Ref id)))) snapshot)))
(def compiled-executions (atom 0))
(def fallback-executions (atom 0))
(require '[prototype.block-compile :as block])
(def original-compile-runtime-block-prepared block/compile-runtime-block-prepared)
(defn observe-compile [functions body options]
  (let [result (original-compile-runtime-block-prepared functions body options)
        counter (if (some? (:form result)) compiled-executions fallback-executions)]
    (cond-> (assoc result :execute! (fn [machine] (swap! counter inc) ((:execute! result) machine)))
      (:execute-budget! result)
      (assoc :execute-budget! (fn [machine fuel] (swap! counter inc) ((:execute-budget! result) machine fuel))))))
(defn exercise-backend! [backend dataset]
  (let [f (fixture backend dataset) source (:source (:opened f)) world (:world f)
        snapshot (source-snapshot f world) first-input (get (:by-name f) (nm (:prefix dataset) (if (= :ordinary (:kind dataset)) "Colour" "Metadata")))
        original-heap (:heap world) original-globals (:globals world)
        original-node (m/node world (:environment f)) completed? (atom false)]
    (try
      (let [warm (whole-round! f world)
            ;; Execute a second time through the returned/released world. Stable
            ;; cache roots distinguish immortal global memoization from leaks.
            before-globals (:globals warm) before-heap-keys (set (keys (:heap warm)))
            repeated (whole-round! f warm)
            _ (t/is (= before-globals (:globals repeated)))
            _ (t/is (= before-heap-keys (set (keys (:heap repeated)))))
            _ (t/is (empty? @(:reports f)))
            _ (t/is (= original-node (m/node world (:environment f))))
            _ (t/is (identical? original-heap (:heap world)))
            _ (t/is (identical? original-globals (:globals world)))
            _ (assert-source-preserved! repeated snapshot)
            ;; A genuinely separate immutable fork starts from the pristine
            ;; carrier and must produce the same full raw native answer.
            fork (whole-round! f world)
            _ (assert-source-preserved! fork snapshot)
            released (m/release repeated (:environment f) 1)
            fork-released (m/release fork (:environment f) 1)]
        (t/is (every? #(zero? (:rc %)) (vals (:heap released))))
        (t/is (every? #(zero? (:rc %)) (vals (:heap fork-released)))))
      ;; A fresh bounded call intentionally stops. Do not continue it, do not
      ;; reset its control fields, and do not release owners via an older World.
      (let [entry (m/retain world (:environment f) 1)
            cause (try (finite-call (assoc (:session f) :fuel 1) entry construct
                                    [(:environment f) (ci-name world first-input)])
                       nil (catch Throwable cause cause))
            checkpoint (:checkpoint (ex-data cause))
            matched-session (:checkpoint-session (ex-data cause))]
        (t/is (instance? clojure.lang.ExceptionInfo cause))
        (t/is (= :paused (:status checkpoint)))
        (t/is (> (get-in checkpoint [:stats :steps]) (get-in entry [:stats :steps])))
        (t/is (identical? (:functions checkpoint) (:functions matched-session)))
        ;; Retire this deliberate terminal packet after scalar assertions. No
        ;; closed-Source borrower is left accessible in the shared observer.
        (reset! failure-escrow {:stage :intentional-fuel-failure-discarded
                               :steps (get-in checkpoint [:stats :steps])}))
      (when (= :jvm backend)
        (let [stats (lazy/summary (get-in f [:session :program]))]
          (t/is (pos? (:compiled stats)))
          (t/is (pos? @compiled-executions))
          (swap! observations conj {:kind :jvm-component-observer :compiled-executor-calls @compiled-executions
                                    :fallback-executor-calls @fallback-executions :cache stats :dataset (:kind dataset)})))
      (reset! failure-escrow {:stage :completed-scope-discarded})
      (reset! completed? true)
      (catch Throwable cause
        ;; Do not invalidate the latest canonical packet by closing its Source
        ;; under an unexpected failure; OS disposal owns final resource cleanup.
        (swap! failure-escrow assoc :cause cause :source source
               :source-lifecycle :open-until-process-disposal)
        (throw cause))
      (finally (when @completed? (.close source))))
    ;; This deliberately reads only after all execution/release is finished.
    (t/is (thrown? clojure.lang.ExceptionInfo (m/node world first-input)))))
(t/deftest actual-raw-native-fixtures-on-three-backends
  (t/is (= (get fixture-manifest "helperSourceSha256")
           (wire/sha256 (wire/read-file-bytes "lean/KernelCasesOnRaw.lean" 1048576))))
  (doseq [backend [:reference :mutable :jvm] dataset datasets]
    (let [start (System/nanoTime)]
      (when (= :jvm backend) (reset! compiled-executions 0) (reset! fallback-executions 0))
      (if (= :jvm backend)
        ;; Observe the actual normalized-program compiler boundary. Public raw
        ;; compilation revalidates options and is not called by lazy dispatch.
        ;; Same compiler/form/executors; only a bounded host count is added.
        (with-redefs [block/compile-runtime-block-prepared observe-compile] (exercise-backend! backend dataset))
        (exercise-backend! backend dataset))
      (swap! observations conj {:kind :backend-complete :backend backend :dataset (:kind dataset)
                                :elapsed-ms (/ (- (System/nanoTime) start) 1e6)}))))
