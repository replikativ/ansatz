(ns ansatz.research.ir.bootstrap.policies
  "Explicit source-authenticated Source4 policy configuration. No engine/image,
   source receipt, handler authority, guest call or initializer is created here."
  (:require [clojure.java.io :as io] [clojure.data.json :as json]
            [java-ir-baseline :as j] [ansatz.research.ir.catalogue :as cat]
            [ansatz.research.ir.source-setup :as source]
            [ansatz.research.ir.composite-source-v4 :as composite]
            [ansatz.research.ir.authenticated-demand :as demand]
            [allocation-heartbeat-lab-v1 :as heartbeat]
            [java-prelude-no-native-init :as native-init])
  (:import [java.util WeakHashMap] [java.security MessageDigest]))

(def ^:private data-root (io/file (.getParentFile (io/file *file*)) "data/policies"))
(def ^:private index-sha "9a31d3ebfe00bd2ae7ad71cb78cc50db86d1817d8444b54b2edb9e7ac26112c8")
(def index-pin "74d833d577923821b982e8a9e872a38b5cad011513eb18870b51417e13397f0e")
(deftype Policies [])
(defonce ^:private bundles (WeakHashMap.))
(defn- need [ok text] (when-not ok (throw (ex-info text {:profile :source4-bootstrap-policies-v1}))))
(defn- field [x k] (.get (doto (.getDeclaredField (class x) k) (.setAccessible true)) x))
(defn- digest [^bytes bytes]
  (apply str (map #(format "%02x" (bit-and 255 %)) (.digest (MessageDigest/getInstance "SHA-256") bytes))))
(defn- checked-json [file sha bound] (source/checked-json file sha bound))
(defn requirements
  "Plain metadata for an artifact pack. This does not issue any capability.
   Optional INDEX-FILE must have the exact reviewed package index bytes."
  ([] (requirements (io/file data-root "policy-index.json")))
  ([index-file] (checked-json index-file index-sha 131072)))
(defn- family-files! [directory expected]
  (let [dir (io/file directory) actual (.listFiles dir)]
    (need (and (.isDirectory dir) (not (java.nio.file.Files/isSymbolicLink (.toPath dir))) actual
               (= (set (keys expected)) (set (map #(.getName ^java.io.File %) actual))))
          "Policy fixture directory must contain exactly the declared files")
    (into {} (for [[name evidence] expected
                   :let [f (io/file dir name) path (.toPath f)]]
               (do (need (and (= name (.getName f)) (not (java.nio.file.Files/isSymbolicLink path))
                              (.isFile f) (= (get evidence "bytes") (.length f))) "Policy fixture file/size differs")
                   [name (checked-json f (get evidence "sha256") (* 2 1024 1024))])))))
(defn- header-row [row]
  (let [ir (get row "ir") [kind declaration] (first ir)]
    (need (and (= 1 (count ir)) (contains? #{"extern" "fdecl"} kind)) "Unsupported policy declaration")
    (assoc (dissoc row "pretty") "ir" {kind (dissoc declaration "body")})))
(defn- authenticate-record! [catalogue record]
  (let [expected (get record "header-row") name (get expected "name")
        entry (cat/lookup catalogue name)]
    (need (and entry (= (get record "sha256") (:sha256 entry))
               (= expected (header-row (:row entry)))
               (= (get record "label") (source/label name)))
          "Policy compact Header differs from complete original catalogue/CAS row")
    record))
(defn authenticate-policies!
  "All inputs explicit: {:catalogue actual-catalogue :fixtures {policy-id File}
   :lean-source {:commit pinned-commit :read-blob! relative-path->byte[]}}.
   Directory IDs/file sets come from requirements. No SourceBinding is minted."
  [{:keys [catalogue fixtures lean-source index-file]}]
  (let [index (requirements (or index-file (io/file data-root "policy-index.json")))
        token (cat/source-token catalogue) families (get index "families")
        _ (need (= index-pin (:source-index-sha256 token) (get index "indexSHA256")) "Policy original index differs")
        _ (need (and (= source/lean-pin (:commit lean-source) (get index "leanCommit"))
                     (fn? (:read-blob! lean-source)) (= (set (keys families)) (set (keys fixtures))))
                "Explicit complete fixture directories and pinned source reader required")
        source-proofs (into {} (for [[path expected] (get index "sourceFiles")
                                    :let [bytes ((:read-blob! lean-source) path)]]
                                (do (need (and (= (class (byte-array 0)) (class bytes))
                                               (<= (alength ^bytes bytes) (* 4 1024 1024)) (= expected (digest bytes)))
                                          "Pinned upstream source blob differs") [path expected])))
        accepted (into {} (for [[id spec] families
                               :let [files (family-files! (get fixtures id) (get spec "files"))
                                     manifest (get files "manifest.json") records (get files "header-projections.json")]]
                           (do
                             (when manifest
                               (need (and (= (get spec "schema") (get manifest "schema"))
                                          (= source/lean-pin (get manifest "lean-commit"))
                                          (= index-pin (get manifest "source-index-sha256"))
                                          (= (get spec "headerCount") (count records) (get manifest "header-record-count")))
                                     "Policy manifest schema/source/count differs"))
                             (doseq [record records] (authenticate-record! catalogue record))
                             [id {:manifest manifest :records records :files files}])))]
    ;; Recheck the actual open catalogue lease after all independent metadata IO.
    (cat/source-token catalogue)
    (let [bundle (Policies.)]
      (locking bundles (.put bundles bundle {:catalogue catalogue :index index :families accepted :source-proofs source-proofs}))
      bundle)))
(defn- bundle! [bundle catalogue]
  (let [b (locking bundles (or (.get bundles bundle) (throw (ex-info "Actual authenticated policy bundle required" {}))))]
    (need (identical? catalogue (:catalogue b)) "Foreign policy catalogue")
    (need (= index-pin (:source-index-sha256 (cat/source-token catalogue))) "Policy catalogue changed") b))
(defn description [bundle]
  (let [b (locking bundles (.get bundles bundle))]
    (need b "Actual authenticated policy bundle required")
    (bundle! bundle (:catalogue b))
    {:schema :source4-policy-bundle-v1 :index-sha256 index-sha :original-index-sha256 index-pin
     :source-proofs (:source-proofs b) :fixtures (get-in b [:index "families"])
     :runtime-state-requirements (into {} (for [[id f] (:families b) :when (:manifest f)] [id (:manifest f)]))
     :guest-work 0 :runtime-state-admission false}))
(defn close!
  "Drop only policy metadata. Already configured engine policies and the caller's
   catalogue/source/guest owners remain with their actual lifecycle controllers."
  [bundle]
  (locking bundles (.remove bundles bundle)) nil)

(defn- wire-name [parts]
  (reduce (fn [p x] [(if (integer? x) "num" "str") p (if (integer? x) (str x) x)]) ["anonymous"] parts))
(def profiler-name (wire-name ["_private" "Lean" "Util" "Profile" 0 "Lean" "get_profiler" "_boxed"]))
(def profiler-sha "697f802be49ca83e350147ca7a564a73e3162beb454ca78d2990455df96796ed")
(def native-init-name (wire-name ["_private" "Lean" "Compiler" "InitAttr" 0 "Lean" "runModInitCore"]))
(defn- entry! [receipt name]
  (or (source/lookup-entry receipt name) (throw (ex-info "Policy declaration absent from authenticated receipt" {:name name}))))
(defn- canonical! [receipt driver record]
  (source/guard-source! receipt (:source driver))
  (let [expected (get record "header-row") name (get expected "name") entry (entry! receipt name)
        key (demand/exact-name-key name) memo (:headers-by-name driver)]
    (need (and (= (get record "sha256") (:sha256 entry)) (= expected (header-row (:row entry))))
          "Policy receipt Header projection differs")
    (locking memo
      (let [old (get @memo key) header (demand/ensure-header! driver name)]
        (when old (need (= (:sha256 old) (:sha256 entry)) "Policy canonical Header memo SHA differs"))
        (source/authenticate-canonical-header! (:source driver) (:row entry) (:sha256 entry) header)
        (swap! memo assoc key {:header header :sha256 (:sha256 entry)})
        (source/guard-source! receipt (:source driver)) header))))
(defn- direct-header! [receipt driver name]
  (let [entry (entry! receipt name)]
    (canonical! receipt driver {"label" (source/label name) "sha256" (:sha256 entry) "header-row" (header-row (:row entry))})))

(defn setup-evidence!
  "Authenticate the fixed base setup evidence; returns setup metadata only.
   Four-overlay composition and observer/source extensions belong to Source4."
  [catalogue {:keys [policies]}]
  (let [b (bundle! policies catalogue) files (get-in b [:families "setup" :files])
        aliases (get files "required-guest-exports.json") originals (get files "original-rows.json")
        original-map (into {} (map (fn [x] [(get x "label") x]) originals))]
    (need (and (= 3 (count aliases)) (= 13 (count originals))) "Fixed setup evidence count differs")
    (doseq [original originals]
      (let [entry (cat/lookup catalogue (get-in original ["row" "name"]))]
        (need (and entry (= (:sha256 entry) (get original "sha256")) (= (dissoc (:row entry) "pretty") (get original "row")))
              "Original13 setup raw row differs from catalogue")))
    {:evidence-pins {"original13_sha256" "ac2427476c6bfd38c30715dc32cc2bbeaf99f4253766259a44f063437f2ebdb8"
                     "required_guest_exports_sha256" "7c32ed7a16265b43d6cef8de549cc3550d1de39c53a0047be650b2509bdb20f4"}
     :helpers composite/helpers :aliases aliases
     :checked (mapv (fn [label]
                      (let [entry (get original-map label)]
                        {"name" (get-in entry ["row" "name"]) "sha256" (get entry "sha256")}))
                    ["Lean.Kernel.Environment.addDeclCore" "_private.Lean.Environment.0.Lean.Environment.addDeclCheck"])
     :host-symbols ["lean_add_decl" "lean_elab_add_decl"]}))
(defn prepare-import-context
  "Pre-engine base policies only. Source4 extends this result before capturing
   its one HostGuest policy; no returned configure-engine! hook is invoked here."
  [ctx src existing {:keys [receipt catalogue policies]}]
  (bundle! policies catalogue) (source/guard-source! receipt src)
  (let [get-spec (get heartbeat/specifications heartbeat/get-symbol)
        hb (entry! receipt (:name get-spec)) profiler (entry! receipt profiler-name)
        _ (need (= (:sha get-spec) (:sha256 hb)) "Wrong heartbeat getter source")
        _ (need (= profiler-sha (:sha256 profiler)) "Wrong profiler getter source")
        header! (fn [entry]
                  (let [h (or (get existing (:sha256 entry)) (j/declaration-header src (:row entry) (:sha256 entry)))]
                    (source/authenticate-canonical-header! src (:row entry) (:sha256 entry) h) h))
        hh (header! hb) ph (header! profiler)
        registered (j/register-headers ctx [hh ph] [(select-keys get-spec [:symbol :parameters :borrowed :result])])
        disabled (j/require-disabled-profiling registered ph)
        configured (source/configure-context receipt catalogue (assoc registered :profiling-policy disabled) src
                     (assoc existing (:sha256 hb) hh (:sha256 profiler) ph))]
    configured))
(def configure-context prepare-import-context)

(defn- layout-patterns [row]
  (loop [todo [(get row "ir")] constructors [] projections [] visits 0]
    (need (< visits 100000) "Bounded original layout traversal")
    (if (empty? todo) {"constructors" constructors "projections" projections}
      (let [x (peek todo) tail (pop todo)]
        (cond
          (vector? x) (recur (into tail (rseq x)) constructors projections (inc visits))
          (map? x) (recur (into tail (reverse (vals x)))
                         (if (contains? x "ctor") (conj constructors (get-in x ["ctor" "i"])) constructors)
                         (if (contains? x "proj") (conj projections (get-in x ["proj" "i"])) projections) (inc visits))
          :else (recur tail constructors projections (inc visits)))))))
(defn- check-driver! [driver receipt catalogue]
  (source/guard-source! receipt (:source driver))
  (need (identical? catalogue (:catalogue driver)) "Policy driver catalogue differs")
  (let [c @(:current-ctx driver) e (:engine driver)]
    (need (and (identical? (:class c) (class e)) (identical? (:program c) (field e "program"))
               (= "idle" (j/phase c e)) (zero? (j/instructions c e)))
          "Configure only a same-basis genuinely pristine idle parent")
    (doseq [k ["closed" "disposed" "untrackedFailure" "advancing"]]
      (need (false? (field e k)) "Policy engine lifecycle differs")) c))
(defn- install! [driver receipt catalogue context]
  (check-driver! driver receipt catalogue)
  (j/install-program! context (:engine driver))
  ;; This records the actual installation before any subsequent once-only
  ;; configuration can fail. No rollback of published metadata is promised.
  (reset! (:current-ctx driver) context)
  (check-driver! driver receipt catalogue) context)
(defn- pairs-for [family]
  (or (get-in family [:files "pairs.json"]) (get-in family [:manifest "pairs"]) []))
(defn- pair-labels [pair]
  (if (vector? pair) pair [(get-in pair ["origin" "label"]) (get-in pair ["target" "label"])]))
(defn reservation-origins
  "Authenticated compact ORIGINAL origin rows plus conservative overlay-symbol
   reservations. No Header, engine, Program or guest binding authority escapes."
  [policies catalogue]
  (let [b (bundle! policies catalogue)
        origins (for [[_ family] (:families b) pair (pairs-for family)
                      :let [[origin _] (pair-labels pair)
                            records (into {} (map #(vector (get % "label") %) (:records family)))]]
                  (or (get records origin) (throw (ex-info "Missing policy origin Header record" {:origin origin}))))]
    {:original-origins (vec (vals (into {} (map #(vector (get % "sha256") %) origins))))
     :overlay-symbols (set (map #(get % "symbol") (get-in b [:families "setup" :files "required-guest-exports.json"])))
     :policy-pins (into {} (for [[id spec] (get-in b [:index "families"])]
                               [(str "policy/" id) (or (get-in spec ["files" "manifest.json" "sha256"])
                                                       (get spec "historicalConfiguratorSHA256"))]))}))
(defn- bind-family! [driver receipt catalogue family headers]
  (let [before (check-driver! driver receipt catalogue)
        by-label (into {} (map #(vector (get % "label") %) (:records family)))
        bindings (mapv (fn [pair]
                         (mapv (fn [label]
                                 (let [record (get by-label label) header (get headers (get record "sha256"))]
                                   (need (and record header) "Policy pair is missing its canonical Header")
                                   (when (map? pair)
                                     (let [side (if (= label (get-in pair ["origin" "label"])) "origin" "target")]
                                       (need (and (= (get record "sha256") (get-in pair [side "sha256"]))
                                                  (= (get-in record ["header-row" "name"]) (get-in pair [side "name"])))
                                             "Policy pair Name/SHA differs"))) header)) (pair-labels pair)))
                       (pairs-for family))
        registered (j/register-headers before (mapv #(get headers (get % "sha256")) (:records family)))
        bound (j/bind-guest-exports registered bindings)]
    (install! driver receipt catalogue bound)
    {:bindings (count bindings) :canonical-headers (count (:records family)) :guest-work 0}))
(defn audit-meta-bindings!
  "Inspect the actual Program mapping, never a caller's already-bound claim."
  [driver policies receipt catalogue]
  (let [b (bundle! policies catalogue) c (check-driver! driver receipt catalogue)
        pairs (into [["Lean.Meta.whnf" "Lean.Meta.whnfImp"] ["Lean.Meta.inferType" "Lean.Meta.inferTypeImp"]]
                    (get-in b [:families "meta" :manifest "pairs"]))
        functions ^objects (field (:program c) "functions") exports ^objects (field (:program c) "guestExports")]
    (need (= 21 (count pairs)) "Full Meta21 source policy differs")
    (doseq [[origin target] pairs]
      (need (identical? (aget exports (j/function-id c origin)) (aget functions (j/function-id c target)))
            "Required actual Meta guest-export mapping differs"))
    {:required-bindings 21 :actual-program-bindings-verified true :guest-work 0}))
(defn- configure-level! [driver receipt catalogue headers]
  (let [before (check-driver! driver receipt catalogue)
        policy-class (Class/forName "ansatz.lean.jvm.internal.exec.Interpreter$LevelInstantiationPolicy" true (:loader before))
        header-class (class (first headers))
        policy (j/invoke-static (.getMethod policy-class "originalHelpers" (into-array Class (repeat 5 header-class))) headers)
        registered (j/register-headers before headers)]
    (install! driver receipt catalogue registered)
    (.invoke (.getMethod (class (:engine driver)) "configureLevelInstantiation" (into-array Class [policy-class]))
             (:engine driver) (object-array [policy]))
    (check-driver! driver receipt catalogue)
    {:helper-headers 5 :guest-work 0}))
(defn- configure-transform! [driver receipt catalogue headers]
  (let [before (check-driver! driver receipt catalogue)
        policy (j/expr-transform-policy before (subvec headers 0 9))
        registered (j/register-headers before headers)]
    (install! driver receipt catalogue registered)
    (j/configure-expr-transforms! registered (:engine driver) policy)
    (check-driver! driver receipt catalogue)
    {:helper-headers 21 :guest-work 0}))
(defn- configure-full-expr! [driver receipt catalogue family headers]
  (let [before (check-driver! driver receipt catalogue) manifest (:manifest family)
        proof (get-in family [:files "closure-proof.json"])
        _ (need (= [113 0 [] [] 0 0 true] (mapv proof ["rows" "pending" "missing" "initialized-declarations"
                                                     "new-required-global-roots" "new-heap-roots" "resolved"]))
                "Original Expr hidden static closure differs")
        _ (need (false? (get proof "state-admission-performed")) "Metadata cannot assert state admission")
        _ (doseq [e (get-in family [:files "layout-evidence.json"])]
            (let [entry (entry! receipt (get e "name"))]
              (need (and (= (:sha256 entry) (get e "sha256")) (= (get e "patterns") (layout-patterns (:row entry))))
                    "Original Expr layout evidence differs")))
        level (field (:engine driver) "levelInstantiationPolicy")
        _ (need (and level (= 5 (count (vec (field level "helpers"))))) "Actual original Level policy absent")
        _ (need (every? true? (map identical? (vec (field level "helpers")) (subvec headers 0 5)))
                "Actual Level policy uses different canonical Headers")
        _ (need (= [5 5 9] (mapv #(count (get manifest %)) ["level-helper-order" "expr-helper-order" "constructor-helper-order"]))
                "Original Expr helper tuple differs")
        policy (j/expr-instantiation-policy before level (subvec headers 5 10) (subvec headers 10 19))
        registered (j/register-headers before headers)]
    (install! driver receipt catalogue registered)
    (j/configure-expr-instantiation! registered (:engine driver) policy)
    (check-driver! driver receipt catalogue)
    {:helper-headers 21 :hidden-roles 19 :static-closure-rows 113 :runtime-state-admission false :guest-work 0}))
(defn- configure-pointers! [driver receipt catalogue family headers]
  (let [before (check-driver! driver receipt catalogue)
        by-sha (zipmap (map #(get % "sha256") (:records family)) headers)
        roles (mapv by-sha (get-in family [:manifest "role-hashes"]))
        _ (need (and (= 3 (count roles)) (every? some? roles)) "Original pointer role tuple differs")
        policy (j/pointer-hash-policy before roles) registered (j/register-headers before headers)]
    (install! driver receipt catalogue registered)
    (j/configure-pointer-hashes! registered (:engine driver) policy)
    (check-driver! driver receipt catalogue)
    {:hash-role-records 3 :guest-work 0}))
(defn configure!
  "Configure one freshly imported, pristine idle parent. All compact Headers are
   authenticated before Program/policy publication. Journal is caller-owned and
   prepublished; failure preserves actual installed context, never pretends rollback.
   Opts {:receipt :catalogue :policies :journal optional}. DRIVER must already
   have its actual authenticated demand policy; it is never replaced or reattached.
   Actual captured-state admission is the importer's separate prerequisite."
  [driver {:keys [receipt catalogue policies journal] :or {journal (atom {})}}]
  (let [b (bundle! policies catalogue) initial (check-driver! driver receipt catalogue)
        _ (need (instance? clojure.lang.IAtom journal) "Actual policy construction journal atom required")
        _ (swap! journal assoc :status :authenticating :driver driver :completed {})
        families (:families b)
        all-records (vals (into {} (for [[_ family] families record (:records family)] [(get record "sha256") record])))
        headers (into {} (map #(vector (get % "sha256") (canonical! receipt driver %)) all-records))
        ordered (fn [id] (mapv #(get headers (get % "sha256")) (get-in families [id :records])))
        completed (atom {})
        step! (fn [id f]
                (swap! journal assoc :status :configuring :stage id :driver driver :completed @completed)
                (let [value (f)] (swap! completed assoc id value) (swap! journal assoc :completed @completed) value))]
    (need (instance? clojure.lang.IAtom journal) "Actual policy construction journal atom required")
    (try
      (step! :meta #(bind-family! driver receipt catalogue (get families "meta") headers))
      (step! :level #(configure-level! driver receipt catalogue (ordered "level")))
      (step! :share-common #(do (j/configure-share-common! @(:current-ctx driver) (:engine driver)
                                 (j/jvm-carrier-layout-v1 @(:current-ctx driver))) {:guest-work 0}))
      (step! :expr-transform #(configure-transform! driver receipt catalogue (ordered "expr-transform")))
      (step! :expr-instantiation #(configure-full-expr! driver receipt catalogue (get families "expr-instantiation") (ordered "expr-instantiation")))
      (step! :pointer-hash #(configure-pointers! driver receipt catalogue (get families "pointer-hash") (ordered "pointer-hash")))
      (doseq [id ["compiler" "string" "finalizer" "substring" "meta-whnf"]]
        (step! (keyword id) #(bind-family! driver receipt catalogue (get families id) headers)))
      (step! :actual-meta-audit #(audit-meta-bindings! driver policies receipt catalogue))
      (let [header (direct-header! receipt driver native-init-name)
            cap (step! :native-init #(native-init/configure @(:current-ctx driver) header))
            _ (install! driver receipt catalogue (:ctx cap))]
        (check-driver! driver receipt catalogue)
        (swap! journal assoc :status :ready :stage :ready :driver driver :native-init cap)
        {:driver driver :native-init cap :receipts @completed :journal journal
         :guest-work 0 :runtime-state-admission false})
      (catch Throwable error
        (swap! journal assoc :status :failed :failure-class (.getName (class error)))
        (throw (ex-info "Source4 policy configuration failed; retain actual journal/context" {:journal journal} error))))))
