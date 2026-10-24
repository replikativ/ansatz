(ns ansatz.wf-supplement-test
  "Strict preparation models use real raw parsing, bounded assembly and kernel
   replay. Toy declarations do not model actual Prod.Lex frontend semantics."
  (:require [clojure.test :refer [deftest is]]
            [clojure.data.json :as json]
            [clojure.java.io :as io]
            [ansatz.bundle :as bundle]
            [ansatz.core :as core]
            [ansatz.bundle-test :as bundle-fixtures]
            [ansatz.wf-supplement :as supplement]
            [ansatz.export.role-input :as input]
            [ansatz.export.parser :as parser]
            [ansatz.export.replay :as replay]
            [ansatz.export.storage :as storage]
            [org.replikativ.persistent-sorted-set :as pss]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [ansatz.session :as session])
  (:import [ansatz.kernel ConstantInfo ExprStore Env]
           [java.io ByteArrayOutputStream]
           [java.nio.charset StandardCharsets]
           [java.security MessageDigest]
           [java.util.zip GZIPOutputStream]
           [java.util ArrayList]))

(def input-limits {:inflated-bytes 1048576 :records 10000 :record-chars 8192
                   :name-index 2048 :level-index 256 :expr-index 8192
                   :level-work 1000000 :companion-rows 5000})
(def evidence-limits {:declarations 256 :shell-items 65536 :expr-nodes 8192 :expr-edges 16384 :expr-depth 128
                      :raw-bytes 1048576 :name-nodes 2048 :name-chars 65536 :name-depth 64
                      :level-nodes 256 :level-depth 64 :level-visits 1000000})
(def comparison-limits {:pairs 30000 :edges 300000 :scalar-bytes 1048576 :items 300000 :depth 256})
(def overlay-limits {:rows 5000 :items 100000 :scalar-bytes 1048576 :base-items 100000 :simp-names 5000})

(defn gzip [text]
  (let [output (ByteArrayOutputStream.)]
    (with-open [stream (GZIPOutputStream. output)] (.write stream (.getBytes ^String text StandardCharsets/UTF_8)))
    (.toByteArray output)))
(defn sha [payload]
  (apply str (map #(format "%02x" (bit-and 255 %)) (.digest (MessageDigest/getInstance "SHA-256") payload))))
(defn error [f] (try (f) nil (catch Throwable cause cause)))
(defn context []
  (assoc (session/capture) :env (env/with-extension (Env.) :instances {}) :instance-index {}
         :synth-cache (atom {}) :store nil :recall-store-path nil :discr-trie nil :simp-trie nil
         :instance-caches {} :simp-index-caches nil :simp-caches {:env nil :entries {}}))
(defn options [fixture]
  {:bundle-options {:manifest (:manifest fixture) :read-resource (:resources fixture)}
   :input-limits input-limits :candidate-limits evidence-limits :store-evidence-limits evidence-limits
   :comparison-limits comparison-limits :overlay-limits overlay-limits})

(def toy-records
  [{:in 1 :str {:pre 0 :str "A"}}
   {:in 2 :str {:pre 0 :str "x"}}
   {:in 3 :str {:pre 0 :str "Prod"}}
   {:in 4 :str {:pre 3 :str "Lex"}}
   {:in 5 :str {:pre 4 :str "right'"}}
   {:in 6 :str {:pre 0 :str "P"}}
   {:in 7 :str {:pre 0 :str "Evidence"}}
   {:in 8 :str {:pre 7 :str "thm"}}
   {:il 1 :succ 0}
   {:ie 0 :sort 1}
   {:axiom {:name 1 :levelParams [] :type 0 :isUnsafe false}}
   {:ie 1 :const {:name 1 :us []}}
   {:axiom {:name 2 :levelParams [] :type 1 :isUnsafe false}}
   {:ie 2 :const {:name 2 :us []}}
   {:def {:name 5 :levelParams [] :type 1 :value 2 :hints {:regular 0} :safety "safe" :all [5]}}
   {:ie 3 :sort 0}
   {:ie 4 :bvar 0}
   {:ie 5 :bvar 1}
   {:ie 6 :forallE {:name 0 :type 4 :body 5 :binderInfo "default"}}
   {:ie 7 :forallE {:name 6 :type 3 :body 6 :binderInfo "default"}}
   {:ie 8 :lam {:name 0 :type 4 :body 4 :binderInfo "default"}}
   {:ie 9 :lam {:name 6 :type 3 :body 8 :binderInfo "default"}}
   {:thm {:name 8 :levelParams [] :type 7 :value 9 :all [8]}}])

(defn toy-text [producer records]
  (str (json/write-str {:meta producer}) "\n" (apply str (map #(str (json/write-str %) "\n") records))))
(defn fixture
  ([] (fixture toy-records [{:kind "unfold" :name "Prod.Lex.right'"}]))
  ([records attrs]
   (let [{:keys [generation producer resources]} (bundle-fixtures/generated-fixture)
         resources (assoc resources (get bundle/role-resources :lex) (gzip (toy-text producer records))
                          (get bundle/role-resources :attrs) (gzip (apply str (map #(str (json/write-str %) "\n") attrs))))
         generation (assoc-in generation [:roots :lex] ["Prod.Lex.right'"])
         rows (mapv (fn [[role resource]] {:role role :resource resource :sha256 (sha (get resources resource))}) bundle/role-resources)]
     {:producer producer :resources resources :manifest (bundle/generated-manifest generation producer rows)})))

(deftest strict-preparation-is-unactivated-and-rechecks-existing-complete-declarations
  (let [before (session/capture) captured (context) selected (fixture)
        first (supplement/prepare-strict-role captured :lex (options selected))
        second (supplement/prepare-strict-role first :lex (options selected))]
    (is (instance? ansatz.core.ProofContext first))
    (is (some? (env/lookup (:env first) (name/from-string "Prod.Lex.right'"))))
    (is (contains? (env/get-extension (:env first) :simp-unfold #{}) "Prod.Lex.right'"))
    (is (identical? (:env before) (:env (session/capture))))
    (is (= 1 (count (:supplements (env/get-extension (:env second) :artifact-profile nil)))))
    (is (= {} @(:synth-cache second)))))

(deftest strict-preparation-refuses-legacy-before-candidate-parsing
  (let [captured (context) request (assoc (options (fixture)) :bundle-options {})]
    (with-redefs [parser/parse-ndjson-string-raw (fn [& _] (throw (AssertionError. "legacy must refuse before parse")))]
      (is (= :unsupported-legacy-evidence
             (:reason (ex-data (error #(supplement/prepare-strict-role captured :lex request)))))))))

(deftest exact-overlap-rejects-local-hint-drift-and-omitted-local-proof
  (let [selected (fixture) prepared (supplement/prepare-strict-role (context) :lex (options selected))
        original (env/lookup (:env prepared) (name/from-string "Prod.Lex.right'"))
        changed (env/mk-def (.name ^ConstantInfo original) [] (.type ^ConstantInfo original)
                            (.value ^ConstantInfo original) :hints :abbrev)
        drift (assoc prepared :env (.addOrReplaceConstant ^Env (:env prepared) changed))
        theorem (env/lookup (:env prepared) (name/from-string "Evidence.thm"))
        missing (ConstantInfo/mkThm (.name ^ConstantInfo theorem) (object-array []) (.type ^ConstantInfo theorem)
                                    nil (object-array [(.name ^ConstantInfo theorem)]))
        omitted (assoc prepared :env (.addOrReplaceConstant ^Env (:env prepared) missing))]
    (is (= :overlap (:stage (ex-data (error #(supplement/prepare-strict-role drift :lex (options selected)))))))
    (is (some? (error #(supplement/prepare-strict-role omitted :lex (options selected)))))))

(deftest metadata-closure-and-input-bounds-fail-without-replay-or-global-mutation
  (let [before (session/capture) captured (context)
        bad (fixture toy-records [{:kind "impl" :name "Prod.Lex.right'" :target "missing"}])
        selected (fixture)]
    (with-redefs [replay/replay-from-env (fn [& _] (throw (AssertionError. "must reject before replay")))]
      (is (= :metadata-closure (:stage (ex-data (error #(supplement/prepare-strict-role captured :lex (options bad)))))))
      (is (some? (error #(supplement/prepare-strict-role captured :lex
                                                         (assoc-in (options selected) [:input-limits :expr-index] 1))))))
    (is (identical? (:env before) (:env (session/capture))))))

(deftest original-ordinary-package-closure-is-checked-against-real-lex-payload
  ;; Exercise the actual bundled atomic records, independent of its explicitly
  ;; legacy provenance. No strict activation is claimed for schema-1 bytes.
  (let [payload (bundle/classpath-bytes (get bundle/role-resources :lex))]
    (input/with-candidate
      payload input-limits evidence-limits
      (fn [candidate]
        (let [packages (#'supplement/packages! candidate)]
          (is (= 19 (count packages)))
          (is (every? #(= :inductive (:kind %)) packages))
          (let [group (first (:inductive-groups candidate))
                missing-rec (update-in candidate [:inductive-groups 0] #(-> % (update :end dec) (assoc :recursor-count 0)))
                nested (update-in candidate [:decls (:start group)] identity)]
            (is (some? (error #(#'supplement/packages! missing-rec))))
            ;; A detached header model tests the explicit nested refusal without
            ;; mutating any actual candidate CI retained by the positive check.
            (let [old (nth (:decls nested) (:start group))
                  head (env/mk-induct (.name ^ConstantInfo old) (vec (.levelParams ^ConstantInfo old)) (.type ^ConstantInfo old)
                                      :num-nested 1 :all (vec (.all ^ConstantInfo old)) :ctors (vec (.ctors ^ConstantInfo old)))
                  nested (assoc-in nested [:decls (:start group)] head)]
              (is (= :unsupported-nested-package (:reason (ex-data (error #(#'supplement/packages! nested)))))))))))))

(deftest mixed-presence-packages-are-refused-before-replay
  (input/with-candidate
    (bundle/classpath-bytes (get bundle/role-resources :lex)) input-limits evidence-limits
    (fn [{:keys [decls] :as candidate}]
      (let [packages (#'supplement/packages! candidate)
            first-name (first (:names (first packages)))
            first-ci (first (filter #(= first-name (.name ^ConstantInfo %)) decls))
            base (.addConstant (Env.) first-ci)]
        (is (= :unsupported-partial-package
               (:reason (ex-data (error #(#'supplement/overlap-and-missing base decls packages
                                                                           evidence-limits comparison-limits))))))))))

(deftest parser-store-closes-before-success-and-on-original-or-close-failure
  (let [selected (fixture) payload (get (:resources selected) (get bundle/role-resources :lex))
        opened (atom nil) actual parser/mk-parser-state
        original (ex-info "original callback failed" {}) cleanup (ex-info "cleanup failed" {})
        actual-close @#'input/close-store!]
    (with-redefs [parser/mk-parser-state (fn [] (let [state (actual)] (reset! opened (:exprs state)) state))]
      (is (= :result (input/with-candidate payload input-limits evidence-limits (constantly :result))))
      (is (some? (error #(.readRaw ^ExprStore @opened 0))))
      (with-redefs-fn {#'input/close-store! (fn [store] (actual-close store) (throw cleanup))}
        (fn []
          (let [observed (error #(input/with-candidate payload input-limits evidence-limits (fn [_] (throw original))))]
            (is (identical? original observed))
            (is (some #(identical? cleanup %) (.getSuppressed ^Throwable observed))))
          (is (identical? cleanup
                          (error #(input/with-candidate payload input-limits evidence-limits (constantly :must-not-return))))))))))

(deftest standalone-kernel-dependency-closure-is-not-substituted-by-base-availability
  (let [records (filterv #(not (and (:axiom %) (= 1 (get-in % [:axiom :name])))) toy-records)
        selected (fixture records [])]
    (is (= :kernel-closure
           (:stage (ex-data (error #(supplement/prepare-strict-role (context) :lex (options selected)))))))))

(deftest defs-only-captured-pss-overlap-has-full-proof-without-following-new-head
  (let [selected (fixture)
        parsed (parser/parse-ndjson-string-raw (toy-text (:producer selected) toy-records))
        theorem-name (name/from-string "Evidence.thm")
        theorem-shell (first (filter #(= theorem-name (:name %)) (:decls parsed)))
        tree (fn [cmp entries] (into (pss/sorted-set* {:cmp cmp}) entries))
        trees (try
                {:old-env (tree storage/name-cmp [[theorem-name theorem-shell]])
                 :old-exprs (tree storage/id-cmp (mapv (fn [id] [id (.readRaw ^ExprStore (:exprs parsed) id)]) (range 10)))
                 :old-names (tree storage/id-cmp (mapv (fn [id] [id (.get ^ArrayList (:names parsed) id)]) (range 9)))
                 :old-levels (tree storage/id-cmp (mapv (fn [id] [id (.get ^ArrayList (:levels parsed) id)]) (range 2)))}
                (finally (.close ^ExprStore (:exprs parsed))))
        head (atom {:env-root :old-env :exprs-root :old-exprs :names-root :old-names
                    :levels-root :old-levels :dag-storage? true :env-count 1})
        reads (atom []) normal-reads (atom []) dag-reads (atom 0)
        actual-lookup pss/lookup]
    ;; Real captured PSS roots and resolvers; only backend IO is modeled.
    (with-redefs [pss/lookup (fn [tree key]
                               (when (some #(identical? tree (get trees %)) [:old-exprs :old-names :old-levels])
                                 (swap! dag-reads inc))
                               (actual-lookup tree key))
                  storage/store-get (fn [_ key] (swap! reads conj key) @head)
                  pss/restore-by (fn [_ root _] (or (get trees root) (throw (AssertionError. "new head must not be restored"))))
                  storage/open-store (fn [& _] (throw (AssertionError. "borrowed store must not open")))
                  storage/close-store (fn [& _] (throw (AssertionError. "borrowed store must not close")))]
      (let [store-map {:store :modeled-backend :storage :modeled-backend}
            loader (#'storage/branch-loader store-map "library" :value-policy :defs-only)
            lookup (:lookup-ci loader)
            loader (assoc loader :lookup-ci
                          (fn [name]
                            (let [before @dag-reads result (lookup name)]
                              (swap! normal-reads conj {:name name :dag-reads (- @dag-reads before)})
                              result)))
            loaded (storage/load-env store-map "library" :loader loader)
            thin (.lookup ^Env loaded theorem-name)
            descriptor {:store-map {:borrowed true} :store-path "captured" :branch "library"}
            captured (assoc (context) :env loaded :store descriptor :recall-store-path "captured")]
        (is (nil? (.value ^ConstantInfo thin)))
        (reset! head {:env-root :new-head})
        (reset! normal-reads [])
        (let [prepared (supplement/prepare-strict-role captured :lex (options selected))]
          (is (some? (.lookup ^Env (:env prepared) (name/from-string "Prod.Lex.right'"))))
          (is (identical? descriptor (:store prepared)))
          (is (identical? thin (.lookup ^Env loaded theorem-name)))
          (is (nil? (.value ^ConstantInfo thin)))
          ;; addConstant retains its duplicate guard: exactly one ordinary
          ;; name-tree miss per proved-absent declaration, without DAG hydration.
          (is (= #{"A" "x" "Prod.Lex.right'"} (set (map (comp str :name) @normal-reads))))
          (is (= 3 (count @normal-reads)))
          (is (every? #(zero? (:dag-reads %)) @normal-reads))
          (is (= [[:branches "library"]] @reads)))))))

(deftest replay-view-is-uncached-and-does-not-inherit-out-of-role-handlers-or-flags
  (let [looked-up? (atom false)
        original (.withExternalLookup (.enableQuot (Env.))
                                      (fn [_] (reset! looked-up? true) (throw (AssertionError. "foreign store lookup"))) 0)
        replayed (atom false)]
    (with-redefs [replay/replay-from-env
                  (fn [^Env view declarations & _]
                    (reset! replayed true)
                    (is (empty? declarations))
                    (is (false? (.isQuotEnabled view)))
                    (is (nil? (.lookup view (name/from-string "foreign"))))
                    {:env view :stats {:errors 0 :total 0}})]
      (is (identical? original (#'supplement/replay-isolated original {:missing [] :present {}} []))))
    (is @replayed)
    (is (false? @looked-up?))))

(deftest complete-new-quotient-package-controls-builtin-state-and-transplant
  (let [payload (gzip (slurp (io/resource "ansatz/export/fixtures/quotient-4.29.ndjson") :encoding "UTF-8"))
        limits (assoc input-limits :name-index 4096 :expr-index 16384)]
    (input/with-candidate payload limits evidence-limits
      (fn [{:keys [decls] :as candidate}]
        (let [packages (#'supplement/packages! candidate)
              original (Env.)
              checked (#'supplement/replay-isolated original {:missing decls :present {}} packages)]
          (is (false? (.isQuotEnabled original)))
          (is (.isQuotEnabled ^Env checked))
          (is (= (count decls) (count (.allConstants ^Env checked))))
          (is (some? (.lookup ^Env checked (name/from-string "Quot.ind")))))))))

(deftest escaped-declaration-names-cannot-masquerade-as-dotted-companion-roots
  (let [records (mapv (fn [record]
                        (if (= 5 (:in record)) {:in 5 :str {:pre 0 :str "Prod.Lex.right'"}} record)) toy-records)
        selected (fixture records [])]
    (is (= :unsupported-name-encoding
           (:reason (ex-data (error #(supplement/prepare-strict-role (context) :lex (options selected)))))))))

(deftest raw-constant-universes-require-an-explicit-array
  (let [records (mapv (fn [record]
                        (if (:const record) (update record :const dissoc :us) record)) toy-records)
        selected (fixture records [])]
    (is (re-find #"explicit array"
                 (ex-message (error #(supplement/prepare-strict-role (context) :lex (options selected))))))))

(deftest raw-fields-must-fit-the-actual-expression-store-widths
  (doseq [record [{:ie 20 :const {:name 1 :us (vec (repeat 65536 0))}}
                  {:ie 20 :natVal (str "1" (apply str (repeat 157824 "0")))}
                  {:ie 20 :natVal "-1"}]]
    (let [selected (fixture (conj toy-records record) [])
          options (assoc-in (options selected) [:input-limits :record-chars] 200000)]
      (with-redefs [replay/replay-from-env (fn [& _] (throw (AssertionError. "width check must precede replay")))]
        (is (re-find #"store format width"
                     (ex-message (error #(supplement/prepare-strict-role (context) :lex options)))))))))
