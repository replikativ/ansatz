(ns ansatz.import-test
  "The single importer (ansatz.import) and store format 1: an export in, a COMPLETE store out —
   manifest last, derived state as blobs, content-addressed roots — and `init!` on it, with
   simp served lazily from the store's index and recall from its keys."
  (:require [ansatz.test-env :as test-env]
            [ansatz.export.parser :as parser]
            [clojure.test :refer [deftest is testing]]
            [clojure.java.io :as io]
            [ansatz.core :as a]
            [ansatz.fixtures :as fixtures]
            [ansatz.import :as imp]
            [ansatz.store :as store]
            [ansatz.state :as state]
            [ansatz.simp-index :as si]
            [ansatz.catalogue.scalars :as scalars]
            [ansatz.session :as session]
            [ansatz.recall :as recall]
            [ansatz.discr-key-encoding :as ke]
            [ansatz.export.storage :as storage]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]
            [ansatz.tactic.simp :as simp]))

(def ^:dynamic *ndjson* nil)
(def ^:private declaration-count
  (delay
    (parser/with-parser-state
      (parser/parse-ndjson-string @test-env/bundled-init-text)
      #(count (:decls %)))))
(def ^:private attrs "resources/ansatz/init-attrs.ndjson.gz")

(defn- tmp-store [tag]
  (let [f (java.io.File/createTempFile (str "ansatz-import-" tag) "")]
    (.delete f) (.deleteOnExit f) (.getPath f)))

(defn- import-medium! [dir & {:as opts}]
  (imp/import! dir (merge {:ndjson *ndjson* :attrs attrs :branch "init"
                           :provenance {:lean/toolchain "test" :library/rev "init-medium"}
                           :verbose? false :parallelism 2}
                          opts)))

(def ^:private nat (e/const' (name/from-string "Nat") []))
(defn- nle [x y]
  (e/app* (e/const' (name/from-string "LE.le") [lvl/zero]) nat
          (e/const' (name/from-string "instLENat") []) x y))

(clojure.test/use-fixtures :once fixtures/isolated-session
  (fn [f]
    ;; The importer accepts a file path; materialize the shipped closure for it.
    (let [file (java.io.File/createTempFile "ansatz-bundled-init-" ".ndjson")]
      (try
        (spit file @test-env/bundled-init-text)
        (binding [*ndjson* (.getPath file)] (f))
        (finally (.delete file))))))

(deftest an-import-is-a-complete-store
  (let [dir (tmp-store "full")
        m (import-medium! dir)]
    (testing "the manifest is written last and describes the store"
      (is (= store/store-format (:store/format m)))
      (is (= m (store/read-manifest dir)))
      (is (= "init" (:branch m)))
      (is (= "test" (get-in m [:provenance :lean/toolchain])))
      (let [arts (:artifacts m)]
        (is (= @declaration-count (:declarations arts)))
        (is (= @declaration-count (:facts arts)) "one facts record per declaration")
        (is (> (:attrs arts) 100) "the inherited Init corpus, intersected")
        (is (pos? (:recall-keys arts)))
        (is (pos? (:simp-keys arts)))
        (is (pos? (:matchers arts)))
        (is (pos? (:instances arts)))))
    (testing "layout: only blobs under blobs/, everything else a sibling"
      (is (.isDirectory (io/file dir "blobs")))
      (is (.exists (io/file dir "manifest.edn")))
      (is (.exists (io/file dir "inputs" "init-attrs.ndjson.gz")) "inputs kept for regeneration")
      (is (every? #(.isFile ^java.io.File %) (.listFiles (io/file dir "blobs")))
          "no directory inside the konserve dir (its keys/GC walk every entry)"))
    (testing "init! on it: attributes, instances, matchers from the derived blobs"
      (binding [a/*verbose* false] (a/init! dir "init"))
      (is (= dir (:store-path @state/ansatz-store)))
      (is (contains? (env/get-extension (a/env) :simp-lemmas #{}) "Option.some.injEq")
          "the inherited @[simp] set came from the store")
      (is (pos? (count @a/ansatz-instance-index)))
      (is (some? (:store-path ((requiring-resolve 'ansatz.simp-index/index-source) (a/env))))
          "the env carries its simp-index source"))
    (testing "the catalogue consumes the actual persisted versioned simp artifact"
      (let [kstore (:store (:store-map @state/ansatz-store))
            artifact (storage/read-derived kstore "init" :simp-keys)
            entries (si/key-entries artifact)
            entities (scalars/scalar-entities {:simp-keys artifact})]
        (is (= si/write-key-encoding (:key-encoding artifact)))
        (is (= (set entries)
               (into #{} (mapcat (fn [entity]
                                   (map #(vector (:decl/name entity) (pr-str (:keys (ke/read-path %)))) (:decl/simp-key entity)))) entities)))))
    (testing "the importer versions recall keys and the catalogue preserves their encoding"
      (let [kstore (:store (:store-map @state/ansatz-store))
            artifact (storage/read-derived kstore "init" :recall-keys)
            entities (scalars/scalar-entities {:recall-keys artifact})]
        (is (= ke/write-version (ke/encoding artifact)))
        (is (seq (ke/entries artifact)))
        (is (= (set (ke/entries artifact))
               (into #{} (map (fn [entity]
                                [(:decl/name entity) (pr-str (:keys (ke/read-path (:decl/dt-key entity))))])) entities)))
        (is (every? #(= ke/write-version (ke/encoding (ke/read-path (:decl/dt-key %)))) entities))))
    (testing "simp resolves inherited rules LAZILY from the captured store trie"
      (is (nil? (si/capture-caches)) "no inherited rules resolved before the first simp")
      (binding [a/*verbose* false]
        (a/prove-theorem 'imp-opt-inj '[a :- Nat, b :- Nat]
                         '(= Prop (= (Option Nat) (Option.some a) (Option.some b)) (= Nat a b)) '[(simp)]))
      (is (some? (env/lookup (a/env) (name/from-string "imp-opt-inj"))))
      (is (seq (get-in (si/capture-caches) [:rules "Option.some.injEq"]))
          "the inherited injection rule was resolved on demand"))
    (testing "the facts blobs carry the statement's and the value's vocabulary"
      (let [sm (:store-map @state/ansatz-store)
            kstore (:store sm)
            n (storage/read-derived kstore "init" :facts-chunks)
            facts (into [] (mapcat #(storage/read-derived kstore "init" [:facts %])) (range n))
            by-name (into {} (map (juxt :name identity)) facts)
            f (by-name "Nat.add_comm")]
        (is (pos? n) "facts are chunked")
        (is (= @declaration-count (count facts)))
        (is (= :thm (:kind f)))
        (is (= "Eq" (:concl-head f)))
        (is (= 2 (:num-binders f)))
        (is (contains? (set (:mentions f)) "HAdd.hAdd") "the STATEMENT's constants")
        ;; Init/Data/Nat/Basic.lean add_comm elaborates through kernel recursion
        ;; and an auxiliary in the pinned Lean 4.33.1 export.
        (is (contains? (set (:depends-on f)) "Nat.brecOn") "the VALUE's constants")
        (is (not (contains? (set (:mentions f)) "Nat.brecOn")) "the dependency is value-only")
        (is (not-any? :depends-on (filter #(= :axiom (:kind %)) facts))
            "an axiom has no value, so no dependencies")))
    (testing "recall answers from the store's keys"
      (let [names (recall/recall-names (nle (e/lit-nat 0) (e/mvar 900001)))]
        (is (some #{"Nat.zero_le"} names))))))

(deftest the-same-export-gives-the-same-store
  (testing "content-addressed nodes: two imports of one export share every root"
    (let [a-dir (tmp-store "same-a") b-dir (tmp-store "same-b")
          _ (import-medium! a-dir :max-count 400)
          _ (import-medium! b-dir :max-count 400)
          open (requiring-resolve 'ansatz.export.storage/open-store)
          roots (fn [dir] (let [sm (open dir)
                                m ((requiring-resolve 'ansatz.export.storage/store-get) (:store sm) [:branches "init"])]
                            (select-keys m [:env-root :exprs-root :names-root :levels-root])))]
      (is (= (roots a-dir) (roots b-dir)))
      (is (every? some? (vals (roots a-dir)))))))

(deftest stores-without-the-format-are-refused
  (testing "no manifest → refused with a re-import message, never opened"
    (let [dir (tmp-store "nomanifest")]
      (.mkdirs (io/file dir "blobs"))
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"[Rr]e-import" (a/init! dir "init")))))
  (testing "another format → refused"
    (let [dir (tmp-store "oldformat")]
      (.mkdirs (io/file dir))
      (store/write-manifest! dir {:store/format 0})
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"format 0" (a/init! dir "init")))))
  (testing "an import refuses to overwrite a finished store"
    (let [dir (tmp-store "exists")]
      (.mkdirs (io/file dir))
      (store/write-manifest! dir {:store/format store/store-format})
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"already exists" (import-medium! dir))))))

(deftest read-only-store-can-open-and-prove
  (let [dir (tmp-store "readonly")
        previous (session/capture)]
    (import-medium! dir)
    (let [files (vec (file-seq (io/file dir)))
          permissions (into {} (map (fn [^java.io.File f]
                                      [f (java.nio.file.Files/getPosixFilePermissions
                                          (.toPath f) (make-array java.nio.file.LinkOption 0))])) files)
          snapshot (fn [] (into {} (for [^java.io.File f (file-seq (io/file dir))]
                                     [(.getPath f) [(.length f) (.lastModified f)]])))
          before (snapshot)
          writes #{java.nio.file.attribute.PosixFilePermission/OWNER_WRITE
                   java.nio.file.attribute.PosixFilePermission/GROUP_WRITE
                   java.nio.file.attribute.PosixFilePermission/OTHERS_WRITE}]
      (try
        (doseq [[^java.io.File f perms] permissions]
          (java.nio.file.Files/setPosixFilePermissions (.toPath f) (set (remove writes perms))))
        (binding [a/*verbose* false]
          (a/init! dir "init")
          (is (= ["init"] (mapv :name (storage/list-branches (:store-map @state/ansatz-store)))))
          (let [kstore (get-in @state/ansatz-store [:store-map :store])]
            (is (nil? (storage/store-get kstore :absent)))
            (is (nil? (storage/read-derived kstore "init" :absent))))
          (a/prove-theorem 'readonly-nat-refl '[n :- Nat] '(= Nat n n) '[(rfl)])
          (let [ci (env/lookup (a/env) (name/from-string "readonly-nat-refl"))]
            (is (some? ci))
            (is (env/verifies? (a/env) (.type ci) (.value ci)))))
        (is (= before (snapshot)) "opening, missing reads, lazy resolution and proof leave every file unchanged")
        (finally
          (session/activate! previous)
          (doseq [[^java.io.File f perms] permissions]
            (java.nio.file.Files/setPosixFilePermissions (.toPath f) perms))
          (doseq [^java.io.File f (reverse files)] (.delete f)))))))

(deftest pre-and-inverse-simp-origins-are-persisted-and-served-eagerly
  ;; Lean Origin.decl n post inv (SimpTheorems.lean:69-91): the importer keys only the replayed
  ;; forward post @[simp] rules; pre-phase and inverse origins ride on the :attrs tuples.
  (let [attrs-file (java.io.File/createTempFile "ansatz-origin-attrs" ".ndjson")
        _ (spit attrs-file
                (str "{\"inv\":false,\"kind\":\"simp\",\"name\":\"Nat.add_zero\",\"post\":true,\"prio\":1000}\n"
                     "{\"inv\":false,\"kind\":\"simp\",\"name\":\"Nat.zero_add\",\"post\":false,\"prio\":1000}\n"
                     "{\"inv\":true,\"kind\":\"simp\",\"name\":\"Nat.succ_eq_add_one\",\"post\":true,\"prio\":1000}\n"
                     "{\"inv\":false,\"kind\":\"simp\",\"name\":\"List.length_nil\",\"post\":true,\"prio\":1000}\n"
                     "{\"inv\":true,\"kind\":\"simp\",\"name\":\"List.length_nil\",\"post\":true,\"prio\":1000}\n"))
        dir (tmp-store "origins")
        m (try (import-medium! dir :attrs (.getPath attrs-file)) (finally (.delete attrs-file)))]
    (is (= {:source :dump-fields :pre 1 :inv 2} (get-in m [:artifacts :simp-origins])))
    (binding [a/*verbose* false] (a/init! dir "init"))
    (let [kstore (:store (:store-map @state/ansatz-store))
          tuples (storage/read-derived kstore "init" :attrs)
          keyed (into #{} (map first) (si/key-entries (storage/read-derived kstore "init" :simp-keys)))]
      (is (= [["simp" "Nat.add_zero" nil 1000]
              ["simp" "Nat.zero_add" nil 1000 {:post false :inv false}]
              ["simp" "Nat.succ_eq_add_one" nil 1000 {:post true :inv true}]
              ["simp" "List.length_nil" nil 1000]
              ["simp" "List.length_nil" nil 1000 {:post true :inv true}]]
             (filterv #(= "simp" (first %)) tuples)))
      (testing "the persistent index keys only live forward post rules, encoding unchanged"
        (is (= #{"Nat.add_zero"} keyed))
        (is (= si/write-key-encoding (si/key-encoding (storage/read-derived kstore "init" :simp-keys)))))
      (testing "init! replays the origins: ← erases the forward rule, the rest is served eagerly"
        (is (= #{"Nat.add_zero"} (env/get-extension (a/env) :simp-lemmas #{})))
        (is (= #{["List.length_nil" false]} (si/inherited-erased (a/env))))
        (is (= #{{:name "Nat.zero_add" :post false :inv false :priority 1000}
                 {:name "Nat.succ_eq_add_one" :post true :inv true :priority 1000}
                 {:name "List.length_nil" :post true :inv true :priority 1000}}
               (set (si/eager-origins (a/env))))))
      (testing "both persisted key artifacts carry the literal encoding 2"
        (is (= 2 (:key-encoding (storage/read-derived kstore "init" :simp-keys))))
        (is (= 2 (:key-encoding (storage/read-derived kstore "init" :simp-trie)))))
      (testing "after reopening, simp rewrites with the inverse and the pre rule (kernel-checked)"
        (let [trace (atom [])
              fired #(set (keep (fn [t] (when (:phase t) [(:phase t) (:origin t)])) @trace))]
          (binding [simp/*simp-trace* trace a/*verbose* false]
            (a/prove-theorem 'origin-inv '[^Nat n ^{:- (=> Nat Prop)} P ^{:- (P (Nat.succ n))} h]
                             '(P (+ n 1)) '[(simp) (exact h)]))
          ;; the hard-coded core no longer reintroduces the forward Nat.succ_eq_add_one
          (is (contains? (set (map second (fired))) "← Nat.succ_eq_add_one"))
          (is (not (contains? (set (map second (fired))) "Nat.succ_eq_add_one")))
          (reset! trace [])
          (binding [simp/*simp-trace* trace a/*verbose* false]
            (a/prove-theorem 'origin-pre '[^Nat n ^{:- (=> Nat Prop)} P ^{:- (P n)} h]
                             '(P (+ 0 n)) '[(simp) (exact h)]))
          (is (contains? (fired) [:pre "↓ Nat.zero_add"]))
          (reset! trace [])
          (binding [simp/*simp-trace* trace a/*verbose* false]
            (a/prove-theorem 'origin-pre-all '[^Nat n ^{:- (=> Nat Prop)} P ^{:- (P n)} h]
                             '(P (+ 0 n)) '[(simp_all) (exact h)]))
          (is (contains? (fired) [:pre "↓ Nat.zero_add"]))))
      (testing "an explicit simp [n] restores an erased inherited forward rule and erases ←n"
        (let [r (simp/elab-simp-args (a/env) ['List.length_nil] (#'simp/default-simp-arg-context (a/env) {}))]
          (is (contains? (:erased r) ["List.length_nil" true]))
          (is (not (contains? (:erased r) ["List.length_nil" false])))
          ;; the masked entry is seeded as the inherited entry it is; the explicit forward entry
          ;; replaces it in its phase (no duplicate)
          (is (= ['List.length_nil] (#'simp/replace-registrations (:decls r)))))))))

(deftest a-definition-argument-replaces-an-inherited-inverse-equation
  ;; `simp [f]` adds f's equation f.eq_1 forward; an inherited `@[simp ←] f.eq_1` is erased by it
  ;; (Lean addSimpTheorem/eraseFwdIfBwd in argument order); `-f.eq_1` erases whichever is live
  (let [env @test-env/bundled-init-env
        eq1 (first (ansatz.eqns/get-eqns-for? env (name/from-string "List.length")))
        _ (is (some? eq1) "List.length has a registered equation")
        eq1 (str eq1)
        [env _] (ansatz.attrs/import-attr-tuples env [["simp" eq1 nil 1000 {:post true :inv true}]]
                                                 {:present? (constantly true)})
        ctx (#'simp/default-simp-arg-context env {})]
    (let [r (simp/elab-simp-args env ['List.length] ctx)]
      (is (contains? (:erased r) [eq1 true]))
      (is (not (contains? (:erased r) [eq1 false]))))
    (testing "[f, -f.eq_1]: the forward equation is erased"
      (let [r (simp/elab-simp-args env ['List.length {:erase eq1}] ctx)]
        (is (contains? (:erased r) [eq1 false]))
        (is (contains? (:erased r) [eq1 true]))))
    (testing "[-f.eq_1, f]: the inherited inverse is erased first, f re-adds the forward equation"
      (let [r (simp/elab-simp-args env [{:erase eq1} 'List.length] ctx)]
        (is (contains? (:erased r) [eq1 true]))
        (is (not (contains? (:erased r) [eq1 false])))))))
