(ns ansatz.import-test
  "The single importer (ansatz.import) and store format 1: an export in, a COMPLETE store out —
   manifest last, derived state as blobs, content-addressed roots — and `init!` on it, with
   simp served lazily from the store's index and recall from its keys."
  (:require [clojure.test :refer [deftest is testing]]
            [clojure.java.io :as io]
            [ansatz.core :as a]
            [ansatz.import :as imp]
            [ansatz.store :as store]
            [ansatz.state :as state]
            [ansatz.recall :as recall]
            [ansatz.export.storage :as storage]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]))

(def ^:private ndjson "test-data/init-medium.ndjson")
(def ^:private attrs "resources/ansatz/init-attrs.ndjson.gz")

(defn- tmp-store [tag]
  (let [f (java.io.File/createTempFile (str "ansatz-import-" tag) "")]
    (.delete f) (.deleteOnExit f) (.getPath f)))

(defn- import-medium! [dir & {:as opts}]
  (imp/import! dir (merge {:ndjson ndjson :attrs attrs :branch "init"
                           :provenance {:lean/toolchain "test" :library/rev "init-medium"}
                           :verbose? false :parallelism 2}
                          opts)))

(def ^:private nat (e/const' (name/from-string "Nat") []))
(defn- nle [x y]
  (e/app* (e/const' (name/from-string "LE.le") [lvl/zero]) nat
          (e/const' (name/from-string "instLENat") []) x y))

(deftest an-import-is-a-complete-store
  (let [dir (tmp-store "full")
        m (import-medium! dir)]
    (testing "the manifest is written last and describes the store"
      (is (= store/store-format (:store/format m)))
      (is (= m (store/read-manifest dir)))
      (is (= "init" (:branch m)))
      (is (= "test" (get-in m [:provenance :lean/toolchain])))
      (let [arts (:artifacts m)]
        (is (= 2997 (:declarations arts)))
        (is (= 2997 (:facts arts)) "one facts record per declaration")
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
    (testing "simp serves the inherited set LAZILY from the store's trie blob"
      (is (nil? @state/ansatz-simp-trie) "nothing loaded before the first simp")
      (binding [a/*verbose* false]
        (a/prove-theorem 'imp-opt-inj '[a :- Nat, b :- Nat]
                         '(= Prop (= (Option Nat) (Option.some a) (Option.some b)) (= Nat a b)) '[(simp)]))
      (is (some? (env/lookup (a/env) (name/from-string "imp-opt-inj"))))
      (is (some? (:trie @state/ansatz-simp-trie)) "the trie blob was loaded on demand"))
    (testing "the facts blobs carry the statement's and the value's vocabulary"
      (let [sm (:store-map @state/ansatz-store)
            kstore (:store sm)
            n (storage/read-derived kstore "init" :facts-chunks)
            facts (into [] (mapcat #(storage/read-derived kstore "init" [:facts %])) (range n))
            by-name (into {} (map (juxt :name identity)) facts)
            f (by-name "Nat.add_comm")]
        (is (pos? n) "facts are chunked")
        (is (= 2997 (count facts)))
        (is (= :thm (:kind f)))
        (is (= "Eq" (:concl-head f)))
        (is (= 2 (:num-binders f)))
        (is (contains? (set (:mentions f)) "HAdd.hAdd") "the STATEMENT's constants")
        (is (contains? (set (:depends-on f)) "Nat.succ_add") "the VALUE's constants")
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
