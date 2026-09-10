(ns ansatz.catalogue-test
  "The store catalogue (ansatz.catalogue): built once from the key sidecars into a datahike DB
   with the durable disc-tree index as two instances (`:idx/dt` recall, `:idx/simp` simp
   LHS), connected — not rebuilt — by later processes, and reached from ansatz.recall with the
   in-memory trie as the fallback."
  (:require [clojure.test :refer [deftest is testing]]
            [clojure.java.io :as io]
            [datahike.api :as d]
            [ansatz.catalogue :as cat]
            [ansatz.recall :as recall]
            [ansatz.state :as state]
            [ansatz.index.discr :as dti]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl])
  (:import [java.util.zip GZIPOutputStream]))

(defn- nat [] (e/const' (name/from-string "Nat") []))
(defn- nle [a b]
  (e/app* (e/const' (name/from-string "LE.le") [lvl/zero]) (nat)
          (e/const' (name/from-string "instLENat") []) a b))
(defn- eqp [a b]
  (e/app* (e/const' (name/from-string "Eq") [(lvl/succ lvl/zero)]) (nat) a b))
(defn- hole [] (e/mvar 900001))

(defn- write-keys! [^java.io.File f rows]
  (with-open [w (io/writer (GZIPOutputStream. (io/output-stream f)))]
    (doseq [[n k] rows] (.write w (pr-str {:name n :key k})) (.write w "\n"))))

(defn- fresh-store-dir []
  (let [d (java.io.File/createTempFile "ansatz-store" "")]
    (.delete d) (.mkdirs d) (.deleteOnExit d)
    d))

(defn- sidecars! [dir]
  ;; recall keys: conclusions; simp keys: LHS patterns — deliberately overlapping names
  (write-keys! (io/file dir "discr-keys.ndjson.gz")
               [["le_a" (dti/conclusion-key (nle (e/lit-nat 1) (e/lit-nat 2)))]
                ["zero_le" (dti/conclusion-key (nle (e/lit-nat 0) (hole)))]
                ["eq_a" (dti/conclusion-key (eqp (e/lit-nat 3) (e/lit-nat 3)))]])
  (write-keys! (io/file dir "simp-keys.ndjson.gz")
               [["zero_le" (dti/conclusion-key (nle (e/lit-nat 0) (hole)))]
                ["and_split" (dti/conclusion-key (eqp (hole) (e/lit-nat 7)))]
                ["and_split" (dti/conclusion-key (eqp (e/lit-nat 7) (hole)))]]))

(deftest build-connect-and-query-both-indices
  (let [dir (fresh-store-dir) p (.getPath dir)]
    (sidecars! dir)
    (testing "one entity per name, keys merged from both sidecars"
      (let [stats (cat/build! p)]
        (is (= 4 (:entities stats)))
        (is (= 3 (:dt-keys stats)))
        (is (= 3 (:simp-keys stats)))))
    (testing "a fresh connection answers through the persisted indices"
      (is (cat/exists? p))
      (let [conn (cat/connect p) db @conn]
        (try
          (is (= #{"le_a"} (set (cat/recall-names db (dti/query-key (nle (e/lit-nat 1) (e/lit-nat 2)))))))
          (is (= #{"zero_le"} (set (cat/recall-names db (dti/query-key (nle (e/lit-nat 0) (e/lit-nat 9))))))
              "a stored star matches")
          (is (= #{"le_a" "zero_le"} (set (cat/recall-names db (dti/query-key (nle (hole) (hole)))))))
          (is (= #{"and_split"} (set (cat/simp-lemma-names db (dti/query-key (eqp (e/lit-nat 7) (e/lit-nat 7))))))
              "cardinality-many simp keys both index the same lemma; names are deduped")
          (is (= #{"zero_le"} (set (cat/simp-lemma-names db (dti/query-key (nle (e/lit-nat 0) (e/lit-nat 1)))))))
          (is (= #{} (set (cat/simp-lemma-names db (dti/query-key (nle (e/lit-nat 1) (e/lit-nat 2))))))
              "the recall index does not leak into the simp index")
          (is (vector? (:root @(get (:secondary-indices db) :idx/dt))) "restored from a persisted root")
          (finally (d/release conn)))))))

(deftest recall-prefers-the-catalogue-and-falls-back-to-the-trie
  (let [dir (fresh-store-dir) p (.getPath dir)]
    (sidecars! dir)
    (try
      (testing "no catalogue → the in-memory trie from the keys sidecar"
        (reset! recall/store-path p)
        (reset! recall/discr-keys-path (.getPath (io/file dir "discr-keys.ndjson.gz")))
        (reset! state/ansatz-discr-trie nil)
        (is (= #{"zero_le"} (set (recall/recall-names (nle (e/lit-nat 0) (e/lit-nat 5))))))
        (is (some? @state/ansatz-discr-trie) "the trie was built on demand"))
      (testing "with a catalogue → the persisted index, trie untouched"
        (cat/build! p)
        (reset! state/ansatz-discr-trie nil)
        (is (= #{"zero_le"} (set (recall/recall-names (nle (e/lit-nat 0) (e/lit-nat 5))))))
        (is (nil? @state/ansatz-discr-trie) "no trie was built"))
      (finally
        (reset! recall/store-path nil)
        (reset! recall/discr-keys-path nil)
        (reset! state/ansatz-discr-trie nil)))))
