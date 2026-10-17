(ns prototype.declaration-store-test
  (:require [clojure.test :refer [deftest is]]
            [clojure.java.io :as io]
            [clojure.data.json :as json]
            [prototype.declaration-store :as store]
            [prototype.import-ir :as ir]
            [prototype.module-bench :as modules]
            [prototype.heap-examples :as h]
            [prototype.lazy-runtime :as lazy]
            [prototype.machine :as m]
            [prototype.mutable :as u]))

(defmacro with-directory [[sym] & body]
  `(let [~sym (.toFile (java.nio.file.Files/createTempDirectory
                        "ansatz-store-test-" (make-array java.nio.file.attribute.FileAttribute 0)))]
     (try ~@body
          (finally (doseq [file# (reverse (file-seq ~sym))] (io/delete-file file# true))))))

(defn execute [functions entry args cache]
  (let [program (lazy/open-program functions {} cache)
        initial (m/start (m/world functions) entry args)]
    {:state (u/freeze (lazy/run! program (u/thaw initial)))
     :reference (m/run initial) :counts (lazy/summary program)}))

(deftest selected-real-ir-reload-and-execution
  (with-directory [dir]
    (let [packed (store/pack! dir ["fixtures/list-map.jsonl" "fixtures/list-fold.jsonl"])
          hash (store/checkpoint! packed)
          reopened (store/open-index dir hash)
          root (h/entry (ir/load-bundle "fixtures/list-map.jsonl") "List.map._redArg")
          selected (ir/load-closure reopened [root])
          [world input] (m/guest-list (m/world selected) [1 2 3])
          initial (m/start world root [(m/->Builtin :inc) input])
          result (u/freeze (lazy/run! (lazy/open-program selected) (u/thaw initial)))]
      (is (= 1 (:blob-reads (store/stats reopened))))
      (is (= 1 (count selected)))
      (is (= (ir/load-closure (ir/index-bundles ["fixtures/list-map.jsonl"]) [root]) selected))
      (is (= (m/run initial) result))
      (is (= [2 3 4] (m/list-values result (:result result))))
      (is (= hash (store/checkpoint! reopened))))))

(deftest unused-blobs-remain-unread-and-may-be-unsupported
  (with-directory [dir]
    (let [input (str (io/file dir "module.jsonl"))
          _ (modules/write-module! 100 input)
          packed (store/pack! dir [input])
          unknown (modules/name-of "unsupported")
          packed (store/with-declaration! packed {:kind "decl" :name unknown :ir {:extern {}}})
          reopened (store/open-index dir (store/checkpoint! packed))
          cold (modules/name-of "cold0")
          cold-file (io/file dir "declarations" (str (get (:declarations reopened) cold) ".json"))]
      (is (zero? (:blob-reads (store/stats reopened))))
      ;; Even a missing unused file cannot affect selecting a different closure.
      (io/delete-file cold-file)
      (is (= 2 (count (ir/load-closure reopened [modules/entry]))))
      (is (= 2 (:blob-reads (store/stats reopened))))
      (is (thrown? java.nio.file.NoSuchFileException (ir/load-closure reopened [cold])))
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Missing body or extern"
                            (ir/load-closure reopened [unknown])))
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Missing declaration dependency"
                            (ir/load-closure reopened [(modules/name-of "missing")]))))))

(deftest immutable-edit-checkpoints-and-code-reuse
  (with-directory [dir]
    (let [input (str (io/file dir "module.jsonl"))
          _ (modules/write-module! 10 input)
          old (store/open-index dir (store/checkpoint! (store/pack! dir [input])))
          old-hash (store/checkpoint! old)
          edited (store/with-declaration! old (modules/declaration modules/value-name 43))
          new-hash (store/checkpoint! edited)
          cache (lazy/code-cache)
          before (execute (ir/load-closure old [modules/entry]) modules/entry [] cache)
          after (execute (ir/load-closure edited [modules/entry]) modules/entry [] cache)]
      (is (not= old-hash new-hash))
      (is (= (dissoc (:declarations old) modules/value-name)
             (dissoc (:declarations edited) modules/value-name)))
      (is (= 42 (get-in before [:state :result])))
      (is (= 43 (get-in after [:state :result])))
      (is (= (:reference before) (:state before)))
      (is (= (:reference after) (:state after)))
      (is (= 1 (get-in after [:counts :compiled])))
      (is (= 2 (get-in after [:counts :cache-hits])))
      (is (= 42 (get-in (execute (ir/load-closure (store/open-index dir old-hash) [modules/entry])
                                modules/entry [] cache) [:state :result])))
      (is (= 43 (get-in (execute (ir/load-closure (store/open-index dir new-hash) [modules/entry])
                                modules/entry [] cache) [:state :result]))))))

(deftest corrupted-blobs-and-indexes-are-rejected
  (with-directory [dir]
    (let [packed (store/pack! dir ["fixtures/list-map.jsonl"])
          hash (store/checkpoint! packed)
          reopened (store/open-index dir hash)
          name (first (keys (:declarations reopened)))
          file (io/file dir "declarations" (str (get (:declarations reopened) name) ".json"))]
      (spit file "{}")
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"digest mismatch" (ir/load-closure reopened [name])))
      (spit (io/file dir "indexes" (str hash ".json")) "{}")
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"digest mismatch" (store/open-index dir hash)))
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Invalid store digest" (store/open-index dir "../escape"))))))

(deftest canonical-row-identity-and-conflicting-input
  (with-directory [dir]
    (let [row (modules/declaration modules/value-name 42)
          old (store/with-declaration! (store/empty-store dir) row)
          reordered (store/with-declaration! old (into (sorted-map-by #(compare (str %2) (str %1))) row))
          input (io/file dir "bad.jsonl")]
      (is (= (:declarations old) (:declarations reordered)))
      (spit input (str (json/write-str {:schema "lean-ir-probe/1" :leanVersion "wrong"}) "\n"))
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Unsupported producer" (store/pack! dir [input])))
      (modules/write-module! 0 (str input))
      (spit input (str (json/write-str (modules/declaration modules/value-name 99)) "\n") :append true)
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Conflicting declaration" (store/pack! dir [input]))))))

(deftest numeric-and-string-name-components-stay-distinct
  (with-directory [dir]
    (let [numeric ["num" ["anonymous"] 1]
          string ["str" ["anonymous"] "1"]
          old (-> (store/empty-store dir)
                  (store/with-declaration! (modules/declaration numeric 42))
                  (store/with-declaration! (modules/declaration string 99)))
          reopened (store/open-index dir (store/checkpoint! old))
          functions (ir/load-closure reopened [numeric string])
          cache (lazy/code-cache)]
      (is (= #{numeric string} (set (keys functions))))
      (is (= 42 (get-in (execute functions numeric [] cache) [:state :result])))
      (is (= 99 (get-in (execute functions string [] cache) [:state :result]))))))

(deftest catalogue-overlay-resolves-only-selected-rows
  (let [a (modules/name-of "base") b (modules/name-of "overlay")
        unused (modules/name-of "unused") missing (modules/name-of "missing")
        reads (atom [])
        row-a (modules/declaration a 1) row-b (modules/declaration b 2)
        base {:manifests [{:base true}] :declarations {a :opaque-a unused :opaque-unused}
              :read-declaration (fn [name] (swap! reads conj name)
                                  (if (= name a) row-a (throw (ex-info "Unused blob read" {}))))}
        addition {:manifests [{:overlay true}] :declarations {b row-b}}
        combined (store/overlay base addition)]
    (is (= [] @reads))
    (is (= [{:base true} {:overlay true}] (:manifests combined)))
    (is (= #{a b unused} (set (keys (:declarations combined)))))
    (is (= :opaque-a (get-in combined [:declarations a])))
    (is (= row-b ((:read-declaration combined) b)))
    (is (= [] @reads))
    (is (nil? ((:read-declaration combined) missing)))
    (is (= row-a ((:read-declaration combined) a)))
    (is (= [a] @reads))
    (is (= {a :opaque-a unused :opaque-unused} (:declarations base)))
    (is (= {b row-b} (:declarations addition)))))

(deftest catalogue-overlay-reconciles-duplicates-lazily
  (let [name modules/value-name row (modules/declaration name 42)
        local (assoc row :sourceLocal true :runtime {:role "closed"})
        reads (atom [])
        indexed (fn [label row]
                  {:declarations {name (keyword label)}
                   :read-declaration (fn [n] (swap! reads conj [label n]) row)})
        combined (store/overlay (indexed "base" row) (indexed "overlay" local))]
    (is (empty? @reads))
    (is (= local ((:read-declaration combined) name)))
    (is (= [["base" name] ["overlay" name]] @reads))
    (is (= row ((:read-declaration (store/overlay {:declarations {name row}}
                                               {:declarations {name row}})) name)))
    (is (= local ((:read-declaration (store/overlay {:declarations {name local}}
                                                 {:declarations {name row}})) name)))))

(deftest catalogue-overlay-rejects-selected-drift-without-touching-unrelated-rows
  (let [name modules/value-name row (modules/declaration name 42)]
    (doseq [changed [(assoc row :ir {:changed true})
                     (assoc row :dependencies [(modules/name-of "unexpected")])
                     (assoc row :redirect (modules/name-of "redirect"))
                     (assoc row :runtime {:role "closed"})]]
      (let [combined (store/overlay {:declarations {name row}}
                                    {:declarations {name changed}})]
        (is (nil? ((:read-declaration combined) (modules/name-of "absent"))))
        (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Conflicting declaration"
                              ((:read-declaration combined) name)))))))

(deftest catalogue-overlay-keeps-durable-base-index-and-unused-blobs-untouched
  (with-directory [dir]
    (let [packed (store/pack! dir ["fixtures/list-map.jsonl"])
          hash (store/checkpoint! packed)
          base (store/open-index dir hash)
          before (:declarations base)
          name (modules/name-of "new-local") row (modules/declaration name 7)
          combined (store/overlay base {:declarations {name row}})]
      (is (zero? (:blob-reads (store/stats base))))
      (is (= row ((:read-declaration combined) name)))
      (is (zero? (:blob-reads (store/stats base))))
      (is (zero? (:blob-publishes (store/stats base))))
      (is (identical? before (:declarations base)))
      (is (= hash (store/checkpoint! base))))))

(deftest checkpoint-canonical-order-encodes-each-name-once
  (with-directory [dir]
    (let [names (vec (concat (for [i (range 40)] ["str" ["anonymous"] (str "entry" i)])
                             [["num" ["anonymous"] 0] ["str" ["anonymous"] "0"]
                              ["str" ["anonymous"] "λ界"]]))
          declarations (zipmap names (repeat (apply str (repeat 64 "0"))))
          catalogue (assoc (store/empty-store dir) :declarations declarations)
          encode #'store/encode
          original @encode
          legacy-index {:schema "lean-ir-store/1" :manifests []
                        :declarations (sort-by (comp original first) declarations)}
          expected (:hash (#'store/publish! dir "indexes" legacy-index))
          calls (atom 0)
          actual (with-redefs-fn {encode (fn [value] (swap! calls inc) (original value))}
                   #(store/checkpoint! catalogue))]
      (is (= expected actual))
      ;; One key per Name and the schema string; no full-index encoding.
      (is (= (inc (count names)) @calls))
      (is (= declarations (:declarations (store/open-index dir actual)))))))

(deftest streaming-index-reopen-shares-name-prefixes-without-changing-content
  (with-directory [dir]
    (let [prefix ["str" ["anonymous"] "Shared"]
          a ["str" prefix "a"] b ["str" prefix "b"]
          declarations {a (apply str (repeat 64 "1")) b (apply str (repeat 64 "2"))}
          packed (assoc (store/empty-store dir) :declarations declarations)
          hash (store/checkpoint! packed)
          reopened (store/open-index dir hash)
          names (vec (keys (:declarations reopened)))]
      (is (= declarations (:declarations reopened)))
      (is (identical? (second (first names)) (second (second names))))
      (is (= hash (store/checkpoint! reopened)))
      (is (zero? (:blob-reads (store/stats reopened)))))))

(deftest streaming-index-reader-rejects-invalid-json-and-duplicate-fields
  (with-directory [dir]
    (let [write! (fn [text]
                   (let [bytes (#'store/utf8-bytes text)
                         hash (#'store/digest bytes)
                         file (io/file dir "indexes" (str hash ".json"))]
                     (io/make-parents file)
                     (spit file text :encoding "UTF-8") hash))]
      (doseq [text ["{\"declarations\":[],\"manifests\":[],\"schema\":\"lean-ir-store/1\",}"
                    "{\"declarations\":[],\"manifests\":[],\"schema\":\"lean-ir-store/1\"}null"
                    "{\"declarations\":[],\"declarations\":[],\"manifests\":[],\"schema\":\"lean-ir-store/1\"}"]]
        (is (thrown? clojure.lang.ExceptionInfo (store/open-index dir (write! text)))))
      (let [text "{\"schema\":\"lean-ir-store/1\",\"manifests\":[],\"declarations\":[]}"]
        (is (= {} (:declarations (store/open-index dir (write! text)))))))))
