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
