(ns prototype.bootstrap-archive-test
  (:require [clojure.test :refer [deftest is]] [clojure.java.io :as io]
            [prototype.bootstrap-archive :as archive] [prototype.machine :as m])
  (:import [java.security MessageDigest]))
(def header {:lean-version archive/lean-version :lean-commit archive/lean-commit :note "tiny test"})
(defn sha [text]
  (apply str (map #(format "%02x" (bit-and 255 %))
                 (.digest (MessageDigest/getInstance "SHA-256") (.getBytes ^String text "UTF-8")))))
(defn path [] (doto (java.io.File/createTempFile "ansatz-bootstrap-test-" ".edn") (.deleteOnExit)))
(defn options [hash] {:expected-sha256 hash :expected-lean-commit archive/lean-commit})
(defn world []
  (let [name ["f"] function (with-meta {:params [0] :body [:return [:var 0]]}
                                     {:runtime-signature {:params [{:ty "object" :borrow false}] :return-type "object"}
                                      :nested (with-meta [:abi] {:preserved true})})
        [world ref] (m/allocate (m/world {name function}) :ctor 3 [(m/->Tag 0) (m/->Builtin :inc)])]
    (assoc world :status :done :result ref :globals {["constant"] {:status :ready :value ref}}
           :stdio-runtime {:streams {}})))
(deftest tiny-world-roundtrip-preserves-metadata-ownership-and-carriers
  (let [file (path) original (world) written (archive/write! file original header)
        restored (archive/restore file (options (:sha256 written))) after (:world restored)
        before-function (get-in original [:functions ["f"]]) after-function (get-in after [:functions ["f"]])]
    (is (:verified written))
    (is (= {:functions 1 :heap 1 :globals 1} (:counts written)))
    (is (= original after))
    (is (= (meta before-function) (meta after-function)))
    (is (= {:preserved true} (meta (:nested (meta after-function)))))
    (is (= (:sha256 written) (:sha256 restored)))
    (is (= 1 (:rc (m/node after (:result after)))))
    (is (= original (world)))))
(defn minimal-rows []
  (let [world (assoc (m/world {}) :status :done)
        header (merge header {:format archive/format-id :counts {:functions 0 :heap 0 :globals 0} :status :done})]
    [[:header header] [:state (dissoc world :functions :heap :globals)] [:end (:counts header)]]))
(defn text [rows] (str (clojure.string/join "\n" (map pr-str rows)) "\n"))
(defn restore-rows [rows]
  (let [file (path) contents (text rows)]
    (spit file contents) (archive/restore file (options (sha contents)))))
(deftest old-format-is-accepted-and-digest-and-provenance-are-mandatory
  (is (= :done (get-in (restore-rows (minimal-rows)) [:world :status])))
  (let [file (path) original (world) result (archive/write! file original header)]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"SHA256 mismatch"
          (archive/restore file (options (apply str (repeat 64 "0"))))))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"explicit SHA256"
          (archive/restore file {:expected-sha256 (:sha256 result)})))
    (is (thrown? clojure.lang.ExceptionInfo
          (archive/restore file (assoc (options (:sha256 result)) :expected-lean-commit "wrong")))))
  (doseq [change [(fn [rows] (assoc-in rows [0 1 :lean-commit] "wrong"))
                  (fn [rows] (assoc-in rows [0 1 :lean-version] "4.33.0"))
                  (fn [rows] (assoc-in rows [0 1 :format] "other"))]]
    (is (thrown? clojure.lang.ExceptionInfo (restore-rows (change (minimal-rows)))))))
(deftest malformed-truncated-duplicate-and-trailing-rows-are-rejected
  (doseq [rows [(pop (minimal-rows))
                (assoc-in (minimal-rows) [0 1 :counts :heap] 1)
                (assoc-in (minimal-rows) [2 1 :functions] 1)
                (conj (minimal-rows) [:extra])
                [(first (minimal-rows)) [:state {}] (last (minimal-rows))]
                [(first (minimal-rows)) (second (minimal-rows)) (second (minimal-rows)) (last (minimal-rows))]
                [(first (minimal-rows)) [:unknown] (last (minimal-rows))]
                [(first (minimal-rows)) [:state (assoc (second (second (minimal-rows))) :heap {})] (last (minimal-rows))]]]
    (is (thrown? Exception (restore-rows rows))))
  (let [rows (minimal-rows) header (assoc-in (second (first rows)) [:counts :functions] 2)
        f {:params [] :body [:return [:imm 0]]}]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Duplicate"
          (restore-rows [[:header header] [:function ["f"] f] [:function ["f"] f]
                         (second rows) [:end (:counts header)]])))))
(deftest reader-tags-and-eval-forms-are-not-authority
  (doseq [form ["#inst \"2020-01-01\"" "#uuid \"00000000-0000-0000-0000-000000000000\""
                "#unknown {}" "#prototype.machine.Ref []" "#=(throw (Exception.))"]]
    (let [file (path) contents (str (pr-str (first (minimal-rows))) "\n" form "\n")]
      (spit file contents)
      (is (thrown? Exception (archive/restore file (options (sha contents))))))))
(deftest unsupported-worlds-and-failed-writes-never-replace-the-destination
  (doseq [change [#(assoc % :native-imports [:opaque]) #(assoc % :kernel-environments {0 :opaque})
                  #(assoc % :opaque (atom 1)) #(assoc % :status :running)
                  #(assoc-in % [:heap 0 :rc] -1) #(assoc-in % [:heap 0 :fields] [(m/->Ref 999)])
                  #(assoc-in % [:heap 0 :kind] :resource)]]
    (let [file (path)]
      (spit file "existing")
      (is (thrown? Exception (archive/write! file (change (world)) header)))
      (is (= "existing" (slurp file))))))

(deftest completed-dead-registers-are-data-not-live-owners
  (let [file (path) before (assoc (world) :locals {7 (m/->Ref 999)}
                                 :body [:return [:var 7]] :result (m/->Tag 0))
        saved (archive/write! file before header)
        restored (:world (archive/restore file (options (:sha256 saved))))]
    (is (= before restored))
    (is (= (m/->Ref 999) (get-in restored [:locals 7])))))
(deftest all-entry-tables-reject-duplicates-and-restored-unsupported-state
  (doseq [[kind key value counter] [[:function ["f"] {:params [] :body [:return [:imm 0]]} :functions]
                                   [:heap 0 {:kind :ctor :tag 0 :fields [] :rc 1} :heap]
                                   [:global ["g"] {:status :ready :value 0} :globals]]]
    (let [rows (minimal-rows) header (assoc-in (second (first rows)) [:counts counter] 2)]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Duplicate"
            (restore-rows [[:header header] [kind key value] [kind key value]
                           (second rows) [:end (:counts header)]])))))
  (doseq [change [#(assoc % :native-imports [:native]) #(assoc % :kernel-environments {0 :kernel})]]
    (is (thrown? clojure.lang.ExceptionInfo
          (restore-rows (update-in (minimal-rows) [1 1] change))))))

(deftest executable-identity-capabilities-cannot-be-serialized-as-equal-copies
  (let [original (world)
        authorization {:functions (:functions original)}
        file (path)]
    (spit file "unchanged")
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"identity authorizations"
          (archive/write! file (assoc original :eval-const-authorizations authorization) header)))
    (is (= "unchanged" (slurp file)))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"identity authorizations"
          (restore-rows (assoc-in (minimal-rows) [1 1 :eval-const-authorizations] authorization)))))
  (let [file (path) original (assoc (world) :eval-const-authorizations {})
        saved (archive/write! file original header)]
    (is (= original (:world (archive/restore file (options (:sha256 saved))))))))

(deftest owned-source-module-capabilities-require-explicit-reattachment
  (doseq [key [:source-modules :source-regions :source-import-prefixes]]
    (let [file (path) capabilities {"A" {:data (m/->Ref 0)}}]
      (spit file "unchanged")
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Owned source module"
            (archive/write! file (assoc (world) key capabilities) header)))
      (is (= "unchanged" (slurp file)))
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Owned source module"
            (restore-rows (assoc-in (minimal-rows) [1 1 key] capabilities))))))
  (let [file (path) original (assoc (world) :source-modules {} :source-regions {})
        saved (archive/write! file original header)]
    (is (= original (:world (archive/restore file (options (:sha256 saved))))))))
