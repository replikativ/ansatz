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

(defn serialized-name [] ["str" ["str" ["anonymous"] "Namespace"] "member"])
(defn same-data? [a b]
  ((ns-resolve 'prototype.bootstrap-archive 'same-data?) a b))

(deftest restored-name-prefixes-share-within-one-restore-only
  (let [file (path)
        function {:params [] :body [:return [:imm 0]] :target (serialized-name)}
        original (assoc (world)
                        :functions {(serialized-name) function}
                        :function-copies [function function]
                        :globals {(serialized-name) {:status :ready :value (:result (world))}}
                        :repeated [(serialized-name) (serialized-name)
                                   ["str" ["str" ["anonymous"] "Namespace"] "other"]])
        saved (archive/write! file original (assoc header :entrypoint (serialized-name)))
        shared (archive/restore file (options (:sha256 saved)))
        after (:world shared)
        unshared (archive/restore file (assoc (options (:sha256 saved)) :share-names? false))
        again (archive/restore file (options (:sha256 saved)))
        n (first (keys (:functions after)))
        copies [(get-in shared [:header :entrypoint])
                (get-in after [:functions n :target])
                (first (keys (:globals after)))
                (get-in after [:repeated 0]) (get-in after [:repeated 1])]]
    (is (same-data? original after))
    (is (same-data? after (:world unshared)))
    (is (= (:sha256 shared) (:sha256 unshared) (:sha256 saved)))
    (is (every? #(identical? n %) copies))
    (is (identical? (second n) (second (get-in after [:repeated 2]))))
    (is (not (identical? (get-in unshared [:world :repeated 0])
                         (get-in unshared [:world :repeated 1]))))
    (is (not (identical? n (get-in again [:world :repeated 0]))))
    (is (not (identical? (get-in after [:function-copies 0]) (get-in after [:function-copies 1]))))
    (is (= 1 (:rc (m/node after (:result after)))))
    (is (= (class (:result original)) (class (:result after))))))

(deftest name-sharing-preserves-nested-metadata-and-never-conflates-prefixes
  (let [file (path)
        prefix-a (with-meta ["str" ["anonymous"] "Namespace"]
                   {:different (with-meta [:detail] {:flavor :a}) :name (serialized-name)})
        prefix-b (with-meta ["str" ["anonymous"] "Namespace"]
                   {:different (with-meta [:detail] {:flavor :b}) :name (serialized-name)})
        outer (with-meta (serialized-name) {:outer (with-meta [:meta] {:nested true})})
        first-name ["str" prefix-a "member"]
        second-name ["str" prefix-b "member"]
        original (assoc (world)
                        :names [first-name second-name outer (serialized-name)]
                        :containers (with-meta
                                      {:key (with-meta (list (serialized-name)) {:list-meta true})
                                       :set (with-meta #{(serialized-name)} {:set-meta true})
                                       :record (with-meta (m/->Tag 7) {:carrier-name (serialized-name)})}
                                      {:map-meta (with-meta [(serialized-name)] {:vector-meta true})}))
        saved (archive/write! file original header)
        after (:world (archive/restore file (options (:sha256 saved))))]
    (is (same-data? original after))
    (is (= (get-in after [:names 0]) (get-in after [:names 1])))
    (is (not (identical? (get-in after [:names 0]) (get-in after [:names 1]))))
    (is (= :a (:flavor (meta (:different (meta (second (get-in after [:names 0]))))))))
    (is (= :b (:flavor (meta (:different (meta (second (get-in after [:names 1]))))))))
    (is (not (identical? (get-in after [:names 2]) (get-in after [:names 3]))))
    (is (= {:nested true} (meta (:outer (meta (get-in after [:names 2]))))))
    (is (instance? prototype.machine.Tag (get-in after [:containers :record])))
    (is (= 7 (:tag (get-in after [:containers :record]))))))

(deftest name-sharing-does-not-normalize-numeric-parts-or-lookalikes
  (let [file (path)
        values [["str" ["anonymous"] "1"] ["num" ["anonymous"] "1"]
                ["num" ["anonymous"] "01"] ["num" ["anonymous"] 1]
                ["num" ["anonymous"] "-1"] ["num" ["anonymous"] "not-numeric"]
                ["str" ["anonymous"] :member] ["str" ["anonymous"] "member" :extra]
                ["str" ["wrong"] "member"] ["anonymous" :extra]
                ["str" (with-meta ["anonymous"] {:prefix :metadata}) "1"]]
        original (assoc (world) :lookalikes values
                        :carriers [(m/->Ref 0) (m/->Tag 3) (m/->Builtin :inc)])
        saved (archive/write! file original header)
        after (:world (archive/restore file (options (:sha256 saved))))]
    (is (same-data? original after))
    (doseq [[left right] [[0 1] [1 2] [1 3] [0 10]]]
      (is (not (identical? (get-in after [:lookalikes left]) (get-in after [:lookalikes right])))))
    (is (= {:prefix :metadata} (meta (second (get-in after [:lookalikes 10])))))
    (is (= (mapv class (:carriers original)) (mapv class (:carriers after))))))

(deftest name-sharing-does-not-weaken-archive-validation
  (let [file (path) saved (archive/write! file (world) header)]
    (doseq [share? [true false]]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"SHA256 mismatch"
                            (archive/restore file (assoc (options (apply str (repeat 64 "0"))) :share-names? share?)))))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"must be boolean"
                          (archive/restore file (assoc (options (:sha256 saved)) :share-names? :yes)))))
  (doseq [share? [true false]]
    (let [file (path)
          rows (update-in (minimal-rows) [1 1] assoc :reachable-name
                          ["str" ["anonymous"] (m/->Ref 999)])
          contents (text rows)]
      (spit file contents)
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"dangling"
                            (archive/restore file (assoc (options (sha contents)) :share-names? share?)))))))

(deftest deep-ir-row-restores-with-name-sharing-and-exact-metadata
  ;; Exercise recursive restore traversal on the same fixed worker stack as a
  ;; real archive, without recursive Clojure equality over the deep row.
  (let [file (path)
        deep-name (reduce (fn [prefix i] ["str" prefix (str "n" i)]) ["anonymous"] (range 512))
        body (reduce (fn [body i]
                       (with-meta [:let i [:literal (if (zero? (mod i 32)) deep-name "value")] body]
                         {:depth i :note (with-meta [:annotation] {:preserved true})}))
                     [:return [:imm 0]] (range 512))
        original (assoc (world) :functions {["deep"] (with-meta {:params [] :body body} {:name deep-name})}
                        :repeated-deep-names [deep-name deep-name])
        saved (archive/write! file original header)
        shared (:world (archive/restore file (options (:sha256 saved))))
        baseline (:world (archive/restore file (assoc (options (:sha256 saved)) :share-names? false)))
        expected-name (first (:repeated-deep-names shared))]
    (is (same-data? original shared))
    (is (same-data? shared baseline))
    (is (identical? expected-name (second (:repeated-deep-names shared))))
    (is (identical? expected-name (:name (meta (get-in shared [:functions ["deep"]])))))
    (loop [node (get-in shared [:functions ["deep"] :body]) depth 511 seen 0]
      (if (neg? depth)
        (do (is (= :return (first node))) (is (= 16 seen)))
        (do
          (is (= depth (:depth (meta node))))
          (is (true? (:preserved (meta (:note (meta node))))))
          (when (zero? (mod depth 32))
            (is (identical? expected-name (second (nth node 2)))))
          (recur (nth node 3) (dec depth) (if (zero? (mod depth 32)) (inc seen) seen)))))))
