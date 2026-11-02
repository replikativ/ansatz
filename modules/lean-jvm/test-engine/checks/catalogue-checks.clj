(ns java-ir-catalogue-checks
  "Small host-only catalogue gates. Does not open the full campaign catalogue."
  (:require [clojure.test :refer [deftest is run-tests]]
            [clojure.data.json :as json]
            [clojure.java.io :as io]
            [ansatz.research.ir.catalogue :as catalogue])
  (:import (java.nio.file Files Path StandardCopyOption)
           (java.nio.charset StandardCharsets)
           (java.security MessageDigest)
           (java.util Arrays ArrayList)))

(def ^:private fixture-root
  (.getCanonicalFile (io/file ".")))
(def ^:private source-pin (apply str (repeat 64 "1")))
(defn- digest [^bytes bytes] (.digest (MessageDigest/getInstance "SHA-256") bytes))
(defn- hex [^bytes bytes] (apply str (map #(format "%02x" (bit-and 255 %)) bytes)))
(defn- utf8 [text] (.getBytes ^String text StandardCharsets/UTF_8))
(defn- write! [file ^bytes bytes]
  (Files/write (.toPath (io/file file)) bytes (make-array java.nio.file.OpenOption 0)))
(defn- original-rows []
  (let [rows (json/read-str
              (slurp (io/file fixture-root "test/fixtures/java-ref-runtime/original-rows.json")))]
    (mapv #(get % "row") (take 2 rows))))
(defn- java-lists [value]
  (if (vector? value) (ArrayList. ^java.util.Collection (mapv java-lists value)) value))
(defn- with-directory [f]
  (let [parent (io/file fixture-root "target/java-catalogue-checks")]
    (.mkdirs parent)
    (let [directory (.toFile (Files/createTempDirectory (.toPath parent) "case-"
                                                       (make-array java.nio.file.attribute.FileAttribute 0)))]
      (try (f directory)
           (finally (doseq [file (reverse (file-seq directory))] (io/delete-file file)))))))
(defn- fixture!
  ([directory] (fixture! directory nil))
  ([directory forced-key]
   (let [declarations (io/file directory "declarations")
         _ (.mkdirs declarations)
         entries (mapv (fn [row]
                         (let [bytes (utf8 (json/write-str row))
                               sha (hex (digest bytes))]
                           (write! (io/file declarations (str sha ".json")) bytes)
                           {:row row :sha sha :bytes bytes
                            :key (digest (catalogue/typed-name-bytes (get row "name")))}))
                       (original-rows))
         ;; For collision tests A is the larger row SHA, so B is necessarily scanned first.
         by-sha (vec (sort-by :sha entries))
         a (peek by-sha)
         b (first by-sha)
         entries (if forced-key (mapv #(assoc % :key (:key a)) entries) entries)
         records (mapv (fn [{:keys [key sha]}]
                         (let [record (byte-array 64)]
                           (System/arraycopy key 0 record 0 32)
                           (doseq [i (range 32)]
                             (aset-byte record (+ 32 i)
                                        (unchecked-byte (Integer/parseInt (subs sha (* 2 i) (+ 2 (* 2 i))) 16))))
                           record)) entries)
         sorted-records (sort #(Arrays/compareUnsigned ^bytes %1 ^bytes %2) records)
         data (byte-array (* 64 (count entries)))
         _ (doseq [[i record] (map-indexed vector sorted-records)]
             (System/arraycopy record 0 data (* 64 i) 64))
         manifest {"schema" "java-ir-code-catalogue/1" "name-codec" "lean-typed-name-prefix/1"
                   "source-index-sha256" source-pin "data-file" "catalogue.dat"
                   "data-sha256" (hex (digest data)) "count" (count entries) "record-bytes" 64
                   "sort" "unsigned-name-sha256-then-row-sha256"}
         manifest-bytes (utf8 (json/write-str manifest))
         manifest-path (io/file directory "manifest.json")]
     (write! (io/file directory "catalogue.dat") data)
     (write! manifest-path manifest-bytes)
     {:manifest manifest-path :directory directory :a a :b b :entries entries
      :options {:expected-manifest-sha256 (hex (digest manifest-bytes))
                :expected-source-index-sha256 source-pin :cas-root directory}})))
(defn- open-fixture [{:keys [manifest options]}] (catalogue/open manifest options))

(deftest exact-name-codec-python-golden-vectors
  (doseq [[name expected]
          [[["anonymous"] "00"]
           [["str" ["anonymous"] ""] "000100000000"]
           [["num" ["anonymous"] "0"] "00020000000130"]
           [["str" ["num" ["anonymous"] "12"] "λ"] "00020000000231320100000002cebb"]]]
    (is (= expected (hex (catalogue/typed-name-bytes name))))
    (is (= expected (hex (catalogue/typed-name-bytes (java-lists name))))))
  (is (not= (hex (catalogue/typed-name-bytes ["str" ["anonymous"] "1"]))
            (hex (catalogue/typed-name-bytes ["num" ["anonymous"] "1"]))))
  (is (not= (hex (catalogue/typed-name-bytes ["str" ["anonymous"] "é"]))
            (hex (catalogue/typed-name-bytes ["str" ["anonymous"] "é"]))))
  (doseq [name [[] ["anonymous" 0] ["num" ["anonymous"] 0]
                ["num" ["anonymous"] "01"] ["num" ["anonymous"] "-1"]
                ["str" ["anonymous"] (String. (char-array [(char 0xd800)]))]
                ["str" ["anonymous"] (apply str (repeat 1048577 "a"))]]]
    (is (thrown? Exception (catalogue/typed-name-bytes name)))))

(deftest tiny-exact-lookup-missing-close-and-lightweight-token
  (with-directory
    (fn [directory]
      (let [fixture (fixture! directory) c (open-fixture fixture)]
        (try
          (doseq [{:keys [row sha]} (:entries fixture)]
            (is (= {:name (get row "name") :sha256 sha :row row}
                   (catalogue/lookup c (get row "name")))))
          (is (nil? (catalogue/lookup c ["str" ["anonymous"] "missing"])))
          (let [token (catalogue/source-token c)]
            (is (= source-pin (:source-index-sha256 token)))
            (is (every? keyword? (keys token)))
            (is (every? #(or (string? %) (integer? %)) (vals token)))
            (is (= 2 (:count token))))
          (is (= 2 (get (catalogue/descriptor c) "count")))
          (catalogue/close! c)
          (catalogue/close! c)
          (is (thrown-with-msg? Exception #"closed" (catalogue/lookup c ["anonymous"])))
          (is (thrown-with-msg? Exception #"closed" (catalogue/source-token c)))
          (finally (catalogue/close! c)))))))

(deftest authenticated-collision-range-compares-exact-name
  (with-directory
    (fn [directory]
      (let [fixture (fixture! directory true) {:keys [a b]} fixture]
        (is (neg? (compare (:sha b) (:sha a))))
        (with-open [c (open-fixture fixture)]
          (is (= (:sha a) (:sha256 (catalogue/lookup c (get (:row a) "name")))))
          ;; Both accepted records use A's key. B is not returned under its own key.
          (is (nil? (catalogue/lookup c (get (:row b) "name")))))
        ;; Corrupt B: proves candidate B was read before the matching A record.
        (write! (io/file directory "declarations" (str (:sha b) ".json")) (utf8 "{}"))
        (with-open [c (open-fixture fixture)]
          (is (thrown-with-msg? Exception #"row hash mismatch"
                                (catalogue/lookup c (get (:row a) "name")))))))))

(deftest rejected-manifest-source-data-and-body-pins
  (with-directory
    (fn [directory]
      (let [{:keys [manifest options a] :as fixture} (fixture! directory)]
        (is (thrown-with-msg? Exception #"Manifest hash mismatch"
                              (catalogue/open manifest (assoc options :expected-manifest-sha256 source-pin))))
        (is (thrown-with-msg? Exception #"manifest"
                              (catalogue/open manifest (assoc options :expected-source-index-sha256
                                                              (apply str (repeat 64 "2"))))))
        (with-open [c (catalogue/open manifest (assoc options :max-blob-bytes 1))]
          (is (thrown-with-msg? Exception #"read bound" (catalogue/lookup c (get (:row a) "name")))))
        (with-open [c (open-fixture fixture)]
          (write! (io/file directory "declarations" (str (:sha a) ".json")) (utf8 "{}"))
          (is (thrown-with-msg? Exception #"row hash mismatch" (catalogue/lookup c (get (:row a) "name")))))
        ;; Flip the last row-hash byte; key order and length remain valid.
        (let [file (io/file directory "catalogue.dat") data (Files/readAllBytes (.toPath file))]
          (aset-byte data (dec (alength data)) (unchecked-byte (bit-xor 1 (aget data (dec (alength data))))))
          (write! file data))
        (is (thrown-with-msg? Exception #"data hash mismatch" (open-fixture fixture)))))))

(deftest ordinary-data-path-replacement-rejects-hit-and-absence
  (doseq [absent? [false true]]
    (with-directory
      (fn [directory]
        (let [{:keys [a] :as fixture} (fixture! directory)]
          (with-open [c (open-fixture fixture)]
            (let [replacement (io/file directory "replacement.dat")
                  current (io/file directory "catalogue.dat")]
              ;; A different length guarantees detection even where fileKey is unavailable.
              (write! replacement (byte-array 65))
              (Files/move (.toPath replacement) (.toPath current)
                          (into-array java.nio.file.CopyOption [StandardCopyOption/REPLACE_EXISTING])))
            (is (thrown-with-msg? Exception #"file changed" (catalogue/source-token c)))
            (is (thrown-with-msg? Exception #"file changed"
                                  (catalogue/lookup c (if absent? ["str" ["anonymous"] "absent"]
                                                         (get (:row a) "name")))))))))))

(deftest replacement-between-initial-check-and-result-rejects-hits-and-misses
  (doseq [absent? [false true]]
    (with-directory
      (fn [directory]
        (let [{:keys [a] :as fixture} (fixture! directory)
              original-live @#'ansatz.research.ir.catalogue/live!
              replaced (atom false)]
          (with-open [c (open-fixture fixture)]
            (with-redefs-fn
              {#'ansatz.research.ir.catalogue/live!
               (fn [resource]
                 (original-live resource)
                 ;; Deterministically interleave an external file replacement
                 ;; after the initial stamp check. The open channel is still valid.
                 (when (compare-and-set! replaced false true)
                   (let [replacement (io/file directory "during-lookup.dat")]
                     (write! replacement (byte-array 65))
                     (Files/move (.toPath replacement) (.toPath (io/file directory "catalogue.dat"))
                                 (into-array java.nio.file.CopyOption [StandardCopyOption/REPLACE_EXISTING])))))}
              #(is (thrown-with-msg? Exception #"file changed"
                    (catalogue/lookup c (if absent? ["str" ["anonymous"] "absent"]
                                                  (get (:row a) "name"))))))))))))

(defn check! [] (run-tests 'java-ir-catalogue-checks))
