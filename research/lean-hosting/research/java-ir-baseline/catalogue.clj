(ns ansatz.research.ir.catalogue
  "Optional host-scoped base-CAS lookup. Never put this resource in an engine fork.
  Publish immutable files: stat guards detect ordinary replacement/rewrites, not a
  malicious host restoring timestamps. Source tokens contain only pinned scalars."
  (:refer-clojure :exclude [open])
  (:require [clojure.data.json :as json])
  (:import (java.io ByteArrayOutputStream Closeable DataOutputStream)
           (java.nio ByteBuffer)
           (java.nio.channels FileChannel)
           (java.nio.charset CodingErrorAction StandardCharsets)
           (java.nio.file Files Path Paths StandardOpenOption LinkOption)
           (java.nio.file.attribute BasicFileAttributes)
           (java.security MessageDigest)
           (java.util Arrays List)))

(def ^:private codec "lean-typed-name-prefix/1")
(defn- fail [message] (throw (ex-info message {:component :java-code-catalogue})))
(defn- require! [predicate message] (when-not predicate (fail message)))
(defn- sha256 [^bytes data] (.digest (MessageDigest/getInstance "SHA-256") data))
(defn- hex [^bytes data] (apply str (map #(format "%02x" (bit-and 255 %)) data)))
(defn- utf8 [^String text]
  (let [encoder (doto (.newEncoder StandardCharsets/UTF_8)
                  (.onMalformedInput CodingErrorAction/REPORT)
                  (.onUnmappableCharacter CodingErrorAction/REPORT))
        buffer (.encode encoder (java.nio.CharBuffer/wrap text))
        result (byte-array (.remaining buffer))]
    (.get buffer result) result))
(defn- text-utf8 [^bytes data]
  (str (.decode (doto (.newDecoder StandardCharsets/UTF_8)
                 (.onMalformedInput CodingErrorAction/REPORT)
                 (.onUnmappableCharacter CodingErrorAction/REPORT))
               (ByteBuffer/wrap data))))

(defn typed-name-bytes
  "Injective prefix-first codec. Numeric leaves are canonical decimal strings."
  ^bytes [name]
  (let [segments
        (loop [current name result [] total 1]
          (require! (and (instance? List current) (pos? (count current))) "Malformed typed Name")
          (if (= "anonymous" (nth current 0))
            (do (require! (= 1 (count current)) "Malformed anonymous Name") result)
            (let [[kind prefix leaf] current]
              (require! (and (= 3 (count current)) (< (count result) 256)
                             (#{"str" "num"} kind) (string? leaf)
                             (or (= kind "str") (re-matches #"0|[1-9][0-9]*" leaf)))
                        "Malformed Name segment or noncanonical numeric leaf")
              ;; Every valid UTF8 encoding has at least as many bytes as UTF16 units.
              ;; Reject over-budget leaves before the encoder allocates its buffer.
              (require! (<= (.length ^String leaf) (- 1048576 total 5))
                        "Encoded Name exceeds bound")
              (let [bytes (utf8 leaf)]
                (require! (<= (+ total 5 (alength bytes)) 1048576) "Encoded Name exceeds bound")
                (recur prefix (conj result [(if (= kind "str") 1 2) bytes])
                       (+ total 5 (alength bytes)))))))
        output (ByteArrayOutputStream.)
        writer (DataOutputStream. output)]
    (.writeByte writer 0)
    (doseq [[kind ^bytes bytes] (rseq segments)]
      (.writeByte writer (int kind)) (.writeInt writer (alength bytes)) (.write writer bytes))
    (require! (<= (.size output) 1048576) "Encoded Name exceeds bound")
    (.toByteArray output)))

(defn- path ^Path [value] (if (instance? Path value) value (Paths/get (str value) (make-array String 0))))
(defn- stamp [^Path file]
  (let [a (Files/readAttributes file BasicFileAttributes (make-array LinkOption 0))]
    [(.size a) (.lastModifiedTime a) (.fileKey a)]))
(defn- bounded-read [^Path file limit]
  (with-open [input (Files/newInputStream file (make-array java.nio.file.OpenOption 0))]
    (let [bytes (.readNBytes input (int (inc limit)))]
      (require! (<= (alength bytes) limit) "File exceeds read bound") bytes)))
(defn- read-at! [^FileChannel channel ^ByteBuffer buffer offset]
  (.clear buffer)
  (loop [position (long offset)]
    (when (.hasRemaining buffer)
      (let [n (.read channel buffer position)]
        (require! (pos? n) "Truncated catalogue data")
        (recur (+ position n)))))
  (.flip buffer) buffer)

(declare close!)
(deftype Catalogue [^FileChannel channel ^Path dataPath ^Path casRoot metadata token originalStamp lock closed maxBlob]
  Closeable (close [this] (close! this)))
(defn close! [^Catalogue catalogue]
  (locking (.-lock catalogue)
    (when (compare-and-set! (.-closed catalogue) false true)
      (.close (.-channel catalogue)))))
(defn- live! [^Catalogue catalogue]
  (require! (not @(.-closed catalogue)) "Catalogue is closed")
  (require! (= (.-originalStamp catalogue) (stamp (.-dataPath catalogue))) "Catalogue file changed"))
(defn source-token [^Catalogue catalogue]
  (locking (.-lock catalogue) (live! catalogue) (.-token catalogue)))
(defn descriptor [^Catalogue catalogue] (.-metadata catalogue))

(defn open
  "Open with independently accepted manifest and original-index SHA256 pins.
  Uses positional reads and a closeable channel, never a retained Name map.
  Data is hashed and sortedness checked through the accepted channel once."
  [manifest-path {:keys [expected-manifest-sha256 expected-source-index-sha256 cas-root max-blob-bytes]
                  :or {max-blob-bytes 8388608}}]
  (doseq [pin [expected-manifest-sha256 expected-source-index-sha256]]
    (require! (and (string? pin) (re-matches #"[0-9a-f]{64}" pin)) "Expected SHA256 pin required"))
  (require! (and (integer? max-blob-bytes) (<= 1 max-blob-bytes 67108864) cas-root) "Invalid blob bound/CAS root")
  (let [manifest-path (.toAbsolutePath (path manifest-path))
        raw (bounded-read manifest-path 65536)
        _ (require! (= expected-manifest-sha256 (hex (sha256 raw))) "Manifest hash mismatch")
        m (json/read-str (text-utf8 raw))
        n (get m "count")
        filename (get m "data-file")
        _ (require! (and (= "java-ir-code-catalogue/1" (get m "schema"))
                         (= codec (get m "name-codec"))
                         (= expected-source-index-sha256 (get m "source-index-sha256"))
                         (= 64 (get m "record-bytes"))
                         (= "unsigned-name-sha256-then-row-sha256" (get m "sort"))
                         (integer? n) (<= 0 n 500000)
                         (= "catalogue.dat" filename)
                         (string? (get m "data-sha256"))
                         (re-matches #"[0-9a-f]{64}" (get m "data-sha256"))) "Unsupported catalogue manifest")
        data-path (.resolve (.getParent manifest-path) ^String filename)
        initial-stamp (stamp data-path)
        channel (FileChannel/open data-path (into-array java.nio.file.OpenOption [StandardOpenOption/READ]))]
    (try
      (require! (= (* 64 n) (.size channel) (first initial-stamp)) "Catalogue length mismatch")
      (let [digest (MessageDigest/getInstance "SHA-256")
            buffer (ByteBuffer/allocate 65536)]
        (loop [offset 0 previous nil]
          (when (< offset (* 64 n))
            (.limit buffer (int (min 65536 (- (* 64 n) offset))))
            ;; read-at! clears the buffer, so use a bounded slice on the final chunk.
            (let [chunk (.slice buffer) _ (read-at! channel chunk offset)
                  bytes (.array buffer) size (.limit chunk)]
              (.update digest bytes 0 size)
              (let [last-record
                    (loop [i 0 prior previous]
                      (if (= i size) prior
                          (do (when prior
                                (require! (<= (Arrays/compareUnsigned ^bytes prior 0 64 ^bytes bytes i (+ i 64)) 0)
                                          "Catalogue records are not sorted"))
                              (recur (+ i 64) (Arrays/copyOfRange bytes i (+ i 64))))))]
                (recur (+ offset size) last-record)))))
        (require! (= (get m "data-sha256") (hex (.digest digest))) "Catalogue data hash mismatch"))
      (require! (= initial-stamp (stamp data-path)) "Catalogue changed during acceptance")
      (Catalogue. channel data-path (.toAbsolutePath (path cas-root)) m
                  {:schema "java-ir-code-source/1" :name-codec codec
                   :manifest-sha256 expected-manifest-sha256
                   :source-index-sha256 expected-source-index-sha256
                   :data-sha256 (get m "data-sha256") :count n}
                  initial-stamp (Object.) (atom false) max-blob-bytes)
      (catch Throwable failure (.close channel) (throw failure)))))

(defn lookup
  "Return nil or {:name exact-typed-Name :sha256 original-row-SHA :row row}.
  Hash collisions scan their complete contiguous range and compare exact Names.
  Every candidate is bounded, raw-byte authenticated and parsed on demand."
  [^Catalogue catalogue name]
  (let [encoded (typed-name-bytes name) wanted (sha256 encoded)
        buffer (ByteBuffer/allocate 64)]
    (locking (.-lock catalogue)
      (live! catalogue)
      (let [channel (.-channel catalogue)
            n (get (.-metadata catalogue) "count")
            read-record (fn [i] (read-at! channel buffer (* 64 (long i))) (.array buffer))
            compare-key (fn [^bytes record] (Arrays/compareUnsigned record 0 32 wanted 0 32))
            first-match (loop [lo 0 hi n]
                          (if (= lo hi) lo
                              (let [mid (quot (+ lo hi) 2)]
                                (if (neg? (compare-key (read-record mid)))
                                  (recur (inc mid) hi) (recur lo mid)))))]
        (let [result
              (loop [i first-match]
          (when (< i n)
            (let [record (read-record i)]
              (when (zero? (compare-key record))
                (let [row-sha (hex (Arrays/copyOfRange ^bytes record 32 64))
                      file (.resolve (.resolve (.-casRoot catalogue) "declarations") (str row-sha ".json"))
                      bytes (bounded-read file (.-maxBlob catalogue))
                      _ (require! (= row-sha (hex (sha256 bytes))) "Original CAS row hash mismatch")
                      row (json/read-str (text-utf8 bytes))
                      actual (get row "name")
                      actual-bytes (typed-name-bytes actual)]
                  (require! (= "decl" (get row "kind")) "CAS row is not a declaration")
                  (if (Arrays/equals encoded actual-bytes)
                    {:name actual :sha256 row-sha :row row}
                    (recur (inc i))))))))]
          (live! catalogue)
          result)))))
