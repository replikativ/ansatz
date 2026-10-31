(ns ansatz.research.ir.bootstrap.artifacts
  "Explicit caller-pinned bootstrap metadata and file leases. No catalogue,
   SourceBinding, engine, store or guest capability is issued here."
  (:require [clojure.data.json :as json] [clojure.java.io :as io]
            [clojure.string :as str])
  (:import [java.nio.file Files Path LinkOption] [java.nio.charset StandardCharsets CodingErrorAction]
           [java.nio.file.attribute BasicFileAttributes] [java.security MessageDigest]
           [java.util WeakHashMap]))
(def lean-pin "819816b2e0a3bf405af45ae5c7af2491d8f5bee6")
(def profile-id "explicit-prelude-source4-v1")
(deftype Profile [])
(defonce ^:private profiles (WeakHashMap.))
(defn- need [ok message] (when-not ok (throw (ex-info message {:component :source4-artifacts}))))
(defn sha256 [file]
  (let [digest (MessageDigest/getInstance "SHA-256") buffer (byte-array 65536)]
    (with-open [input (io/input-stream file)]
      (loop [] (let [n (.read input buffer)] (when (pos? n) (.update digest buffer 0 n) (recur)))))
    (apply str (map #(format "%02x" (bit-and 255 %)) (.digest digest)))))
(defn- pin? [x] (and (string? x) (boolean (re-matches #"[0-9a-f]{64}" x))))
(defn- id? [x] (and (string? x) (boolean (re-matches #"[a-zA-Z0-9][a-zA-Z0-9_.-]{0,127}" x))))
(defn- relative! [text]
  (need (and (string? text) (<= 1 (count text) 4096)
             (not (str/includes? text (str (char 92))))
             (not (str/includes? text (str (char 0))))
             (not (.isAbsolute (.toPath (io/file text))))
             (every? #(and (seq %) (not (contains? #{"." ".."} %))) (str/split text #"/" -1)))
        "Bounded normalized relative artifact path required")
  text)
(defn- real [file] (.toRealPath (.toPath (io/file file)) (make-array LinkOption 0)))
(defn- stamp [^Path path]
  (need (and (Files/isRegularFile path (into-array LinkOption [LinkOption/NOFOLLOW_LINKS]))
             (not (Files/isSymbolicLink path))) "Regular non-symlink artifact required")
  (let [a (Files/readAttributes path BasicFileAttributes (into-array LinkOption [LinkOption/NOFOLLOW_LINKS]))]
    [(.size a) (.lastModifiedTime a) (.fileKey a)]))
(defn- under! [roots root-id relative]
  (need (and (id? root-id) (contains? roots root-id)) "Unknown explicit artifact root")
  (let [^Path root (get roots root-id) candidate (.resolve root ^String (relative! relative)) path (real (.toFile candidate))]
    (need (and (.startsWith path root) (= path (.normalize candidate))) "Artifact escapes root or uses a symlink alias")
    path))
(defn- bounded-bytes [file maximum]
  (need (and (integer? maximum) (<= 1 maximum (* 32 1024 1024))) "Bounded metadata byte limit required")
  (with-open [input (io/input-stream file)]
    (let [data (.readNBytes input (int (inc maximum)))]
      (need (<= (alength data) maximum) "Metadata file exceeds bound") data)))
(defn- utf8 [data]
  (str (.decode (doto (.newDecoder StandardCharsets/UTF_8)
                  (.onMalformedInput CodingErrorAction/REPORT) (.onUnmappableCharacter CodingErrorAction/REPORT))
                (java.nio.ByteBuffer/wrap data))))
(defn- metadata-bound! [value]
  (loop [todo [[value 0]] visits 0 characters 0]
    (need (and (<= visits 100000) (<= characters (* 8 1024 1024)) (<= (count todo) 100000)) "Profile metadata budget")
    (when (seq todo)
      (let [[x depth] (peek todo) rest (pop todo)]
        (need (<= depth 64) "Profile metadata depth")
        (cond
          (map? x) (recur (into rest (map #(vector % (inc depth)) (mapcat identity x))) (inc visits) characters)
          (vector? x) (recur (into rest (map #(vector % (inc depth)) x)) (inc visits) characters)
          (string? x) (recur rest (inc visits) (+ characters (count x)))
          (or (nil? x) (boolean? x) (integer? x)) (recur rest (inc visits) characters)
          :else (throw (ex-info "Unsupported profile metadata value" {})))))))
(defn- profile-shape! [p]
  (metadata-bound! p)
  (need (every? #{"schema" "profile" "lean-commit" "target" "artifacts" "directories" "runtime"
                  "catalogue" "capture" "overlays" "policies" "lean-source" "layout-directory" "matched"
                  "externs" "evidence" "enabled-admissions" "budgets" "definitions" "models"} (keys p))
        "Unknown bootstrap profile field")
  (need (and (= "ansatz-source4-bootstrap/1" (get p "schema"))
             (= profile-id (get p "profile")) (= lean-pin (get p "lean-commit"))
             (= {"triple" "x86_64-unknown-linux-gnu" "word-bits" 64} (get p "target"))
             (map? (get p "artifacts")) (<= 1 (count (get p "artifacts")) 512)
             (map? (get p "directories")) (<= (count (get p "directories")) 128)
             (vector? (get p "overlays")) (= 4 (count (get p "overlays"))))
        "Unsupported explicit Source4 profile envelope")
  (doseq [[id a] (get p "artifacts")]
    (need (and (id? id) (= #{"root" "path" "sha256" "bytes"} (set (keys a)))
               (id? (get a "root")) (pin? (get a "sha256"))
               (integer? (get a "bytes")) (<= 0 (get a "bytes") (* 512 1024 1024))) "Artifact descriptor differs")
    (relative! (get a "path")))
  (doseq [[id group] (get p "directories")]
    (need (and (id? id) (= #{"root" "path" "files"} (set (keys group))) (id? (get group "root"))
               (vector? (get group "files")) (<= 1 (count (get group "files")) 512)
               (= (count (get group "files")) (count (set (get group "files")))))
          "Explicit directory file-set required")
    (relative! (get group "path"))
    (doseq [file (get group "files")] (need (contains? (get p "artifacts") file) "Directory refers to undeclared file")))
  (need (<= (reduce + 0 (map #(get % "bytes") (vals (get p "artifacts")))) (* 512 1024 1024))
        "Aggregate bootstrap file extent exceeds profile bound")
  p)
(defn- entry [token]
  (locking profiles (or (.get profiles token) (throw (ex-info "Authenticated bootstrap Profile required" {})))))
(defn- same-file! [record]
  (need (and (= (:path record) (real (.toFile ^Path (:path record))))
             (= (:stamp record) (stamp (:path record)))) "Bootstrap artifact file changed or closed")
  record)
(defn- directory-files! [^Path directory expected]
  (with-open [paths (Files/walk directory (int 16) (make-array java.nio.file.FileVisitOption 0))]
    (let [iterator (.iterator paths)]
      (loop [seen #{} entries 0]
        (need (<= entries 8192) "Artifact directory traversal bound")
        (if-not (.hasNext iterator)
          (need (= expected seen) "Artifact directory contains missing or undeclared files")
          (let [^Path path (.next iterator)]
            (need (not (Files/isSymbolicLink path)) "Artifact directory contains a symlink")
            (cond
              (Files/isDirectory path (into-array LinkOption [LinkOption/NOFOLLOW_LINKS]))
              (do (need (< (.getNameCount (.relativize directory path)) 16) "Artifact directory depth bound")
                  (recur seen (inc entries)))
              (Files/isRegularFile path (into-array LinkOption [LinkOption/NOFOLLOW_LINKS]))
              (do (need (contains? expected path) "Artifact directory contains an undeclared file")
                  (recur (conj seen path) (inc entries)))
              :else (throw (ex-info "Unsupported artifact directory entry" {})))))))))
(defn guard! [token]
  (let [s (entry token)]
    (need (= :open (:status s)) "Bootstrap artifact lease is closed")
    (same-file! (:manifest s))
    (doseq [[_ record] (:files s)] (same-file! record))
    token))
(defn authenticate-profile!
  "EXPECTED-SHA is independently supplied; never read it from the profile being
   authenticated. ROOTS maps explicit string IDs to directories. Hashes pin bytes,
   not runtime execution or checking authority. All files preflight before issue."
  [profile-file expected-sha roots]
  (need (and (pin? expected-sha) (map? roots) (<= 1 (count roots) 32)) "Independent profile digest and explicit roots required")
  (let [path (real profile-file) before (stamp path)
        _ (need (<= (first before) 1048576) "Profile exceeds 1 MiB")
        raw (bounded-bytes (.toFile path) 1048576)
        digest (apply str (map #(format "%02x" (bit-and 255 %))
                               (.digest (MessageDigest/getInstance "SHA-256") raw)))
        _ (need (= expected-sha digest) "Independent profile digest mismatch")
        p (profile-shape! (json/read-str (utf8 raw)))
        _ (need (= before (stamp path)) "Profile changed while reading")
        roots (into {} (for [[id root] roots]
                         (do (need (id? id) "Invalid root ID")
                             (let [r (real root)] (need (Files/isDirectory r (make-array LinkOption 0)) "Explicit root is not a directory") [id r]))))
        files (reduce-kv (fn [out id a]
                           (let [file (under! roots (get a "root") (get a "path")) before (stamp file)]
                             (need (and (= (get a "bytes") (first before))
                                        (= (get a "sha256") (sha256 (.toFile file)))
                                        (= before (stamp file))) "Artifact size/digest/stability differs")
                             (assoc out id {:path file :stamp before}))) {} (get p "artifacts"))
        _ (need (= (count files) (count (set (map :path (vals files))))) "Duplicate artifact file aliases")
        directories (into {} (for [[id group] (get p "directories")]
                              (let [dir (under! roots (get group "root") (get group "path"))]
                                (need (Files/isDirectory dir (make-array LinkOption 0)) "Artifact directory absent")
                                (doseq [id (get group "files")]
                                  (need (.startsWith ^Path (:path (get files id)) dir) "Directory file escapes declared group"))
                                (directory-files! dir (set (map #(get-in files [% :path]) (get group "files"))))
                                [id dir])))
        token (Profile.)]
    (locking profiles (.put profiles token {:status :open :description p :manifest {:path path :stamp before}
                                           :roots roots :files files :directories directories}))
    token))
(defn description [token] (guard! token) (:description (entry token)))
(defn file! [token id]
  (let [s (entry (guard! token)) record (get (:files s) id)]
    (need record "Undeclared bootstrap artifact ID") (.toFile ^Path (:path record))))
(defn directory! [token id]
  (let [s (entry (guard! token)) directory (get (:directories s) id)]
    (need directory "Undeclared bootstrap directory ID")
    (directory-files! directory (set (map #(get-in s [:files % :path])
                                          (get-in s [:description "directories" id "files"]))))
    (.toFile ^Path directory)))
(defn root!
  "Explicit non-file resource root, e.g. the CAS. Its contents need the lower
   catalogue's own per-row/index authentication; this accessor grants none."
  [token id]
  (let [s (entry (guard! token)) root (get (:roots s) id)]
    (need root "Undeclared bootstrap root ID") (.toFile ^Path root)))
(defn bytes! [token id maximum]
  (let [data (bounded-bytes (file! token id) maximum) digest (MessageDigest/getInstance "SHA-256")
        actual (apply str (map #(format "%02x" (bit-and 255 %)) (.digest digest data)))
        expected (get-in (entry token) [:description "artifacts" id "sha256"])]
    (need (= expected actual) "Artifact changed during bounded read")
    (guard! token) data))
(defn text! [token id maximum] (utf8 (bytes! token id maximum)))
(defn json! [token id maximum] (json/read-str (text! token id maximum)))
(defn source-reader [token]
  (let [m (get (description token) "lean-source") files (get m "files")]
    (need (and (= lean-pin (get m "commit")) (map? files) (<= 1 (count files) 256)) "Pinned upstream source archive required")
    {:commit lean-pin :read-blob! (fn [relative]
                                  (relative! relative)
                                  (let [id (get files relative)]
                                    (need id "Unlisted upstream source blob")
                                    (bytes! token id (* 4 1024 1024))))}))
(defn close! [token]
  (locking profiles
    (entry token)
    (.put profiles token {:status :closed})) nil)
