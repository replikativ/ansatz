(ns prototype.project-source
  "Bounded host-only source capture for the explicit string-segment module subset.
   No guest execution, import authority, cache, Lake resolution or .olean loading.
   Package precedence follows Lean.Util.Path at pinned Lean819816. The supported
   module subset deliberately excludes path syntax and dotted Name segments.
   Symlinks escaping the chosen source root are rejected as a host policy."
  (:import [java.nio.file Files Path LinkOption OpenOption]
           [java.nio.charset StandardCharsets]
           [java.util Arrays]
           [java.security MessageDigest]))

(defn- fail [message data] (throw (ex-info message data)))
(defn- path [x] (Path/of (str x) (make-array String 0)))
(defn- real [^Path p] (.toRealPath p (make-array LinkOption 0)))
(defn- exists? [^Path p] (Files/exists p (make-array LinkOption 0)))
(defn- directory? [^Path p] (Files/isDirectory p (make-array LinkOption 0)))
(defn- module! [segments]
  (when-not (and (vector? segments) (<= 1 (count segments) 256)
                (every? #(and (string? %) (<= 1 (count %) 16384)
                              (not (re-find #"[.\\/\u0000]" %))) segments))
    (fail "Module outside the string-segment source profile" {}))
  segments)

(defn provider
  "Capture explicit canonical source roots and a PER-FILE byte limit (1..64 MiB).
   Root order is significant. This is configuration, not an import permission.
   A future Project owns aggregate file/count/dependency/I/O policies."
  [roots max-bytes]
  (when-not (and (vector? roots) (<= 1 (count roots) 256)
                (integer? max-bytes) (<= 1 max-bytes 67108864))
    (fail "Explicit bounded roots and source byte limit required" {}))
  {:roots (mapv #(let [_ (when-not (or (instance? Path %) (and (string? %) (seq %)))
                          (fail "Source roots must be explicit nonempty paths" {}))
                       p (real (path %))]
                  (when-not (directory? p) (fail "Source root is not a directory" {}))
                  p) roots)
   :max-bytes max-bytes})

(defn select-source
  "Select FIRST root owning the package, even when that root lacks the leaf.
   In particular, a missing P.X under root1/P must not fall through to root2/P/X."
  [{:keys [roots]} segments]
  (module! segments)
  (let [pkg (first segments)]
    (when-let [[ordinal root]
               (first (filter (fn [[_ ^Path root]]
                                (or (directory? (.resolve root pkg))
                                    (exists? (.resolve root (str pkg ".lean")))))
                              (map-indexed vector roots)))]
      {:root root :root-index ordinal :module segments
       :path (reduce (fn [^Path p part] (.resolve p ^String part)) root
                     (conj (pop segments) (str (peek segments) ".lean")))})))

(defn capture-source
  "Read at most limit+1 bytes once, decode strictly, keep only immutable content.
   Returned text is the exact immutable UTF-8 snapshot used for later header
   discovery AND compilation; callers must not reopen :path for compilation.
   The digest identifies captured bytes, not a checked module or graph receipt.

   This API assumes a cooperative filesystem: realpath containment precedes
   opening, so hostile concurrent ancestor/symlink replacement is not prevented.
   In-place edits can produce mixed-version bytes. There is no I/O deadline or
   multi-file transaction; a Project must not claim a consistent filesystem view."
  [{:keys [max-bytes] :as provider} segments]
  (let [{:keys [root path] :as selection} (select-source provider segments)]
    (when-not selection (fail "Unknown source package" {:module segments}))
    (when-not (exists? path)
      (fail "Selected package lacks source module" {:module segments :root-index (:root-index selection)}))
    (let [resolved (real path)]
      (when-not (.startsWith ^Path resolved ^Path root)
        (fail "Selected source escapes its explicit root" {:module segments}))
      (when-not (Files/isRegularFile resolved (make-array LinkOption 0))
        (fail "Selected source is not a regular file" {:module segments}))
      (let [bytes (with-open [in (Files/newInputStream resolved (make-array OpenOption 0))]
                    (.readNBytes in (inc max-bytes)))]
        (when (> (alength bytes) max-bytes) (fail "Source exceeds byte limit" {:module segments}))
        (let [text (String. bytes StandardCharsets/UTF_8)
              _ (when-not (Arrays/equals bytes (.getBytes text StandardCharsets/UTF_8))
                  (fail "Source is not valid UTF-8" {:module segments}))
              hash-bytes (.digest (MessageDigest/getInstance "SHA-256") bytes)]
          (assoc selection :path resolved :text text :byte-count (alength bytes)
                 :sha256 (apply str (map #(format "%02x" (bit-and 255 %)) hash-bytes))))))))
