(ns filesystem-nat-source-profile-v2
  "Pure finite source grammar plus bounded filesystem capture. Metadata is input
   description only; actual original frontend observations remain required."
  (:require [prototype.project-source :as project-source])
  (:import [java.nio.file Path]))
(def prefix "prelude\nimport Init.Prelude\n")
(def max-source-bytes 16384)
(defn- need [ok message] (when-not ok (throw (ex-info message {:profile :filesystem-nat-identities-v2}))))
(defn sha256 [^String text]
  (apply str (map #(format "%02x" (bit-and 255 %))
                 (.digest (java.security.MessageDigest/getInstance "SHA-256") (.getBytes text "UTF-8")))))
(def ^:private reserved
  #{"_" "def" "theorem" "axiom" "opaque" "abbrev" "example" "instance" "class"
    "structure" "inductive" "where" "let" "in" "if" "then" "else" "match" "with"
    "do" "return" "by" "fun" "forall" "end" "namespace" "section" "import"
    "prelude" "module" "public" "private" "protected" "unsafe" "partial"
    "noncomputable" "mutual" "deriving" "initialize" "builtin_initialize"
    "set_option" "open" "export" "attribute" "variable" "universe" "Type" "Prop" "Sort"})
(def ^:private definition-pattern
  #"def ([A-Za-z_][A-Za-z0-9_]{0,63}) \(([A-Za-z_][A-Za-z0-9_]{0,63}) : Nat\) : Nat := ([A-Za-z_][A-Za-z0-9_]{0,63})\n")
(defn parse-profile
  "Accept only the literal Prelude header and 1..16 complete identity lines.
   All accepted characters are ASCII, so character and UTF-8 offsets coincide.
   :start/:end describe the original parser positions, including trailing LF."
  [text]
  (need (and (string? text) (<= (count text) max-source-bytes)
             (.startsWith ^String text prefix)) "Expected bounded exact legacy Prelude source")
  (let [matcher (re-matcher definition-pattern text) end (count text)
        commands (loop [pos (count prefix) commands [] names #{}]
                   (if (= pos end)
                     (do (need (<= 1 (count commands) 16) "Expected 1..16 definitions") commands)
                     (do
                       (need (< (count commands) 16) "Definition count bound")
                       (.region matcher pos end)
                       (need (.lookingAt matcher) "Unsupported source grammar")
                       (let [root (.group matcher 1) binder (.group matcher 2) body (.group matcher 3)
                             next-pos (.end matcher) index (count commands)]
                         (need (and (= binder body) (not (reserved root)) (not (reserved binder))) "Expected independent identity identifiers")
                         (need (not (contains? names root)) "Duplicate definition Name")
                         (recur next-pos
                           (conj commands {:action :definition :index index :root root :binder binder :start pos :end next-pos
                                           :previous-start (if (zero? index) pos (:start (peek commands)))
                                           :next-start next-pos :baseline-count index :observed-count (inc index)})
                           (conj names root))))))]
    {:profile "legacy-private-filesystem-nat-identities/2" :text text
     :sha256 (sha256 text) :byte-count end :header-end (count prefix)
     :command-count (count commands) :commands commands
     :eof {:action :eof :index (count commands) :root nil :binder nil
           :start end :end end :next-start end :previous-start (:start (peek commands))
           :baseline-count (count commands) :observed-count (inc (count commands))}}))
(defn captured-profile
  "Snapshot bounded project-source capture fields; never interpret a digest or
   host map as compiler, artifact, or checked-declaration authority."
  [captured]
  (need (map? captured) "Captured source map required")
  (let [text (:text captured) profile (parse-profile text) filename (:path captured)
        module (:module captured)]
    (need (and (or (instance? Path filename) (string? filename)) (seq (str filename))) "Captured filename required")
    (need (and (= (:sha256 profile) (:sha256 captured)) (= (:byte-count profile) (:byte-count captured))) "Captured source digest/size differ")
    (need (and (vector? module) (<= 1 (count module) 256)
               (every? #(and (string? %) (<= 1 (count %) 16384) (not (re-find #"[.\\/\u0000]" %))) module)) "Captured module segments required")
    (assoc profile :filename (str filename) :module (mapv identity module))))
(defn capture-source!
  "Use the tracked bounded filesystem reader, then validate this finite profile.
   Compile :text and use (str :path) as filename; do not reopen the file."
  [provider module]
  (need (and (map? provider) (integer? (:max-bytes provider)) (<= 1 (:max-bytes provider) max-source-bytes)) "Filesystem source limit must be 1..16384 bytes")
  (let [captured (project-source/capture-source provider module)]
    (captured-profile captured)
    captured))

(def ^:private arithmetic-pattern
  #"def ([A-Za-z_][A-Za-z0-9_]{0,63}) \(([A-Za-z_][A-Za-z0-9_]{0,63}) : Nat\) : Nat := (?:([A-Za-z_][A-Za-z0-9_]{0,63})( \+ 1)?|Nat\.add ([A-Za-z_][A-Za-z0-9_]{0,63}) 1)\n")
(defn parse-arithmetic-profile
  "Accept only the literal Prelude header and 1..16 complete identity or add-one lines.
   All accepted characters are ASCII, so character and UTF-8 offsets coincide.
   :start/:end describe the original parser positions, including trailing LF."
  [text]
  (need (and (string? text) (<= (count text) max-source-bytes)
             (.startsWith ^String text prefix)) "Expected bounded exact legacy Prelude source")
  (let [matcher (re-matcher arithmetic-pattern text) end (count text)
        commands (loop [pos (count prefix) commands [] names #{}]
                   (if (= pos end)
                     (do (need (<= 1 (count commands) 16) "Expected 1..16 definitions") commands)
                     (do
                       (need (< (count commands) 16) "Definition count bound")
                       (.region matcher pos end)
                       (need (.lookingAt matcher) "Unsupported source grammar")
                       (let [root (.group matcher 1) binder (.group matcher 2) body (or (.group matcher 3) (.group matcher 5)) operation (if (or (.group matcher 4) (.group matcher 5)) :add-one :identity)
                             next-pos (.end matcher) index (count commands)]
                         (need (and (= binder body) (not (reserved root)) (not (reserved binder))) "Expected independent identity identifiers")
                         (need (not (contains? names root)) "Duplicate definition Name")
                         (recur next-pos
                           (conj commands {:action :definition :operation operation :index index :root root :binder binder :start pos :end next-pos
                                           :previous-start (if (zero? index) pos (:start (peek commands)))
                                           :next-start next-pos :baseline-count index :observed-count (inc index)})
                           (conj names root))))))]
    {:profile "legacy-private-filesystem-nat-arithmetic/3" :text text
     :sha256 (sha256 text) :byte-count end :header-end (count prefix)
     :command-count (count commands) :commands commands
     :eof {:action :eof :index (count commands) :root nil :binder nil
           :start end :end end :next-start end :previous-start (:start (peek commands))
           :baseline-count (count commands) :observed-count (inc (count commands))}}))

(defn captured-arithmetic-profile
  "Snapshot bounded project-source capture fields; never interpret a digest or
   host map as compiler, artifact, or checked-declaration authority."
  [captured]
  (need (map? captured) "Captured source map required")
  (let [text (:text captured) profile (parse-arithmetic-profile text) filename (:path captured)
        module (:module captured)]
    (need (and (or (instance? Path filename) (string? filename)) (seq (str filename))) "Captured filename required")
    (need (and (= (:sha256 profile) (:sha256 captured)) (= (:byte-count profile) (:byte-count captured))) "Captured source digest/size differ")
    (need (and (vector? module) (<= 1 (count module) 256)
               (every? #(and (string? %) (<= 1 (count %) 16384) (not (re-find #"[.\\/\u0000]" %))) module)) "Captured module segments required")
    (assoc profile :filename (str filename) :module (mapv identity module))))
