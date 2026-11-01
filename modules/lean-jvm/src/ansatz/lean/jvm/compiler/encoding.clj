(ns ansatz.lean.jvm.compiler.encoding
  "Bounded exact UTF-8 and JSON parsing shared by the native source producer."
  (:require [clojure.data.json :as json])
  (:import [java.nio.charset StandardCharsets]))
(defn- need [ok message] (when-not ok (throw (ex-info message {:code "ArtifactConflict"}))))
(defn text! [bytes]
  (let [s (String. ^bytes bytes StandardCharsets/UTF_8)]
    (need (java.util.Arrays/equals ^bytes bytes (.getBytes s StandardCharsets/UTF_8)) "Artifact is not exact UTF-8") s))
(defn json! [text]
  (need (and (string? text) (<= (count text) 33554432)) "JSON text exceeds bound")
  ;; Bound recursive JSON parsing before invoking the library reader.
  (loop [characters (seq text) depth 0 quoted false escaped false]
    (need (<= 0 depth 256) "Artifact JSON nesting exceeds bound")
    (when-let [c (first characters)]
      (cond
        escaped (recur (next characters) depth quoted false)
        (and quoted (= c \\)) (recur (next characters) depth quoted true)
        (= (int c) 34) (recur (next characters) depth (not quoted) false)
        quoted (recur (next characters) depth quoted false)
        (contains? #{\{ \[} c) (recur (next characters) (inc depth) false false)
        (contains? #{\} \]} c) (recur (next characters) (dec depth) false false)
        :else (recur (next characters) depth false false))))
  (json/read-str text
    :extra-data-fn
    (fn [value reader]
      (loop [seen 0]
        (let [c (.read ^java.io.Reader reader)]
          (cond
            (= -1 c) value
            (#{32 9 10 13} c)
            (do (need (< seen 33554432) "Trailing JSON whitespace exceeds bound")
                (recur (inc seen)))
            :else (need false "Non-whitespace data follows the JSON value")))))))
