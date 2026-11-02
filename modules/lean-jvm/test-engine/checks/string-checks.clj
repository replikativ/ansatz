(ns java-ir-string-checks
  "Original wrappers and byte-position semantics over valid immutable Strings."
  (:require [clojure.test :refer [deftest is run-tests]]
            [clojure.data.json :as json] [clojure.edn :as edn]
            [java-ir-baseline :as j] [java-ir-baseline-checks :as c]
            [lean-compatibility-corpus :as corpus]))
(def ^:dynamic *basis* nil)
(def fixture "test/fixtures/java-string-runtime/original-rows.json")
(def supported-symbols
  #{"lean_string_utf8_byte_size" "lean_string_append" "lean_string_push" "lean_string_mk"
    "lean_string_utf8_get_fast" "lean_string_utf8_next_fast" "lean_string_utf8_at_end"
    "lean_string_utf8_get" "lean_string_utf8_next" "lean_string_utf8_prev" "lean_string_is_valid_pos"
    "lean_string_utf8_extract" "lean_string_dec_eq" "lean_string_dec_lt" "lean_string_compare"
    "lean_string_get_byte_fast" "lean_string_contains" "lean_string_length" "lean_string_utf8_set"
    "lean_string_memcmp" "lean_substring_beq" "lean_string_posof" "lean_string_offsetofpos" "lean_string_pushn"})
(defn originals [] (json/read-str (slurp fixture)))
(defn selected-rows []
  (let [rows (mapv #(get % "row") (originals))
        names (set (for [r rows :when (contains? supported-symbols
                                       (get-in r ["ir" "extern" "ext" "entries" 0 "standard" "fn"]))]
                     (get r "name")))]
    (filterv (fn [r] (let [n (get r "name")]
                      (or (contains? names n)
                          (and (= "_boxed" (last n)) (contains? names (second n)))))) rows)))
(defn context [] (assoc *basis* :program (j/invoke-static (:prepare *basis*) [(selected-rows)])))
(defn invoke [ctx engine label args] (j/call ctx engine (str label "._boxed") args))
(defn raw [ctx engine op s p] (invoke ctx engine (str "String.Pos.Raw." op) [s p]))
(defn utf8 [^String s] (.getBytes s java.nio.charset.StandardCharsets/UTF_8))
(def huge (.shiftLeft java.math.BigInteger/ONE 80))

(deftest original-fixture-and-supported-subset-have-exact-abis
  (let [manifest (edn/read-string (slurp "test/fixtures/java-string-runtime/provenance.edn"))]
    (is (= (:fixture-sha256 manifest) (corpus/sha256 fixture)))
    (is (= 62 (count (originals)))) (is (= 60 (count (selected-rows))))
    (doseq [row (selected-rows) :when (get-in row ["ir" "extern"])]
      (is (string? (j/invoke-static (.getMethod ^Class (:class *basis*) "validateExternAbi"
                                                (into-array Class [java.util.Map])) [row]))))))

(deftest valid-and-invalid-byte-positions-match-native-safe-domain
  (let [ctx (context) engine (j/machine ctx)]
    (try
      (doseq [s ["" "ascii" "a\u0000b" "éλ" "\uE000𐀀😀"]
              :let [chars (vec (.toArray (.codePoints ^String s)))
                    widths (mapv #(alength ^bytes (utf8 (String. (Character/toChars (int %))))) chars)
                    starts (vec (butlast (reductions + 0 widths)))
                    ends (vec (reductions + 0 widths)) length (last ends)
                    by-start (zipmap starts chars) by-width (zipmap starts widths)]
              p (range (+ length 3))]
        (is (= (if (>= p length) 1 0) (raw ctx engine "atEnd" s p)))
        (is (= (get by-start p 65) (raw ctx engine "get" s p)))
        (is (= (+ p (get by-width p 1)) (raw ctx engine "next" s p)))
        (is (= (cond (zero? p) 0 (> p length) (dec p)
                     :else (last (filter #(< % p) ends))) (raw ctx engine "prev" s p)))
        (is (= (if (some #{p} ends) 1 0) (raw ctx engine "isValid" s p)))
        (when (< p length)
          (is (= (Byte/toUnsignedInt (aget ^bytes (utf8 s) p))
                 (invoke ctx engine "String.getUTF8Byte" [s p 0]))))
        (when (contains? by-start p)
          (is (= (get by-start p) (invoke ctx engine "String.Pos.Raw.get'" [s p 0])))
          (is (= (+ p (get by-width p)) (invoke ctx engine "String.Pos.Raw.next'" [s p 0])))))
      (finally (j/close! ctx engine)))))

(deftest huge-positions-do-not-wrap-or-truncate
  (let [ctx (context) engine (j/machine ctx)]
    (try
      (doseq [s ["" "é😀"] p [Long/MAX_VALUE (.add java.math.BigInteger/ONE (biginteger Long/MAX_VALUE)) huge]]
        (is (= 1 (raw ctx engine "atEnd" s p)))
        (is (= 65 (raw ctx engine "get" s p)))
        (is (= (inc' p) (raw ctx engine "next" s p)))
        (is (= (dec p) (raw ctx engine "prev" s p)))
        (is (= 0 (raw ctx engine "isValid" s p))))
      (finally (j/close! ctx engine)))))

(deftest extraction-uses-byte-boundaries-and-native-invalid-end-policy
  (let [ctx (context) engine (j/machine ctx) s "aé😀z"]
    (try
      (doseq [[begin end expected] [[0 1 "a"] [1 3 "é"] [3 7 "😀"] [7 8 "z"]
                                  [1 2 "é😀z"] [2 7 ""] [8 9 ""] [3 1 ""]
                                  [3 999 "😀z"] [0 huge s] [huge 0 s]
                                  [Long/MAX_VALUE Long/MAX_VALUE ""]]]
        (is (= expected (invoke ctx engine "String.Pos.Raw.extract" [s begin end]))))
      (finally (j/close! ctx engine)))))

(deftest equality-and-order-use-unsigned-utf8-and-include-embedded-nul
  (let [ctx (context) engine (j/machine ctx)]
    (try
      (doseq [[a b order] [["" "" 1] ["a" "b" 0] ["b" "a" 2] ["a" "aa" 0]
                         ["a\u0000b" "a\u0000c" 0] ["é" "é" 2]
                         ["𐀀" "\uE000" 2] ["😀" "😀" 1]]]
        (is (= order (invoke ctx engine "String.compare" [a b])))
        (is (= (if (= order 1) 1 0) (invoke ctx engine "String.decEq" [a b])))
        (is (= (if (= order 0) 1 0) (invoke ctx engine "String.decidableLT" [a b]))))
      (finally (j/close! ctx engine)))))

(deftest replacement-length-and-char-membership-use-unicode-scalars
  (let [ctx (context) engine (j/machine ctx) s "aé😀z"]
    (try
      (is (= 4 (invoke ctx engine "String.Internal.length" [s])))
      (is (= 8 (invoke ctx engine "String.utf8ByteSize" [s])))
      (is (= 1 (invoke ctx engine "String.Internal.contains" [s 128512])))
      (is (= 0 (invoke ctx engine "String.Internal.contains" [s 0])))
      (doseq [[position cp expected] [[1 88 "aX😀z"] [3 233 "aééz"]
                                    [0 0 "\u0000é😀z"] [2 88 s] [8 88 s] [huge 88 s]]]
        (is (= expected (invoke ctx engine "String.Pos.Raw.set" [s position cp]))))
      (finally (j/close! ctx engine)))))
(defn check! [basis] (binding [*basis* basis] (run-tests 'java-ir-string-checks)))
