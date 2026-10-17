(ns prototype.runtime-string-test
  (:require [clojure.test :refer [deftest is]]
            [prototype.machine :as m]
            [prototype.runtime-string :as runtime]))

(def ops {:ref? m/ref? :node m/node :release m/release})
(defn result [symbol args] (second (runtime/evaluate ops (m/world {}) symbol args)))

(deftest utf8-positions-match-pinned-native-c-oracle
  ;; native/RuntimeStringOracle.c calls the installed 4.33.1 runtime directly.
  (let [s "é😀Z"
        get-cps [233 65 128512 65 65 65 90 65 65 65]
        next-pos [2 2 6 4 5 6 7 8 9 10]]
    (is (= 7 (result "lean_string_utf8_byte_size" [s])))
    (is (= 3 (result "lean_string_length" [s])))
    (doseq [p (range 10)]
      (is (= (nth get-cps p) (result "lean_string_utf8_get" [s p])))
      (is (= (nth next-pos p) (result "lean_string_utf8_next" [s p])))
      (is (= (if (>= p 7) 1 0) (result "lean_string_utf8_at_end" [s p])))
      (is (= (if (contains? #{0 2 6 7} p) 1 0) (result "lean_string_is_valid_pos" [s p]))))
    (is (= [195 169 240 159 152 128 90]
           (mapv #(result "lean_string_get_byte_fast" [s % m/erased]) (range 7))))
    (is (= 128512 (result "lean_string_utf8_get_fast" [s 2 m/erased])))
    (is (= 6 (result "lean_string_utf8_next_fast" [s 2 m/erased])))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"precondition"
          (result "lean_string_utf8_get_fast" [s 7 m/erased]))))
  (is (= 9223372036854775809N
         (result "lean_string_utf8_next" ["" 9223372036854775808N]))))

(deftest extraction-and-comparison-use-byte-boundaries
  (is (= "😀" (result "lean_string_utf8_extract" ["é😀Z" 2 6])))
  (is (= "" (result "lean_string_utf8_extract" ["é😀Z" 1 6])))
  (is (= "😀Z" (result "lean_string_utf8_extract" ["é😀Z" 2 3])))
  (is (= "😀Z" (result "lean_string_utf8_extract" ["é😀Z" 2 100])))
  (is (= "" (result "lean_string_utf8_extract" ["é😀Z" 7 100])))
  (is (= "é😀Z" (result "lean_string_utf8_extract" ["é😀Z" 0 9223372036854775808N])))
  ;; JVM compareTo orders surrogate U+10000 before U+E000; Lean compares UTF8.
  (is (= [0 1 2] [(result "lean_string_compare" ["" "𐀀"])
                  (result "lean_string_compare" ["" ""])
                  (result "lean_string_compare" ["𐀀" ""])]))
  (is (= 1 (result "lean_string_dec_lt" ["a" "aa"])))
  (is (= 1 (result "lean_string_dec_eq" ["a\u0000b" "a\u0000b"])))
  (is (= 1 (result "lean_string_memcmp" ["é😀Z" "X😀Y" 2 1 4 m/erased m/erased])))
  (is (thrown-with-msg? clojure.lang.ExceptionInfo #"precondition"
        (result "lean_string_memcmp" ["x" "y" 0 0 2 m/erased m/erased]))))

(deftest exact-native-hashes-and-mixing
  (doseq [[s expected] [["" 9877294847684254529N]
                        ["a" 15917291556903334389N]
                        ["abcdefg" 934485623504580153N]
                        ["abcdefgh" 4343876127666658534N]
                        ["abcdefghi" 4853633868021991863N]
                        ["é😀Z" 6873531063907902072N]
                        ["" 6385641516529775551N]
                        ["𐀀" 5942749834094437470N]]]
    (is (= expected (result "lean_string_hash" [s]))))
  (is (= 3866779316627607737N (result "lean_uint64_mix_hash" [0 0])))
  (is (= 16582581243253999004N (result "lean_uint64_mix_hash" [1 2])))
  (is (= 5932200832493835139N
         (result "lean_uint64_mix_hash" [18446744073709551615N 18446744073709551615N]))))

(deftest constructing-strings-and-consuming-list-substring-objects
  (is (= "é😀" (result "lean_string_append" ["é" "😀"])))
  (is (= "é😀" (result "lean_string_push" ["é" 128512])))
  (is (= 1 (result "lean_string_contains" ["é😀" 128512])))
  (is (= 0 (result "lean_string_contains" ["é😀" 65])))
  (is (= "18446744073709551615" (result "lean_string_of_usize" [18446744073709551615N])))
  (let [[world list] (m/guest-list (m/world {}) [233 128512 90])
        [world string] (runtime/evaluate ops world "lean_string_mk" [list])]
    (is (= "é😀Z" string))
    (is (empty? (:heap world))))
  (let [[world a] (m/allocate (m/world {}) :ctor 0 ["é😀Z" 2 6])
        [world b] (m/allocate world :ctor 0 ["X😀Y" 1 5])
        [world equal] (runtime/evaluate ops world "lean_substring_beq" [a b])]
    (is (= 1 equal))
    (is (empty? (:heap world))))
  (let [[world a] (m/allocate (m/world {}) :ctor 0 ["é😀Z" 1 6])
        [world b] (m/allocate world :ctor 0 ["X😀Y" 6 6])
        [_ equal] (runtime/evaluate ops world "lean_substring_beq" [a b])]
    (is (= 1 equal) "invalid starts are repaired to end; inverted substrings are empty")))

(deftest invalid-host-unicode-and-arity-fail-explicitly
  (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Malformed host Unicode"
        (result "lean_string_utf8_byte_size" [(String. (char-array [(char 55296)]))])))
  (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Invalid Unicode scalar"
        (result "lean_string_push" ["" 55296])))
  (is (thrown-with-msg? clojure.lang.ExceptionInfo #"arity" (result "lean_string_hash" [])))
  (is (thrown-with-msg? clojure.lang.ExceptionInfo #"position"
        (result "lean_string_utf8_get" ["x" -1]))))

(deftest derived-cache-is-bounded-and-follows-access-order
  (runtime/clear-encoding-cache!)
  (try
    ;; Count-only queries now use scalar summaries; exercise an actual position
    ;; operation here to verify the independent full-view cache's LRU contract.
    (doseq [i (range 8)] (result "lean_string_utf8_get" [(str "cache-" i) 0]))
    (result "lean_string_utf8_get" ["cache-0" 0])
    (result "lean_string_utf8_get" ["cache-8" 0])
    (is (= {:entries 8 :bytes 56 :hits 1 :misses 9}
           (select-keys (runtime/encoding-cache-stats) [:entries :bytes :hits :misses])))
    (result "lean_string_utf8_get" ["cache-0" 0])
    (is (= 2 (:hits (runtime/encoding-cache-stats))) "recent entry survives insertion")
    (result "lean_string_utf8_get" ["cache-1" 0])
    (is (= 10 (:misses (runtime/encoding-cache-stats))) "least recent entry was evicted")
    (is (= 8 (:entries (runtime/encoding-cache-stats))))
    (finally (runtime/clear-encoding-cache!))))

(deftest cache-byte-budget-and-oversized-bypass
  (runtime/clear-encoding-cache!)
  (try
    (binding [runtime/*encoding-cache-byte-budget* 12]
      (doseq [s ["abc" "dé" "😀" "123456"]] (result "lean_string_utf8_get" [s 0]))
      (is (= {:entries 2 :bytes 10 :byte-budget 12}
             (select-keys (runtime/encoding-cache-stats) [:entries :bytes :byte-budget])))
      (let [before (select-keys (runtime/encoding-cache-stats) [:entries :bytes])]
        (is (= 109 (result "lean_string_utf8_get" ["abcdefghijklm" 12])))
        (is (= before (select-keys (runtime/encoding-cache-stats) [:entries :bytes])))))
    (finally (runtime/clear-encoding-cache!))))

(deftest cached-and-uncached-unicode-have-identical-guest-behavior
  (let [operations [["lean_string_utf8_byte_size" ["é😀Z"]]
                    ["lean_string_length" ["é😀Z"]]
                    ["lean_string_utf8_get" ["é😀Z" 2]]
                    ["lean_string_utf8_next" ["é😀Z" 2]]
                    ["lean_string_utf8_extract" ["é😀Z" 2 3]]
                    ["lean_string_hash" ["é😀Z"]]]]
    (runtime/clear-encoding-cache!)
    (try
      (let [uncached (binding [runtime/*encoding-cache-byte-budget* 0]
                       (mapv (fn [[symbol args]] (result symbol args)) operations))]
        (is (zero? (:entries (runtime/encoding-cache-stats))))
        (is (= uncached (mapv (fn [[symbol args]] (result symbol args)) operations)))
        (is (pos? (:hits (runtime/encoding-cache-stats))))
        (is (= 1 (:entries (runtime/encoding-cache-stats)))))
      (finally (runtime/clear-encoding-cache!)))))

(deftest derived-cache-can-be-used-concurrently
  (runtime/clear-encoding-cache!)
  (try
    (let [workers (doall (for [_ (range 16)]
                           (future (dotimes [_ 10]
                                     (assert (= 128512 (result "lean_string_utf8_get" ["é😀Z" 2]))))
                                   true)))]
      (is (every? true? (map deref workers)))
      (is (= 1 (:entries (runtime/encoding-cache-stats))))
      (is (= 7 (:bytes (runtime/encoding-cache-stats))))
      (is (= 160 (+ (:hits (runtime/encoding-cache-stats)) (:misses (runtime/encoding-cache-stats))))))
    (finally (runtime/clear-encoding-cache!))))
