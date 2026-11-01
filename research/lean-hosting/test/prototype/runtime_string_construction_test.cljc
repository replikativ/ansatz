(ns prototype.runtime-string-construction-test
  (:require [prototype.runtime-string :as string]
            #?(:clj [clojure.test :refer [deftest is]]
               :cljs [cljs.test :refer-macros [deftest is]])))

(def ops {:ref? (constantly false)})
(defn result [symbol args]
  (let [before {:immutable :world}
        [after value] (string/evaluate ops before symbol args)]
    (is (identical? before after)) value))
(defn clear [] (string/clear-validation-cache!) (string/clear-encoding-cache!))

(deftest growing-push-prefixes-do-not-build-or-rescan-utf8-views
  (clear)
  (try
    (let [seed "A😀"
          output (reduce (fn [s _] (result "lean_string_push" [s 233])) seed (range 2000))
          stats (string/validation-cache-stats)]
      (is (= (str seed (apply str (repeat 2000 "é"))) output))
      (is (= seed "A😀") "the original immutable prefix stays intact")
      (is (= 0 (:misses (string/encoding-cache-stats))))
      (is (= 1 (:scans stats)))
      (is (= (count seed) (:input-code-units stats)))
      (is (<= (:entries stats) (:entry-limit stats)))
      #?(:clj (do (is (= :weak-identity (:retention stats)))
                   (is (= 0 (:retained-code-units stats))))
         :cljs (is (<= (:retained-code-units stats) 2097152)))
      ;; Byte positions and hash operations still build their exact view on
      ;; demand, independently of construction's validity-only cache.
      (is (= 4005 (result "lean_string_utf8_byte_size" [output])))
      (is (= 0 (:misses (string/encoding-cache-stats))))
      (is (= 128512 (result "lean_string_utf8_get" [output 1])))
      (is (= 1 (:misses (string/encoding-cache-stats)))))
    (finally (clear))))

(deftest growing-append-prefixes-only-revalidate-bounded-small-fragments
  (clear)
  (try
    (let [fragment "é😀"
          output (reduce (fn [s _] (result "lean_string_append" [s fragment])) "" (range 1500))
          stats (string/validation-cache-stats)]
      (is (= (apply str (repeat 1500 fragment)) output))
      (is (= "é😀" fragment))
      (is (zero? (:misses (string/encoding-cache-stats))))
      ;; The fixed-size validity cache may evict a repeated fragment. Even then
      ;; it scans the tiny fragment, never the increasingly long output prefix.
      (is (<= (:input-code-units stats) (* 1500 (count fragment)))))
    (finally (clear))))

(deftest construction-rejects-malformed-inputs-without-caching-them
  (clear)
  (try
    (let [high #?(:clj (str (char 55296)) :cljs (js/String.fromCharCode 55296))
          low #?(:clj (str (char 56320)) :cljs (js/String.fromCharCode 56320))]
      (doseq [bad [high low (str "a" high "b") (str low "😀")]
              args [[bad "ok"] ["ok" bad]]]
        (is (thrown-with-msg? #?(:clj clojure.lang.ExceptionInfo :cljs js/Error)
              #"Malformed host Unicode" (result "lean_string_append" args))))
      (doseq [bad [high low]]
        (dotimes [_ 2]
          (is (thrown-with-msg? #?(:clj clojure.lang.ExceptionInfo :cljs js/Error)
                #"Malformed host Unicode" (result "lean_string_push" [bad 65])))))
      ;; Appending malformed halves must not accidentally repair them.
      (is (thrown? #?(:clj clojure.lang.ExceptionInfo :cljs js/Error)
            (result "lean_string_append" [high low])))
      (doseq [cp [55296 57343 1114112]]
        (is (thrown-with-msg? #?(:clj clojure.lang.ExceptionInfo :cljs js/Error)
              #"Invalid Unicode scalar" (result "lean_string_push" ["ok" cp])))))
    (finally (clear))))

(deftest validated-constructors-reuse-validity-without-forcing-position-views
  (clear)
  (try
    (let [utf8 (string/from-utf8 [195 169 240 159 152 128])
          number (result "lean_string_of_usize" [123])]
      (is (= "é😀123!" (-> (result "lean_string_append" [utf8 number])
                           (vector 33) (#(result "lean_string_push" %)))))
      (is (= 0 (:scans (string/validation-cache-stats))))
      (is (= 0 (:misses (string/encoding-cache-stats)))))
    (finally (clear))))

(deftest count-queries-on-growing-strings-use-derived-native-header-summaries
  (clear)
  (try
    (let [output
          (reduce (fn [s i]
                    (let [appended (result "lean_string_append" [s "é\u0000"])
                          pushed (result "lean_string_push" [appended 128512])]
                      (is (= (* 7 (inc i)) (result "lean_string_utf8_byte_size" [pushed])))
                      (is (= (* 3 (inc i)) (result "lean_string_length" [pushed])))
                      pushed)) "" (range 1000))
          stats (string/validation-cache-stats)]
      (is (= 7000 (result "lean_string_utf8_byte_size" [output])))
      (is (= 3000 (result "lean_string_length" [output])))
      (is (= 0 (:misses (string/encoding-cache-stats))))
      (is (< (:input-code-units stats) 1000))
      (is (<= (:entries stats) (:entry-limit stats))))
    (finally (clear))))

(deftest summary-only-counts-preserve-unicode-boundaries-and-reject-malformed-input
  (clear)
  (try
    (doseq [[s bytes scalars] [["" 0 0] ["\u0000" 1 1] ["A\u0000éλ😀" 10 5]
                               ["😀é𐀀" 10 3] ["\uFEFF\uFFFF" 6 2]
                               [#?(:clj (String. (Character/toChars 1114111))
                                   :cljs (js/String.fromCodePoint 1114111)) 4 1]]]
      (is (= bytes (result "lean_string_utf8_byte_size" [s])))
      (is (= scalars (result "lean_string_length" [s]))))
    (doseq [bad [#?(:clj (str (char 55296)) :cljs (js/String.fromCharCode 55296))
                 #?(:clj (str (char 56320)) :cljs (js/String.fromCharCode 56320))]
            symbol ["lean_string_utf8_byte_size" "lean_string_length"]]
      (is (thrown-with-msg? #?(:clj clojure.lang.ExceptionInfo :cljs js/Error)
            #"Malformed host Unicode" (result symbol [bad]))))
    (is (= 0 (:misses (string/encoding-cache-stats))))
    (finally (clear))))

#?(:cljs (defn -main [] (cljs.test/run-tests 'prototype.runtime-string-construction-test)))
#?(:cljs (set! *main-cli-fn* -main))
