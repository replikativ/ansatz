(ns prototype.runtime-string-posof-test
  (:require [prototype.runtime-string :as runtime]
            #?(:clj [clojure.test :refer [deftest is]]
               :cljs [cljs.test :refer-macros [deftest is]])))

(deftest posof-matches-native-exported-lean-implementation
  ;; Native/RuntimeStringOracle.c verifies these directly against pinned
  ;; lean_string_posof, exported by Init/Data/String/Search.lean:194–196.
  ;; Missing characters return end byte offset, not an Option or a character index.
  (doseq [[s cp expected] [["" 10 0] ["abc" 10 3] ["a\nb\n" 10 1]
                            ["é😀\nλ" 10 6] ["é😀\nλ" 233 0]
                            ["é😀\nλ" 128512 2] ["é😀\nλ" 955 7]
                            ["é😀\nλ" 90 9] ["a\u0000b" 0 1]
                            ["😀é😀" 128512 0] ["𐀀" 57344 4]
                            ["x\r\ny" 10 2]]]
    (let [world {:test :unchanged}
          [after result] (runtime/evaluate {} world "lean_string_posof" [s cp])]
      (is (= world after))
      (is (= expected result)))))

(deftest posof-rejects-invalid-scalar-values-and-abi
  (doseq [cp [-1 55296 57343 1114112 0.5]]
    (is (thrown? #?(:clj clojure.lang.ExceptionInfo :cljs js/Error)
          (runtime/evaluate {} nil "lean_string_posof" ["abc" cp]))))
  (is (thrown? #?(:clj clojure.lang.ExceptionInfo :cljs js/Error)
        (runtime/evaluate {} nil "lean_string_posof"
                          [#?(:clj (str (char 55296)) :cljs (js/String.fromCharCode 55296)) 10])))
  (is (thrown-with-msg? #?(:clj clojure.lang.ExceptionInfo :cljs js/Error) #"arity"
        (runtime/evaluate {} nil "lean_string_posof" ["abc"]))))

#?(:cljs (defn -main [] (cljs.test/run-tests 'prototype.runtime-string-posof-test)))
#?(:cljs (set! *main-cli-fn* -main))
