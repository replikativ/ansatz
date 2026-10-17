(ns prototype.utf8-validation-test
  (:require [clojure.test :refer [deftest is]]
            [prototype.machine :as m]
            [prototype.runtime-string :as string]))

(def cases
  [[[] true] [[0] true] [[127] true] [[128] false] [[191] false] [[192 128] false]
   [[193 191] false] [[194 128] true] [[223 191] true] [[194] false] [[194 127] false]
   [[224 160 128] true] [[224 159 191] false] [[237 159 191] true] [[237 160 128] false]
   [[237 191 191] false] [[238 128 128] true] [[239 191 191] true]
   [[240 144 128 128] true] [[240 143 191 191] false] [[244 143 191 191] true]
   [[244 144 128 128] false] [[245 128 128 128] false] [[248 136 128 128 128] false]
   [[255] false] [[224] false] [[224 160] false] [[240] false] [[240 144] false]
   [[240 144 128] false] [[97 0 206 187 240 159 152 128] true]
   [[97 240 159 128 97] false]])

(deftest pinned-native-utf8-boundaries
  ;; Same vectors + complete1/2-byte counts are checked by native/UTF8Oracle.c
  ;; against pinned lean_string_validate_utf8, not a replacement decoder.
  (doseq [[bytes expected] cases]
    (is (= expected (string/valid-utf8? bytes)) (str bytes)))
  (is (= 128 (count (filter #(string/valid-utf8? [%]) (range 256)))))
  (is (= 18304 (count (for [a (range 256) b (range 256) :when (string/valid-utf8? [a b])] [a b])))))

(deftest raw-abi-borrows-byte-array-without-changing-world
  (let [ops {:ref? m/ref? :node m/node :release m/release}]
    (doseq [[bytes expected] cases]
      (let [[world value] (m/allocate (m/world {}) :byte-array 248 [])
            world (assoc-in world [:heap (:id value) :bytes] bytes)
            [after result] (string/evaluate ops world "lean_string_validate_utf8" [value])]
        (is (= (if expected 1 0) result))
        (is (identical? world after))
        (is (= 1 (:rc (m/node after value))))))))

(deftest unchecked-construction-preserves-nul-unicode-and-consumes-owned-array
  (let [ops {:ref? m/ref? :node m/node :release m/release}
        bytes [97 0 206 187 240 159 152 128]]
    (doseq [ownership [:unique :shared :persistent]]
      (let [[world value] (m/allocate (m/world {}) :byte-array 248 [])
            world (assoc-in world [:heap (:id value) :bytes] bytes)
            world (case ownership :shared (m/retain world value 1) :persistent (m/mark-persistent world value) world)
            [after text] (string/evaluate ops world "lean_string_from_utf8_unchecked" [value m/erased])]
        (is (= "a\u0000λ😀" text))
        (is (= (= ownership :unique) (not (contains? (:heap after) (:id value)))))
        (when-not (= ownership :unique)
          (is (= (if (= ownership :shared) 1 0) (:rc (m/node after value)))))))
    (doseq [[bad valid?] cases :when (not valid?)]
      (let [[world value] (m/allocate (m/world {}) :byte-array 248 [])
            world (assoc-in world [:heap (:id value) :bytes] bad)]
        (is (thrown-with-msg? clojure.lang.ExceptionInfo #"UTF8 proof violated"
              (string/evaluate ops world "lean_string_from_utf8_unchecked" [value m/erased])))))))
