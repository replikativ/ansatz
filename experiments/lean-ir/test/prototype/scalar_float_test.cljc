(ns prototype.scalar-float-test
  (:require [prototype.scalar :as scalar]
            #?(:clj [clojure.test :refer [deftest is]]
               :cljs [cljs.test :refer-macros [deftest is]])))

(defn slot [type] {:index 0 :offset 0 :type type :region :scalar})
(defn layout [type] {:objects 0 :usize 0 :ssize (scalar/width type)})
(defn stored [type value]
  (let [memory (scalar/write-bytes (layout type) {} (slot type) value)]
    (scalar/read-bytes (layout type) memory (slot type))))
(defn nan? [x] #?(:clj (Double/isNaN (double x)) :cljs (js/Number.isNaN x)))
(def infinity #?(:clj Double/POSITIVE_INFINITY :cljs js/Infinity))

(deftest ieee-widths-boxing-and-signed-zero
  (is (= 8 (scalar/width "float")))
  (is (= 4 (scalar/width "float32")))
  (doseq [[type zero-bits negative-bits infinity-bits]
          [["float" [0 0 0 0 0 0 0 0] [0 0 0 0 0 0 0 128] [0 0 0 0 0 0 240 127]]
           ["float32" [0 0 0 0] [0 0 0 128] [0 0 128 127]]]]
    (is (= (layout type) (scalar/box-layout type)))
    (is (= (slot type) (scalar/box-slot type)))
    (is (= zero-bits (scalar/float-bytes type (stored type 0.0))))
    (is (= negative-bits (scalar/float-bytes type (stored type -0.0))))
    (is (= infinity-bits (scalar/float-bytes type (stored type infinity))))
    (is (= (conj (pop infinity-bits) 255) (scalar/float-bytes type (stored type (- infinity)))))
    (is (= 1.5 (stored type 1.5)))
    (is (= -2.25 (stored type -2.25)))))

(deftest float32-rounding-overflow-and-subnormals
  (is (= 16777216.0 (stored "float32" 16777217.0)))
  (is (= 1.0 (stored "float32" 1.0000000596046448)))
  (is (= 1.0000001192092896 (stored "float32" 1.0000001192092896)))
  (is (= infinity (stored "float32" 1.0e100)))
  (doseq [[type bytes] [["float32" [1 0 0 0]] ["float" [1 0 0 0 0 0 0 0]]]]
    (let [number (scalar/float-from-bytes type bytes)]
      (is (pos? number))
      (is (= bytes (scalar/float-bytes type (stored type number)))))))

(deftest nan-payloads-and-signaling-bits-survive-storage-exactly
  (doseq [[type bytes] [["float" [69 35 1 0 0 0 240 127]]
                        ["float" [69 35 1 0 0 0 248 127]]
                        ["float" [69 35 1 0 0 0 248 255]]
                        ["float32" [69 35 161 127]]
                        ["float32" [69 35 225 127]]
                        ["float32" [69 35 225 255]]]]
    (let [value (scalar/float-from-bytes type bytes)
          restored (stored type value)]
      (is (map? value))
      (is (= bytes (scalar/float-bytes type value)))
      (is (= value restored))
      (is (= bytes (scalar/float-bytes type restored)))
      (is (nan? (scalar/float-number type restored)))))
  (doseq [type ["float" "float32"]]
    (is (nan? (scalar/float-number type (stored type #?(:clj Double/NaN :cljs js/NaN)))))))

(deftest scalar-aliasing-mixed-layouts-and-forks
  (let [layout {:objects 1 :usize 1 :ssize 12}
        double-slot {:index 2 :offset 0 :type "float" :region :scalar}
        single-slot {:index 3 :offset 0 :type "float32" :region :scalar}
        original (scalar/write-bytes layout {} double-slot -0.0)
        child (scalar/write-bytes layout original single-slot 1.5)
        changed (scalar/write-bytes layout child double-slot 2.5)]
    (is (= [0 0 0 0 0 0 0 128] (mapv original (range 16 24))))
    (is (= 2147483648 (scalar/read-bytes layout original (assoc double-slot :type "uint32" :offset 4))))
    (is (= 1.5 (scalar/read-bytes layout child single-slot)))
    (is (= 2.5 (scalar/read-bytes layout changed double-slot)))
    (is (= [0 0 0 0 0 0 0 128] (scalar/float-bytes "float" (scalar/read-bytes layout child double-slot))))
    (is (not (contains? original 24)))))

(deftest malformed-floats-layouts-and-uninitialized-bytes-fail
  (is (thrown-with-msg? #?(:clj clojure.lang.ExceptionInfo :cljs js/Error) #"floating scalar value"
        (scalar/value! "float" "1.5")))
  (is (thrown-with-msg? #?(:clj clojure.lang.ExceptionInfo :cljs js/Error) #"IEEE scalar bytes"
        (scalar/float-from-bytes "float32" [0 0 0 256])))
  (is (thrown-with-msg? #?(:clj clojure.lang.ExceptionInfo :cljs js/Error) #"uninitialized"
        (scalar/read-bytes (layout "float") {} (slot "float"))))
  (is (thrown-with-msg? #?(:clj clojure.lang.ExceptionInfo :cljs js/Error) #"outside constructor"
        (scalar/write-bytes {:objects 0 :usize 0 :ssize 12} {} (assoc (slot "float") :offset 4) 1.5)))
  (is (thrown-with-msg? #?(:clj clojure.lang.ExceptionInfo :cljs js/Error) #"integer scalar type"
        (scalar/integer! "float" 1))))
