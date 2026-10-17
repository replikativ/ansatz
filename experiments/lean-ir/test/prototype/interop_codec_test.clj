(ns prototype.interop-codec-test
  (:require [clojure.test :refer [deftest is testing]]
            [prototype.interop-codec :as codec]
            [prototype.machine :as m]
            [prototype.scalar :as scalar]
            [prototype.native-scalar :as native]
            [prototype.mutable :as u]))

(deftest immediate-values-and-unbounded-nats
  (let [world (m/world {})]
    (doseq [[descriptor host guest] [[:nat 0 0] [:nat (bigint (.shiftLeft java.math.BigInteger/ONE 200))
                                                 (bigint (.shiftLeft java.math.BigInteger/ONE 200))]
                                     [:string "éλ😀" "éλ😀"] [:string "a\u0000b" "a\u0000b"]
                                     [:bool true 1] [:bool false 0] [:unit nil 0] [:world nil m/erased]]]
      (is (= [world guest] (codec/encode world descriptor host)))
      (is (= host (codec/decode world descriptor guest))))
    (is (false? (codec/decode world :bool (m/->Tag 0))))
    (is (true? (codec/decode world :bool (m/->Tag 1))))
    (is (nil? (codec/decode world :unit (m/->Tag 0))))
    (doseq [[descriptor value] [[:nat -1] [:nat 1.0] [:nat 1/2] [:bool 1] [:unit false] [:world 0]
                                [:string (str (char 55296))] [:string nil]]]
      (is (thrown? clojure.lang.ExceptionInfo (codec/encode world descriptor value))))
    (doseq [[descriptor value] [[:bool 2] [:bool true] [:unit 1] [:world 0] [:nat -1]]]
      (is (thrown? clojure.lang.ExceptionInfo (codec/decode world descriptor value))))))

(deftest byte-array-allocation-borrows-on-decode-and-forks-independently
  (let [before (m/world {}) bytes [0 127 128 255]
        [world value] (codec/encode before :bytes bytes)
        decoded (codec/decode world :bytes value)
        fork (assoc-in world [:heap (:id value) :bytes] [42])]
    (is (= {:kind :byte-array :tag 248 :fields [] :rc 1 :bytes bytes} (m/node world value)))
    (is (= bytes decoded))
    (is (= bytes (codec/decode world :bytes value)))
    (is (= [42] (codec/decode fork :bytes value)))
    (is (= 1 (:rc (m/node world value))))
    (is (empty? (:heap before)))
    (is (empty? (:heap (m/release world value 1)))))
  (doseq [bytes ['(1 2) (byte-array [1 2]) [256] [-1] [0.5]]]
    (is (thrown? clojure.lang.ExceptionInfo (codec/encode (m/world {}) :bytes bytes)))))

(deftest options-distinguish-none-from-some-unit-and-transfer-ownership
  (let [before (m/world {})]
    (is (= [before 0] (codec/encode before [:option :unit] nil)))
    (is (nil? (codec/decode before [:option :unit] (m/->Tag 0))))
    (doseq [[descriptor host] [[[:option :unit] {:some nil}]
                                [[:option :string] {:some ""}]
                                [[:option [:option :nat]] {:some nil}]
                                [[:option [:option :nat]] {:some {:some 42}}]
                                [[:option :bytes] {:some [1 2]}]]]
      (let [[world value] (codec/encode before descriptor host)]
        (is (= 1 (:tag (m/node world value))))
        (is (= host (codec/decode world descriptor value)))
        (is (= 1 (:rc (m/node world value))))
        (is (empty? (:heap (m/release world value 1))))))
    (doseq [host [false {:some 1 :extra 2} {}]]
      (is (thrown? clojure.lang.ExceptionInfo (codec/encode before [:option :nat] host))))))

(deftest unsigned-and-ieee-scalars-use-raw-carriers-and-boxed-fields
  (doseq [[descriptor type value] [[:uint8 "uint8" 255] [:uint16 "uint16" 65535]
                                    [:uint32 "uint32" 4294967295]
                                    [:uint64 "uint64" 18446744073709551615N]
                                    [:usize "usize" 18446744073709551615N]
                                    [:float "float" -0.0] [:float32 "float32" -0.0]
                                    [:float "float" Double/POSITIVE_INFINITY]
                                    [:float32 "float32" 1.234567890123]]]
    (let [before (m/world {})
          [raw-world raw] (codec/encode before descriptor value)
          expected (if (scalar/float-type? type)
                     (scalar/float-bytes type value) value)
          [world option] (codec/encode before [:option descriptor] {:some value})
          field (first (:fields (m/node world option)))
          actual (:some (codec/decode world [:option descriptor] option))]
      (is (= before raw-world))
      (is (= expected (if (scalar/float-type? type) (scalar/float-bytes type raw) raw)))
      (is (= expected (if (scalar/float-type? type) (scalar/float-bytes type actual) actual)))
      (if-let [layout (scalar/box-layout type)]
        (do (is (m/ref? field)) (is (= layout (:layout (m/node world field)))))
        (is (= value field)))
      (is (empty? (:heap (m/release world option 1))))))
  (doseq [[type bytes] [["float" [1 0 0 0 0 0 240 127]]
                         ["float" [123 0 0 0 0 0 248 255]]
                         ["float32" [1 0 128 127]]]]
    (let [descriptor (keyword type) value (scalar/float-from-bytes type bytes)
          [world guest] (codec/encode (m/world {}) [:option descriptor] {:some value})
          decoded (:some (codec/decode world [:option descriptor] guest))]
      (is (= bytes (scalar/float-bytes type decoded)))
      (is (= value decoded))))
  (doseq [[descriptor value] [[:uint8 256] [:uint16 -1] [:uint64 18446744073709551616N]
                               [:float {}] [:float32 "NaN"]]]
    (is (thrown? clojure.lang.ExceptionInfo (codec/encode (m/world {}) descriptor value)))))

(deftest io-success-decodes-without-releasing-and-errors-are-explicit
  (let [[world bytes] (codec/encode (m/world {}) :bytes [1 255])
        [world ok] (m/allocate world :ctor 0 [bytes])
        [world error] (m/allocate world :ctor 1 ["native error"])]
    (is (= [1 255] (codec/decode world [:io :bytes] ok)))
    (is (= 1 (:rc (m/node world ok))))
    (is (= 1 (:rc (m/node world bytes))))
    (let [exception (try (codec/decode world [:io :nat] error) nil
                         (catch clojure.lang.ExceptionInfo e e))]
      (is (= :guest-error (:type (ex-data exception))))
      (is (= "native error" (:guest-error (ex-data exception))))
      (is (not (contains? (ex-data exception) :world))))
    (is (thrown? clojure.lang.ExceptionInfo (codec/encode world [:io :nat] 42)))
    (is (thrown? clojure.lang.ExceptionInfo (codec/encode world [:option [:io :nat]] nil)))))

(deftest invalid-descriptors-and-guest-layouts-fail
  (doseq [descriptor [:unknown "nat" [:nat] [:option] [:io :nat :extra] [:option :unknown]]]
    (is (thrown? clojure.lang.ExceptionInfo (codec/encode (m/world {}) descriptor nil)))
    (is (thrown? clojure.lang.ExceptionInfo (codec/decode (m/world {}) descriptor 0))))
  (doseq [[descriptor kind tag fields] [[[:option :nat] :ctor 0 [1]]
                                         [[:option :nat] :ctor 1 []]
                                         [[:io :nat] :ctor 0 [1 2]]
                                         [[:io :nat] :array 0 [1]]
                                         [:bytes :byte-array 247 []]
                                         [:bytes :byte-array 248 [1]]]]
    (let [[world value] (m/allocate (m/world {}) kind tag fields)]
      (is (thrown? clojure.lang.ExceptionInfo (codec/decode world descriptor value)))))
  (let [[world value] (codec/encode (m/world {}) [:option :uint64] {:some 42})
        field (first (:fields (m/node world value)))]
    (is (thrown? clojure.lang.ExceptionInfo
          (codec/decode (assoc-in world [:heap (:id field) :tag] 9) [:option :uint64] value)))
    (is (thrown? clojure.lang.ExceptionInfo
          (codec/decode (assoc-in world [:heap (:id field) :scalar-bytes] {}) [:option :uint64] value)))
    (is (thrown? clojure.lang.ExceptionInfo
          (codec/decode (assoc-in world [:heap (:id field) :scalar-bytes 0] 256)
                        [:option :uint64] value)))))

(defn native-node [world kind tag fields extras]
  (let [[world value] (m/allocate world kind tag fields)]
    [(update-in world [:heap (:id value)] merge extras) value]))

(deftest native-imported-values-decode-in-typed-context-without-consuming
  (let [raw (native/native-scalar 4294967295)
        [world number] (native-node (m/world {}) :mpz 250 [] {:integer 1267650600228229401496703205376N})
        [world text] (native-node world :string 249 [] {:text "é😀"})
        [world option] (m/allocate world :ctor 1 [number])
        [world result] (m/allocate world :ctor 0 [text])]
    (is (= 4294967295 (codec/decode world :nat raw)))
    (is (= 1267650600228229401496703205376N (codec/decode world :nat number)))
    (is (= "é😀" (codec/decode world :string text)))
    (is (= {:some 1267650600228229401496703205376N} (codec/decode world [:option :nat] option)))
    (is (= "é😀" (codec/decode world [:io :string] result)))
    (is (nil? (codec/decode world [:option :nat] (native/native-scalar 0))))
    (is (nil? (codec/decode world :unit (native/native-scalar 0))))
    (is (false? (codec/decode world :bool (native/native-scalar 0))))
    (is (true? (codec/decode world :bool (native/native-scalar 1))))
    (is (= 255 (codec/decode world :uint8 raw)))
    (doseq [value [number text option result]] (is (= 1 (:rc (m/node world value)))))
    (doseq [descriptor [:bool :unit]]
      (is (thrown? clojure.lang.ExceptionInfo (codec/decode world descriptor raw))))
    (doseq [[descriptor value] [[:nat raw] [:nat number] [:string text] [:bool (native/native-scalar 1)]
                                [:unit (native/native-scalar 0)]]]
      (is (thrown? clojure.lang.ExceptionInfo (codec/encode world descriptor value))))))

(deftest imported-scalar-tail-padding-and-usize-views
  (doseq [[descriptor type bytes expected]
          [[:usize "usize" [1 0 0 0 1 0 0 0] 4294967297]
           [:float32 "float32" [1 0 128 127 19 20 21 22]
            (scalar/float-from-bytes "float32" [1 0 128 127])]]]
    (let [raw-layout {:objects 0 :usize 0 :ssize 8}
          [world value] (native-node (m/world {}) :ctor 0 []
                                     {:layout raw-layout :scalar-bytes (zipmap (range 8) bytes)
                                      :native-source-id 17 :native-object-bytes 16})
          [world option] (m/allocate world :ctor 1 [value])
          machine (u/thaw world) before (u/freeze machine)]
      (is (= expected (:some (codec/decode world [:option descriptor] option))))
      (is (= expected (m/unbox-value world type value)))
      (is (= expected (u/unbox machine type value)))
      (is (= before (u/freeze machine)))
      (doseq [alter [(fn [n] (dissoc n :native-source-id))
                    #(assoc % :native-object-bytes 15)
                    #(update % :scalar-bytes dissoc 7)]]
        (let [bad (update-in world [:heap (:id value)] alter)]
          (is (thrown? clojure.lang.ExceptionInfo (codec/decode bad [:option descriptor] option)))))))
  ;; uproj follows the same path as unbox, even after ordinary object fields.
  (let [[world value] (native-node (m/world {}) :ctor 0 [0]
                                   {:layout {:objects 1 :usize 0 :ssize 8}
                                    :scalar-bytes (zipmap (range 8 16) [7 0 0 0 0 0 0 0])
                                    :native-source-id 18 :native-object-bytes 24})]
    (is (= 7 (m/read-scalar-node (m/node world value)
                                {:index 1 :offset 0 :type "usize" :region :usize})))
    (is (= 7 (m/read-scalar-node (dissoc (m/node world value) :native-source-id)
                                 {:index 1 :offset 0 :type "usize" :region :usize})))))
