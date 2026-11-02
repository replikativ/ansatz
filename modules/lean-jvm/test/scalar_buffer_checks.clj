(ns ansatz-lean-jvm-scalar-buffer-checks
  "Host and structural codec models; ModelNode is not an actual interpreter Node.
   Root separately executes the compiled engine and native-corpus acceptance."
  (:require [clojure.test :refer [deftest is run-tests]] [ansatz.lean.jvm.scalar-buffer :as codec])
  (:import [java.math BigInteger] [java.util ArrayList]))
(defn- integer-type [bits signed] {"kind" "machine-int" "bits" bits "signed" signed})
(defn- float-type [bits] {"kind" "float" "bits" bits})
(defn- error-code [f] (try (f) nil (catch clojure.lang.ExceptionInfo e (:code (ex-data e)))))
(defn- raw [type input] (let [result (codec/encode-scalar type input)] (if (map? result) (:bits result) result)))
(deftest integer-widths-signedness-and-exact-carriers
  (doseq [bits [8 16 32 64] signed [false true]]
    (let [type (integer-type bits signed)
          bound (.shiftLeft BigInteger/ONE (if signed (dec bits) bits))
          lo (if signed (.negate bound) BigInteger/ZERO) hi (.subtract bound BigInteger/ONE)]
      (doseq [input [lo hi BigInteger/ZERO]]
        (is (= input (codec/decode-raw-scalar type (raw type input)))))
      (is (= "InvalidArgument" (error-code #(codec/encode-scalar type (.subtract lo BigInteger/ONE)))))
      (is (= "InvalidArgument" (error-code #(codec/encode-scalar type (.add hi BigInteger/ONE)))))
      (is (= "UnsupportedArgumentType" (error-code #(codec/encode-scalar type 1.0))))))
  (is (= "UnsupportedArgumentType" (error-code #(codec/encode-scalar (integer-type 8 false) (proxy [BigInteger] ["1"]
                                                                                           (signum [] (throw (AssertionError. "virtual signum")))))))))
(deftest word64-and-managed-scalar-plan-algebra
  (doseq [signed [false true]]
    (let [type {"kind" "word" "signed" signed} input (if signed (BigInteger/valueOf -1) (.subtract (.shiftLeft BigInteger/ONE 64) BigInteger/ONE))
          recipe (codec/encode-scalar type input)]
      (is (= {:kind :scalar :lane "usize" :bits (long -1)} recipe))
      (is (= input (codec/decode-raw-scalar type (:bits recipe))))))
  (is (= {:kind :scalar :lane "uint64" :bits (long -1)}
         (codec/encode-scalar (integer-type 64 true) -1)))
  (is (= 255 (codec/encode-scalar (integer-type 8 true) -1))))
(deftest float-raw-bits-signed-zero-infinities-and-nans
  (doseq [bits [32 64] raw (if (= bits 32) [0 0x80000000 0x7f800000 0xff800000 0x7fc01234]
                              [0 Long/MIN_VALUE 0x7ff0000000000000 0xfff0000000000000 0x7ff8000000001234])]
    (let [type (float-type bits) bits-value (if (instance? clojure.lang.BigInt raw) (.longValue ^Number raw) (long raw))
          host (codec/decode-raw-scalar type bits-value)]
      (is (= (if (= bits 32) Float Double) (class host)))
      (is (= bits-value (:bits (codec/encode-scalar type host))))))
  (is (= "UnsupportedArgumentType" (error-code #(codec/encode-scalar (float-type 32) (double 1.0)))))
  (is (= "RuntimeBoundary" (error-code #(codec/decode-raw-scalar (float-type 32) (long -1))))))
(deftest unicode-scalar-char-is-not-arbitrary-uint32
  (let [type {"kind" "char"}]
    (doseq [value [0 65 0xd7ff 0xe000 0x1f600 0x10ffff]]
      (is (= (int value) (codec/decode-raw-scalar type (codec/encode-scalar type value)))))
    (doseq [value [-1 0xd800 0xdfff 0x110000]]
      (is (= "InvalidArgument" (error-code #(codec/encode-scalar type value)))))
    (is (= "RuntimeBoundary" (error-code #(codec/decode-raw-scalar type (long 0xd800)))))
    (is (= "UnsupportedArgumentType" (error-code #(codec/encode-scalar type "a"))))))
(deftest mutable-host-inputs-are-snapshotted-and-bounded
  (let [input (byte-array [0 1 -1]) copy (codec/snapshot-bytes input)]
    (aset-byte input 0 (byte 8)) (is (= [0 1 -1] (vec copy))) (is (not (identical? input copy))))
  (let [input (object-array [1 2]) copy (codec/snapshot-array input)]
    (aset input 0 :changed) (is (= [1 2] copy)))
  (let [input (ArrayList. [1 2]) copy (codec/snapshot-array input)]
    (.set input 0 :changed) (is (= [1 2] copy)))
  (is (= "ResourceLimit" (error-code #(codec/snapshot-bytes (byte-array 1048577)))))
  (is (= "ResourceLimit" (error-code #(codec/snapshot-array (object-array 100001)))))
  (is (= "UnsupportedArgumentType" (error-code #(codec/snapshot-bytes "utf8"))))
  (is (= "UnsupportedArgumentType" (error-code #(codec/snapshot-array (range))))))

(deftype ModelNode [tag rc fields scalars dead array ref readyTask closure metadata])
(deftype ModelArrayState [size])
(deftype ModelByteArrayState [size])
(deftype ModelSharingMetadata [inner])
(defn- model-field [name] (doto (.getDeclaredField ModelNode name) (.setAccessible true)))
(def model-ctx {:class ModelNode :node-class ModelNode :tag (model-field "tag") :rc (model-field "rc")
                :fields (model-field "fields") :scalars (model-field "scalars")})
(defn- model [tag members payload metadata array]
  (ModelNode. tag 1 (object-array members) (byte-array payload) false array false false nil metadata))
(defn- with-model [f]
  (with-redefs [ansatz.lean.jvm.scalar-buffer/cohort-class
                (fn [_ suffix] (case suffix "ArrayState" ModelArrayState "ByteArrayState" ModelByteArrayState
                                     "SharingMetadata" ModelSharingMetadata))]
    (f)))
(deftest borrowed-scalar-layout-and-kind-guards
  (with-model
    #(let [raw (model 0 [] [0 0 0 -128] nil false)]
       (is (= Integer/MIN_VALUE (Float/floatToRawIntBits (codec/decode-scalar model-ctx (float-type 32) raw))))
       (is (= 1 (.-rc raw)))
       (doseq [bad [(model 0 [] [0 0 0] nil false) (model 1 [] [0 0 0 0] nil false)
                    (model 0 [] [0 0 0 0] (ModelArrayState. 0) false)
                    (model 0 [(long 0)] [0 0 0 0] nil false)]]
         (is (= "RuntimeBoundary" (error-code (fn [] (codec/decode-scalar model-ctx (float-type 32) bad)))))))))
(deftest borrowed-buffer-live-extents-and-snapshots
  (with-model
    #(let [bytes (model 248 [] [1 2 99] (ModelByteArrayState. 2) false)
           result (codec/decode-bytes model-ctx bytes)
           array (model 246 [(long 7) (long 8) nil] [] (ModelSharingMetadata. (ModelArrayState. 2)) true)]
       (is (= [1 2] (vec result)))
       (aset-byte ^bytes (.-scalars bytes) 0 (byte 9)) (is (= [1 2] (vec result)))
       (is (= [7 8] (codec/decode-array-fields model-ctx array)))
       (is (= 1 (.-rc bytes) (.-rc array)))
       (doseq [bad [(model 248 [] [1] (ModelByteArrayState. 2) false)
                    (model 248 [] [1] (ModelArrayState. 1) false)
                    (model 248 [] [1] (ModelByteArrayState. -1) false)]]
         (is (= "RuntimeBoundary" (error-code (fn [] (codec/decode-bytes model-ctx bad)))))))))
(defn check! [] (run-tests 'ansatz-lean-jvm-scalar-buffer-checks))
