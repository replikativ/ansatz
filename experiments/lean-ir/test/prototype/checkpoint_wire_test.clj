(ns prototype.checkpoint-wire-test
  "Portable wire-format contracts, independent of a restored consumer capture."
  (:require [clojure.test :refer [deftest is]]
            [prototype.checkpoint-wire :as wire]
            [prototype.machine :as m]
            [prototype.native-scalar :as native])
  (:import [java.io ByteArrayInputStream ByteArrayOutputStream DataInputStream DataOutputStream EOFException]))

(deftest metadata-guest-carriers-and-floating-bits-survive-framing
  (let [row (with-meta
              {:name (with-meta ["str" ["anonymous"] "λ🦉"] {:source :name})
               :guest [(m/->Ref 41) (m/->Tag 7) (m/->Builtin :inc) (native/native-scalar 42)]
               :float (Float/intBitsToFloat (unchecked-int 0x7fc00011))
               :double (Double/longBitsToDouble 0x7ff8000000000011)
               :negative-zero (Double/longBitsToDouble Long/MIN_VALUE)}
              {:source {:nested (with-meta [:abi] {:preserved true})}})
        bytes (ByteArrayOutputStream.)]
    (with-open [output (DataOutputStream. bytes)] (wire/write-frame! output row) (wire/write-frame! output [:end]))
    (with-open [input (DataInputStream. (ByteArrayInputStream. (.toByteArray bytes)))]
      (let [decoded (wire/read-frame! input)]
        (is (wire/same-data? row decoded))
        (is (= (meta row) (meta decoded)))
        (is (= (meta (:name row)) (meta (:name decoded))))
        (is (= 0x7fc00011 (Float/floatToRawIntBits (:float decoded))))
        (is (= 0x7ff8000000000011 (Double/doubleToRawLongBits (:double decoded))))
        (is (= Long/MIN_VALUE (Double/doubleToRawLongBits (:negative-zero decoded)))))
      (is (= [:end] (wire/read-frame! input)))
      (is (thrown? EOFException (wire/read-frame! input))))
    (is (false? (wire/same-data? -0.0 0.0)))
    (is (false? (wire/same-data? (with-meta [:x] {:x 1}) (with-meta [:x] {:x 2}))))))

(deftest framing-rejects-invalid-lengths-and-truncation-before-decoding
  (doseq [length [0 -1 (inc wire/max-row-bytes)]]
    (let [bytes (ByteArrayOutputStream.)]
      (with-open [output (DataOutputStream. bytes)] (.writeInt output length))
      (with-open [input (DataInputStream. (ByteArrayInputStream. (.toByteArray bytes)))]
        (is (thrown-with-msg? clojure.lang.ExceptionInfo #"frame length" (wire/read-frame! input))))))
  (let [bytes (ByteArrayOutputStream.)]
    (with-open [output (DataOutputStream. bytes)] (.writeInt output 10) (.write output (byte-array [91 93])))
    (with-open [input (DataInputStream. (ByteArrayInputStream. (.toByteArray bytes)))]
      (is (thrown? EOFException (wire/read-frame! input))))))

(deftest bounded-reading-probes-once-and-preserves-borrowed-stream-ownership
  (let [closed (atom false)
        input (proxy [ByteArrayInputStream] [(byte-array [1 2 3 4])]
                (close [] (reset! closed true)))]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"byte size exceeds" (wire/read-bounded-bytes input 2)))
    (is (= 1 (.available input)))
    (is (false? @closed))
    (.close input)
    (is (true? @closed)))
  (with-open [input (ByteArrayInputStream. (byte-array [1 2]))]
    (is (= [1 2] (vec (wire/read-bounded-bytes input 2)))))
  (with-open [input (ByteArrayInputStream. (byte-array []))]
    (is (= [] (vec (wire/read-bounded-bytes input 0))))))

(deftest strict-utf8-single-data-values-and-closed-carriers-are-required
  (doseq [bytes [(byte-array [(unchecked-byte 0xc3) 0x28]) (byte-array [(unchecked-byte 0xff)])]]
    (is (thrown? java.nio.charset.CharacterCodingException (wire/decode bytes))))
  (doseq [text ["" "[] []" "#=(throw (Exception.))" "#unknown {}" "#inst \"2020-01-01\""
                "#prototype.machine.Ref {:id -1}" "#prototype.machine.Ref {:id 1 :extra 2}"
                "#prototype.machine.Tag {:tag 256}" "#prototype.machine.Builtin {:name :unknown}"]]
    (is (thrown? Exception (wire/decode (.getBytes ^String text "UTF-8")))))
  (doseq [row [(Object.) (atom 1) (with-meta (m/->Ref 1) {:opaque :metadata})
               {Double/NaN :value} #{Double/NaN} (str (char 0xd800))]]
    (is (thrown? Exception (wire/encode row)))))

(deftest bounded-encoding-rejects-the-first-byte-beyond-the-configured-row-cap
  ;; Exercise the public bound with tiny rows; no giant allocation is necessary.
  (with-redefs [wire/max-row-bytes 2]
    (is (= ":x" (wire/utf8-string (wire/encode :x)))))
  (with-redefs [wire/max-row-bytes 1]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"byte size exceeds" (wire/encode :x)))))

(deftest public-name-sharing-preserves-annotated-prefixes-and-guest-records
  (let [p1 ["str" (vector "anonymous") "Package"]
        p2 ["str" (vector "anonymous") "Package"]
        annotated (with-meta ["str" (vector "anonymous") "Package"] {:source :annotated})
        ref (m/->Ref 1)
        original {:names [["str" p1 "member"] ["str" p2 "other"] ["str" annotated "member"]] :ref ref}
        shared (wire/share-name-prefixes (java.util.HashMap.) original)
        names (:names shared)]
    (is (wire/same-data? original shared))
    (is (identical? (second (nth names 0)) (second (nth names 1))))
    (is (not (identical? (second (nth names 0)) (second (nth names 2)))))
    (is (= {:source :annotated} (meta (second (nth names 2)))))
    (is (identical? ref (:ref shared)))
    (is (instance? prototype.machine.Ref (:ref shared)))))
