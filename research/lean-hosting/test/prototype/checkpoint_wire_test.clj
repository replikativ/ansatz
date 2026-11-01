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

(deftest validate-only-keeps-the-original-value-and-all-supported-edges
  (doseq [value [nil false \c 'symbol :keyword "λ🦉" 1 1N 1/3 1.25M
                 Float/NaN Double/NaN -0.0
                 (m/->Ref 1) (m/->Tag 7) (m/->Builtin :inc) (native/native-scalar 512)
                 (with-meta {:a [(with-meta '(1 2) {:list true}) #{:a :b}]
                             :nested {(with-meta [:key] {:key true}) (with-meta [:value] {:value true})}}
                   {:metadata (with-meta [:data] {:nested true})})]]
    (is (identical? value (wire/validate-value! value)))
    (is (wire/same-data? value (wire/decode (wire/encode value))))))

(deftest validate-only-and-transform-share-rejections-including-nested-key-context
  (doseq [value [(Object.) (atom 1) (sorted-map :a 1) (sorted-set :a)
                 (assoc (m/->Ref 1) :extra 2) (m/->Ref -1) (m/->Tag 256) (m/->Builtin :other)
                 (native/->RawNativeScalar -1) (assoc (native/->RawNativeScalar 1) :extra 2)
                 (with-meta (m/->Ref 1) {})
                 {[:nested {:value [Double/NaN]}] :value}
                 #{[:nested {:value [Float/NaN]}]}
                 {(with-meta [:key] {:hidden [Double/NaN]}) :value}
                 (with-meta [:valid] {:nested-key {[:bad Float/NaN] :value}})]]
    (let [failure (fn [f] (try (f value) :accepted
                              (catch Throwable cause [(.getName (class cause)) (.getMessage cause)])))]
      (is (not= :accepted (failure wire/wire-value)))
      (is (= (failure wire/wire-value) (failure wire/validate-value!))))))

(deftype MetaVector [values metadata]
  clojure.lang.IPersistentVector
  (count [_] (count values))
  (nth [_ index] (nth values index))
  (nth [_ index missing] (nth values index missing))
  (seq [_] (seq values))
  clojure.lang.IMeta
  (meta [_] metadata))

(deftype InitSensitiveVector [opaque-with-transient?]
  clojure.lang.IPersistentVector
  (count [_] 1)
  (nth [_ index] (nth [1] index))
  (nth [_ index missing] (nth [1] index missing))
  (seq [_] (seq [1]))
  clojure.lang.IReduceInit
  (reduce [_ f init]
    (f init (if (= opaque-with-transient? (instance? clojure.lang.ITransientVector init)) (Object.) 1))))

(deftest validate-only-models-transformed-collection-metadata-capability
  ;; mapv produces an IObj even when the accepted original vector only has IMeta.
  (let [value (MetaVector. [1 2] {:source :custom-vector})]
    (is (vector? value))
    (is (not (instance? clojure.lang.IObj value)))
    (is (= {:source :custom-vector} (meta (wire/wire-value value))))
    (is (identical? value (wire/validate-value! value)))))

(deftest custom-reducers-keep-the-complete-transforming-accumulator-contract
  ;; With transient[] mapv must reject the first instance and accept the second;
  ;; a nil-accumulator validation reduction would reverse both decisions.
  (let [bad (InitSensitiveVector. true) good (InitSensitiveVector. false)]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Opaque checkpoint value" (wire/wire-value bad)))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Opaque checkpoint value" (wire/validate-value! bad)))
    (is (= [1] (wire/wire-value good)))
    (is (identical? good (wire/validate-value! good)))
    ;; SubVector is deliberately not a fast path; its public backing may be custom.
    (let [slice (clojure.lang.APersistentVector$SubVector. nil (MetaVector. [1] nil) 0 1)]
      (is (= [1] (wire/wire-value slice)))
      (is (identical? slice (wire/validate-value! slice))))))

(deftest custom-fallback-preserves-nested-map-key-float-policy
  (doseq [value [{(MetaVector. [Double/NaN] nil) :value}
                 {(MetaVector. [[:deep Float/NaN]] nil) :value}
                 {(MetaVector. [1] {:hidden [Double/NaN]}) :value}]]
    (is (thrown? clojure.lang.ExceptionInfo (wire/wire-value value)))
    (is (thrown? clojure.lang.ExceptionInfo (wire/validate-value! value)))))

(deftest custom-fallback-processes-metadata-children-exactly-once
  (let [reads (atom 0)
        leaf (reify clojure.lang.IPersistentVector clojure.lang.IReduceInit
               (count [_] 1)
               (nth [_ index] (nth [1] index))
               (nth [_ index missing] (nth [1] index missing))
               (seq [_] (seq [1]))
               (reduce [_ f init] (swap! reads inc) (reduce f init [1])))
        value (MetaVector. [1] {:leaf leaf})]
    (wire/wire-value value)
    (is (= 1 @reads))
    (reset! reads 0)
    (is (identical? value (wire/validate-value! value)))
    (is (= 1 @reads))))
