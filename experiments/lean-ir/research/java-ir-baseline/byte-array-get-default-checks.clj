(ns java-ir-byte-array-get-default-checks
  "Original ByteArray.get! rows: zero outside live extent; proof-fget is distinct."
  (:require [clojure.test :refer [deftest is run-tests]] [clojure.data.json :as json] [clojure.java.io :as io]
            [java-ir-baseline :as j] [java-ir-baseline-checks :as c]
            [java-ir-byte-array-checks :as b] [java-ir-generation-checks :as g]
            [java-ir-host-checks :as host] [lean-compatibility-corpus :as corpus])
  (:import [java.math BigInteger]))
(def ^:dynamic *basis* nil)
(def ^:dynamic *directory* "test/fixtures/java-byte-array-get-default")
(defn fixture-file [file] (io/file (str *directory*) file))
(defn rows [] (mapv #(json/read-str (slurp (fixture-file %))) ["original-raw.json" "original-boxed.json"]))
(defn context []
  (j/extend-program (binding [b/*basis* *basis*] (b/context)) (rows)))
(defn get! [ctx engine value index]
  (j/retain! ctx engine value)
  (j/call ctx engine "ByteArray.get!._boxed" [value index]))
(defn fixture! [ctx engine bytes]
  (first (b/install ctx engine [(b/raw-descriptor ctx 1 99 (byte-array (map unchecked-byte bytes)))]
                    [(j/graph-ref ctx 1)] true)))

(deftest original-rows-have-exact-borrowed-abi-and-byte-provenance
  (let [p (json/read-str (slurp (fixture-file "provenance.json"))) [raw boxed] (rows)]
    (is (= "819816b2e0a3bf405af45ae5c7af2491d8f5bee6" (get p "leanCommit")))
    (doseq [[f pin] (get p "rows")] (is (= pin (corpus/sha256 (fixture-file f)))))
    (is (= ["object" "tobject"] (mapv #(get % "ty") (get-in raw ["ir" "extern" "xs"]))))
    (is (= [true true] (mapv #(get % "borrow") (get-in raw ["ir" "extern" "xs"]))))
    (is (= "uint8" (get-in raw ["ir" "extern" "type"])))
    (is (string? (j/invoke-static (.getMethod ^Class (:class *basis*) "validateExternAbi"
                                             (into-array Class [java.util.Map])) [raw])))
    (doseq [bad [(assoc-in raw ["ir" "extern" "xs" 0 "borrow"] false)
                 (assoc-in raw ["ir" "extern" "xs" 1 "ty"] "usize")
                 (assoc-in raw ["ir" "extern" "type"] "tagged")]]
      (is (g/bad? #(j/invoke-static (.getMethod ^Class (:class *basis*) "validateExternAbi"
                                             (into-array Class [java.util.Map])) [bad]))))
    (is (= [false false] (mapv #(get % "borrow") (get-in boxed ["ir" "fdecl" "xs"]))))))

(deftest valid-out-of-range-and-huge-indices-return-zero-without-wrapping
  (let [ctx (context) engine (j/machine ctx) value (fixture! ctx engine [0 128 255])]
    (try
      (doseq [[index expected] [[0 0] [1 128] [2 255] [3 0] [4 0] [Long/MAX_VALUE 0]
                                [(.add (BigInteger/valueOf Long/MAX_VALUE) BigInteger/ONE) 0]
                                [(.shiftLeft BigInteger/ONE 200) 0]]]
        (is (= expected (get! ctx engine value index)))
        (is (= 1 (c/rc ctx value)))
        (is (= [0 128 255] (b/payload ctx value))))
      (finally (j/release! ctx engine value) (j/close! ctx engine)))))

(deftest unused-capacity-is-not-live-data-and-borrow-does-not-store
  (let [ctx (context) engine (j/machine ctx) input (fixture! ctx engine [7])
        value (b/push! ctx engine input 255)]
    (try
      (is (= 4 (alength ^bytes (.get ^java.lang.reflect.Field (:scalars ctx) value))))
      (aset-byte ^bytes (.get ^java.lang.reflect.Field (:scalars ctx) value) 2 (unchecked-byte 123))
      (let [before (b/counters engine)]
        (is (= 255 (get! ctx engine value 1)))
        (is (= 0 (get! ctx engine value 2)))
        (is (= 0 (get! ctx engine value 3)))
        (is (= 1 (c/rc ctx value)))
        ;; The genuine boxed bridge consumes only the explicitly retained call
        ;; owner. The borrowed primitive neither allocates nor stores.
        (is (= [0 0 3 3] (mapv - (b/counters engine) before))))
      (finally (j/release! ctx engine value) (j/close! ctx engine)))))

(deftest borrowed-raw-entry-and-closure-guards-are-unchanged
  (let [ctx (context) engine (j/machine ctx) value (fixture! ctx engine [9])]
    (try
      (is (re-find #"Borrowed ByteArray primitive" (c/failure #(j/call ctx engine "ByteArray.get!" [value 0]))))
      (is (= 1 (c/rc ctx value)))
      (is (g/bad? #(j/make-closure! ctx engine "ByteArray.get!" [])))
      (finally (j/release! ctx engine value) (j/close! ctx engine)))))

(deftest same-class-ordinary-byte-array-permits-explicit-owned-transfer
  (let [ctx (context) source (j/machine ctx) target (j/machine ctx)
        value (fixture! ctx source [9])]
    (try
      ;; Ordinary ByteArrayState has no interpreter-specific realm. The actual
      ;; owned boxed bridge consumes this occurrence on the destination engine.
      (is (= 9 (j/call ctx target "ByteArray.get!._boxed" [value 0])))
      (is (= 0 (c/rc ctx value)))
      (is (true? (host/private-value value "dead")))
      (finally
        ;; Never decrement a call occurrence already consumed by the bridge.
        (when (pos? (c/rc ctx value)) (j/release! ctx source value))
        (j/close! ctx target) (j/close! ctx source)))))

(defn rejected-input! [mode]
  (let [ctx (context) engine (j/machine ctx) value (fixture! ctx engine [9])
        metadata (let [method (doto (.getDeclaredMethod ^Class (:class ctx) "kindMetadata"
                                      (into-array Class [(:node-class ctx)])) (.setAccessible true))]
                   (.invoke method nil (object-array [value])))
        size-field (when (= mode :malformed-size)
                     (doto (.getDeclaredField (class metadata) "size") (.setAccessible true)))]
    (case mode
      :dead (j/release! ctx engine value)
      :wrong-kind (.setInt ^java.lang.reflect.Field (:tag ctx) value 0)
      :malformed-size (.setInt ^java.lang.reflect.Field size-field metadata 2))
    (try
      (is (g/bad? #(j/call ctx engine "ByteArray.get!._boxed" [value 0])))
      (if (= mode :dead)
        (is (= 0 (c/rc ctx value)))
        (is (= 1 (c/rc ctx value))))
      (finally
        (when (= mode :wrong-kind) (.setInt ^java.lang.reflect.Field (:tag ctx) value 248))
        (when size-field (.setInt ^java.lang.reflect.Field size-field metadata 1))
        ;; Unexpected acceptance must be reported by the assertions, rather
        ;; than causing a second decrement that masks subsequent test families.
        (when (pos? (c/rc ctx value)) (j/release! ctx engine value))
        (j/close! ctx engine)))))
(deftest dead-value-is-not-a-valid-out-of-range-index (rejected-input! :dead))
(deftest wrong-node-kind-is-not-a-valid-out-of-range-index (rejected-input! :wrong-kind))
(deftest malformed-live-extent-is-not-a-valid-out-of-range-index (rejected-input! :malformed-size))

(defn check!
  ([] (run-tests 'java-ir-byte-array-get-default-checks))
  ([basis] (check! basis *directory*))
  ([basis fixture-directory]
   (binding [*basis* basis *directory* fixture-directory] (check!))))
