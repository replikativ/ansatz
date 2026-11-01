(ns prototype.module-data-test
  (:require [clojure.test :refer [deftest is]]
            [clojure.data.json :as json]
            [clojure.java.io :as io]
            [prototype.module-data :as data]
            [prototype.native-scalar :as native]
            [prototype.machine :as m]
            [prototype.mutable :as u]
            [prototype.runtime-string :as string]
            [prototype.scalar :as scalar]))

(def fixture "fixtures/module-data-canary.jsonl")
(def fixture-sha "d3c1f3b06d2490832df99c32f94b4a06deefdabc68f4e5585c55353864ebb9a4")
(def ops {:ref? m/ref? :node m/node :release m/release})

(defn- previous-bytes! [text]
  (when-not (and (string? text) (even? (count text)) (re-matches #"[0-9a-f]*" text))
    (m/fail "Invalid ModuleData hexadecimal storage" {}))
  (mapv #(Integer/parseInt (subs text % (+ % 2)) 16) (range 0 (count text) 2)))
(defn- bytes-outcome [decode text]
  (try (let [value (decode text)] [:ok (class value) (mapv class value) value])
       (catch Throwable error [:error (class error) (.getMessage error) (ex-data error)])))

(deftest hexadecimal-decoding-preserves-values-carriers-and-errors
  (let [inputs (concat (map #(format "%02x" %) (range 256))
                       ["" "0001027f80feff" "0123456789abcdef" (apply str (repeat 512 "ff"))
                        "A0" "aF" "FF" "0" "abc" "0g" "  " "00\n" "λ0" "💥"
                        nil false 0 [] {} (Object.)])]
    (doseq [[index text] (map-indexed vector inputs)]
      (is (= (bytes-outcome previous-bytes! text) (bytes-outcome data/bytes! text))
          (str "Hex input " index)))))

(deftest actual-native-compacted-canary-retains-sharing-bits-and-typed-number-views
  (let [[old anchor] (m/resource (assoc (m/world {}) :environment {"preserved" "yes"}) :old-owner)
        result (data/load-file old fixture {:sha256 fixture-sha})
        world (:world result) [a b] (:roots result)
        node (m/node world a)
        [shared again big-nat big-int small-int ambiguous-nat bytes floats] (:fields node)
        [text1 text2] (:fields (m/node world shared))
        power (.shiftLeft java.math.BigInteger/ONE 200)]
    (is (= fixture-sha (:sha256 result)))
    (is (= a b))
    (is (= shared again))
    (is (= text1 text2))
    (is (= 8 (- (:next-id world) (:next-id old))))
    (is (identical? (:functions old) (:functions world)))
    (is (identical? (m/node old anchor) (m/node world anchor)))
    (is (= (dissoc old :heap :next-id :stats) (dissoc world :heap :next-id :stats)))
    (is (= 1 (:rc (m/node world anchor))))
    (is (every? zero? (map :rc (vals (dissoc (:heap world) (:id anchor))))))
    (is (= "λ\u0000😀" (string/string-value ops world text1)))
    (is (= [206 187 0 240 159 152 128] (:utf8-bytes (m/node world text1))))
    (is (= (bigint power) (native/nat-value ops world big-nat)))
    (is (= (- (bigint (.shiftLeft power 1))) (native/int-value ops world big-int)))
    ;; The native words are exactly the same. Only their typed operation can
    ;; decide whether the payload means -1 or4294967295.
    (is (native/native-scalar? small-int))
    (is (= small-int ambiguous-nat))
    (is (= -1 (native/int-value small-int)))
    (is (= 4294967295 (native/nat-value small-int)))
    (is (= 8589934591 (native/pointer-word small-int)))
    (is (= [0 255 128] (:bytes (m/node world bytes))))
    (is (= [1 0 0 0 0 0 248 127]
           (scalar/float-bytes "float" (first (:values (m/node world floats))))))
    (is (= {:objects 8 :usize 0 :ssize 32} (:layout node)))
    (is (= 18446744073709551615N
           (m/read-scalar-node node {:index 8 :offset 0 :type "usize" :region :usize})))
    (is (= 18446744073709551615N
           (m/read-scalar-node node {:index 9 :offset 0 :type "uint64" :region :scalar})))
    (is (= [1 0 0 0 0 0 248 127]
           (scalar/float-bytes "float" (m/read-scalar-node node {:index 10 :offset 0 :type "float" :region :scalar}))))
    (is (= 1 (m/read-scalar-node node {:index 11 :offset 0 :type "uint8" :region :scalar})))
    (is (= (:heap world) (:heap (u/freeze (u/thaw world)))))))

(defn- mutated [change f]
  (let [rows (mapv #(json/read-str % :key-fn keyword) (line-seq (io/reader fixture)))
        path (io/file "target" (str "module-data-test-" (java.util.UUID/randomUUID) ".jsonl"))]
    (try
      (spit path (apply str (map #(str (json/write-str %) "\n") (change rows))))
      (f path)
      (finally (io/delete-file path true)))))

(deftest malformed-or-different-profile-graphs-never-produce-a-candidate-world
  (doseq [change [#(assoc-in % [0 :wordBits] 32)
                  #(assoc-in % [0 :input :leanCommit] "different")
                  #(assoc-in % [0 :input :nativeEnvironmentFinalized] true)
                  #(assoc-in % [0 :input :regionAddressesTransported] true)
                  #(assoc-in % [0 :root] {:immediate "-1"})
                  #(assoc-in % [1 :id] 1)
                  #(assoc-in % [1 :fields 0 :ref] 999)
                  #(pop %)
                  #(assoc-in % [2 :tag] 245)
                  #(assoc-in % [2 :bytesHex] "0g")
                  #(update-in % [2 :fields] pop)
                  #(assoc-in % [0 :inventory :nodes] 100)]]
    (mutated change (fn [path] (is (thrown? clojure.lang.ExceptionInfo (data/load-file (m/world {}) path))))))
  (is (thrown-with-msg? clojure.lang.ExceptionInfo #"digest mismatch"
        (data/load-file (m/world {}) fixture {:sha256 (apply str (repeat 64 "0"))})))
  (is (thrown? clojure.lang.ExceptionInfo (data/load-file (m/world {}) fixture {:max-nodes 2})))
  (is (thrown? clojure.lang.ExceptionInfo (data/load-file (m/world {}) fixture {:max-bytes 10})))
  (is (thrown-with-msg? clojure.lang.ExceptionInfo #"idle top-level"
        (data/load-file (assoc (m/world {}) :status :paused) fixture))))

(deftest raw-immediate-conversion-is-contextual-and-never-uses-cljs-mod-rounding
  (is (= 0 (native/nat-value {} nil (native/native-scalar 0))))
  (is (= 4294967295 (native/unsigned-value 64 (native/native-scalar 4294967295))))
  (is (= -1 (native/int-value (native/native-scalar 9007199254740991))))
  (is (= 9223372036854775807N (native/nat-value (native/native-scalar 9223372036854775807N))))
  (is (= 18446744073709551615N (native/pointer-word (native/native-scalar 9223372036854775807N))))
  (is (thrown? clojure.lang.ExceptionInfo (native/native-scalar -1)))
  (is (thrown? clojure.lang.ExceptionInfo (native/native-scalar 9223372036854775808N)))
  (is (thrown? clojure.lang.ExceptionInfo (native/nat-value -1))))
