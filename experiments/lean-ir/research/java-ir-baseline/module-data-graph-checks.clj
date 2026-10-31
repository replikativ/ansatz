(ns java-ir-module-data-graph-checks
  (:require [clojure.test :refer [deftest is]]
            [clojure.data.json :as json]
            [clojure.java.io :as io]
            [clojure.string :as str]
            [java-ir-module-data-graph :as module]
            [java-ir-baseline :as j])
  (:import [java.security MessageDigest]))
(def commit "819816b2e0a3bf405af45ae5c7af2491d8f5bee6")
(defn manifest []
  {:kind "manifest" :schema "lean-module-dag/1" :wordBits 64 :byteOrder "little"
   :immediateEncoding "unsigned-native-tagged-payload" :root {:ref 0}
   :input {:leanVersion "4.33.1" :leanCommit commit :nativeEnvironmentFinalized false
           :regionAddressesTransported false
           :modules [{:parts [{:rootIndex 0 :artifact {:oleanVersion 2 :leanCommit commit}}] :irParts []}]}
   :inventory {:nodes 4 :tags {"246" 1 "0" 1 "249" 1 "250" 1}}})
(defn fixture []
  [(manifest)
   {:id 0 :kind "array" :tag 246 :size 1 :capacity 8 :objectBytes 88 :fields [{:ref 1}] :bytesHex ""}
   {:id 1 :kind "ctor" :tag 0 :objectBytes 56 :scalarBytesIncludePadding true
    :fields [{:ref 2} {:ref 2} {:ref 3} {:immediate "4294967295"} {:immediate "0"}]
    :bytesHex "0011223344556677"}
   {:id 2 :kind "string" :tag 249 :objectBytes 40 :size 5 :capacity 8 :utf8Length 1
    :fields [] :bytesHex "f09f988000"}
   {:id 3 :kind "mpz" :tag 250 :objectBytes 0 :fields [] :signedDecimal "18446744073709551616"}])
(defn with-source [rows f]
  (let [dir (doto (io/file "target/module-data-graph-checks") .mkdirs)
        file (java.io.File/createTempFile "source-" ".jsonl" dir)
        text (str (str/join "\n" (map json/write-str rows)) "\n")
        bytes (.getBytes text "UTF-8")
        digest (.digest (MessageDigest/getInstance "SHA-256") bytes)
        sha (apply str (map #(format "%02x" (bit-and 255 %)) digest))]
    (try (spit file text) (f file sha) (finally (.delete file)))))
(defn converted [path sha domain]
  (with-redefs [j/graph-ref (fn [_ id] [:ref id])
                j/graph-node (fn [_ node] node)
                j/module-data-graph (fn [_ _ _ nodes root] {:nodes (vec nodes) :root root})]
    (module/prepare nil :source :token path {:sha256 sha :domain domain})))
(deftest complete-source-aliases-padding-logical-size-and-utf8
  (with-source (fixture)
    (fn [path sha]
      (let [calls (atom []) result (converted path sha (fn [slot] (swap! calls conj slot) :nat))
            [root part] (get-in result [:graph :nodes]) [a b large] (:fields part)]
        (is (= 4 (get-in result [:census :source-nodes])))
        (is (= 2 (get-in result [:census :normalized-nodes])))
        (is (= [[:ref 1]] (:fields root))) ; capacity 8 is not logical size
        (is (= [:ref 0] (get-in result [:graph :root])))
        (is (identical? a b))
        (is (= "😀" a)) ; UTF-8 size minus terminator, not utf8Length bytes
        (is (= (biginteger "18446744073709551616") large))
        (is (= [0 17 34 51 68 85 102 119] (:scalars part)))
        (is (= [[sha 1 3 "4294967295"]] @calls))))))
(deftest ambiguous-scalars-digest-mismatch-and-negative-mpz-stop-before-recipe
  (with-source (fixture)
    (fn [path sha]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Unaudited" (converted path sha nil)))
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Unaudited" (converted path sha (constantly :int))))
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"digest mismatch" (converted path (apply str (repeat 64 "0")) (constantly :nat))))))
  (with-source (assoc-in (fixture) [4 :signedDecimal] "-2147483649")
    (fn [path sha]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"MPZ domain" (converted path sha (constantly :nat)))))))
(deftest missing-record-invalid-array-and-malformed-utf8-reject
  (doseq [rows [(pop (fixture))
                (assoc-in (fixture) [1 :size] 8)
                (assoc-in (fixture) [3 :utf8Length] 2)
                (assoc-in (fixture) [3 :bytesHex] "ff9f988000")
                (assoc-in (fixture) [0 :input :modules 0 :parts 0 :rootIndex] 1)]]
    (with-source rows
      (fn [path sha]
        (is (thrown? clojure.lang.ExceptionInfo (converted path sha (constantly :nat))))))))

(deftest aggregate-parts-must-be-present-reference-backed-module-data
  (let [manifest (-> (manifest) (assoc-in [:inventory :nodes] 1)
                     (assoc-in [:inventory :tags] {"246" 1}))
        root (assoc (second (fixture)) :fields [{:immediate "0"}])]
    (with-source [manifest root]
      (fn [path sha]
        (is (thrown-with-msg? clojure.lang.ExceptionInfo #"parts must be references"
                             (converted path sha (constantly :nat))))))
    (with-source [manifest (assoc root :fields [{:ref 1}])]
      (fn [path sha]
        (is (thrown-with-msg? clojure.lang.ExceptionInfo #"missing referenced records"
                             (converted path sha (constantly :nat)))))))))
