(ns java-ir-utf8-buffer-checks
  "Pinned UTF8 conversion/validation and borrowed-source buffer copies. No image."
  (:require [clojure.test :refer [deftest is run-tests]]
            [clojure.data.json :as json] [clojure.edn :as edn]
            [java-ir-baseline :as j] [java-ir-baseline-checks :as c]
            [java-ir-extern-checks :as x] [java-ir-generation-checks :as g]
            [java-ir-host-checks :as host] [java-ir-byte-array-checks :as bytes]
            [java-ir-byte-array-empty-checks :as empty] [lean-compatibility-corpus :as corpus]))
(def ^:dynamic *basis* nil)
(def directory "test/fixtures/java-utf8-buffer-runtime/")
(defn records [] (json/read-str (slurp (str directory "original-rows.json"))))
(defn original [label] (get (first (filter #(= label (get % "label")) (records))) "row"))
(defn context [explicit]
  (let [rows (mapv #(get % "row") (concat (records) (bytes/originals) (empty/records)))
        helpers [(c/decl "utf8-apply" [(c/p 1 "object") (c/p 2 "object")] "object"
                   (c/let-ir 3 "object" {:ap {:x {:idx 1} :ys [(c/v 2)]}} (c/ret 3)))
                 ;; Deliberate native-safe alias model: one owned buffer is also
                 ;; borrowed as the source. The native helper enforces its subset.
                 (c/decl "copy-one-credit-alias" [(c/p 1 "object") (c/p 2 "tobject")
                                                 (c/p 3 "tobject") (c/p 4 "tobject") (c/p 5 "uint8")] "object"
                   (c/let-ir 6 "object" {:fap {:c (get (original "ByteArray.copySlice") "name")
                                                  :ys [(c/v 1) (c/v 2) (c/v 1) (c/v 3) (c/v 4) (c/v 5)]}} (c/ret 6)))]]
    (assoc *basis* :explicit explicit :program (j/invoke-static (:prepare *basis*) [(into rows (x/raw helpers))]))))
(defn buffer! [ctx e values capacity]
  (reduce #(bytes/push! ctx e %1 %2) (empty/empty! ctx e capacity) values))
(defn size [ctx a] (count (bytes/payload ctx a)))
(defn cap [ctx a] (empty/capacity ctx a))
(defn validate! [ctx e a] (j/retain! ctx e a) (j/call ctx e "ByteArray.validateUTF8._boxed" [a]))
(defn decode! [ctx e a] (j/call ctx e "String.ofByteArray" [a 0]))
(defn copy! [ctx e src from dest to length exact]
  (j/call ctx e "ByteArray.copySlice._boxed" [src from dest to length exact]))
(defn counters [e] (mapv #(host/private-value e %) ["allocations" "stores" "retains" "releases" "shellDeletes"]))
(defn healthy-close! [ctx e]
  ;; Actual failed guest frames have no generic unwind contract in this suite.
  (when (= "idle" (j/phase ctx e))
    (when-not (host/private-value e "untrackedFailure") (j/close! ctx e))))

(deftest authenticated-five-extern-abis-and-original-wrappers
  (let [manifest (edn/read-string (slurp (str directory "provenance.edn"))) rows (records)
        method (.getMethod ^Class (:class *basis*) "validateExternAbi" (into-array Class [java.util.Map]))]
    (is (= 10 (count rows)))
    (is (= (:fixture-sha256 manifest) (corpus/sha256 (str directory "original-rows.json"))))
    (is (= 375258 (:source-index-declarations manifest)))
    (is (= :same-stream-sha256-and-exact-typed-membership (:source-index-authentication manifest)))
    (doseq [r rows :when (get-in r ["row" "ir" "extern"])]
      (is (string? (j/invoke-static method [(get r "row")]))))
    (doseq [label ["String.toUTF8" "ByteArray.validateUTF8" "ByteArray.copySlice"]]
      (is (g/bad? #(j/invoke-static method
                     [(if (= label "String.toUTF8")
                        (assoc-in (original label) ["ir" "extern" "xs" 0 "ty"] "usize")
                        (assoc-in (original label) ["ir" "extern" "xs" 0 "borrow"] false))]))))))

(deftest unicode-nul-roundtrips-through-both-original-string-origins
  (doseq [explicit [false true] text ["" "ascii" "a\u0000b" "\u007f\u0080\u07ff\u0800" "\ud7ff\ue000\uffff" "\ud800\udc00\udbff\udfff" "éλ😀"]]
    (let [ctx (context explicit) e (j/machine ctx)]
      (try
        (doseq [label ["String.toByteArray._boxed" "String.toUTF8._boxed"]]
          (let [a (j/call ctx e label [text]) expected (.getBytes ^String text "UTF-8")]
            (is (= (alength expected) (cap ctx a) (size ctx a)))
            (is (= (mapv #(Byte/toUnsignedInt %) expected) (bytes/payload ctx a)))
            (is (= 1 (c/rc ctx a))) (is (= 1 (validate! ctx e a)))
            (is (= text (decode! ctx e a))) (is (host/private-value a "dead"))))
        (finally (j/close! ctx e))))))

(deftest string-utf8-cache-is-never-exposed-as-mutable-byte-storage
  (doseq [explicit [false true]]
    (let [ctx (context explicit) e (j/machine ctx) text "immutable-é😀"
          a (j/call ctx e "String.toByteArray" [text]) cached (host/private-value e "utf8Bytes")
          b (j/call ctx e "String.toByteArray" [text])]
      (try
        (is (not (identical? cached (.get ^java.lang.reflect.Field (:scalars ctx) a))))
        (is (not (identical? (.get ^java.lang.reflect.Field (:scalars ctx) a) (.get ^java.lang.reflect.Field (:scalars ctx) b))))
        (let [source (buffer! ctx e [90] 1) changed (copy! ctx e source 0 a 0 1 1)]
          (is (identical? a changed)) (is (= 90 (first (bytes/payload ctx changed))))
          (is (= text (decode! ctx e b)))
          (let [again (j/call ctx e "String.toByteArray" [text])]
            (is (= text (decode! ctx e again))))
          (j/release! ctx e changed))
        (finally (j/close! ctx e))))))

(def valid-bytes [[0] [127] [194 128] [223 191] [224 160 128] [237 159 191]
                  [238 128 128] [239 191 191] [240 144 128 128] [244 143 191 191]])
(def invalid-bytes [[128] [191] [192 128] [193 191] [194] [194 0]
                    [224 128 128] [224 160] [237 160 128] [239 191 0]
                    [240 128 128 128] [240 144 128] [244 144 128 128]
                    [245 128 128 128] [248 128 128 128 128] [255]])
(deftest strict-source-validation-boundaries-and-failure-classes
  (doseq [explicit [false true] [data expected] (concat (map #(vector % 1) valid-bytes) (map #(vector % 0) invalid-bytes))]
    (let [ctx (context explicit) e (j/machine ctx) a (buffer! ctx e data (+ 3 (count data))) before (vec (bytes/payload ctx a))]
      (try
        (is (= expected (validate! ctx e a)))
        (is (= before (bytes/payload ctx a))) (is (= 1 (c/rc ctx a)))
        (finally (j/release! ctx e a) (j/close! ctx e))))))

(deftest validation-and-decoding-ignore-spare-bytes
  (doseq [explicit [false true]]
    (let [ctx (context explicit) e (j/machine ctx) a (buffer! ctx e [65] 8)]
      (try
        ;; Deliberate spare-storage model: no live byte is altered.
        (aset-byte ^bytes (.get ^java.lang.reflect.Field (:scalars ctx) a) 7 (unchecked-byte 255))
        (is (= 1 (validate! ctx e a))) (is (= 8 (cap ctx a)))
        (is (= "A" (decode! ctx e a)))
        (finally (j/close! ctx e))))))

(deftest malformed-unchecked-conversion-rejects-before-root-owner-claim
  (doseq [explicit [false true] data invalid-bytes]
    (let [ctx (context explicit) e (j/machine ctx) a (buffer! ctx e data (long (count data))) before (counters e)]
      (try
        (is (re-find #"Malformed unchecked UTF8" (c/failure #(decode! ctx e a))))
        (is (= before (counters e))) (is (= 1 (c/rc ctx a)))
        (is (= data (bytes/payload ctx a))) (is (= "idle" (j/phase ctx e)))
        (is (false? (host/private-value e "untrackedFailure")))
        (finally (j/release! ctx e a) (j/close! ctx e))))))

(deftest invalid-java-surrogates-and-proof-reject-before-effects
  (doseq [explicit [false true]]
    (let [ctx (context explicit) e (j/machine ctx) a (buffer! ctx e [65] 1) before (counters e)]
      (try
        (doseq [text ["\ud800" "\udc00" "x\ud800y"]]
          (is (re-find #"Invalid Unicode" (c/failure #(j/call ctx e "String.toByteArray" [text])))))
        (doseq [proof [1 "proof" a]]
          (is (re-find #"erased placeholder" (c/failure #(j/call ctx e "String.ofByteArray" [a proof])))))
        (is (= before (counters e))) (is (= 1 (c/rc ctx a))) (is (= "idle" (j/phase ctx e)))
        (finally (j/release! ctx e a) (j/close! ctx e))))))

(deftest owned-original-conversion-is-first-class-but-borrowed-raw-origins-are-fenced
  (doseq [explicit [false true]]
    (let [ctx (context explicit) e (j/machine ctx)
          closure (j/make-closure! ctx e "String.toByteArray" [])
          a (j/call ctx e "utf8-apply" [closure "valid"])]
      (try
        (is (= "valid" (decode! ctx e a)))
        (doseq [label ["String.toUTF8" "ByteArray.validateUTF8" "ByteArray.copySlice"]]
          (let [before (counters e)]
            (is (g/bad? #(j/call ctx e label [])))
            (is (g/bad? #(j/make-closure! ctx e label [])))
            (is (= before (counters e))) (is (= "idle" (j/phase ctx e)))))
        (finally (j/close! ctx e))))))

(deftest original-boxed-owned-proof-conversion-and-partial-application
  (doseq [explicit [false true]]
    (let [ctx (context explicit) e (j/machine ctx) a (buffer! ctx e [194 128] 2)
          closure (j/make-closure! ctx e "String.ofByteArray._boxed" [a])]
      (try
        (is (= "\u0080" (j/call ctx e "utf8-apply" [closure 0])))
        (is (host/private-value closure "dead")) (is (host/private-value a "dead"))
        (finally (j/close! ctx e))))))

(deftest copy-clamps-offsets-length-and-preserves-live-tail
  (doseq [explicit [false true]
          [from to length expected] [[1 1 2 [9 2 3 9]] [1 999 999 [9 9 9 9 2 3]] [3 2 0 [9 9 9 9]]]]
    (let [ctx (context explicit) e (j/machine ctx) src (buffer! ctx e [1 2 3] 3) dest (buffer! ctx e [9 9 9 9] 8)
          out (copy! ctx e src from dest to length 1)]
      (try
        (is (identical? dest out)) (is (= expected (bytes/payload ctx out)))
        (is (= 8 (cap ctx out))) (is (= 1 (c/rc ctx out))) (is (host/private-value src "dead"))
        (finally (j/release! ctx e out) (j/close! ctx e))))))

(deftest copy-exact-and-geometric-growth-use-new-size-not-old-capacity
  (doseq [explicit [false true] exact [0 1]]
    (let [ctx (context explicit) e (j/machine ctx) src (buffer! ctx e [1 2 3] 3) dest (buffer! ctx e [9 9] 2)
          out (copy! ctx e src 0 dest 2 3 exact)]
      (try
        (is (not (identical? dest out))) (is (host/private-value dest "dead"))
        (is (= [9 9 1 2 3] (bytes/payload ctx out)))
        (is (= (if (= exact 1) 5 10) (cap ctx out)))
        (finally (j/release! ctx e out) (j/close! ctx e))))))

(deftest zero-length-copy-still-cows-a-shared-destination
  (doseq [explicit [false true]]
    (let [ctx (context explicit) e (j/machine ctx) src (buffer! ctx e [1] 1) dest (buffer! ctx e [9] 8)
          _ (j/retain! ctx e dest) out (copy! ctx e src 1 dest 0 0 0)]
      (try
        (is (not (identical? dest out))) (is (= [9] (bytes/payload ctx dest) (bytes/payload ctx out)))
        (is (= 8 (cap ctx out))) (is (= 1 (c/rc ctx dest) (c/rc ctx out)))
        (finally (j/release! ctx e dest) (j/release! ctx e out) (j/close! ctx e))))))

(deftest positive-alias-source-and-destination-cow-with-separate-boxed-credits
  (doseq [explicit [false true]]
    (let [ctx (context explicit) e (j/machine ctx) a (buffer! ctx e [1 2 3 4] 8)
          _ (j/retain! ctx e a) out (copy! ctx e a 0 a 1 3 1)]
      (try
        (is (not (identical? a out))) (is (= [1 1 2 3] (bytes/payload ctx out)))
        (is (= 8 (cap ctx out))) (is (= 1 (c/rc ctx out)))
        (is (host/private-value a "dead"))
        (finally (j/release! ctx e out) (j/close! ctx e))))))

(deftest native-safe-one-credit-alias-supports-disjoint-and-zero-length-only
  (doseq [explicit [false true] [from to n expected] [[0 2 2 [1 2 1 2]] [0 4 0 [1 2 3 4]]]]
    (let [ctx (context explicit) e (j/machine ctx) a (buffer! ctx e [1 2 3 4] 8)
          out (j/call ctx e "copy-one-credit-alias" [a from to n 1])]
      (try
        (is (identical? a out)) (is (= expected (bytes/payload ctx out))) (is (= 1 (c/rc ctx out)))
        (finally (j/release! ctx e out) (j/close! ctx e))))))

(deftest one-credit-overlap-or-growth-refuses-without-native-effects
  (doseq [explicit [false true] [from to n capacity] [[0 1 3 8] [0 4 4 4]]]
    (let [ctx (context explicit) e (j/machine ctx) a (buffer! ctx e [1 2 3 4] capacity) before (counters e)]
      (is (g/bad? #(j/call ctx e "copy-one-credit-alias" [a from to n 1])))
      (is (= before (counters e))) (is (= [1 2 3 4] (bytes/payload ctx a))) (is (= 1 (c/rc ctx a)))
      ;; This intentional unsafe-model failure leaves the argument with the
      ;; failed guest frame. No fake ownership unwind/release is performed.
      (healthy-close! ctx e))))

(deftest native-size-t-domain-and-source-early-return-order
  (doseq [explicit [false true]]
    (let [ctx (context explicit) e (j/machine ctx) huge (biginteger "18446744073709551616")
          maximum (biginteger "18446744073709551615")]
      (let [src (buffer! ctx e [1] 1) dest (buffer! ctx e [9] 4)
            out (copy! ctx e src maximum dest huge huge 1)]
        (is (identical? dest out)) (is (= [9] (bytes/payload ctx out))) (j/release! ctx e out))
      (let [src (buffer! ctx e [1 2] 2) dest (buffer! ctx e [9] 4)
            out (copy! ctx e src 0 dest maximum maximum 1)]
        (is (= [9 1 2] (bytes/payload ctx out))) (j/release! ctx e out))
      (j/close! ctx e))))

(deftest persistent-source-and-destination-remain-live-and-copy
  (doseq [explicit [false true]]
    (let [ctx (context explicit) e (j/machine ctx)
          [src dest] (bytes/install ctx e [(bytes/raw-descriptor ctx 1 0 (byte-array [1 2]))
                                           (bytes/raw-descriptor ctx 2 0 (byte-array [9 9]))]
                       [(j/graph-ref ctx 1) (j/graph-ref ctx 2)] false)
          out (copy! ctx e src 0 dest 0 2 1)]
      (try
        (is (not (identical? out dest))) (is (= [9 9] (bytes/payload ctx dest)))
        (is (= [1 2] (bytes/payload ctx out))) (is (= 0 (c/rc ctx src) (c/rc ctx dest)))
        (finally (j/release! ctx e out) (j/close! ctx e))))))

(deftest fork-copies-independent-live-size-and-storage
  (doseq [explicit [false true]]
    (let [ctx (context explicit) e (j/machine ctx) src (buffer! ctx e [1 2] 2) dest (buffer! ctx e [9 9] 8)
          fork (j/fork! ctx e [src dest]) ce (:engine fork) [child-src child-dest] (:roots fork)
          _ (j/retain! ctx e src) out (copy! ctx e src 0 dest 0 2 1)
          child-src (bytes/push! ctx ce child-src 255)
          _ (j/retain! ctx ce child-src) child-out (copy! ctx ce child-src 0 child-dest 0 3 1)]
      (try
        (is (= [1 2] (bytes/payload ctx out))) (is (= [1 2 255] (bytes/payload ctx child-out)))
        (is (= [1 2] (bytes/payload ctx src))) (is (= 8 (cap ctx out) (cap ctx child-out)))
        (is (not (identical? (.get ^java.lang.reflect.Field (:scalars ctx) out) (.get ^java.lang.reflect.Field (:scalars ctx) child-out))))
        (finally (j/release! ctx e src) (j/release! ctx e out)
                 (j/release! ctx ce child-src) (j/release! ctx ce child-out) (j/close! ctx e) (j/close! ctx ce))))))
(deftest header-based-native-abi-keeps-owned-and-borrowed-string-modes-distinct
  (doseq [explicit [false true]]
    (let [base (assoc (j/prepare-host-program *basis* [] []) :explicit explicit)
          source (j/source-binding base (Object.))
          by-label (into {} (for [entry (records) :when (get-in entry ["row" "ir" "extern"])]
                              [(get entry "label") (j/declaration-header source (get entry "row") (get entry "sha256"))]))
          ctx (j/register-headers base (vec (vals by-label))) e (j/machine ctx)]
      (try
        (let [a (j/call ctx e "String.toByteArray" ["header-native"])]
          (is (= "header-native" (decode! ctx e a))))
        (let [before (counters e)]
          (is (g/bad? #(j/call ctx e "String.toUTF8" ["header-native"])))
          (is (g/bad? #(j/make-closure! ctx e "String.toUTF8" [])))
          (let [recipe (j/prepared-graph ctx source (Object.)
                         [(j/graph-node ctx {:kind :closure :id 1 :target (get by-label "String.toUTF8")})]
                         [] [] [(j/graph-ref ctx 1)])]
            (is (g/bad? #(j/install-graph! ctx e recipe))))
          (is (= before (counters e))) (is (false? (host/private-value e "graphInstalled"))))
        (finally (j/close! ctx e))))))

(deftest copy-invalid-bool-or-required-nat-conversion-is-terminal-with-no-native-effects
  (doseq [explicit [false true]
          [from to length exact] [[(biginteger "18446744073709551616") 0 0 1]
                                 [0 (biginteger "18446744073709551616") 0 1]
                                 [0 0 (biginteger "18446744073709551616") 1]
                                 [-1 0 0 1] [0 0 1 2]]]
    (let [ctx (context explicit) e (j/machine ctx) src (buffer! ctx e [1 2] 2) dest (buffer! ctx e [9 9] 8)
          before (counters e)]
      (is (g/bad? #(copy! ctx e src from dest to length exact)))
      (is (= before (counters e)))
      (is (= [1 2] (bytes/payload ctx src))) (is (= [9 9] (bytes/payload ctx dest)))
      (is (= 1 (c/rc ctx src) (c/rc ctx dest)))
      (is (or (= "failed" (j/phase ctx e)) (host/private-value e "untrackedFailure")))
      (healthy-close! ctx e))))

(defn check! [basis] (binding [*basis* basis] (run-tests 'java-ir-utf8-buffer-checks)))
