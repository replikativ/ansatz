(ns java-ir-main-checks
  (:require [clojure.test :refer [deftest is run-tests]]
            [clojure.edn :as edn]
            [java-ir-baseline :as j]
            [java-ir-baseline-checks :as c]
            [java-ir-extern-checks :as x]
            [lean-compatibility-corpus :as corpus])
  (:import [java.lang.reflect Method Field]))

(def ^:dynamic *basis* nil)
(defn prepare [rows] (binding [x/*basis* *basis*] (x/prepare rows)))
(defn stdout [ctx engine]
  (.invoke (.getMethod ^Class (:class ctx) "capturedStdout" (make-array Class 0)) engine (object-array 0)))
(defn fields [ctx value] (.get ^Field (:fields ctx) value))
(defn helper-rows []
  (let [originals (x/originals)
        call (fn [label args] {:fap {:c (get (originals label) "name") :ys args}})]
    [(c/object-constant "child")
     (c/decl "argument-list" [(c/p 1 "object")] "object"
             (c/let-ir 2 "object" (c/ctor 1 [(c/v 1) "erased"] 0) (c/ret 2)))
     (c/decl "cons" [(c/p 1 "object") (c/p 2 "object")] "object"
             (c/let-ir 3 "object" (c/ctor 1 [(c/v 1) (c/v 2)] 0) (c/ret 3)))
     (c/decl "owned-array-size" [(c/p 1 "object")] "object"
             (c/let-ir 2 "tagged" (call "Array.size" ["erased" (c/v 1)])
               ["dec" {:idx 1} 1 true false (c/ret 2)]))
     (c/decl "owned-array-get" [(c/p 1 "object") (c/p 2 "object")] "object"
             (c/let-ir 3 "tobject" (call "Array.getInternalBorrowed" ["erased" (c/v 1) (c/v 2) "erased"])
               ["inc" {:idx 3} 1 true false
                ["dec" {:idx 1} 1 true false (c/ret 3)]]))
     (c/decl "put" [(c/p 1 "object")] "object"
             (c/let-ir 2 "object" (call "IO.getStdout" ["erased"])
               (c/let-ir 3 "object" {:proj {:x {:idx 2} :i 4}}
                 ["inc" {:idx 3} 1 true false
                  ["dec" {:idx 2} 1 true false
                   (c/let-ir 4 "object" {:ap {:x {:idx 3} :ys [(c/v 1) "erased"]}} (c/ret 4))]])))
     (c/decl "apply-put" [(c/p 1 "object") (c/p 2 "object")] "object"
             (c/let-ir 3 "object" {:ap {:x {:idx 1} :ys [(c/v 2) "erased"]}} (c/ret 3)))
     (c/decl "partial-put" [(c/p 1 "object")] "object"
             (c/let-ir 2 "object" (call "IO.getStdout" ["erased"])
               (c/let-ir 3 "object" {:proj {:x {:idx 2} :i 4}}
                 ["inc" {:idx 3} 1 true false
                  ["dec" {:idx 2} 1 true false
                   (c/let-ir 4 "object" {:ap {:x {:idx 3} :ys [(c/v 1)]}} (c/ret 4))]])))
     (c/decl "apply-zero" [(c/p 1 "object")] "object"
             (c/let-ir 2 "object" {:ap {:x {:idx 1} :ys ["erased"]}} (c/ret 2)))
     (c/decl "repeat-list" [(c/p 1 "object") (c/p 2 "object")] "object"
             (c/let-ir 3 "object" (c/lit 0)
               (c/let-ir 4 "uint8" (call "Nat.decEq" [(c/v 1) (c/v 3)])
                 ["case" (c/name-ir "Bool") {:idx 4} "uint8"
                  [["ctor" {:cidx 1} (c/ret 2)]
                   ["ctor" {:cidx 0}
                    (c/let-ir 5 "object" (c/lit 1)
                      (c/let-ir 6 "object" (call "Nat.sub" [(c/v 1) (c/v 5)])
                        (c/let-ir 7 "object" (c/lit 65)
                          (c/let-ir 8 "object" (c/ctor 1 [(c/v 7) (c/v 2)] 0)
                            (c/let-ir 9 "object" (c/fap "repeat-list" [(c/v 6) (c/v 8)]) (c/ret 9))))))]]])))]))

(defn context []
  (prepare (concat (j/rows "test/fixtures/unchanged-programs/rbmap-main.jsonl") (helper-rows))))

(deftest original-main-matches-pinned-native-output
  (let [receipt (edn/read-string (slurp "measurements/java-ir-rbmap-main-oracle.edn"))
        ctx (context) engine (j/machine ctx)]
    (try
      (is (= 1 (:schema receipt)))
      (is (= (:source-sha256 receipt) (corpus/sha256 (:source receipt))))
      (is (= "819816b2e0a3bf405af45ae5c7af2491d8f5bee6" (:producer receipt)))
      (is (= 7 (count (:cases receipt))))
      (loop [cases (:cases receipt) expected ""]
        (when-let [{:keys [input exit out err]} (first cases)]
          (is (zero? exit)) (is (= "" err))
          (let [args (j/call ctx engine "argument-list" [input])
                result (j/call ctx engine "main" [args 0])]
            (is (= {:tag 0 :fields [0] :scalar-bytes []} (j/java-value ctx result)))
            (j/release! ctx engine result)
            (is (= (str expected out) (stdout ctx engine)))
            (recur (next cases) (str expected out)))))
      (finally (j/close! ctx engine)))))

(deftest strings-match-native-utf8-and-list-ownership
  (let [receipt (edn/read-string (slurp "measurements/java-ir-string-oracle.edn"))
        ctx (context) engine (j/machine ctx)
        s "Aé€😀\n"
        make-list (fn [values] (reduce (fn [tail head] (j/call ctx engine "cons" [head tail])) 0 (reverse values)))]
    (try
      (is (= 1 (:schema receipt)))
      (is (= "819816b2e0a3bf405af45ae5c7af2491d8f5bee6" (:producer receipt)))
      (is (zero? (:exit receipt)))
      (is (= 6 (count (:strings receipt))))
      (is (= 5 (count (:positions receipt))))
      (is (= (:source-sha256 receipt) (corpus/sha256 (:source receipt))))
      (let [list (make-list [65 233 8364 128512 10])]
        (j/retain! ctx engine list)
        (let [values {"empty" "" "unicode" s "nul" "A\u0000B"
                      "push" (j/call ctx engine "String.push" ["A" 128512])
                      "append" (j/call ctx engine "String.Internal.append" [s s])
                      "ofList" (j/call ctx engine "String.ofList" [list])}]
          (doseq [{:keys [label size bytes]} (:strings receipt) :let [value (values label)]]
            (is (= size (j/call ctx engine "String.utf8ByteSize" [value])))
            (is (= bytes (mapv #(bit-and 255 %) (.getBytes ^String value java.nio.charset.StandardCharsets/UTF_8))))))
        (is (= 1 (c/rc ctx list)))
        (j/release! ctx engine list))
      (is (= "" (j/call ctx engine "String.ofList" [0])))
      (doseq [{:keys [position cp next]} (:positions receipt)]
        (is (= cp (j/call ctx engine "String.decodeChar" [s position 0])))
        (is (= next (j/call ctx engine "String.Pos.next" [s position 0]))))
      (doseq [position [2 11 12 (biginteger "18446744073709551616")]]
        (is (not= "NO ERROR" (c/failure #(j/call ctx engine "String.decodeChar" [s position 0])))))
      (finally (j/close! ctx engine)))))

(deftest arrays-preserve-shared-spines-and-borrowed-results
  (let [ctx (context)]
    (doseq [shared-root? [false true] shared-tail? [false true]]
      (let [engine (j/machine ctx)]
        (try
          (let [child (j/call ctx engine "child" [])
                _ (j/retain! ctx engine child)
                tail (j/call ctx engine "cons" [child 0])
                _ (when shared-tail? (j/retain! ctx engine tail))
                list (j/call ctx engine "cons" [child tail])
                _ (when shared-root? (j/retain! ctx engine list))
                array (j/call ctx engine "Array.mk" [0 list])]
            (when shared-root? (j/release! ctx engine list))
            (when shared-tail? (j/release! ctx engine tail))
            (is (= 3 (c/rc ctx child)))
            (j/retain! ctx engine array)
            (is (= 2 (j/call ctx engine "owned-array-size" [array])))
            (doseq [index [0 1]]
              (j/retain! ctx engine array)
              (let [value (j/call ctx engine "owned-array-get" [array index])]
                (is (identical? child value))
                (is (= 4 (c/rc ctx child)))
                (j/release! ctx engine value)
                (is (= 3 (c/rc ctx child)))))
            (doseq [[label args] [["Array.size" [0 array]] ["Array.getInternalBorrowed" [0 array 0 0]]]]
              (is (re-find #"requires owned guest wrapper" (c/failure #(j/call ctx engine label args))))
              (is (= 1 (c/rc ctx array))))
            (j/release! ctx engine array)
            (is (= 1 (c/rc ctx child))))
          (finally (j/close! ctx engine)))))))

(deftest long-list-destruction-uses-private-work-stack
  (let [ctx (context) engine (j/machine ctx)]
    (try
      (let [list (j/call ctx engine "repeat-list" [50000 0])
            text (j/call ctx engine "String.ofList" [list])]
        (is (= 50000 (count text)))
        (is (every? #(= \A %) text))
        (is (zero? (c/rc ctx list))))
      (finally (j/close! ctx engine)))))

(deftest release-preserves-persistent-nodes-and-counted-owners
  (let [ctx (context) engine (j/machine ctx)
        leaf (j/call ctx engine "child" [])
        persistent (j/call ctx engine "cons" [leaf 0])]
    (.setInt ^Field (:rc ctx) persistent 0)
    (try
      (let [outer (j/call ctx engine "cons" [persistent 0])
            _ (j/retain! ctx engine outer)
            release-field (.getField ^Class (:class ctx) "releases")
            before (.getLong release-field engine)]
        (.invoke ^Method (:dec ctx) engine (object-array [outer (int 2)]))
        (is (zero? (c/rc ctx outer)))
        (is (= (+ before 2) (.getLong release-field engine)))
        (is (zero? (c/rc ctx persistent)))
        (is (identical? leaf (aget ^objects (fields ctx persistent) 0)))
        (is (= 2 (c/rc ctx leaf))))
      (j/retain! ctx engine persistent) (j/release! ctx engine persistent)
      (is (zero? (c/rc ctx persistent)))
      (doseq [[method pattern] [[(:inc ctx) #"Negative reference increment"]
                                [(:dec ctx) #"Negative reference decrement"]]]
        (is (re-find pattern (c/failure #(.invoke ^Method method engine
                                                 (object-array [persistent (int -1)]))))))
      (finally
        ;; Test fixture only: restore a finite owner to release its child graph.
        ;; This does not expose a production operation to unpersist values.
        (.setInt ^Field (:rc ctx) persistent 1)
        (j/release! ctx engine persistent)
        (j/close! ctx engine)))))

(deftest captured-stream-methods-own-and-isolate-state
  (let [ctx (context) a (j/machine ctx) b (j/machine ctx)]
    (try
      (doseq [[engine text] [[a "one"] [b "two"] [a "\n"]]]
        (let [value (j/call ctx engine "put" [text])]
          (is (= {:tag 0 :fields [0] :scalar-bytes []} (j/java-value ctx value)))
          (j/release! ctx engine value)))
      (is (= "one\n" (stdout ctx a))) (is (= "two" (stdout ctx b)))
      (let [stream (j/call ctx a "IO.getStdout" [0])
            method (aget ^objects (fields ctx stream) 4)
            tty (aget ^objects (fields ctx stream) 5)]
        (is (= 6 (alength ^objects (fields ctx stream))))
        (j/retain! ctx a method) (j/retain! ctx a tty)
        (j/release! ctx a stream)
        (is (= 0 (j/call ctx a "apply-zero" [tty])))
        (is (re-find #"Host closure belongs to another interpreter"
                     (c/failure #(j/call ctx b "apply-put" [method "wrong"]))))
        (is (= 2 (c/rc ctx method)))
        (let [result (j/call ctx a "apply-put" [method "three"])] (j/release! ctx a result))
        (is (= "one\nthree" (stdout ctx a)))
        (is (= "two" (stdout ctx b))))
      (let [partial (j/call ctx a "partial-put" ["later"])]
        (is (= "one\nthree" (stdout ctx a)))
        (is (re-find #"Host closure belongs to another interpreter"
                     (c/failure #(j/call ctx b "apply-zero" [partial]))))
        (is (= 1 (c/rc ctx partial)))
        (let [result (j/call ctx a "apply-zero" [partial])] (j/release! ctx a result))
        (is (= "one\nthreelater" (stdout ctx a))))
      (finally (j/close! ctx a) (j/close! ctx b)))))

(deftest paused-output-is-appended-exactly-once
  (let [ctx (assoc (context) :explicit true) engine (j/machine ctx)]
    (try
      (j/start! ctx engine "put" ["once"])
      (is (false? (j/advance! ctx engine 0)))
      (is (= "" (stdout ctx engine)))
      (dotimes [_ 4]
        (is (false? (j/advance! ctx engine 1)))
        (is (= "" (stdout ctx engine))))
      (is (false? (j/advance! ctx engine 1)))
      (is (= "once" (stdout ctx engine)))
      (is (true? (j/advance! ctx engine 1)))
      (is (true? (j/advance! ctx engine 0)))
      (is (= "once" (stdout ctx engine)))
      (let [result (j/take-result! ctx engine)] (j/release! ctx engine result))
      (is (= "idle" (j/phase ctx engine)))
      (finally (j/close! ctx engine)))))

(deftest stream-aliases-outlive-engine-owned-root
  (let [ctx (context) engine (j/machine ctx)
        stream (j/call ctx engine "IO.getStdout" [0])
        method (aget ^objects (fields ctx stream) 4)]
    (j/retain! ctx engine method)
    (is (= 2 (c/rc ctx stream)))
    (is (= 2 (c/rc ctx method)))
    (j/close! ctx engine)
    (is (= 1 (c/rc ctx stream)))
    (is (= 2 (c/rc ctx method)))
    (j/release! ctx engine stream)
    (is (= 1 (c/rc ctx method)))
    (j/release! ctx engine method)
    (is (zero? (c/rc ctx method)))))

(deftest unsupported-and-invalid-runtime-paths-are-explicit
  (let [ctx (context)]
    (x/probe-failure! ctx "panicCore" [0 0 "test panic"] #"panicCore default-return policy outside")
    (doseq [text [(String. (char-array [(char 0xd800)]))
                 (String. (char-array [(char 0xdc00)]))]]
      (x/probe-failure! ctx "String.utf8ByteSize" [text] #"Invalid Unicode String"))
    (let [engine (j/machine ctx) stream (j/call ctx engine "IO.getStdout" [0])
          method (aget ^objects (fields ctx stream) 3)]
      (j/retain! ctx engine method)
      (j/release! ctx engine stream)
      (is (re-find #"Captured-output stream operation not implemented"
                   (c/failure #(j/call ctx engine "apply-zero" [method]))))
      (if (= "failed" (j/phase ctx engine))
        (is (re-find #"requires ownership cleanup" (c/failure #(j/close! ctx engine))))
        (j/close! ctx engine)))))

(defn check! [basis]
  (binding [*basis* basis] (run-tests 'java-ir-main-checks)))
