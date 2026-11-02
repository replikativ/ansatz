(ns java-ir-ref-checks
  "Original ST.Ref declarations and owned wrappers, both Java execution drivers."
  (:require [clojure.test :refer [deftest is run-tests]]
            [clojure.data.json :as json]
            [clojure.edn :as edn]
            [java-ir-baseline :as j]
            [java-ir-baseline-checks :as c]
            [java-ir-extern-checks :as x]
            [java-ir-generation-checks :as g]
            [java-ir-host-checks :as host]
            [lean-compatibility-corpus :as corpus]))
(def ^:dynamic *basis* nil)
(def fixture "test/fixtures/java-ref-runtime/original-rows.json")
(defn originals [] (json/read-str (slurp fixture)))
(defn context []
  (assoc *basis* :program (j/invoke-static (:prepare *basis*)
           [(conj (mapv #(get % "row") (originals))
                  (first (x/raw [(c/decl "fresh" [(c/p 1 "object")] "object"
                                     (c/let-ir 2 "object" (c/ctor 0 [] 1) (c/ret 2)))])))])))
(defn fields [ctx node] (.get ^java.lang.reflect.Field (:fields ctx) node))
(defn make-ref! [ctx engine value] (j/call ctx engine "ST.Prim.mkRef" [0 0 value 0]))
(defn ref-get! [ctx engine ref]
  (j/retain! ctx engine ref)
  (j/call ctx engine "ST.Prim.Ref.get._boxed" [0 0 ref 0]))
(defn ref-set! [ctx engine ref value]
  (j/retain! ctx engine ref)
  (j/call ctx engine "ST.Prim.Ref.set._boxed" [0 0 ref value 0]))
(defn ref-swap! [ctx engine ref value]
  (j/retain! ctx engine ref)
  (j/call ctx engine "ST.Prim.Ref.swap._boxed" [0 0 ref value 0]))
(defn ref-take! [ctx engine ref]
  (j/retain! ctx engine ref)
  (j/call ctx engine "ST.Prim.Ref.take._boxed" [0 0 ref 0]))
(defn same-ref! [ctx engine a b]
  (j/retain! ctx engine a) (j/retain! ctx engine b)
  (j/call ctx engine "ST.Prim.Ref.ptrEq._boxed" [0 0 a b 0]))

(deftest fixture-and-exact-extern-signatures-match-the-pinned-source
  (let [manifest (edn/read-string (slurp "test/fixtures/java-ref-runtime/provenance.edn"))
        records (originals)]
    (is (= "819816b2e0a3bf405af45ae5c7af2491d8f5bee6" (:lean-commit manifest)))
    (is (= (:fixture-sha256 manifest) (corpus/sha256 fixture)))
    (is (= 12 (count records)))
    (doseq [r records :let [row (get r "row")] :when (get-in row ["ir" "extern"])]
      (let [method (.getMethod ^Class (:class *basis*) "validateExternAbi" (into-array Class [java.util.Map]))]
        (is (string? (j/invoke-static method [row])))
        (is (g/bad? #(j/invoke-static method [(assoc-in row ["ir" "extern" "xs" 0 "ty"] "void")])))))))

(deftest get-set-and-swap-preserve-owned-payload-credits
  (let [ctx (context) engine (j/machine ctx) a (j/call ctx engine "fresh" [0])
        ref (make-ref! ctx engine a)]
    (try
      (is (= 1 (c/rc ctx ref) (c/rc ctx a)))
      (let [read (ref-get! ctx engine ref)]
        (is (identical? a read)) (is (= 2 (c/rc ctx a)))
        (j/release! ctx engine read))
      (let [b (j/call ctx engine "fresh" [0]) old (ref-swap! ctx engine ref b)]
        (is (identical? a old)) (is (= 1 (c/rc ctx a) (c/rc ctx b)))
        (j/release! ctx engine old)
        (is (= 0 (c/rc ctx a)))
        (is (= 0 (ref-set! ctx engine ref 42)))
        (is (= 0 (c/rc ctx b)))
        (is (= 42 (ref-get! ctx engine ref))))
      (is (= 1 (c/rc ctx ref)))
      (finally (j/release! ctx engine ref) (j/close! ctx engine)))))

(deftest take-transfers-the-payload-and-set-refills-the-cell
  (let [ctx (context) engine (j/machine ctx) value (j/call ctx engine "fresh" [0])
        ref (make-ref! ctx engine value)]
    (try
      (let [taken (ref-take! ctx engine ref)]
        (is (identical? value taken)) (is (= 1 (c/rc ctx value)))
        (is (nil? (aget ^objects (fields ctx ref) 0)))
        (is (= 0 (ref-set! ctx engine ref taken)))
        (is (identical? value (aget ^objects (fields ctx ref) 0)))
        (let [read (ref-get! ctx engine ref)] (is (= 2 (c/rc ctx read))) (j/release! ctx engine read)))
      (finally (j/release! ctx engine ref) (j/close! ctx engine)))
    (is (= 0 (c/rc ctx value)))))

(deftest pointer-equality-and-forked-mutation-use-cell-identity
  (let [ctx (context) parent (j/machine ctx) old (j/call ctx parent "fresh" [0])
        ref (make-ref! ctx parent old) other (make-ref! ctx parent 0)
        {:keys [engine roots]} (j/fork! ctx parent [ref other old])
        child engine [child-ref child-other child-old] roots]
    (try
      (is (= 1 (same-ref! ctx parent ref ref)))
      (is (= 0 (same-ref! ctx parent ref other)))
      (is (= 1 (same-ref! ctx child child-ref child-ref)))
      (is (not (identical? ref child-ref)))
      (is (identical? child-old (aget ^objects (fields ctx child-ref) 0)))
      (is (= 0 (ref-set! ctx child child-ref 42)))
      (is (= 0 (c/rc ctx child-old)))
      (is (= 1 (c/rc ctx old)))
      (let [read (ref-get! ctx parent ref)] (is (identical? old read)) (j/release! ctx parent read))
      (is (= 42 (ref-get! ctx child child-ref)))
      (finally
        (j/release! ctx parent ref) (j/release! ctx parent other)
        (j/release! ctx child child-ref) (j/release! ctx child child-other)
        (j/close! ctx parent) (j/close! ctx child)))))

(deftest same-value-update-needs-and-consumes-its-distinct-owned-credit
  (let [ctx (context) engine (j/machine ctx) value (j/call ctx engine "fresh" [0])
        ref (make-ref! ctx engine value)]
    (try
      (let [owned (ref-get! ctx engine ref)]
        (is (= 2 (c/rc ctx owned)))
        (is (= 0 (ref-set! ctx engine ref owned)))
        (is (= 1 (c/rc ctx value)))
        (is (identical? value (aget ^objects (fields ctx ref) 0))))
      (finally (j/release! ctx engine ref) (j/close! ctx engine)))
    (is (= 0 (c/rc ctx value)))))

(deftest ref-cycles-can-be-forked-and-broken-with-real-primitives
  (let [ctx (context) parent (j/machine ctx) ref (make-ref! ctx parent 0)]
    ;; Separate owned credit for the stored self-edge; set! supplies the wrapper's.
    (j/retain! ctx parent ref) (ref-set! ctx parent ref ref)
    (is (= 2 (c/rc ctx ref)))
    (let [{:keys [engine roots]} (j/fork! ctx parent [ref]) child engine [child-ref] roots]
      (try
        (is (identical? child-ref (aget ^objects (fields ctx child-ref) 0)))
        (is (= 2 (c/rc ctx child-ref)))
        (ref-set! ctx child child-ref 42)
        (is (= 1 (c/rc ctx child-ref)))
        (is (identical? ref (aget ^objects (fields ctx ref) 0)))
        (ref-set! ctx parent ref 0)
        (is (= 1 (c/rc ctx ref)))
        (finally
          (j/release! ctx parent ref) (j/release! ctx child child-ref)
          (j/close! ctx parent) (j/close! ctx child))))))

(deftest borrowed-native-entries-reject-before-taking-root-ownership
  (let [ctx (context) engine (j/machine ctx) ref (make-ref! ctx engine 42)]
    (try
      (doseq [[label args] [["get" [0 0 ref 0]] ["take" [0 0 ref 0]]
                            ["set" [0 0 ref 0 0]] ["swap" [0 0 ref 0 0]]
                            ["ptrEq" [0 0 ref ref 0]]]]
        (is (g/bad? #(j/call ctx engine (str "ST.Prim.Ref." label) args)))
        (is (= 1 (c/rc ctx ref)))
        (is (= "idle" (j/phase ctx engine))))
      (is (g/bad? #(j/make-closure! ctx engine "ST.Prim.Ref.get" [])))
      (finally (j/release! ctx engine ref) (j/close! ctx engine)))))

(deftest empty-cells-and-constructors-are-named-errors-not-spinning-reads
  (doseq [op [:get :swap :take :wrong-kind]]
    (let [ctx (context) engine (j/machine ctx)
          value (if (= op :wrong-kind) (j/call ctx engine "fresh" [0]) (make-ref! ctx engine 0))]
      (when-not (= op :wrong-kind) (ref-take! ctx engine value))
      (let [message (c/failure #(case op
                                 :get (ref-get! ctx engine value)
                                 :swap (ref-swap! ctx engine value 42)
                                 :take (ref-take! ctx engine value)
                                 :wrong-kind (ref-get! ctx engine value)))]
        (is (not= "NO ERROR" message))
        (is (re-find #"(?i)(empty|reference|ref cell)" message)))
      ;; Discard the failed engine. Recursive Java frames unwind; closing them
      ;; clears caches, without promising cleanup of failed owned arguments.
      (if (:explicit ctx)
        (is (g/bad? #(j/close! ctx engine)))
        (is (nil? (j/close! ctx engine)))))))

(deftest borrowed-same-payload-cannot-be-reused-as-an-owned-update
  (doseq [operation [ref-set! ref-swap!]]
    (let [ctx (context) engine (j/machine ctx) value (j/call ctx engine "fresh" [0])
          ref (make-ref! ctx engine value)]
      (is (g/bad? #(operation ctx engine ref value)))
      (is (identical? value (aget ^objects (fields ctx ref) 0)))
      (is (= 1 (c/rc ctx value)))
      ;; Failed owned wrapper arguments are deliberately not replayed or cleaned.
      (if (:explicit ctx) (is (g/bad? #(j/close! ctx engine))) (is (nil? (j/close! ctx engine)))))))

(deftest erased-and-world-placeholders-cannot-hide-owned-payloads
  (doseq [position [0 1 3]]
    (let [ctx (context) engine (j/machine ctx) hidden (j/call ctx engine "fresh" [0])
          value (j/call ctx engine "fresh" [0]) args (assoc [0 0 value 0] position hidden)
          allocations (host/private-value engine "allocations")]
      (is (g/bad? #(j/call ctx engine "ST.Prim.mkRef" args)))
      (is (= 1 (c/rc ctx hidden) (c/rc ctx value)))
      (is (= allocations (host/private-value engine "allocations")))
      ;; Validation precedes ref allocation or ownership effects.
      (j/release! ctx engine hidden) (j/release! ctx engine value) (j/close! ctx engine))))

(defn check! [basis] (binding [*basis* basis] (run-tests 'java-ir-ref-checks)))
