(ns java-ir-share-common-checks
  "Explicit target-layout maxsharing, owner packets and budgeted forks."
  (:require [clojure.test :refer [deftest is run-tests]] [clojure.data.json :as json]
            [java-ir-baseline :as j] [java-ir-baseline-checks :as c]
            [java-ir-expr-find-checks :as f] [java-ir-extern-checks :as x]
            [java-ir-host-checks :as h] [java-ir-generation-checks :as g]
            [java-ir-array-checks :as a] [java-ir-byte-array-checks :as b]
            [java-ir-ref-checks :as r] [java-ir-sync-task-checks :as sync]
            [java-ir-logical-sharing-checks :as sharing]
            [java-ir-continuation-checks :as k] [lean-compatibility-corpus :as corpus]))
(def ^:dynamic *basis* nil)
(def directory "test/fixtures/java-sharecommon-runtime/")
(def base-records f/records)
(defn records [] (json/read-str (slurp (str directory "original-rows.json"))))
(defn raw-name [] (get-in (first (records)) ["row" "name"]))
(defn helpers []
  [(c/decl "share-leaf" [(c/p 1 "object")] "object"
     (c/let-ir 2 "object" (c/ctor 0 [(c/v 1)] 0) (c/ret 2)))
   (c/decl "share-pair" (mapv #(c/p % "object") [1 2]) "object"
     (c/let-ir 3 "object" (c/ctor 1 [(c/v 1) (c/v 2)] 0) (c/ret 3)))
   (c/decl "share-triple" (mapv #(c/p % "object") [1 2 3]) "object"
     (c/let-ir 4 "object" (c/ctor 2 [(c/v 1) (c/v 2) (c/v 3)] 0) (c/ret 4)))
   (c/decl "share-keep" (mapv #(c/p % "object") [1 2]) "object"
     (c/let-ir 3 "object" {:fap {:c (raw-name) :ys [(c/v 1) (c/v 2)]}}
       (c/let-ir 4 "object" (c/ctor 1 [(c/v 2) (c/v 3)] 0) (c/ret 4))))
   (c/decl "share-apply" (mapv #(c/p % "object") [1 2 3]) "object"
     (c/let-ir 4 "object" {:ap {:x {:idx 1} :ys [(c/v 2) (c/v 3)]}} (c/ret 4)))])
(defn context
  ([] (context {}))
  ([options]
   (binding [f/*basis* *basis*]
     (with-redefs [f/records #(concat (base-records) (records) (a/originals) (b/originals) (r/originals))]
       (f/context (update options :rows #(concat (helpers) %)))))))
(defn machine [ctx]
  (let [e (j/machine ctx)] (j/configure-share-common! ctx e (j/jvm-carrier-layout-v1 ctx)) e))
(defn call [ctx e label args] (f/invoke ctx e label args))
(defn share! [ctx e value] (call ctx e "ShareCommon.shareCommon'._boxed" [0 value]))
(defn fields [ctx value] (vec (f/fields ctx value)))
(defn leaf! [ctx e value] (call ctx e "share-leaf" [value]))
(defn pair! [ctx e left right] (call ctx e "share-pair" [left right]))
(defn triple! [ctx e x y z] (call ctx e "share-triple" [x y z]))
(defn share-action [e]
  (loop [action (sync/action e)]
    (when action (if (h/private-value action "share") action (recur (h/private-value action "parent"))))))
(defn state [e] (some-> (share-action e) (h/private-value "share")))
(defn until! [ctx e condition]
  (loop [left 100000]
    (assert (pos? left) "ShareCommon test did not reach bounded checkpoint")
    (when-not (condition) (j/advance! ctx e 1) (recur (dec left)))))
(defn array! [ctx e capacity values]
  (reduce #(call ctx e "Array.push._boxed" [0 %1 %2])
          (call ctx e "Array.mkEmpty._boxed" [0 (long capacity)]) values))
(defn bytes! [ctx e values] (call ctx e "ByteArray.mk._boxed" [(array! ctx e (count values) values)]))
(defn install! [ctx e source nodes roots]
  (j/install-graph! ctx e (j/selected-owner-graph ctx source (Object.) nodes [] [] roots)))

(deftest exact-original-abi-and-opt-in-is-required-even-for-scalars
  (let [rs (records) p (json/read-str (slurp (str directory "provenance.json")))
        d (get-in (first rs) ["row" "ir" "extern"])]
    (is (= 2 (count rs))) (is (= (get p "original-rows-sha256") (corpus/sha256 (str directory "original-rows.json"))))
    (is (= [] (get p "initialized-dependencies")))
    (is (= [["erased" "tobject"] [false true] "tobject"]
           [(mapv #(get % "ty") (get d "xs")) (mapv #(get % "borrow") (get d "xs")) (get d "type")]))
    (is (= [false false] (mapv #(get % "borrow") (get-in (second rs) ["row" "ir" "fdecl" "xs"])))))
  (let [{:keys [ctx]} (context) e (j/machine ctx) before (k/counters ctx e)]
    (j/start! ctx e "ShareCommon.shareCommon'._boxed" [0 7])
    (is (re-find #"configured JvmCarrierLayoutV1" (c/failure #(sync/finish! ctx e))))
    (is (= before (k/counters ctx e))))
  (let [{:keys [ctx]} (context) e (machine ctx) layout (h/private-value e "shareCommonLayout")]
    (is (g/bad? #(j/configure-share-common! ctx e layout)))
    (doseq [value [0 -1 2147483648 4294967295 Long/MAX_VALUE]] (is (= value (share! ctx e value))))
    (let [{:keys [engine]} (j/fork! ctx e [])]
      (is (identical? layout (h/private-value engine "shareCommonLayout")))
      (is (= -1 (share! ctx engine -1))) (sync/close! ctx engine))
    (sync/close! ctx e) (is (g/bad? #(j/configure-share-common! ctx e layout)))))

(deftest borrowed-root-closure-pap-import-and-inactive-guards
  (let [{:keys [ctx source headers]} (context) e (machine ctx) input (leaf! ctx e 7) before (k/counters ctx e)]
    (is (g/bad? #(j/start! ctx e "ShareCommon.shareCommon'" [0 input])))
    (is (= before (k/counters ctx e))) (is (= "idle" (j/phase ctx e)))
    (is (g/bad? #(j/make-closure! ctx e "ShareCommon.shareCommon'" [])))
    (is (g/bad? #(context {:rows [(c/decl "bad-share-pap" [] "object"
                       (c/let-ir 1 "object" {:pap {:c (raw-name) :ys []}} (c/ret 1)))]})))
    (is (g/bad? #(j/install-graph! ctx e (j/prepared-graph ctx source (Object.)
                  [(j/graph-node ctx {:kind :closure :id 1 :target (headers "ShareCommon.shareCommon'")})]
                  [] [] [(j/graph-ref ctx 1)]))))
    (is (false? (h/private-value e "graphInstalled")))
    (sync/release! ctx e input) (sync/close! ctx e))
  (doseq [mode [:recursive :explicit]]
    (let [{:keys [ctx]} (context {:inactive mode}) e (j/machine ctx)]
      (is (g/bad? #(j/configure-share-common! ctx e (j/jvm-carrier-layout-v1 ctx))))
      (is (re-find #"active explicit runtime" (c/failure #(j/call ctx e "ShareCommon.shareCommon'._boxed" [0 0])))))))

(deftest rebuilt-unique-and-shared-inputs-canonicalize-with-source-owner-counts
  (doseq [shared? [false true]]
    (let [{:keys [ctx]} (context) e (machine ctx) a (leaf! ctx e 7)
          b (if shared? (do (j/retain! ctx e a) a) (leaf! ctx e 7)) root (pair! ctx e a b)
          before (h/private-value e "allocations") output (share! ctx e root) [x y] (fields ctx output)]
      (is (= (if shared? 2 3) (- (h/private-value e "allocations") before)))
      (is (not (identical? output root))) (is (not (identical? x a)))
      (is (identical? x y)) (is (= [7] (fields ctx x))) (is (= 2 (c/rc ctx x)))
      (is (every? #(h/private-value % "dead") [root a b]))
      (sync/release! ctx e output) (is (h/private-value x "dead")) (sync/close! ctx e))))

(deftest direct-borrowed-fap-keeps-input-live-and-owned-original-wrapper-is-first-class
  (let [{:keys [ctx]} (context) e (machine ctx) input (leaf! ctx e 7)
        output (call ctx e "share-keep" [0 input]) [original copied] (fields ctx output)]
    (is (identical? input original)) (is (false? (h/private-value input "dead")))
    (is (= 1 (c/rc ctx original) (c/rc ctx copied))) (is (= (fields ctx original) (fields ctx copied)))
    (sync/release! ctx e output) (sync/close! ctx e))
  (let [{:keys [ctx]} (context) e (machine ctx) input (leaf! ctx e 8)
        wrapped (j/make-closure! ctx e "ShareCommon.shareCommon'._boxed" [])
        output (call ctx e "share-apply" [wrapped 0 input])]
    (is (h/private-value wrapped "dead")) (is (h/private-value input "dead"))
    (is (= [8] (fields ctx output))) (sync/release! ctx e output) (sync/close! ctx e)))

(deftest scalar-carrier-kinds-logical-values-and-colliding-strings-stay-exact
  (let [{:keys [ctx]} (context) e (machine ctx)
        big-a (java.math.BigInteger. "1") big-b (java.math.BigInteger. "1")
        source (triple! ctx e (leaf! ctx e -1) (leaf! ctx e 4294967295)
                         (triple! ctx e 1 big-a big-b))
        output (share! ctx e source) [a b nested] (fields ctx output) [small x y] (fields ctx nested)]
    (is (not (identical? a b))) (is (= [-1] (fields ctx a))) (is (= [4294967295] (fields ctx b)))
    (is (instance? Long small)) (is (= java.math.BigInteger (class x)))
    (is (identical? big-a x)) (is (identical? x y)) (is (not= (class small) (class x)))
    (sync/release! ctx e output) (sync/close! ctx e))
  (let [{:keys [ctx]} (context) e (machine ctx) aa (String. "Aa") bb (String. "BB") aa2 (String. "Aa")
        root (triple! ctx e aa bb aa2) output (share! ctx e root) [x y z] (fields ctx output)]
    (is (= (.hashCode aa) (.hashCode bb))) (is (identical? aa x)) (is (identical? bb y))
    (is (identical? x z)) (is (not (identical? x y)))
    (doseq [value [(String. "a\u0000b") (String. "λ𝄞")]] (is (identical? value (share! ctx e value))))
    (sync/release! ctx e output) (sync/close! ctx e)))

(deftest exact-stored-constructor-extents-padding-and-boxed-bits
  (let [{:keys [ctx source]} (context) e (machine ctx)
        payloads [[0] (repeat 8 0) (repeat 9 0) (repeat 16 0)
                  [0 0 0 0 0 0 0 (unchecked-byte 128)]
                  [1 0 0 0 0 0 (unchecked-byte 248) 127]
                  [2 0 0 0 0 0 (unchecked-byte 248) 127]]
        nodes (mapv (fn [i data] (j/graph-node ctx {:kind :ctor :id i :rc 99 :tag 0 :scalars data})) (range 1 8) payloads)
        root-id 8 root (j/graph-node ctx {:kind :ctor :id root-id :rc 99 :tag 1 :fields (mapv #(j/graph-ref ctx %) (range 1 8))})
        [input] (install! ctx e source (conj nodes root) [(j/graph-ref ctx root-id)])
        output (share! ctx e input) values (fields ctx output)]
    (is (= [1 8 9 16 8 8 8] (mapv #(alength ^bytes (.get ^java.lang.reflect.Field (:scalars ctx) %)) values)))
    (is (every? false? (for [i (range (count values)) j (range i)] (identical? (nth values i) (nth values j)))))
    (doseq [[value bytes] (map vector values payloads)]
      (is (= (vec bytes) (vec (.get ^java.lang.reflect.Field (:scalars ctx) value)))))
    (sync/release! ctx e output) (sync/close! ctx e)))

(deftest object-array-capacity-normalizes-but-byte-array-terminal-capacity-does-not
  (let [{:keys [ctx]} (context) e (machine ctx) a (array! ctx e 2 [7]) b (array! ctx e 8 [7])
        output (share! ctx e (pair! ctx e a b)) [x y] (fields ctx output)]
    (is (identical? x y)) (is (= [7] (a/elements ctx x)))
    (is (= 1 (alength ^objects (f/fields ctx x)))) (is (= 2 (c/rc ctx x)))
    (sync/release! ctx e output) (sync/close! ctx e))
  (let [{:keys [ctx]} (context) e (machine ctx)
        short (bytes! ctx e [7 8]) wide (call ctx e "ByteArray.push._boxed" [(bytes! ctx e [7]) 8])
        wide2 (call ctx e "ByteArray.push._boxed" [(bytes! ctx e [7]) 8])
        _ (aset-byte ^bytes (.get ^java.lang.reflect.Field (:scalars ctx) wide2) 3 (unchecked-byte 255))
        output (share! ctx e (triple! ctx e short wide wide2)) [x y z] (fields ctx output)]
    (is (= [2 4 4] (mapv #(alength ^bytes (.get ^java.lang.reflect.Field (:scalars ctx) %)) [x y z])))
    (is (identical? short x)) (is (identical? wide y)) (is (identical? y z))
    (is (not (identical? x y))) (is (= [7 8] (b/payload ctx y))) (is (= 2 (c/rc ctx y)))
    (sync/release! ctx e output) (sync/close! ctx e)))

(deftest genuine-original-expr-constructors-retain-cached-bytes-and-share
  (let [{:keys [ctx]} (context {:genuine true}) e (machine ctx)
        a (call ctx e "Lean.Expr.bvar._override" [7]) b (call ctx e "Lean.Expr.bvar._override" [7])
        left (call ctx e "Lean.Expr.app._override" [a (call ctx e "Lean.Expr.bvar._override" [8])])
        right (call ctx e "Lean.Expr.app._override" [b (call ctx e "Lean.Expr.bvar._override" [8])])
        expected (vec (.get ^java.lang.reflect.Field (:scalars ctx) left))
        output (share! ctx e (pair! ctx e left right)) [x y] (fields ctx output)]
    (is (identical? x y)) (is (= 2 (c/rc ctx x)))
    (is (= expected (vec (.get ^java.lang.reflect.Field (:scalars ctx) x))))
    (sync/release! ctx e output) (sync/close! ctx e)))

(deftest persistent-and-logical-mt-constructors-rebuild-as-fresh-st
  (doseq [mode [:persistent :mt]]
    (let [{:keys [ctx source]} (context) e (machine ctx)
          input (if (= mode :persistent)
                  (first (j/install-graph! ctx e (j/prepared-graph ctx source (Object.)
                    [(j/graph-node ctx {:kind :ctor :id 1 :tag 0 :fields [7]})] [] [] [(j/graph-ref ctx 1)])))
                  (leaf! ctx e 7))
          _ (when (= mode :mt) (sharing/mark! ctx e input))
          output (share! ctx e input)]
      (is (not (identical? input output))) (is (= [7] (fields ctx output)))
      (is (= 1 (c/rc ctx output))) (is (false? (sharing/mt? ctx output)))
      (if (= mode :persistent) (is (= 0 (c/rc ctx input))) (is (h/private-value input "dead")))
      (sync/release! ctx e output) (sync/close! ctx e))))

(deftest opaque-ref-closure-and-task-identities-are-retained-without-descent
  (let [{:keys [ctx]} (context {:tasks true}) e (machine ctx)
        ref (call ctx e "ST.Prim.mkRef" [0 0 7 0])
        closure (j/make-closure! ctx e "share-leaf" [])
        task (call ctx e "Task.pure" [0 8])
        output (share! ctx e (triple! ctx e ref closure task)) [a b c] (fields ctx output)]
    (is (every? true? (map identical? [ref closure task] [a b c])))
    (is (= [1 1 1] (mapv #(c/rc ctx %) [a b c])))
    (sync/release! ctx e output) (is (every? #(h/private-value % "dead") [ref closure task])) (sync/close! ctx e)))

(deftest partial-output-fork-copies-candidates-table-ids-and-owner-aliases
  (let [{:keys [ctx]} (context) parent (machine ctx) source (pair! ctx parent (leaf! ctx parent 7) (leaf! ctx parent 7))]
    (j/start! ctx parent "ShareCommon.shareCommon'._boxed" [0 source])
    (until! ctx parent #(let [s (state parent) frames (when s (h/private-value s "frames")) top (when frames (.peek ^java.util.Deque frames))]
                        (and top (identical? source (h/private-value top "input"))
                             (= 1 (h/private-value top "cursor")) (= 1 (h/private-value top "stage")))))
    (let [s (state parent) frame (.peek ^java.util.Deque (h/private-value s "frames")) candidate (h/private-value frame "candidate")
          first-child (first (fields ctx candidate)) {:keys [engine roots]} (j/fork! ctx parent [source candidate first-child])
          child engine [cs cc cf] roots]
      (is (false? (j/advance! ctx parent 0)))
      (is (identical? cf (first (fields ctx cc)))) (is (= 1 (c/rc ctx first-child) (c/rc ctx cf)))
      (is (false? (h/private-value source "dead"))) (is (false? (h/private-value cs "dead")))
      (doseq [[e expected] [[parent candidate] [child cc]]]
        (let [output (sync/finish! ctx e) [x y] (fields ctx output)]
          (is (identical? expected output)) (is (identical? x y)) (is (= 2 (c/rc ctx x)))
          (sync/release! ctx e output)) (sync/close! ctx e)))))

(deftest duplicate-disposal-pauses-and-forks-its-native-order-release-transaction
  (let [{:keys [ctx]} (context) parent (machine ctx) source (pair! ctx parent (leaf! ctx parent 7) (leaf! ctx parent 7))]
    (j/start! ctx parent "ShareCommon.shareCommon'._boxed" [0 source])
    (until! ctx parent #(some-> (state parent) (h/private-value "discarding")))
    (let [release (sync/action parent) s (state parent) frame (.peek ^java.util.Deque (h/private-value s "frames"))
          duplicate (h/private-value frame "candidate") canonical (h/private-value frame "representative")
          {:keys [engine roots]} (j/fork! ctx parent [duplicate canonical]) child engine [cd cc] roots]
      (is (= 1 (h/private-value release "operation"))) (is (h/private-value duplicate "dead"))
      (is (false? (h/private-value frame "candidateOwned")))
      (is (= 1 (c/rc ctx canonical) (c/rc ctx cc)))
      (doseq [[e dead] [[parent duplicate] [child cd]]]
        (let [output (sync/finish! ctx e) [x y] (fields ctx output)]
          (is (h/private-value dead "dead")) (is (every? nil? (fields ctx dead)))
          (is (identical? x y)) (is (= 2 (c/rc ctx x))) (sync/release! ctx e output)) (sync/close! ctx e)))))

(deftest cycles-unknown-kinds-malformed-unicode-and-subclasses-reject-honestly
  (let [{:keys [ctx source]} (context) e (machine ctx)
        [cycle] (install! ctx e source [(j/graph-node ctx {:kind :ctor :id 1 :rc 99 :tag 0 :fields [(j/graph-ref ctx 1)]})] [(j/graph-ref ctx 1)])]
    (j/start! ctx e "ShareCommon.shareCommon'._boxed" [0 cycle])
    (is (re-find #"cycle outside" (c/failure #(sync/finish! ctx e))))
    (is (= "failed" (j/phase ctx e))) (is (false? (h/private-value cycle "dead")))
    (is (g/bad? #(j/fork! ctx e []))))
  (doseq [value [(String. (char-array [(char 0xd800)])) (String. (char-array [(char 0xdc00)]))
                (proxy [java.math.BigInteger] ["1"] (hashCode [] 0))]]
    (let [{:keys [ctx]} (context) e (machine ctx)]
      (is (g/bad? #(share! ctx e value))) (is (= "failed" (j/phase ctx e)))))
  (let [{:keys [ctx]} (context) e (machine ctx) input (leaf! ctx e 7)]
    (.setInt ^java.lang.reflect.Field (:tag ctx) input 254)
    (is (re-find #"Unsupported ShareCommon Node" (c/failure #(share! ctx e input))))
    (is (= 1 (c/rc ctx input))))
  (doseq [value [(Double/valueOf 1.5) (object-array 0)]]
    (let [{:keys [ctx]} (context) e (machine ctx) before (k/counters ctx e)]
      ;; Float rejects at external entry; an Object[] may enter the original
      ;; generic wrapper, but the native callee rejects it before primitive effects.
      (is (g/bad? #(share! ctx e value)))
      (is (= before (k/counters ctx e)))
      (if (= "idle" (j/phase ctx e)) (sync/close! ctx e)
        (is (= "failed" (j/phase ctx e)))))))

(deftest deep-traversal-is-iterative-and-work-failure-retains-the-owned-prefix
  (let [{:keys [ctx]} (context) e (machine ctx) root (reduce (fn [v _] (leaf! ctx e v)) 0 (range 512))
        output (share! ctx e root)]
    (is (= 0 (loop [v output n 512] (if (zero? n) v (recur (first (fields ctx v)) (dec n))))))
    (sync/release! ctx e output) (sync/close! ctx e))
  (let [{:keys [ctx]} (context) e (machine ctx) input (pair! ctx e (leaf! ctx e 7) (leaf! ctx e 8))]
    (j/start! ctx e "ShareCommon.shareCommon'._boxed" [0 input])
    (until! ctx e #(let [s (state e) top (when s (.peek ^java.util.Deque (h/private-value s "frames")))]
                    (and top (h/private-value top "candidateOwned"))))
    (let [s (state e) frame (.peek ^java.util.Deque (h/private-value s "frames")) out (h/private-value frame "candidate")]
      ;; Forged control bound, not a supported retry or guest graph edit.
      (sync/private-set! s "work" (long 8000000))
      (is (re-find #"work outside" (c/failure #(j/advance! ctx e 1))))
      (is (h/private-value frame "candidateOwned")) (is (= 1 (c/rc ctx out)))
      (is (false? (h/private-value input "dead"))) (is (= "failed" (j/phase ctx e))))))

(deftest opaque-promise-does-not-finalize-until-returned-output-is-released
  (let [spec (h/spec "watch" ["object" "object"] [false false] "object")
        base (binding [sync/*basis* *basis*] (sync/task-context [(h/ext "watch" spec)] [spec]))
        ctx (j/extend-program base (concat (map #(get % "row") (records)) (x/raw (helpers))))
        parent (machine ctx) promise (sync/watching-promise! ctx parent) input (leaf! ctx parent promise)
        output (share! ctx parent input)]
    (is (nil? (j/host-request ctx parent))) (is (h/private-value input "dead"))
    (is (identical? promise (first (fields ctx output)))) (is (= 1 (c/rc ctx promise)))
    (j/start-release! ctx parent output 1)
    (let [request (h/request! ctx parent) {:keys [engine]} (j/fork! ctx parent []) child engine]
      (is (= "watch" (j/request-value request "symbol")))
      (doseq [e [parent child]]
        (j/resume-host! ctx e (j/host-request ctx e) 0)
        (is (= 0 (sync/finish! ctx e))) (is (sync/quiescent? ctx e)) (sync/close! ctx e)))))

(defn check! [basis] (binding [*basis* basis] (run-tests 'java-ir-share-common-checks)))
