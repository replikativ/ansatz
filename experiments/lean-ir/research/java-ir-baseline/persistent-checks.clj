(ns java-ir-persistent-checks
  "Pinned markPersistent identity/RC semantics and bounded atomic admission."
  (:require [clojure.test :refer [deftest is run-tests]] [clojure.data.json :as json]
            [java-ir-baseline :as j] [java-ir-baseline-checks :as c]
            [java-ir-extern-checks :as x] [java-ir-generation-checks :as g]
            [java-ir-host-checks :as host] [java-ir-header-checks :as h]
            [java-ir-logical-sharing-checks :as sharing] [java-ir-ref-checks :as ref]
            [java-ir-array-checks :as array] [java-ir-byte-array-checks :as byte]
            [java-ir-task-map-checks :as task] [java-ir-sync-task-checks :as sync]
            [lean-compatibility-corpus :as corpus]))
(def ^:dynamic *basis* nil)
(def directory "test/fixtures/java-mark-persistent-runtime/")
(defn records []
  (mapv (fn [r] (assoc r "row" (json/read-str (slurp (str directory (get r "file"))))))
        (get (json/read-str (slurp (str directory "provenance.json"))) "rows")))
(defn originals [] (mapv #(get % "row") (records)))
(defn raw-name [] (get (first (originals)) "name"))
(defn helpers []
  [(c/decl "persistent-keep-first" [(c/p 1 "object") (c/p 2 "object")] "object"
     ["dec" {:idx 2} 1 true false (c/ret 1)])
   (c/decl "persistent-fresh" [(c/p 1 "object")] "object"
     (c/let-ir 2 "object" (c/ctor 0 [(c/v 1)] 0) (c/ret 2)))
   (c/decl "persistent-pair" [(c/p 1 "object") (c/p 2 "object")] "object"
     (c/let-ir 3 "object" (c/ctor 0 [(c/v 1) (c/v 2)] 0) (c/ret 3)))
   (c/decl "persistent-fap" [(c/p 1 "object")] "tobject"
     (c/let-ir 2 "tobject" {:fap {:c (raw-name) :ys ["erased" (c/v 1) "erased"]}} (c/ret 2)))
   (c/decl "persistent-pap" [(c/p 1 "object")] "object"
     (c/let-ir 2 "object" {:pap {:c (get (second (originals)) "name") :ys ["erased" (c/v 1)]}} (c/ret 2)))
   (c/decl "persistent-ap" [(c/p 1 "object")] "object"
     (c/let-ir 2 "object" {:ap {:x {:idx 1} :ys ["erased"]}} (c/ret 2)))])
(defn direct [row]
  (let [self (get row "name")]
    (vals (into {} (for [x (tree-seq coll? seq (get-in row ["ir" "fdecl" "body"]))
                        :when (map? x) :let [call (or (get x "fap") (get x "pap"))]
                        :when call :let [n (get call "c")] :when (not= n self)] [(json/write-str n) n])))))
(defn context []
  (let [additional (concat (map #(get % "row") (concat (ref/originals) (array/originals) (byte/originals)))
                           task/originals task/task-rows
                           (map #(get % "row") (json/read-str (slurp "test/fixtures/java-task-sync-runtime/original-rows.json"))))
        models (mapv (fn [row] {"row" row "sha256" h/digest}) (x/raw (concat additional (helpers))))
        entries (vals (into {} (map (juxt #(get-in % ["row" "name"]) identity) (concat (records) models))))
        base (j/prepare-host-program *basis* [] [])
        source (j/source-binding base {:fixture (corpus/sha256 (str directory "provenance.json")) :models true})
        headers (into {} (map (fn [r] [(get-in r ["row" "name"])
                           (j/declaration-header source (get r "row") (get r "sha256"))]) entries))
        ctx (j/register-headers base (vec (vals headers)) [])]
    (reduce (fn [ctx r]
              (let [row (get r "row")]
                (if (get-in row ["ir" "fdecl"])
                  (j/materialize-body ctx (headers (get row "name")) row
                    (mapv headers (direct row))) ctx))) ctx entries)))
(defn fresh [ctx e value] (j/call ctx e "persistent-fresh" [value]))
(defn mark! [ctx e value] (j/call ctx e "Runtime.markPersistent" [0 value 0]))
(defn fields [ctx value] (.get ^java.lang.reflect.Field (:fields ctx) value))
(defn counters [e] (mapv #(host/private-value e %) ["allocations" "stores" "retains" "releases" "shellDeletes"]))
(defn private-mark! [ctx e value]
  (sharing/private-call ctx e "persistentIntrinsic" [Object Object Object] [0 value 0]))

(deftest actual-original-byte-digests-and-exact-abi
  (let [method (.getMethod ^Class (:class *basis*) "validateExternAbi" (into-array Class [java.util.Map]))
        raw (first (originals))]
    (doseq [r (records)] (is (= (get r "sha256") (corpus/sha256 (str directory (get r "file"))))))
    (is (= "lean_runtime_mark_persistent" (j/invoke-static method [raw])))
    (doseq [i (range 3)]
      (is (g/bad? #(j/invoke-static method [(assoc-in raw ["ir" "extern" "xs" i "borrow"] true)]))))
    (doseq [i (range 3)]
      (is (g/bad? #(j/invoke-static method [(assoc-in raw ["ir" "extern" "xs" i "ty"] "object")]))))
    (is (g/bad? #(j/invoke-static method [(assoc-in raw ["ir" "extern" "type"] "object")])))))

(deftest direct-original-boxed-fap-pap-ap-preserve-object-and-atomic-identities
  (doseq [explicit? [false true]]
    (let [ctx (assoc (context) :explicit explicit?) e (j/machine ctx)]
      (try
        (doseq [label ["Runtime.markPersistent" "Runtime.markPersistent._boxed" "persistent-fap"]]
          (let [value (fresh ctx e 0) before (counters e)
                result (j/call ctx e label (if (= label "persistent-fap") [value] [0 value 0]))]
            (is (identical? value result)) (is (zero? (c/rc ctx value)))
            (is (= before (counters e)))))
        (let [value (fresh ctx e 0) partial (j/call ctx e "persistent-pap" [value])]
          (is (identical? value (j/call ctx e "persistent-ap" [partial])))
          (is (zero? (c/rc ctx value))))
        (doseq [value [0 17 "source-string" (biginteger "18446744073709551616")]]
          (is (identical? value (mark! ctx e value))))
        (finally (j/close! ctx e))))))

(deftest raw-native-ap-preflight-preserves-closure-and-capture-credits-on-error
  (doseq [explicit? [false true]]
    (let [ctx (assoc (context) :explicit explicit?) e (j/machine ctx)
          leaf (fresh ctx e 0) root (fresh ctx e leaf)
          partial (j/make-closure! ctx e "Runtime.markPersistent" [0 root])]
      (try
        (.setInt ^java.lang.reflect.Field (:tag ctx) leaf 244)
        (let [before (counters e)]
          (is (g/bad? #(sharing/private-call ctx e (if explicit? "prepareExplicitApply" "apply")
                        [Object (class (object-array 0))] [partial (object-array [(long 0)])])))
          (is (= before (counters e)))
          (is (false? (sharing/dead? partial)))
          (is (= [1 1 1] (mapv #(c/rc ctx %) [partial root leaf])))
          (is (identical? root (aget ^objects (fields ctx partial) 1))))
        (.setInt ^java.lang.reflect.Field (:tag ctx) leaf 0)
        (is (identical? root (j/call ctx e "persistent-ap" [partial])))
        (is (= [0 0] [(c/rc ctx root) (c/rc ctx leaf)]))
        (finally (j/close! ctx e))))))

(deftest cyclic-shared-owning-graph-and-rc-zero-traversal-stop
  (let [ctx (context) e (j/machine ctx) source (j/source-binding ctx (Object.))
        [root stopped child] (j/install-graph! ctx e
          (j/selected-owner-graph ctx source (Object.)
            [(j/graph-node ctx {:kind :ctor :id 1 :rc 1 :tag 0 :fields [(j/graph-ref ctx 2) (j/graph-ref ctx 2)]})
             (j/graph-node ctx {:kind :ref :id 2 :rc 1 :fields [(j/graph-ref ctx 1)]})
             (j/graph-node ctx {:kind :ref :id 3 :rc 0 :fields [(j/graph-ref ctx 4)]})
             (j/graph-node ctx {:kind :ctor :id 4 :rc 1 :tag 0 :fields [0]})]
            [] [] [(j/graph-ref ctx 1) (j/graph-ref ctx 3) (j/graph-ref ctx 4)]))
        cell (aget ^objects (fields ctx root) 0)]
    (try
      (is (every? #(pos? (c/rc ctx %)) [root cell child]) "positive cycle and contrasted payload are collectable before marking")
      (is (identical? root (mark! ctx e root)))
      (is (identical? cell (aget ^objects (fields ctx root) 1)))
      (is (= [0 0] [(c/rc ctx root) (c/rc ctx cell)]))
      (let [before (counters e)] (mark! ctx e root) (is (= before (counters e))))
      (mark! ctx e stopped) (is (pos? (c/rc ctx child)))
      (finally (j/release! ctx e child) (j/close! ctx e)))))

(deftest persistent-ref-new-payload-is-mt-and-remains-collectable-and-fork-local
  (let [ctx (context) e (j/machine ctx) old (fresh ctx e 0) cell (ref/make-ref! ctx e old)
        word (sharing/private-call ctx e "pointerWord" [Object] [cell])
        metadata (sharing/metadata cell)]
    (try
      (mark! ctx e cell)
      (is (= word (sharing/private-call ctx e "pointerWord" [Object] [cell])))
      (is (identical? metadata (sharing/metadata cell))) (is (= [0 0] [(c/rc ctx cell) (c/rc ctx old)]))
      (let [fork (j/fork! ctx e [cell cell]) child (:engine fork) [copy alias] (:roots fork)
            incoming (fresh ctx child 0)]
        (try
          (is (identical? copy alias)) (is (not (identical? copy cell)))
          (is (= word (sharing/private-call ctx child "pointerWord" [Object] [copy])))
          (ref/ref-set! ctx child copy incoming)
          (is (sharing/mt? ctx incoming)) (is (= 1 (c/rc ctx incoming)))
          (is (identical? old (aget ^objects (fields ctx cell) 0)))
          (mark! ctx child copy) (is (= 1 (c/rc ctx incoming)) "rc0 Ref does not remark future payloads")
          (ref/ref-set! ctx child copy 0) (is (sharing/dead? incoming))
          (finally (j/close! ctx child))))
      (finally (j/close! ctx e)))))

(deftest constructor-array-bytes-ref-ready-task-and-closure-owning-edges
  (let [ctx (context) e (j/machine ctx) leaf (fresh ctx e 0)
        capture (j/make-closure! ctx e "persistent-keep-first" [leaf])
        bytes (byte/push! ctx e (j/call ctx e "ByteArray.mk._boxed" [(array/empty! ctx e 0)]) 7)
        a (array/push! ctx e (array/push! ctx e (array/empty! ctx e 4) capture) bytes)
        ready (task/pure ctx e a) cell (ref/make-ref! ctx e ready) root (fresh ctx e cell)]
    (try
      (is (identical? root (mark! ctx e root)))
      (is (every? #(zero? (c/rc ctx %)) [root cell ready a capture bytes leaf]))
      (is (= [7] (byte/payload ctx bytes)))
      (is (every? #(not (sharing/mt? ctx %)) [root cell ready a capture bytes leaf]))
      (finally (j/close! ctx e)))))

(deftest malformed-descendant-interrupt-and-placeholder-errors-are-atomic
  (let [ctx (context) e (j/machine ctx) leaf (fresh ctx e 0) root (fresh ctx e leaf)]
    (try
      (let [before (counters e)]
        (.setInt ^java.lang.reflect.Field (:tag ctx) leaf 244)
        (is (g/bad? #(private-mark! ctx e root)))
        (is (= [1 1] [(c/rc ctx root) (c/rc ctx leaf)])) (is (= before (counters e)))
        (.setInt ^java.lang.reflect.Field (:tag ctx) leaf 0)
        (.interrupt (Thread/currentThread))
        (try (is (g/bad? #(private-mark! ctx e root)))
             (finally (Thread/interrupted)))
        (is (= [1 1] [(c/rc ctx root) (c/rc ctx leaf)]))
        (is (g/bad? #(j/call ctx e "Runtime.markPersistent" [1 root 0])))
        (is (g/bad? #(j/call ctx e "Runtime.markPersistent" [0 root 1])))
        (is (= [1 1] [(c/rc ctx root) (c/rc ctx leaf)])))
      (finally (j/release! ctx e root) (j/close! ctx e)))))

(deftest foreign-source-closure-rejects-before-marking-its-parent
  (let [ctx (context) foreign (context) e (j/machine ctx) other (j/machine foreign)
        root (fresh ctx e 0) closure (j/make-closure! foreign other "persistent-fresh" [])]
    (try
      (aset ^objects (fields ctx root) 0 closure)
      (is (g/bad? #(private-mark! ctx e root)))
      (is (= [1 1] [(c/rc ctx root) (c/rc foreign closure)]))
      (finally
        (aset ^objects (fields ctx root) 0 (long 0))
        (j/release! ctx e root) (j/release! foreign other closure)
        (j/close! ctx e) (j/close! foreign other)))))

(deftest runtime-created-tasks-and-promises-reject-before-any-rc-change
  (let [ctx (sync/active (context)) e (j/machine ctx)
        promise (sync/promise! ctx e) task (sync/result-task! ctx e promise)
        root (fresh ctx e task)]
    (try
      (doseq [value [promise task root]]
        (let [before (counters e) counts (mapv #(c/rc ctx %) [promise task root])]
          (is (g/bad? #(private-mark! ctx e value)))
          (is (= before (counters e)))
          (is (= counts (mapv #(c/rc ctx %) [promise task root])))))
      (finally (sync/release! ctx e root) (sync/release! ctx e promise) (sync/close! ctx e)))))

(deftest owning-edge-bound-rejects-before-marking-any-validated-prefix
  (let [ctx (context) e (j/machine ctx) root (array/empty! ctx e 4000)
        constructor (.getDeclaredConstructor ^Class (:node-class ctx)
                      (into-array Class [Integer/TYPE Integer/TYPE Integer/TYPE]))
        state (sharing/metadata root)
        size (.getDeclaredField (class state) "size")]
    (.setAccessible constructor true) (.setAccessible size true)
    (dotimes [i 4000]
      (let [child (.newInstance constructor (object-array [(int 0) (int 255) (int 0)]))]
        (java.util.Arrays/fill ^objects (fields ctx child) (long 0))
        (aset ^objects (fields ctx root) i child)))
    (.setInt size state 4000)
    (try
      (let [before (counters e)]
        (is (re-find #"edge bound" (c/failure #(private-mark! ctx e root))))
        (is (= before (counters e)))
        (is (= 1 (c/rc ctx root)))
        (is (every? #(= 1 (c/rc ctx %)) (seq (fields ctx root)))))
      (finally (j/release! ctx e root) (j/close! ctx e)))))

(deftest deep-owning-graph-is-iterative
  (let [ctx (context) e (j/machine ctx) leaf (fresh ctx e 0)
        root (loop [n 4000 value leaf] (if (zero? n) value (recur (dec n) (fresh ctx e value))))]
    (try
      (mark! ctx e root) (is (= [0 0] [(c/rc ctx root) (c/rc ctx leaf)]))
      (finally (j/close! ctx e)))))

(defn check! [basis] (binding [*basis* basis] (run-tests 'java-ir-persistent-checks)))
