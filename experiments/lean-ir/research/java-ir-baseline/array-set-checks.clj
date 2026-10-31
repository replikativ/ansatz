(ns java-ir-array-set-checks
  "Original checked array update, owner/COW parity and resumable finalizer boundaries."
  (:require [clojure.test :refer [deftest is run-tests]]
            [clojure.data.json :as json] [clojure.edn :as edn]
            [java-ir-baseline :as j] [java-ir-baseline-checks :as c]
            [java-ir-extern-checks :as x] [java-ir-host-checks :as host]
            [java-ir-generation-checks :as g] [java-ir-array-checks :as a]
            [java-ir-logical-sharing-checks :as sharing]
            [java-ir-sync-task-checks :as sync]
            [lean-compatibility-corpus :as corpus]))
(def ^:dynamic *basis* nil)
(def fixture "test/fixtures/java-array-set-runtime/original-rows.json")
(def provenance-file "test/fixtures/java-array-set-runtime/provenance.edn")
(defn originals [] (json/read-str (slurp fixture)))
(def apply-row
  (c/decl "apply-set" (mapv #(c/p % "object") [1 2 3]) "object"
    (c/let-ir 4 "object" {:ap {:x {:idx 1} :ys [(c/v 2) (c/v 3)]}} (c/ret 4))))
(defn context []
  (assoc *basis* :program (j/invoke-static (:prepare *basis*)
    [(vec (concat (map #(get % "row") (concat (a/originals) (originals)))
                   (x/raw [apply-row
                     (c/decl "fresh-set-value" [(c/p 1 "object")] "object"
                       (c/let-ir 2 "object" (c/ctor 0 [(c/v 1)] 0) (c/ret 2)))])))])))
(defn fresh [ctx engine value] (j/call ctx engine "fresh-set-value" [value]))
(defn counters [engine]
  (mapv #(host/private-value engine %) ["allocations" "stores" "retains" "releases" "shellDeletes"]))
(defn update! [ctx engine target index value boxed?]
  (j/call ctx engine (if boxed? "Array.set!._boxed" "Array.set!") [0 target index value]))

(deftest exact-native-signature-and-authentic-owned-wrapper
  (let [rows (originals) manifest (edn/read-string (slurp provenance-file))
        raw (get-in (first rows) ["row" "ir" "extern"])]
    (is (= 2 (count rows)))
    (is (= (:fixture-sha256 manifest) (corpus/sha256 fixture)))
    (is (= "819816b2e0a3bf405af45ae5c7af2491d8f5bee6" (:lean-commit manifest)))
    (is (= ["erased" "object" "tobject" "tobject"] (mapv #(get % "ty") (get raw "xs"))))
    (is (= [false false true false] (mapv #(get % "borrow") (get raw "xs"))))
    (is (= "lean_array_set"
           (j/invoke-static (.getMethod ^Class (:class *basis*) "validateExternAbi" (into-array Class [java.util.Map]))
             [(get (first rows) "row")])))
    (doseq [changed [(assoc-in (get (first rows) "row") ["ir" "extern" "xs" 2 "borrow"] false)
                     (update-in (get (first rows) "row") ["ir" "extern" "xs"] conj {"x" {"idx" 5} "ty" "erased" "borrow" false})]]
      (is (re-find #"Captured extern ABI mismatch" (c/failure #(j/invoke-static
         (.getMethod ^Class (:class *basis*) "validateExternAbi" (into-array Class [java.util.Map])) [changed])))))))

(deftest native-and-original-boxed-unique-update-transfer-only-the-replaced-edge
  (doseq [boxed? [false true] index [0 (biginteger 0)]]
    (let [ctx (context) engine (j/machine ctx) old (fresh ctx engine 7) replacement (fresh ctx engine 8)
          source (a/push! ctx engine (a/empty! ctx engine 3) old)
          before (counters engine) answer (update! ctx engine source index replacement boxed?)]
      (is (identical? source answer))
      (is (= [replacement] (a/elements ctx answer)))
      (is (host/private-value old "dead")) (is (= 1 (c/rc ctx replacement)))
      (is (= (first before) (first (counters engine))))
      (is (= (inc (second before)) (second (counters engine))))
      (j/release! ctx engine answer) (is (host/private-value replacement "dead")) (j/close! ctx engine))))

(deftest shared-and-persistent-copies-preserve-every-live-alias
  (doseq [rc [0 99]]
    (let [ctx (context) engine (j/machine ctx) binding (j/source-binding ctx (Object.)) r #(j/graph-ref ctx %)
          [source] (j/install-graph! ctx engine (j/selected-owner-graph ctx binding (Object.)
             [(j/graph-node ctx {:kind :array :id 1 :rc rc :fields [(r 2) (r 2)]})
              (j/graph-node ctx {:kind :ctor :id 2 :rc 99 :tag 0 :fields [7]})] [] [] [(r 1)]))
          value (first (a/elements ctx source)) replacement (fresh ctx engine 9)]
      (j/retain! ctx engine source)
      (let [answer (update! ctx engine source 1 replacement true)]
        (is (not (identical? source answer)))
        (is (= [value value] (a/elements ctx source))) (is (= [value replacement] (a/elements ctx answer)))
        (is (= 3 (c/rc ctx value)))
        (j/release! ctx engine answer) (is (= 2 (c/rc ctx value)))
        (is (host/private-value replacement "dead")))
      (j/release! ctx engine source) (j/close! ctx engine))))

(deftest logical-mt-count-one-copy-and-fork-isolation
  (let [ctx (context) parent (j/machine ctx) source (a/push! ctx parent (a/empty! ctx parent 2) 7)]
    (sharing/mark! ctx parent source)
    (is (= 1 (c/rc ctx source))) (is (sharing/mt? ctx source))
    (let [answer (update! ctx parent source 0 8 false)
          packet (j/fork! ctx parent [answer]) child (:engine packet) copy (first (:roots packet))
          changed (update! ctx child copy 0 9 true)]
      (is (not (identical? source answer))) (is (host/private-value source "dead"))
      (is (= [8] (a/elements ctx answer))) (is (= [9] (a/elements ctx changed)))
      (j/release! ctx child changed) (j/close! ctx child)
      (j/release! ctx parent answer) (j/close! ctx parent))))

(deftest raw-preflight-rejects-panic-domains-and-invalid-carriers-before-effects
  (let [ctx (context) engine (j/machine ctx) old (fresh ctx engine 7) replacement (fresh ctx engine 8)
        source (a/push! ctx engine (a/empty! ctx engine 4) old)]
    (doseq [index [1 Long/MAX_VALUE (.shiftLeft java.math.BigInteger/ONE 80)]]
      (let [before (counters engine)]
        (is (re-find #"Array.set! panic path" (c/failure #(update! ctx engine source index replacement false))))
        (is (= before (counters engine))) (is (= "idle" (j/phase ctx engine)))
        (is (= [old] (a/elements ctx source))) (is (= 1 (c/rc ctx replacement)))))
    (doseq [args [[1 source 0 replacement] [0 source -1 replacement]
                  [0 source (biginteger -1) replacement] [0 old 0 replacement]
                  [0 source 0 (Double/valueOf 0.5)] [0 source 0 (object-array 0)]]]
      (let [before (counters engine)]
        (is (g/bad? #(j/call ctx engine "Array.set!" args)))
        (is (= before (counters engine))) (is (= "idle" (j/phase ctx engine)))))
    (let [before (counters engine)]
      ;; The slot's old credit is not an owned replacement argument.
      (is (g/bad? #(update! ctx engine source 0 old false)))
      (is (= before (counters engine))) (is (= 1 (c/rc ctx old))))
    (j/retain! ctx engine old)
    (is (identical? source (update! ctx engine source (biginteger 0) old false)))
    (is (= 1 (c/rc ctx old)))
    (is (identical? source (update! ctx engine source 0 replacement false)))
    (is (host/private-value old "dead"))
    (j/release! ctx engine source) (j/close! ctx engine)))

(deftest owning-ap-range-preflight-preserves-captures-and-replacement-before-transfer
  (doseq [index [1 (.shiftLeft java.math.BigInteger/ONE 80)]]
    (let [ctx (context) engine (j/machine ctx) old (fresh ctx engine 7) replacement (fresh ctx engine 8)
          source (a/push! ctx engine (a/empty! ctx engine 1) old)
          closure (j/make-closure! ctx engine "Array.set!" [0 source]) before (counters engine)]
      (is (re-find #"Array.set! panic path"
                   (c/failure #(j/call ctx engine "apply-set" [closure index replacement]))))
      (is (= before (counters engine)))
      (is (false? (host/private-value closure "dead")))
      (is (= 1 (c/rc ctx closure) (c/rc ctx source) (c/rc ctx replacement)))
      (is (= [old] (a/elements ctx source)))
      ;; The inactive failed invocation is discarded. This does not claim a
      ;; general failed-frame cleanup/rollback contract for the legacy driver.
      )))

(deftest active-native-replacement-waits-for-promise-callback-and-forks-once
  (let [spec (host/spec "watch" ["object" "object"] [false false] "object")
        base (binding [sync/*basis* *basis*] (sync/task-context [(host/ext "watch" spec) apply-row] [spec]))
        ctx (j/extend-program base (mapv #(get % "row") (originals)))]
    (doseq [route [:raw :boxed :ap]]
      (let [parent (j/machine ctx) promise (sync/watching-promise! ctx parent)
            source (a/push! ctx parent (a/empty! ctx parent 1) promise)
            replacement (j/call ctx parent "cons" [8])]
        (case route
          :raw (j/start! ctx parent "Array.set!" [0 source (biginteger 0) replacement])
          :boxed (j/start! ctx parent "Array.set!._boxed" [0 source 0 replacement])
          :ap (j/start! ctx parent "apply-set" [(j/make-closure! ctx parent "Array.set!" [0 source]) 0 replacement]))
        (let [_ (host/request! ctx parent) native (sync/enclosing-native parent)
              packet (j/fork! ctx parent [source replacement]) child (:engine packet) [copy copied-value] (:roots packet)]
          (is (identical? source (host/private-value native "output")))
          (is (true? (host/private-value native "releaseClaimed")))
          (is (host/private-value promise "dead"))
          (is (identical? promise (first (a/elements ctx source))))
          (is (= 1 (c/rc ctx replacement)))
          (is (false? (j/advance! ctx parent 0)))
          (doseq [[engine array value] [[parent source replacement] [child copy copied-value]]]
            (j/resume-host! ctx engine (j/host-request ctx engine) 0)
            (is (identical? array (sync/finish! ctx engine)))
            (is (identical? value (first (a/elements ctx array))))
            (is (= 1 (c/rc ctx value)))
            (sync/release! ctx engine array) (sync/close! ctx engine)))))))

(defn check! [basis] (binding [*basis* basis] (run-tests 'java-ir-array-set-checks)))
