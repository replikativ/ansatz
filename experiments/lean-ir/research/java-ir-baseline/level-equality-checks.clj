(ns java-ir-level-equality-checks
  "Structural Level equality. Graph/cache adversaries are explicitly models."
  (:require [clojure.test :refer [deftest is]] [clojure.data.json :as json]
            [java-ir-baseline :as j] [java-ir-baseline-checks :as c]
            [java-ir-extern-checks :as x] [java-ir-host-checks :as host]
            [java-ir-generation-checks :as g] [java-ir-continuation-checks :as k]
            [java-ir-expr-equality-checks :as eq] [lean-compatibility-corpus :as corpus]))
(def ^:dynamic *basis* nil)
(def directory "test/fixtures/java-level-equality-runtime/")
(defn records [] (json/read-str (slurp (str directory "original-rows.json"))))
(defn record [label] (first (filter #(= label (get % "label")) (records))))
(defn named [label] (get-in (record label) ["row" "name"]))
(defn helpers []
  [(c/decl "model-level-borrow" [(assoc (c/p 1 "tobject") :borrow true) (assoc (c/p 2 "tobject") :borrow true)] "uint8"
     (c/let-ir 3 "uint8" {:fap {:c (named "Lean.Level.beq") :ys [(c/v 1) (c/v 2)]}} (c/ret 3)))
   (c/decl "level-apply-two" [(c/p 1 "object") (c/p 2 "tobject") (c/p 3 "tobject")] "tobject"
     (c/let-ir 4 "tobject" {:ap {:x {:idx 1} :ys [(c/v 2) (c/v 3)]}} (c/ret 4)))
   (c/decl "level-apply-one" [(c/p 1 "object") (c/p 2 "tobject")] "tobject"
     (c/let-ir 3 "tobject" {:ap {:x {:idx 1} :ys [(c/v 2)]}} (c/ret 3)))])
(defn context
  ([] (context []))
  ([extra] (assoc *basis* :program (j/invoke-static (:prepare *basis*)
    [(x/raw (concat (map #(get % "row") (eq/records)) (map #(get % "row") (records))
                    (helpers) extra))]))))
(defn model-context [] (let [ctx (context)] (assoc ctx :engine (j/machine ctx))))
(defn compare-level [ctx a b] (j/call ctx (:engine ctx) "model-level-borrow" [a b]))
(defn owned-compare [ctx e a b]
  (j/retain! ctx e a) (j/retain! ctx e b)
  (j/call ctx e "Lean.Level.beq._boxed" [a b]))
(defn failure-packet [ctx e]
  {:phase (j/phase ctx e) :counters (k/counters ctx e)
   :slots (vec (host/private-value e "objects"))
   :numbers (vec (host/private-value e "numbers"))
   :continuations (vec (host/private-value e "continuations"))
   :control (mapv #(host/private-value e %)
              ["bp" "sp" "jbp" "jsp" "continuationDepth" "active" "entry"
               "failedHostRequest" "failedCodeRequest" "failedRuntimeAction"
               "untrackedFailure" "pendingOwnedResult" "closed"])})
(defn finish-probe! [ctx e]
  (if (= "failed" (j/phase ctx e))
    ;; Explicit failure retains its activation/owners. The existing engine has
    ;; no managed cleanup for these pure probes: assert rejection, preserve the
    ;; packet, then discard this probe. Never reset state or claim a close.
    (let [before (failure-packet ctx e)]
      (is (re-find #"requires ownership cleanup" (c/failure #(j/close! ctx e))))
      (is (= before (failure-packet ctx e)))
      (is (= "failed" (j/phase ctx e))))
    (j/close! ctx e)))

(deftest authenticated-raw-boxed-and-complete-Level-extern-family
  (let [p (json/read-str (slurp (str directory "provenance.json")))
        raw (get-in (record "Lean.Level.beq") ["row" "ir" "extern"])
        boxed (get-in (record "Lean.Level.beq._boxed") ["row" "ir" "fdecl"])]
    (is (= 2 (count (records))))
    (is (= (get p "fixture-sha256") (corpus/sha256 (str directory "original-rows.json"))))
    (doseq [[file sha] (get p "shared-fixtures")] (is (= sha (corpus/sha256 (str directory file)))))
    (is (= [["tobject" "tobject"] [true true] "uint8"]
           [(mapv #(get % "ty") (get raw "xs")) (mapv #(get % "borrow") (get raw "xs")) (get raw "type")]))
    (is (= [["tobject" "tobject"] [false false] "tagged"]
           [(mapv #(get % "ty") (get boxed "xs")) (mapv #(get % "borrow") (get boxed "xs")) (get boxed "type")]))
    ;; Level.lean has exactly mk_data and structural beq externs; eqv is not bound.
    (is (= "lean_level_eq" (get-in raw ["ext" "entries" 0 "standard" "fn"])))
    (let [row (get (record "Lean.Level.beq") "row")
          validate (.getMethod ^Class (:class *basis*) "validateExternAbi" (into-array Class [java.util.Map]))]
      (is (= "lean_level_eq" (j/invoke-static validate [row])))
      (doseq [invalid [(assoc-in row ["ir" "extern" "xs" 0 "borrow"] false)
                       (assoc-in row ["ir" "extern" "xs" 0 "ty"] "object")
                       (assoc-in row ["ir" "extern" "type"] "uint64")]]
        (is (g/bad? #(j/invoke-static validate [invalid])))))
    (is (= "lean_level_mk_data" (get-in (eq/record "Lean.Level.mkData") ["row" "ir" "extern" "ext" "entries" 0 "standard" "fn"])))
    (is (g/bad? #(j/prepare-host-program *basis* [] [(host/spec "lean_level_eq" ["tobject" "tobject"] [true true] "uint8")])))))

(deftest genuine-original-constructors-owned-wrappers-and-AP
  (let [ctx (context) e (j/machine ctx)
        make-level (fn [tag]
                     (case tag
                       0 (j/call ctx e "Lean.Level.zero._override" [])
                       1 (j/call ctx e "Lean.Level.succ._override" [0])
                       2 (j/call ctx e "Lean.Level.max._override" [0 0])
                       3 (j/call ctx e "Lean.Level.imax._override" [0 0])
                       (let [n (j/call ctx e "Lean.Name.str._override" [0 "u"])]
                         (j/call ctx e (if (= tag 4) "Lean.Level.param._override" "Lean.Level.mvar._override") [n]))))]
    (try
      (doseq [tag (range 6)]
        (let [a (make-level tag) b (make-level tag)]
          (try
            (is (= 1 (owned-compare ctx e a b)))
            (let [closure (j/make-closure! ctx e "Lean.Level.beq._boxed" [])]
              (j/retain! ctx e a) (j/retain! ctx e b)
              (is (= 1 (j/call ctx e "level-apply-two" [closure a b]))))
            (when (pos? tag) (is (= 1 (c/rc ctx a) (c/rc ctx b))))
            (finally (j/release! ctx e a) (j/release! ctx e b)))))
      (finally (finish-probe! ctx e)))))

(deftest models-all-six-tags-ordered-children-and-native-cache-rules
  (let [ctx (model-context) e (:engine ctx) b (eq/model-builder ctx) add (:add b) level (:level b) nm (:name b)
        u (nm "u") v (nm "v") pu (level 4 [u]) pv (level 4 [v]) mu (level 5 [u])
        cases [[0 0 1] [0 (level 1 [0]) 0]
               [(level 1 [0]) (level 1 [0]) 1]
               [pu (level 4 [(nm "u")]) 1] [pu pv 0] [pu mu 0]
               [mu (level 5 [(nm "u")]) 1]
               [(level 2 [pu pv]) (level 2 [pu pv]) 1]
               [(level 2 [pu pv]) (level 2 [pv pu]) 0]
               [(level 3 [pu pv]) (level 2 [pu pv]) 0]
               [(level 3 [pu pv]) (level 3 [pu pv]) 1]
               ;; Semantic equivalence/normalization is deliberately absent.
               [(level 2 [pu pu]) pu 0] [(level 3 [pu 0]) 0 0]
               [(add 1 [0] 8 9 0) (add 1 [0] 8 (+ 9 (bit-shift-left 1 40)) 0) 0]
               [(add 2 [pu pv] 8 9 0) (add 2 [pu pv] 8 10 0) 0]
               [(add 4 [u] 8 9 0) (add 4 [u] 8 (+ 9 (bit-shift-left 1 40)) 0) 1]
               [(add 5 [u] 8 9 0) (add 5 [u] 8 (+ 9 (bit-shift-left 1 32)) 0) 1]
               [(add 1 [0] 8 9 0) (add 1 [0] 8 (+ 9 (bit-shift-left 1 32)) 0) 1]]
        roots ((:finish b) (vec (mapcat #(take 2 %) cases))) counts (k/counters ctx e)
        snapshots (mapv #(when-not (number? %) [(c/rc ctx %) (vec (host/private-value % "fields"))
                                               (vec (host/private-value % "scalars")) (host/private-value % "metadata")]) roots)]
    (try
      (doseq [[i [_ _ expected]] (map-indexed vector cases)]
        (is (= expected (compare-level ctx (nth roots (* 2 i)) (nth roots (inc (* 2 i)))))))
      (is (= counts (k/counters ctx e)))
      (is (= snapshots (mapv #(when-not (number? %) [(c/rc ctx %) (vec (host/private-value % "fields"))
                         (vec (host/private-value % "scalars")) (host/private-value % "metadata")]) roots)))
      (finally (finish-probe! ctx e)))))

(deftest borrowed-root-PAP-factory-import-and-host-registration-fences
  (let [ctx (context) e (j/machine ctx)]
    (try
      (is (g/bad? #(j/call ctx e "Lean.Level.beq" [0 0]))) (is (= "idle" (j/phase ctx e)))
      (is (g/bad? #(j/make-closure! ctx e "Lean.Level.beq" [])))
      (is (g/bad? #(context [(c/decl "bad-level-pap" [] "object"
                       (c/let-ir 1 "object" {:pap {:c (named "Lean.Level.beq") :ys []}} (c/ret 1)))])))
      (let [base (j/prepare-host-program *basis* [] []) source (j/source-binding base (Object.))
            r (record "Lean.Level.beq") h (j/declaration-header source (get r "row") (get r "sha256"))
            next (j/register-headers base [h]) engine (j/machine next)]
        (try
          (is (g/bad? #(j/install-graph! next engine
                  (j/prepared-graph next source (Object.) [(j/graph-node next {:kind :closure :id 1 :target h})] [] [] [(j/graph-ref next 1)]))))
          (is (false? (host/private-value engine "graphInstalled")))
          (finally (j/close! next engine))))
      (finally (finish-probe! ctx e)))))

(deftest authentic-owned-boxed-wrapper-closure-import-and-partial-application
  (let [base (j/prepare-host-program *basis* [] []) source (j/source-binding base (Object.))
        nr (record "Lean.Level.beq") wr (record "Lean.Level.beq._boxed")
        native (j/declaration-header source (get nr "row") (get nr "sha256"))
        wrapper (j/declaration-header source (get wr "row") (get wr "sha256"))
        registered (j/register-headers base [native wrapper])
        ready (j/materialize-body registered wrapper (get wr "row") [native])
        ctx (j/extend-program ready (x/raw (rest (helpers)))) e (j/machine ctx)
        [closure] (j/install-graph! ctx e (j/prepared-graph ctx source (Object.)
                     [(j/graph-node ctx {:kind :closure :id 1 :target wrapper})] [] [] [(j/graph-ref ctx 1)]))]
    (try
      (is (= 1 (j/call ctx e "level-apply-two" [closure 0 0])))
      (let [partial (j/make-closure! ctx e "Lean.Level.beq._boxed" [0])]
        (is (= 1 (j/call ctx e "level-apply-one" [partial 0]))))
      (finally (finish-probe! ctx e)))))

(deftest model-forged-raw-closures-reject-at-host-admission-and-reply-boundaries
  (let [rows (concat (map #(get % "row") (eq/records)) (map #(get % "row") (records))
                     (helpers) [(host/ext "host" host/owned) (first g/common) (second g/common)])
        ctx (j/prepare-host-program *basis* (x/raw rows) [host/owned]) e (j/machine ctx)
        value (eq/forged-raw-closure ctx "Lean.Level.beq")]
    (try
      (is (g/bad? #(j/call ctx e "identity" [value]))) (is (= "idle" (j/phase ctx e)))
      (is (= 1 (c/rc ctx value)))
      (j/start! ctx e "host" [0])
      (let [request (j/host-request ctx e)]
        (is (g/bad? #(j/resume-host! ctx e request value)))
        (is (identical? request (j/host-request ctx e))) (is (= 1 (c/rc ctx value)))
        (j/resume-host! ctx e request 0) (is (= 0 (j/take-result! ctx e))))
      (finally (j/release! ctx e value) (finish-probe! ctx e)))))

(deftest malformed-Level-heads-reject-without-owner-or-counter-effects
  (doseq [descriptor [{:kind :ref :id 1 :fields [0]}
                      {:kind :array :id 1 :fields [0]}
                      {:kind :byte-array :id 1 :bytes [0]}
                      {:kind :ctor :id 1 :tag 0 :fields [0] :scalars []}
                      {:kind :ctor :id 1 :tag 6 :fields [0] :scalars (repeat 8 0)}
                      {:kind :ctor :id 1 :tag 1 :fields [0] :scalars (repeat 7 0)}
                      {:kind :ctor :id 1 :tag 2 :fields [0] :scalars (repeat 8 0)}]]
    (let [ctx (model-context) e (:engine ctx) source (j/source-binding ctx (Object.))
          [value] (j/install-graph! ctx e (j/prepared-graph ctx source (Object.) [(j/graph-node ctx descriptor)] [] [] [(j/graph-ref ctx 1)]))
          before (k/counters ctx e)]
      (try
        ;; Validate both heads before identity, even the same malformed Node.
        (is (g/bad? #(compare-level ctx value value))) (is (= before (k/counters ctx e)))
        (finally (finish-probe! ctx e)))))
  (let [ctx (model-context) e (:engine ctx)]
    (try (is (g/bad? #(compare-level ctx 1 1))) (finally (finish-probe! ctx e)))))

(deftest models-deep-shared-DAG-and-cycle-have-bounded-local-workspaces
  (let [ctx (model-context) e (:engine ctx) b (eq/model-builder ctx) level (:level b)
        make (fn [depth dag?] (loop [i depth root 0] (if (zero? i) root
                                (recur (dec i) (if dag? (level 2 [root root]) (level 1 [root]))))))
        roots ((:finish b) [(make 4096 false) (make 4096 false) (make 24 true) (make 24 true)]) before (k/counters ctx e)]
    (try (is (= 1 (compare-level ctx (nth roots 0) (nth roots 1))))
         (is (= 1 (compare-level ctx (nth roots 2) (nth roots 3))))
         (is (= before (k/counters ctx e))) (finally (finish-probe! ctx e))))
  (let [ctx (model-context) e (:engine ctx) source (j/source-binding ctx (Object.))
        [a b] (j/install-graph! ctx e (j/prepared-graph ctx source (Object.)
                  [(j/graph-node ctx {:kind :ctor :id 1 :tag 1 :fields [(j/graph-ref ctx 1)] :scalars (repeat 8 0)})
                   (j/graph-node ctx {:kind :ctor :id 2 :tag 1 :fields [(j/graph-ref ctx 2)] :scalars (repeat 8 0)})]
                  [] [] [(j/graph-ref ctx 1) (j/graph-ref ctx 2)])) before (k/counters ctx e)]
    (try (is (= 1 (compare-level ctx a a)))
         (is (re-find #"equality cycle outside bounded" (c/failure #(compare-level ctx a b))))
         (is (= before (k/counters ctx e))) (finally (finish-probe! ctx e)))))

(deftest model-name-work-and-interruption-preserve-guest-state
  (doseq [[length interrupt? pattern] [[600000 false #"equality work outside bounded"] [2048 true #"equality interrupted"]]]
    (let [ctx (model-context) e (:engine ctx) b (eq/model-builder ctx) level (:level b) nm (:name b)
          text (apply str (repeat length "x")) [a d] ((:finish b) [(level 4 [(nm text)]) (level 4 [(nm text)])])
          before (k/counters ctx e) outcome (atom nil)
          run #(reset! outcome (c/failure (fn [] (compare-level ctx a d))))]
      (try
        (if interrupt?
          (let [worker (Thread. ^Runnable (fn [] (.interrupt (Thread/currentThread)) (try (run) (finally (Thread/interrupted)))))]
            (.start worker) (.join worker 1000) (is (not (.isAlive worker))))
          (run))
        (is (re-find pattern (or @outcome ""))) (is (= before (k/counters ctx e)))
        (finally (finish-probe! ctx e))))))

(defn check! [basis] (binding [*basis* basis] (clojure.test/run-tests 'java-ir-level-equality-checks)))
