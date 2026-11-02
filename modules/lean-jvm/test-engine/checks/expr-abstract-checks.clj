(ns java-ir-expr-abstract-checks
 "Original borrowed abstraction: semantic Names, offset cache and owner/fork boundaries."
 (:require [clojure.test :refer [deftest is run-tests]] [clojure.data.json :as json]
   [java-ir-baseline :as j] [java-ir-baseline-checks :as c] [engine-support.expr :as expr]
   [java-ir-expr-find-checks :as find] [java-ir-array-checks :as arr] [java-ir-host-checks :as h]
   [java-ir-sync-task-checks :as sync] [java-ir-generation-checks :as g]
   [java-ir-logical-sharing-checks :as sharing] [java-ir-continuation-checks :as k] [lean-compatibility-corpus :as corpus]))
(def ^:dynamic *basis* nil)
(def directory "test/fixtures/java-expr-abstract-runtime/")
(defn records [] (json/read-str (slurp (str directory "original-rows.json"))))
(defn raw-name [] (get-in (first (records)) ["row" "name"]))
(defn helpers []
 [(c/decl "abstract-keep" (mapv #(c/p % "object") [1 2 3]) "object"
    (c/let-ir 4 "object" {:fap {:c (raw-name) :ys [(c/v 1) (c/v 2) (c/v 3)]}}
     ["dec" {:idx 3} 1 false false ["dec" {:idx 2} 1 false false
      (c/let-ir 5 "object" (c/ctor 0 [(c/v 1) (c/v 4)] 0) (c/ret 5))]]))
  (c/decl "abstract-apply" (mapv #(c/p % "object") [1 2 3 4]) "object"
   (c/let-ir 5 "object" {:ap {:x {:idx 1} :ys [(c/v 2) (c/v 3) (c/v 4)]}} (c/ret 5)))])
(defn context
 ([] (context {}))
 ([options]
  (binding [expr/*basis* *basis*]
   (expr/context (-> options
     (update :rows #(concat (helpers) %))
     (update :extra-originals #(concat (take 4 (records)) (arr/originals) %)))))))
(defn machine [{:keys [ctx headers]}]
 (let [e (j/machine ctx)]
  (j/configure-expr-transforms! ctx e (j/expr-transform-policy ctx (mapv headers expr/roles))) e))
(defn call [ctx e label xs] (j/start! ctx e label xs) (sync/finish! ctx e))
(defn name! [ctx e s] (call ctx e "Lean.Name.str._override" [0 s]))
(defn fvar! [ctx e s] (call ctx e "Lean.Expr.fvar._override" [(name! ctx e s)]))
(defn mvar! [ctx e s] (call ctx e "Lean.Expr.mvar._override" [(name! ctx e s)]))
(defn array! [ctx e xs]
 (reduce #(call ctx e "Array.push._boxed" [0 %1 %2])
   (call ctx e "Array.mkEmpty._boxed" [0 (long (count xs))]) xs))
(defn range! [ctx e value n values] (call ctx e "Lean.Expr.abstractRange._boxed" [value n values]))
(defn whole! [ctx e value values] (call ctx e "Lean.Expr.abstract._boxed" [value values]))
(defn index [ctx value] (first (expr/fields ctx value)))
(defn tag [ctx value] (.getInt ^java.lang.reflect.Field (:tag ctx) value))
(defn dead? [v] (true? (h/private-value v "dead")))
(defn state [e]
 (loop [a (sync/action e)]
  (when a (or (h/private-value a "exprMachinery") (recur (h/private-value a "parent"))))))
(defn job [e] (some-> (state e) (h/private-value "jobs") ^java.util.Deque (.peekLast)))
(defn until! [ctx e condition]
 (loop [left 100000]
  (assert (pos? left) "Abstraction checkpoint outside bounded test dispatch count")
  (when-not (condition)
   (assert (= "running" (j/phase ctx e)) "Unexpected abstraction control boundary")
   (j/advance! ctx e 1) (recur (dec left)))))

(deftest exact-authenticated-raw-and-boxed-abis
 (let [rs (records) p (json/read-str (slurp (str directory "provenance.json")))]
  (is (= 13 (count rs)))
  (is (= (get p "original-rows-sha256") (corpus/sha256 (str directory "original-rows.json"))))
  (is (= [] (get p "initialized-dependencies")))
  (is (= [55 123812] (mapv #(get p %) ["static-closure-rows" "static-closure-raw-bytes"])))
  (doseq [[i params borrow] [[0 ["object" "tobject" "object"] [true true true]]
                            [1 ["object" "tobject" "object"] [false false false]]
                            [2 ["object" "object"] [true true]] [3 ["object" "object"] [false false]]]]
   (let [d (or (get-in (rs i) ["row" "ir" "extern"]) (get-in (rs i) ["row" "ir" "fdecl"]))]
    (is (= [params borrow "object"] [(mapv #(get % "ty") (get d "xs"))
                                    (mapv #(get % "borrow") (get d "xs")) (get d "type")]))))))

(deftest semantic-distinct-name-nodes-and-variable-domains
 (doseq [kind [:fvar :mvar]]
  (let [{:keys [ctx] :as lab} (context) e (machine lab) make (if (= kind :fvar) fvar! mvar!)
        x (make ctx e "x") other (make ctx e "x") values (array! ctx e [other])
        output (range! ctx e x 1 values)]
   (is (not (identical? x other))) (is (= 0 (tag ctx output) (index ctx output)))
   (is (every? dead? [x other values])) (is (= 1 (c/rc ctx output)))
   (sync/release! ctx e output) (sync/close! ctx e)))
 (doseq [[make other] [[fvar! mvar!] [mvar! fvar!]]]
  (let [{:keys [ctx] :as lab} (context) e (machine lab) x (make ctx e "same")
        output (range! ctx e x 1 (array! ctx e [(other ctx e "same")]))]
   (is (identical? x output)) (is (= 1 (c/rc ctx output)))
   (sync/release! ctx e output) (sync/close! ctx e))))

(deftest reverse-prefix-duplicates-clamp-and-nonvariable-entries
 (doseq [[n expected] [[0 nil] [1 0] [2 1] [3 0] [Long/MAX_VALUE 0]]]
  (let [{:keys [ctx] :as lab} (context) e (machine lab) x (fvar! ctx e "x")
        values (array! ctx e [(fvar! ctx e "x") (expr/sort! ctx e) (fvar! ctx e "x")])
        output (range! ctx e x n values)]
   (if (nil? expected) (is (identical? x output)) (do (is (= 0 (tag ctx output))) (is (= expected (index ctx output)))))
   (sync/release! ctx e output) (sync/close! ctx e)))
 (let [{:keys [ctx] :as lab} (context) e (machine lab) x (fvar! ctx e "x")
       output (whole! ctx e x (array! ctx e [(fvar! ctx e "x") (fvar! ctx e "y")]))]
  (is (= 1 (index ctx output))) (sync/release! ctx e output) (sync/close! ctx e)))

(deftest heap-nat-range-uses-full-live-array-including-small-heap-model
 ;; Small BigInteger is a carrier-model case, not an ordinary Lean Nat producer.
 (doseq [n [(java.math.BigInteger/valueOf 1) (.shiftLeft java.math.BigInteger/ONE 100)]]
  (let [{:keys [ctx] :as lab} (context) e (machine lab)
        output (range! ctx e (fvar! ctx e "x") n (array! ctx e [(fvar! ctx e "x") (fvar! ctx e "y")]))]
   (is (= 1 (index ctx output))) (sync/release! ctx e output) (sync/close! ctx e))))

(deftest existing-bound-variables-and-binder-offsets-are-preserved
 (let [{:keys [ctx] :as lab} (context) e (machine lab)
       body (expr/app! ctx e (fvar! ctx e "x") (expr/bvar! ctx e 0))
       root (expr/lam! ctx e body) values (array! ctx e [(fvar! ctx e "x")])
       output (range! ctx e root 1 values)
       out-body (nth (expr/fields ctx output) 2) [f a] (expr/fields ctx out-body)]
  (is (= 6 (tag ctx output))) (is (= 1 (index ctx f))) (is (= 0 (index ctx a)))
  (is (dead? root)) (sync/release! ctx e output) (sync/close! ctx e)))

(deftest borrowed-direct-fap-and-authentic-boxed-first-class-entry
 (let [{:keys [ctx] :as lab} (context) e (machine lab) x (fvar! ctx e "x")
       output (call ctx e "abstract-keep" [x 1 (array! ctx e [(fvar! ctx e "x")])])
       [original abstracted] (expr/fields ctx output)]
  (is (identical? x original)) (is (not (dead? x))) (is (= 0 (index ctx abstracted)))
  (is (= 1 (c/rc ctx original) (c/rc ctx abstracted)))
  (sync/release! ctx e output) (sync/close! ctx e))
 (let [{:keys [ctx] :as lab} (context) e (machine lab)
       wrapped (j/make-closure! ctx e "Lean.Expr.abstractRange._boxed" [])
       output (call ctx e "abstract-apply" [wrapped (fvar! ctx e "x") 1 (array! ctx e [(fvar! ctx e "x")])])]
  (is (dead? wrapped)) (is (= 0 (index ctx output)))
  (sync/release! ctx e output) (sync/close! ctx e)))

(deftest zero-prefix-retains-source-offset-cache-for-fvar-and-universe-mvar-sort
 (doseq [kind [:fvar :level-mvar]]
  (let [{:keys [ctx] :as lab} (context) e (machine lab)
        root (if (= kind :fvar) (fvar! ctx e "x")
               (expr/setup! ctx e 1 [(call ctx e "Lean.Level.mvar._override" [(name! ctx e "u")])]))
        values (array! ctx e [])]
   (j/retain! ctx e root)
   (j/start! ctx e "Lean.Expr.abstractRange._boxed" [root 0 values])
   (until! ctx e #(some-> (state e) (h/private-value "liveCacheEntries") pos?))
   (is (= 1 (h/private-value (state e) "liveCacheEntries"))) (is (= 4 (c/rc ctx root)))
   (let [output (sync/finish! ctx e)]
    (is (identical? root output)) (is (= 2 (c/rc ctx root))) (is (dead? values))
    (sync/release! ctx e output) (sync/release! ctx e root) (sync/close! ctx e)))))

(defn check! [basis] (binding [*basis* basis] (run-tests 'java-ir-expr-abstract-checks)))


(deftest default-policy-and-borrowed-root-pap-import-fences
 (let [{:keys [ctx] :as lab} (context) e (j/machine ctx) root (expr/bvar! ctx e 0)
       values (array! ctx e []) before (k/counters ctx e)]
  (is (re-find #"original constructor policy" (c/failure #(range! ctx e root 0 values))))
  (is (= before (k/counters ctx e))) (is (= "failed" (j/phase ctx e)))
  (is (= 1 (c/rc ctx root) (c/rc ctx values))))
 (doseq [label ["Lean.Expr.abstractRange" "Lean.Expr.abstract"]]
  (let [{:keys [ctx source headers] :as lab} (context) e (machine lab)
        root (expr/bvar! ctx e 0) values (array! ctx e []) before (k/counters ctx e)
        args (if (= label "Lean.Expr.abstractRange") [root 0 values] [root values])]
   (is (g/bad? #(j/start! ctx e label args))) (is (= "idle" (j/phase ctx e)))
   (is (= before (k/counters ctx e))) (is (g/bad? #(j/make-closure! ctx e label [])))
   (is (g/bad? #(context {:rows [(c/decl "invalid-abstract-pap" [] "object"
      (c/let-ir 1 "object" {:pap {:c (get-in (first (filter (fn [r] (= label (get r "label"))) (records))) ["row" "name"]) :ys []}} (c/ret 1)))]})))
   (is (g/bad? #(j/install-graph! ctx e (j/prepared-graph ctx source (Object.)
     [(j/graph-node ctx {:kind :closure :id 1 :target (headers label)})] [] [] [(j/graph-ref ctx 1)]))))
   (is (false? (h/private-value e "graphInstalled")))
   (sync/release! ctx e values) (sync/release! ctx e root) (sync/close! ctx e))))

(deftest negative-range-rejects-before-native-allocation-and-spare-slots-are-ignored
 (doseq [n [-1 (java.math.BigInteger/valueOf -1)]]
  (let [{:keys [ctx] :as lab} (context) e (machine lab) root (fvar! ctx e "x") values (array! ctx e [])
        before (k/counters ctx e)]
   (is (re-find #"nonnegative Nat" (c/failure #(range! ctx e root n values))))
   (is (= before (k/counters ctx e))) (is (= 1 (c/rc ctx root) (c/rc ctx values)))))
 (let [{:keys [ctx] :as lab} (context) e (machine lab)
       values (call ctx e "Array.push._boxed" [0 (call ctx e "Array.mkEmpty._boxed" [0 8]) (fvar! ctx e "x")])
       _ (is (= 8 (alength ^objects (find/fields ctx values))))
       output (range! ctx e (fvar! ctx e "x") Long/MAX_VALUE values)]
  (is (= 0 (index ctx output))) (sync/release! ctx e output) (sync/close! ctx e)))

(deftest same-node-at-different-binder-offsets-has-distinct-cache-entries
 (let [{:keys [ctx] :as lab} (context) e (machine lab) x (fvar! ctx e "x")
       body (expr/lam! ctx e (expr/retain ctx e x)) root (expr/app! ctx e x body)
       output (range! ctx e root 1 (array! ctx e [(fvar! ctx e "x")]))
       [f lam] (expr/fields ctx output) b (nth (expr/fields ctx lam) 2)]
  (is (= 0 (index ctx f))) (is (= 1 (index ctx b))) (is (not (identical? f b)))
  (is (dead? x)) (sync/release! ctx e output) (sync/close! ctx e)))

(deftest same-node-at-same-offset-reuses-result-identity-and-mt-rc1-does-not-cache
 (let [{:keys [ctx] :as lab} (context) e (machine lab) x (fvar! ctx e "x")
       root (expr/app! ctx e (expr/retain ctx e x) x)
       output (range! ctx e root 1 (array! ctx e [(fvar! ctx e "x")]))
       [f a] (expr/fields ctx output)]
  (is (identical? f a)) (is (= 2 (c/rc ctx f)))
  (sync/release! ctx e output) (sync/close! ctx e))
 (let [{:keys [ctx] :as lab} (context) e (machine lab) root (fvar! ctx e "x")
       values (array! ctx e [])]
  (sharing/mark! ctx e root)
  (j/start! ctx e "Lean.Expr.abstractRange._boxed" [root 0 values])
  (until! ctx e #(let [f (some-> (job e) (h/private-value "frames") ^java.util.Deque (.peekLast))]
                  (and f (= 7 (h/private-value f "stage")))))
  (let [f (.peekLast ^java.util.Deque (h/private-value (job e) "frames"))]
   (is (false? (h/private-value f "shared"))) (is (zero? (h/private-value (state e) "liveCacheEntries"))))
  (let [output (sync/finish! ctx e)]
   (is (identical? root output)) (is (sharing/mt? ctx output)) (is (= 1 (c/rc ctx output)))
   (sync/release! ctx e output) (sync/close! ctx e))))

(deftest all-binders-let-metadata-and-projection-preserve-payloads-and-flags
 (doseq [role [4 5 6 7 8]]
  (let [{:keys [ctx] :as lab} (context) e (machine lab) n (name! ctx e "binder")
        root (case role
          (4 5) (expr/setup! ctx e role [n (expr/sort! ctx e) (fvar! ctx e "x") 3])
          6 (expr/setup! ctx e role [n (expr/sort! ctx e) (fvar! ctx e "x") (fvar! ctx e "x") 1])
          7 (do (sync/release! ctx e n) (expr/setup! ctx e role [0 (fvar! ctx e "x")]))
          8 (expr/setup! ctx e role [n 2 (fvar! ctx e "x")]))
        output (range! ctx e root 1 (array! ctx e [(fvar! ctx e "x")])) fs (expr/fields ctx output)]
   (is (dead? root))
   (case role
    (4 5) (do (is (identical? n (fs 0))) (is (= 1 (index ctx (fs 2))))
              (is (= 3 (bit-and 255 (aget ^bytes (.get ^java.lang.reflect.Field (:scalars ctx) output) 8)))))
    6 (do (is (identical? n (fs 0))) (is (= 0 (index ctx (fs 2)))) (is (= 1 (index ctx (fs 3))))
          (is (= 1 (bit-and 255 (aget ^bytes (.get ^java.lang.reflect.Field (:scalars ctx) output) 8)))))
    7 (do (is (= 0 (fs 0))) (is (= 0 (index ctx (fs 1)))))
    8 (do (is (identical? n (fs 0))) (is (= 2 (fs 1))) (is (= 0 (index ctx (fs 2))))))
   (sync/release! ctx e output) (sync/close! ctx e))))

(deftest mid-prefix-scan-fork-remaps-borrowed-input-array-and-cursors
 (let [{:keys [ctx] :as lab} (context) parent (machine lab) root (fvar! ctx parent "x")
       values (array! ctx parent [(fvar! ctx parent "x") (fvar! ctx parent "y") (fvar! ctx parent "z")])]
  (j/start! ctx parent "Lean.Expr.abstractRange._boxed" [root 3 values])
  (until! ctx parent #(let [f (some-> (job parent) (h/private-value "frames") ^java.util.Deque (.peekLast))]
    (and f (= 7 (h/private-value f "stage")) (= 2 (h/private-value f "abstractScan")))))
  (let [{:keys [engine]} (j/fork! ctx parent []) child engine
        cr (h/private-value (job child) "input") ca (h/private-value (job child) "abstractArray")]
   (is (not (identical? root cr))) (is (not (identical? values ca)))
   (let [output (sync/finish! ctx child)]
    (is (= 2 (index ctx output))) (is (dead? cr)) (is (dead? ca))
    (is (not (dead? root))) (is (not (dead? values)))
    (sync/release! ctx child output) (sync/close! ctx child))
   (let [output (sync/finish! ctx parent)]
    (is (= 2 (index ctx output))) (is (dead? root)) (is (dead? values))
    (sync/release! ctx parent output) (sync/close! ctx parent)))))

(deftest original-bvar-and-rebuilding-constructor-code-requests-fork-correctly
 (doseq [role [0 3]]
  (let [label (expr/roles role) {:keys [ctx] :as lab} (context {:defer #{label}}) parent (machine lab)
        root (if (= role 0) (fvar! ctx parent "x")
                (expr/app! ctx parent (fvar! ctx parent "x") (fvar! ctx parent "y")))
        values (array! ctx parent [(fvar! ctx parent "x") (fvar! ctx parent "y")])]
   (j/start! ctx parent "Lean.Expr.abstractRange._boxed" [root 2 values])
   (loop [left 10000]
    (assert (pos? left))
    (when (= "running" (j/phase ctx parent)) (j/advance! ctx parent 1) (recur (dec left))))
   (is (= "code-call" (j/phase ctx parent)))
   (let [request (j/code-request ctx parent) {:keys [engine]} (j/fork! ctx parent []) child engine
         ready (expr/materialize lab label)]
    (is (= (get-in lab [:headers label]) (j/request-value request "header")))
    (doseq [e [parent child]]
     (j/install-program! ready e) (j/resume-code! ready e (j/code-request ready e))
     (let [output (sync/finish! ready e)]
      (if (= role 0) (is (= 1 (index ready output)))
       (is (= [1 0] (mapv #(index ready %) (expr/fields ready output)))))
      (sync/release! ready e output) (sync/close! ready e)))))))

(deftest aggregate-budget-failure-keeps-cache-result-and-borrowed-call-inputs
 (let [{:keys [ctx] :as lab} (context) e (machine lab) root (fvar! ctx e "x") values (array! ctx e [])]
  (j/retain! ctx e root)
  (j/start! ctx e "Lean.Expr.abstractRange._boxed" [root 0 values])
  (until! ctx e #(some-> (state e) (h/private-value "liveCacheEntries") pos?))
  (let [s (state e) budget (h/private-value s "budget") before (c/rc ctx root)]
   (sync/private-set! budget "work" (long 1000000))
   (is (re-find #"work outside bounded" (c/failure #(j/advance! ctx e 1))))
   (is (= before (c/rc ctx root))) (is (= 4 before)) (is (= 1 (c/rc ctx values)))
   (is (= "failed" (j/phase ctx e))) (is (g/bad? #(j/fork! ctx e []))))))


(deftest constructor-host-suspension-and-fork-retain-the-exact-owner-packets
 ;; MODEL observational Host prefix in an otherwise original App constructor.
 (let [label (expr/roles 3)
       original (get-in (first (filter #(= label (get % "label")) (records))) ["row" "ir" "fdecl" "body"])
       spec (h/spec "abstract_constructor_event" ["object" "object"] [true true] "object")
       body (c/let-ir 100 "object" (c/fap "abstract-constructor-event" [(c/v 1) (c/v 2)]) original)
       {:keys [ctx] :as lab} (context {:replacements {label body}
         :rows [(h/ext "abstract-constructor-event" spec)] :host-specs [spec]})
       parent (machine lab)
       input (expr/app! ctx parent (fvar! ctx parent "x") (fvar! ctx parent "y"))
       values (array! ctx parent [(fvar! ctx parent "x") (fvar! ctx parent "y")])]
  (j/start! ctx parent "Lean.Expr.abstractRange._boxed" [input 2 values])
  (let [request (h/request! ctx parent) {:keys [engine]} (j/fork! ctx parent []) child engine]
   (is (= "abstract_constructor_event" (j/request-value request "symbol")))
   (is (= [2 2] (mapv #(c/rc ctx %) (h/args request))))
   (is (g/bad? #(j/resume-host! ctx child request 0)))
   (doseq [e [parent child]]
    (let [packet (h/private-value (state e) "call")]
     (is (true? (h/private-value packet "entered")))
     (is (= [false false] (vec (h/private-value packet "owned")))))
    (j/resume-host! ctx e (j/host-request ctx e) 0)
    (let [output (sync/finish! ctx e)]
     (is (= [1 0] (mapv #(index ctx %) (expr/fields ctx output))))
     (sync/release! ctx e output) (sync/close! ctx e))))))

(deftest malformed-constructor-result-keeps-receiver-owned-at-failure
 ;; MODEL bad original-role body: ABI/source metadata alone does not bless output.
 (let [label (expr/roles 0) body (c/let-ir 2 "object" (c/ctor 3 [(c/v 1)] 8) (c/ret 2))
       {:keys [ctx] :as lab} (context {:replacements {label body}}) e (machine lab)
       root (fvar! ctx e "x") values (array! ctx e [(fvar! ctx e "x")])]
  (j/start! ctx e "Lean.Expr.abstractRange._boxed" [root 1 values])
  (is (re-find #"unexpected head" (c/failure #(sync/finish! ctx e))))
  (let [action (sync/action e) receiver (aget ^objects (h/private-value e "objects") (h/private-value action "slot"))
        packet (h/private-value (state e) "call")]
   (is (= 3 (tag ctx receiver))) (is (= 1 (c/rc ctx receiver)))
   (is (= 1 (c/rc ctx root) (c/rc ctx values)))
   (is (true? (h/private-value packet "entered")))
   (is (= [false] (vec (h/private-value packet "owned")))))
  (is (= "failed" (j/phase ctx e))) (is (g/bad? #(j/fork! ctx e [])))))

(deftest cache-drain-fork-preserves-distinct-input-result-and-outside-occurrences
 (let [{:keys [ctx] :as lab} (context) parent (machine lab) root (fvar! ctx parent "x")
       values (array! ctx parent [])]
  (j/retain! ctx parent root)
  (j/start! ctx parent "Lean.Expr.abstractRange._boxed" [root 0 values])
  (until! ctx parent #(some-> (state parent) (h/private-value "liveCacheEntries") pos?))
  (let [{:keys [engine roots]} (j/fork! ctx parent [root]) child engine cr (first roots)]
   (is (= 4 (c/rc ctx root) (c/rc ctx cr))) (is (not (identical? root cr)))
   (doseq [[e outside] [[parent root] [child cr]]]
    (let [output (sync/finish! ctx e)]
     (is (identical? outside output)) (is (= 2 (c/rc ctx output)))
     (is (nil? (state e)))
     (sync/release! ctx e output) (is (= 1 (c/rc ctx outside)))
     (sync/release! ctx e outside) (is (dead? outside))
     (sync/close! ctx e))))))

(deftest malformed-structural-cycle-rejects-with-owned-call-state-preserved
 ;; MODEL forged cyclic Expr storage with deliberate edge-owner transfer; no unwind claim.
 (let [{:keys [ctx] :as lab} (context) e (machine lab)
       root (expr/app! ctx e (fvar! ctx e "x") (fvar! ctx e "y")) values (array! ctx e [])]
  (let [fields ^objects (.get ^java.lang.reflect.Field (:fields ctx) root) displaced (aget fields 0)]
   (aset fields 0 root)
   (.setInt ^java.lang.reflect.Field (:rc ctx) root 2)
   (sync/release! ctx e displaced))
  (j/start! ctx e "Lean.Expr.abstractRange._boxed" [root 0 values])
  (is (re-find #"structural cycle outside" (c/failure #(sync/finish! ctx e))))
  (is (= "failed" (j/phase ctx e))) (is (not (dead? root)))
  (is (= 2 (c/rc ctx root))) (is (= 1 (c/rc ctx values)))
  (is (g/bad? #(j/fork! ctx e [])))))
