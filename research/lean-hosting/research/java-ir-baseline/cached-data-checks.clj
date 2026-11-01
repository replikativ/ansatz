(ns java-ir-cached-data-checks
  "Borrowed Expr cache words and genuine Expr/Level constructor/readback paths."
  (:require [clojure.test :refer [deftest is run-tests]] [clojure.data.json :as json]
            [java-ir-baseline :as j] [java-ir-baseline-checks :as c]
            [java-ir-extern-checks :as x] [java-ir-u64-checks :as u]
            [java-ir-host-checks :as host] [java-ir-header-checks :as header]
            [java-ir-continuation-checks :as k] [java-ir-code-checks :as code] [java-ir-generation-checks :as g]
            [lean-compatibility-corpus :as corpus]))
(def ^:dynamic *basis* nil)
(def directory "test/fixtures/java-cached-data-runtime/")
(defn originals [] (json/read-str (slurp (str directory "original-rows.json"))))
(defn record [label] (first (filter #(= label (get % "label")) (originals))))
(defn target-name [label] (get-in (record label) ["row" "name"]))
(defn layouts [] (json/read-str (slurp (str directory "layout-evidence.json"))))
(defn model-name [tag size] (str "model-" tag "-" size))
(defn model-row [tag fields size]
  (c/decl (model-name tag size) [(c/p 1 "uint64") (c/p 2 "uint64")] "object"
    (c/let-ir 3 "object" (c/ctor tag (vec (repeat fields "erased")) size)
      ["sset" {:idx 3} fields 0 {:idx 1} "uint64"
       (if (= size 16) ["sset" {:idx 3} (inc fields) 0 {:idx 2} "uint64" (c/ret 3)] (c/ret 3))])))
(defn helpers []
  (concat (filter #(contains? #{"u64-box" "u64-unbox"} (last (:name %))) (u/helpers))
    [(c/decl "identity" [(c/p 1 "object")] "object" (c/ret 1))
     (c/decl "apply-one" [(c/p 1 "object") (c/p 2 "object")] "object"
       (c/let-ir 3 "object" {:ap {:x {:idx 1} :ys [(c/v 2)]}} (c/ret 3)))
     (c/decl "read-borrow" [(assoc (c/p 1 "object") :borrow true)] "uint64"
       (c/let-ir 2 "uint64" {:fap {:c (target-name "Lean.Expr.data") :ys [(c/v 1)]}} (c/ret 2)))]
    (for [entry (layouts) :let [i (get entry "ctor") tag (get i "cidx") n (get i "size") size (get i "ssize")]
          extent (if (= size 9) [9 16] [8])]
      (model-row tag n extent))))
(defn context []
  (assoc *basis* :program (j/invoke-static (:prepare *basis*)
    [(into (mapv #(get % "row") (originals)) (x/raw (helpers)))])))
(defn raw [ctx engine expr] (j/call ctx engine "read-borrow" [expr]))
(defn owned-data [ctx engine expr]
  (j/retain! ctx engine expr)
  (u/unbox ctx engine (j/call ctx engine "Lean.Expr.data._boxed" [expr])))
(defn flag [ctx engine expr]
  (j/retain! ctx engine expr) (j/call ctx engine "Lean.Expr.hasMVar._boxed" [expr]))
(deftest exact-source-abi-layout-family-and-offset-oracle
  (let [p (json/read-str (slurp (str directory "provenance.json")))
        receipt (json/read-str (slurp (str directory "native-receipt.json")))
        abi (get-in (record "Lean.Expr.data") ["row" "ir" "extern"])]
    (is (= 46 (count (originals)))) (is (= 12 (count (layouts))))
    (is (= (get p "fixture-sha256") (corpus/sha256 (str directory "original-rows.json"))))
    (is (= (get p "layout-evidence-sha256") (corpus/sha256 (str directory "layout-evidence.json"))))
    (is (= [["object"] [true] "uint64"] [(mapv #(get % "ty") (get abi "xs")) (mapv #(get % "borrow") (get abi "xs")) (get abi "type")]))
    (is (= [0 0 16 true] (mapv #(get receipt %) ["exit" "stderr-bytes" "vectors" "storage-read-only-check"])))
    (doseq [[file digest] (get p "compiled-offset-oracle")]
      (is (= digest (corpus/sha256 (str directory file)))))
    (is (string? (j/invoke-static (.getMethod ^Class (:class *basis*) "validateExternAbi"
                                (into-array Class [java.util.Map])) [(get (record "Lean.Expr.data") "row")])))))
(deftest all-pinned-expr-layouts-read-first-word-and-preserve-binder-padding
  (let [ctx (context) engine (j/machine ctx) tail (biginteger "12379813738877118208")]
    (try
      (doseq [entry (layouts) :let [i (get entry "ctor") tag (get i "cidx") semantic (get i "ssize")]
              extent (if (= semantic 9) [9 16] [8]) word [0 u/high u/max64]]
        (let [node (j/call ctx engine (model-name tag extent) [word tail])
              before (vec (.get ^java.lang.reflect.Field (:scalars ctx) node))
              before-fields (vec (.get ^java.lang.reflect.Field (:fields ctx) node))
              counts (k/counters ctx engine)]
          (is (= word (raw ctx engine node)))
          (is (= before (vec (.get ^java.lang.reflect.Field (:scalars ctx) node))))
          (is (= before-fields (vec (.get ^java.lang.reflect.Field (:fields ctx) node))))
          (is (= counts (k/counters ctx engine))) (is (= 1 (c/rc ctx node)))
          (j/release! ctx engine node)))
      (finally (j/close! ctx engine)))))
(deftest genuine-original-constructors-propagate-cache-hash-range-and-mvar-flags
  (let [ctx (context) engine (j/machine ctx)
        bvar (j/call ctx engine "Lean.Expr.bvar._override" [1048574])
        name (j/call ctx engine "Lean.Name.str._override" [0 "cached_mvar"])
        mvar (j/call ctx engine "Lean.Expr.mvar._override" [name])
        lname (j/call ctx engine "Lean.Name.str._override" [0 "cached_level"])
        level (j/call ctx engine "Lean.Level.mvar._override" [lname])
        _ (j/retain! ctx engine level)
        sort (j/call ctx engine "Lean.Expr.sort._override" [level])
        expected (j/call ctx engine "Lean.Expr.mkData"
                         [(j/call ctx engine "mixHash" [7 1048574]) 1048575 0 0 0 0 0])]
    (try
      (is (= expected (raw ctx engine bvar) (owned-data ctx engine bvar)))
      (is (>= expected u/high)) (is (= 0 (flag ctx engine bvar)))
      (is (= 1 (flag ctx engine mvar) (flag ctx engine sort)))
      (j/retain! ctx engine level)
      (let [ldata (u/unbox ctx engine (j/call ctx engine "Lean.Level.data._override._boxed" [level]))]
        (is (.testBit (biginteger ldata) 32))
        (is (.testBit (biginteger (raw ctx engine sort)) 42)))
      (j/retain! ctx engine bvar) (j/retain! ctx engine mvar)
      (let [a (raw ctx engine bvar) b (raw ctx engine mvar)
            app (j/call ctx engine "Lean.Expr.app._override" [bvar mvar])]
        (is (= (j/call ctx engine "Lean.Expr.mkAppData" [a b]) (raw ctx engine app)))
        (is (= 1 (flag ctx engine app))) (j/release! ctx engine app))
      (let [zero (j/call ctx engine "Lean.Level.zero._override" [])
            succ (j/call ctx engine "Lean.Level.succ._override" [zero])]
        (is (= 2221 (u/unbox ctx engine (j/call ctx engine "Lean.Level.data._override._boxed" [0]))))
        (j/retain! ctx engine succ)
        (let [word (u/unbox ctx engine (j/call ctx engine "Lean.Level.data._override._boxed" [succ]))]
          (is (= 1 (.longValue (.shiftRight (biginteger word) 40)))))
        (j/release! ctx engine succ))
      (doseq [value [bvar mvar sort level]] (j/release! ctx engine value))
      (finally (j/close! ctx engine)))))
(deftest genuine-boxed-getter-application-forks-actual-expression-and-credits
  (let [ctx (context) parent (j/machine ctx)
        expr (j/call ctx parent "Lean.Expr.bvar._override" [1048574]) expected (raw ctx parent expr)
        closure (j/make-closure! ctx parent "Lean.Expr.data._boxed" [])
        {:keys [engine roots]} (j/fork! ctx parent [closure expr]) child engine [cf ce] roots]
    (try
      (doseq [[e f value] [[parent closure expr] [child cf ce]]]
        (let [result (j/call ctx e "apply-one" [f value])]
          (is (= 1 (c/rc ctx result))) (is (= expected (u/unbox ctx e result)))
          (is (true? (host/private-value f "dead"))) (is (true? (host/private-value value "dead")))))
      (finally (j/close! ctx parent) (j/close! ctx child)))))
(deftest borrowed-native-entry-and-first-class-origins-reject-before-effects
  (let [ctx (context) engine (j/machine ctx) expr (j/call ctx engine "Lean.Expr.bvar._override" [0])
        counts (k/counters ctx engine)]
    (is (g/bad? #(j/call ctx engine "Lean.Expr.data" [expr])))
    (is (g/bad? #(j/make-closure! ctx engine "Lean.Expr.data" [])))
    (is (= counts (k/counters ctx engine))) (is (= 1 (c/rc ctx expr)))
    (let [pap (c/decl "bad-pap" [] "object"
                (c/let-ir 1 "object" {:pap {:c (target-name "Lean.Expr.data") :ys []}} (c/ret 1)))]
      (is (g/bad? #(j/extend-program ctx (x/raw [pap])))))
    (j/release! ctx engine expr) (j/close! ctx engine))
  (let [base (j/prepare-host-program *basis* [] []) source (j/source-binding base (Object.))
        r (record "Lean.Expr.data") h (j/declaration-header source (get r "row") (get r "sha256"))
        ctx (j/register-headers base [h]) engine (j/machine ctx)
        graph (j/selected-owner-graph ctx source (Object.)
                [(j/graph-node ctx {:kind :closure :id 1 :rc 1 :target h :fields []})]
                [] [] [(j/graph-ref ctx 1)]) counts (k/counters ctx engine)]
    (is (g/bad? #(j/install-graph! ctx engine graph)))
    (is (= counts (k/counters ctx engine))) (j/close! ctx engine)))
(deftest malformed-layouts-and-distinct-runtime-kinds-do-not-mutate-borrowed-input
  (doseq [descriptor [{:kind :ctor :tag 12 :fields [0] :scalars (vec (repeat 8 0))}
                      {:kind :ctor :tag 0 :fields [0 0] :scalars (vec (repeat 8 0))}
                      {:kind :ctor :tag 0 :fields [0] :scalars (vec (repeat 7 0))}
                      {:kind :ctor :tag 6 :fields [0 0 0] :scalars (vec (repeat 10 0))}
                      {:kind :array :fields [0]} {:kind :ref :fields [0]}]]
    (let [ctx (context) engine (j/machine ctx) source (j/source-binding ctx (Object.))
          [value] (j/install-graph! ctx engine (j/selected-owner-graph ctx source (Object.)
                    [(j/graph-node ctx (assoc descriptor :id 1 :rc 1))] [] [] [(j/graph-ref ctx 1)]))
          counts (k/counters ctx engine)]
      (is (g/bad? #(raw ctx engine value))) (is (= counts (k/counters ctx engine)))
      (is (= 1 (c/rc ctx value))) (is (false? (host/private-value value "dead")))
      ;; Deliberate guest failures retain borrowed caller-owned inputs; failed
      ;; frame cleanup remains the existing profile limit. No automatic unwind.
      )))
(deftest original-wrapper-code-host-and-fork-transport-preserve-borrowed-cache-word
  (let [spec (host/spec "research_expr_word" ["uint64"] [false] "uint64")
        base (j/prepare-host-program *basis*
               (x/raw [(model-row 0 1 8) (host/ext "host-word" spec)]) [spec])
        source (j/source-binding base (Object.)) native-row (record "Lean.Expr.data")
        wrapper-row (record "Lean.Expr.data._boxed")
        native (j/declaration-header source (get native-row "row") (get native-row "sha256"))
        wrapper (j/declaration-header source (get wrapper-row "row") (get wrapper-row "sha256"))
        ctx (j/register-headers base [native wrapper])
        caller (c/decl "caller" [(c/p 1 "object")] "uint64"
                 (c/let-ir 2 "object" {:fap {:c (get-in wrapper-row ["row" "name"]) :ys [(c/v 1)]}}
                   (c/let-ir 3 "uint64" {:unbox {:x {:idx 2}}}
                     ["dec" {:idx 2} 1 false false
                      (c/let-ir 4 "uint64" (c/fap "host-word" [(c/v 3)]) (c/ret 4))])))
        ctx (j/extend-program ctx (x/raw [caller])) parent (j/machine ctx)
        expr (j/call ctx parent (model-name 0 8) [u/max64 0])
        ready (j/materialize-body ctx wrapper (get wrapper-row "row") [native])]
    (j/start! ctx parent "caller" [expr])
    (let [request (code/request! ctx parent) child (:engine (j/fork! ctx parent []))]
      (try
        (is (identical? wrapper (.header request)))
        (is (= (get wrapper-row "sha256") (.originalSha256 wrapper)))
        (doseq [e [parent child]]
          (j/resume-code! ready e (j/code-request ready e))
          (let [request (host/request! ready e)]
            (is (= [u/max64] (host/args request)))
            (is (g/bad? #(j/resume-host! ready e request -1)))
            (is (identical? request (j/host-request ready e)))
            (j/resume-host! ready e request u/high)
            (is (= u/high (code/finish! ready e)))))
        (is (true? (host/private-value expr "dead")))
        (finally (j/close! ready parent) (j/close! ready child))))))

(defn check! [basis] (binding [*basis* basis] (run-tests 'java-ir-cached-data-checks)))
