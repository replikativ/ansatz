(ns java-ir-expr-equality-checks
  "Source-backed Expr comparators; structural/cache adversaries are labeled models."
  (:require [clojure.test :refer [deftest is]] [clojure.data.json :as json]
            [java-ir-baseline :as j] [java-ir-baseline-checks :as c]
            [java-ir-extern-checks :as x] [java-ir-host-checks :as host]
            [java-ir-generation-checks :as g] [java-ir-header-checks :as header]
            [java-ir-continuation-checks :as k] [java-ir-u64-checks :as u]
            [java-ir-code-checks :as code] [lean-compatibility-corpus :as corpus]))
(def ^:dynamic *basis* nil)
(def directory "test/fixtures/java-expr-equality-runtime/")
(defn records [] (json/read-str (slurp (str directory "original-rows.json"))))
(defn record [label] (first (filter #(= label (get % "label")) (records))))
(defn named [label] (get-in (record label) ["row" "name"]))
(defn helper [label target]
  (c/decl label [(assoc (c/p 1 "object") :borrow true) (assoc (c/p 2 "object") :borrow true)] "uint8"
    (c/let-ir 3 "uint8" {:fap {:c (named target) :ys [(c/v 1) (c/v 2)]}} (c/ret 3))))
(defn helpers [] (vec (concat (filter #(contains? #{"u64-box" "u64-unbox"} (last (:name %))) (u/helpers)) [(helper "model-eqv-borrow" "Lean.Expr.eqv") (helper "model-equal-borrow" "Lean.Expr.equal")
  (c/decl "apply-two" [(c/p 1 "object") (c/p 2 "object") (c/p 3 "object")] "object"
    (c/let-ir 4 "object" {:ap {:x {:idx 1} :ys [(c/v 2) (c/v 3)]}} (c/ret 4)))])))
(defn context
  ([] (context []))
  ([extra] (assoc *basis* :program (j/invoke-static (:prepare *basis*)
    [(x/raw (concat (map #(get % "row") (records)) (helpers) extra))]))))
(defn bytes64 [n] (mapv #(bit-and 255 (.intValue (.shiftRight (biginteger n) (* 8 %)))) (range 8)))
(defn model-builder [ctx]
  (let [nodes (atom [])
        add (fn [tag fields size word flag]
              (let [id (inc (count @nodes))
                    bytes (vec (concat (take size (concat (bytes64 word) (repeat 0)))) )
                    bytes (if (> size 8) (assoc bytes 8 flag) bytes)]
                (swap! nodes conj (j/graph-node ctx {:id id :kind :ctor :tag tag :fields (vec fields) :scalars bytes}))
                (j/graph-ref ctx id)))
        array (fn [fields] (let [id (inc (count @nodes))]
                            (swap! nodes conj (j/graph-node ctx {:id id :kind :array :fields (vec fields)}))
                            (j/graph-ref ctx id)))]
    {:add add :array array
     :name (fn [leaf] (add 1 [0 leaf] 8 0 0))
     :expr (fn [tag fields] (add tag fields (if (<= 6 tag 8) 9 8) 0 0))
     :level (fn [tag fields] (add tag fields 8 0 0))
     :list (fn [xs] (reduce (fn [tail head] (add 1 [head tail] 0 0 0)) 0 (reverse xs)))
     :finish (fn [roots] (j/install-graph! ctx (get ctx :engine)
                  (j/selected-owner-graph ctx (j/source-binding ctx (Object.)) (Object.) @nodes [] [] (vec roots))))}))
(defn finish [b ctx engine roots] ((:finish b) roots))
(defn model-context [] (let [ctx (context)] (assoc ctx :engine (j/machine ctx))))
(defn compare-pair [ctx a b]
  [(j/call ctx (:engine ctx) "model-eqv-borrow" [a b])
   (j/call ctx (:engine ctx) "model-equal-borrow" [a b])])
(defn own-compare [ctx engine label a b]
  (j/retain! ctx engine a) (j/retain! ctx engine b)
  (j/call ctx engine (str "Lean.Expr." label "._boxed") [a b]))
(deftest authenticated-family-layouts-and-native-reference
  (let [p (json/read-str (slurp (str directory "provenance.json")))]
    (is (= 74 (count (records))))
    (is (= [] (get p "initialized-dependencies")))
    (doseq [[file sha] (get p "files")] (is (= sha (corpus/sha256 (str directory file)))))
    (doseq [label ["Lean.Expr.eqv" "Lean.Expr.equal"]
            :let [d (get-in (record label) ["row" "ir" "extern"])]]
      (is (= [["object" "object"] [true true] "uint8"]
             [(mapv #(get % "ty") (get d "xs")) (mapv #(get % "borrow") (get d "xs")) (get d "type")])))))
(deftest genuine-original-constructors-binder-policy-and-owned-boxed-ap
  (let [ctx (context) engine (j/machine ctx)
        bvar #(j/call ctx engine "Lean.Expr.bvar._override" [%])
        sort #(j/call ctx engine "Lean.Expr.sort._override" [0])
        nm #(j/call ctx engine "Lean.Name.str._override" [0 %])
        lam #(j/call ctx engine "Lean.Expr.lam._override" [(nm %1) (sort) (bvar 0) %2])
        a (lam "x" 0) b (lam "y" 0) d (lam "x" 1)]
    (try
      (is (= 1 (own-compare ctx engine "eqv" a b))) (is (= 0 (own-compare ctx engine "equal" a b)))
      (is (= 1 (own-compare ctx engine "eqv" a d))) (is (= 0 (own-compare ctx engine "equal" a d)))
      (doseq [label ["eqv" "equal"]]
        (let [closure (j/make-closure! ctx engine (str "Lean.Expr." label "._boxed") [])]
          (j/retain! ctx engine a) (j/retain! ctx engine b)
          (is (= (if (= label "eqv") 1 0) (j/call ctx engine "apply-two" [closure a b])))))
      (is (= 1 (c/rc ctx a) (c/rc ctx b) (c/rc ctx d)))
      (finally (doseq [v [a b d]] (j/release! ctx engine v)) (j/close! ctx engine)))))
(deftest models-cover-every-expr-tag-and-structural-level-case
  (let [ctx (model-context) e (:engine ctx) b (model-builder ctx) add (:add b) expr (:expr b) level (:level b)
        name (:name b) lst (:list b) n (name "n") other (name "other")
        z (expr 0 [0]) z2 (expr 0 [(biginteger 0)]) one (expr 0 [1])
        lu (level 4 [n]) lv (level 4 [other]) lm (level 5 [n])
        succ (level 1 [0]) maxuv (level 2 [lu lv]) maxvu (level 2 [lv lu]) imax (level 3 [lu lv])
        pair (fn [a c expected] [a c expected])
        cases [(pair z z2 [1 1]) (pair z one [0 0])
               (pair (expr 1 [n]) (expr 1 [other]) [0 0]) (pair (expr 2 [n]) (expr 2 [n]) [1 1])
               (pair (expr 1 [n]) (expr 2 [n]) [0 0])
               (pair (expr 3 [lu]) (expr 3 [lv]) [0 0]) (pair (expr 3 [lu]) (expr 3 [lm]) [0 0])
               (pair (expr 3 [maxuv]) (expr 3 [maxvu]) [0 0]) (pair (expr 3 [imax]) (expr 3 [maxuv]) [0 0])
               (pair (expr 3 [succ]) (expr 3 [0]) [0 0])
               (pair (expr 4 [n (lst [lu lv])]) (expr 4 [n (lst [lu lv])]) [1 1])
               (pair (expr 4 [n (lst [lu lv])]) (expr 4 [n (lst [lv lu])]) [0 0])
               (pair (expr 5 [z one]) (expr 5 [z z2]) [0 0])
               (pair (expr 6 [n z one]) (expr 6 [other z one]) [1 0])
               (pair (expr 7 [n z one]) (add 7 [n z one] 16 0 3) [1 0])
               (pair (expr 8 [n z z one]) (add 8 [n z z one] 9 0 1) [0 0])
               (pair (expr 8 [n z z one]) (expr 8 [other z z one]) [1 0])
               (pair (expr 9 [(add 0 [(biginteger "18446744073709551616")] 0 0 0)])
                     (expr 9 [(add 0 [(biginteger "18446744073709551616")] 0 0 0)]) [1 1])
               (pair (expr 9 [(add 1 ["λ"] 0 0 0)]) (expr 9 [(add 1 ["μ"] 0 0 0)]) [0 0])
               (pair (expr 10 [0 z]) (expr 10 [0 z2]) [1 1])
               (pair (expr 11 [n 2 z]) (expr 11 [n 3 z2]) [0 0])]
        roots ((:finish b) (vec (mapcat #(take 2 %) cases)))]
    (try
      (doseq [[i [_ _ expected]] (map-indexed vector cases)] (is (= expected (compare-pair ctx (nth roots (* 2 i)) (nth roots (inc (* 2 i)))))))
      (finally (j/close! ctx e)))))
(deftest models-ordered-metadata-all-six-datavalue-kinds-and-padding
  (let [ctx (model-context) e (:engine ctx) b (model-builder ctx) add (:add b) expr (:expr b) name (:name b) lst (:list b)
        n (name "k") m (name "m") z (expr 0 [0])
        dv (fn [tag value] (if (= tag 1) (add tag [] 1 value 0) (add tag [value] 0 0 0)))
        md (fn [entries] (expr 10 [(lst (map #(add 0 % 0 0 0) entries)) z]))
        cases (concat
          (for [[tag a c expected] [[0 "λ" "λ" [1 1]] [1 0 1 [0 0]] [2 n n [1 1]]
                                   [3 7 (biginteger 7) [1 1]] [4 (j/graph-int ctx -9) (j/graph-int ctx -9) [1 1]]
                                   [5 0 0 [1 1]]]] [(md [[n (dv tag a)]]) (md [[n (dv tag c)]]) expected])
          [[(md [[n (dv 0 "x")] [m (dv 3 1)]]) (md [[m (dv 3 1)] [n (dv 0 "x")]]) [0 0]]
           [(md [[n (dv 0 "x")]]) (md [[n (dv 0 "x")] [n (dv 0 "x")]]) [0 0]]
           [(md [[n (dv 1 1)]]) (md [[n (add 1 [] 8 (biginteger "16045690981097406465") 0)]]) [1 1]]
           [(md [[n (dv 1 0)]]) (md [[n (add 1 [] 8 (biginteger "16045690981097406464") 0)]]) [1 1]]
           [(md [[n (dv 3 7)]]) (md [[n (dv 4 7)]]) [0 0]]])
        cases (vec cases) roots ((:finish b) (vec (mapcat #(take 2 %) cases)))]
    (try (doseq [[i [_ _ expected]] (map-indexed vector cases)] (is (= expected (compare-pair ctx (nth roots (* 2 i)) (nth roots (inc (* 2 i)))))))
         (finally (j/close! ctx e)))))
(deftest models-syntax-source-info-substring-repair-and-preresolved-order
  (let [ctx (model-context) e (:engine ctx) b (model-builder ctx) add (:add b) expr (:expr b) name (:name b) lst (:list b)
        nm (name "id") z (expr 0 [0]) ns (add 0 [nm] 0 0 0) decl (add 1 [nm (lst ["x" "y"])] 0 0 0)
        raw #(add 0 [%1 %2 %3] 0 0 0)
        ident #(add 3 [%1 %2 nm (lst %3)] 0 0 0)
        wrap (fn [stx] (expr 10 [(lst [(add 0 [nm (add 5 [stx] 0 0 0)] 0 0 0)]) z]))
        node #(add 1 [%1 nm ((:array b) %2)] 0 0 0)
        cases [[(wrap (add 2 ["ignored1" "x"] 0 0 0)) (wrap (add 2 ["ignored2" "x"] 0 0 0)) [1 1]]
               [(wrap (add 2 [0 "x"] 0 0 0)) (wrap (add 2 [0 "y"] 0 0 0)) [0 0]]
               [(wrap (ident 0 (raw "_id_" 1 3) [ns decl])) (wrap (ident 7 (raw "id" 0 2) [ns decl])) [1 1]]
               [(wrap (ident 0 (raw "id" 0 2) [ns decl])) (wrap (ident 0 (raw "id" 0 2) [decl ns])) [0 0]]
               [(wrap (ident 0 (raw "é" 1 2) [])) (wrap (ident 0 (raw "" 0 0) [])) [1 1]]
               [(wrap (node 0 [0 (add 2 [0 "x"] 0 0 0)])) (wrap (node 8 [0 (add 2 [8 "x"] 0 0 0)])) [1 1]]]
        roots ((:finish b) (vec (mapcat #(take 2 %) cases)))]
    (try (doseq [[i [_ _ expected]] (map-indexed vector cases)] (is (= expected (compare-pair ctx (nth roots (* 2 i)) (nth roots (inc (* 2 i)))))))
         (finally (j/close! ctx e)))))
(deftest models-native-low-hash-depth-and-app-spine-cache-rules
  (let [ctx (model-context) e (:engine ctx) b (model-builder ctx) add (:add b) expr (:expr b)
        z (expr 0 [0])
        a (expr 5 [z z]) a2 (add 5 [z z] 8 1 0)
        cases [[z (add 0 [0] 8 1 0) [0 0]]
               [z (add 0 [0] 8 (biginteger "18446744069414584320") 0) [1 1]]
               [(expr 5 [a z]) (expr 5 [a2 z]) [1 1]]
               [a a2 [0 0]]
               [(expr 3 [(add 1 [0] 8 9 0)]) (expr 3 [(add 1 [0] 8 (+ 9 (bit-shift-left 1 40)) 0)]) [0 0]]
               [(expr 3 [(add 4 [0] 8 9 0)]) (expr 3 [(add 4 [0] 8 (+ 9 (bit-shift-left 1 32)) 0)]) [1 1]]]
        roots ((:finish b) (vec (mapcat #(take 2 %) cases))) counts (k/counters ctx e)]
    (try (doseq [[i [_ _ expected]] (map-indexed vector cases)] (is (= expected (compare-pair ctx (nth roots (* 2 i)) (nth roots (inc (* 2 i)))))))
         (is (= counts (k/counters ctx e))) (finally (j/close! ctx e)))))
(deftest borrowed-raw-root-pap-factory-import-and-host-registration-fences
  (let [ctx (context) engine (j/machine ctx) value (j/call ctx engine "Lean.Expr.bvar._override" [0])]
    (try
      (doseq [label ["Lean.Expr.eqv" "Lean.Expr.equal"]]
        (is (g/bad? #(j/call ctx engine label [value value]))) (is (= "idle" (j/phase ctx engine)))
        (is (= 1 (c/rc ctx value))) (is (g/bad? #(j/make-closure! ctx engine label [])))
        (is (g/bad? #(context [(c/decl "bad-pap" [] "object"
                       (c/let-ir 1 "object" {:pap {:c (named label) :ys []}} (c/ret 1)))])))
        (let [base (j/prepare-host-program *basis* [] []) source (j/source-binding base (Object.))
              h (j/declaration-header source (get (record label) "row") (get (record label) "sha256"))
              next (j/register-headers base [h]) e (j/machine next)]
          (is (g/bad? #(j/install-graph! next e
                  (j/prepared-graph next source (Object.) [(j/graph-node next {:kind :closure :id 1 :target h})] [] [] [(j/graph-ref next 1)]))))
          (is (false? (host/private-value e "graphInstalled"))) (j/close! next e))
        (is (g/bad? #(j/prepare-host-program *basis* [] [(host/spec (if (.endsWith label "eqv") "lean_expr_eqv" "lean_expr_equal") ["object" "object"] [true true] "uint8")]))))
      (finally (j/release! ctx engine value) (j/close! ctx engine)))))
(deftest models-cycles-and-work-have-named-rejections-without-owner-effects
  (let [ctx (model-context) e (:engine ctx) source (j/source-binding ctx (Object.))
        [a b] (j/install-graph! ctx e (j/prepared-graph ctx source (Object.)
                    [(j/graph-node ctx {:kind :ctor :id 1 :tag 5 :fields [(j/graph-ref ctx 1) (j/graph-ref ctx 1)] :scalars (repeat 8 0)})
                     (j/graph-node ctx {:kind :ctor :id 2 :tag 5 :fields [(j/graph-ref ctx 2) (j/graph-ref ctx 2)] :scalars (repeat 8 0)})]
                    [] [] [(j/graph-ref ctx 1) (j/graph-ref ctx 2)])) counts (k/counters ctx e)]
    (is (= [1 1] (compare-pair ctx a a)))
    (is (re-find #"equality cycle outside bounded" (c/failure #(compare-pair ctx a b))))
    (is (= counts (k/counters ctx e)))))
(deftest models-deep-spine-and-shared-dag-are-iterative
  (let [ctx (model-context) e (:engine ctx) b (model-builder ctx) expr (:expr b) name (:name b)
        make (fn [leaf mode depth] (let [n (name leaf) z (expr 0 [0]) t (expr 6 [n z z])]
                                    (loop [i depth a t] (if (zero? i) a (recur (dec i) (expr 5 [a (if (= mode :dag) a z)]))))))
        roots ((:finish b) [(make "x" :spine 4096) (make "y" :spine 4096) (make "x" :dag 22) (make "y" :dag 22)])]
    (try (is (= [1 0] (compare-pair ctx (nth roots 0) (nth roots 1))))
         (is (= [1 0] (compare-pair ctx (nth roots 2) (nth roots 3))))
         (finally (j/close! ctx e)))))
(deftest malformed-heads-kinds-and-leaf-work-reject-without-guest-effects
  (doseq [descriptor [{:kind :ref :id 1 :fields [0]}
                      {:kind :array :id 1 :fields [0]}
                      {:kind :byte-array :id 1 :bytes [0]}
                      {:kind :ctor :id 1 :tag 12 :fields [0] :scalars (repeat 8 0)}
                      {:kind :ctor :id 1 :tag 0 :fields [0] :scalars (repeat 7 0)}
                      {:kind :ctor :id 1 :tag 6 :fields [0 0 0] :scalars (repeat 8 0)}]]
    (let [ctx (model-context) e (:engine ctx) source (j/source-binding ctx (Object.))
          [value] (j/install-graph! ctx e (j/prepared-graph ctx source (Object.) [(j/graph-node ctx descriptor)] [] [] [(j/graph-ref ctx 1)]))
          counts (k/counters ctx e)]
      (is (g/bad? #(compare-pair ctx value value))) (is (= counts (k/counters ctx e)))))
  (let [ctx (model-context) e (:engine ctx) b (model-builder ctx) add (:add b) expr (:expr b)
        text (apply str (repeat 600000 "x"))
        [a d] ((:finish b) [(expr 9 [(add 1 [text] 0 0 0)]) (expr 9 [(add 1 [text] 0 0 0)])])
        counts (k/counters ctx e)]
    (is (re-find #"equality work outside bounded" (c/failure #(compare-pair ctx a d))))
    (is (= counts (k/counters ctx e)))))
(deftest interrupt-guard-is-local-and-does-not-change-guest-owners
  (let [ctx (model-context) e (:engine ctx) b (model-builder ctx) add (:add b) expr (:expr b)
        text (apply str (repeat 2048 "x"))
        [a d] ((:finish b) [(expr 9 [(add 1 [text] 0 0 0)]) (expr 9 [(add 1 [text] 0 0 0)])])
        counts (k/counters ctx e) outcome (atom nil)
        worker (Thread. ^Runnable (fn []
                  (.interrupt (Thread/currentThread))
                  (try (reset! outcome (c/failure #(compare-pair ctx a d)))
                       (finally (Thread/interrupted)))))]
    ;; This private worker alone uses e during the call; no retained REPL thread
    ;; is interrupted. No kernel/native host adapter scope is installed.
    (.start worker) (.join worker 1000)
    (is (not (.isAlive worker))) (is (re-find #"equality interrupted" (or @outcome "")))
    (is (= counts (k/counters ctx e)))))
(deftest original-owned-wrapper-code-host-fork-and-typed-reply-boundaries
  (let [spec (host/spec "research_expr_equality" ["uint8"] [false] "uint8")
        model (c/decl "model-bvar" [(c/p 1 "object")] "object" (c/let-ir 2 "object" (c/ctor 0 [(c/v 1)] 8) (c/ret 2)))
        base (j/prepare-host-program *basis* (x/raw [model (host/ext "host-bool" spec)]) [spec])
        source (j/source-binding base (Object.)) nr (record "Lean.Expr.eqv") wr (record "Lean.Expr.eqv._boxed")
        native (j/declaration-header source (get nr "row") (get nr "sha256"))
        wrapper (j/declaration-header source (get wr "row") (get wr "sha256"))
        ctx (j/register-headers base [native wrapper])
        caller (c/decl "caller" [(c/p 1 "object") (c/p 2 "object")] "uint8"
                 (c/let-ir 3 "object" {:fap {:c (get-in wr ["row" "name"]) :ys [(c/v 1) (c/v 2)]}}
                   (c/let-ir 4 "uint8" {:unbox {:x {:idx 3}}}
                     ["dec" {:idx 3} 1 false false
                      (c/let-ir 5 "uint8" (c/fap "host-bool" [(c/v 4)]) (c/ret 5))])))
        ctx (j/extend-program ctx (x/raw [caller])) parent (j/machine ctx)
        a (j/call ctx parent "model-bvar" [0]) b (j/call ctx parent "model-bvar" [0])
        ready (j/materialize-body ctx wrapper (get wr "row") [native])]
    (j/start! ctx parent "caller" [a b])
    (let [request (code/request! ctx parent) child (:engine (j/fork! ctx parent []))]
      (try
        (is (identical? wrapper (.header request)))
        (doseq [[e answer] [[parent 1] [child 0]]]
          (j/resume-code! ready e (j/code-request ready e))
          (let [r (host/request! ready e)]
            (is (= [1] (host/args r))) (is (g/bad? #(j/resume-host! ready e r -1)))
            (is (identical? r (j/host-request ready e)))
            (j/resume-host! ready e r answer) (is (= answer (code/finish! ready e)))))
        (is (true? (host/private-value a "dead"))) (is (true? (host/private-value b "dead")))
        (finally (j/close! ready parent) (j/close! ready child))))))
(defn forged-raw-closure [ctx label]
  (let [cls ^Class (:node-class ctx) ctor (.getDeclaredConstructor cls (into-array Class [Integer/TYPE Integer/TYPE Integer/TYPE]))
        _ (.setAccessible ctor true) value (.newInstance ctor (object-array [(int 245) (int 0) (int 0)]))
        functions (host/private-value (:program ctx) "functions")
        function (aget ^objects functions (int (j/function-id ctx label)))]
    (doseq [[key payload] [["closure" function] ["metadata" (host/private-value (:program ctx) "generation")]]]
      (let [f (.getDeclaredField cls key)] (.setAccessible f true) (.set f value payload))) value))
(deftest model-forged-borrowed-closures-and-host-replies-reject-before-claim
  (let [rows (concat (map #(get % "row") (records)) [(host/ext "host" host/owned) (first g/common) (second g/common)])
        ctx (j/prepare-host-program *basis* (x/raw rows) [host/owned]) e (j/machine ctx)]
    (try
      (doseq [label ["Lean.Expr.eqv" "Lean.Expr.equal"] :let [value (forged-raw-closure ctx label)]]
        (is (g/bad? #(j/call ctx e "identity" [value]))) (is (= "idle" (j/phase ctx e)))
        (is (= 1 (c/rc ctx value)))
        (j/start! ctx e "host" [0])
        (let [r (j/host-request ctx e)]
          (is (g/bad? #(j/resume-host! ctx e r value))) (is (identical? r (j/host-request ctx e)))
          (is (= 1 (c/rc ctx value)))
          (j/resume-host! ctx e r 0) (is (= 0 (j/take-result! ctx e))))
        (j/release! ctx e value))
      (finally (j/close! ctx e)))))
(deftest syntax-arrays-compare-logical-size-not-spare-capacity
  (let [array-rows (json/read-str (slurp "test/fixtures/java-array-runtime/original-rows.json"))
        selected (filter #(contains? #{"Array.emptyWithCapacity" "Array.emptyWithCapacity._boxed" "Array.push" "Array.push._boxed"} (get % "label")) array-rows)
        wrap (c/decl "wrap-syntax-array" [(c/p 1 "object")] "object"
               (c/let-ir 2 "object" (c/ctor 1 ["erased" "erased" (c/v 1)] 0)
                 (c/let-ir 3 "object" (c/ctor 5 [(c/v 2)] 0)
                   (c/let-ir 4 "object" (c/ctor 0 ["erased" (c/v 3)] 0)
                     (c/let-ir 5 "object" (c/ctor 1 [(c/v 4) "erased"] 0)
                       (c/let-ir 6 "object" (c/ctor 0 ["erased"] 8)
                         (c/let-ir 7 "object" (c/ctor 10 [(c/v 5) (c/v 6)] 8) (c/ret 7))))))))
        ctx (context (concat (map #(get % "row") selected) [wrap])) e (j/machine ctx)
        mk (fn [capacity] (let [a (j/call ctx e "Array.emptyWithCapacity._boxed" [0 capacity])]
                           (j/call ctx e "Array.push._boxed" [0 a 0])))
        aa (mk 4) bb (mk 8)
        a (j/call ctx e "wrap-syntax-array" [aa]) b (j/call ctx e "wrap-syntax-array" [bb])
        ctx (assoc ctx :engine e) counts (k/counters ctx e)]
    (try
      (is (= 1 (.arraySize aa) (.arraySize bb)))
      (is (< (alength ^objects (.get ^java.lang.reflect.Field (:fields ctx) aa))
             (alength ^objects (.get ^java.lang.reflect.Field (:fields ctx) bb))))
      (is (= [1 1] (compare-pair ctx a b))) (is (= counts (k/counters ctx e)))
      (finally (j/release! ctx e a) (j/release! ctx e b) (j/close! ctx e)))))
(deftest exact-constructor-scalar-casts-cover-full-byte-domain-and-high-u64
  (let [ctx (context) e (j/machine ctx)]
    (try
      (doseq [value (range 256)]
        (is (= value (j/call ctx e "UInt8.toUInt32" [value])))
        (is (= value (j/call ctx e "UInt8.toUInt32._boxed" [value]))))
      (doseq [value [0 1 255 256 257 (biginteger "4294967295") u/high u/max64]
              :let [expected (.longValue (.and (biginteger value) (biginteger 255)))]]
        (is (= expected (j/call ctx e "UInt64.toUInt8" [value])))
        (is (= expected (j/call ctx e "UInt64.toUInt8._boxed" [(u/box ctx e value)]))))
      (doseq [[label invalids] [["UInt8.toUInt32" [-1 256 u/max64 "not-a-scalar"]]
                               ["UInt64.toUInt8" [-1 (inc u/max64) "not-a-scalar"]]]
              value invalids :let [before (k/counters ctx e)]]
        (is (g/bad? #(j/call ctx e label [value])))
        (is (= "idle" (j/phase ctx e))) (is (= before (k/counters ctx e))))
      (finally (j/close! ctx e)))))
(defn check! [basis] (binding [*basis* basis] (clojure.test/run-tests 'java-ir-expr-equality-checks)))
