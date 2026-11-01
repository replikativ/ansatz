(ns java-ir-pointer-checks
  "Certified local identity equality; no escaping addresses or native FFI."
  (:require [clojure.test :refer [deftest is run-tests]]
            [clojure.data.json :as json] [clojure.edn :as edn]
            [java-ir-baseline :as j] [java-ir-baseline-checks :as c]
            [java-ir-extern-checks :as x] [java-ir-host-checks :as host]
            [java-ir-generation-checks :as g] [java-ir-header-checks :as header]
            [java-ir-code-checks :as code] [java-ir-byte-array-checks :as byte] [lean-compatibility-corpus :as corpus]))
(def ^:dynamic *basis* nil)
(def fixture "test/fixtures/java-pointer-runtime/original-rows.json")
(defn records [path] (json/read-str (slurp path)))
(defn rows [path] (mapv #(get % "row") (records path)))
(defn original [label]
  (get (first (filter #(= label (get % "label"))
               (records "test/fixtures/java-pointer-runtime/name-comparison-rows.json"))) "row"))
(def pointer (first (rows fixture)))
(def equality (original "USize.decEq"))
(defn direct [row args] {:fap {:c (get row "name") :ys args}})
(defn ptr [id] (direct pointer ["erased" (c/v id)]))
(defn equal [a b] (direct equality [(c/v a) (c/v b)]))
(defn observed [cont]
  (c/let-ir 10 "usize" (ptr 1)
    (c/let-ir 11 "usize" (ptr 2)
      (c/let-ir 12 "uint8" (equal 10 11) cont))))
(defn compare-row []
  (c/decl "identity-eq" [(c/p 1 "object") (c/p 2 "object")] "uint8"
    (observed ["dec" {:idx 1} 1 false false ["dec" {:idx 2} 1 false false (c/ret 12)]])))
(defn common []
  [pointer equality (compare-row)
   (c/decl "fresh" [(c/p 1 "object")] "object"
     (c/let-ir 2 "object" (c/ctor 0 [] 1) (c/ret 2)))
   (second g/common)])
(defn prepare [extra]
  (assoc *basis* :program (j/invoke-static (:prepare *basis*) [(x/raw (concat (common) extra))])))
(defn private-field [object name] (host/private-value object name))
(defn metadata [node] (private-field node "metadata"))
(defn word [node] (private-field (metadata node) "word"))
(defn fresh [ctx engine] (j/call ctx engine "fresh" [0]))
(defn same [ctx engine a b]
  (j/retain! ctx engine a) (j/retain! ctx engine b)
  (j/call ctx engine "identity-eq" [a b]))
(defn finish [ctx engine] (code/finish! ctx engine))

(deftest genuine-name-comparator-preserves-hash-collision-fallback
  (let [comparison "test/fixtures/java-pointer-runtime/name-comparison-rows.json"
        manifest (edn/read-string (slurp "test/fixtures/java-pointer-runtime/provenance.edn"))
        names (rows "test/fixtures/java-u64-runtime/name-rows.json")
        all (vals (into {} (map (juxt #(get % "name") identity) (concat (rows comparison) names))))
        ctx (assoc *basis* :program (j/invoke-static (:prepare *basis*) [all])) engine (j/machine ctx)
        label "_private.Lean.Data.Name.0.Lean.Name.quickCmpImpl._boxed"
        a (j/call ctx engine "Lean.Name.str._override" [0 "foo"])
        equal-name (j/call ctx engine "Lean.Name.str._override" [0 "foo"])
        other (j/call ctx engine "Lean.Name.str._override" [0 "bar"])
        cmp (fn [left right]
              (j/retain! ctx engine left) (j/retain! ctx engine right)
              (j/call ctx engine label [left right]))]
    (try
      (is (= (:fixture-sha256 manifest) (corpus/sha256 fixture)))
      (is (= (get-in manifest [:files "name-comparison-rows.json" :sha256]) (corpus/sha256 comparison)))
      (is (= 1 (cmp a a)))
      (is (= 1 (cmp a equal-name)))
      (is (not= (word a) (word equal-name)))
      (is (not= 1 (cmp a other)))
      (is (= 1 (cmp 0 0)))
      (is (= 1 (c/rc ctx a) (c/rc ctx equal-name) (c/rc ctx other)))
      (finally
        (doseq [value [a equal-name other]] (j/release! ctx engine value))
        (j/close! ctx engine)))))

(deftest identity-domain-and-lazy-metadata-preserve-owner-credits
  (let [ctx (prepare []) engine (j/machine ctx) a (fresh ctx engine) b (fresh ctx engine)]
    (try
      (is (nil? (metadata a)))
      (is (= 1 (same ctx engine a a))) (is (= 0 (same ctx engine a b)))
      (is (not= (word a) (word b))) (is (zero? (bit-and 7 (word a))))
      (is (= 1 (c/rc ctx a) (c/rc ctx b)))
      (doseq [v [0 1 Long/MAX_VALUE]] (is (= 1 (same ctx engine v v))))
      (is (= 0 (same ctx engine 0 a)))
      (finally (j/release! ctx engine a) (j/release! ctx engine b) (j/close! ctx engine))))
  (doseq [v ["same" (biginteger 0) -1]]
    (let [ctx (prepare []) engine (j/machine ctx)]
      (is (re-find #"canonical nonnegative Long" (c/failure #(j/call ctx engine "identity-eq" [v v])))))))

(deftest fork-between-observations-preserves-words-and-rejects-foreign-values
  (let [ctx (assoc (prepare []) :explicit true) engine (j/machine ctx) a (fresh ctx engine)]
    (j/retain! ctx engine a) (j/retain! ctx engine a)
    (j/start! ctx engine "identity-eq" [a a]) (j/advance! ctx engine 1)
    (let [{child :engine [b] :roots} (j/fork! ctx engine [a]) parent-word (word a)]
      (try
        (is (= parent-word (word b)))
        (is (not (identical? (private-field (metadata a) "owner") (private-field (metadata b) "owner"))))
        (is (= 1 (finish ctx engine) (finish ctx child)))
        (is (= 1 (c/rc ctx a) (c/rc ctx b)))
        (is (g/bad? #(j/call ctx child "fresh" [a])))
        (is (= "idle" (j/phase ctx child)))
        (is (g/bad? #(j/fork! ctx child [a])))
        (let [x (fresh ctx engine) y (fresh ctx child)]
          (same ctx engine x x) (same ctx child y y)
          (is (not= (word x) (word y)))
          (j/release! ctx engine x) (j/release! ctx child y))
        (finally (j/release! ctx engine a) (j/release! ctx child b)
                 (j/close! ctx engine) (j/close! ctx child))))))

(deftest all-pointer-word-escapes-and-mixed-equality-reject-at-preparation
  (let [base (fn [body type] (c/decl "bad" [(c/p 1 "object") (c/p 2 "usize")] type
                                        (c/let-ir 10 "usize" (ptr 1) body)))]
    (doseq [row [(base (c/ret 10) "usize")
                 (base (c/let-ir 11 "object" {:box {:ty "usize" :x {:idx 10}}} (c/ret 11)) "object")
                 (base (c/let-ir 11 "uint8" (equal 10 2) (c/ret 11)) "uint8")
                 (base ["case" (c/name-ir "USize") {:idx 10} "usize" [["default" (c/ret 2)]]] "usize")
                 (base ["uset" {:idx 1} 0 {:idx 10} (c/ret 1)] "object")
                 (base ["jdecl" {:idx 20} [(c/p 21 "usize")] (c/ret 21) ["jmp" {:idx 20} [(c/v 10)]]] "usize")
                 (base (c/ret 1) "object")
                 (second (rows fixture))]]
      (is (g/bad? #(prepare [row]))))
    (is (g/bad? #(prepare [(c/decl "partial" [(c/p 1 "object")] "object"
                             (c/let-ir 2 "object" {:pap {:c (get pointer "name") :ys []}} (c/ret 2)))])))))

(deftest raw-root-makeclosure-and-import-cannot-authorize-pointer-dispatch
  (let [ctx (prepare []) engine (j/machine ctx) a (fresh ctx engine)]
    (try
      (is (g/bad? #(j/call ctx engine "ptrAddrUnsafe" [0 a])))
      (is (= "idle" (j/phase ctx engine))) (is (= 1 (c/rc ctx a)))
      (is (g/bad? #(j/make-closure! ctx engine "ptrAddrUnsafe" [])))
      (let [source (j/source-binding ctx (Object.)) target (j/declaration-header source pointer header/digest)
            ctx2 (j/register-headers (j/prepare-host-program *basis* [] []) [target])
            engine2 (j/machine ctx2)]
        (try
          (is (g/bad? #(j/install-graph! ctx2 engine2
                  (j/prepared-graph ctx2 source (Object.)
                    [(j/graph-node ctx2 {:kind :closure :id 1 :target target})] [] [] [(j/graph-ref ctx2 1)]))))
          (is (false? (private-field engine2 "graphInstalled")))
          (finally (j/close! ctx2 engine2))))
      (finally (j/release! ctx engine a) (j/close! ctx engine)))))

(deftest kind-metadata-wrappers-preserve-array-state-and-closure-generation
  (let [array-row (host/ext "array-empty" (host/spec "lean_mk_empty_array_with_capacity" ["erased" "tobject"] [false true] "object"))
        push-row (host/ext "array-push" (host/spec "lean_array_push" ["erased" "object" "tobject"] [false false false] "object"))
        ctx (prepare [array-row push-row]) engine (j/machine ctx)
        a (j/call ctx engine "array-empty" [0 4])
        closure (j/make-closure! ctx engine "fresh" [])]
    (try
      (same ctx engine a a) (same ctx engine closure closure)
      (is (= 0 (.arraySize a)))
      (let [{child :engine [b child-closure] :roots} (j/fork! ctx engine [a closure])]
        (try
          (is (= (word a) (word b))) (is (= 0 (.arraySize b)))
          (is (not (identical? (private-field (metadata a) "inner") (private-field (metadata b) "inner"))))
          (is (identical? b (j/call ctx child "array-push" [0 b 99])))
          (is (= 0 (.arraySize a))) (is (= 1 (.arraySize b)))
          (is (= (word closure) (word child-closure)))
          (is (identical? (private-field (metadata closure) "inner") (private-field (metadata child-closure) "inner")))
          (let [v (j/call ctx child "apply" [child-closure 0])] (j/release! ctx child v))
          (finally (j/release! ctx child b) (j/close! ctx child))))
      (finally (j/release! ctx engine a) (j/release! ctx engine closure) (j/close! ctx engine)))))

(deftest suspended-caller-certificate-survives-code-host-fork-and-program-installation
  (let [spec (host/spec "research_pointer_gap" ["object"] [false] "object")
        base (j/prepare-host-program *basis* [] [spec]) source (j/source-binding base (Object.))
        host-row (host/ext "gap-host" spec)
        gap-row (c/decl "gap" [(c/p 1 "object")] "uint8"
                  (c/let-ir 2 "object" (c/fap "gap-host" ["erased"])
                    ["dec" {:idx 2} 1 false false (c/let-ir 3 "uint8" (c/lit 0) (c/ret 3))]))
        [ph eh hh gh] (mapv #(header/header source %) [pointer equality host-row gap-row])
        base (j/register-headers base [ph eh hh gh])
        caller (c/decl "paused" [(c/p 1 "object") (c/p 2 "object")] "uint8"
                 (c/let-ir 10 "usize" (ptr 1)
                   (c/let-ir 13 "uint8" (c/fap "gap" ["erased"])
                     (c/let-ir 11 "usize" (ptr 2)
                       (c/let-ir 12 "uint8" (equal 10 11)
                         ["dec" {:idx 1} 1 false false ["dec" {:idx 2} 1 false false (c/ret 12)]])))))
        ctx (j/extend-program base (x/raw [caller (nth (common) 3)]))
        ready (j/materialize-body ctx gh (first (x/raw [gap-row])) [hh])
        engine (j/machine ctx) value (fresh ctx engine)]
    (j/retain! ctx engine value) (j/retain! ctx engine value)
    (j/start! ctx engine "paused" [value value])
    (let [request (code/request! ctx engine)
          {child :engine [child-value] :roots} (j/fork! ctx engine [value])]
      (try
        (is (= (word value) (word child-value)))
        (j/resume-code! ready engine request)
        (j/resume-code! ready child (j/code-request ctx child))
        (let [parent-host (host/request! ready engine) child-host (host/request! ready child)
              descendant (j/extend-program ready (x/raw [(g/literal "installed-later" 7)]))]
          (is (g/bad? #(j/resume-host! ready child child-host value)))
          (is (identical? child-host (j/host-request ready child)))
          (is (= 3 (c/rc ctx value) (c/rc ctx child-value)))
          (j/install-program! descendant engine) (j/install-program! descendant child)
          (j/resume-host! descendant engine parent-host 0) (j/resume-host! descendant child child-host 0)
          (is (= 1 (finish descendant engine) (finish descendant child)))
          (is (= 1 (c/rc ctx value) (c/rc ctx child-value))))
        (finally (j/release! ctx engine value) (j/release! ctx child child-value)
                 (j/close! ctx engine) (j/close! ctx child))))))

(defn forged-raw-closure
  "Negative ingress fixture: bypass the public constructors to test the fence."
  [ctx]
  (let [node ^Class (:node-class ctx)
        ctor (.getDeclaredConstructor node (into-array Class [Integer/TYPE Integer/TYPE Integer/TYPE]))
        _ (.setAccessible ctor true) value (.newInstance ctor (object-array [(int 245) (int 0) (int 0)]))
        functions (private-field (:program ctx) "functions")
        function (aget ^objects functions (int (j/function-id ctx "ptrAddrUnsafe")))]
    (doseq [[field payload] [["closure" function] ["metadata" (private-field (:program ctx) "generation")]]]
      (let [f (.getDeclaredField node field)] (.setAccessible f true) (.set f value payload)))
    value))

(deftest first-class-raw-pointer-closure-cannot-enter-through-object-or-host-reply
  (let [spec host/owned
        ctx (j/prepare-host-program *basis* (x/raw (concat (common) [(host/ext "host" spec)])) [spec])
        engine (j/machine ctx) raw (forged-raw-closure ctx)]
    (try
      (is (g/bad? #(j/call ctx engine "fresh" [raw])))
      (is (= "idle" (j/phase ctx engine))) (is (= 1 (c/rc ctx raw)))
      (j/start! ctx engine "host" [0])
      (let [request (j/host-request ctx engine)]
        (is (g/bad? #(j/resume-host! ctx engine request raw)))
        (is (identical? request (j/host-request ctx engine)))
        (is (= 1 (c/rc ctx raw)))
        (j/resume-host! ctx engine request 0)
        (is (= 0 (j/take-result! ctx engine))))
      (finally (j/release! ctx engine raw) (j/close! ctx engine))))
  (let [ctx (prepare []) engine (j/machine ctx) raw (forged-raw-closure ctx)]
    (is (g/bad? #(j/call ctx engine "apply" [raw 0])))
    (is (= 1 (c/rc ctx raw)))
    (is (false? (private-field raw "dead")))
    (j/release! ctx engine raw)))

(deftest exact-certificate-is-immutable-and-cannot-be-borrowed-by-another-body
  (let [ctx (prepare []) other (prepare []) engine (j/machine ctx)
        pb (aget ^objects (private-field (:program ctx) "preparedBodies") (int (j/function-id ctx "identity-eq")))
        other-pb (aget ^objects (private-field (:program other) "preparedBodies") (int (j/function-id other "identity-eq")))
        sites (private-field pb "pointerSites") alien-site (first (seq (private-field other-pb "pointerSites")))
        function (private-field alien-site "target")
        method (.getDeclaredMethod (class engine) "pointerIdentity"
                 (into-array Class [(class function) (class (int-array 0)) (class pb) (class alien-site)]))]
    (try
      (is (= 2 (count sites)))
      (is (g/bad? #(.add ^java.util.Set sites nil)))
      (.setAccessible method true)
      (is (g/bad? #(.invoke method engine (object-array [function (int-array [0 1]) pb alien-site]))))
      (let [site (first (seq sites)) target (private-field site "target")
            copied-slots (aclone ^ints (private-field site "args"))]
        (is (re-find #"exact certified FAP site"
              (c/failure #(.invoke method engine (object-array [target copied-slots pb site]))))))
      (is (= "idle" (j/phase ctx engine)))
      (finally (j/close! ctx engine)))))

(deftest allocator-exhaustion-and-no-common-node-state-growth
  (let [loader (:loader *basis*) cls (Class/forName "ansatz.lean.jvm.internal.exec.Interpreter$PointerAllocator" true loader)
        ctor (.getDeclaredConstructor cls (into-array Class [Long/TYPE]))
        _ (.setAccessible ctor true) allocator (.newInstance ctor (object-array [(long -8)]))
        allocate (.getDeclaredMethod cls "allocate" (make-array Class 0))]
    (.setAccessible allocate true)
    (is (= -8 (.invoke allocate allocator (object-array 0))))
    (is (g/bad? #(.invoke allocate allocator (object-array 0)))))
  (is (= #{"tag" "rc" "fields" "scalars" "closure" "metadata" "dead" "array" "ref" "readyTask"}
         (set (map #(.getName ^java.lang.reflect.Field %) (.getDeclaredFields ^Class (:node-class *basis*)))))))

(deftest operand-audit-rejects-call-capture-projection-mutation-and-hidden-branch-escapes
  (let [wrapped (fn [tail type] (c/decl "escape" [(c/p 1 "object") (c/p 2 "object")] type
                                 (c/let-ir 10 "usize" (ptr 1) tail)))
        identity (c/decl "ordinary-word" [(c/p 1 "usize")] "usize" (c/ret 1))
        rows [(wrapped (c/let-ir 11 "usize" (c/fap "ordinary-word" [(c/v 10)]) (c/ret 11)) "usize")
              (wrapped (c/let-ir 11 "object" (c/ctor 0 [(c/v 10)] 0) (c/ret 11)) "object")
              (wrapped (c/let-ir 11 "object" {:proj {:x {:idx 10} :i 0}} (c/ret 11)) "object")
              (wrapped (c/let-ir 11 "usize" {:uproj {:x {:idx 10} :i 0}} (c/ret 11)) "usize")
              (wrapped (c/let-ir 11 "uint8" {:isShared {:x {:idx 10}}} (c/ret 11)) "uint8")
              (wrapped (c/let-ir 11 "usize" {:unbox {:x {:idx 10}}} (c/ret 11)) "usize")
              (wrapped (c/let-ir 11 "object" {:ap {:x {:idx 10} :ys [(c/v 2)]}} (c/ret 11)) "object")
              (wrapped (c/let-ir 11 "object" {:pap {:c (c/name-ir "fresh") :ys [(c/v 10)]}} (c/ret 11)) "object")
              (wrapped ["set" {:idx 1} 0 {:idx 10} (c/ret 1)] "object")
              (wrapped ["sset" {:idx 1} 0 0 {:idx 10} "uint64" (c/ret 1)] "object")
              (wrapped ["inc" {:idx 10} 1 false false (c/ret 1)] "object")
              (wrapped ["dec" {:idx 10} 1 false false (c/ret 1)] "object")
              (wrapped ["del" {:idx 10} (c/ret 1)] "object")
              (wrapped ["setTag" {:idx 10} 0 (c/ret 1)] "object")
              (c/decl "hidden-join" [(c/p 1 "object")] "object"
                ["jdecl" {:idx 20} []
                 (c/let-ir 10 "usize" (ptr 1) (c/let-ir 11 "object" {:box {:ty "usize" :x {:idx 10}}} (c/ret 11)))
                 (c/ret 1)])]]
    (doseq [row rows] (is (g/bad? #(prepare [identity row])))))
  (let [spec (host/spec "lookalike_equality" ["usize" "usize"] [false false] "uint8")
        fake (host/ext "lookalike" spec)
        row (c/decl "bad-equality" [(c/p 1 "object") (c/p 2 "object")] "uint8"
              (c/let-ir 10 "usize" (ptr 1)
                (c/let-ir 11 "usize" (ptr 2)
                  (c/let-ir 12 "uint8" (c/fap "lookalike" [(c/v 10) (c/v 11)]) (c/ret 12)))))]
    (is (g/bad? #(j/prepare-host-program *basis* (x/raw [pointer fake row]) [spec]))))
  (let [spec (host/spec "lean_ptr_addr" ["erased" "tobject"] [false true] "usize")]
    (is (g/bad? #(j/prepare-host-program *basis* [] [spec])))))

(deftest raw-dispatch-and-lazy-materialization-cannot-inherit-an-ambient-certificate
  (let [ctx (assoc (prepare []) :explicit true) engine (j/machine ctx) value (fresh ctx engine)
        function (aget ^objects (private-field (:program ctx) "functions") (int (j/function-id ctx "ptrAddrUnsafe")))]
    (j/retain! ctx engine value) (j/retain! ctx engine value)
    (j/start! ctx engine "identity-eq" [value value]) (j/advance! ctx engine 1)
    (let [before [(word value) (c/rc ctx value) (private-field engine "allocations")]]
      (doseq [[method-name parameter arguments]
              [["intrinsicSlots" (class (int-array 0)) (int-array [0 1])]
               ["intrinsicExternal" (class (object-array 0)) (object-array [0 value])]]]
        (let [method (.getDeclaredMethod (class engine) method-name (into-array Class [(class function) parameter]))]
          (.setAccessible method true)
          (is (g/bad? #(.invoke method engine (object-array [function arguments]))))))
      (is (= before [(word value) (c/rc ctx value) (private-field engine "allocations")]))
      (is (= 1 (finish ctx engine)))
      (j/release! ctx engine value) (j/close! ctx engine)))
  (let [base (j/prepare-host-program *basis* [] []) source (j/source-binding base (Object.))
        boxed (second (rows fixture)) ph (j/declaration-header source pointer header/digest)
        wh (j/declaration-header source boxed header/digest)
        ctx (j/register-headers base [ph wh]) engine (j/machine ctx)]
    (j/start! ctx engine "ptrAddrUnsafe._boxed" [0 0])
    (let [request (j/code-request ctx engine)]
      (is (g/bad? #(j/materialize-body ctx wh boxed [ph])))
      (is (identical? request (j/code-request ctx engine)))
      (is (every? nil? (seq (private-field (:program ctx) "preparedBodies"))))
      (is (= "code-call" (j/phase ctx engine)))
      (j/fail-code! ctx engine request (ex-info "rejected escaping raw wrapper" {})))))

(deftest host-reply-raw-ap-is-denied-while-a-certified-caller-is-active
  (let [spec host/owned
        caller (c/decl "certified-host-ap" [(c/p 1 "object") (c/p 2 "object")] "object"
                 (observed (c/let-ir 20 "object" (c/fap "host" ["erased"])
                             (c/let-ir 21 "object" {:ap {:x {:idx 20} :ys ["erased" "erased"]}} (c/ret 21)))))
        target (c/decl "owned-two" [(c/p 1 "object") (c/p 2 "object")] "object" (c/ret 1))
        ctx (j/prepare-host-program *basis* (x/raw (concat (common) [(host/ext "host" spec) caller target])) [spec])
        engine (j/machine ctx) raw (forged-raw-closure ctx)]
    (try
      (j/start! ctx engine "certified-host-ap" [0 0])
      (let [request (host/request! ctx engine)]
        (is (seq (private-field (private-field engine "activePrepared") "pointerSites")))
        (is (g/bad? #(j/resume-host! ctx engine request raw)))
        (is (identical? request (j/host-request ctx engine)))
        (is (= 1 (c/rc ctx raw))) (is (false? (private-field raw "dead")))
        (j/resume-host! ctx engine request (j/make-closure! ctx engine "owned-two" []))
        (is (= 0 (finish ctx engine))))
      (finally (j/release! ctx engine raw) (j/close! ctx engine)))))

(defn private-instance [ctx suffix]
  (let [cls (Class/forName (str "ansatz.lean.jvm.internal.exec.Interpreter$" suffix) true (:loader ctx))
        ctor (.getDeclaredConstructor cls (make-array Class 0))]
    (.setAccessible ctor true) (.newInstance ctor (object-array 0))))
(defn private-set! [object field value]
  (let [f (.getDeclaredField (class object) field)]
    (.setAccessible f true)
    (if (= Integer/TYPE (.getType f)) (.setInt f object (int value)) (.set f object value))))

(deftest unaudited-analysis-opcodes-fail-closed-and-constructor-reuse-keeps-identity
  (let [ctx (prepare []) engine (j/machine ctx)
        body (private-instance ctx "Body")
        method (.getDeclaredMethod ^Class (:class ctx) "certifyPointerSites" (into-array Class [(class body)]))]
    (.setAccessible method true)
    (private-set! body "op" 999)
    (is (g/bad? #(.invoke method nil (object-array [body]))))
    (let [pb (aget ^objects (private-field (:program ctx) "preparedBodies") (int (j/function-id ctx "identity-eq")))
          ptr-expr (first (seq (private-field pb "pointerSites")))
          unknown (private-instance ctx "Body") expression (private-instance ctx "Expr")
          ret (private-instance ctx "Body")]
      (private-set! expression "op" 999)
      (doseq [[o k v] [[body "op" 0] [body "a" 10] [body "expr" ptr-expr] [body "next" unknown]
                       [unknown "op" 0] [unknown "a" 99] [unknown "expr" expression] [unknown "next" ret]
                       [ret "op" 8] [ret "a" 1]]]
        (private-set! o k v))
      (is (g/bad? #(.invoke method nil (object-array [body])))))
    (j/close! ctx engine))
  (let [ctx (prepare [(c/decl "retag" [(c/p 1 "object")] "object"
                       ["setTag" {:idx 1} 7 (c/ret 1)])])
        engine (j/machine ctx) value (fresh ctx engine)]
    (try
      (same ctx engine value value)
      (let [identity (word value)]
        (is (identical? value (j/call ctx engine "retag" [value])))
        (is (= identity (word value))))
      (is (= Object (class (private-field (metadata value) "owner"))))
      (is (= #{"word" "owner" "inner"}
             (set (map #(.getName ^java.lang.reflect.Field %) (.getDeclaredFields (class (metadata value)))))))
      (finally (j/release! ctx engine value) (j/close! ctx engine)))))

(deftest recursive-nested-and-self-tail-activations-use-their-own-sites
  (let [borrowed [(assoc (c/p 1 "object") :borrow true) (assoc (c/p 2 "object") :borrow true)]
        inner (c/decl "inner" borrowed "uint8" (observed (c/ret 12)))
        outer (c/decl "outer" [(c/p 1 "object") (c/p 2 "object")] "uint8"
                (c/let-ir 10 "usize" (ptr 1)
                  (c/let-ir 14 "uint8" (c/fap "inner" [(c/v 1) (c/v 2)])
                    (c/let-ir 11 "usize" (ptr 2)
                      (c/let-ir 12 "uint8" (equal 10 11)
                        ["dec" {:idx 1} 1 false false ["dec" {:idx 2} 1 false false (c/ret 12)]])))))
        nat-rows (x/originals) eq (nat-rows "Nat.decEq") sub (nat-rows "Nat.sub")
        again (c/let-ir 24 "object" (c/lit 1)
                (c/let-ir 25 "object" (direct sub [(c/v 2) (c/v 24)])
                  (c/let-ir 26 "uint8" (c/fap "loop" [(c/v 1) (c/v 25)]) (c/ret 26))))
        loop-row (c/decl "loop" [(c/p 1 "object") (c/p 2 "object")] "uint8"
                   (c/let-ir 10 "usize" (ptr 1)
                     (c/let-ir 11 "usize" (ptr 1)
                       (c/let-ir 12 "uint8" (equal 10 11)
                         (c/let-ir 20 "object" (c/lit 0)
                           (c/let-ir 21 "uint8" (direct eq [(c/v 2) (c/v 20)])
                             ["case" (c/name-ir "Bool") {:idx 21} "uint8"
                              [["ctor" {:cidx 0} again]
                               ["ctor" {:cidx 1} ["dec" {:idx 1} 1 false false (c/ret 12)]]]]))))))
        ctx (prepare [inner outer eq sub loop-row]) engine (j/machine ctx) value (fresh ctx engine)]
    (try
      (j/retain! ctx engine value) (j/retain! ctx engine value)
      (is (= 1 (j/call ctx engine "outer" [value value])))
      (let [observed-word (word value)]
        (j/retain! ctx engine value)
        (is (= 1 (j/call ctx engine "loop" [value 1500])))
        (is (= observed-word (word value)))
        (is (= 1 (c/rc ctx value))))
      (finally (j/release! ctx engine value) (j/close! ctx engine)))))

(deftest observed-byte-array-kind-survives-fork-and-in-place-push
  (let [ctx (prepare (mapv #(get % "row") (byte/originals)))
        parent (j/machine ctx) source (j/source-binding ctx (Object.))
        [a] (j/install-graph! ctx parent
              (j/selected-owner-graph ctx source (Object.)
                [(j/graph-node ctx {:kind :byte-array :id 1 :rc 99 :bytes [1]})]
                [] [] [(j/graph-ref ctx 1)]))
        a (byte/push! ctx parent a 2)
        _ (is (= 1 (same ctx parent a a)))
        child (j/fork! ctx parent [a a]) engine (:engine child) [b alias] (:roots child)]
    (try
      (is (identical? b alias)) (is (= (word a) (word b)))
      (is (= 1 (same ctx engine b b)))
      (is (identical? a (byte/push! ctx parent a 3)))
      (is (identical? b (byte/push! ctx engine b 4)))
      (is (= [1 2 3] (byte/payload ctx a))) (is (= [1 2 4] (byte/payload ctx b)))
      (is (= (word a) (word b)))
      (finally (j/release! ctx parent a) (j/release! ctx engine b)
               (j/close! ctx parent) (j/close! ctx engine)))))

(defn check! [basis] (binding [*basis* basis] (run-tests 'java-ir-pointer-checks)))
