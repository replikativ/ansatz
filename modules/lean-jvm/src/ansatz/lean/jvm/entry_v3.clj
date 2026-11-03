(ns ansatz.lean.jvm.entry-v3
  "Private candidate-v3 correspondence checks only. No producer registration,
   source custody, runtime admission or public descriptor authority is issued."
  (:require [ansatz.lean.jvm.entry :as legacy]
            [ansatz.lean.jvm.installed :as installed]
            [ansatz.lean.jvm.type-graph :as graph]
            [ansatz.lean.jvm.used-products :as products]
            [ansatz.lean.jvm.representation :as representation]
            [clojure.data.json :as json])
  (:import [java.math BigInteger]
           [java.nio.charset StandardCharsets]))

(def ^:private object-lanes #{"object" "tobject" "tagged"})
(def ^:private scalar-lanes #{"uint8" "uint16" "uint32" "uint64" "usize" "float" "float32"})
(def ^:private ir-lanes (into (conj object-lanes "void" "erased") scalar-lanes))
(def ^:private top-keys
  #{"schema" "producer" "leanCommit" "leanVersion" "compiledModule" "runtimeProfile"
    "request" "moduleProducts" "typeGraph" "rootTypes" "representation" "runtimeWitnesses"
    "entries" "declarations" "importedModuleOrder" "initializerAttributeInventory"
    "initializerAttributeScope" "dynamicAPSites" "dynamicClosureProven" "initializationPlanScope" "guestKernelAdmission"})
(defn- need [ok reason]
  (when-not ok (throw (ex-info "Candidate v3 entry description rejected"
                              {:code "InvalidEntryV3" :reason reason}))))
(defn- exact! [m ks] (need (and (map? m) (= ks (set (keys m)))) :keys))
(defn- vector! [v n] (need (and (vector? v) (<= (count v) n)) :vector) v)
(defn- nat! [v n] (need (and (integer? v) (<= 0 v n)) :integer) v)
(defn- poll! [] (need (not (.isInterrupted (Thread/currentThread))) :cancelled))
(defn- sha! [x] (need (and (string? x) (boolean (re-matches #"[0-9a-f]{64}" x))) :digest))
(defn- name! [x]
  (try (#'legacy/name! x)
       (catch clojure.lang.ExceptionInfo _ (need false :name))))
(defn- module! [x] (#'products/module! x))
(defn- named [text] ["str" ["anonymous"] text])
(defn- string-bytes! [^String text maximum]
  ;; Bound JSON's escaped UTF-8 extent before allocating any encoded copy.
  (loop [i 0 bytes 2]
    (need (<= bytes maximum) :document-strings)
    (if (= i (.length text)) bytes
      (let [c (.charAt text i) code (int c)]
        (when (zero? (bit-and i 1023)) (poll!))
        (cond
          (Character/isHighSurrogate c)
          (do (need (and (< (inc i) (.length text))
                         (Character/isLowSurrogate (.charAt text (inc i)))) :utf16)
              (recur (+ i 2) (+ bytes 4)))
          (Character/isLowSurrogate c) (need false :utf16)
          (or (= code 34) (= code 92) (#{8 9 10 12 13} code)) (recur (inc i) (+ bytes 2))
          (< code 32) (recur (inc i) (+ bytes 6))
          (< code 128) (recur (inc i) (inc bytes))
          (< code 2048) (recur (inc i) (+ bytes 2))
          (#{8232 8233} code) (recur (inc i) (+ bytes 6))
          :else (recur (inc i) (+ bytes 3)))))))
(defn- data-bound! [document maximum]
  (loop [todo [[document 0]] visits 0 encoded 0]
    (poll!) (need (<= (+ visits (count todo)) 1000000) :document-work)
    (need (<= encoded maximum) :encoded-bound)
    (when (seq todo)
      (let [[x depth] (peek todo) tail (pop todo)]
        (need (< depth 256) :document-depth)
        (cond
          (map? x) (do (need (and (<= (count x) 32768) (every? string? (keys x))) :document-map)
                       (recur (into tail (map #(vector % (inc depth)) (mapcat identity x)))
                              (inc visits) (+ encoded 2 (count x) (max 0 (dec (count x))))))
          (vector? x) (do (need (<= (count x) 65536) :document-vector)
                          (recur (into tail (map #(vector % (inc depth)) x))
                                 (inc visits) (+ encoded 2 (max 0 (dec (count x))))))
          (string? x) (recur tail (inc visits) (+ encoded (string-bytes! x (- maximum encoded))))
          (#{Byte Short Integer Long BigInteger clojure.lang.BigInt} (class x))
          (let [n (if (= clojure.lang.BigInt (class x)) (.toBigInteger ^clojure.lang.BigInt x)
                      (if (= BigInteger (class x)) x (BigInteger/valueOf (long x))))]
            ;; Bound exact classes and magnitude BEFORE decimal stringification.
            ;; Charge each logical occurrence, even repeated references to one n.
            (need (and (= BigInteger (class n)) (<= (.bitLength ^BigInteger n) 4096)) :document-integer)
            (let [bits (.bitLength (.abs ^BigInteger n))
                  _ (need (<= bits 4096) :document-integer)
                  digits (max 1 (quot (+ (* bits 30103) 99999) 100000))
                  charge (+ digits (if (neg? (.signum ^BigInteger n)) 1 0))]
              (recur tail (inc visits) (+ encoded charge))))
          (nil? x) (recur tail (inc visits) (+ encoded 4))
          (instance? Boolean x) (recur tail (inc visits) (+ encoded (if x 4 5)))
          :else (need false :document-value)))))
  (need (<= (alength (.getBytes ^String (json/write-str document :escape-unicode false :escape-slash false)
                                  StandardCharsets/UTF_8)) maximum) :encoded-bound))
(defn- level! [x depth work]
  (poll!) (need (and (< depth 128) (<= (vswap! work inc) 100000)) :ast-bound)
  (vector! x 3)
  (let [value (case (first x)
                "zero" (do (need (= 1 (count x)) :level) 0)
                "succ" (do (need (= 2 (count x)) :level) (inc (level! (second x) (inc depth) work)))
                "max" (do (need (= 3 (count x)) :level) (max (level! (second x) (inc depth) work) (level! (nth x 2) (inc depth) work)))
                "imax" (do (need (= 3 (count x)) :level)
                            (let [a (level! (second x) (inc depth) work) b (level! (nth x 2) (inc depth) work)]
                              (if (zero? b) 0 (max a b))))
                (need false :open-level))]
    (nat! value 255)))
(defn- closed-type! [x depth work]
  (poll!) (need (and (< depth 256) (<= (vswap! work inc) 100000)) :ast-bound)
  (vector! x 5)
  (case (first x)
    "const" (do (need (= 3 (count x)) :native-type) (name! (second x))
                (vector! (nth x 2) 32) (doseq [u (nth x 2)] (level! u 0 work)))
    "app" (do (need (= 3 (count x)) :native-type)
              (closed-type! (second x) (inc depth) work) (closed-type! (nth x 2) (inc depth) work))
    ;; No bvars, let, lambda, projection or executable metadata in this bounded
    ;; closed signature profile. Native arbitrary DefEq is not reimplemented.
    (need false :open-or-unsupported-native-type)))
(defn- expected-type [signature roots]
  (let [payload (nth roots (get signature "result"))
        result (if (= "io" (get signature "effect")) ["app" ["const" (named "IO") []] payload] payload)]
    (reduce (fn [body i] ["forall" ["anonymous"] "default" (nth roots i) body])
            result (rseq (get signature "arguments")))))
(defn- actual-type! [actual work]
  ;; A closed AST claim is not a pure proof of native definitional equality.
  ;; Aliases and abbrevs can legitimately hide the whole expected function type.
  (loop [todo [[actual 0 0]]]
    (poll!)
    (when (seq todo)
      (let [[x binders depth] (peek todo) tail (pop todo)
            _ (need (and (< depth 256) (<= (vswap! work inc) 100000)) :ast-bound)
            _ (vector! x 128) child #(vector % binders (inc depth))
            next
            (case (first x)
              "const" (do (need (= 3 (count x)) :native-type) (name! (second x)) (vector! (nth x 2) 32)
                          (doseq [u (nth x 2)] (level! u 0 work)) tail)
              "bvar" (do (need (= 2 (count x)) :native-type) (nat! (second x) (dec binders)) tail)
              "sort" (do (need (= 2 (count x)) :native-type) (level! (second x) 0 work) tail)
              "app" (do (need (= 3 (count x)) :native-type) (conj tail (child (nth x 2)) (child (second x))))
              ("forall" "lam") (do (need (= 5 (count x)) :native-type) (name! (second x))
                                      (need (#{"default" "implicit" "strictImplicit" "instImplicit"} (nth x 2)) :native-binder)
                                      (conj tail [(nth x 4) (inc binders) (inc depth)] (child (nth x 3))))
              "let" (do (need (and (= 6 (count x)) (instance? Boolean (nth x 2))) :native-type) (name! (second x))
                        (conj tail [(nth x 5) (inc binders) (inc depth)] (child (nth x 4)) (child (nth x 3))))
              "proj" (do (need (= 4 (count x)) :native-type) (name! (second x)) (nat! (nth x 2) 1048576)
                         (conj tail (child (nth x 3))))
              ("nat" "string") (do (need (and (= 2 (count x)) (string? (second x))) :native-literal)
                                      (when (= "nat" (first x)) (need (and (<= (count (second x)) 1234)
                                                                                         (re-matches #"0|[1-9][0-9]*" (second x))) :native-literal)) tail)
              "mdata" (do (need (= 3 (count x)) :native-type) (vector! (second x) 128)
                          (doseq [entry (second x)]
                            (vector! entry 2) (need (= 2 (count entry)) :native-metadata) (name! (first entry))
                            (let [v (second entry)]
                              (vector! v 2) (need (= 2 (count v)) :native-metadata)
                              (case (first v)
                                "name" (name! (second v))
                                "bool" (need (instance? Boolean (second v)) :native-metadata)
                                "string" (need (string? (second v)) :native-metadata)
                                ("nat" "int") (need (and (string? (second v)) (<= (count (second v)) 1235)
                                                         (re-matches (if (= "nat" (first v)) #"0|[1-9][0-9]*" #"0|-?[1-9][0-9]*") (second v))) :native-metadata)
                                (need false :native-metadata))))
                          (conj tail (child (nth x 2))))
              (need false :open-or-unsupported-native-type))]
        (recur next)))))
(defn- signature! [signature count-roots]
  (exact! signature #{"arguments" "result" "effect"})
  (vector! (get signature "arguments") 64)
  (need (#{"pure" "io"} (get signature "effect")) :effect)
  (doseq [i (conj (get signature "arguments") (get signature "result"))] (nat! i (dec count-roots)))
  signature)
(defn- id! [x] (exact! x #{"idx"}) (nat! (get x "idx") Integer/MAX_VALUE))
(defn- params! [xs]
  (vector! xs 1024)
  (doseq [p xs]
    (exact! p #{"x" "ty" "borrow"}) (id! (get p "x"))
    (need (and (instance? Boolean (get p "borrow")) (ir-lanes (get p "ty"))) :parameter))
  (need (= (count xs) (count (set (map #(get % "x") xs)))) :duplicate-parameter))
(defn- abi! [abi]
  (exact! abi #{"name" "xs" "type"}) (name! (get abi "name")) (params! (get abi "xs"))
  (need (ir-lanes (get abi "type")) :ir-lane) abi)
(defn- declaration-abi [declaration]
  {"name" (get declaration "f") "xs" (get declaration "xs") "type" (get declaration "type")})
(defn- ctor! [c]
  (exact! c #{"name" "cidx" "size" "usize" "ssize"}) (name! (get c "name"))
  (doseq [k ["cidx" "size" "usize" "ssize"]] (nat! (get c k) 1048576)))
(defn- arg! [arg]
  (if (= "erased" arg) true
    (do (exact! arg #{"var"}) (exact! (get arg "var") #{"id"}) (id! (get-in arg ["var" "id"])))))
(defn- args! [args] (vector! args 4096) (doseq [arg args] (arg! arg)))
(defn- expression! [expr]
  (need (and (map? expr) (= 1 (count expr))) :ir-expression)
  (let [[op x] (first expr)]
    (case op
      ("fap" "pap") (do (exact! x #{"c" "ys"}) (name! (get x "c")) (args! (get x "ys")) {:dependencies [(get x "c")] :dynamic 0})
      "ap" (do (exact! x #{"x" "ys"}) (id! (get x "x")) (args! (get x "ys")) {:dependencies [] :dynamic 1})
      "ctor" (do (exact! x #{"i" "ys"}) (ctor! (get x "i")) (args! (get x "ys")) {})
      "reuse" (do (exact! x #{"x" "i" "updtHeader" "ys"}) (id! (get x "x")) (ctor! (get x "i"))
                  (need (instance? Boolean (get x "updtHeader")) :reuse) (args! (get x "ys")) {})
      "reset" (do (exact! x #{"n" "x"}) (nat! (get x "n") 1048576) (id! (get x "x")) {})
      ("proj" "uproj") (do (exact! x #{"i" "x"}) (nat! (get x "i") 1048576) (id! (get x "x")) {})
      "sproj" (do (exact! x #{"n" "offset" "x"}) (nat! (get x "n") 1048576) (nat! (get x "offset") 1048576) (id! (get x "x")) {})
      "box" (do (exact! x #{"ty" "x"}) (need (ir-lanes (get x "ty")) :ir-lane) (id! (get x "x")) {})
      ("unbox" "isShared") (do (exact! x #{"x"}) (id! (get x "x")) {})
      "lit" (do (exact! x #{"v"})
                (let [v (get x "v")]
                  (need (and (map? v) (= 1 (count v))) :ir-literal)
                  (let [[kind payload] (first v) _ (exact! payload #{"v"}) value (get payload "v")]
                    ;; Pinned deriving ToJson IR.LitVal and existing Interpreter
                    ;; parser both encode num/str as a constructor payload {v:...}.
                    (case kind "num" (need (and (integer? value) (not (neg? value))) :ir-literal)
                               "str" (need (string? value) :ir-literal) (need false :ir-literal)))) {})
      (need false :ir-expression))))
(defn- body! [root]
  (loop [todo [[root 0]] visits 0 dependencies [] dynamic 0]
    (poll!) (need (<= (+ visits (count todo)) 100000) :ir-work)
    (if (empty? todo) {:dependencies dependencies :dynamic dynamic}
      (let [[body depth] (peek todo) tail (pop todo) _ (need (< depth 512) :ir-depth)
            _ (vector! body 7) op (first body) child #(vector % (inc depth))
            result
            (case op
              "vdecl" (do (need (= 5 (count body)) :ir-body) (id! (nth body 1)) (need (ir-lanes (nth body 2)) :ir-lane)
                          (let [expr (expression! (nth body 3))]
                            {:todo (conj tail (child (nth body 4))) :deps (:dependencies expr []) :dynamic (:dynamic expr 0)}))
              "jdecl" (do (need (= 5 (count body)) :ir-body) (id! (nth body 1)) (params! (nth body 2))
                          {:todo (conj tail (child (nth body 4)) (child (nth body 3)))})
              ("set" "uset") (do (need (= 5 (count body)) :ir-body) (id! (nth body 1)) (nat! (nth body 2) 1048576)
                                 (if (= op "set") (arg! (nth body 3)) (id! (nth body 3))) {:todo (conj tail (child (nth body 4)))})
              "setTag" (do (need (= 4 (count body)) :ir-body) (id! (nth body 1)) (nat! (nth body 2) 1048576) {:todo (conj tail (child (nth body 3)))})
              "sset" (do (need (= 7 (count body)) :ir-body) (id! (nth body 1))
                         (doseq [i [2 3]] (nat! (nth body i) 1048576)) (id! (nth body 4)) (need (ir-lanes (nth body 5)) :ir-lane)
                         {:todo (conj tail (child (nth body 6)))})
              ("inc" "dec") (do (need (= 6 (count body)) :ir-body) (id! (nth body 1)) (nat! (nth body 2) 1048576)
                                 (need (every? #(instance? Boolean %) [(nth body 3) (nth body 4)]) :ir-body)
                                 {:todo (conj tail (child (nth body 5)))})
              "del" (do (need (= 3 (count body)) :ir-body) (id! (nth body 1)) {:todo (conj tail (child (nth body 2)))})
              "case" (do (need (= 5 (count body)) :ir-body) (name! (nth body 1)) (id! (nth body 2)) (need (ir-lanes (nth body 3)) :ir-lane)
                         (vector! (nth body 4) 1024)
                         {:todo (into tail (reverse (map (fn [alt]
                                                        (vector! alt 3)
                                                        (case (first alt)
                                                          "ctor" (do (need (= 3 (count alt)) :ir-alt) (ctor! (second alt)) (child (nth alt 2)))
                                                          "default" (do (need (= 2 (count alt)) :ir-alt) (child (second alt)))
                                                          (need false :ir-alt))) (nth body 4))))})
              "ret" (do (need (= 2 (count body)) :ir-body) (arg! (second body)) {:todo tail})
              "jmp" (do (need (= 3 (count body)) :ir-body) (id! (second body)) (args! (nth body 2)) {:todo tail})
              "unreachable" (do (need (= 1 (count body)) :ir-body) {:todo tail})
              (need false :ir-body))]
        (recur (:todo result) (inc visits) (into dependencies (:deps result [])) (+ dynamic (:dynamic result 0)))))))
(defn- extern! [ext]
  (exact! ext #{"entries"}) (vector! (get ext "entries") 16)
  (doseq [entry (get ext "entries")]
    (if (= entry "opaque") true
      (do (need (and (map? entry) (= 1 (count entry))) :extern-entry)
          (let [[kind body] (first entry)]
            (case kind
              "standard" (do (exact! body #{"backend" "fn"}) (name! (get body "backend")) (need (string? (get body "fn")) :extern-entry))
              "inline" (do (exact! body #{"backend" "pattern"}) (name! (get body "backend")) (need (string? (get body "pattern")) :extern-entry))
              "adhoc" (do (exact! body #{"backend"}) (name! (get body "backend")))
              (need false :extern-entry)))))))
(defn- rows! [rows imported allowed?]
  (vector! rows 2048) (need (seq rows) :declarations)
  (let [index (into {} (map #(vector (get % "name") %) rows))]
    (need (= (count rows) (count index)) :duplicate-declaration)
    (let [dynamic
          (reduce
           (fn [total row]
             (poll!)
             (exact! row #{"kind" "name" "ir" "dependencies" "redirect" "sourceLocal" "sourceModule" "runtime"})
             (need (and (= "decl" (get row "kind")) (false? (get row "sourceLocal"))) :declaration-profile)
             (name! (get row "name")) (module! (get row "sourceModule"))
             (need (and (contains? imported (get row "sourceModule")) (allowed? (get row "sourceModule"))) :declaration-owner)
             (let [ir (get row "ir") runtime (get row "runtime") redirect (get row "redirect")
                   _ (need (and (map? ir) (= 1 (count ir))) :declaration-ir)
                   fdecl (get ir "fdecl") extern (get ir "extern") declaration (or fdecl extern)
                   _ (need declaration :declaration-ir)
                   _ (exact! declaration (if fdecl #{"f" "xs" "type" "body" "info"} #{"f" "xs" "type" "ext"}))
                   abi (abi! (declaration-abi declaration))
                   _ (need (= (get row "name") (get abi "name")) :declaration-identity)
                   _ (exact! runtime #{"role" "initializer" "initializationAction"})
                   initializer (get runtime "initializer") action (get runtime "initializationAction")
                   _ (need (and (#{"ordinary" "value" "closed" "ground" "initialized"} (get runtime "role"))
                                (contains? #{nil "io" "builtin-io"} action)
                                (= (some? initializer) (= "initialized" (get runtime "role")))) :declaration-runtime)
                   _ (when (some? initializer) (name! initializer))
                   _ (need (or (nil? redirect) (map? redirect)) :redirect)
                   _ (when redirect
                       (exact! redirect #{"name" "params" "type"}) (name! (get redirect "name")) (params! (get redirect "params"))
                       (need (ir-lanes (get redirect "type")) :redirect)
                       (let [target (get-in index [(get redirect "name") "ir" "fdecl"])]
                         (need (= {"name" (get redirect "name") "xs" (get redirect "params") "type" (get redirect "type")}
                                  (declaration-abi target)) :redirect-target)))
                   result (if fdecl
                            (do (exact! (get fdecl "info") #{}) (body! (get fdecl "body")))
                            (do (extern! (get extern "ext")) {:dependencies [] :dynamic 0}))
                   expected (cond-> (vec (:dependencies result)) initializer (conj initializer) redirect (conj (get redirect "name")))]
               (vector! (get row "dependencies") 16384)
               (need (= expected (get row "dependencies")) :declaration-dependencies)
               (doseq [dependency expected] (name! dependency) (need (contains? index dependency) :missing-dependency))
               (+ total (:dynamic result)))) 0 rows)]
      {:index index :dynamic dynamic})))
(defn- inventory! [modules inventory]
  (vector! inventory 4096)
  (need (= modules (mapv #(get % "module") inventory)) :initializer-module-order)
  (let [total (volatile! 0)]
    (doseq [row inventory]
      (exact! row #{"module" "regularModuleEntries" "regularIREntries" "builtinModuleEntries" "builtinIREntries"})
      (doseq [key ["regularModuleEntries" "regularIREntries" "builtinModuleEntries" "builtinIREntries"]
              :let [entries (vector! (get row key) 16384)] pair entries]
        (need (<= (vswap! total inc) 16384) :initializer-count)
        (vector! pair 2) (need (= 2 (count pair)) :initializer-pair)
        (doseq [name pair] (name! name)))))
  inventory)
(defn- entry! [entry roots root-irs index local-modules imported work binding-profile?]
  (exact! entry (cond-> #{"name" "kind" "levelParams" "compiledModule" "actualType" "typeCheck" "semanticArity"
                         "runtimeArity" "argumentPlan" "resultABI" "raw" "callable" "selection"}
                 binding-profile? (conj "hostBinding")))
  (name! (get entry "name")) (module! (get entry "compiledModule"))
  (need (and (#{"definition" "opaque"} (get entry "kind")) (= [] (get entry "levelParams"))
             (contains? local-modules (get entry "compiledModule")) (contains? imported (get entry "compiledModule"))) :entry-origin)
  (let [check (get entry "typeCheck") _ (exact! check #{"algorithm" "transparency" "signature" "expectedType"})
        signature (signature! (get check "signature") (count roots))
        arguments (get signature "arguments") result (get signature "result") io? (= "io" (get signature "effect"))
        arity (count arguments) runtime (+ arity (if io? 1 0))
        raw (abi! (get entry "raw")) callable (abi! (get entry "callable"))
        boxed? (= "original-interpreter-boxed-lookup" (get entry "selection"))
        result-abi (get entry "resultABI") scalar? (= "raw-nullary-scalar" (get result-abi "kind"))
        boxed-lane #(case % ("object" "float" "float32") "object" ("void" "tagged" "uint8" "uint16") "tagged" "tobject")]
    (when binding-profile?
      (let [binding (get entry "hostBinding")]
        (need (#{"none" "reference" "foreign"} binding) :host-binding-kind)
        (when (= "reference" binding)
          (need (= "definition" (get entry "kind")) :host-binding-reference))
        (when (= "foreign" binding)
          (need (= "opaque" (get entry "kind")) :host-binding-foreign))))
    (need (and (= "Lean.Meta.isDefEq" (get check "algorithm")) (= "default" (get check "transparency"))
               (= (expected-type signature roots) (get check "expectedType"))) :expected-type)
    (actual-type! (get entry "actualType") work)
    (need (and (= arity (get entry "semanticArity")) (= runtime (get entry "runtimeArity"))
               (= runtime (count (get raw "xs")) (count (get callable "xs")))
               (= (get entry "name") (get raw "name"))
               (#{"original-interpreter-boxed-lookup" "original-owned-raw"} (get entry "selection"))
               (if boxed? (seq (get raw "xs")) (= raw callable))
               (every? #(and (false? (get % "borrow")) (object-lanes (get % "ty"))) (get callable "xs"))) :owned-callable)
    (when boxed?
      (need (and (= (mapv #(boxed-lane (get % "ty")) (get raw "xs")) (mapv #(get % "ty") (get callable "xs")))
                 (= (boxed-lane (get raw "type")) (get callable "type"))) :boxed-abi-correspondence))
    (need (= (cond-> (mapv #(hash-map "kind" "argument" "index" %) (range arity))
               io? (conj {"kind" "io-world" "representation" "canonical-erased-zero"}))
             (get entry "argumentPlan")) :argument-plan)
    (need (= (mapv #(nth root-irs %) arguments) (mapv #(get % "ty") (take arity (get raw "xs")))) :raw-argument-lowering)
    (if io?
      (need (and (= "void" (get-in raw ["xs" arity "ty"])) (= "tagged" (get-in callable ["xs" arity "ty"]))
                 (= "object" (get raw "type") (get callable "type")) (not scalar?)) :io-world-abi)
      (need (= (nth root-irs result) (get raw "type")) :raw-result-lowering))
    (if scalar?
      (do (exact! result-abi #{"kind" "lane" "resultRoot"})
          (need (and (not io?) (zero? arity) (not boxed?) (= raw callable)
                     (= result (get result-abi "resultRoot")) (scalar-lanes (get result-abi "lane"))
                     (= (nth root-irs result) (get result-abi "lane") (get callable "type"))) :raw-result-abi))
      (do (exact! result-abi #{"kind"})
          (need (and (= "boxed-object-lane" (get result-abi "kind")) (object-lanes (get callable "type"))) :boxed-result-abi)))
    (doseq [role ["raw" "callable"]]
      (let [abi (get entry role) row (get index (get abi "name"))
            external (get-in row ["ir" "extern"])
            declaration (or (get-in row ["ir" "fdecl"]) external)
            foreign? (and binding-profile? (= "foreign" (get entry "hostBinding")))
            raw? (= role "raw")]
        (need (and declaration (= abi (declaration-abi declaration))
                   (= (boolean external) (and foreign? (or raw? (not boxed?))))
                   (= (get entry "compiledModule") (get row "sourceModule"))
                   (nil? (get row "redirect")) (nil? (get-in row ["runtime" "initializer"]))
                   (nil? (get-in row ["runtime" "initializationAction"]))) :original-returned-declaration)
        (when external
          (let [externs (get-in external ["ext" "entries"]) standard (get-in externs [0 "standard"])]
            (need (and (= 1 (count externs)) (= #{"standard"} (set (keys (first externs))))
                       (#{["str" ["anonymous"] "all"] ["str" ["anonymous"] "c"]} (get standard "backend"))
                       (string? (get standard "fn")) (re-matches #"ansatz_jvm_[A-Za-z0-9_]+" (get standard "fn")))
                  :host-binding-extern)))))
    entry))
(defn validate-document!
  "Return bounded checked-description-only data. Native Meta DefEq/safety claims
   require future authenticated producer+source/IR+product custody; this pure
   function never proves DefEq, selects a cohort or issues runtime authority."
  [context document]
  (exact! context #{:root :request :module-products :local-modules :installed-imports})
  (data-bound! document (* 16 1048576))
  (exact! document top-keys)
  (let [{:keys [root request module-products local-modules installed-imports]} context
        version (case (get document "schema") "lean-native-entry-evidence/3" 3 "lean-native-entry-evidence/4" 4 nil)
        _ (module! root) _ (exact! request #{"schema" "module" "entries" "moduleProductsSHA256"})
        _ (data-bound! request 65536)
        _ (need (and version (= (str "lean-native-entry-requests/" version) (get request "schema"))) :request-schema)
        _ (sha! (get request "moduleProductsSHA256"))
        requested (vector! (get request "entries") legacy/max-selected-entries)
        entries (vector! (get document "entries") legacy/max-selected-entries)
        _ (need (and (seq requested) (= (count requested) (count entries))
                     (= (count requested) (count (set (map #(get % "name") requested))))) :selected-entries)
        _ (doseq [selection requested] (exact! selection #{"name"}) (name! (get selection "name")))
        _ (need (and version
                     (= "NativeNominalEntryEvidence.exportEntries" (get document "producer"))
                     (= "819816b2e0a3bf405af45ae5c7af2491d8f5bee6" (get document "leanCommit"))
                     (= "4.33.1" (get document "leanVersion"))
                     (= {"wordBits" 64 "target" "x86_64-unknown-linux-gnu"} (get document "runtimeProfile"))
                     (= root (get request "module") (get document "compiledModule"))
                     (= request (get document "request")) (= module-products (get document "moduleProducts"))
                     (false? (get document "dynamicClosureProven")) (false? (get document "guestKernelAdmission"))
                     (= "external-source-phase-capture-required" (get document "initializationPlanScope"))
                     (= "actual-imported-module-and-IR-entries-not-execution" (get document "initializerAttributeScope"))) :document-profile)
        _ (need (= (products/digest module-products) (get request "moduleProductsSHA256")) :module-products-digest)
        g (graph/validate! (get document "typeGraph"))
        required (vec (distinct (map #(get-in % ["origin" "module"]) (get g "definitions"))))
        _ (products/authorize! module-products required local-modules installed-imports)
        _ (products/bind-graph! module-products g)
        locals (set local-modules) declared (set installed-imports)
        allowed? #(or (locals %) (declared %) (installed/init? %))
        _ (need (locals root) :root-module-authorization)
        modules (vector! (get document "importedModuleOrder") 4096)
        _ (need (and (seq modules) (= (count modules) (count (set modules)))) :imported-modules)
        _ (doseq [module modules] (module! module) (need (allowed? module) :imported-module-authorization))
        imported (set modules) _ (need (contains? imported root) :root-module-import)
        _ (inventory! modules (get document "initializerAttributeInventory"))
        _ (doseq [module required] (need (contains? imported module) :origin-module-import))
        roots (vector! (get document "rootTypes") 1024)
        _ (need (= (count roots) (count (get g "roots"))) :root-catalog)
        signatures (mapv #(signature! (get-in % ["typeCheck" "signature"]) (count roots)) entries)
        used (set (mapcat #(conj (get % "arguments") (get % "result")) signatures))
        _ (need (= used (set (range (count roots)))) :root-usage)
        io? (boolean (some #(= "io" (get % "effect")) signatures))
        normalized (representation/normalize-entry-types! document io?)
        rows-by-id (into {} (map #(vector (get % "id") %) (get-in normalized [:normalized "plans"])))
        root-irs (mapv #(get-in rows-by-id [% "closedIR"]) (get-in normalized [:normalized "roots"]))
        _ (need (= (count roots) (count root-irs)) :normalized-root-catalog)
        rows (rows! (get document "declarations") imported allowed?)
        _ (nat! (get document "dynamicAPSites") 1000000)
        _ (need (= (:dynamic rows) (get document "dynamicAPSites")) :dynamic-site-count)
        _ (need (= (mapv #(get % "name") requested) (mapv #(get % "name") entries)) :entry-request-order)
        work (volatile! 0)
        _ (doseq [type roots] (closed-type! type 0 work))
        checked (mapv #(entry! % roots root-irs (:index rows) locals imported work (= version 4)) entries)
        start (vec (mapcat #(map (fn [role] (get-in % [role "name"])) ["raw" "callable"]) checked))
        reachable (loop [todo start seen #{}]
                    (if (empty? todo) seen
                      (let [name (peek todo) tail (pop todo)]
                        (if (seen name) (recur tail seen)
                          (do (need (contains? (:index rows) name) :missing-dependency)
                              (recur (into tail (get-in rows [:index name "dependencies"])) (conj seen name)))))))]
    (need (= reachable (set (keys (:index rows)))) :declaration-closure)
    {:scope :checked-description-only :authority :none
     :native-defeq-requires-authenticated-producer true :source-reconciliation :required
     :entries checked :type-graph g :root-types roots :storage normalized
     :declarations (:index rows) :module-products module-products :io? io?}))


(defn- canonical-custody [x]
  (cond (map? x) (into (sorted-map) (map (fn [[k v]] [k (canonical-custody v)])) x)
        (vector? x) (mapv canonical-custody x) :else x))
(defn- custody-data-bound! [document maximum]
  ;; Build receipts contain measured finite decimal elapsed times. This separate
  ;; grammar cannot admit decimals into entry signatures, IR or layout evidence.
  (loop [todo [[document 0]] visits 0 encoded 0]
    (poll!)
    (need (and (<= (+ visits (count todo)) 1000000) (<= encoded maximum)) :custody-bound)
    (when (seq todo)
      (let [[x depth] (peek todo) tail (pop todo)]
        (need (< depth 256) :custody-depth)
        (cond
          (map? x) (do (need (and (<= (count x) 32768) (every? string? (keys x))) :custody-map)
                       (recur (into tail (map #(vector % (inc depth)) (mapcat identity x)))
                              (inc visits) (+ encoded 2 (count x) (max 0 (dec (count x))))))
          (vector? x) (do (need (<= (count x) 65536) :custody-vector)
                          (recur (into tail (map #(vector % (inc depth)) x))
                                 (inc visits) (+ encoded 2 (max 0 (dec (count x))))))
          (string? x) (recur tail (inc visits) (+ encoded (string-bytes! x (- maximum encoded))))
          (= Double (class x))
          (do (need (Double/isFinite (double x)) :custody-number)
              (recur tail (inc visits) (+ encoded (count (Double/toString x)))))
          :else
          (do
            ;; Reuse the exact bounded scalar grammar for integers/booleans/null;
            ;; custom Numbers, ratios and arbitrary objects remain refused.
            (need (not (or (coll? x) (string? x))) :custody-value)
            (data-bound! x 2048)
            (recur tail (inc visits) (+ encoded (count (json/write-str x)))))))))
  document)
(defn- custody-sha [x newline?]
  (let [text (str (json/write-str (canonical-custody x) :escape-unicode false :escape-slash false)
                  (when newline? "\n"))]
    (apply str (map #(format "%02x" (bit-and 255 %))
                    (.digest (java.security.MessageDigest/getInstance "SHA-256")
                             (.getBytes text StandardCharsets/UTF_8))))))
(defn validate-producer-custody!
  "Pure independently pinned source-closure/build-receipt correspondence. Never
   discovers native files or issues a build/artifact/runtime capability."
  [custody helper-source helper]
  (exact! custody #{:source-closure :source-closure-sha256 :build-receipt :build-receipt-sha256})
  (custody-data-bound! {"closure" (:source-closure custody) "receipt" (:build-receipt custody)} (* 2 1048576))
  (let [version (legacy/schema-for-pins! (get helper-source "sha256") (get helper "sha256"))
        cohort (when (legacy/nominal-schema? version) (get legacy/cohorts version))
        rows (:source-closure custody) receipt (:build-receipt custody)]
    (need (and cohort (= (:source cohort) (get helper-source "sha256"))
               (= (:binary cohort) (get helper "sha256"))
               (= (:source-closure cohort) (:source-closure-sha256 custody))
               (= (:build-receipt cohort) (:build-receipt-sha256 custody))) :producer-custody-pins)
    (need (and (= (:source-closure-sha256 custody) (custody-sha rows false))
               (= (:build-receipt-sha256 custody) (custody-sha receipt true))) :producer-custody-digest)
    (need (and (= "lean-native-entry-candidate/1" (get receipt "schema"))
               (= "entry-built-not-published" (get receipt "status"))
               (= "819816b2e0a3bf405af45ae5c7af2491d8f5bee6" (get receipt "leanCommit"))
               (= rows (get receipt "sourceClosure"))
               (= (:source-closure-sha256 custody) (get receipt "sourceClosureSHA256"))
               (= [(assoc helper "path" "entry")]
                  (filterv #(= "entry" (get % "path")) (get receipt "products")))) :producer-custody-receipt)
    custody))
