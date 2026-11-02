(ns ansatz.lean.jvm.representation
  "Private observation→storage-program checks. No native/source authentication,
   public descriptor issuance, entry admission, or legacy behavior changes."
  (:require [ansatz.lean.jvm.type-graph :as graph]
            [clojure.data.json :as json])
  (:import [java.math BigInteger] [clojure.lang BigInt]))

(def ^:private lanes #{"object" "tobject" "tagged" "uint8" "uint16" "uint32" "uint64" "usize" "float" "float32"})
(def ^:private scalar-width {"uint8" 1 "uint16" 2 "uint32" 4 "uint64" 8 "usize" 8 "float" 8 "float32" 4})
(def ^:private special-kinds #{"machine-int" "word" "float" "bool" "char" "unit" "array" "bytes"})
(def ^:private builtin-names {"list" "List" "option" "Option" "product" "Prod" "sum" "Sum" "except" "Except" "array" "Array"})
(defn- fail [reason] (throw (ex-info (str "Invalid native representation: " (name reason)) {:code "InvalidRepresentation" :reason reason})))
(defn- need [ok reason] (when-not ok (fail reason)))
(defn- poll! [] (when (.isInterrupted (Thread/currentThread)) (fail :cancelled)))
(defn- keys! [m expected] (need (and (map? m) (= expected (set (keys m)))) :keys))
(defn- vector! [v n] (need (and (vector? v) (<= (count v) n)) :vector))
(defn- nat! [x n] (need (and (integer? x) (<= 0 x n)) :integer))
(defn- lane! [x] (need (contains? lanes x) :lane))
(defn- metadata-integer! [value]
  ;; Native JSON numeric metadata are natural machine values, never arbitrary
  ;; mathematical payloads. Check exact classes and magnitude before decimal
  ;; encoding, allocation via abs, or invoking a BigInteger subclass method.
  (let [type (class value)]
    (cond
      (#{Byte Short Integer Long} type) (need (not (neg? (long value))) :metadata-integer)
      (or (= BigInteger type) (= BigInt type))
      (let [n (if (= BigInt type) (.toBigInteger ^BigInt value) value)]
        (need (= BigInteger (class n)) :metadata-integer)
        (need (and (not (neg? (.signum ^BigInteger n))) (<= (.bitLength ^BigInteger n) 64)) :metadata-integer))
      :else (fail :metadata-integer))))
(defn- data-bound! [x maximum]
  (loop [todo [[x 0]] visits 0 units 0]
    (poll!) (need (<= (+ visits (count todo)) 200000) :document-work)
    (when (seq todo)
      (let [[v depth] (peek todo) tail (pop todo)]
        (need (< depth 128) :document-depth)
        (cond
          (map? v) (do (need (<= (count v) 8192) :document-map) (need (every? string? (keys v)) :document-key)
                       (recur (into tail (map #(vector % (inc depth)) (mapcat identity v))) (inc visits) units))
          (vector? v) (do (need (<= (count v) 32768) :document-vector) (recur (into tail (map #(vector % (inc depth)) v)) (inc visits) units))
          (string? v) (let [next-units (+ units (count v))]
                        (need (and (<= (count v) 65536) (<= next-units maximum)) :document-strings)
                        (loop [i 0]
                          (when (< i (count v))
                            (let [c (.charAt ^String v i)]
                              (if (Character/isHighSurrogate c)
                                (do (need (and (< (inc i) (count v)) (Character/isLowSurrogate (.charAt ^String v (inc i)))) :utf16)
                                    (recur (+ i 2)))
                                (do (need (not (Character/isLowSurrogate c)) :utf16) (recur (inc i)))))))
                        (recur tail (inc visits) next-units))
          (integer? v) (do (metadata-integer! v) (recur tail (inc visits) units))
          (or (nil? v) (instance? Boolean v)) (recur tail (inc visits) units)
          :else (fail :document-value))))))
(defn- encoded! [x n]
  (data-bound! x n)
  (need (<= (alength (.getBytes ^String (json/write-str x :escape-unicode false :escape-slash false) "UTF-8")) n) :encoded-bound))
(defn- name! [x]
  (loop [x x depth 0]
    (poll!) (need (< depth 64) :name-depth) (vector! x 3)
    (if (= ["anonymous"] x) true
      (do (need (and (= 3 (count x)) (#{"str" "num"} (first x)) (string? (nth x 2)) (<= (count (nth x 2)) 1024)) :name)
          (when (= "num" (first x))
            (need (and (re-matches #"0|[1-9][0-9]*" (nth x 2)) (<= (count (nth x 2)) 20)
                       (<= (bigint (nth x 2)) 18446744073709551615N)) :name-number))
          (recur (nth x 1) (inc depth))))))
(defn- level! [x depth work]
  (poll!) (need (and (< depth 64) (<= (vswap! work inc) 32768)) :ast-bound) (vector! x 3)
  (let [n (case (first x)
            "zero" (do (need (= 1 (count x)) :level) 0)
            "succ" (do (need (= 2 (count x)) :level) (inc (level! (second x) (inc depth) work)))
            "max" (do (need (= 3 (count x)) :level) (max (level! (second x) (inc depth) work) (level! (nth x 2) (inc depth) work)))
            "imax" (do (need (= 3 (count x)) :level) (let [a (level! (second x) (inc depth) work) b (level! (nth x 2) (inc depth) work)] (if (zero? b) 0 (max a b))))
            (fail :level))] (nat! n 255) n))
(defn- native! [x depth work]
  (poll!) (need (and (< depth 128) (<= (vswap! work inc) 32768)) :ast-bound) (vector! x 3)
  (case (first x)
    "const" (do (need (= 3 (count x)) :native-type) (name! (second x)) (vector! (nth x 2) 32)
                (doseq [u (nth x 2)] (level! u 0 work)))
    "app" (do (need (= 3 (count x)) :native-type) (native! (second x) (inc depth) work) (native! (nth x 2) (inc depth) work))
    (fail :open-or-unsupported-native-type)))
(defn- spine [expr]
  (loop [e expr args []]
    (if (= "app" (first e)) (recur (second e) (conj args (nth e 2))) [e (vec (rseq args))])))
(defn- primitive [t]
  (case (get t "kind")
    "nat" "Nat" "int" "Int" "string" "String" "bool" "Bool" "char" "Char" "unit" "Unit" "bytes" "ByteArray"
    "machine-int" (str (if (get t "signed") "Int" "UInt") (get t "bits"))
    "word" (if (get t "signed") "ISize" "USize")
    "float" (if (= 32 (get t "bits")) "Float32" "Float") nil))
(defn- children [t]
  (case (get t "kind") ("list" "option" "array") [(get t "element")]
    "product" [(get t "first") (get t "second")] "sum" [(get t "left") (get t "right")]
    "except" [(get t "error") (get t "value")] []))
(defn- def-types [d]
  (into (vec (get d "arguments")) (for [c (get d "constructors") f (get c "fields")] (get f "type"))))
(defn- matches! [defs t expr work]
  (native! expr 0 work)
  (let [[head args] (spine expr) kind (get t "kind") d (when (= "nominal" kind) (get defs (get t "id")))
        expected-name (if d (get d "name") ["str" ["anonymous"] (or (primitive t) (get builtin-names kind))])
        expected-args (if d (get d "arguments") (children t))
        expected-levels (when d (get d "universes"))]
    (need (and (= "const" (first head)) (= expected-name (second head)) (= (count args) (count expected-args))) :native-logical-correspondence)
    (if d (need (= expected-levels (mapv #(level! % 0 work) (nth head 2))) :native-universes)
      (need (= (count (nth head 2)) (if (primitive t) 0 (if (#{"product" "sum" "except"} kind) 2 1))) :native-universe-arity))
    (doseq [[ct ce] (map vector expected-args args)] (matches! defs ct ce work))))
(defn- defeq! [check defs type work]
  (keys! check #{"algorithm" "transparency" "actualType" "expectedType"})
  (need (and (= "Lean.Meta.isDefEq" (get check "algorithm")) (= "default" (get check "transparency"))) :native-defeq)
  (native! (get check "actualType") 0 work)
  (matches! defs type (get check "expectedType") work))
(defn- unique-index [rows k]
  (let [out (into {} (map #(vector (get % k) %) rows))] (need (= (count rows) (count out)) :duplicate-row) out))
(defn- family! [family]
  (keys! family #{"typeName" "irType" "trivialStructure" "constructors"}) (name! (get family "typeName")) (lane! (get family "irType"))
  (vector! (get family "constructors") 1024) (need (seq (get family "constructors")) :empty-family)
  (doseq [[ci c] (map-indexed vector (get family "constructors"))]
    (keys! c #{"constructor" "ctorInfo" "fields"}) (name! (get c "constructor"))
    (let [info (get c "ctorInfo") fields (get c "fields")]
      (keys! info #{"name" "cidx" "size" "usize" "ssize"})
      (need (and (= (get c "constructor") (get info "name")) (= ci (get info "cidx"))) :constructor-identity)
      (doseq [[k limit] [["size" 64] ["usize" 64] ["ssize" 1024]]] (nat! (get info k) limit))
      (vector! fields 64)
      (let [oi (volatile! 0) ui (volatile! (get info "size"))]
        (doseq [f fields]
          (case (get f "kind")
            "object" (do (keys! f #{"kind" "index" "irType"}) (need (#{"object" "tobject" "tagged"} (get f "irType")) :object-lane)
                         (need (= @oi (get f "index")) :object-slot-order) (vswap! oi inc))
            "usize" (do (keys! f #{"kind" "index"}) (need (= @ui (get f "index")) :usize-slot-order) (vswap! ui inc))
            "scalar" (do (keys! f #{"kind" "bytes" "offset" "irType"})
                         (need (and (contains? scalar-width (get f "irType")) (not= "usize" (get f "irType")) (= (get f "bytes") (get scalar-width (get f "irType")))) :scalar-width)
                         (nat! (get f "offset") 1024))
            ("erased" "void") (keys! f #{"kind"}) (fail :field-kind)))
        (need (and (= @oi (get info "size")) (= @ui (+ (get info "size") (get info "usize")))) :layout-counts))
      (let [offset (volatile! 0)]
        (doseq [width [8 4 2 1] f fields :when (and (= "scalar" (get f "kind")) (= width (get f "bytes")))]
          (need (= @offset (get f "offset")) :grouped-scalar-offset) (vswap! offset + width))
        (need (= @offset (get info "ssize")) :scalar-extent))))
  (let [cs (get family "constructors") empty-count (count (filter #(every? zero? (map (get % "ctorInfo") ["size" "usize" "ssize"])) cs))
        expected (cond (= empty-count (count cs)) (cond (= 1 (count cs)) "tagged" (< (count cs) 256) "uint8" :else "uint16")
                       (zero? empty-count) "object" :else "tobject")]
    (need (= expected (get family "irType")) :generic-family-lowering))
  (need (or (nil? (get family "trivialStructure")) (map? (get family "trivialStructure"))) :trivial-structure)
  (when-let [trivial (get family "trivialStructure")]
    (keys! trivial #{"constructor" "fieldIndex" "numParams"}) (nat! (get trivial "numParams") 64)
    (need (= 1 (count (get family "constructors"))) :trivial-family)
    (let [c (first (get family "constructors")) fields (get c "fields") selected (get trivial "fieldIndex")]
      (nat! selected 63) (need (and (= (get trivial "constructor") (get c "constructor")) (< selected (count fields))
                                   (= [selected] (vec (keep-indexed #(when-not (#{"erased" "void"} (get %2 "kind")) %1) fields)))) :trivial-selection)))
  family)
(defn- type-closure [defs roots]
  (loop [todo (vec (reverse roots)) types [] seen #{} ids []]
    (poll!) (need (<= (+ (count todo) (count types)) 16384) :closure-work)
    (if (empty? todo) {:types types :ids ids}
      (let [t (peek todo) tail (pop todo)]
        (if (seen t) (recur tail types seen ids)
          (let [nominal? (= "nominal" (get t "kind")) id (get t "id")
                cs (if nominal? (def-types (get defs id)) (children t))]
            (recur (into tail (reverse cs)) (conj types t) (conj seen t) (if nominal? (conj ids id) ids))))))))
(defn- rewrite-type [ids t]
  (if (= "nominal" (get t "kind")) (assoc t "id" (get ids (get t "id")))
    (case (get t "kind") ("list" "option" "array") (update t "element" #(rewrite-type ids %))
      "product" (-> t (update "first" #(rewrite-type ids %)) (update "second" #(rewrite-type ids %)))
      "sum" (-> t (update "left" #(rewrite-type ids %)) (update "right" #(rewrite-type ids %)))
      "except" (-> t (update "error" #(rewrite-type ids %)) (update "value" #(rewrite-type ids %))) t)))

(defn normalize-observation!
  "Prepare one strict private typed-storage program; this issues no source authority.
   Explicit root subsets are for bounded observation work, never silent fallback."
  ([observation] (normalize-observation! observation {:roots (vec (range (count (get-in observation ["typeGraph" "roots"])))) :runtime-witnesses nil :io? false}))
  ([observation options]
   (poll!) (keys! observation #{"schema" "scope" "typeGraph" "rootTypeChecks" "representation"})
   (need (and (= "lean-jvm-private-nominal-observations/1" (get observation "schema")) (= "private-no-cohort-admission" (get observation "scope"))) :observation-schema)
   (keys! options #{:roots :runtime-witnesses :io?})
   (need (or (nil? (:runtime-witnesses options)) (map? (:runtime-witnesses options))) :runtime-witnesses)
   (need (instance? Boolean (:io? options)) :options)
   (encoded! observation 4194304)
   (let [g (graph/validate! (get observation "typeGraph")) defs (unique-index (get g "definitions") "id")
         rep (get observation "representation") work (volatile! 0) facts (volatile! {})]
     (keys! rep #{"schema" "scope" "rootTypes" "applications" "closedFields" "families"})
     (need (and (= "lean-jvm-native-layout-observations/4" (get rep "schema")) (= "observed-not-admitted" (get rep "scope"))) :representation-schema)
     (encoded! rep 1048576)
     (let [roots (get g "roots") root-native (get rep "rootTypes") checks (get observation "rootTypeChecks")
           applications (unique-index (get rep "applications") "definition") closed (unique-index (get rep "closedFields") "definition")
           families (unique-index (mapv family! (get rep "families")) "typeName")
           register! (fn [t expr ir]
                       (lane! ir) (matches! defs t expr work)
                       (let [fact {:native expr :ir ir}] (when-let [old (get @facts t)] (need (= old fact) :inconsistent-closed-lowering))
                         (vswap! facts assoc t fact)))]
       (doseq [[rows limit] [[root-native 1024] [checks 1024] [(get rep "applications") 256] [(get rep "closedFields") 256] [(get rep "families") 512]]] (vector! rows limit))
       (need (and (= (count roots) (count root-native) (count checks)) (= (set (keys defs)) (set (keys applications)) (set (keys closed)))) :observation-closure)
       (let [required (into (set (map #(get % "name") (vals defs)))
                            (for [t (:types (type-closure defs roots)) :let [kind (get t "kind")]
                                  :when (#{"list" "option" "product" "sum" "except"} kind)]
                              ["str" ["anonymous"] (get builtin-names kind)]))]
         (need (= required (set (keys families))) :family-closure))
       (doseq [[i t] (map-indexed vector roots)]
         (let [r (nth root-native i) c (nth checks i)]
           (keys! r #{"root" "nativeType" "irType"}) (keys! c #{"root" "algorithm" "transparency" "actualType" "expectedType"})
           (need (and (= i (get r "root") (get c "root")) (= (get r "nativeType") (get c "expectedType"))) :root-native-binding)
           (defeq! (dissoc c "root") defs t work) (register! t (get r "nativeType") (get r "irType"))))
       (doseq [[id d] defs]
         (let [t {"kind" "nominal" "id" id} app (get applications id) fields (get closed id) family (get families (get d "name"))
               cs (get d "constructors") native-cs (get family "constructors") observed-cs (get fields "constructors")]
           (keys! app #{"definition" "nativeType" "irType"}) (keys! fields #{"definition" "constructors"})
           (need family :missing-family) (register! t (get app "nativeType") (get app "irType"))
           (vector! observed-cs 1024) (need (= (count cs) (count native-cs) (count observed-cs)) :constructor-closure)
           (doseq [[ci c] (map-indexed vector cs)]
             (let [native (nth native-cs ci) observed (nth observed-cs ci) fs (get c "fields") of (get observed "fields") nf (get native "fields")]
               (keys! observed #{"constructor" "constructorIndex" "fields"})
               (need (and (= ci (get observed "constructorIndex")) (= (get c "name") (get native "constructor") (get observed "constructor"))) :constructor-binding)
               (vector! of 64) (need (= (count fs) (count of) (count nf)) :field-closure)
               (doseq [[fi f] (map-indexed vector fs)]
                 (let [o (nth of fi) t (get f "type") check (get o "typeCheck")]
                   (keys! o #{"field" "logicalType" "typeCheck" "closedIRType" "genericFieldIndex" "genericFieldInfo"})
                   (need (and (= fi (get o "field") (get o "genericFieldIndex")) (= t (get o "logicalType")) (= (nth nf fi) (get o "genericFieldInfo"))) :generic-closed-field-binding)
                   (defeq! check defs t work) (register! t (get check "expectedType") (get o "closedIRType"))))))))
       (let [selection (:roots options) _ (vector! selection 1024)
             _ (need (and (seq selection) (= (count selection) (count (set selection)))) :selected-roots)
             _ (doseq [i selection] (nat! i (dec (count roots)))) selected (mapv #(nth roots %) selection)
             closure (type-closure defs selected) ids (zipmap (:ids closure) (range))
             pruned (assoc g "roots" selected "definitions" (filterv #(contains? ids (get % "id")) (get g "definitions")))
             canonical (graph/canonical-graph pruned) types (:types closure) plans (zipmap types (range)) witnesses (:runtime-witnesses options)
             special (if witnesses
                       (do (encoded! witnesses 1048576) (keys! witnesses #{"algorithm" "specialTypes" "ioFamilies" "world"})
                           (need (= "Lean.Compiler.LCNF.toLCNFType/toMonoType/toImpureType" (get witnesses "algorithm")) :runtime-algorithm)
                           (vector! (get witnesses "specialTypes") 8192)
                           (vector! (get witnesses "ioFamilies") 64)
                           (unique-index (get witnesses "specialTypes") "type")) {})]
         (doseq [[t w] special]
           (keys! w #{"type" "nativeType" "irType"}) (need (special-kinds (get t "kind")) :special-witness-kind)
           (need (contains? (set (:types (type-closure defs roots))) t) :orphan-special-witness)
           (register! t (get w "nativeType") (get w "irType")))
         (when (:io? options)
           (need (and witnesses (= "canonical-erased-zero" (get witnesses "world"))) :missing-io-world)
           ;; Closed EST.Out/IO.Error witness-to-selected-entry binding is not yet
           ;; emitted in005; generic families alone cannot authorize that envelope.
           (fail :missing-closed-io-witness))
         (when witnesses (need (and (nil? (get witnesses "world")) (empty? (get witnesses "ioFamilies"))) :unexpected-io-witness))
         (letfn [(lower [t]
                   (poll!)
                   (let [kind (get t "kind") fact (get @facts t) ir (:ir fact)]
                     (when (special-kinds kind) (need (contains? special t) :missing-special-witness))
                     (need fact :missing-closed-lowering)
                     (cond
                       (#{"nat" "int" "string"} kind) (do (need (= ir (if (= kind "string") "object" "tobject")) :leaf-lowering) {"kind" kind})
                       (= "unit" kind) (do (need (= ir "tagged") :unit-lowering) {"kind" "unit"})
                       (= "bytes" kind) (do (need (= ir "object") :bytes-lowering) {"kind" "bytes"})
                       (= "array" kind) (do (need (= ir "object") :array-lowering) {"kind" "array" "element" (get plans (get t "element"))})
                       (= "word" kind) (fail :missing-native-target-width)
                       (#{"machine-int" "float" "bool" "char"} kind)
                       (let [lane (case kind "machine-int" (str "uint" (get t "bits")) "float" (if (= 32 (get t "bits")) "float32" "float") "bool" "uint8" "char" "uint32")]
                         (need (= ir lane) :scalar-lowering)
                         {"kind" "scalar" "lane" lane "boxed" (cond (= lane "float32") "box32" (#{"uint64" "float"} lane) "box64" :else "small-immediate")})
                       (contains? builtin-names kind) (fail :missing-closed-builtin-witness)
                       (= "nominal" kind)
                       (let [d (get defs (get t "id")) family (get families (get d "name")) trivial (get family "trivialStructure") native-cs (get family "constructors")]
                         (when trivial (need (= (count (get d "arguments")) (get trivial "numParams")) :trivial-parameter-count))
                         (when-not trivial (need (= ir (get family "irType")) :closed-family-lowering))
                         {"kind" "family" "constructors"
                          (mapv (fn [ci c]
                                  (let [native (nth native-cs ci) info (get native "ctorInfo") fields (get native "fields") alias (when trivial (get trivial "fieldIndex"))
                                        immediate? (zero? (+ (get info "size") (get info "usize") (get info "ssize")))]
                                    (when-not (or immediate? trivial) (need (<= ci 243) :allocated-tag))
                                    {"index" ci "name" (get c "name")
                                     "representation" (cond trivial {"kind" "alias" "field" alias}
                                                            immediate? {"kind" "immediate" "tag" ci}
                                                            :else {"kind" "node" "tag" ci "objects" (get info "size") "usize" (get info "usize") "ssize" (get info "ssize")})
                                     "fields" (mapv (fn [fi f]
                                                       (let [generic (nth fields fi) child (get f "type") child-ir (:ir (get @facts child))]
                                                         {"index" fi "plan" (get plans child)
                                                          "location" (if trivial
                                                                         (do (need (= fi alias) :unsupported-value-erasure)
                                                                             (need (= ir child-ir) :trivial-closed-lowering) {"kind" "self"})
                                                                         (case (get generic "kind")
                                                                           "object" {"kind" "object" "slot" (get generic "index")}
                                                                           "usize" (do (need (= child-ir "usize") :closed-scalar-correspondence) {"kind" "usize" "nativeIndex" (get generic "index")})
                                                                           "scalar" (do (need (= child-ir (get generic "irType")) :closed-scalar-correspondence) {"kind" "scalar" "offset" (get generic "offset") "lane" child-ir})
                                                                           (fail :unsupported-value-erasure)))}))
                                                     (range) (get c "fields"))}))
                                (range) (get d "constructors"))})
                       :else (fail :unsupported-logical-kind))))]
           (let [rows (mapv (fn [i t] {"id" i "type" (rewrite-type ids t) "closedIR" (:ir (get @facts t)) "encoding" (lower t)}) (range) types)
                 normalized {"schema" "lean-jvm-typed-storage/1" "logicalDigest" (graph/logical-digest canonical)
                             "target" {"wordBits" 64 "byteOrder" "little" "storageAbi" "node-pure-data/1"}
                             "roots" (mapv plans selected) "plans" rows}]
             (encoded! normalized 1048576)
             {:logical canonical :normalized normalized})))))))
