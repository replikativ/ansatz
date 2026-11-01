(ns ansatz.lean.jvm.entry
  "Shared native entry observations. Validating metadata never issues a build,
   artifact or runtime capability; those issuers retain their own byte custody."
  (:require [ansatz.lean.jvm.signature :as signature])
  (:import [java.nio.charset StandardCharsets]))

(def legacy-profiles #{"nat-to-nat" "string-to-string" "io-unit"})
(def cohorts
  {1 {:evidence "lean-native-entry-evidence/1" :request "lean-native-entry-requests/1"
      :producer "NativeEntryEvidence.exportEntries"
      :source "e89beefe6ebb864d830367a377360d68cbce89c97fa6a5a5e9dab8877b6c6629"
      :binary "a94b830bcada8032736e3bbd43e7dce559054e2214cb74489bd58709ac486593"}
   2 {:evidence "lean-native-entry-evidence/2" :request "lean-native-entry-requests/2"
      :producer "NativeGeneralEntryEvidence.exportEntries"
      :source "e3e6f269769d2155b2367fc12e685b86b18204248b4303639e9fa6a59325f8ed"
      :binary "64fc830a0bc395eed1e11280321331c9877021ce0e69b3aec6dfcb8b7646355a"}})
(def producer-pins
  "Independently admitted source/binary pairs. New producer builds enter only
   after root-owned compilation/acceptance; the original v2 pair stays explicit."
  {1 #{[(get-in cohorts [1 :source]) (get-in cohorts [1 :binary])]}
   2 #{[(get-in cohorts [2 :source]) (get-in cohorts [2 :binary])]}})
(defn- need [ok stage]
  (when-not ok (throw (ex-info "Native entry observation rejected" {:code "EntryRejected" :stage stage}))))
(defn schema-for-pins! [source binary]
  (or (some (fn [[schema pairs]] (when (contains? pairs [source binary]) schema)) producer-pins)
      (throw (ex-info "Unsupported native entry producer cohort" {:code "UnsupportedProjectConfig" :stage :entry-helper-cohort}))))
(defn- typed-name [parts] (reduce (fn [parent part] ["str" parent part]) ["anonymous"] parts))
(defn- name! [value]
  (loop [name value depth 0 characters 0]
    (need (and (vector? name) (< depth 128) (<= characters 16384)) :name)
    (if (= ["anonymous"] name) value
      (let [[kind parent leaf] name]
        (need (and (= 3 (count name)) (#{"str" "num"} kind) (string? leaf) (<= (count leaf) 4096)) :name)
        (let [bytes (.getBytes ^String leaf StandardCharsets/UTF_8)]
          (need (and (<= (alength bytes) 4096)
                     (= leaf (String. bytes StandardCharsets/UTF_8))) :name-unicode))
        (when (= "num" kind)
          (need (and (re-matches #"0|[1-9][0-9]{0,19}" leaf)
                     (<= (bigint leaf) 18446744073709551615N)) :name-number))
        (recur parent (inc depth) (+ characters (count leaf)))))))
(defn descriptor [entry]
  (let [value (get-in entry ["typeCheck" "signature"])]
    (if (string? value) (signature/from-legacy value) (signature/validate! value))))
(defn- legacy-expected! [profile expected]
  (let [constant #(vector "const" (typed-name [%]) [])]
    (if (= "io-unit" profile)
      (need (= ["app" (constant "IO") (constant "Unit")] expected) :expected-type)
      (let [base (constant (if (= "nat-to-nat" profile) "Nat" "String"))]
        ;; Preserve v1's native binder-name freedom, not a new textual equality.
        (need (and (vector? expected) (= 5 (count expected)) (= "forall" (first expected))
                   (= "default" (nth expected 2)) (= base (nth expected 3)) (= base (nth expected 4))) :expected-type)))))
(defn- object-field [index] {"kind" "object" "index" index "irType" "tobject"})
(defn- constructor [family leaf tag fields]
  (let [name (typed-name (conj family leaf))]
    {"constructor" name "ctorInfo" {"name" name "cidx" tag
                                   "size" (count (filter #(= "object" (get % "kind")) fields))
                                   "usize" 0 "ssize" 0}
     "fields" fields}))
;; These admitted layouts are independently observed under the pinned v2
;; producer/Lean cohort. Comparison with actual native witnesses is mandatory;
;; this policy table alone never authorizes a Node or a host allocation recipe.
(def ^:private layout-policy
  {(typed-name ["Prod"]) {"typeName" (typed-name ["Prod"]) "irType" "object" "trivialStructure" nil
                           "constructors" [(constructor ["Prod"] "mk" 0 [(object-field 0) (object-field 1)])]}
   (typed-name ["Option"]) {"typeName" (typed-name ["Option"]) "irType" "tobject" "trivialStructure" nil
                             "constructors" [(constructor ["Option"] "none" 0 [])
                                             (constructor ["Option"] "some" 1 [(object-field 0)])]}
   (typed-name ["List"]) {"typeName" (typed-name ["List"]) "irType" "tobject" "trivialStructure" nil
                           "constructors" [(constructor ["List"] "nil" 0 [])
                                           (constructor ["List"] "cons" 1 [(object-field 0) (object-field 1)])]}
   (typed-name ["Sum"]) {"typeName" (typed-name ["Sum"]) "irType" "object" "trivialStructure" nil
                         "constructors" [(constructor ["Sum"] "inl" 0 [(object-field 0)])
                                         (constructor ["Sum"] "inr" 1 [(object-field 0)])]}
   (typed-name ["Except"]) {"typeName" (typed-name ["Except"]) "irType" "object" "trivialStructure" nil
                            "constructors" [(constructor ["Except"] "error" 0 [(object-field 0)])
                                            (constructor ["Except"] "ok" 1 [(object-field 0)])]}
   (typed-name ["EST" "Out"]) {"typeName" (typed-name ["EST" "Out"]) "irType" "object" "trivialStructure" nil
                                "constructors" [(constructor ["EST" "Out"] "ok" 0 [(object-field 0) {"kind" "void"}])
                                                (constructor ["EST" "Out"] "error" 1 [(object-field 0) {"kind" "void"}])]}})
(defn- type-families [type]
  (case (get type "kind")
    "product" (into #{(typed-name ["Prod"])} (concat (type-families (get type "first")) (type-families (get type "second"))))
    "option" (conj (type-families (get type "element")) (typed-name ["Option"]))
    "list" (conj (type-families (get type "element")) (typed-name ["List"]))
    "array" (type-families (get type "element"))
    "sum" (into #{(typed-name ["Sum"])} (concat (type-families (get type "left")) (type-families (get type "right"))))
    "except" (into #{(typed-name ["Except"])} (concat (type-families (get type "error")) (type-families (get type "value"))))
    #{}))
(defn- witnesses! [descriptor witnesses]
  (let [expected (reduce into (type-families (get descriptor "result")) (map type-families (get descriptor "arguments")))
        expected (cond-> expected (= "io" (get descriptor "effect")) (conj (typed-name ["EST" "Out"])))
        families (get witnesses "families")]
    (need (and (map? witnesses) (= #{"algorithm" "scope" "families"} (set (keys witnesses)))
               (= "Lean.Compiler.LCNF.getCtorLayout" (get witnesses "algorithm"))
               (= "actual-persisted-native-compiler-layout-not-host-allocation-authority" (get witnesses "scope"))
               (vector? families) (<= (count families) 6)
               (= (count families) (count (set (map #(get % "typeName") families))))
               (= expected (set (map #(get % "typeName") families)))) :codec-witness-set)
    (doseq [family families]
      (need (= family (get layout-policy (get family "typeName"))) :codec-witness-layout))))
(defn- scalar-lane [type]
  (case (get type "kind")
    "bool" "uint8"
    "machine-int" (str "uint" (get type "bits"))
    "word" "usize"
    "float" (if (= 32 (get type "bits")) "float32" "float")
    "char" "uint32"
    nil))
(defn- special-types [type]
  (case (get type "kind")
    ("machine-int" "word" "float" "char" "bytes") #{type}
    "array" (conj (special-types (get type "element")) type)
    "product" (into (special-types (get type "first")) (special-types (get type "second")))
    "sum" (into (special-types (get type "left")) (special-types (get type "right")))
    "except" (into (special-types (get type "error")) (special-types (get type "value")))
    ("option" "list") (special-types (get type "element"))
    #{}))
(defn- representation! [descriptor representation]
  (let [types (reduce into (special-types (get descriptor "result")) (map special-types (get descriptor "arguments")))
        observations (get representation "types")]
    ;; The original core-only v2 producer predates this field. Special types
    ;; always require it; an optional observation on old types must still match.
    (when (or (seq types) (some? representation))
      (need (and (map? representation) (= #{"algorithm" "types"} (set (keys representation)))
                 (= "Lean.Compiler.LCNF.toLCNFType/toMonoType/toImpureType" (get representation "algorithm"))
                 (vector? observations) (<= (count observations) 512)
                 (= (count observations) (count (set (map #(get % "type") observations))))
                 (= types (set (map #(get % "type") observations)))) :native-representation-set)
      (doseq [observation observations]
        (let [type (get observation "type") lane (or (scalar-lane type) "object")]
          (need (and (= #{"type" "irType"} (set (keys observation)))
                     (= lane (get observation "irType"))) :native-representation-lane))))))
(defn- abi! [abi]
  (need (and (map? abi) (= #{"name" "xs" "type"} (set (keys abi)))
             (vector? (get abi "xs")) (<= (count (get abi "xs")) 65)) :callable-abi)
  (name! (get abi "name")) abi)
(defn validate!
  "Validate one full, pre-compaction native entry. The actual issuer, source
   rows and file/provenance checks remain mandatory at each owning boundary."
  [entry]
  (let [profile (get-in entry ["typeCheck" "signature"]) v1? (string? profile)
        descriptor (descriptor entry) callable (abi! (get entry "callable")) raw (abi! (get entry "raw"))
        parameters (get callable "xs") arity (if v1? 1 (signature/runtime-arity descriptor))
        scalar? (and (not v1?) (= "pure" (get descriptor "effect"))
                     (empty? (get descriptor "arguments"))
                     (some? (scalar-lane (get descriptor "result")))
                     (= (scalar-lane (get descriptor "result")) (get callable "type")))
        scalar-bool? (and scalar? (= {"kind" "bool"} (get descriptor "result")))]
    (name! (get entry "name")) (name! (get entry "compiledModule"))
    (need (and (#{"definition" "opaque"} (get entry "kind")) (= [] (get entry "levelParams"))
               (= "Lean.Meta.isDefEq" (get-in entry ["typeCheck" "algorithm"]))
               (= "default" (get-in entry ["typeCheck" "transparency"]))
               (vector? (get entry "actualType"))) :native-type-check)
    (if v1? (legacy-expected! profile (get-in entry ["typeCheck" "expectedType"]))
      (need (= (signature/expected-type descriptor) (get-in entry ["typeCheck" "expectedType"])) :expected-type))
    (need (and (= (get entry "name") (get raw "name"))
               (#{"original-interpreter-boxed-lookup" "original-owned-raw"} (get entry "selection"))
               (= arity (count parameters))
               (every? #(and (false? (get % "borrow")) (#{"object" "tobject" "tagged"} (get % "ty"))) parameters)
               (or (#{"object" "tobject" "tagged"} (get callable "type"))
                   (and scalar? (= "original-owned-raw" (get entry "selection"))))) :owned-callable)
    (when-not v1?
      (need (and (= (signature/arity descriptor) (get entry "semanticArity"))
                 (= arity (get entry "runtimeArity"))
                 (= (cond-> (mapv #(hash-map "kind" "argument" "index" %) (range (signature/arity descriptor)))
                      (= "io" (get descriptor "effect"))
                      (conj {"kind" "io-world" "representation" "canonical-erased-zero"}))
                    (get entry "argumentPlan"))
                 (= (cond scalar-bool? "raw-nullary-bool-uint8" scalar? "raw-nullary-scalar" :else "boxed-object-lane") (get entry "resultABI"))
                 (if (= "original-owned-raw" (get entry "selection")) (= raw callable) (seq (get raw "xs")))) :v2-call-plan)
      (witnesses! descriptor (get entry "codecWitnesses"))
      (representation! descriptor (get entry "nativeRepresentation")))
    entry))
(defn validate-rows! [entry index]
  (validate! entry)
  (doseq [role ["raw" "callable"]]
    (let [abi (get entry role) row (get index (get abi "name")) declaration (get-in row ["ir" "fdecl"])]
      (need (and declaration (= abi {"name" (get declaration "f") "xs" (get declaration "xs") "type" (get declaration "type")})
                 (= (get entry "compiledModule") (get row "sourceModule"))) :original-callable)))
  entry)
(defn validate-document! [root request document]
  (let [schema (some (fn [[schema cohort]] (when (= (:evidence cohort) (get document "schema")) schema)) cohorts)
        cohort (get cohorts schema) requests (get request "entries") entries (get document "entries")]
    (need (and cohort (= (:request cohort) (get request "schema"))
               (= (:producer cohort) (get document "producer"))
               (= "819816b2e0a3bf405af45ae5c7af2491d8f5bee6" (get document "leanCommit"))
               (= "4.33.1" (get document "leanVersion"))
               (= {"wordBits" 64 "target" "x86_64-unknown-linux-gnu"} (get document "runtimeProfile"))
               (false? (get document "dynamicClosureProven"))
               (= root (get request "module") (get document "compiledModule"))
               (vector? requests) (vector? entries) (<= 1 (count requests) 16)
               (= (count requests) (count entries) (count (set (map #(get % "name") requests))))
               (= (mapv #(get % "name") requests) (mapv #(get % "name") entries))) :entry-document)
    (name! root)
    (when (= 2 schema)
      (need (= #{"schema" "module" "entries"} (set (keys request))) :request-fields))
    (doseq [[request entry] (map vector requests entries)]
      (validate! entry)
      (if (= 1 schema)
        (need (and (legacy-profiles (get request "signature"))
                   (= (get request "signature") (get-in entry ["typeCheck" "signature"]))) :requested-signature)
        (need (and (= #{"name"} (set (keys request))) (map? (get-in entry ["typeCheck" "signature"]))) :request-fields)))
    entries))
