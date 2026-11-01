(ns ansatz.lean.jvm.capabilities
  "Audited positive task-free profile. Descriptors are metadata, not artifact authority."
  (:require [ansatz.lean.jvm.ir :as j]))
(def ^:private families
  {:nat ["ADD" "SUB" "MOD" "EQ" "LT" "MUL" "DIV" "POW" "NAT_LE" "NAT_LOG2" "NAT_OR" "NAT_SHL" "NAT_SHR"]
   :int ["INT_OF_NAT" "INT_NEG_SUCC" "INT_NEG" "INT_ABS" "INT_ADD" "INT_SUB" "INT_EQ" "INT_LT" "INT_LE"]
   :word ["USIZE_NAT" "USIZE_REPR" "USIZE_LT" "USIZE_ADD" "USIZE_EQ" "USIZE_SUB" "USIZE_TO_NAT"
          "USIZE_SHR" "USIZE_SHL" "USIZE_AND" "USIZE_LE" "USIZE_MUL" "USIZE_TO_U64"
          "U8_ADD" "U8_NAT" "U8_EQ" "U8_AND" "U8_LE" "U8_TO_U32" "U8_TO_U64" "U16_EQ" "U16_NAT"
          "U32_OWNED_NAT" "U32_NAT" "U32_EQ" "U32_LE" "U32_FROM_NAT" "U32_TO_U8" "U32_ADD" "U32_TO_U64" "U32_LT"
          "U64_MIX" "U64_NAT" "U64_SHR" "U64_XOR" "U64_USIZE" "U64_LT" "U64_EQ" "U64_OWNED_NAT"
          "U64_TO_U32" "U64_TO_U8" "U64_TO_NAT" "BOOL_U64" "U64_ADD" "U64_SUB" "U64_MUL"
          "U64_DIV" "U64_MOD" "U64_AND" "U64_OR" "U64_NOT" "U64_NEG" "U64_LOG2" "U64_SHL" "U64_LE"]
   :string ["STR_PUSH" "STR_LIST" "STR_GET" "STR_NEXT" "STR_APPEND" "STR_SIZE" "STR_END"
            "STR_SAFE_GET" "STR_SAFE_NEXT" "STR_PREV" "STR_VALID" "STR_EXTRACT" "STR_EQ" "STR_LT"
            "STR_COMPARE" "STR_BYTE" "STR_CONTAINS" "STR_LENGTH" "STR_SET" "STR_HASH" "STR_MEMCMP"
            "STR_SUBSTRING_EQ" "STR_POS_OF" "STR_OFFSET_OF_POS" "STR_PUSHN" "STR_POS_SET"
            "STR_TO_UTF8" "STR_FROM_UTF8" "STR_VALIDATE_UTF8"]
   :byte-array ["BYTE_MK" "BYTE_GET" "BYTE_SIZE" "BYTE_PUSH" "BYTE_EMPTY" "BYTE_COPY_SLICE" "BYTE_GET_DEFAULT"]
   :array ["ARRAY_MK" "ARRAY_SIZE" "ARRAY_GET" "ARRAY_EMPTY" "ARRAY_PUSH" "ARRAY_POP" "ARRAY_USIZE"
           "ARRAY_FGET" "ARRAY_UGET" "ARRAY_UGET_BORROWED" "ARRAY_FSET" "ARRAY_USET" "ARRAY_SWAP"
           "ARRAY_LIST" "ARRAY_REPLICATE" "ARRAY_CHECKED_GET" "ARRAY_CHECKED_BORROWED" "ARRAY_CHECKED_SET"]
   :ref ["REF_MK" "REF_GET" "REF_SET" "REF_SWAP" "REF_TAKE" "REF_PTR_EQ"]
   :heap-persistence ["VOID_MK" "MARK_PERSISTENT"]
   :build-layout-observation ["PLATFORM_BITS" "BUILD_GITHASH" "BUILD_TARGET" "IO_INITIALIZING"
                              "LAYOUT_FIELDS" "LAYOUT_SCALARS" "LAYOUT_TAG" "LAYOUT_USIZE"]
   :float ["FLOAT32_BITS" "FLOAT32_DIV" "FLOAT32_MUL" "U64_FLOAT32" "FLOAT_ADD" "FLOAT32_ADD" "FLOAT_BITS" "FLOAT_U64" "FLOAT_SUB" "FLOAT_MUL" "FLOAT_DIV" "FLOAT_EQ" "FLOAT_LT" "FLOAT_LE" "FLOAT_STRING"]
   :captured-stdout ["GET_STDOUT"]
   :entropy ["IO_RANDOM_BYTES"]
   ;; Existing Interpreter PANIC terminates with an unsupported-operation
   ;; failure; it never invents Lean's default-return result.
   :terminal-trap ["PANIC"]})
(defn- need [p message] (when-not p (throw (ex-info message {:code "CapabilityMissing" :profile :task-free-captured-output-v1}))))
(defn- field [object name]
  (let [f (.getDeclaredField (class object) name)] (.setAccessible f true) (.get f object)))
(defn- static-field [^Class cls name]
  (let [f (.getDeclaredField cls name)] (.setAccessible f true) (.get f nil)))
(defn- family-index [^Class cls]
  (reduce-kv (fn [index family fields]
               (reduce (fn [index name]
                         (let [value (static-field cls name)]
                           (need (and (integer? value) (not (contains? index value))) "Runtime intrinsic cohort differs")
                           (assoc index value {:family family :field name}))) index fields)) {} families))
(defn- abi [declaration]
  {:params (mapv #(get % "ty") (get declaration "xs"))
   :borrowed (mapv #(get % "borrow") (get declaration "xs")) :result (get declaration "type")})
(defn- spec-abi [spec]
  {:params (vec (field spec "paramTypes")) :borrowed (vec (field spec "borrowed")) :result (field spec "resultType")})
(defn check-rows!
  "Refuse every unknown capability before Header publication/engine effects.
   Match actual runtime symbol AND full ABI, then classify semantic intrinsic ID."
  [basis rows]
  (let [cls (:class basis) registry (static-field cls "EXTERNS") index (family-index cls)
        externs (into {}
                      (for [row rows :let [declaration (get-in row ["ir" "extern"])] :when declaration]
                        (let [symbol (try (j/invoke-static (.getMethod ^Class cls "validateExternAbi" (into-array Class [java.util.Map])) [row])
                                          (catch java.lang.reflect.InvocationTargetException failure
                                            (throw (ex-info "Unsupported Lean runtime extern or ABI"
                                                            {:code "CapabilityMissing" :name (get row "name")} failure))))
                              matches (filter #(= (abi declaration) (spec-abi %)) (get registry symbol))
                              _ (need (= 1 (count matches)) "Unknown or ambiguous runtime extern ABI")
                              intrinsic (field (first matches) "intrinsic") family (get index intrinsic)]
                          (need family "Required intrinsic is outside the audited task-free profile")
                          (when (= :entropy (:family family))
                            (need (= ["str" ["str" ["anonymous"] "IO"] "getRandomBytes"] (get row "name"))
                                  "Entropy profile requires its canonical installed Header Name"))
                          [(get row "name") (assoc family :intrinsic intrinsic :symbol symbol :abi (abi declaration))])))]
    {:profile :task-free-captured-output-v1 :runtime-class cls :registry-object registry
     :entropy-action (static-field cls "ACTION_ENTROPY")
     :externs externs :typed-inputs #{:nat :string :erased-world}
     :dynamic-io-profile :captured-stdout-write-flush-tty
     :runtime-unsupported #{:captured-stream-read :captured-stream-write :captured-stream-line :panic-default-return}
     :task-runtime false :host-handlers false :guest-export-aliases false :code-demand false}))
(defn check-program!
  "Bind the requirements to the actual fully prepared canonical Program. No engine exists."
  [ctx headers descriptor]
  (need (and (identical? (:runtime-class descriptor) (:class ctx))
             (identical? (:registry-object descriptor) (static-field (:class ctx) "EXTERNS"))) "Capability descriptor belongs to another runtime cohort")
  (let [program (:program ctx) functions (field program "functions") bodies (field program "preparedBodies")
        exports (field program "guestExports") by-header (java.util.IdentityHashMap.)]
    (need (empty? (field program "hostRegistry")) "Host service registration is outside this profile")
    (need (= (count headers) (alength ^objects functions) (alength ^objects bodies) (alength ^objects exports)) "Program/header domain differs")
    (doseq [[name header] headers] (.put by-header header name))
    (doseq [i (range (alength ^objects functions))]
      (let [function (aget ^objects functions i) header (field function "header") name (.get by-header header)
            requirement (get-in descriptor [:externs name]) intrinsic (field function "intrinsic")]
        (need (and name (nil? (field function "hostExtern")) (nil? (aget ^objects exports i))) "Program has foreign Header/host handler/guest export")
        (if requirement
          (need (= intrinsic (:intrinsic requirement)) "Actual Program intrinsic differs from audited descriptor")
          (need (and (= 0 intrinsic) (some? (aget ^objects bodies i))) "Program body is unavailable or unclassified"))))
    descriptor))
