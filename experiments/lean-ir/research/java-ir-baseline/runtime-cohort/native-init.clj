(ns java-prelude-no-native-init
  "Explicit empty native-symbol provider. A missing symbol selects Lean's real
   interpreted initializer path; it never reports that an initializer ran."
  (:require [java-ir-baseline :as j]))
(def spec {:symbol "lean_run_mod_init_core" :parameters ["object" "void"]
           :borrowed [true false] :result "object"})
(def original-sha "4da38699c35568ae9c898025e40628f1bcd3cae0fa14f4eaa8570a58105c3f2a")
(defn- need [ok message] (when-not ok (throw (ex-info message {:profile :empty-native-symbol-table}))))
(defn- field [x n] (.get (doto (.getDeclaredField (class x) n) (.setAccessible true)) x))
(defn configure [ctx header]
  (need (= original-sha (j/request-value header "originalSha256")) "Wrong native init source Header")
  (need (= ["object" "void"] (vec (j/request-value header "paramTypes"))) "Wrong native init ABI")
  (need (= [true false] (vec (j/request-value header "borrowed"))) "Wrong native init borrow ABI")
  (need (= "object" (j/request-value header "resultType")) "Wrong native init result ABI")
  {:ctx (j/register-headers ctx [header] [spec]) :header header :native-symbols #{}})
(defn serve! [cap driver]
  (let [ctx @(:current-ctx driver) e (:engine driver) request (j/host-request ctx e)]
    (need (= #{} (:native-symbols cap)) "Only an actually empty native symbol provider is supported")
    (need (= "host-call" (j/phase ctx e)) "No paused native init request")
    (need request "Missing native init request")
    (need (identical? (field request "owner") (field e "runtimeIdentity")) "Foreign native init request")
    (need (identical? (:header cap) (field (field (field request "call") "function") "header")) "Wrong native init caller Header")
    (need (= (:symbol spec) (j/request-value request "symbol")) "Wrong native init symbol")
    (let [arguments (vec (j/request-value request "arguments")) symbol (first arguments)]
      (need (and (= 2 (count arguments)) (string? symbol) (<= (.length ^String symbol) 65536)) "Invalid native symbol name")
      ;; The existing interpreter IO-ok Unit allocator is exactly ctor0[Long0].
      ;; Long0 is also Bool.false in this erased runtime. No field is fabricated
      ;; or rewritten after allocation; the result owns its normal single credit.
      (let [method (doto (.getDeclaredMethod (class e) "ioUnit" (make-array Class 0)) (.setAccessible true))
            result (.invoke method e (object-array 0))]
        (need (and (= 0 (.getInt ^java.lang.reflect.Field (:tag ctx) result))
                   (= [0] (vec (.get ^java.lang.reflect.Field (:fields ctx) result)))
                   (= 0 (alength ^bytes (.get ^java.lang.reflect.Field (:scalars ctx) result))))
              "IO Boolean false representation differs")
        (j/resume-host! ctx e request result)
        {:status :native-symbol-absent :symbol symbol :initializer-executed false}))))
