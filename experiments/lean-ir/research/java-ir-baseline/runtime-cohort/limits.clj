(ns original-runtime-limits-provider-v1
  "Two fixed, source-authenticated pure runtime queries. No IO.Result, offset,
   guest allocation, source issuance, registry mutation or branch clone."
  (:require [java-ir-baseline :as j]
            [ansatz.research.ir.source-setup :as source])
  (:import [java.lang.reflect InvocationTargetException]))
(def specifications
  {"lean_max_small_nat"
   {:symbol "lean_max_small_nat" :name ["str" ["str" ["anonymous"] "Lean"] "maxSmallNatFn"]
    :sha "7d18f28382b82388fe76f41b71ff6c626f60cfd1583a05820c36ad4de38b7f1d"
    :parameters ["tagged"] :borrowed [false] :result "tobject" :value Long/MAX_VALUE}
   "lean_closure_max_args"
   {:symbol "lean_closure_max_args" :name ["str" ["str" ["anonymous"] "Lean"] "closureMaxArgsFn"]
    :sha "6a8f4a7abe6f57dd8f0c2af46d0d7fd120313ffa6c171236874404e2c38b654e"
    :parameters ["tagged"] :borrowed [false] :result "tobject" :value (long 16)}})
(defn- need [ok message] (when-not ok (throw (ex-info message {:profile :original-runtime-limits-v1}))))
(defn- field [x k] (.get (doto (.getDeclaredField (class x) k) (.setAccessible true)) x))
(defn- invoke [target name types args]
  (try (.invoke (doto (.getDeclaredMethod (class target) name (into-array Class types)) (.setAccessible true)) target (object-array args))
       (catch InvocationTargetException e (throw (.getCause e)))))
(defn handles? [symbol] (contains? specifications symbol))
(defn- original! [receipt symbol]
  (let [{:keys [name sha parameters borrowed result] :as spec} (get specifications symbol)
        _ (need spec "Unsupported runtime-limit symbol")
        entry (source/lookup-entry receipt name) row (:row entry) declaration (get-in row ["ir" "extern"])]
    (need (and (= sha (:sha256 entry)) (= name (get row "name"))
               (= #{"extern"} (set (keys (get row "ir"))))
               (= parameters (mapv #(get % "ty") (get declaration "xs")))
               (= borrowed (mapv #(get % "borrow") (get declaration "xs")))
               (= result (get declaration "type"))
               (= symbol (get-in declaration ["ext" "entries" 0 "standard" "fn"]))
               (= [] (get row "dependencies")) (nil? (get row "redirect"))
               (= {"role" "ordinary" "initializer" nil} (get row "runtime")))
          "Original runtime-limit row/metadata/ABI differs")
    [spec row]))
(defn early-specifications!
  "Return authenticated descriptors before first Header registration. Existing
   unavailable immutable Functions cannot be upgraded by later host registration."
  [actual-code-receipt]
  (mapv (fn [symbol]
          (let [[spec _] (original! actual-code-receipt symbol)]
            (select-keys spec [:symbol :parameters :borrowed :result])))
        ["lean_max_small_nat" "lean_closure_max_args"]))
(defn serve!
  "Reply once to the actual current request, using THIS call's live receipt,
   engine/source/current Program. Captures no previous parent or SourceBinding.
   Unknown symbols and invalid preflight leave the request untouched."
  [actual-code-receipt session]
  (let [driver (:driver session) ctx @(:current-ctx driver) engine (:engine driver)
        _ (need (and (identical? (:class ctx) (class engine))
                     (identical? (:program ctx) (field engine "program"))) "Current runtime-limit basis/Program differs")
        _ (doseq [k ["closed" "disposed" "untrackedFailure" "advancing"]]
            (need (false? (field engine k)) "Invalid runtime-limit engine lifecycle"))
        _ (need (= "host-call" (j/phase ctx engine)) "Current runtime-limit HostRequest required")
        _ (source/guard-source! actual-code-receipt (:source driver))
        _ (need (identical? (field engine "buildIdentity") (j/supported-build-identity ctx))
                "Runtime-limit target requires explicit supported Lean 4.33.1 x86_64 profile")
        request (j/host-request ctx engine)
        _ (need request "Actual current request required")
        symbol (j/request-value request "symbol")
        [spec row] (original! actual-code-receipt symbol)
        call (invoke engine "requireHostRequest" [(class request)] [request])
        header (field (field call "function") "header")
        _ (source/authenticate-canonical-header! (:source driver) row (:sha spec) header)
        _ (need (= [(:parameters spec) (:borrowed spec) (:result spec)]
                   [(vec (j/request-value request "paramTypes"))
                    (vec (j/request-value request "borrowed")) (j/request-value request "resultType")])
                "Actual runtime-limit request ABI differs")
        args (vec (j/request-value request "arguments"))
        _ (need (and (= 1 (count args)) (instance? Long (first args)) (zero? (first args)))
                "Runtime-limit Unit must be actual Long zero")
        value (:value spec)
        _ (invoke engine "preflightHostCompletion" [(class call) Object] [call value])
        journal {:request request :symbol symbol :reply value :status :reply-pending}]
    ;; Unit and result are immutable immediate carriers with no guest RC/finalizer
    ;; work. Java retains any claimed HostCompletion on failure; do not replay it.
    (try
      (j/resume-host! ctx engine request value)
      {:status :runtime-limit-replied :symbol symbol :value value}
      (catch Throwable error
        (throw (ex-info "Runtime-limit completion failed; preserve actual request and do not replay"
                        {:profile :original-runtime-limits-v1 :completion journal :disposition :do-not-replay} error))))))
