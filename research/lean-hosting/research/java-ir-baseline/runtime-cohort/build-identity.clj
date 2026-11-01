(ns original-build-identity-provider-v1
  "Five fixed, source-authenticated supported-build version queries. No IO.Result, offset,
   guest allocation, source issuance, registry mutation or branch clone."
  (:require [java-ir-baseline :as j]
            [ansatz.research.ir.source-setup :as source])
  (:import [java.lang.reflect InvocationTargetException]))
(defn- wire [parts]
  (reduce (fn [p x] (if (integer? x) ["num" p (str x)] ["str" p x])) ["anonymous"] parts))
(def specifications
  (into {} (map (fn [[symbol leaf sha result value private?]]
    [symbol {:symbol symbol :name (wire (into (if private? ["_private" "Init" "Meta" "Defs" 0] []) ["Lean" "version" leaf]))
             :sha sha :parameters ["tagged"] :borrowed [false] :result result :value value}])
    [["lean_version_get_major" "getMajor" "168e9ed3b15cfe2c03809edb4f24e2250fc6b9965a9c482190f711843ff20cb6" "tobject" (long 4) true]
     ["lean_version_get_minor" "getMinor" "4ad505698e16882157f1be6e9ced80689ea32e3b7931a9efe53198b90722ddaf" "tobject" (long 33) true]
     ["lean_version_get_patch" "getPatch" "b5a06b61f354e3ca520288ac2f85a58def8ecd989663ba1599eed840186eef6b" "tobject" (long 1) true]
     ["lean_version_get_is_release" "getIsRelease" "5db15bbc78c8f52f541874a479d1be7ac9787403b5b11a7e1a32ec94824a58f3" "uint8" (long 1) false]
     ["lean_version_get_special_desc" "getSpecialDesc" "7f7ca043796ad93976a00dfb51a4c5c9294535683c3a26f3bec0a175ba3f69e2" "object" "" false]])))
(defn- need [ok message] (when-not ok (throw (ex-info message {:profile :original-build-identity-v1}))))
(defn- field [x k] (.get (doto (.getDeclaredField (class x) k) (.setAccessible true)) x))
(defn- invoke [target name types args]
  (try (.invoke (doto (.getDeclaredMethod (class target) name (into-array Class types)) (.setAccessible true)) target (object-array args))
       (catch InvocationTargetException e (throw (.getCause e)))))
(defn handles? [symbol] (contains? specifications symbol))
(defn- original! [receipt symbol]
  (let [{:keys [name sha parameters borrowed result] :as spec} (get specifications symbol)
        _ (need spec "Unsupported build-identity symbol")
        entry (source/lookup-entry receipt name) row (:row entry) declaration (get-in row ["ir" "extern"])]
    (need (and (= sha (:sha256 entry)) (= name (get row "name"))
               (= #{"extern"} (set (keys (get row "ir"))))
               (= parameters (mapv #(get % "ty") (get declaration "xs")))
               (= borrowed (mapv #(get % "borrow") (get declaration "xs")))
               (= result (get declaration "type"))
               (= symbol (get-in declaration ["ext" "entries" 0 "standard" "fn"]))
               (= [] (get row "dependencies")) (nil? (get row "redirect"))
               (= {"role" "ordinary" "initializer" nil} (get row "runtime")))
          "Original build-identity row/metadata/ABI differs")
    [spec row]))
(defn early-specifications!
  "Return authenticated descriptors before first Header registration. Existing
   unavailable immutable Functions cannot be upgraded by later host registration."
  [actual-code-receipt]
  (mapv (fn [symbol]
          (let [[spec _] (original! actual-code-receipt symbol)]
            (select-keys spec [:symbol :parameters :borrowed :result])))
        (sort (keys specifications))))
(defn serve!
  "Reply once to the actual current request, using THIS call's live receipt,
   engine/source/current Program. Captures no previous parent or SourceBinding.
   Unknown symbols and invalid preflight leave the request untouched."
  [actual-code-receipt session]
  (let [driver (:driver session) ctx @(:current-ctx driver) engine (:engine driver)
        _ (need (and (identical? (:class ctx) (class engine))
                     (identical? (:program ctx) (field engine "program"))) "Current build-identity basis/Program differs")
        _ (doseq [k ["closed" "disposed" "untrackedFailure" "advancing"]]
            (need (false? (field engine k)) "Invalid build-identity engine lifecycle"))
        _ (need (= "host-call" (j/phase ctx engine)) "Current build-identity HostRequest required")
        _ (source/guard-source! actual-code-receipt (:source driver))
        _ (need (identical? (field engine "buildIdentity") (j/supported-build-identity ctx))
                "Build-identity target requires explicit supported Lean 4.33.1 x86_64 profile")
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
                "Actual build-identity request ABI differs")
        args (vec (j/request-value request "arguments"))
        _ (need (and (= 1 (count args)) (instance? Long (first args)) (zero? (first args)))
                "Build-identity Unit must be actual Long zero")
        value (if (= "object" (:result spec)) (String. ^String (:value spec)) (:value spec))
        _ (invoke engine "preflightHostCompletion" [(class call) Object] [call value])
        journal {:request request :symbol symbol :reply value :status :reply-pending}]
    ;; Unit and result are immutable JVM carriers with no guest RC/finalizer
    ;; work. Java retains any claimed HostCompletion on failure; do not replay it.
    (try
      (j/resume-host! ctx engine request value)
      {:status :build-identity-replied :symbol symbol :value value}
      (catch Throwable error
        (throw (ex-info "Build-identity completion failed; preserve actual request and do not replay"
                        {:profile :original-build-identity-v1 :completion journal :disposition :do-not-replay} error))))))
