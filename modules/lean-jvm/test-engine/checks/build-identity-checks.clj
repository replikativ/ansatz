(ns java-ir-build-identity-checks
  "Explicit accepted-producer metadata, independent of module initialization."
  (:require [clojure.test :refer [deftest is run-tests]]
            [clojure.data.json :as json] [clojure.edn :as edn]
            [java-ir-baseline :as j] [java-ir-baseline-checks :as c]
            [java-ir-extern-checks :as x] [java-ir-generation-checks :as g]
            [java-ir-host-checks :as host] [java-ir-header-checks :as h]
            [java-ir-code-checks :as code] [lean-compatibility-corpus :as corpus]))
(def ^:dynamic *basis* nil)
(def fixture "test/fixtures/java-build-identity-runtime/original-rows.json")
(def originals (mapv #(get % "row") (json/read-str (slurp fixture))))
(def expected {"Lean.getGithash" "819816b2e0a3bf405af45ae5c7af2491d8f5bee6"
               "System.Platform.getTarget" "x86_64-unknown-linux-gnu"})
(defn context
  ([] (context []))
  ([extra] (assoc *basis* :program (j/invoke-static (:prepare *basis*) [(x/raw (concat originals extra))]))))
(defn enabled [ctx] (assoc ctx :build-identity (j/supported-build-identity ctx)))
(defn counters [engine] (mapv #(host/private-value engine %) ["allocations" "stores" "retains" "releases" "shellDeletes"]))

(deftest exact-original-abi-and-owned-wrappers
  (let [manifest (edn/read-string (slurp "test/fixtures/java-build-identity-runtime/provenance.edn"))
        ctx (enabled (context)) engine (j/machine ctx)]
    (try
      (is (= 4 (count originals))) (is (= (:fixture-sha256 manifest) (corpus/sha256 fixture)))
      (doseq [row [(originals 0) (originals 2)]]
        (is (= [{"borrow" false "ty" "tagged" "x" {"idx" 1}}] (get-in row ["ir" "extern" "xs"])))
        (is (string? (j/invoke-static (.getMethod ^Class (:class ctx) "validateExternAbi" (into-array Class [java.util.Map])) [row]))))
      (doseq [[label value] expected]
        (is (= value (j/call ctx engine label [0])))
        (is (= value (j/call ctx engine (str label "._boxed") [0]))))
      (is (= [0 0 0 0 0] (counters engine)))
      (finally (j/close! ctx engine)))))

(deftest default-constructors-do-not-infer-profile
  (doseq [initializing [false true]]
    (let [ctx (assoc (context) :initializing initializing) engine (j/machine ctx)]
      (try
        (doseq [label (keys expected)] (is (g/bad? #(j/call ctx engine label [0]))))
        (is (= [0 0 0 0 0] (counters engine)))
        (j/install-program! ctx engine)
        (is (g/bad? #(j/call ctx engine "Lean.getGithash" [0])))
        (is (= initializing (j/initializing? ctx engine)))
        (finally (j/close! ctx engine))))))

(deftest invalid-root-unit-is-preentry-and-engine-remains-usable
  (let [maker (c/decl "payload" [(c/p 1 "object")] "object"
                (c/let-ir 2 "object" (c/ctor 7 [(c/v 1)] 0) (c/ret 2)))
        ctx (enabled (context [maker])) engine (j/machine ctx)
        value (j/call ctx engine "payload" [7])]
    (try
      (doseq [unit [1 -1 Long/MAX_VALUE "unit" java.math.BigInteger/ZERO value nil]]
        (let [before (counters engine)]
          (is (g/bad? #(j/call ctx engine "Lean.getGithash" [unit])))
          (is (= before (counters engine))) (is (= 1 (c/rc ctx value)))))
      (is (= (expected "Lean.getGithash") (j/call ctx engine "Lean.getGithash" [0])))
      (finally (j/release! ctx engine value) (j/close! ctx engine)))))

(deftest forks-inherit-profile-with-independent-initialization
  (let [ctx (assoc (enabled (context)) :initializing true) parent (j/machine ctx)
        child (:engine (j/fork! ctx parent []))]
    (try
      (j/finish-initialization! ctx child)
      (is (true? (j/initializing? ctx parent))) (is (false? (j/initializing? ctx child)))
      (is (identical? (host/private-value parent "buildIdentity") (host/private-value child "buildIdentity")))
      (doseq [[label value] expected]
        (is (= value (j/call ctx parent (str label "._boxed") [0]) (j/call ctx child label [0]))))
      (finally (j/close! ctx parent) (j/close! ctx child)))))

(deftest guest-ap-and-cache-preserve-string-result
  (let [call (c/decl "apply-unit" [(c/p 1 "object") (c/p 2 "object")] "object"
               ["vdecl" {:idx 3} "object" {:ap {:x {:idx 1} :ys [{:var {:id {:idx 2}}}]}} (c/ret 3)])
        constant (c/decl "build-constant" [] "object"
                   ["vdecl" {:idx 1} "tagged" (c/lit 0)
                    ["vdecl" {:idx 2} "object" {:fap {:c (get-in (first originals) ["name"]) :ys [{:var {:id {:idx 1}}}]}} (c/ret 2)]])
        ctx (enabled (context [call constant])) engine (j/machine ctx)]
    (try
      (doseq [[label value] expected]
        (let [closure (j/make-closure! ctx engine label [])]
          (is (= value (j/call ctx engine "apply-unit" [closure 0])))
          (is (host/private-value closure "dead"))))
      (is (= (expected "Lean.getGithash") (j/call ctx engine "build-constant" [])))
      (is (= (expected "Lean.getGithash") (j/call ctx engine "build-constant" [])))
      (finally (j/close! ctx engine)))))

(deftest invalid-ap-unit-preserves-unconsumed-closure-credit
  (let [call (c/decl "bad-apply" [(c/p 1 "object") (c/p 2 "object")] "object"
               (c/let-ir 3 "object" {:ap {:x {:idx 1} :ys [(c/v 2)]}} (c/ret 3)))
        ctx (enabled (context [call])) engine (j/machine ctx)
        closure (j/make-closure! ctx engine "Lean.getGithash" []) before (counters engine)]
    (is (g/bad? #(j/call ctx engine "bad-apply" [closure 1])))
    (is (= before (counters engine)))
    (is (= 1 (c/rc ctx closure))) (is (false? (host/private-value closure "dead")))
    ;; Guest failure is terminal; the caller still owns this unconsumed input.
    (j/release! ctx engine closure)
    (if (:explicit ctx)
      (is (g/bad? #(j/close! ctx engine)))
      (j/close! ctx engine))))

(deftest demand-code-fork-and-descendant-install-preserve-profile
  (when (:explicit *basis*)
    (let [base (j/prepare-host-program *basis* [] []) binding (j/source-binding base (Object.))
          root (h/header binding (originals 0)) wrapper (h/header binding (originals 1))
          ctx (enabled (j/register-headers base [root wrapper]))
          ready (j/materialize-body ctx wrapper (originals 1) [root])
          parent (j/machine ctx)]
      (j/start! ctx parent "Lean.getGithash._boxed" [0])
      (let [request (j/code-request ctx parent) child (:engine (j/fork! ctx parent []))]
        (try
          (is (= "code-call" (j/phase ctx parent) (j/phase ctx child)))
          (is (identical? (host/private-value parent "buildIdentity") (:build-identity ctx)))
          (j/resume-code! ready parent request)
          (j/install-program! ready child)
          (j/resume-code! ready child (j/code-request ready child))
          (is (= (expected "Lean.getGithash") (code/finish! ready parent) (code/finish! ready child)))
          (is (identical? (host/private-value child "buildIdentity") (:build-identity ctx)))
          (finally (j/close! ready parent) (j/close! ready child)))))))

(deftest host-reply-string-transport-and-profile-do-not-interfere
  (when (:explicit *basis*)
    (let [spec (host/spec "research_build_identity" ["object"] [true] "object")
          ctx (enabled (j/prepare-host-program *basis*
                         (x/raw (concat originals [(host/ext "host" spec)])) [spec]))
          engine (j/machine ctx)]
      (try
        (let [value (j/call ctx engine "System.Platform.getTarget._boxed" [0])]
          (j/start! ctx engine "host" [value])
          (let [request (j/host-request ctx engine)]
            (is (= [value] (host/args request)))
            (j/resume-host! ctx engine request value)
            (is (= value (j/take-result! ctx engine)))))
        (is (= (expected "Lean.getGithash") (j/call ctx engine "Lean.getGithash" [0])))
        (is (= [0 0 0 0 0] (counters engine)))
        (finally (j/close! ctx engine))))))

(defn check! [basis] (binding [*basis* basis] (run-tests 'java-ir-build-identity-checks)))
