(ns java-ir-initialization-checks
  "Native boot flag, distinct from guest importing refs and module guards."
  (:require [clojure.test :refer [deftest is run-tests]]
            [clojure.data.json :as json] [clojure.edn :as edn]
            [java-ir-baseline :as j] [java-ir-baseline-checks :as c]
            [java-ir-extern-checks :as x] [java-ir-generation-checks :as g]
            [java-ir-header-checks :as h] [java-ir-code-checks :as code]
            [java-ir-host-checks :as host] [lean-compatibility-corpus :as corpus]))
(def ^:dynamic *basis* nil)
(def fixture "test/fixtures/java-initialization-runtime/original-rows.json")
(defn originals [] (json/read-str (slurp fixture)))
(defn context []
  (assoc *basis* :program (j/invoke-static (:prepare *basis*)
                          [(into (mapv #(get % "row") (originals)) (x/raw [(first g/common)]))])))
(defn query [ctx engine] (j/call ctx engine "IO.initializing._boxed" [0]))

(deftest exact-source-query-defaults-to-ordinary-and-completes-one-way
  (let [manifest (edn/read-string (slurp "test/fixtures/java-initialization-runtime/provenance.edn"))
        ctx (context)]
    (is (= (:fixture-sha256 manifest) (corpus/sha256 fixture)))
    (is (= 2 (count (originals))))
    (doseq [mode [false true] :let [ctx (assoc ctx :initializing mode) engine (j/machine ctx)]]
      (try
        (is (= mode (j/initializing? ctx engine)))
        (is (= (if mode 1 0) (query ctx engine)))
        (j/finish-initialization! ctx engine)
        (is (false? (j/initializing? ctx engine)))
        (is (= 0 (query ctx engine)))
        (j/finish-initialization! ctx engine)
        (is (= 0 (query ctx engine)))
        (finally (j/close! ctx engine))))))

(deftest fork-initialization-completion-is-branch-local
  (let [ctx (assoc (context) :initializing true) parent (j/machine ctx)
        child (:engine (j/fork! ctx parent []))]
    (try
      (is (= 1 (query ctx parent) (query ctx child)))
      (j/finish-initialization! ctx child)
      (is (= 1 (query ctx parent))) (is (= 0 (query ctx child)))
      (let [grandchild (:engine (j/fork! ctx child []))]
        (try (is (= 0 (query ctx grandchild))) (finally (j/close! ctx grandchild))))
      (finally (j/close! ctx parent) (j/close! ctx child)))))

(deftest graph-and-code-generation-installation-do-not-infer-runtime-phase
  (doseq [mode [false true]
          :let [ctx (assoc (context) :initializing mode) engine (j/machine ctx)
                source (j/source-binding ctx (Object.))
                next (j/extend-program ctx (x/raw [(g/literal "later" 42)]))]]
    (try
      (is (= [] (j/install-graph! ctx engine (j/prepared-graph ctx source (Object.) [] [] [] []))))
      (is (= mode (j/initializing? ctx engine)))
      (j/install-program! next engine)
      (is (= mode (j/initializing? next engine)))
      (is (= (if mode 1 0) (query next engine)))
      (finally (j/close! next engine)))))

(deftest running-and-unclaimed-result-boundaries-reject-phase-completion
  (let [ctx (assoc (context) :explicit true :initializing true) engine (j/machine ctx)]
    (try
      (j/start! ctx engine "identity" [42])
      (is (g/bad? #(j/finish-initialization! ctx engine)))
      (is (true? (j/initializing? ctx engine)))
      (j/advance! ctx engine 100)
      (is (= "complete" (j/phase ctx engine)))
      (is (g/bad? #(j/finish-initialization! ctx engine)))
      (is (= 42 (j/take-result! ctx engine)))
      (is (= 1 (query ctx engine)))
      (j/finish-initialization! ctx engine) (is (= 0 (query ctx engine)))
      (finally (j/close! ctx engine)))))

(deftest pending-code-request-forks-phase-and-rejects-premature-completion
  (let [base (j/prepare-host-program (assoc *basis* :explicit true :initializing true) [] [])
        source (j/source-binding base (Object.)) target (h/header source h/identity-row)
        ctx (j/register-headers base [target]) engine (j/machine ctx)
        ready (code/materialize ctx target h/identity-row [])]
    (try
      (j/start! ctx engine "identity" [42])
      (let [request (code/request! ctx engine) child (:engine (j/fork! ctx engine []))]
        (try
          (is (g/bad? #(j/finish-initialization! ctx engine)))
          (is (true? (j/initializing? ctx child)))
          (j/resume-code! ready child (j/code-request ctx child))
          (is (= 42 (code/finish! ready child)))
          (j/finish-initialization! ready child)
          (is (false? (j/initializing? ready child)))
          (is (true? (j/initializing? ctx engine)))
          (j/resume-code! ready engine request) (is (= 42 (code/finish! ready engine)))
          (is (true? (j/initializing? ready engine)))
          (finally (j/close! ready child))))
      (finally (j/close! ready engine)))))

(deftest host-suspension-closed-and-failed-engines-preserve-phase
  (let [ctx (j/prepare-host-program (assoc *basis* :initializing true)
              (x/raw [(host/ext "phase-host" host/owned)]) [host/owned])
        engine (j/machine ctx)]
    (try
      (j/start! ctx engine "phase-host" [42])
      (is (g/bad? #(j/finish-initialization! ctx engine)))
      (is (true? (j/initializing? ctx engine)))
      (j/resume-host! ctx engine (j/host-request ctx engine) 42)
      (is (= 42 (j/take-result! ctx engine)))
      (is (true? (j/initializing? ctx engine)))
      (finally (j/close! ctx engine)))
    (is (g/bad? #(j/finish-initialization! ctx engine)))
    (is (true? (j/initializing? ctx engine))))
  (let [ctx (assoc (context) :initializing true) engine (j/machine ctx)]
    (is (g/bad? #(j/call ctx engine "IO.initializing" [42])))
    (is (g/bad? #(j/finish-initialization! ctx engine)))
    (is (true? (j/initializing? ctx engine)))))
(defn check! [basis] (binding [*basis* basis] (run-tests 'java-ir-initialization-checks)))
