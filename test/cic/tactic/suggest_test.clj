(ns cic.tactic.suggest-test
  "Tests for LLM tactic suggestion, trace export, and prompt formatting."
  (:require [clojure.test :refer [deftest testing is]]
            [clojure.data.json :as json]
            [cic.kernel.expr :as e]
            [cic.kernel.env :as env]
            [cic.kernel.name :as name]
            [cic.kernel.level :as lvl]
            [cic.tactic.proof :as proof]
            [cic.tactic.basic :as basic]
            [cic.tactic.trace :as trace]
            [cic.tactic.suggest :as suggest]
            [cic.tactic.llm :as llm]
            [cic.export.parser :as parser]
            [cic.export.replay :as replay]))

(def prop (e/sort' lvl/zero))

(defn- minimal-env [] (env/empty-env))

(def ^:private init-medium-env
  (delay
    (let [f "test-data/init-medium.ndjson"]
      (when (.exists (java.io.File. f))
        (let [st (parser/parse-ndjson-file f)
              result (replay/replay (:decls st))]
          (:env result))))))

(defn- require-init-medium []
  (or @init-medium-env
      (throw (ex-info "init-medium.ndjson not found" {}))))

;; ============================================================
;; Trace export tests
;; ============================================================

(deftest test-goal-serialization
  (testing "serialize-goal produces expected structure"
    (let [env (minimal-env)
          goal-type (e/forall' "a" prop (e/forall' "h" (e/bvar 0) (e/bvar 1) :default) :default)
          [ps _] (proof/start-proof env goal-type)
          ps (basic/intro ps "a")
          goal (proof/current-goal ps)
          serialized (trace/serialize-goal goal)]
      (is (some? serialized))
      (is (string? (:type serialized)))
      (is (vector? (:hypotheses serialized)))
      (is (= 1 (count (:hypotheses serialized))))
      (is (= "a" (:name (first (:hypotheses serialized))))))))

(deftest test-proof-trace-serialization
  (testing "serialize-proof-trace captures full proof"
    (let [env (minimal-env)
          goal-type (e/forall' "a" prop (e/forall' "h" (e/bvar 0) (e/bvar 1) :default) :default)
          [ps _] (proof/start-proof env goal-type)
          ps (-> ps (basic/intro "a") (basic/intro "h") basic/assumption)
          trace-map (trace/serialize-proof-trace ps)]
      (is (:solved trace-map))
      (is (= 3 (:num-steps trace-map)))
      (is (= 3 (count (:steps trace-map))))
      (is (= "intro" (:tactic (first (:steps trace-map)))))
      ;; Should be valid JSON
      (is (string? (json/write-str trace-map))))))

(deftest test-ndjson-roundtrip
  (testing "write and read trace NDJSON"
    (let [env (minimal-env)
          goal-type (e/forall' "a" prop (e/forall' "h" (e/bvar 0) (e/bvar 1) :default) :default)
          [ps _] (proof/start-proof env goal-type)
          ps (-> ps (basic/intro "a") (basic/intro "h") basic/assumption)
          path (str (System/getProperty "java.io.tmpdir") "/test-trace.ndjson")]
      (trace/write-trace-ndjson path ps)
      (let [content (slurp path)
            parsed (json/read-str content :key-fn keyword)]
        (is (:solved parsed))
        (is (= 3 (:num-steps parsed)))))))

;; ============================================================
;; Prompt formatting tests
;; ============================================================

(deftest test-goal-prompt
  (testing "goal->prompt formats correctly"
    (let [env (minimal-env)
          goal-type (e/forall' "a" prop (e/forall' "h" (e/bvar 0) (e/bvar 1) :default) :default)
          [ps _] (proof/start-proof env goal-type)
          ps (basic/intro ps "a")
          goal (proof/current-goal ps)
          prompt (trace/goal->prompt goal)]
      (is (string? prompt))
      (is (clojure.string/includes? prompt "Hypotheses:"))
      (is (clojure.string/includes? prompt "Goal:"))
      (is (clojure.string/includes? prompt "a :")))))

(deftest test-proof-state-prompt
  (testing "proof-state->prompt includes goal count"
    (let [env (minimal-env)
          goal-type (e/forall' "a" prop (e/forall' "h" (e/bvar 0) (e/bvar 1) :default) :default)
          [ps _] (proof/start-proof env goal-type)
          prompt (trace/proof-state->prompt ps)]
      (is (clojure.string/includes? prompt "1 goal remaining")))))

;; ============================================================
;; Suggestion parsing tests
;; ============================================================

(deftest test-parse-suggestions
  (testing "parse plain JSON array"
    (let [response "[{\"tactic\": \"intro\", \"args\": [\"a\"], \"confidence\": 0.9}]"
          suggestions (suggest/parse-suggestions response)]
      (is (= 1 (count suggestions)))
      (is (= :intro (:name (first suggestions))))
      (is (= ["a"] (:args (first suggestions))))
      (is (= 0.9 (:weight (first suggestions))))))

  (testing "parse with markdown fences"
    (let [response "```json\n[{\"tactic\": \"rfl\", \"args\": [], \"confidence\": 0.95}]\n```"
          suggestions (suggest/parse-suggestions response)]
      (is (= 1 (count suggestions)))
      (is (= :rfl (:name (first suggestions))))))

  (testing "parse multiple suggestions sorted by weight"
    (let [response "[{\"tactic\": \"intro\", \"confidence\": 0.5}, {\"tactic\": \"rfl\", \"confidence\": 0.9}]"
          suggestions (suggest/parse-suggestions response)]
      (is (= 2 (count suggestions)))
      (is (= :rfl (:name (first suggestions))))
      (is (= :intro (:name (second suggestions))))))

  (testing "parse garbage returns nil"
    (is (nil? (suggest/parse-suggestions "I don't know what to do")))
    (is (nil? (suggest/parse-suggestions "")))))

;; ============================================================
;; LLM integration test (only runs with API key)
;; ============================================================

(deftest ^:llm test-llm-suggest-prop-identity
  (testing "LLM suggests intro for forall goal"
    (if-let [api-key (or (System/getenv "FIREWORKS_API_KEY")
                           (System/getenv "OPENAI_API_KEY"))]
      (try
        (let [config (llm/make-config {:api-key api-key})
              env (minimal-env)
              goal-type (e/forall' "a" prop
                          (e/forall' "h" (e/bvar 0) (e/bvar 1) :default) :default)
              [ps _] (proof/start-proof env goal-type)
              suggestions (suggest/suggest-tactics config ps)]
          (is (seq suggestions))
          ;; Should suggest intro since the goal is a forall
          (is (some #(= :intro (:name %)) suggestions)))
        (catch clojure.lang.ExceptionInfo e
          (if (= 401 (:status (ex-data e)))
            (println "Skipping: API key not authorized for Fireworks")
            (throw e))))
      (println "Skipping LLM test: no API key set"))))

(deftest ^:llm test-llm-suggest-and-apply
  (testing "LLM suggestions can be applied"
    (if-let [api-key (or (System/getenv "FIREWORKS_API_KEY")
                           (System/getenv "OPENAI_API_KEY"))]
      (try
        (let [config (llm/make-config {:api-key api-key})
              env (minimal-env)
              goal-type (e/forall' "a" prop
                          (e/forall' "h" (e/bvar 0) (e/bvar 1) :default) :default)
              [ps _] (proof/start-proof env goal-type)
              results (suggest/suggest-and-apply config ps)]
          (is (seq results))
          ;; At least one suggestion should successfully apply
          (is (some #(some? (:ps %)) results)))
        (catch clojure.lang.ExceptionInfo e
          (if (= 401 (:status (ex-data e)))
            (println "Skipping: API key not authorized for Fireworks")
            (throw e))))
      (println "Skipping LLM test: no API key set"))))

(deftest ^:llm test-llm-beam-search
  (testing "LLM-guided beam search solves simple proof"
    (if-let [api-key (or (System/getenv "FIREWORKS_API_KEY")
                           (System/getenv "OPENAI_API_KEY"))]
      (let [config (llm/make-config {:api-key api-key})
            env (minimal-env)
            goal-type (e/forall' "a" prop
                        (e/forall' "h" (e/bvar 0) (e/bvar 1) :default) :default)
            [ps _] (proof/start-proof env goal-type)
            result (suggest/llm-beam-search config ps 3 10 :verbose true)]
        (is (some? result))
        (is (proof/solved? result)))
      (println "Skipping LLM test: FIREWORKS_API_KEY not set"))))

(deftest ^:llm test-llm-nat-eq-with-init-medium
  (testing "LLM proves ∀ (a : Nat), a = a"
    (if-let [api-key (or (System/getenv "FIREWORKS_API_KEY")
                           (System/getenv "OPENAI_API_KEY"))]
      (let [config (llm/make-config {:api-key api-key})
            env (require-init-medium)
            nat (e/const' (name/from-string "Nat") [])
            u1 (lvl/succ lvl/zero)
            eq-name (name/from-string "Eq")
            eq-aa (e/app* (e/const' eq-name [u1]) nat (e/bvar 0) (e/bvar 0))
            goal-type (e/forall' "a" nat eq-aa :default)
            [ps _] (proof/start-proof env goal-type)
            result (suggest/llm-beam-search config ps 3 10 :verbose true)]
        (is (some? result))
        (when result
          (is (proof/solved? result))))
      (println "Skipping LLM test: FIREWORKS_API_KEY not set"))))
