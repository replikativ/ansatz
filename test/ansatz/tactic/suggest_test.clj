(ns ansatz.tactic.suggest-test
  "Tests for LLM tactic suggestion, trace export, and prompt formatting."
  (:require [clojure.test :refer [deftest testing is]]
            [clojure.data.json :as json]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]
            [ansatz.tactic.proof :as proof]
            [ansatz.tactic.basic :as basic]
            [ansatz.tactic.trace :as trace]
            [ansatz.tactic.suggest :as suggest]
            [ansatz.tactic.llm :as llm]
            [ansatz.export.parser :as parser]
            [ansatz.export.replay :as replay]))

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

;; LLM integration tests removed — require external API key.
;; Re-enable by setting FIREWORKS_API_KEY or OPENAI_API_KEY env var
;; and uncommenting the tests in this section.
