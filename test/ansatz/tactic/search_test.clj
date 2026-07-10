(ns ansatz.tactic.search-test
  (:require [clojure.data.json :as json]
            [clojure.string :as str]
            [clojure.test :refer [deftest is testing]]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.name :as name]
            [ansatz.tactic.proof :as proof]
            [ansatz.tactic.search :as search]
            [ansatz.tactic.trace :as trace]))

(def prop (e/sort' lvl/zero))

(defn- prop-id-goal []
  ;; ∀ (a : Prop), a → a
  (e/forall' "a" prop
             (e/forall' "h" (e/bvar 0) (e/bvar 1) :default)
             :default))

(defn- premise-index [& cis]
  {:kind :ansatz.tactic/premise-index
   :entries (mapv search/premise-index-entry cis)})

(deftest best-first-search-solves-and-verifies
  (testing "policy search solves Prop identity and records a replayable path"
    (let [[ps _] (proof/start-proof (env/empty-env) (prop-id-goal))
          result (search/best-first-search ps {:max-steps 20
                                               :beam-width 4
                                               :verify? true})]
      (is (= :solved (:status result)))
      (is (proof/solved? (:ps result)))
      (is (some? (:proof result)))
      (is (= [:intro :intro :assumption]
             (mapv #(get-in % [:name]) (:path result))))
      (is (seq (:transitions result)))
      (is (every? #(contains? % :before) (:transitions result)))
      (is (every? #(contains? % :action) (:transitions result))))))

(deftest best-first-search-keeps-failed-action-records
  (testing "failed proposals become training data while other branches continue"
    (let [[ps _] (proof/start-proof (env/empty-env) (prop-id-goal))
          bad (search/make-action :bad
                                  (fn [_]
                                    (throw (ex-info "synthetic proposal failure"
                                                    {:reason :test})))
                                  {:prior 0.99
                                   :source :test})
          proposer (fn [ps node opts]
                     (into [bad] (search/default-proposer ps node opts)))
          result (search/best-first-search ps {:max-steps 20
                                               :beam-width 4
                                               :proposer proposer
                                               :verify? true})]
      (is (= :solved (:status result)))
      (is (some #(and (= :error (:status %))
                      (= :bad (get-in % [:action :name]))
                      (= :test (get-in % [:error :data :reason])))
                (:transitions result))))))

(deftest theorem-proposer-solves-from-env-premise
  (testing "environment constants can propose exact/apply actions"
    (let [p-name (name/from-string "p")
          env (env/add-constant (env/empty-env) (env/mk-axiom p-name [] prop))
          [ps _] (proof/start-proof env prop)
          result (search/best-first-search ps {:max-steps 4
                                               :beam-width 4
                                               :proposer search/theorem-proposer
                                               :premise-limit 8
                                               :verify? true})]
      (is (= :solved (:status result)))
      (is (proof/solved? (:ps result)))
      (is (= :exact-const (get-in result [:path 0 :name])))
      (is (= ["p"] (get-in result [:path 0 :args]))))))

(deftest premise-candidates-are-scored
  (testing "exact target-type matches rank ahead of unrelated constants"
    (let [p-name (name/from-string "p")
          q-name (name/from-string "q")
          env (-> (env/empty-env)
                  (env/add-constant (env/mk-axiom q-name [] (e/forall' "a" prop (e/bvar 0) :default)))
                  (env/add-constant (env/mk-axiom p-name [] prop)))
          [ps _] (proof/start-proof env prop)
          ranked (search/ranked-premise-candidates ps)
          actions (search/theorem-proposer ps nil {:premise-limit 1})]
      (is (= "p" (:name (first ranked))))
      (is (> (:score (first ranked)) (:score (second ranked))))
      (is (= [:exact-const :apply-const]
             (mapv :name actions)))
      (is (= [["p"] ["p"]]
             (mapv :args actions))))))

(deftest premise-index-can-be-installed-on-proof-state
  (testing "premise facts can be cached as env extension state"
    (let [p-ci (env/mk-axiom (name/from-string "p") [] prop)
          q-ci (env/mk-axiom (name/from-string "q") [] prop)
          env (-> (env/empty-env)
                  (env/add-constant p-ci)
                  (env/add-constant q-ci))
          idx (search/build-premise-index env {:premise-tags #{:axiom}})
          [ps _] (proof/start-proof env prop)
          indexed-ps (search/index-proof-state ps {:premise-tags #{:axiom}})
          installed (env/get-extension (:env indexed-ps) search/premise-index-extension-key)]
      (is (= #{"p" "q"} (set (map :name-string (:entries idx)))))
      (is (= :ansatz.tactic/premise-index (:kind installed)))
      (is (= #{"p" "q"} (set (map :name-string (:entries installed)))))
      (is (= #{"p" "q"} (set (map :name (search/ranked-premise-candidates indexed-ps))))))))

(deftest theorem-proposer-uses-premise-index-extension
  (testing "an env-attached index can narrow theorem proposal without rescanning"
    (let [p-ci (env/mk-axiom (name/from-string "p") [] prop)
          q-ci (env/mk-axiom (name/from-string "q") [] prop)
          env (-> (env/empty-env)
                  (env/add-constant p-ci)
                  (env/add-constant q-ci)
                  (env/with-extension search/premise-index-extension-key
                                      (premise-index q-ci)))
          [ps _] (proof/start-proof env prop)
          actions (search/theorem-proposer ps nil {:premise-limit 1})]
      (is (= [:exact-const :apply-const] (mapv :name actions)))
      (is (= [["q"] ["q"]] (mapv :args actions))))))

(deftest theorem-proposer-explicit-premise-index-overrides-env-extension
  (testing "call-site policy can replace the env-indexed premise view"
    (let [p-ci (env/mk-axiom (name/from-string "p") [] prop)
          q-ci (env/mk-axiom (name/from-string "q") [] prop)
          env (-> (env/empty-env)
                  (env/add-constant p-ci)
                  (env/add-constant q-ci)
                  (env/with-extension search/premise-index-extension-key
                                      (premise-index p-ci)))
          [ps _] (proof/start-proof env prop)
          actions (search/theorem-proposer ps nil {:premise-index (premise-index q-ci)
                                                   :premise-limit 1})]
      (is (= [:exact-const :apply-const] (mapv :name actions)))
      (is (= [["q"] ["q"]] (mapv :args actions))))))

(deftest theorem-proposer-instantiates-polymorphic-premise
  (testing "candidate levels can be inferred from the current goal"
    (let [u-name (name/from-string "u")
          poly-id-name (name/from-string "polyId")
          poly-id-type (e/forall' "α" (e/sort' (lvl/param u-name))
                                  (e/forall' "x" (e/bvar 0) (e/bvar 1) :default)
                                  :default)
          env (env/add-constant (env/empty-env)
                                (env/mk-axiom poly-id-name [u-name] poly-id-type))
          [ps _] (proof/start-proof env (prop-id-goal))
          ranked (search/ranked-premise-candidates ps)
          result (search/best-first-search ps {:max-steps 4
                                               :beam-width 4
                                               :proposer search/theorem-proposer
                                               :premise-limit 1
                                               :verify? true})]
      (is (= "polyId" (:name (first ranked))))
      (is (= [lvl/zero] (:levels (first ranked))))
      (is (= :solved (:status result)))
      (is (= :exact-const (get-in result [:path 0 :name])))
      (is (= ["polyId"] (get-in result [:path 0 :args]))))))

(deftest search-result-serializes-to-json-records
  (testing "policy-search traces are JSON/NDJSON friendly"
    (let [[ps _] (proof/start-proof (env/empty-env) (prop-id-goal))
          result (search/best-first-search ps {:max-steps 20
                                               :beam-width 4
                                               :verify? true})
          serialized (trace/serialize-search-result result)
          transition (trace/serialize-search-transition (first (:transitions result)))
          tmp (java.io.File/createTempFile "ansatz-search-" ".ndjson")]
      (is (= "solved" (get serialized "status")))
      (is (vector? (get serialized "transitions")))
      (is (= "ok" (get transition "status")))
      (trace/write-search-transitions-ndjson (.getPath tmp) result)
      (let [lines (remove str/blank? (str/split-lines (slurp tmp)))
            first-line (json/read-str (first lines))]
        (is (= (count (:transitions result)) (count lines)))
        (is (= "ok" (get first-line "status")))
        (is (contains? first-line "before"))))))
