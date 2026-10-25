(ns prototype.coherent-consumer-profile-test
  "Pure host contract/routing tests. Model hashes are not loaded-code evidence.
   No guest execution, restore, native readiness query or kernel admission."
  (:require [clojure.test :refer [deftest is testing]]
            [clojure.edn :as edn]
            [clojure.java.io :as io]
            [prototype.checkpoint-wire :as wire]
            [prototype.globals-consumer-profile :as old]
            [prototype.coherent-consumer-profile :as coherent]
            [prototype.globals-consumer-factory :as factory]
            [prototype.restore-consumer :as restore]))

(def a (apply str (repeat 64 "a")))
(def b (apply str (repeat 64 "b")))
(def member-kinds
  {"prototype/coherent_consumer_profile.clj" :host-source
   "prototype/globals_consumer_profile.clj" :host-source
   "prototype/globals_consumer_factory.clj" :host-source
   "prototype/restore_consumer.clj" :host-source
   "controller/prepare.clj" :host-source
   "src-java/ansatz/kernel/TypeChecker.java" :host-source
   "src-java/ansatz/kernel/Env.java" :host-source
   "src-java/ansatz/kernel/Expr.java" :host-source
   "ansatz/kernel/TypeChecker.class" :kernel-class
   "ansatz/kernel/Env.class" :kernel-class
   "ansatz/kernel/Expr.class" :kernel-class})
(def inventory (mapv (fn [[id kind]] {:id id :kind kind :sha256 a}) (sort-by key member-kinds)))
(def target ["str" ["str" ["anonymous"] "KernelCasesOnRaw"] "mkCasesOn"])
(defn contract-for [rows]
  {:schema coherent/schema :profile coherent/profile-id
   :producer {:implementation-sha256 old/producer-implementation-sha256
              :recipe-sha256 old/producer-recipe-sha256}
   :lean-commit coherent/lean-commit :target coherent/target
   :inventory rows :implementation-sha256 (old/consumer-identity rows)
   :kernel-policy coherent/kernel-policy
   :limits {:max-helper-bytes 1048576 :max-helper-declarations 1000 :checker-fuel 1000000}
   :composition {:controllers [{:id "controller/prepare.clj" :entrypoints ["controller.prepare/prepare"]}]
                 :helpers [{:id "cases-on" :source-id "helpers/KernelCasesOnRaw.lean" :source-sha256 a
                            :ir-id "helpers/cases-on.ndjson" :ir-sha256 b :entrypoints ["KernelCasesOnRaw.mkCasesOn"]}]
                 :redirects [{:symbol "lean_mk_cases_on" :target target :row-sha256 coherent/cases-on-original-row-sha256}]
                 :stages [:fresh-init :ordinary-helpers :cases-on :seal :project :typed-io
                          :ordinary-module :chain :diamond :reload]}})
(def contract (contract-for inventory))
(defn valid! [contract]
  (coherent/validate-contract! contract (:implementation-sha256 contract)))
(defn text-digest [text] (wire/sha256 (.getBytes ^String text java.nio.charset.StandardCharsets/UTF_8)))

(deftest reviewed-build-data-has-one-stable-contract-schema
  (is (identical? contract (valid! contract)))
  (let [rows (conj inventory {:id "prototype/new_feature.clj" :kind :host-source :sha256 b})
        next (contract-for rows)]
    (is (= coherent/profile-id (:profile (valid! next))))
    (is (= coherent/schema (:schema next)))
    (is (not= (:implementation-sha256 next) (:implementation-sha256 contract)))
    (is (thrown? clojure.lang.ExceptionInfo
                 (coherent/validate-contract! next (:implementation-sha256 contract)))))
  (let [recipe (edn/read-string (slurp (io/resource "fixtures/producer50f-catalogue-recipe.edn")))]
    ;; The new manifest's selected domain cannot bypass the old closed profile.
    (is (thrown? clojure.lang.ExceptionInfo
                 (old/validate-hosted-application-control-inventory!
                  recipe inventory (:implementation-sha256 contract))))))

(deftest unknown-fields-policy-drift-and-incomplete-members-reject
  (doseq [bad [(assoc contract :arbitrary-callback 'evaluate)
               (assoc contract :profile old/hosted-application-control-profile-id)
               (assoc-in contract [:producer :implementation-sha256] a)
               (assoc-in contract [:producer :unknown] true)
               (assoc contract :lean-commit a)
               (assoc-in contract [:target :word-bits] 32)
               (assoc-in contract [:kernel-policy :allow-nested?] true)
               (assoc-in contract [:limits :checker-fuel] 0)
               (assoc-in contract [:limits :unknown] 1)
               (assoc-in contract [:composition :controllers 0 :id] "missing.clj")
               (assoc-in contract [:composition :helpers 0 :unknown] "ignored")
               (assoc-in contract [:composition :helpers] [])
               (assoc-in contract [:composition :redirects 0 :symbol] "lean_elab_add_decl")
               (assoc-in contract [:composition :redirects 0 :target] ["invented"])
               (assoc-in contract [:composition :stages] [:fresh-init :seal :cases-on])
               (contract-for (vec (remove #(= "src-java/ansatz/kernel/Env.java" (:id %)) inventory)))
               (contract-for (conj inventory {:id "../escape.clj" :kind :host-source :sha256 a}))
               (contract-for (conj inventory {:id "prototype/finalizer_checkpoint.clj" :kind :host-source :sha256 a}))]]
    (is (thrown? clojure.lang.ExceptionInfo (valid! bad)))))

(deftest external-pin-precedes-parsing-and-all-resolvers
  (let [text (pr-str contract)]
    (is (= contract (coherent/read-contract! text (text-digest text))))
    (doseq [bad ["#=(System/exit 1)" "#unknown/thing {}" "{} {}"
                 (str (apply str (repeat 257 "[")) (apply str (repeat 257 "]")))]]
      (is (thrown? clojure.lang.ExceptionInfo
                   (coherent/read-contract! bad (text-digest bad)))))
    (let [reads (atom [])
          options (zipmap coherent/option-keys (repeat nil))
          options (assoc options :consumer-contract-source "not even valid EDN ["
                         :expected-consumer-contract-sha256 a
                         :producer-resolve-artifact #(swap! reads conj [:producer %])
                         :consumer-resolve-source #(swap! reads conj [:consumer %]))]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"external contract digest"
                            (coherent/authenticate! options)))
      (is (empty? @reads)))))

(deftest complete-inventory-and-loaded-attestation-are-independent-required-inputs
  (let [text (pr-str contract)
        base (assoc (zipmap coherent/option-keys (repeat nil))
                    :consumer-contract-source text :expected-consumer-contract-sha256 (text-digest text)
                    :expected-consumer-implementation-sha256 (:implementation-sha256 contract)
                    :loaded-consumer-implementation-sha256 (:implementation-sha256 contract)
                    :consumer-inventory inventory :store-root "model-store")
        reads (atom [])
        base (assoc base :consumer-resolve-source #(swap! reads conj [:consumer %])
                    :producer-resolve-artifact #(swap! reads conj [:producer %]))]
    (doseq [options [(assoc base :loaded-consumer-implementation-sha256 a)
                     (assoc base :consumer-inventory [])
                     (assoc base :skip-authentication? true)]]
      (is (thrown? clojure.lang.ExceptionInfo (coherent/authenticate! options))))
    (is (empty? @reads))))

(deftest second-factory-gate-checks-producer-originals-and-current-classes-separately
  ;; Private gate is tested with bounded hash/resolver models. Actual CodeSource,
  ;; class loading and fresh-process bootstrap remain separate execution gates.
  (let [producer-rows [{:id "ansatz/kernel/Env.class" :kind :kernel-class :sha256 a}
                       {:id "producer/original.clj" :kind :host-source :sha256 a}]
        recipe {:build-inventory producer-rows}
        preparation {:implementation-sha256 (factory/build-identity producer-rows)}
        current [{:id "ansatz/kernel/Env.class" :kind :kernel-class :sha256 b}]
        reads (atom []) loaded (atom [])
        resolver (fn [id] (swap! reads conj id) [:original id])
        run (fn [producer-hash loaded-hash]
              (with-redefs-fn {#'wire/file-sha256 (fn [[cohort _]]
                                                 (is (= :original cohort)) producer-hash)
                              #'factory/loaded-kernel-class-sha256!
                              (fn [id] (swap! loaded conj id) loaded-hash)}
                #(#'factory/authenticate-coherent-build! recipe preparation resolver current)))]
    (is (nil? (run a b)))
    (is (= (set (map :id producer-rows)) (set @reads)))
    (is (= ["ansatz/kernel/Env.class"] @loaded))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"original producer" (run b b)))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"loaded kernel class" (run a a)))))

(deftest restore-recognizes-only-issued-description-with-exact-identities
  (let [producer {:model :producer} digest (:implementation-sha256 contract)
        description {:producer-preparation producer :consumer-implementation-sha256 digest
                     :compatibility-profile coherent/profile-id}]
    (is (= coherent/profile-id (#'restore/factory-profile! description producer digest)))
    (doseq [bad [(assoc description :compatibility-profile "arbitrary-consumer")
                 (assoc description :producer-preparation {})
                 (assoc description :consumer-implementation-sha256 a)]]
      (is (thrown? clojure.lang.ExceptionInfo (#'restore/factory-profile! bad producer digest))))))
