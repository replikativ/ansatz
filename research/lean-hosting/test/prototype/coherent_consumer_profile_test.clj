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
(def target coherent/cases-on-target)
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
                            :ir-id "helpers/cases-on.ndjson" :ir-sha256 b :entrypoints ["KernelCasesOnRaw.construct"]}]
                 :redirects [{:symbol "lean_mk_cases_on" :target target :row-sha256 coherent/cases-on-original-row-sha256}]
                 :stages [:fresh-init :ordinary-helpers :cases-on :seal :project :typed-io
                          :ordinary-module :chain :diamond :reload]}})
(def contract (contract-for inventory))
(defn valid! [contract]
  (coherent/validate-contract! contract (:implementation-sha256 contract)))
(defn text-digest [text] (wire/sha256 (.getBytes ^String text java.nio.charset.StandardCharsets/UTF_8)))

(deftest artifact-base-admission-is-explicit-closed-contract-data
  (let [mode {:basis :trusted-artifact :profile coherent/artifact-base-profile-id}
        selected (assoc contract :kernel-base-admission mode)]
    (is (identical? contract (valid! contract)))
    (is (not (contains? contract :kernel-base-admission)))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"requires the finite JVM provider profile"
                         (valid! selected)))
    (is (not= (text-digest (pr-str contract)) (text-digest (pr-str selected))))
    (doseq [bad [nil true {} {:basis :strict-fresh}
                 (assoc mode :profile :caller-selected-base)
                 (assoc mode :sha256 a) (assoc mode :verified true)
                 (assoc mode :basis :caller-trust)]]
      (is (thrown? clojure.lang.ExceptionInfo
                   (valid! (assoc contract :kernel-base-admission bad)))))))

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
               (assoc contract :inventory (conj inventory {:id "../escape.clj" :kind :host-source :sha256 a}))
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
                     :compatibility-profile coherent/profile-id :consumer-contract-sha256 b}]
    (is (= coherent/profile-id (#'restore/factory-profile! description producer digest)))
    (doseq [bad [(assoc description :compatibility-profile "arbitrary-consumer")
                 (assoc description :producer-preparation {})
                 (assoc description :consumer-implementation-sha256 a)]]
      (is (thrown? clojure.lang.ExceptionInfo (#'restore/factory-profile! bad producer digest))))))

(deftest actual-issued-capability-retains-its-authenticated-composition
  ;; Model ONLY the private construction's already-authenticated envelope. Actual
  ;; Factory issuance/registry/accessors/invoke and restore identity checks below
  ;; are real. These models do not prove fresh bootstrap or loaded-code closure.
  (let [one contract
        two (assoc-in contract [:composition :helpers 0 :ir-sha256] a)
        _ (is (= (:inventory one) (:inventory two)))
        _ (is (= (:implementation-sha256 one) (:implementation-sha256 two)))
        _ (is (= one (valid! one)))
        _ (is (= two (valid! two)))
        producer {:factory-id factory/shared-linear-factory-id
                  :catalogue-recipe {:schema "full-init-checkpoint-preparation/2"}
                  :kernel-policy factory/kernel-policy
                  :trusted-roots (vec (concat factory/assembly-roots [factory/shared-linear-target factory/exporter]))}
        describe (fn [contract]
                   {:producer-preparation producer
                    :consumer-implementation-sha256 (:implementation-sha256 contract)
                    :compatibility-profile coherent/profile-id
                    :consumer-contract-sha256 (text-digest (pr-str contract))})
        issue (fn [contract]
                (with-redefs-fn
                  {#'factory/make-factory*
                   (fn [& args]
                     (is (= :coherent (nth args 6)))
                     (let [description (describe contract)]
                       {:description description
                        :coherent-contract {:sha256 (:consumer-contract-sha256 description) :contract contract}
                        :invoke (fn [_] (assoc description :catalogue {} :bindings {}))}))}
                  #(factory/make-coherent-frontend-factory {:producer-preparation producer})))
        f1 (issue one) f2 (issue two)
        d1 (factory/descriptor f1) d2 (factory/descriptor f2)
        c1 (factory/coherent-contract f1) c2 (factory/coherent-contract f2)
        r1 (factory/invoke! f1 {})
        manifest {:binding-signatures {}}]
    (is (not= d1 d2))
    (is (not= (:sha256 c1) (:sha256 c2)))
    (is (identical? one (:contract c1)))
    (is (identical? two (:contract c2)))
    (is (identical? r1 (#'restore/factory-result! r1 producer (:implementation-sha256 one)
                       coherent/profile-id manifest d1)))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"contract digest mismatch"
                          (#'restore/factory-result! r1 producer (:implementation-sha256 one)
                           coherent/profile-id manifest d2)))
    (doseq [fake [d1 c1 {} (Object.) (factory/->Factory)]]
      (is (thrown? clojure.lang.ExceptionInfo (factory/coherent-contract fake))))
    (doseq [description [(dissoc d1 :consumer-contract-sha256)
                         (assoc d1 :consumer-contract-sha256 "bad")
                         (assoc d1 :extra true)]]
      (is (thrown? clojure.lang.ExceptionInfo
                   (#'restore/factory-profile! description producer (:implementation-sha256 one)))))
    (let [legacy-description (dissoc (assoc d1 :compatibility-profile old/profile-id)
                                    :consumer-contract-sha256)
          legacy (with-redefs-fn
                   {#'factory/make-factory* (fn [& _] {:description legacy-description
                                                     :coherent-contract nil :invoke identity})}
                   #(factory/make-factory {:producer-preparation producer}))]
      (is (= legacy-description (factory/descriptor legacy)))
      (is (thrown? clojure.lang.ExceptionInfo (factory/coherent-contract legacy))))))

(deftest clj-and-cljc-shadow-names-are-both-covered
  ;; Shape test only; actual extra-root/jar shadow rejection belongs to the
  ;; pre-project isolated bootstrap, before either namespace could execute.
  (is (= "prototype/frontend__init.class" (#'coherent/aot-resource-id "prototype/frontend.clj")))
  (is (= "prototype/machine__init.class" (#'coherent/aot-resource-id "prototype/machine.cljc")))
  (is (nil? (#'coherent/aot-resource-id "prototype/runtime_signatures.edn"))))

(deftest all-legacy-constructors-preserve-routing-and-issued-descriptors
  ;; Only the already-authenticated construction envelope is modeled. These are
  ;; real public issuance, private registry, descriptor and invoke paths, not an
  ;; archive/restore claim. Nine constructors cover eight historical profiles;
  ;; native-base intentionally shares the frontend profile with a private owner.
  (let [producer {:factory-id factory/shared-linear-factory-id
                  :catalogue-recipe {:schema "full-init-checkpoint-preparation/2"}
                  :kernel-policy factory/kernel-policy
                  :trusted-roots (vec (concat factory/assembly-roots [factory/shared-linear-target factory/exporter]))}
        routes [[factory/make-factory [false false false false false nil] old/profile-id false]
                [factory/make-reconstruction-factory [true false false false false nil] old/reconstruction-profile-id false]
                [factory/make-runtime-ops-reconstruction-factory [true true false false false nil] old/runtime-ops-reconstruction-profile-id false]
                [factory/make-heap-net-dirty-reconstruction-factory [true true true false false nil] old/heap-net-dirty-reconstruction-profile-id false]
                [factory/make-source-graph-reconstruction-factory [true true true true false nil] old/source-graph-reconstruction-profile-id false]
                [factory/make-source-graph-frontend-reconstruction-factory [true true true true true nil] old/source-graph-frontend-reconstruction-profile-id false]
                [factory/make-source-graph-native-base-factory [true true true true true nil] old/source-graph-frontend-reconstruction-profile-id true]
                [factory/make-hosted-application-factory [true true true true true :v1] old/hosted-application-profile-id true]
                [factory/make-hosted-application-control-factory [true true true true true :v2] old/hosted-application-control-profile-id true]]]
    (doseq [[construct expected-flags profile owns-native?] routes]
      (testing profile
        (let [options {:producer-preparation producer}
              description {:producer-preparation producer :consumer-implementation-sha256 a :compatibility-profile profile}
              input (Object.) calls (atom 0)
              capability (with-redefs-fn
                           {#'factory/make-factory*
                            (fn [& args]
                              (swap! calls inc)
                              (is (= expected-flags (subvec (vec args) 1 7)))
                              (is (identical? options (nth args 7)))
                              (is (= owns-native? (some? (nth args 8))))
                              {:description description :coherent-contract nil
                               :invoke (fn [actual] (is (identical? input actual)) description)})}
                           #(construct options))]
          (is (= 1 @calls))
          (is (identical? description (factory/descriptor capability)))
          (is (= #{:producer-preparation :consumer-implementation-sha256 :compatibility-profile}
                 (set (keys (factory/descriptor capability)))))
          (is (identical? description (factory/invoke! capability input)))
          (is (thrown? clojure.lang.ExceptionInfo (factory/coherent-contract capability)))
          (is (thrown? clojure.lang.ExceptionInfo (factory/descriptor description))))))))
