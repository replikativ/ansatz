(ns java-source-module-base-models-v1
  "Source Base structural/lease models. No real source Module/finalizer issuance."
  (:require [clojure.test :refer [deftest is run-tests]]
            [java-source-module-base-v1 :as base]
            [java-matched-artifact-base-v1 :as fixed]
            [java-composite-artifact-base-v1 :as dispatch]
            [prototype.kernel-projection-snapshot :as snapshot]
            [java-source-module-exchange-v1 :as exchange]
            [prototype.imported-kernel :as imported]
            [ansatz.research.ir.kernel-projection :as projection])
  (:import [ansatz.kernel Env Name Expr ConstantInfo]))
(deftest public-empty-token-and-plain-java-env-cannot-issue-a-source-view
  (doseq [x [(base/->SourceBase) {} (Env.) nil]]
    (is (thrown? Exception (base/guard! x)))
    (is (thrown? Exception (base/with-env! x identity)))
    (is (thrown? Exception (dispatch/guard! x)))))
(deftest index-must-be-exact-disjoint-checked-segments-not-caller-ci-snapshots
  (let [nat (Expr/mkConst (Name/mkStr Name/ANONYMOUS_NAME "Nat") (object-array 0) false)
        name (Name/mkStr Name/ANONYMOUS_NAME "local")
        ci (ConstantInfo/mkAxiom name (object-array 0) nat false)
        payload (Object.) info (Object.) index {name {:ci ci :kind 0 :payload payload :info info}}
        segment (snapshot/snapshot-segment {name ci})]
    (with-redefs [fixed/domain-names (fn [_] #{})]
      (is (= #{name} (#'base/validate-index! :actual-prelude index [segment])))
      (is (= #{} (#'base/validate-index! :actual-prelude {} [])))
      (is (thrown? Exception (#'base/validate-index! :actual-prelude index [])))
      (is (thrown? Exception (#'base/validate-index! :actual-prelude (assoc-in index [name :kind] 1) [segment])))
      (is (thrown? Exception (#'base/validate-index! :actual-prelude index [segment segment]))))
    (with-redefs [fixed/domain-names (fn [_] #{name})]
      (is (thrown? Exception (#'base/validate-index! :actual-prelude index [segment]))))))
(deftest changed-checked-ci-fails-before-composite-resolver-is-issued
  (let [name (Name/mkStr Name/ANONYMOUS_NAME "local") nat (Expr/mkConst name (object-array 0) false)
        ci (ConstantInfo/mkDef name (object-array 0) nat nat 0 (byte 0) (object-array [name]))
        index {name {:ci ci :kind 1 :payload (Object.) :info (Object.)}} segment (snapshot/snapshot-segment {name ci})]
    (set! (.-value ci) (Expr/mkConst (Name/mkStr Name/ANONYMOUS_NAME "changed") (object-array 0) false))
    (with-redefs [fixed/domain-names (fn [_] #{})]
      (is (thrown? Exception (#'base/validate-index! :actual-prelude index [segment]))))))

(deftest source-readback-compares-name-kind-and-exact-original-payload
  (let [name (Name/mkStr Name/ANONYMOUS_NAME "source") payload (Object.)
        info {:name name :kind 0 :fields [payload]} s {:index {name {:kind 0 :payload payload}}}
        ops {:node (fn [_ x] x)}]
    (with-redefs [imported/project-constant-name-kind (fn [_ x _ _] (select-keys x [:name :kind]))]
      (is (= {:name name :kind 0 :payload payload} (#'base/source-info! s :world ops info)))
      (doseq [bad [(assoc info :kind 1) (assoc info :fields [(Object.)])
                   (assoc info :fields [payload payload]) (assoc info :name Name/ANONYMOUS_NAME)]]
        (is (thrown? Exception (#'base/source-info! s :world ops bad)))))))

(deftest finalized-domain-is-complete-and-no-duplicate-or-substituted-ci-is-accepted
  (let [native (Name/mkStr Name/ANONYMOUS_NAME "native") local (Name/mkStr Name/ANONYMOUS_NAME "local")
        native-payload (Object.) local-payload (Object.)
        ni {:name native :kind 0 :fields [native-payload]}
        li {:name local :kind 1 :fields [local-payload]}
        values (atom [ni li]) closed (atom 0) checked (atom [])
        s {:prelude-base :model :domain #{native local} :index {local {:kind 1 :payload local-payload}}}]
    (with-redefs-fn
      {#'base/array-values (fn [_ _] @values)
       #'projection/open-projector (fn [& _] {:world :model :carrier-ops {:node (fn [_ x] x)}
                                              :close! #(swap! closed inc)})
       #'imported/project-constant-name-kind (fn [_ x _ _] (select-keys x [:name :kind]))
       #'fixed/with-env! (fn [_ f] (f :model-env))
       #'fixed/validate-base-info! (fn [_ _ _ x]
                                   (is (identical? native-payload (first (:fields x))))
                                   (swap! checked conj (:name x)))}
      (fn []
        (is (nil? (#'base/validate-finalized! s)))
        (is (= [native] @checked))
        (doseq [bad [[ni ni] [li] [ni (assoc li :fields [(Object.)])]
                     [ni (assoc li :kind 0)] [ni li ni]]]
          (reset! values bad)
          (is (thrown? Exception (#'base/validate-finalized! s))))
        (is (= 6 @closed))))))

(defn- with-model-base [callback]
  ;; Deliberately mocked issuer/engine lifecycle. This tests composite custody
  ;; and lazy Java lookup, never actual SourceClosure/finalizer authority.
  (let [prelude (Object.) closure (Object.) run (Object.) engine (Object.) source (Object.) receipt (Object.)
        native (Name/mkStr Name/ANONYMOUS_NAME "native") local (Name/mkStr Name/ANONYMOUS_NAME "local")
        typ (Expr/mkConst native (object-array 0) false)
        ni (ConstantInfo/mkAxiom native (object-array 0) typ false)
        li (ConstantInfo/mkAxiom local (object-array 0) typ false)
        native-env (.addConstant (Env.) ni) source-index {local {:ci li :kind 0 :payload (Object.) :info (Object.)}}
        segments [(snapshot/snapshot-segment {local li})] issuer-open (atom true) full-checks (atom 0)
        driver {:current-ctx (atom {})}
        c {:prelude-base prelude :engine engine :source source :code-receipt receipt
           :source-index source-index :snapshot-segments segments :driver driver}
        r {:basis :actual-source-closure-finalizer-only :closure closure :engine engine :source source
           :code-receipt receipt :quot 1 :empty 0 :constant-count 2
           :environment (Object.) :kernel-root (Object.) :constant-map (Object.) :constants (Object.)}
        scoped (fn [expected actual value f]
                 (when-not (and @issuer-open (identical? expected actual)) (throw (ex-info "Model issuer revoked/foreign" {})))
                 (swap! full-checks inc)
                 (try (f value) (finally (when-not @issuer-open (throw (ex-info "Model issuer revoked in borrow" {}))))))]
    (with-redefs-fn
      {#'base/cheap-live! (fn [holder]
                           (let [s @holder]
                             (when-not (and (= :open (:status s)) (identical? (:thread s) (Thread/currentThread)))
                               (throw (ex-info "Model Base not live" {}))) @holder))
       #'base/validate-finalized! (fn [_] nil)
       #'fixed/guard! identity
       #'fixed/domain-names (fn [_] #{native})
       #'fixed/with-env! (fn [_ f] (f native-env))
       #'exchange/with-closure! (fn [token f] (scoped closure token c f))
       #'exchange/with-finalized! (fn [token f] (scoped run token r f))}
      (fn []
        (let [token (base/open-base! prelude closure run)]
          (try (callback {:token token :engine engine :source source :run run
                          :native native :local local :ni ni :li li :issuer-open issuer-open
                          :full-checks full-checks})
               (finally (base/revoke! token))))))))

(deftest lazy-composite-lookup-is-scoped-and-does-not-walk-full-ledger-per-ci
  (with-model-base
    (fn [{:keys [token native local ni li full-checks]}]
      (let [saved (atom nil) before @full-checks]
        (base/with-env! token
          (fn [^Env env]
            (reset! saved env)
            (is (identical? ni (.lookup env native)))
            (dotimes [_ 5] (is (identical? li (.lookup env local))))
            (is (nil? (.lookup env (Name/mkStr Name/ANONYMOUS_NAME "unknown"))))
            (is (thrown? Exception (base/revoke! token)))))
        (is (= 2 (- @full-checks before)))
        (is (thrown? Exception (.lookup ^Env @saved local)))))))

(deftest version-and-session-binding-preserve-exact-composite-external-view
  (with-model-base
    (fn [{:keys [token engine source run]}]
      (is (identical? token (base/assert-session! token engine source run)))
      (doseq [args [[(Object.) source run] [engine (Object.) run] [engine source (Object.)]]]
        (is (thrown? Exception (apply base/assert-session! token args))))
      (base/with-env! token
        (fn [^Env env]
          (is (identical? env (base/with-version! token env identity)))
          (is (thrown? Exception (base/with-version! token (Env.) identity))))))))

(deftest revoked-issuer-and-exceptional-borrows-do-not-leave-lookup-credits
  (with-model-base
    (fn [{:keys [token issuer-open]}]
      (is (thrown? Exception (base/with-env! token (fn [_] (throw (ex-info "Model checker rejection" {}))))))
      (is (zero? (:borrow-depth @(#'base/cell token))))
      (reset! issuer-open false)
      (is (thrown? Exception (base/guard! token)))
      (is (= :failed (:status @(#'base/cell token)))))))

(deftest issuer-failure-inside-borrow-still-allows-view-only-revocation-after-unwind
  (with-model-base
    (fn [{:keys [token issuer-open]}]
      (is (thrown? Exception
            (base/with-env! token
              (fn [_]
                (reset! issuer-open false)
                (base/guard! token)))))
      (is (= :failed (:status @(#'base/cell token))))
      (is (zero? (:borrow-depth @(#'base/cell token))))
      (is (nil? (base/revoke! token)))
      (is (= :revoked (:status @(#'base/cell token)))))))

(defn check! [] (run-tests 'java-source-module-base-models-v1))
