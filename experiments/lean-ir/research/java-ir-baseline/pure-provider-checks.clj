(ns java-ir-pure-provider-checks
  "Selector unit models; these do not run or authenticate the Lean frontend."
  (:require [clojure.test :refer [deftest is run-tests]]
            [java-ir-pure-provider :as provider]
            [java-ir-baseline-checks :as c]
            [prototype.import-ir :as ir]
            [prototype.machine :as m]
            [prototype.module-import :as imports]
            [prototype.raw-interop :as raw])
  (:import [ansatz.kernel Name Expr ConstantInfo Env]))

(def ^:dynamic *basis* nil)
(defn- type-expr [name] (Expr/mkConst (Name/mkStr Name/ANONYMOUS_NAME name) (object-array 0) false))
(defn- definition [type]
  (ConstantInfo/mkDef (provider/kernel-name (c/name-ir "identity")) (object-array 0)
                      type (Expr/bvar 0) 1 (byte 0) (object-array 0)))
(defn- env [info] (.addConstant (Env.) info))
(defn- arrow [domain range] (Expr/forall Name/ANONYMOUS_NAME domain range :default))

(deftest exact-logical-type-classification
  (let [nat (type-expr "Nat") string (type-expr "String") name (c/name-ir "identity")]
    (is (= {:arguments [:nat :string] :result :nat}
           (provider/logical-signature (env (definition (arrow nat (arrow string nat)))) name)))
    (is (= {:arguments [] :result :string}
           (provider/logical-signature (env (definition string)) name)))
    (doseq [type [(type-expr "Bool") (arrow (type-expr "Prop") nat)
                  (Expr/forall Name/ANONYMOUS_NAME nat nat :implicit)
                  (Expr/forall Name/ANONYMOUS_NAME nat nat :inst-implicit)
                  (arrow nat (Expr/bvar 0))]]
      (is (nil? (provider/logical-signature (env (definition type)) name))))
    (let [unsafe (definition (arrow nat nat))]
      (set! (.-safety unsafe) (byte 1))
      (is (nil? (provider/logical-signature (env unsafe) name))))
    (is (nil? (provider/logical-signature (Env.) name)))
    (is (nil? (provider/logical-signature
               (env (ConstantInfo/mkAxiom (provider/kernel-name name) (object-array 0) nat false)) name)))))

(defn- modeled-request [type]
  (let [row (c/decl "identity" [(c/p 1 "object")] "object" (c/ret 1))
        [target function] (ir/lower-declaration row)
        helpers imports/helpers
        identity {:params [1] :body [:inc [:var 1] 1 [:return [:var 1]]]}
        functions {target function (:root helpers) identity
                   (:constant-map helpers) identity
                   (:quot-init? helpers) {:params [1] :body [:return [:imm 0]]}}
        [world environment] (m/allocate (m/world functions) :ctor 0 [])
        world (assoc-in world [:kernel-environments (:id environment)]
                        {:anchor environment :env (env (definition type))})
        world (assoc-in world [:eval-const-authorizations :declarations target] row)]
    {:prepared {:world world :session (raw/open-functions functions {}) :environment environment}
     :configuration {:kernel-helpers helpers}
     :target target :source-name target :function function
     :abi {:params [{:ty "object" :borrow false}] :return-type "object"}
     :signature {:arguments [:nat] :result :nat}}))

(deftest selected-region-preserves-checked-view-and-session
  (let [request (modeled-request (arrow (type-expr "Nat") (type-expr "Nat")))
        events (atom [])
        selection ((provider/selector *basis* #(swap! events conj %)) request)
        prepared (:prepared selection)
        result ((:invoke selection) (:session prepared) (:world prepared) (:target request)
                [184467440737095516160000N])]
    (is (= [:java-pure :java-pure] (mapv :tier @events)))
    (is (= 184467440737095516160000N (:value result)))
    (is (identical? (:session prepared) (:session result)))
    (is (identical? (get-in request [:prepared :world :functions]) (get-in result [:state :functions])))
    (is (= 1 (:rc (m/node (:state result) (:environment prepared)))))))

(deftest unsupported-logical-type-selects-ordinary-before-entry
  (let [request (modeled-request (arrow (type-expr "String") (type-expr "String")))
        events (atom []) selection ((provider/selector *basis* #(swap! events conj %)) request)]
    (is (= [:ordinary] (mapv :tier @events)))
    (is (identical? raw/call (:invoke selection)))))

(deftest diagnostic-failure-does-not-lose-completed-result
  (let [request (modeled-request (arrow (type-expr "Nat") (type-expr "Nat")))
        selection ((provider/selector *basis* (fn [_] (throw (ex-info "diagnostic failure" {})))) request)
        prepared (:prepared selection)
        result ((:invoke selection) (:session prepared) (:world prepared) (:target request) [41])]
    (is (= 41 (:value result)))
    (is (= :done (get-in result [:state :status])))))

(defn check! [basis] (binding [*basis* basis] (run-tests 'java-ir-pure-provider-checks)))
