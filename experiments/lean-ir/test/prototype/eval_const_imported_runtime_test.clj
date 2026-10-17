(ns prototype.eval-const-imported-runtime-test
  (:require [clojure.test :refer [deftest is]]
            [clojure.data.json :as json]
            [prototype.eval-const :as eval]
            [prototype.eval-const-resolution-test :as f]
            [prototype.eval-const-test :as names]
            [prototype.machine :as m]
            [prototype.raw-interop :as raw]))

(def next-name (names/n "newSourceUsingImportedClosed"))
(defn candidate [catalogue]
  (let [new-row (-> (get-in catalogue [:declarations f/answer])
                    (assoc :name next-name :sourceLocal true :sourceModule (names/n "NewSource"))
                    (assoc-in [:ir :fdecl :f] next-name))]
    (-> catalogue
        (update :declarations #(into {} (map (fn [[n r]] [n (assoc r :sourceLocal false :sourceModule nil)]) %)))
        (assoc-in [:declarations f/imported-closed :runtime] {:role "value" :initializer nil})
        (assoc-in [:declarations next-name] new-row)
        (assoc-in [:manifests 0 :requestedRoots] [next-name])
        (assoc-in [:manifests 0 :entryPoints] [{:name next-name :boxedTarget next-name}]))))

(deftest imported-closed-classification-is-preserved-only-for-source-bundle-reuse
  ;; Model lost non-persistent closed-term/simple-ground cache membership;
  ;; executable IR is independently the already-authorized imported IR.
  (doseq [backend [:reference :mutable :jvm]
          canonical-role ["closed" "ground"]]
    (let [catalogue (assoc-in (f/imported-catalogue) [:declarations f/imported-closed :runtime :role] canonical-role)
          context (f/missing-import-context backend catalogue)
          first-result (f/evaluate context)
          [world closure] (f/unwrap first-result)
          called (raw/call (:session first-result) world names/apply-answer [closure 42])
          world (:state called) original world
          bundle (candidate catalogue)
          options {:catalogue catalogue :trusted-functions (:functions world)}
          installed (eval/install-bundle world bundle options)
          after (:world installed)
          session (raw/open-functions (:functions after) (get-in called [:session :bindings]) {:backend backend})
          result (raw/call session after next-name [m/erased 42])]
      (is (= 42 (:value result)))
      (is (= (#'prototype.eval-const/bundle-digest bundle bundle) (:unit-digest installed)))
      (is (= (:globals original) (:globals after)))
      (is (= :ready (get-in after [:globals f/imported-closed :status])))
      (doseq [[n function] (:functions original)]
        (is (identical? function (get-in after [:functions n]))))
      (is (= (get-in original [:eval-const-authorizations :imported-declarations])
             (get-in after [:eval-const-authorizations :imported-declarations])))
      (is (nil? (get-in after [:eval-const-authorizations :declarations f/imported-closed])))
      (is (nil? (get-in original [:functions next-name])))
      (is (= "value" (get-in bundle [:declarations f/imported-closed :runtime :role])))
      (is (= canonical-role (get-in after [:eval-const-authorizations :imported-declarations f/imported-closed :runtime :role])))
      ;; Imported dependency runtime must not become source-unit provenance.
      (is (= [next-name] (get-in after [:eval-const-authorizations :units (:unit-digest installed) :declarations])))
      (doseq [change [#(assoc-in % [:declarations f/imported-closed :ir :fdecl :body] ["ret" {:irrelevant nil}])
                      #(assoc-in % [:declarations f/imported-closed :runtime :initializer] (names/n "differentInit"))
                      #(assoc-in % [:declarations f/imported-closed :runtime :role] (if (= canonical-role "closed") "ground" "closed"))
                      #(assoc-in % [:declarations f/imported-closed :sourceLocal] true)]]
        (is (thrown-with-msg? clojure.lang.ExceptionInfo #"selected IR differs"
              (eval/install-bundle original (change bundle) options))))
      (let [without-authority (update-in original [:eval-const-authorizations :imported-declarations] dissoc f/imported-closed)]
        (is (thrown-with-msg? clojure.lang.ExceptionInfo #"selected IR differs"
              (eval/install-bundle without-authority bundle options))))
      ;; Same runtime-bearing row as an interpreter witness stays rejected.
      (let [witness (update (:witness context) :declarations
                     #(mapv (fn [r] (if (= f/imported-closed (:name r))
                                     (assoc r :runtime {:role "value" :initializer nil}) r)) %))
            bad-context (-> (f/continue-from context called)
                            (assoc-in [:world :heap (:id (:environment context)) :fields 0] (json/write-str witness)))]
        (is (thrown-with-msg? clojure.lang.ExceptionInfo #"selected IR differs" (f/evaluate bad-context))))
      (is (= original world)))))
