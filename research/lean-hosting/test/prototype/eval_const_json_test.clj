(ns prototype.eval-const-json-test
  "Transport/ownership tests with modeled helper IR and encoded Json. Native
   Json layouts and actual helper parity are checked independently."
  (:require [clojure.test :refer [deftest is]]
            [prototype.eval-const :as eval]
            [prototype.eval-const-resolution-test :as resolution]
            [prototype.eval-const-test :as fixtures]
            [prototype.guest-json :as guest-json]
            [prototype.guest-json-test :as json-fixture]
            [prototype.machine :as m]
            [prototype.raw-interop :as raw]))

(defn setup [backend change io-tag]
  (let [base (resolution/setup backend false identity)
        [world payload] (json-fixture/encode (:world base) (change (:witness base)))
        [world environment] (m/allocate world :ctor 0 [payload (resolution/bundle-text resolution/fixture)])
        world (m/release world (:environment base) 1)
        helper {:params [1 2 3]
                :body [:let 4 [:project [:var 1] 0]
                       [:inc [:var 4] 1
                        [:dec [:var 1] 1 [:dec [:var 2] 1
                         [:let 5 [:ctor io-tag [[:var 4]]] [:return [:var 5]]]]]]]}
        functions (assoc (:functions world) resolution/witness-helper helper)
        binding (eval/make-binding fixtures/exporter
                  {:witness resolution/witness-helper :witness-format :guest-json
                   :trusted-functions functions :catalogue resolution/fixture})
        world (assoc world :functions functions)
        session (raw/open-functions functions {"lean_eval_const" binding} {:backend backend})]
    (assoc base :world world :environment environment :session session :json-payload payload)))

(deftest guest-json-witness-resolves-through-the-same-authority-checks
  (doseq [backend [:reference :mutable :jvm]]
    (let [context (setup backend identity 0)
          result (resolution/evaluate context)
          [world closure] (resolution/unwrap result)
          called (raw/call (:session result) world fixtures/apply-answer [closure 42])]
      (is (= 42 (:value called)))
      (is (= (:witness context)
             (guest-json/project (:state called) (:json-payload context) {:key-fn keyword})))
      (is (= 1 (:rc (m/node (:state called) (:json-payload context)))))
      (is (= 1 (:rc (m/node (:state called) (:environment context)))))
      (is (= 1 (:rc (m/node (:state called) (:name context)))))
      (is (identical? (get-in context [:world :functions resolution/answer])
                      (get-in called [:state :functions resolution/answer]))))))

(deftest invalid-json-witness-preserves-the-exact-owned-result-and-snapshot
  (doseq [change [(constantly true)
                  #(assoc % :sorryDep resolution/answer)
                  #(assoc % :leanCommit "untrusted")
                  #(assoc-in % [:declarations 0 :ir :fdecl :xs 0 :borrow] true)
                  #(assoc % :declarations [])]
          backend [:reference :mutable :jvm]]
    (let [context (setup backend change 0)
          failure (try (resolution/evaluate context) nil (catch clojure.lang.ExceptionInfo e e))
          data (ex-data failure) world (:checkpoint data) owner (:witness-io-result data)]
      (is (some? failure))
      (is (m/ref? owner))
      (is (= 0 (:tag (m/node world owner))))
      (is (= [(:json-payload context)] (:fields (m/node world owner))))
      (is (= 1 (:rc (m/node (:world context) (:json-payload context)))))
      (is (= (:functions world) (get-in data [:checkpoint-session :functions])))
      (let [cleaned (m/release world owner 1)]
        (when (m/ref? (:json-payload context))
          (is (= 1 (:rc (m/node cleaned (:json-payload context))))))))))

(deftest guest-io-error-retains-its-wrapper-owner
  (doseq [backend [:reference :mutable :jvm]]
    (let [context (setup backend identity 1)
          failure (try (resolution/evaluate context) nil (catch clojure.lang.ExceptionInfo e e))
          data (ex-data failure) world (:checkpoint data) owner (:witness-io-result data)]
      (is (= :guest-error (:type data)))
      (is (= (:json-payload context) (:guest-error data)))
      (is (= 1 (:tag (m/node world owner))))
      (is (= [(:guest-error data)] (:fields (m/node world owner))))
      (is (= 2 (:rc (m/node world (:guest-error data)))))
      (is (= 1 (:rc (m/node (m/release world owner 1) (:json-payload context))))))))

(deftest witness-format-is-explicit-and-validated
  (doseq [format [nil :auto :json "guest-json" 0]]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Invalid evalConst witness format"
                         (eval/make-binding fixtures/exporter {:witness-format format})))))
