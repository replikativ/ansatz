(ns prototype.hosted-file-test
  "Runner contracts with a frontend-envelope helper MODEL, the captured actual
   hosted PreludeIdentity IR, and real guest Name encoding. This does not rerun
   Lean's full frontend/bootstrap and makes no new compatibility claim."
  (:require [clojure.test :refer [deftest is]]
            [clojure.data.json :as json]
            [prototype.hosted-file :as hosted]
            [prototype.frontend-test :as model]
            [prototype.guest-encoding :as encoding]
            [prototype.import-ir :as ir]
            [prototype.runtime-abi :as abi]
            [prototype.raw-interop :as raw]
            [prototype.machine :as m])
  (:import [ansatz.kernel Name]))

(def module-name (Name/mkStr Name/ANONYMOUS_NAME "PreludeIdentity"))
(def answer-name (Name/mkStr Name/ANONYMOUS_NAME "answer"))
(def file-path "fixtures/hosted/PreludeIdentity.lean")
(def captured (delay (slurp "fixtures/hosted/PreludeIdentity.ir.jsonl")))
(def encoders
  (delay (let [catalogue (ir/index-bundles ["fixtures/kernel-encoding.jsonl"])]
           (ir/load-closure catalogue [encoding/names-helper] #(abi/lower-deferred-catalogue catalogue %)))))
(defn prepared [backend success bundle]
  (let [envelope (assoc (model/envelope success) :fileName file-path
                        :mainModule ["str" ["anonymous"] "PreludeIdentity"] :bundle (when success bundle))
        {:keys [world arguments]} (model/setup backend envelope (model/header))
        functions (merge @encoders (:functions world))]
    {:session (raw/open-functions functions {} {:backend backend :fuel 1000000})
     :world (assoc world :functions functions) :environment (:environment arguments) :options (:options arguments)
     :catalogue (ir/index-bundles ["fixtures/hosted/PreludeIdentity.ir.jsonl"])}))
(defn request [policy]
  {:path file-path :module-name module-name :roots [answer-name] :initialization policy})

(deftest file-compilation-and-boxed-calls-preserve-prepared-forks-and-owners
  (doseq [backend [:reference :mutable :jvm]]
    (let [before (prepared backend true @captured)
          [world input] (m/resource (:world before) "owned-call-input")
          before (assoc before :world world)
          result (hosted/run-file before (assoc (request :defer) :calls [{:name answer-name :args [m/erased input]}]))
          value (get-in result [:call-results 0 :value])
          after (:world result)]
      (is (:success result))
      (is (= :deferred (:initialization-state result)))
      (is (= input value))
      (is (= 1 (:rc (m/node after value))))
      (is (= 2 (:rc (m/node after (:environment before)))))
      (is (= 1 (:rc (m/node after (:options before)))))
      (is (not (contains? (:heap (m/release after value 1)) (:id value))))
      (is (not (contains? (:functions (:world before)) model/answer)))
      (is (nil? (:eval-const-authorizations (:world before))))
      (is (= 1 (:rc (m/node (:world before) input))))
      (is (pos? (- (get-in after [:stats :steps]) (get-in before [:world :stats :steps])))))))

(deftest diagnostics-return-owned-environment-without-consuming-unstarted-call-arguments
  (let [before (prepared :reference false nil)
        [world input] (m/resource (:world before) "not-called")
        result (hosted/run-file (assoc before :world world)
                               (assoc (request :run) :calls [{:name answer-name :args [m/erased input]}]))]
    (is (false? (:success result)))
    (is (= :not-compiled (:initialization-state result)))
    (is (= [] (:call-results result)))
    (is (seq (:diagnostics result)))
    (is (= 1 (:rc (m/node (:world result) input))))
    (is (= 2 (:rc (m/node (:world result) (:environment before)))))
    (is (nil? (:eval-const-authorizations (:world result))))))

(def cached-name ["str" ["anonymous"] "cached"])
(defn initialization-bundle []
  (let [rows (mapv #(json/read-str % :key-fn keyword) (clojure.string/split-lines @captured))
        manifest (assoc-in (first rows) [:initializationPlan :actions]
                           [{:meta false :action {:kind "value" :name cached-name :target cached-name}}])
        global {:kind "decl" :name cached-name :sourceLocal true :sourceModule ["str" ["anonymous"] "PreludeIdentity"]
                :runtime {:role "value" :initializer nil}
                :ir {:fdecl {:f cached-name :xs [] :type "object" :info {}
                             :body ["vdecl" {:idx 1} "object" {:lit {:v {:str {:v "initialized"}}}}
                                    ["ret" {:var {:id {:idx 1}}}]]}}}]
    (clojure.string/join "\n" (map json/write-str (into [manifest] (conj (subvec rows 1) global))))))

(deftest initialization-is-explicit-and-executes-admitted-guest-actions
  (doseq [backend [:reference :mutable :jvm]]
    (let [before (prepared backend true (initialization-bundle))
          deferred (hosted/run-file before (request :defer))
          initialized (hosted/run-file before (assoc (request :run) :calls [{:name answer-name :args [m/erased 42]}]))]
      (is (= 1 (count (:pending-local-initializers deferred))))
      (is (nil? (get-in deferred [:world :globals cached-name])))
      (is (= :ready (:initialization-state initialized)))
      (is (= [] (:pending-local-initializers initialized)))
      (is (= :ready (get-in initialized [:world :globals cached-name :status])))
      (is (= "initialized" (get-in initialized [:world :globals cached-name :value])))
      (is (= 42 (get-in initialized [:call-results 0 :value])))
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"pending module initializers"
            (hosted/run-file before (assoc (request :defer) :calls [{:name answer-name :args [m/erased 42]}])))))))

(deftest invalid-inputs-fail-before-guest-execution-and-call-failure-retains-results
  (let [before (prepared :reference true @captured)]
    (doseq [change [#(dissoc % :initialization) #(assoc % :initialization :automatic)
                    #(assoc % :text "prelude") #(assoc % :roots ["answer"])
                    #(assoc % :calls [{:name answer-name :args nil}])]]
      (is (thrown? clojure.lang.ExceptionInfo (hosted/run-file before (change (request :defer))))))
    (let [[world input] (m/resource (:world before) "completed-call")
          unknown (Name/mkStr Name/ANONYMOUS_NAME "not-exported")
          error (try (hosted/run-file (assoc before :world world)
                                     (assoc (request :defer) :calls [{:name answer-name :args [m/erased input]}
                                                                    {:name unknown :args []}]))
                     nil (catch clojure.lang.ExceptionInfo error error))
          data (ex-data error)]
      (is (re-find #"not an admitted boxed entrypoint" (.getMessage error)))
      (is (= input (get-in data [:call-results 0 :value])))
      (is (= 1 (:rc (m/node (:checkpoint data) input))))
      (is (= (:environment before) (:compiled-environment data)))
      (is (identical? (get-in data [:checkpoint :functions]) (get-in data [:session :functions]))))))

(deftest module-export-returns-owned-io-errors-without-consuming-input-environment
  (doseq [backend [:reference :mutable :jvm]]
    (let [before (prepared backend true @captured)
          target ["str" ["anonymous"] "modeledSourceModuleExport"]
          symbol "hosted_file_export_model"
          signature {:params [{:ty "object" :borrow false} {:ty "object" :borrow false}
                              {:ty "void" :borrow false}] :return-type "object"}
          binding {:signature signature
                   :handler (fn [_ world [environment module _]]
                              (let [world (-> world (m/release environment 1) (m/release module 1))
                                    [world error] (m/resource world "export-error")]
                                (m/allocate world :ctor 1 [error])))}
          functions (assoc (get-in before [:world :functions]) target
                           {:params [1 2 3] :raw-extern {:symbol symbol :signature signature}
                            :body [:host symbol [[:var 1] [:var 2] [:var 3]] 4 [:return [:var 4]]]})
          before (assoc before :world (assoc (:world before) :functions functions)
                         :session (raw/open-functions functions {symbol binding} {:backend backend}))
          result (hosted/export-module before module-name {:export-options {:helper target}})
          released (m/release (:world result) (:io-result result) 1)]
      (is (= :io-error (:status result)))
      (is (nil? (:module-data result)))
      (is (= 1 (:rc (m/node (:world result) (:environment before)))))
      (is (= 1 (:rc (m/node (:world before) (:environment before)))))
      (is (= [[:released "export-error"]] (:events released)))
      (is (identical? (get-in result [:world :functions]) (get-in result [:session :functions]))))))

(deftest staged-file-finisher-reuses-compiled-result-without-recompiling-or-reading-source
  (doseq [backend [:reference :mutable :jvm]]
    (let [before (prepared backend true @captured)
          req (assoc (request :defer) :calls [{:name answer-name :args [m/erased 42]}])
          finish hosted/finish-file
          compiled (with-redefs [hosted/finish-file (fn [compiled _] compiled)]
                     (hosted/run-file before req))
          result (with-redefs [slurp (fn [& _] (throw (Exception. "source must not be read")))]
                   (finish compiled req))]
      (is (= 42 (get-in result [:call-results 0 :value])))
      (is (= :deferred (:initialization-state result)))
      (is (= (:environment compiled) (:environment result)))
      (is (= 2 (:rc (m/node (:world result) (:environment result)))))
      (is (identical? (get-in compiled [:world :functions]) (get-in result [:world :functions])))
      (is (not (contains? (:functions (:world before)) model/answer)))
      (is (empty? (:call-results compiled)))
      (let [unknown (Name/mkStr Name/ANONYMOUS_NAME "not-exported")
            error (try (finish compiled (assoc req :calls [{:name answer-name :args [m/erased 42]}
                                                          {:name unknown :args []}])) nil
                       (catch clojure.lang.ExceptionInfo error error))
            data (ex-data error)]
        (is (= 42 (get-in data [:call-results 0 :value])))
        (is (= (:environment compiled) (:compiled-environment data)))
        (is (identical? (get-in data [:checkpoint :functions]) (get-in data [:session :functions])))))))

(deftest staged-file-finisher-preserves-explicit-initialization-and-request-validation
  (let [before (prepared :reference true (initialization-bundle))
        compiled (with-redefs [hosted/finish-file (fn [compiled _] compiled)]
                   (hosted/run-file before (request :defer)))
        ready (hosted/finish-file compiled (request :run))]
    (is (= :ready (:initialization-state ready)))
    (is (= :ready (get-in ready [:world :globals cached-name :status])))
    (is (nil? (get-in compiled [:world :globals cached-name])))
    (doseq [bad [(dissoc (request :defer) :initialization)
                 (assoc (request :defer) :calls [{:name answer-name :args nil}])]]
      (is (thrown? clojure.lang.ExceptionInfo (hosted/finish-file compiled bad))))))

(deftest staged-file-finisher-rejects-malformed-compilation-result
  (let [before (prepared :reference true @captured)
        compiled (with-redefs [hosted/finish-file (fn [compiled _] compiled)]
                   (hosted/run-file before (request :defer)))]
    (doseq [bad [(dissoc compiled :success)
                 (update-in compiled [:session :functions] with-meta {:different-identity true})]]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"frontend compilation result"
            (hosted/finish-file bad (request :defer)))))))

(deftest invalid-execution-request-is-rejected-before-compilation
  (let [before (prepared :reference true @captured) calls (atom 0)]
    (with-redefs [prototype.frontend/compile-file (fn [& _] (swap! calls inc) (throw (Exception. "must not compile")))]
      (doseq [bad [(dissoc (request :run) :initialization)
                   (assoc (request :run) :calls [{:name answer-name :args nil}])]]
        (is (thrown? clojure.lang.ExceptionInfo (hosted/run-file before bad)))))
    (is (zero? @calls))))
