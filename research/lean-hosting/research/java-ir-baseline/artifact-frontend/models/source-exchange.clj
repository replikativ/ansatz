(ns source-module-exchange-checks-v1
  "Pure metadata/custody rejection models, not original helper/runtime execution."
  (:require [clojure.test :refer [deftest is run-tests]] [clojure.data.json :as json]
            [java-source-module-exchange-v1 :as exchange]
            [ansatz.research.ir.source-setup :as source]
            [java-matched-prelude-module-v4 :as module]
            [java-prelude-finalizer-lineage-v1 :as lineage]
            [java-ir-baseline :as j]
            [general-command-receipt-v1 :as command]))
(def module-name ["str" ["anonymous"] "A"])
(def constant-name ["str" ["anonymous"] "answer"])
(def observed {:index {:actual-ci ::placeholder} :constant-names [constant-name]
               :imports [{:module exchange/prelude-name :importAll false :isExported true :isMeta false}]
               :extra-names [] :extensions []})
(def metadata
  {:schema "lean-source-module/2" :producer "SourceModuleExport.exportClassic"
   :leanCommit source/lean-pin :leanVersion "4.33.1"
   :runtimeProfile {:wordBits 64 :target "x86_64-unknown-linux-gnu"}
   :module module-name :moduleSystem false :level "private" :origin "owned-guest-module-data"
   :initializersExecuted false :environmentSerialized false
   :requirementsPolicy "no-local-initializers-exports-externs-redirects/1"
   :localRegularInitCount 0 :localBuiltinInitCount 0 :imports (:imports observed)
   :constantNames [constant-name] :constantCount 1 :extraConstantNames [] :extensions []})
(deftest metadata-requires-real-new-profile-and-exact-actual-inventory
  (is (= metadata (#'exchange/metadata! (json/write-str metadata) module-name observed)))
  (doseq [changed [(assoc metadata :schema "lean-source-module/1")
                   (dissoc metadata :requirementsPolicy)
                   (assoc metadata :localRegularInitCount 1)
                   (assoc metadata :localBuiltinInitCount 1)
                   (assoc metadata :constantNames [])
                   (assoc metadata :constantCount 0)
                   (assoc metadata :module exchange/prelude-name)
                   (assoc metadata :environmentSerialized true)
                   (assoc metadata :extensions [{:name module-name :entryCount 1}])]]
    (is (thrown? Exception (#'exchange/metadata! (json/write-str changed) module-name observed)))))
(deftest borrowed-metadata-cannot-supply-source-module-authority
  (is (thrown? Exception (exchange/with-module! {:verified true :module-data :fabricated} identity)))
  (is (thrown? Exception (exchange/owner-packet {:status :sealed :owners {}}))))
(deftest terminal-module-guard-runs-before-runtime-dereference
  (let [token (exchange/->SourceModule) cell (atom {:status :retired})]
    (#'exchange/publish! @#'exchange/modules token cell)
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"revoked or failed" (exchange/with-module! token identity)))))
(deftest captured-description-uses-real-frozen-string-keys
  (let [view {:summary {:source-description (sorted-map "module" ["Hosted" "A"] "profile" "actual")}}]
    (is (= ["str" ["str" ["anonymous"] "Hosted"] "A"] (#'exchange/captured-module! view)))
    (is (thrown? Exception (#'exchange/captured-module! {:summary {:source-description (sorted-map "profile" "actual")}})))))
(defn retirement-model [f]
  (let [program (Object.) engine (Object.) source (Object.) receipt (Object.)
        rh (atom {:status :failed :thread (Thread/currentThread) :engine engine :source source
                  :code-receipt receipt :active nil :driver {:current-ctx (atom {:program program})}})]
    (with-redefs-fn
      {#'exchange/field (fn [_ key] (if (= key "program") program false))
       #'j/phase (fn [& _] "idle") #'source/guard-source! (fn [& _])
       #'module/inspect! (fn [& _]) #'lineage/inspect! (fn [& _])}
      #(f rh))))
(deftest failed-operation-transfers-alias-occurrences-once-and-compacts-anchors
  (retirement-model
    (fn [rh]
      (let [same (Object.) a (object-array [same :owned]) b (object-array [same :owned])
            cell (atom {:status :failed :thread (Thread/currentThread) :runtime-holder rh
                        :owners {:a a :b b :old (object-array [same :transferred])}})
            token (exchange/->Operation)]
        (#'exchange/publish! @#'exchange/operations token cell)
        (let [packet (exchange/take-operation-retirement-owners! token)]
          (is (= 2 (count packet)))
          (is (every? #(identical? same %) packet)))
        (is (= [:external-retirement :external-retirement] [(aget a 1) (aget b 1)]))
        (is (= #{:status :retirement-output} (set (keys @cell))))
        (is (= :failed (:status @rh)))
        (is (thrown? Exception (exchange/take-operation-retirement-owners! token)))))))
(deftest failed-operation-rejects-pending-ownership-without-transfer
  (retirement-model
    (fn [rh]
      (doseq [state [:retain-pending :start-pending :take-pending :release-pending]]
        (let [slot (object-array [(Object.) state]) cell (atom {:status :failed :runtime-holder rh
                  :thread (Thread/currentThread) :owners {:pending slot}}) token (exchange/->Operation)]
          (#'exchange/publish! @#'exchange/operations token cell)
          (is (thrown? Exception (exchange/take-operation-retirement-owners! token)))
          (is (= state (aget slot 1))))))))
(deftest nursery-keeps-only-owner-slots-not-holder-backreferences
  (let [rh (atom {}) opaque-parent (Object.) slot (object-array [(Object.) :owned])
        cell (atom {:status :active :owners {:one slot} :parents [opaque-parent]})
        keeper (#'exchange/watch-owners! rh cell)]
    (is (= #{:owners :status :output} (set (keys keeper))))
    (is (identical? slot (get @(:owners keeper) :one)))
    (swap! cell assoc :parents [(Object.)] :status :sealed)
    (is (= :sealed @(:status keeper)))
    (is (not-any? #(identical? opaque-parent %) (tree-seq coll? seq keeper)))))
(deftest terminal-runtime-transfer-deduplicates-slots-not-aliased-nodes
  (retirement-model
    (fn [rh]
      (let [value (Object.) a (object-array [value :owned]) b (object-array [value :owned])
            keeper {:owners (atom {:a a :b b}) :status (atom :sealed) :output (object-array 1)}
            runtime (exchange/->SourceRuntime)]
        (swap! rh assoc :keepers [keeper keeper])
        (#'exchange/publish! @#'exchange/runtimes runtime rh)
        (is (= 2 (count (exchange/take-runtime-retirement-owners! runtime))))
        (is (= #{:status :retirement-output} (set (keys @rh))))
        (is (thrown? Exception (exchange/take-runtime-retirement-owners! runtime)))
        (exchange/close-runtime! runtime)
        (is (= {:status :closed} @rh))))))

(deftest file-retirement-rebases-before-operation-or-owner-effects
  (doseq [reject? [false true]]
    (let [events (atom []) holder (atom {}) rh (atom {}) run (Object.) module (Object.)]
      (with-redefs-fn
        {#'exchange/issued (fn [& _] holder)
         #'exchange/module! (fn [& _] {:source-holder holder :runtime-holder rh :file-retired false})
         #'command/issued (fn [& _] holder)
         #'command/rebase-idle-deadline! (fn [actual milliseconds]
             (is (identical? run actual)) (is (= 60000 milliseconds))
             (swap! events conj :rebase)
             (when reject? (throw (ex-info "failed command" {}))))
         #'exchange/publish! (fn [& _] (swap! events conj :publish))
         #'exchange/operation! (fn [& _] (swap! events conj :operation)
                                    (throw (ex-info "stop before effects" {})))}
        #(is (thrown? Exception (exchange/retire-file! module run))))
      (is (= (if reject? [:rebase] [:rebase :publish :operation]) @events)))))

(defn check! [] (run-tests 'source-module-exchange-checks-v1))
