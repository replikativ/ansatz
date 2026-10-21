(ns prototype.resident-frontend-boundary-test
  "Resident ownership/ABI acceptance MODELS. Captured emitted identity IR supplies
   the manifest and source identity; explicitly modified boxed IR, raw externs,
   and compiler envelopes model boundary cases. No actual frontend is executed."
  (:require [clojure.test :refer [deftest is testing]]
            [clojure.data.json :as json]
            [clojure.string :as str]
            [prototype.resident-frontend :as resident]
            [prototype.resident-frontend-test :as model]
            [prototype.hosted-file-test :as hosted-model]
            [prototype.frontend-test :as frontend-model]
            [prototype.frontend :as frontend]
            [prototype.raw-interop :as raw]
            [prototype.machine :as m]
            [prototype.interop-codec :as codec]))

(def backends [:reference :mutable :jvm])
(def boxed-name ["str" ["str" ["anonymous"] "answer"] "_boxed"])

(defn- boxed-model-bundle [change]
  (->> (str/split-lines @hosted-model/captured)
       (map #(json/read-str % :key-fn keyword))
       (map #(if (= boxed-name (:name %)) (change %) %))
       (map json/write-str)
       (str/join "\n")))

(defn- adopt [prepared]
  (resident/adopt-prepared prepared
                           {:trusted-functions (get-in prepared [:world :functions])
                            :trusted-bindings (get-in prepared [:session :bindings])}))

(defn- io-model-bundle [symbol]
  (boxed-model-bundle
   #(-> %
        (assoc :dependencies [])
        (assoc :ir {:extern {:f boxed-name
                             :xs [{:x {:idx 1} :ty "object" :borrow false}
                                  {:x {:idx 2} :ty "void" :borrow false}]
                             :type "object"
                             :ext {:entries [{:standard {:backend ["str" ["anonymous"] "all"]
                                                         :fn symbol}}]}}}))))

(deftest explicit-io-success-discharges-wrapper-and-payload-owners
  (doseq [backend backends]
    (let [symbol "resident_boundary_io_success"
          base (model/context backend true (io-model-bundle symbol))
          configured (resident/with-externs base
                       {symbol {:signature {:params [{:ty "object" :borrow false}
                                                     {:ty "void" :borrow false}]
                                            :return-type "object"}
                                :handler (fn [_ world [payload _]]
                                           (m/allocate world :ctor 0 [payload]))}})
          loaded (model/load-identity configured)
          ctx (:context loaded)
          before (resident/snapshot ctx)
          called (resident/call-io ctx (:file loaded) hosted-model/answer-name
                                   [[1 128 255]] {:arguments [:bytes] :result :bytes})
          after (resident/snapshot (:context called))]
      (is (= [1 128 255] (:value called)) (str backend))
      (is (= 0 (get-in after [:world :result])))
      (is (= (count (get-in before [:world :heap])) (count (get-in after [:world :heap]))))
      (is (identical? (get-in after [:world :functions]) (get-in after [:session :functions])))
      (doseq [context [base configured ctx (:context called)]] (resident/close! context)))))

(deftest explicit-io-error-retains-owned-wrapper-and-error-in-exact-checkpoint
  (doseq [backend backends]
    (let [symbol "resident_boundary_io_error"
          base (model/context backend true (io-model-bundle symbol))
          configured (resident/with-externs base
                       {symbol {:signature {:params [{:ty "object" :borrow false}
                                                     {:ty "void" :borrow false}]
                                            :return-type "object"}
                                :handler (fn [_ world [payload _]]
                                           (let [world (m/release world payload 1)
                                                 [world error] (m/resource world "modeled-io-error")]
                                             (m/allocate world :ctor 1 [error])))}})
          loaded (model/load-identity configured)
          ctx (:context loaded)
          before (resident/snapshot ctx)
          error (try (resident/call-io ctx (:file loaded) hosted-model/answer-name
                                       [[1 2]] {:arguments [:bytes] :result :bytes})
                     nil (catch clojure.lang.ExceptionInfo error error))
          data (ex-data error)
          world (:checkpoint data)
          wrapper (:resident-owned-result data)
          payload (:guest-error data)]
      (is error (str backend))
      (is (= :guest-error (:type data)))
      (is (= payload (first (:fields (m/node world wrapper)))))
      (is (= 1 (:rc (m/node world wrapper))))
      (is (= 1 (:rc (m/node world payload))))
      (is (identical? (:functions world) (get-in data [:checkpoint-session :functions])))
      (let [released (m/release world wrapper 1)]
        (is (= [[:released "modeled-io-error"]] (:events released)))
        (is (not (contains? (:heap released) (:id payload)))))
      (is (= (count (:heap world)) (+ 2 (count (get-in before [:world :heap])))))
      (doseq [context [base configured ctx]] (resident/close! context)))))

(deftest borrowed-boxed-heap-argument-and-alias-result-release-both-owners
  (let [bundle (boxed-model-bundle
                #(-> %
                     (assoc :dependencies [])
                     (assoc-in [:ir :fdecl :xs 0 :ty] "erased")
                     (assoc-in [:ir :fdecl :xs 1 :borrow] true)
                     (assoc-in [:ir :fdecl :body]
                               ["inc" {:idx 2} 1 true false ["ret" {:var {:id {:idx 2}}}]])))]
    (doseq [backend backends]
      (let [base (model/context backend true bundle)
            loaded (model/load-identity base)
            ctx (:context loaded)
            before (resident/snapshot ctx)
            called (resident/call ctx (:file loaded) hosted-model/answer-name [nil [128 255]]
                                  {:arguments [:erased :bytes] :result :bytes})
            after (resident/snapshot (:context called))]
        (is (= [128 255] (:value called)) (str backend))
        (is (= 0 (get-in after [:world :result])))
        (is (= (count (get-in before [:world :heap])) (count (get-in after [:world :heap]))))
        (is (= (:heap (:world before)) (:heap (:world (resident/snapshot ctx)))))
        (doseq [context [base ctx (:context called)]] (resident/close! context))))))

(deftest unboxed-scalar-result-is-rejected-before-encoding
  (let [bundle (boxed-model-bundle
                #(-> % (assoc :dependencies [])
                     (assoc-in [:ir :fdecl :type] "uint64")
                     (assoc-in [:ir :fdecl :body] ["ret" {:var {:id {:idx 2}}}])))]
    (doseq [backend backends]
      (let [base (model/context backend true bundle)
            loaded (model/load-identity base)
            ctx (:context loaded)]
        (with-redefs [codec/encode-boxed (fn [& _] (throw (AssertionError. "encoding must not begin")))]
          (is (thrown-with-msg? clojure.lang.ExceptionInfo #"boxed entrypoint ABI"
                                (resident/call ctx (:file loaded) hosted-model/answer-name [nil 42]
                                               {:arguments [:erased :nat] :result :uint64}))))
        (doseq [context [base ctx]] (resident/close! context))))))

(deftest adoption-rejects-paused-or-active-guest-execution
  (let [prepared (model/prepared :reference true @hosted-model/captured)]
    (doseq [world [(assoc (:world prepared) :status :paused)
                   (assoc (:world prepared) :status :running)
                   (assoc (:world prepared) :status :done :frames [:modeled-frame])
                   (assoc (:world prepared) :host-request {:modeled-request true})]]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"idle guest execution"
                            (adopt (assoc prepared :world world)))))))

(deftest diagnostic-new-environment-releases-old-owner-only-in-returned-branch
  (doseq [backend backends]
    (let [prepared (model/prepared backend false nil)
          envelope (assoc (frontend-model/envelope false)
                          :fileName hosted-model/file-path
                          :mainModule ["str" ["anonymous"] "PreludeIdentity"])
          ;; Explicit compiler MODEL consumes its owned arguments, then returns a
          ;; genuinely distinct Environment in the normal IO(pair Env envelope).
          compiler {:params [1 2 3 4 5 6 7]
                    :body (frontend-model/drop-args [1 2 3 4 5 6]
                                                    [:let 10 [:ctor 0 [[:imm 0]]]
                                                     [:let 8 [:ctor 0 [[:var 10] [:imm (json/write-str envelope)]]]
                                                      [:let 9 [:ctor 0 [[:var 8]]] [:return [:var 9]]]]])}
          functions (assoc (get-in prepared [:world :functions]) frontend/compile-target compiler)
          prepared (-> prepared (assoc-in [:world :functions] functions)
                       (assoc :session (raw/open-functions functions {} {:backend backend})))
          base (adopt prepared)
          before (resident/snapshot base)
          old (:environment before)
          loaded (model/load-identity base)
          next (:context loaded)
          after (resident/snapshot next)
          new (:environment after)]
      (is (false? (:success loaded)) (str backend))
      (is (seq (:diagnostics loaded)))
      (is (nil? (:file loaded)))
      (is (not= old new))
      (is (= 1 (:rc (m/node (:world after) new))))
      (testing "only the original kernel-association anchor remains in the new branch"
        (is (= 1 (:rc (m/node (:world after) old)))))
      (is (= 2 (:rc (m/node (:world (resident/snapshot base)) old))))
      (is (not (contains? (get-in before [:world :heap]) (:id new))))
      (is (= 1 (:rc (m/node (:world after) (:options after)))))
      (is (identical? (get-in after [:world :functions]) (get-in after [:session :functions])))
      (resident/close! next)
      (is (= 2 (:rc (m/node (:world (resident/snapshot base)) old))))
      (resident/close! base))))
