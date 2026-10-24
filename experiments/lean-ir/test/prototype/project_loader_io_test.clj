(ns prototype.project-loader-io-test
  "Project storage/transport MODEL with real issued resident FileHandles, actual
   installed IO-shaped IR execution, Context owners and value codecs. No actual
   Lean frontend or Project source graph is loaded; no new host IO capability."
  (:require [clojure.test :refer [deftest is]]
            [clojure.data.json :as json]
            [clojure.string :as str]
            [prototype.project-loader :as loader]
            [prototype.project-loader-test :as protocol]
            [prototype.project-discovery-test :as files]
            [prototype.resident-frontend :as resident]
            [prototype.resident-frontend-test :as model]
            [prototype.hosted-file-test :as hosted]
            [prototype.interop-codec :as codec]
            [prototype.machine :as m])
  (:import [ansatz.kernel Name]
           [java.util WeakHashMap]))

(def module (files/wire ["PreludeIdentity"]))
(def io-signature {:arguments [:bytes] :result :bytes})
(defn- argument [index] {:var {:id {:idx index}}})
(defn- io-bundle [mode]
  ;; Explicitly modified captured IR, not a newly compiled Lean IO definition.
  ;; Constructor transfers its owned input into the Result.ok/error field.
  (->> (str/split-lines @hosted/captured)
       (map #(json/read-str % :key-fn keyword))
       (map (fn [row]
              (if (= ["str" ["str" ["anonymous"] "answer"] "_boxed"] (:name row))
                (-> row
                    (assoc :dependencies [])
                    (assoc-in [:ir :fdecl :xs]
                              [{:x {:idx 1} :ty "object" :borrow false}
                               {:x {:idx 2} :ty "void" :borrow false}])
                    (assoc-in [:ir :fdecl :type] (if (= mode :unboxed) "uint64" "object"))
                    (assoc-in [:ir :fdecl :body]
                              (if (= mode :unboxed) ["ret" (argument 1)]
                                ["vdecl" {:idx 3} "object"
                                 {:ctor {:i {:cidx (if (= mode :error) 1 0) :size 1 :usize 0 :ssize 0}
                                         :ys [(argument 1)]}}
                                 ["ret" (argument 3)]])))
                row)))
       (map json/write-str)
       (str/join "\n")))

(defn- fixture-state [project]
  (let [^WeakHashMap registry @#'loader/versions]
    (locking registry (.get registry project))))

(defn- with-project [backend mode f]
  (files/with-files {["PreludeIdentity"] "-- protocol-only Project storage\n"}
    (fn [_ provider]
      (let [contexts (atom []) projects (atom [])]
        (try
          (let [base (model/context backend true (if (= mode :ordinary) @hosted/captured (io-bundle mode)))
                _ (swap! contexts conj base)
                loaded (model/load-identity base) ctx (:context loaded)
                _ (swap! contexts conj ctx)
                ;; These profile descriptors are protocol-only. invoke does not
                ;; use them; this does not issue graph/prefix/import authority.
                options (assoc (protocol/options {:configuration {}} provider)
                               :prefix (Object.) :profile (Object.))
                project (loader/open-project ctx options)
                _ (swap! projects conj project)
                ;; Model only the stored-file/export result of Project loading.
                ;; FileHandle itself is actually issued by resident/load-source.
                _ (swap! (fixture-state project) assoc
                         :files {["PreludeIdentity"] (:file loaded)}
                         :exports {["PreludeIdentity"] [hosted/answer-name]})]
            (f {:project project :context ctx :file (:file loaded)
                :own-project! #(do (swap! projects conj %) %)
                :own-contexts! #(swap! contexts into %)}))
          (finally
            (doseq [p (reverse @projects)] (loader/close-project! p))
            (doseq [ctx (reverse @contexts)] (resident/close! ctx))))))))

(defn- failure! [f own-contexts!]
  (let [cause (try (f) nil (catch clojure.lang.ExceptionInfo cause cause))]
    (own-contexts! (:project-owned-contexts (ex-data cause)))
    cause))

(deftest explicit-io-value-new-version-parent-and-close-ownership
  (doseq [backend [:reference :mutable :jvm]]
    (with-project backend :success
      (fn [{:keys [project file own-project!]}]
        (let [parent-data (#'loader/version! project)
              before (resident/snapshot (:context parent-data))
              called (loader/invoke-io project module hosted/answer-name [[0 128 255]] io-signature)
              child (own-project! (:project called))
              child-data (#'loader/version! child)
              after (resident/snapshot (:context child-data))]
          (is (instance? prototype.resident_frontend.FileHandle file))
          (is (= [0 128 255] (:value called)) (str backend))
          (is (not (identical? project child)))
          (is (not (identical? (:context parent-data) (:context child-data))))
          (is (not (identical? (:baseline parent-data) (:baseline child-data))))
          (is (identical? before (resident/snapshot (:context parent-data))))
          (is (= (count (:heap (:world before))) (count (:heap (:world after)))))
          (is (= 0 (get-in after [:world :result])))
          (is (identical? (get-in before [:session :cache]) (get-in after [:session :cache])))
          (loader/close-project! project)
          (loader/close-project! project)
          (is (thrown-with-msg? clojure.lang.ExceptionInfo #"closed"
                                (loader/invoke-io project module hosted/answer-name [[]] io-signature)))
          (let [again (loader/invoke-io child module hosted/answer-name [[7]] io-signature)]
            (own-project! (:project again))
            (is (= [7] (:value again)))))))))

(deftest explicit-export-file-and-argument-contracts-reject-before-encoding
  (with-project :reference :success
    (fn [{:keys [project own-contexts!]}]
      (let [before (resident/snapshot (:context (#'loader/version! project)))]
        (with-redefs [codec/encode-boxed (fn [& _] (throw (AssertionError. "encoding must not start")))]
          (is (thrown-with-msg? clojure.lang.ExceptionInfo #"explicit export"
                                (loader/invoke-io project module (Name/fromString "notExported") [[]] io-signature)))
          (is (thrown-with-msg? clojure.lang.ExceptionInfo #"stored FileHandle"
                                (loader/invoke-io project (files/wire ["Missing"]) hosted/answer-name [[]] io-signature)))
          (let [cause (failure! #(loader/invoke-io project module hosted/answer-name []
                                                  {:arguments [] :result :bytes}) own-contexts!)]
            (is (= :invoke-io (:project-operation (ex-data cause))))
            (is (re-find #"matching codecs and arity" (.getMessage cause)))
            (is (= 2 (count (:project-owned-contexts (ex-data cause)))))
            (is (every? #(map? (resident/snapshot %)) (:project-owned-contexts (ex-data cause))))))
        (is (identical? before (resident/snapshot (:context (#'loader/version! project)))))))))

(deftest stale-issued-file-and-unboxed-result-abi-are-rejected
  (with-project :reference :success
    (fn [{:keys [project own-contexts!]}]
      (with-project :reference :success
        (fn [{other-file :file}]
          ;; Negative storage model: real handle from an independent generation.
          (swap! (fixture-state project) assoc-in [:files ["PreludeIdentity"]] other-file)
          (with-redefs [codec/encode-boxed (fn [& _] (throw (AssertionError. "encoding must not start")))]
            (let [cause (failure! #(loader/invoke-io project module hosted/answer-name [[]] io-signature)
                                  own-contexts!)]
              (is (= :invoke-io (:project-operation (ex-data cause))))
              (is (re-find #"different context generation" (.getMessage cause)))))))))
  (with-project :reference :unboxed
    (fn [{:keys [project own-contexts!]}]
      (with-redefs [codec/encode-boxed (fn [& _] (throw (AssertionError. "encoding must not start")))]
        (let [cause (failure! #(loader/invoke-io project module hosted/answer-name [[]] io-signature)
                              own-contexts!)]
          (is (= :invoke-io (:project-operation (ex-data cause))))
          (is (re-find #"boxed entrypoint ABI" (.getMessage cause))))))))

(deftest io-error-retains-canonical-packet-and-owned-result-without-cleanup
  (doseq [backend [:reference :mutable :jvm]]
    (with-project backend :error
      (fn [{:keys [project own-contexts!]}]
        (let [parent (#'loader/version! project) before (resident/snapshot (:context parent))
              cause (failure! #(loader/invoke-io project module hosted/answer-name [[1 2]] io-signature)
                              own-contexts!)
              data (ex-data cause) world (:checkpoint data) session (:checkpoint-session data)
              wrapper (:resident-owned-result data) payload (:guest-error data)]
          (is (= :invoke-io (:project-operation data)) (str backend))
          (is (= :guest-error (:type data)))
          (is (= :call (:resident-operation data)))
          (is (= payload (first (:fields (m/node world wrapper)))))
          (is (= 1 (:rc (m/node world wrapper))))
          (is (= 1 (:rc (m/node world payload))))
          (is (= [1 2] (:bytes (m/node world payload))))
          (is (= wrapper (:result world)))
          (is (identical? (:functions world) (:functions session)))
          (is (= 2 (count (:project-owned-contexts data))))
          (is (every? #(map? (resident/snapshot %)) (:project-owned-contexts data)))
          (is (identical? before (resident/snapshot (:context parent))))
          ;; Closing the input version must not prematurely consume diagnostic
          ;; Contexts, wrapper or payload in their distinct immutable packet.
          (loader/close-project! project)
          (is (every? #(map? (resident/snapshot %)) (:project-owned-contexts data)))
          (is (= 1 (:rc (m/node world wrapper))))
          (let [released (m/release world wrapper 1)]
            (is (not (contains? (:heap released) (:id wrapper))))
            (is (not (contains? (:heap released) (:id payload)))))
          (is (= 1 (:rc (m/node world payload)))))))))

(deftest ordinary-invoke-retains-existing-dispatch-and-error-tag
  (with-project :reference :ordinary
    (fn [{:keys [project own-project! own-contexts!]}]
      (with-redefs [resident/call-io (fn [& _] (throw (AssertionError. "ordinary invoke must not dispatch IO")))]
        (let [called (loader/invoke project module hosted/answer-name [nil 42] model/identity-signature)]
          (own-project! (:project called))
          (is (= 42 (:value called))))
        (let [cause (failure! #(loader/invoke project module hosted/answer-name [] model/identity-signature)
                              own-contexts!)]
          (is (= :invoke (:project-operation (ex-data cause)))))))))

(deftest closed-current-context-failure-retains-already-forked-baseline
  (with-project :reference :success
    (fn [{:keys [project own-contexts!]}]
      (resident/close! (:context (#'loader/version! project)))
      (let [cause (failure! #(loader/invoke-io project module hosted/answer-name [[]] io-signature)
                            own-contexts!)
            data (ex-data cause)]
        (is (= :invoke-io (:project-operation data)))
        (is (re-find #"closed" (.getMessage cause)))
        (is (= 1 (count (:project-owned-contexts data))))
        (is (map? (resident/snapshot (first (:project-owned-contexts data)))))))))
