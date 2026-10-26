(ns prototype.resident-compiler-options-test
  "Post-load compiler selection over actual emitted boxed IR. The frontend
   envelope/kernel preparation are explicit models, not genuine Lean loading."
  (:require [clojure.test :refer [deftest is]]
            [clojure.java.io :as io] [clojure.data.json :as json] [clojure.string :as str]
            [prototype.resident-frontend :as resident]
            [prototype.resident-frontend-test :as resident-model]
            [prototype.frontend-test :as frontend-model]
            [prototype.hosted-file-test :as hosted-model]
            [prototype.frontend :as frontend]
            [prototype.module-import :as imports]
            [prototype.import-ir :as ir]
            [prototype.runtime-abi :as abi]
            [prototype.raw-interop :as raw]
            [prototype.machine :as m]
            [prototype.interop-codec :as codec]
            [prototype.typed-tail-test :as fixture]
            [prototype.scalar-wrapper-test :as scalar-fixture]
            [prototype.session-compiler-options-test :as session-fixture]
            [prototype.typed-tail-execution :as execution]
            [prototype.lazy-runtime :as lazy])
  (:import [ansatz.kernel Name]))

(def root ["str" ["str" ["anonymous"] "ScalarWrapperProbe"] "sum64"])
(def module ["str" ["anonymous"] "ScalarWrapperProbe"])
(def root-name (Name/fromString "ScalarWrapperProbe.sum64"))
(def call-signature {:arguments [:uint64 :uint64] :result :uint64})

(defn packet []
  ;; Preserve every emitted executable declaration byte-for-byte as data. Only
  ;; the frontend's transport manifest is modeled from the existing capture.
  (let [native (with-open [reader (io/reader (io/file fixture/fixture-dir "boxed-scalar-wrapper-programs.jsonl"))]
                 (mapv #(json/read-str % :key-fn keyword) (line-seq reader)))
        template (json/read-str (first (str/split-lines @hosted-model/captured)) :key-fn keyword)
        manifest (-> template
                     (assoc :requestedRoots [root] :entryPoints [{:name root :boxedTarget ["str" root "_boxed"]}]
                            :initializationPlan (:initializationPlan (first native))))
        bundle (str (str/join "\n" (map json/write-str (cons manifest (rest native)))) "\n")]
    {:bundle bundle :catalogue (ir/index-bundles [(io/file fixture/fixture-dir "boxed-scalar-wrapper-programs.jsonl")])}))

(defn context []
  (let [{:keys [bundle catalogue]} (packet)
        p (resident-model/prepared :jvm true bundle)
        envelope (assoc (frontend-model/envelope true) :fileName "ScalarWrapperProbe.lean"
                        :mainModule module :bundle bundle)
        helper-functions (get-in (frontend-model/setup :jvm envelope (frontend-model/header)) [:world :functions])
        functions (merge (get-in p [:world :functions]) helper-functions)
        prepared (assoc p :world (assoc (:world p) :functions functions) :catalogue catalogue
                         :session (raw/open-functions functions {} {:cache (get-in p [:session :cache])
                                                                  :compile-threshold 1}))]
    (resident/adopt-prepared prepared {:trusted-functions functions :trusted-bindings {}
                                      :application-extern-symbols #{"application_answer"}})))

(defn load-worker [context]
  (resident/load-source context {:text "import Init\n-- frontend transport model; emitted scalar IR is captured\n"
                                 :file-name "ScalarWrapperProbe.lean" :module-name (Name/fromString "ScalarWrapperProbe")
                                 :roots [root-name] :initialization :run}))

(defn selection-from-loaded [context]
  (let [rows (get-in (resident/snapshot context) [:world :eval-const-authorizations :declarations])
        actual (or (get rows root) (throw (ex-info "Worker is not an admitted loaded row" {})))
        [name typed] (ir/lower-typed-declaration actual)
        descriptors (into {} (keep (fn [row] (when-let [d (abi/describe-scalar row scalar-fixture/profile)]
                                             [(:name d) d]))) (vals rows))]
    {:typed-tail {:typed-functions {name typed} :roots [name] :descriptors descriptors
                  :profile scalar-fixture/profile :budgets fixture/budgets}}))

(defn call! [owned context file]
  (let [called (resident/call context file root-name [10N 0N] call-signature)]
    (swap! owned conj (:context called))
    (is (= 55N (:value called)))
    called))

(deftest selected-and-cleared-children-retain-loaded-handles-roots-and-cache
  (let [base (context) owned (atom [base])
        before-load (resident/snapshot base)
        loaded (load-worker base) old (:context loaded) file (:file loaded)
        _ (swap! owned conj old)
        before (resident/snapshot old) selection (selection-from-loaded old)
        events (atom []) compile execution/compile-entry]
    (try
      (is (not (contains? (get-in before-load [:world :functions]) root)))
      (is (:success loaded))
      (is (contains? (get-in before [:world :eval-const-authorizations :declarations]) root))
      (let [selected (resident/with-compiler-options old selection)
            _ (swap! owned conj selected)
            binding {:signature {:params [] :return-type "object"} :handler (fn [_ world _] [world 42])}
            extended (resident/with-externs selected {"application_answer" binding})
            _ (swap! owned conj extended)
            cleared (resident/with-compiler-options extended {}) _ (swap! owned conj cleared)]
        (is (identical? before (resident/snapshot old)))
        (is (not (contains? (:session before) :compiler-options)))
        (doseq [child [selected extended cleared]
                :let [after (resident/snapshot child)]]
          (is (identical? (:world before) (:world after)))
          (is (= (:environment before) (:environment after)))
          (is (= (:options before) (:options after)))
          (is (identical? (get-in before [:session :cache]) (get-in after [:session :cache])))
          (is (= (get-in before [:session :fuel]) (get-in after [:session :fuel])))
          (is (= (get-in before [:session :compile-threshold]) (get-in after [:session :compile-threshold]))))
        (is (= selection (get-in (resident/snapshot selected) [:session :compiler-options])))
        (is (= {} (get-in (resident/snapshot cleared) [:session :compiler-options])))
        (is (identical? binding (get-in (resident/snapshot cleared) [:session :bindings "application_answer"])))
        (with-redefs [execution/compile-entry (session-fixture/observe-route events compile)]
          (call! owned old file)
          (let [seen (count @events)]
            (call! owned selected file)
            (is (some #{[:typed-tail :specialized]} (subvec @events seen))))
          (let [seen (count @events)]
            (call! owned cleared file)
            (is (not (some #{[:typed-tail :specialized]} (subvec @events seen)))))
          (call! owned old file))
        (is (pos? (:cache-hits (lazy/summary (get-in (resident/snapshot cleared) [:session :program]))))))
      (finally (doseq [ctx @owned] (resident/close! ctx))))))

(deftest invalid-selection-fails-without-adopting-a-child-or-changing-the-input
  (let [base (context) loaded (load-worker base) context (:context loaded) file (:file loaded)
        before (resident/snapshot context) selection (selection-from-loaded context)
        owned (atom [base context])]
    (try
      (doseq [bad [nil {:unknown {}} {:prototype.block-compile/tail-provider {:bind identity}}
                   (assoc-in selection [:typed-tail :typed-functions root :body] [:return [:imm 91]])
                   (assoc-in selection [:typed-tail :typed-functions root :owner] (Object.))]]
        (is (thrown? clojure.lang.ExceptionInfo (resident/with-compiler-options context bad)))
        (is (identical? before (resident/snapshot context))))
      (call! owned context file)
      (let [closed (resident/fork context)]
        (resident/close! closed)
        (with-redefs [raw/open-functions (fn [& _] (throw (AssertionError. "closed setter reached constructor")))]
          (is (thrown-with-msg? clojure.lang.ExceptionInfo #"closed"
                               (resident/with-compiler-options closed selection)))))
      (finally (doseq [ctx @owned] (resident/close! ctx))))))

(deftest selection-cannot-bypass-protected-helper-or-host-binding-checks
  (let [base (context) loaded (load-worker base) context (:context loaded)
        binding {:signature {:params [] :return-type "object"} :handler (fn [_ world _] [world 42])}
        extended (resident/with-externs context {"application_answer" binding})
        helper-victim (resident/fork extended) binding-victim (resident/fork extended)]
    (try
      (let [state (.-state ^prototype.resident_frontend.Context helper-victim)
            functions (update (get-in @state [:prepared :world :functions]) (:root imports/helpers)
                              with-meta {:replaced true})]
        (swap! state #(-> % (assoc-in [:prepared :world :functions] functions)
                         (assoc-in [:prepared :session :functions] functions))))
      (swap! (.-state ^prototype.resident_frontend.Context binding-victim)
             assoc-in [:prepared :session :bindings "application_answer"]
             (assoc binding :handler (fn [_ world _] [world 99])))
      (with-redefs [raw/open-functions (fn [& _] (throw (AssertionError. "protected setter reached constructor")))]
        (is (thrown-with-msg? clojure.lang.ExceptionInfo #"protected executable"
                             (resident/with-compiler-options helper-victim {})))
        (is (thrown-with-msg? clojure.lang.ExceptionInfo #"protected host capability"
                             (resident/with-compiler-options binding-victim {}))))
      (is (identical? binding (get-in (resident/snapshot extended) [:session :bindings "application_answer"])))
      (finally (doseq [ctx [base context extended helper-victim binding-victim]] (resident/close! ctx))))))
