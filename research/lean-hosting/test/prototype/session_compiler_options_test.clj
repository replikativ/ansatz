(ns prototype.session-compiler-options-test
  "Compiler selection composition; frontend helpers remain explicit models."
  (:require [clojure.test :refer [deftest is]]
            [prototype.session-compiler-options :as selection]
            [prototype.typed-tail-test :as fixture]
            [prototype.typed-tail-execution-test :as execution-fixture]
            [prototype.typed-tail-execution :as execution]
            [prototype.typed-tail :as tail]
            [prototype.typed-ir :as typed]
            [prototype.raw-interop :as raw]
            [prototype.interop :as interop]
            [prototype.machine :as m]
            [prototype.lazy-runtime :as lazy]
            [prototype.resident-frontend :as resident]
            [prototype.resident-frontend-test :as resident-model]
            [prototype.hosted-file-test :as hosted-model]))

(defn input [] (fixture/bundle "scalar-wrapper-programs.jsonl"))
(defn options [input] {:typed-tail (execution-fixture/config input)})

(defn observe-route [events compile]
  (fn [& args]
    (when-let [artifact (apply compile args)]
      (when (= :typed-tail (get-in artifact [:specialization :kind]))
        (swap! events conj :typed-tail))
      (reduce (fn [out key]
                (if-let [execute (get out key)]
                  (assoc out key (fn [& args]
                                   (let [result (apply execute args)]
                                     (swap! events conj [(get-in artifact [:specialization :kind]) result]) result)))
                  out)) artifact [:execute! :execute-budget!]))))

(deftest closed-pure-selection-and-default-construction
  (let [input (input) fs (:runtime input) opts (options input)
        root (fixture/target (:typed input) "sum64")
        owner (Object.)
        decorated (with-meta (assoc-in opts [:typed-tail :typed-functions root]
                                       (with-meta (get-in opts [:typed-tail :typed-functions root]) {:owner owner}))
                             {:owner owner})
        normalized (selection/validate fs decorated)]
    (is (= opts normalized))
    (is (nil? (meta normalized)))
    (is (nil? (meta (get-in normalized [:typed-tail :typed-functions root]))))
    (doseq [bad [nil {:unknown {}} {:prototype.block-compile/tail-provider {:bind identity}}
                 {:typed-tail (assoc (:typed-tail opts) :owner owner)}
                 {:scalar-wrappers (java.util.HashMap.)}]]
      (is (thrown? clojure.lang.ExceptionInfo (raw/open-functions fs {} {:compiler-options bad}))))
    (is (not (contains? (raw/open-functions fs {}) :compiler-options)))
    (is (not (contains? (interop/open-functions fs {} :jvm (lazy/code-cache)) :compiler-options)))
    (with-redefs [tail/prepare-region (fn [& _] (throw (AssertionError. "Pattern plan on non-JVM backend")))]
      (doseq [backend [:reference :mutable]]
        (is (= opts (:compiler-options (raw/open-functions fs {} {:backend backend :compiler-options opts}))))))))

(deftest stale-source-and-wrapper-facts-fail-before-adoption
  (let [input (input) fs (:runtime input) opts (options input)
        root (fixture/target (:typed input) "sum64")
        wrapper (first (keys (:descriptors input)))
        old (raw/open-functions fs {} {:compiler-options opts})
        cache (:cache old) cached @cache]
    (let [same-value-different-carrier (update-in fs [root :body 2 1] bigint)]
      (is (= fs same-value-different-carrier))
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"does not match executable code"
                           (selection/validate same-value-different-carrier opts))))
    (doseq [changed [(assoc-in fs [root :body] [:return [:imm 91]])
                     (assoc-in fs [wrapper :runtime-extern] "wrong")
                     (dissoc fs root)]]
      (doseq [backend [:reference :mutable :jvm]]
        (is (thrown-with-msg? clojure.lang.ExceptionInfo #"does not match executable code"
                             (raw/open-functions changed {} (assoc (raw/session-options old) :backend backend))))))
    (is (= cached @cache))
    (is (identical? fs (:functions old)))
    (is (= opts (:compiler-options old)))))

(deftest malformed-data-budgets-precede-copy-expansion-and-fingerprints
  (let [input (input) fs (:runtime input) opts (options input)
        root (fixture/target (:typed input) "sum64")
        wide (vec (repeat 200001 nil))
        deep (reduce (fn [x _] [x]) 0 (range 257))
        large (.shiftLeft java.math.BigInteger/ONE 4097)
        many (mapv #(.add (.shiftLeft java.math.BigInteger/ONE 4095) (biginteger %)) (range 257))
        only-root (-> opts (assoc-in [:typed-tail :typed-functions] {root (get-in opts [:typed-tail :typed-functions root])})
                           (assoc-in [:typed-tail :roots] [root]))
        fingerprints (atom 0) expanded (atom 0) original-vec vec]
    (with-redefs [typed/typed-code-key (fn [& _] (swap! fingerprints inc) (throw (AssertionError. "early hash")))
                  clojure.core/vec (fn [x] (when (identical? wide x) (swap! expanded inc)) (original-vec x))]
      (doseq [bad [wide deep large many]]
        (is (thrown? clojure.lang.ExceptionInfo (selection/validate fs {:typed-tail bad}))))
      (is (thrown? clojure.lang.ExceptionInfo
                   (selection/validate (assoc-in fs [root :body] deep) only-root)))
      (is (zero? @fingerprints))
      (is (zero? @expanded)))
    (let [dag (reduce (fn [x _] [x x]) [0] (range 20))
          copied (#'selection/pure-copy dag)]
      (is (identical? (first copied) (second copied)))
      (is (nil? (meta copied))))))

(deftest raw-and-convenient-calls-use-actual-selected-executor
  (let [input (input) fs (:runtime input) opts (options input)
        target (fixture/target (:typed input) "sum64") events (atom [])
        compile execution/compile-entry]
    (with-redefs [execution/compile-entry (observe-route events compile)]
      (let [session (raw/open-functions fs {} {:compiler-options opts})
            world (m/world fs) result (raw/call session world target [10N 0N])
            convenient (interop/open-functions fs {} :jvm (lazy/code-cache) {:compiler-options opts})]
        (is (= 55N (:value result)))
        (is (= 55N (:value (interop/call convenient target [10N 0N]))))
        (is (= opts (:compiler-options convenient)))
        (is (some #{:typed-tail} @events))
        (is (some #{[:typed-tail :specialized]} @events))
        (is (= world (m/world fs)))))))

(deftest callbacks-install-link-and-backend-roundtrips-retain-selection
  (let [input (input) opts (options input) target (fixture/target (:typed input) "sum64")
        root (fixture/name-of "compilerCallback") linked (fixture/name-of "linkedSeven")
        signature {:params [] :return-type "uint64"}
        functions (assoc (:runtime input) root
                         {:params [] :raw-extern {:symbol "compiler_callback" :signature signature}
                          :body [:host "compiler_callback" [] 0 [:return [:var 0]]]})
        catalogue {:manifests [{:kind "manifest" :schema "lean-ir-probe/1" :leanVersion "4.33.1"
                               :runtimeProfile {:target "x86_64-unknown-linux-gnu" :wordBits 64}}]
                   :declarations {linked {:kind "decl" :name linked :runtime {:role "ordinary" :initializer nil}
                                          :ir {:fdecl {:f linked :xs [] :type "object"
                                                       :body ["vdecl" {:idx 1} "object" {:lit {:v {:num {:v 7}}}}
                                                              ["ret" {:var {:id {:idx 1}}}]]}}}}}
        binding {:signature signature
                 :handler (fn [{:keys [switch-backend! install-compiled! link-trusted! invoke]} world _]
                            (let [[world _] (install-compiled! world (slurp "fixtures/runtime-compiled-identity.jsonl") {})
                                  [world _] (link-trusted! world catalogue [linked] (fn [_ new] (is (contains? new linked))))
                                  world (switch-backend! world :reference)
                                  world (switch-backend! world :mutable)
                                  world (switch-backend! world :jvm)]
                              (invoke world target [10N 0N])))}
        cache (lazy/code-cache) events (atom []) compile execution/compile-entry
        session (raw/open-functions functions {"compiler_callback" binding}
                                    {:cache cache :compiler-options opts})
        world (m/world functions)]
    (with-redefs [execution/compile-entry (observe-route events compile)]
      (let [result (raw/call session world root []) next (:session result)]
        (is (= 55N (:value result)))
        (is (= opts (:compiler-options next)))
        (is (identical? cache (:cache next)))
        (is (identical? cache (get-in next [:program :cache])))
        (is (identical? binding (get-in next [:bindings "compiler_callback"])))
        (is (some #{:typed-tail} @events))
        (is (some #{[:typed-tail :specialized]} @events))
        (is (not (contains? (:functions world) linked)))
        (is (identical? functions (:functions session)))))))

(deftest modeled-frontend-and-resident-extension-preserve-selected-code-and-cache
  (let [input (input) opts (options input)
        prepared (resident-model/prepared :jvm true @hosted-model/captured)
        functions (merge (get-in prepared [:world :functions]) (:runtime input))
        cache (get-in prepared [:session :cache])
        prepared (assoc prepared :world (assoc (:world prepared) :functions functions)
                                 :session (raw/open-functions functions {} {:cache cache :compiler-options opts}))
        base (resident/adopt-prepared prepared {:trusted-functions functions :trusted-bindings {}
                                               :application-extern-symbols #{"application_answer"}})
        extension {:signature {:params [] :return-type "object"} :handler (fn [_ world _] [world 42])}
        extended (resident/with-externs base {"application_answer" extension})
        loaded (resident-model/load-identity extended)]
    (try
      (is (:success loaded))
      (doseq [context [base extended (:context loaded)]
              :let [p (resident/snapshot context)]]
        (is (= opts (get-in p [:session :compiler-options])))
        (is (identical? cache (get-in p [:session :cache]))))
      (is (not (contains? (get-in (resident/snapshot base) [:session :bindings]) "application_answer")))
      (is (identical? extension (get-in (resident/snapshot (:context loaded)) [:session :bindings "application_answer"])))
      (finally (doseq [context [base extended (:context loaded)]] (resident/close! context))))))
