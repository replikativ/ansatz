(ns prototype.resident-frontend-test
  "Ownership and orchestration MODEL using captured emitted identity IR. These
   tests do not run Lean's actual frontend or establish broader library coverage."
  (:require [clojure.test :refer [deftest is]]
            [prototype.resident-frontend :as resident]
            [prototype.hosted-file-test :as hosted-model]
            [prototype.module-import :as imports]
            [prototype.machine :as m]
            [prototype.raw-interop :as raw]
            [prototype.lazy-runtime :as lazy]
            [prototype.frontend :as frontend]
            [prototype.hosted-file :as hosted]
            [prototype.guest-encoding :as encoding]
            [prototype.interop-codec :as codec])
  (:import [ansatz.kernel Env]))

(defn prepared [backend success bundle]
  (let [p (hosted-model/prepared backend success bundle)
        identity {:params [1] :body [:inc [:var 1] 1 [:return [:var 1]]]}
        functions (merge (get-in p [:world :functions])
                         {(:root imports/helpers) identity
                          (:constant-map imports/helpers) identity
                          (:quot-init? imports/helpers) {:params [1] :body [:return [:imm 0]]}})
        environment (:environment p)
        world (-> (:world p) (assoc :functions functions) (m/retain environment 1)
                  (assoc-in [:kernel-environments (:id environment)]
                            {:anchor environment :env (Env.) :constant-map environment :quot-init? false}))
        cache (lazy/code-cache)]
    (assoc p :world world :session (raw/open-functions functions {} {:backend backend :cache cache :compile-threshold 64}))))
(defn context
  ([backend] (context backend true @hosted-model/captured))
  ([backend success bundle]
   (let [p (prepared backend success bundle)]
     (resident/adopt-prepared p {:trusted-functions (get-in p [:world :functions])
                                 :trusted-bindings (get-in p [:session :bindings])
                                 :application-extern-symbols #{"application_answer" "resident_boundary_io_success"
                                                               "resident_boundary_io_error"}}))))
(defn load-identity [context]
  (resident/load-source context (hosted-model/request :run)))
(def identity-signature {:arguments [:erased :nat] :result :nat})

(deftest resident-load-call-second-load-forks-and-close
  (doseq [backend [:reference :mutable :jvm]]
    (let [base (context backend)
          before (resident/snapshot base)
          loaded (load-identity base)
          active (:context loaded)
          called (resident/call active (:file loaded) hosted-model/answer-name [nil 42] identity-signature)
          fork (resident/fork (:context called))
          second (load-identity (:context called))]
      (is (:success loaded))
      (is (= [] (:diagnostics loaded)))
      (is (= 42 (:value called)))
      (is (:success second))
      (doseq [ctx [base active (:context called) fork (:context second)]
              :let [p (resident/snapshot ctx)]]
        (is (= 2 (:rc (m/node (:world p) (:environment p)))))
        (is (= 1 (:rc (m/node (:world p) (:options p)))))
        (is (identical? (get-in before [:session :cache]) (get-in p [:session :cache]))))
      (resident/close! active)
      (resident/close! active)
      (is (thrown? clojure.lang.ExceptionInfo (resident/snapshot active)))
      (is (= 42 (:value (resident/call fork (:file loaded) hosted-model/answer-name [nil 42] identity-signature))))
      (is (= 1 (:rc (m/node (:world before) (:options before)))))
      (doseq [ctx [base (:context called) fork (:context second)]] (resident/close! ctx)))))

(deftest diagnostic-load-retains-partial-environment-with-one-owner
  (let [base (context :reference false nil)
        loaded (load-identity base)
        p (resident/snapshot (:context loaded))]
    (is (false? (:success loaded)))
    (is (seq (:diagnostics loaded)))
    (is (nil? (:file loaded)))
    (is (= 2 (:rc (m/node (:world p) (:environment p)))))
    (is (= 1 (:rc (m/node (:world p) (:options p)))))
    (resident/close! (:context loaded))
    (resident/close! base)))

(deftest adoption-rejects-unchecked-or-mismatched-state
  (let [p (prepared :reference true @hosted-model/captured)]
    (doseq [bad [(update p :world dissoc :kernel-environments)
                 (update-in p [:session :functions] with-meta {:other true})
                 (dissoc p :options)
                 (assoc p :catalogue {})
                 (assoc-in p [:catalogue :manifests 0 :leanCommit] "wrong")]]
      (is (thrown? clojure.lang.ExceptionInfo
                   (resident/adopt-prepared bad {:trusted-functions (get-in p [:world :functions])
                                                 :trusted-bindings (get-in p [:session :bindings])
                                                 :application-extern-symbols #{"application_answer" "resident_boundary_io_success"
                                                                               "resident_boundary_io_error"}}))))
    (let [functions (assoc (get-in p [:world :functions]) (:root imports/helpers)
                           {:params [1] :body [:return [:imm 0]]})
          bad (-> p (assoc-in [:world :functions] functions)
                  (assoc :session (raw/open-functions functions {} {:backend :reference})))]
      (is (thrown? clojure.lang.ExceptionInfo
                   (resident/adopt-prepared bad {:trusted-functions (get-in p [:world :functions])
                                                 :trusted-bindings {}}))))))

(deftest values-use-boxed-abi-and-result-owners-are-discharged
  (doseq [backend [:reference :mutable :jvm]]
    (let [loaded (load-identity (context backend))
          ctx (:context loaded)
          before (resident/snapshot ctx)]
      (doseq [[descriptor value] [[:string "éλ😀"] [:bytes [0 128 255]]
                                  [:uint64 18446744073709551615N]
                                  [:float -0.0] [[:option :bytes] {:some [1 2]}]]]
        (let [called (resident/call ctx (:file loaded) hosted-model/answer-name [nil value]
                                    {:arguments [:erased descriptor] :result descriptor})
              p (resident/snapshot (:context called))]
          (is (= value (:value called)))
          (is (= 0 (get-in p [:world :result])))
          (is (= (count (get-in before [:world :heap])) (count (get-in p [:world :heap]))))
          (resident/close! (:context called)))))))

(deftest failed-decoding-preserves-the-owned-result-in-its-exact-world
  (let [loaded (load-identity (context :reference))
        error (try (resident/call (:context loaded) (:file loaded) hosted-model/answer-name
                                  [nil [1 2]] {:arguments [:erased :bytes] :result :nat})
                   nil (catch clojure.lang.ExceptionInfo e e))
        data (ex-data error)
        result (:resident-owned-result data)]
    (is error)
    (is (m/ref? result))
    (is (= [1 2] (:bytes (m/node (:checkpoint data) result))))
    (is (= 1 (:rc (m/node (:checkpoint data) result))))
    (is (identical? (get-in data [:checkpoint :functions]) (get-in data [:checkpoint-session :functions])))))

(deftest handles-are-inherited-but-independent-same-digest-units-are-rejected
  (let [base (context :reference)
        a (load-identity (resident/fork base))
        b (load-identity (resident/fork base))]
    (is (= 42 (:value (resident/call (resident/fork (:context a)) (:file a)
                                     hosted-model/answer-name [nil 42] identity-signature))))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"different context generation"
                          (resident/call (:context b) (:file a) hosted-model/answer-name [nil 42] identity-signature)))
    (is (= (get-in (resident/snapshot (:context a)) [:world :next-id])
           (get-in (resident/snapshot (:context b)) [:world :next-id])))))

(deftest deferred-initializers-block-calls-before-argument-encoding
  (let [ctx (context :reference true (hosted-model/initialization-bundle))
        deferred (resident/load-source ctx (hosted-model/request :defer))]
    (with-redefs [codec/encode-boxed (fn [& _] (throw (AssertionError. "encoding must not start")))]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"pending initializers"
                            (resident/call (:context deferred) (:file deferred) hosted-model/answer-name
                                           [nil 42] identity-signature))))))

(deftest application-externs-preserve-cache-and-protect-existing-capabilities
  (let [base (context :mutable)
        binding {:signature {:params [] :return-type "object"} :handler (fn [_ world _] [world 42])}
        ctx (resident/with-externs base {"application_answer" binding})
        p (resident/snapshot ctx)]
    (is (identical? (get-in (resident/snapshot base) [:session :cache]) (get-in p [:session :cache])))
    (is (identical? binding (get-in p [:session :bindings "application_answer"])))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"cannot replace"
                          (resident/with-externs ctx {"application_answer" binding})))
    (is (thrown? clojure.lang.ExceptionInfo (resident/with-externs base {"invalid" {}})))))

(deftest second-encoder-failure-names-earlier-temporary-and-matching-session
  (let [p (prepared :reference true @hosted-model/captured)
        error (try (frontend/compile-file (:session p) (:world p)
                                          {:module-name hosted-model/module-name :roots []}
                                          {:encode-name encoding/encode-name
                                           :encode-names (fn [_ _ _ _] (throw (ex-info "second encoder failed" {})))})
                   nil (catch clojure.lang.ExceptionInfo e e))
        data (ex-data error)]
    (is (re-find #"second encoder" (.getMessage error)))
    (is (= 1 (count (:frontend-temporary-owners data))))
    (is (= 1 (:rc (m/node (:checkpoint data) (first (:frontend-temporary-owners data))))))
    (is (identical? (get-in data [:checkpoint :functions]) (get-in data [:checkpoint-session :functions])))))

(deftest completed-load-is-preserved-if-facade-validation-fails
  (let [ctx (context :reference)
        invoke hosted/run-file
        error (with-redefs [hosted/run-file
                            (fn [& args]
                              (let [compiled (apply invoke args)
                                    functions (update-in (:world compiled) [:functions frontend/compile-target]
                                                         with-meta {:replaced true})
                                    world functions
                                    session (raw/open-functions (:functions world) (get-in compiled [:session :bindings])
                                                                {:backend :reference})]
                                (assoc compiled :world world :session session)))]
                (try (load-identity ctx) nil (catch clojure.lang.ExceptionInfo e e)))
        data (ex-data error)
        completed (:resident-completed-load data)]
    (is (re-find #"protected executable changed" (.getMessage error)))
    (is (:success completed))
    (is (= (:world completed) (:checkpoint data)))
    (is (identical? (get-in data [:checkpoint :functions]) (get-in data [:checkpoint-session :functions])))
    (is (= 3 (:rc (m/node (:checkpoint data) (:environment completed)))))))

(deftest owned-arguments-and-session-remain-inspectable-after-linking-call-failure
  ;; Model the raw driver's documented callback failure packet, with a new linked
  ;; function map/session and an obsolete :session retained by a nested exception.
  (let [loaded (load-identity (context :reference))
        p (resident/snapshot (:context loaded))
        target ["str" ["anonymous"] "linkedDuringCallback"]
        functions (assoc (get-in p [:world :functions]) target {:params [] :body [:return [:imm 1]]})
        session (raw/open-functions functions {} {:backend :reference})
        error (with-redefs [raw/call (fn [old world _ _]
                                       (throw (ex-info "callback failed after linking"
                                                       {:checkpoint (assoc world :functions functions :status :host-call)
                                                        :checkpoint-session session :session old})))]
                (try (resident/call (:context loaded) (:file loaded) hosted-model/answer-name
                                    [nil [1]] {:arguments [:erased :bytes] :result :bytes})
                     nil (catch clojure.lang.ExceptionInfo e e)))
        data (ex-data error)]
    (is (identical? functions (get-in data [:checkpoint :functions])))
    (is (identical? session (:checkpoint-session data)))
    (is (not (identical? (:session data) (:checkpoint-session data))))
    (is (= :call (:resident-operation data)))
    (is (nil? (:resident-owned-result data)))))

(deftest deferred-unit-can-be-initialized-without-recompilation
  (let [ctx (context :reference true (hosted-model/initialization-bundle))
        loaded (resident/load-source ctx (hosted-model/request :defer))
        ready (with-redefs [hosted/run-file (fn [& _] (throw (AssertionError. "must not compile")))]
                (resident/initialize (:context loaded) (:file loaded)))
        twice (resident/initialize ready (:file loaded))]
    (is (= "initialized" (get-in (resident/snapshot ready) [:world :globals hosted-model/cached-name :value])))
    (is (= 42 (:value (resident/call twice (:file loaded) hosted-model/answer-name [nil 42] identity-signature))))
    (is (nil? (get-in (resident/snapshot (:context loaded)) [:world :globals hosted-model/cached-name])))))

(deftest deferred-runtime-symbols-cannot-be-rebound-as-application-externs
  (let [p (prepared :reference true @hosted-model/captured)
        ctx (resident/adopt-prepared p {:trusted-functions (get-in p [:world :functions])
                                        :trusted-bindings {} :application-extern-symbols #{"lean_string_utf8_byte_size"}})
        binding {:signature {:params [{:ty "object" :borrow true}] :return-type "usize"}
                 :handler (fn [_ world _] [world 42])}]
    (is (not (some #(= "lean_string_utf8_byte_size" (:runtime-extern %)) (vals (get-in p [:world :functions])))))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"reserved runtime capability"
                          (resident/with-externs ctx {"lean_string_utf8_byte_size" binding})))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"not admitted by trusted preparation"
                          (resident/with-externs ctx {"unlisted_application_symbol" binding})))))

(deftest selected-guest-helpers-require-independent-executable-authority
  (let [p (prepared :reference true @hosted-model/captured)
        compiler ["str" ["anonymous"] "residentCompiler"]
        witness ["str" ["anonymous"] "residentWitness"]
        functions (assoc (get-in p [:world :functions])
                         compiler (get-in p [:world :functions frontend/compile-target])
                         witness {:params [] :body [:return [:imm 0]]})
        p (assoc p :world (assoc (:world p) :functions functions)
                   :session (raw/open-functions functions {} {:backend :reference}))
        configuration {:trusted-functions functions :trusted-bindings {}
                       :frontend-configuration {:compile-target compiler
                                                :install-options {:witness witness}}}]
    (doseq [target [compiler witness]]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"differs from authorized program"
                            (resident/adopt-prepared p (update configuration :trusted-functions dissoc target))))
      (let [changed (update functions target with-meta {:replaced true})
            candidate (assoc p :world (assoc (:world p) :functions changed)
                               :session (raw/open-functions changed {} {:backend :reference}))]
        (is (thrown-with-msg? clojure.lang.ExceptionInfo #"differs from authorized program"
                              (resident/adopt-prepared candidate configuration)))))
    (let [ctx (resident/adopt-prepared p configuration)
          loaded (load-identity ctx)
          called (resident/call (:context loaded) (:file loaded) hosted-model/answer-name
                                [nil 42] identity-signature)]
      (is (:success loaded))
      (is (= 42 (:value called)))
      ;; Post-compilation checks must retain the selected closure protection.
      (doseq [target [compiler witness]]
        (let [run-file hosted/run-file]
          (with-redefs [hosted/run-file
                        (fn [& args]
                          (let [compiled (apply run-file args)
                                changed (update (get-in compiled [:world :functions]) target
                                                with-meta {:replaced true})]
                            (assoc compiled :world (assoc (:world compiled) :functions changed)
                                            :session (raw/open-functions changed {} {:backend :reference}))))]
            (is (thrown-with-msg? clojure.lang.ExceptionInfo #"protected executable changed"
                                  (load-identity ctx))))))
      (resident/close! (:context called))
      (resident/close! (:context loaded))
      (resident/close! ctx))))

(deftest available-default-witness-is-protected-too
  (let [p (prepared :reference true @hosted-model/captured)
        witness ["str" ["str" ["anonymous"] "RuntimeCompileShim"] "exportEvalConstWitness"]
        functions (assoc (get-in p [:world :functions]) witness {:params [] :body [:return [:imm 0]]})
        p (assoc p :world (assoc (:world p) :functions functions)
                   :session (raw/open-functions functions {} {:backend :reference}))]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"differs from authorized program"
                          (resident/adopt-prepared p {:trusted-functions (dissoc functions witness)
                                                     :trusted-bindings {}})))))
