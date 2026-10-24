(ns prototype.resident-binding-dependencies-test
  "Resident authority models with a real kernel binding declaration. Guest
   publication bodies are model code and are never invoked by these tests."
  (:require [clojure.test :refer [deftest is]]
            [prototype.resident-frontend :as resident]
            [prototype.resident-frontend-test :as fixture]
            [prototype.hosted-file-test :as hosted]
            [prototype.module-import :as imports]
            [prototype.kernel-host :as kernel]
            [prototype.raw-interop :as raw]))
(defn target [part] ["str" ["str" ["anonymous"] "ProtectedKernel"] part])
(def leaf (target "errorLeaf"))
(def application-dependency (target "applicationDependency"))
(defn setup []
  (let [before (fixture/prepared :reference true @hosted/captured)
        helpers (merge (select-keys imports/helpers [:root :constant-map :quot-init?])
                       (into {} (map (fn [role] [role (target (name role))])
                                    [:empty? :definition :definition-any :axiom :error :compiler-marker
                                     :theorem :opaque :mutual :generated :generated-nested :encode-family
                                     :cancel-is-set :cancel-result])))
        binding (kernel/make-binding helpers {:allow-axioms? true})
        old-functions (get-in before [:world :functions])
        functions (reduce (fn [out name]
                            (if (contains? out name) out
                              (assoc out name {:params [] :body (if (= name (:error helpers))
                                                                 [:tail [:direct leaf] []]
                                                                 [:return [:imm 0]])})))
                          (assoc old-functions leaf {:params [] :body [:return [:imm 0]]}
                                               application-dependency {:params [] :body [:return [:imm 0]]})
                          (:guest-helper-roots binding))
        bindings {"lean_elab_add_decl" binding}
        prepared (-> before (assoc-in [:world :functions] functions)
                     (assoc :session (raw/open-functions functions bindings {:backend :reference})))
        configuration {:trusted-functions functions :trusted-bindings bindings :kernel-helpers helpers
                       :application-extern-symbols #{"application_answer"}}]
    {:prepared prepared :configuration configuration :helpers helpers :binding binding}))
(defn altered [prepared name]
  (let [functions (assoc (get-in prepared [:world :functions]) name {:params [] :body [:return [:imm 99]]})]
    (-> prepared (assoc-in [:world :functions] functions) (assoc-in [:session :functions] functions))))

(deftest independent-helper-closures-protect-adopt-fork-extern-extension-and-readoption
  (let [{:keys [prepared configuration helpers binding]} (setup)
        base (resident/adopt-prepared prepared configuration)
        fork (resident/fork base)
        added {:signature {:params [] :return-type "object"} :handler (fn [_ w _] [w 0])}
        extended (resident/with-externs fork {"application_answer" added})
        again (resident/adopt-prepared (resident/snapshot base) configuration)]
    (try
      (doseq [context [base fork extended again]]
        (is (identical? binding (get-in (resident/snapshot context) [:session :bindings "lean_elab_add_decl"])))
        (doseq [name [(:definition helpers) (:error helpers) (:generated helpers)
                     (:encode-family helpers) (:cancel-result helpers) leaf]]
          ;; Deliberately alter BOTH candidate maps while preserving the binding;
          ;; persistent Context authority must still reject this host mutation.
          (let [state (.-state ^prototype.resident_frontend.Context context) before @state]
            (try
              (swap! state update :prepared altered name)
              (is (thrown-with-msg? clojure.lang.ExceptionInfo #"protected executable"
                                    (resident/fork context)))
              (is (thrown-with-msg? clojure.lang.ExceptionInfo #"protected executable"
                                    (resident/with-externs context {})))
              (finally (reset! state before))))))
      (finally (doseq [context [base fork extended again]] (resident/close! context))))))

(deftest altered-helper-code-and-candidate-binding-metadata-fail-before-guest-association
  (let [{:keys [prepared configuration helpers binding]} (setup)
        calls (atom 0)]
    (with-redefs [kernel/inherit-checked-association
                  (fn [& _] (swap! calls inc) (throw (AssertionError. "No guest work before fixed closure checks")))]
      (doseq [name [(:definition helpers) (:error helpers) (:generated helpers) (:encode-family helpers) leaf]]
        (is (thrown? clojure.lang.ExceptionInfo
                     (resident/adopt-prepared (altered prepared name) configuration))))
      (doseq [forged [(assoc binding :guest-helper-roots [])
                      (assoc binding :kernel-policy {:allow-axioms? false})
                      (dissoc binding :guest-helper-roots)]]
        (is (thrown-with-msg? clojure.lang.ExceptionInfo #"capability differs"
                              (resident/adopt-prepared (assoc-in prepared [:session :bindings "lean_elab_add_decl"] forged)
                                                      configuration))))
      (is (thrown? clojure.lang.ExceptionInfo
                   (resident/adopt-prepared prepared (update configuration :trusted-functions dissoc leaf))))
      (is (zero? @calls)))))

(deftest malformed-trusted-declarations-fail-closed-but-absent-legacy-metadata-stays-explicit
  (let [{:keys [prepared configuration binding]} (setup)]
    (doseq [roots [nil [[:not-a-structured-name]] (repeat (target "lazy"))]]
      (let [bad (assoc binding :guest-helper-roots roots)]
        (is (thrown? clojure.lang.ExceptionInfo
                     (resident/adopt-prepared (assoc-in prepared [:session :bindings "lean_elab_add_decl"] bad)
                                             (assoc-in configuration [:trusted-bindings "lean_elab_add_decl"] bad))))))
    ;; This is a deliberate independent host trust decision, not a claim that
    ;; arbitrary callbacks without metadata can be introspected automatically.
    (let [legacy (dissoc binding :guest-helper-roots)
          context (resident/adopt-prepared
                    (assoc-in prepared [:session :bindings "lean_elab_add_decl"] legacy)
                    (assoc-in configuration [:trusted-bindings "lean_elab_add_decl"] legacy))]
      (is (some? context))
      (resident/close! context))))

(deftest explicitly-admitted-application-declarations-protect-only-independent-existing-code
  (let [{:keys [prepared configuration]} (setup)
        base (resident/adopt-prepared prepared configuration)
        binding {:signature {:params [] :return-type "object"}
                 :guest-helper-roots [application-dependency]
                 :handler (fn [_ w _] [w 0])}
        extended (resident/with-externs base {"application_answer" binding})
        next-configuration (assoc-in configuration [:trusted-bindings "application_answer"] binding)
        again (resident/adopt-prepared (resident/snapshot extended) next-configuration)]
    (try
      (doseq [context [extended again]]
        (let [fork (resident/fork context)]
          (try
            (let [state (.-state ^prototype.resident_frontend.Context fork) before @state]
              (try
                (swap! state update :prepared altered application-dependency)
                (is (thrown-with-msg? clojure.lang.ExceptionInfo #"protected executable"
                                      (resident/fork fork)))
                (finally (reset! state before))))
            (finally (resident/close! fork)))))
      (is (thrown? clojure.lang.ExceptionInfo
                   (resident/with-externs base {"application_answer"
                     (assoc binding :guest-helper-roots [(target "missing")])})))
      (is (thrown? clojure.lang.ExceptionInfo
                   (resident/with-externs base {"application_answer"
                     (assoc binding :guest-helper-roots nil)})))
      ;; This dependency is not protected in BASE yet. Even changing both actual
      ;; maps cannot authorize it: explicit admission still uses the independent
      ;; registry captured before candidate mutation.
      (let [state (.-state ^prototype.resident_frontend.Context base) before @state]
        (try
          (swap! state update :prepared altered application-dependency)
          (is (thrown? clojure.lang.ExceptionInfo
                       (resident/with-externs base {"application_answer" binding})))
          (finally (reset! state before))))
      (let [legacy (resident/with-externs base {"application_answer" (dissoc binding :guest-helper-roots)})]
        (is (some? legacy))
        (resident/close! legacy))
      (finally (doseq [context [base extended again]] (resident/close! context))))))
