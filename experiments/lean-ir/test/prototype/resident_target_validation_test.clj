(ns prototype.resident-target-validation-test
  "Resident call-boundary models over captured identity IR; no Init or frontend."
  (:require [clojure.test :refer [deftest is]]
            [prototype.resident-frontend :as resident]
            [prototype.resident-frontend-test :as fixture]
            [prototype.hosted-file-test :as hosted]
            [prototype.eval-const :as eval]
            [prototype.interop-codec :as codec]
            [prototype.module-import :as imports])
  (:import [java.util WeakHashMap]
           [prototype.executable_closure_proof ExecutableClosureProof]))

(defn with-loaded [backend f]
  (let [base (fixture/context backend) owners (atom [base])
        own! (fn [context] (swap! owners conj context) context)]
    (try
      (let [loaded (fixture/load-identity base) parent (own! (:context loaded)) file (:file loaded)
            call! (fn [context]
                    (let [result (resident/call context file hosted/answer-name [nil 42] fixture/identity-signature)]
                      (own! (:context result))
                      (is (= 42 (:value result)))
                      (:context result)))]
        (f {:parent parent :file file :own! own! :call! call!}))
      (finally (doseq [context (reverse @owners)] (resident/close! context))))))

(defn counting [f]
  (let [calls (atom 0) original eval/validate-executables!]
    (with-redefs [eval/validate-executables! (fn [& args] (swap! calls inc) (apply original args))]
      (f calls))))

(deftest parent-child-and-fork-reuse-without-owner-atom-writes
  (doseq [backend [:reference :mutable :jvm]]
    (with-loaded backend
      (fn [{:keys [parent own! call!]}]
        (counting
          (fn [calls]
            (let [state (.-state ^prototype.resident_frontend.Context parent) before @state writes (atom 0)]
              (add-watch state ::writes (fn [& _] (swap! writes inc)))
              (try
                (let [child (call! parent)]
                  (is (= 1 @calls))
                  (call! parent)
                  (call! child)
                  (call! (own! (resident/fork parent)))
                  (call! (own! (resident/fork child)))
                  (is (= 1 @calls))
                  (is (identical? before @state))
                  (is (zero? @writes)))
                (finally (remove-watch state ::writes))))))))))

(deftest warm-proof-keeps-current-file-initialization-abi-ownership-and-code-checks
  (with-loaded :jvm
    (fn [{:keys [parent file call!]}]
      (counting
        (fn [calls]
          (call! parent)
          (let [state (.-state ^prototype.resident_frontend.Context parent) original @state
                prepared (:prepared original) world (:world prepared)
                digest (.-digest ^prototype.resident_frontend.FileHandle file)
                target (eval/boxed-entrypoint! world digest (#'resident/structured-name hosted/answer-name))
                environment (:environment prepared)
                alterations
                [(fn [p] (update-in p [:world :eval-const-authorizations :units digest] with-meta {:other true}))
                 (fn [p] (assoc-in p [:world :eval-const-authorizations :initializations digest :status] :running))
                 (fn [p] (assoc-in p [:world :eval-const-authorizations :declarations target :ir :fdecl :type] "uint64"))
                 (fn [p] (update-in p [:world :heap] dissoc (:id environment)))
                 (fn [p] (assoc-in p [:world :frames] [{}]))
                 (fn [p] (let [functions (assoc (get-in p [:world :functions]) (:root imports/helpers) {})]
                           (-> p (assoc-in [:world :functions] functions) (assoc-in [:session :functions] functions))))]]
            (try
              (with-redefs [codec/encode-boxed (fn [& _] (throw (AssertionError. "must reject before encoding")))]
                (doseq [alter alterations]
                  (reset! state (assoc original :prepared (alter prepared)))
                  (is (thrown? clojure.lang.ExceptionInfo
                               (resident/call parent file hosted/answer-name [nil 42] fixture/identity-signature)))
                  (reset! state original)))
              (is (= 1 @calls))
              (call! parent)
              (is (= 1 @calls))
              (finally (reset! state original)))))))))

(deftest changed-authorization-registry-misses-and-rejects-before-encoding
  (with-loaded :jvm
    (fn [{:keys [parent file call!]}]
      (counting
        (fn [calls]
          (call! parent)
          (let [state (.-state ^prototype.resident_frontend.Context parent) original @state
                world (get-in original [:prepared :world]) digest (.-digest ^prototype.resident_frontend.FileHandle file)
                target (eval/boxed-entrypoint! world digest (#'resident/structured-name hosted/answer-name))]
            (try
              ;; Equal but distinct immutable registry is a miss, not cached authority.
              (reset! state (update-in original [:prepared :world :eval-const-authorizations :functions] with-meta {:new-image true}))
              (call! parent)
              (is (= 2 @calls))
              (reset! state (update-in original [:prepared :world :eval-const-authorizations :functions] dissoc target))
              (with-redefs [codec/encode-boxed (fn [& _] (throw (AssertionError. "must reject before encoding")))]
                (is (thrown-with-msg? clojure.lang.ExceptionInfo #"differs from authorized"
                                     (resident/call parent file hosted/answer-name [nil 42] fixture/identity-signature))))
              (is (= 3 @calls))
              ;; An application-code change is not protected-kernel tampering:
              ;; matching World/session maps must still miss and fail authority.
              (let [functions (update (:functions world) target with-meta {:changed true})]
                (reset! state (-> original
                                  (assoc-in [:prepared :world :functions] functions)
                                  (assoc-in [:prepared :session :functions] functions)))
                (with-redefs [codec/encode-boxed (fn [& _] (throw (AssertionError. "changed code before encoding")))]
                  (is (thrown-with-msg? clojure.lang.ExceptionInfo #"differs from authorized"
                                       (resident/call parent file hosted/answer-name [nil 42] fixture/identity-signature)))))
              (is (= 4 @calls))
              (finally (reset! state original)))))))))

(deftest dependency-rule-redefinition-invalidates-the-resident-slot
  (with-loaded :jvm
    (fn [{:keys [parent call!]}]
      (counting
        (fn [calls]
          (call! parent)
          (let [original eval/executable-dependencies]
            (with-redefs [eval/executable-dependencies (fn [function] (original function))]
              (call! parent)
              (is (= 2 @calls))
              (call! parent)
              (is (= 2 @calls)))))))))

(deftest private-cache-has-weak-context-keys-and-only-opaque-proof-values
  (with-loaded :jvm
    (fn [{:keys [parent call!]}]
      (call! parent)
      (let [table @(ns-resolve 'prototype.resident-frontend 'target-proofs)]
        (is (instance? WeakHashMap table))
        (locking table (is (instance? ExecutableClosureProof (.get ^WeakHashMap table parent))))))))

(deftest current-manifest-target-and-pending-actions-remain-live
  (with-loaded :jvm
    (fn [{:keys [parent file own! call!]}]
      (counting
        (fn [calls]
          (call! parent)
          (let [state (.-state ^prototype.resident_frontend.Context parent) original @state
                digest (.-digest ^prototype.resident_frontend.FileHandle file)
                name (#'resident/structured-name hosted/answer-name)
                unit (get-in original [:prepared :world :eval-const-authorizations :units digest])
                changed (assoc-in unit [:manifest :entryPoints 0 :boxedTarget] name)
                next-file (prototype.resident_frontend.FileHandle. digest changed (.-module ^prototype.resident_frontend.FileHandle file))]
            (try
              ;; Same executable maps, different CURRENT selected root: must miss.
              (reset! state (assoc-in original [:prepared :world :eval-const-authorizations :units digest] changed))
              (let [result (resident/call parent next-file hosted/answer-name [nil 42] fixture/identity-signature)]
                (own! (:context result))
                (is (= 42 (:value result))))
              (is (= 2 @calls))
              (let [pending (assoc-in changed [:manifest :initializationPlan :actions] [{:action {:kind "value" :name name}}])
                    pending-file (prototype.resident_frontend.FileHandle. digest pending (.-module ^prototype.resident_frontend.FileHandle file))]
                (reset! state (assoc-in original [:prepared :world :eval-const-authorizations :units digest] pending))
                (with-redefs [codec/encode-boxed (fn [& _] (throw (AssertionError. "pending initializer before encoding")))]
                  (is (thrown-with-msg? clojure.lang.ExceptionInfo #"pending initializers"
                                       (resident/call parent pending-file hosted/answer-name [nil 42] fixture/identity-signature)))))
              (is (= 2 @calls))
              (finally (reset! state original)))))))))
