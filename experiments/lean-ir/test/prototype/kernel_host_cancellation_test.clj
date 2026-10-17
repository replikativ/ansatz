(ns prototype.kernel-host-cancellation-test
  (:require [clojure.test :refer [deftest is]]
            [prototype.machine :as m]
            [prototype.kernel-host :as host]
            [prototype.kernel-host-test :as prior]
            [prototype.kernel-bridge-test :as guest]
            [ansatz.kernel.name :as name])
  (:import [ansatz.kernel Env]))

(def helpers (merge prior/helpers host/control-helpers))
(defn fixture []
  (let [[world env root] (#'prior/empty-world)
        [world type] (#'prior/sort1 world)
        [world decl] (#'prior/axiom world "WithCancel" type false)
        [world token] (m/resource world "opaque-guest-cancel-token")
        [world option] (m/allocate world :ctor 1 [token])]
    {:world world :environment env :root root :declaration decl :cancel option}))

(defn context [calls set? & {:keys [pre-poll unsupported? flag]}]
  (let [delegate (:invoke (#'prior/context calls))]
    {:invoke
     (fn [world helper args]
       (cond
         (= helper (:cancel-is-set helpers))
         (do (swap! calls conj helper) [world (or flag (if set? 1 0))])
         (= helper (:cancel-result helpers))
         (do (swap! calls conj helper)
             ;; This models only typed ownership. Native 11-case differential
             ;; oracle independently checks genuine guest pre-poll semantics.
             (if unsupported? [world (m/->Tag 0)]
               (let [[world error]
                     (if pre-poll (m/allocate world :ctor 12 [pre-poll]) [world (m/->Tag 16)])
                     [world result] (m/allocate world :ctor 0 [error])]
                 (m/allocate world :ctor 1 [result]))))
         :else (delegate world helper args)))}))

(defn invoke [world env decl cancel ctx]
  ((:handler (host/make-binding helpers {:allow-axioms? true})) ctx world
    [env 200000000 512 decl cancel]))

(deftest unset-token-permits-checking-and-preserves-the-borrowed-option
  (let [{:keys [world environment declaration cancel]} (fixture)
        before world calls (atom [])
        [after result] (invoke world environment declaration cancel (context calls false))
        env (first (:fields (m/node after result))) root (first (:fields (m/node after env)))
        ^Env checked (get-in after [:kernel-environments (:id root) :env])]
    (is (= 1 (:tag (m/node after result))))
    (is (some? (.lookup checked (name/from-string "WithCancel"))))
    (is (= (m/node before cancel) (m/node after cancel)))
    (is (= (:cancel-is-set helpers) (first @calls)))
    (is (not-any? #{(:cancel-result helpers)} @calls))
    (is (= 1 (:rc (m/node after cancel)))))
  ;; A fork can observe a different logical token snapshot. The callback itself
  ;; never runs a guest setter concurrently with the Java checker.
  (let [{:keys [world environment declaration cancel]} (fixture)
        [unset result] (invoke world environment declaration cancel (context (atom []) false))
        [set result2] (invoke world environment declaration cancel (context (atom []) true))]
    (is (= 1 (:tag (m/node unset result))))
    (is (= 0 (:tag (m/node set result2))))
    (is (= (m/->Tag 16) (first (:fields (m/node set result2)))))))

(deftest set-token-returns-real-interrupted-without-checking-or-publication
  (let [{:keys [world environment root declaration cancel]} (fixture)
        before world calls (atom [])
        [after result] (invoke world environment declaration cancel (context calls true))]
    (is (= [(:cancel-is-set helpers) (:cancel-result helpers)] @calls))
    (is (= 0 (:tag (m/node after result))))
    (is (= [(m/->Tag 16)] (:fields (m/node after result))))
    (is (not (contains? (:heap after) (:id environment))))
    (is (not (contains? (:heap after) (:id root))))
    (is (= (m/node before cancel) (m/node after cancel)))
    (is (= (m/node before declaration) (m/node after declaration)))
    (is (nil? (:kernel-environments after)))))

(deftest actual-pre-poll-errors-pass-through-without-being-mislabeled-interrupted
  (let [{:keys [world environment declaration cancel]} (fixture)
        [after result] (invoke world environment declaration cancel
                        (context (atom []) true :pre-poll "duplicate universe parameter"))
        error (first (:fields (m/node after result)))]
    (is (= 12 (:tag (m/node after error))))
    (is (= ["duplicate universe parameter"] (:fields (m/node after error))))))

(deftest invalid-control-helpers-and-unmodeled-set-token-kinds-fail-explicitly
  (let [{:keys [world environment declaration cancel]} (fixture)
        binding (host/make-binding prior/helpers {:allow-axioms? true})]
    (is (thrown-with-msg? Exception #"snapshot helper"
          ((:handler binding) (context (atom []) false) world
           [environment 200000000 512 declaration cancel])))
    (is (thrown-with-msg? Exception #"Invalid guest cancellation Bool"
          (invoke world environment declaration cancel (context (atom []) false :flag 2))))
    (is (thrown-with-msg? Exception #"pre-poll order unsupported"
          (invoke world environment declaration cancel (context (atom []) true :unsupported? true))))))
