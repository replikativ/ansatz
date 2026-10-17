(ns ansatz.session-test
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [ansatz.core :as core]
            [ansatz.matchers :as matchers]
            [ansatz.kernel.env :as env]
            [ansatz.session :as session]
            [ansatz.state :as state]
            [ansatz.recall :as recall]
            [ansatz.tactic.instance :as instance]
            [ansatz.simp-index :as simp-index]
            [ansatz.tactic.simp :as simp])
  (:import [ansatz.kernel Env]))

(defn- values [snapshot]
  (update (into {} snapshot) :synth-cache deref))

(defn- empty-session []
  (assoc (session/capture)
         :env (Env.) :instance-index {} :synth-cache (atom {})
         :discr-trie nil :simp-trie nil :store nil :recall-store-path nil
         :instance-caches {} :simp-index-caches nil
         :simp-caches {:env nil :entries {}}))

(use-fixtures :each
  (fn [f]
    (let [previous (session/capture)]
      (try
        (session/activate! (empty-session))
        (f)
        (finally (session/activate! previous))))))

(deftest capture-is-an-independent-proof-context
  (let [snapshot (session/capture)
        live-cache @(ns-resolve 'ansatz.core 'synth-cache)]
    (is (instance? ansatz.core.ProofContext snapshot))
    (is (not (identical? live-cache (:synth-cache snapshot))))
    (swap! live-cache assoc :live :later)
    (is (= {} @(:synth-cache snapshot)))
    (swap! (:synth-cache snapshot) assoc :snapshot :only)
    (is (= {:live :later} @live-cache))))

(deftest nested-store-and-bundled-sessions-restore-all-state
  (let [previous (session/capture)
        store-env (env/with-extension (Env.) :session-test :store)
        descriptor {:store-map {:fixture :borrowed} :store-path "fixture-store" :branch "library"}
        store-session (assoc (empty-session)
                             :env store-env :instance-index {:class [:instance]}
                             :store descriptor :recall-store-path "fixture-store"
                             :discr-trie {:recall :store} :simp-trie {:source :store :trie {}}
                             :synth-cache (atom {:store :synth})
                             :instance-caches {:candidate :generic}
                             :simp-index-caches {:path :store :rules {"lemma" [:rule]}}
                             :simp-caches {:env store-env :entries {:function :info}})
        bundled (empty-session)
        outer
        (session/with-session store-session
          (fn []
            (is (= (values store-session) (values (session/capture))))
            (let [inner (session/with-session bundled
                          (fn []
                            (is (nil? @state/ansatz-store))
                            (is (nil? @recall/store-path))
                            (is (= {} (instance/capture-caches)))
                            (is (nil? (simp-index/capture-caches)))
                            (is (= {:env nil :entries {}} (simp/capture-caches)))
                            (reset! state/ansatz-discr-trie {:inner :updated})
                            :inner-value))]
              (is (= :inner-value (:value inner)))
              (is (= {:inner :updated} (:discr-trie (:session inner)))))
            (is (= (values store-session) (values (session/capture))))
            (is (identical? store-env @state/ansatz-env))
            (swap! @(ns-resolve 'ansatz.core 'synth-cache) assoc :outer :updated)
            (instance/restore-caches! {:outer :cache})
            :outer-value))]
    (is (= :outer-value (:value outer)))
    (is (= {:store :synth :outer :updated} @(:synth-cache (:session outer))))
    (is (= {:outer :cache} (:instance-caches (:session outer))))
    (is (= {:store :synth} @(:synth-cache store-session)))
    (is (= (values previous) (values (session/capture))))))

(deftest nil-initial-state-and-callback-errors
  (let [previous (session/capture)
        uninitialized (assoc (empty-session) :env nil :instance-index nil)
        failure (ex-info "body failed" {:intentional true})]
    (session/activate! uninitialized)
    (is (nil? @state/ansatz-env))
    (is (nil? @state/ansatz-instance-index))
    (is (identical? failure
                    (try
                      (session/with-session (empty-session)
                        (fn []
                          (reset! state/ansatz-store {:store-path "changed"})
                          (reset! recall/store-path "changed")
                          (simp/restore-caches! {:env @state/ansatz-env :entries {:changed true}})
                          (throw failure)))
                      (catch Throwable error error))))
    (is (= (values uninitialized) (values (session/capture))))
    (session/activate! previous)))

(deftest validation-and-installation-failure-preserve-prior-state
  (let [previous (session/capture)
        candidate (assoc (empty-session) :store {:store-path "new"} :recall-store-path "new")]
    (testing "all cache validation precedes the first global change"
      (doseq [invalid [(assoc candidate :instance-caches [])
                       (assoc candidate :simp-index-caches {:path :new :rules []})
                       (assoc candidate :simp-caches {:env nil :entries []})
                       (assoc candidate :synth-cache (atom []))
                       (dissoc candidate :recall-store-path)]]
        (is (thrown? clojure.lang.ExceptionInfo (session/activate! invalid)))
        (is (= (values previous) (values (session/capture))))))
    (testing "a late installation exception restores already-installed globals"
      (let [restore simp/restore-caches!
            once (atom true)
            failure (ex-info "injected restore failure" {})]
        (with-redefs [simp/restore-caches!
                      (fn [snapshot]
                        (if (compare-and-set! once true false)
                          (throw failure)
                          (restore snapshot)))]
          (is (identical? failure
                          (try (session/activate! candidate) (catch Throwable error error)))))
        (is (= (values previous) (values (session/capture))))))))

(deftest scoped-installation-failure-does-not-enter-body
  (let [previous (session/capture)
        restore instance/restore-caches!
        once (atom true)
        entered (atom false)]
    (with-redefs [instance/restore-caches!
                  (fn [snapshot]
                    (if (compare-and-set! once true false)
                      (throw (ex-info "injected install failure" {}))
                      (restore snapshot)))]
      (is (thrown? clojure.lang.ExceptionInfo
                   (session/with-session (empty-session) #(reset! entered true)))))
    (is (false? @entered))
    (is (= (values previous) (values (session/capture))))))

(deftest persistent-same-throwable-does-not-mask-installation-failure
  (doseq [operation [:activate :scoped]]
    (let [previous (session/capture)
          candidate (empty-session)
          failure (ex-info "persistent installation and restoration failure" {:operation operation})
          attempts (atom 0)
          entered? (atom false)
          observed (with-redefs [simp/restore-caches!
                                 (fn [_] (swap! attempts inc) (throw failure))]
                     (try
                       (if (= :activate operation)
                         (session/activate! candidate)
                         (session/with-session candidate #(reset! entered? true)))
                       nil
                       (catch Throwable error error)))]
      (is (identical? failure observed) (name operation))
      (is (= 2 @attempts))
      (is (empty? (.getSuppressed ^Throwable failure)))
      (is (false? @entered?))
      ;; The injected last hook throws before writing its cache on both attempts;
      ;; the earlier slots/cache writes are restored by the second attempt.
      (is (= (values previous) (values (session/capture)))))))

(deftest distinct-restoration-failure-is-suppressed-on-original-installation-error
  (doseq [operation [:activate :scoped]]
    (let [previous (session/capture)
          candidate (empty-session)
          failure (ex-info "original installation failure" {:operation operation})
          restoration (ex-info "distinct restoration failure" {:operation operation})
          attempts (atom 0)
          observed (with-redefs [simp/restore-caches!
                                 (fn [_]
                                   (throw (if (= 1 (swap! attempts inc)) failure restoration)))]
                     (try
                       (if (= :activate operation)
                         (session/activate! candidate)
                         (session/with-session candidate #(throw (AssertionError. "must not enter body"))))
                       nil
                       (catch Throwable error error)))]
      (is (identical? failure observed) (name operation))
      (is (= 2 @attempts))
      (is (= 1 (count (.getSuppressed ^Throwable failure))))
      (is (identical? restoration (first (.getSuppressed ^Throwable failure))))
      (is (= (values previous) (values (session/capture)))))))

(deftest callback-error-survives-the-same-restoration-throwable
  (let [previous (session/capture)
        candidate (empty-session)
        failure (ex-info "body and restoration failure" {})
        restore simp/restore-caches!
        attempts (atom 0)
        observed (with-redefs [simp/restore-caches!
                               (fn [snapshot]
                                 (if (= 1 (swap! attempts inc))
                                   (restore snapshot)
                                   (throw failure)))]
                   (try
                     (session/with-session candidate #(throw failure))
                     nil
                     (catch Throwable error error)))]
    (is (identical? failure observed))
    (is (= 2 @attempts))
    (is (empty? (.getSuppressed ^Throwable failure)))
    ;; Restoration itself failed; explicitly reinstall after removing the hook.
    (session/activate! previous)))

(deftest serialized-session-operations-hold-lock-through-body
  (let [snapshot (empty-session)
        entered (promise) release (promise) attempted (promise) second-entered (promise)
        first-call (future (session/with-session snapshot
                             (fn [] (deliver entered true) @release :first)))]
    (try
      (is (= true (deref entered 5000 ::timeout)))
      (let [second-call (future
                          (deliver attempted true)
                          (session/with-session snapshot
                            (fn [] (deliver second-entered true) :second)))]
        (try
          (is (= true (deref attempted 5000 ::timeout)))
          (is (= ::timeout (deref second-entered 50 ::timeout)))
          (deliver release true)
          (is (= :first (:value (deref first-call 5000 {}))))
          (is (= :second (:value (deref second-call 5000 {}))))
          (finally (future-cancel second-call))))
      (finally (deliver release true) (future-cancel first-call)))))

(deftest setup-prepares-extensions-and-clears-all-session-caches
  (let [base (Env.)
        descriptor {:store-map {:fixture :borrowed} :store-path "prepared-store" :branch "library"}
        index {:class [:instance]}
        matcher-info {"fixture.matcher" {:num-params 0}}
        derived {:attrs [["simp" "fixture.lemma" nil nil]] :matchers matcher-info
                 :instances index :simp-trie true}]
    (instance/restore-caches! {:old :candidate})
    (simp-index/restore-caches! {:path "prepared-store" :rules {"old" [:rule]}})
    (simp/restore-caches! {:env base :entries {:old :info}})
    (reset! @(ns-resolve 'ansatz.core 'synth-cache) {:old :synth})
    (reset! state/ansatz-discr-trie {:old :recall})
    (reset! state/ansatz-simp-trie {:old :simp})
    (binding [core/*verbose* false]
      (#'core/setup-env! base descriptor nil derived))
    (let [installed (session/capture)]
      (is (= descriptor (:store installed)))
      (is (= "prepared-store" (:recall-store-path installed)))
      (is (= index (:instance-index installed)))
      (is (= index (env/get-extension (:env installed) :instances nil)))
      (is (= #{"fixture.lemma"} (env/get-extension (:env installed) :simp-lemmas nil)))
      (is (= matcher-info (env/get-extension (:env installed) :matcher-info nil)))
      (is (= (select-keys descriptor [:store-path :branch]) (simp-index/index-source (:env installed))))
      (is (nil? (env/get-extension base :instances nil)))
      (is (= {} @(:synth-cache installed)))
      (is (= {} (:instance-caches installed)))
      (is (nil? (:simp-index-caches installed)))
      (is (= {:env nil :entries {}} (:simp-caches installed)))
      (is (nil? (:discr-trie installed)))
      (is (nil? (:simp-trie installed))))))

(deftest setup-preparation-and-activation-failures-preserve-complete-session
  (let [previous (session/capture)
        descriptor {:store-path "not-activated" :branch "fixture"}
        derived {:attrs [["simp" "fixture.lemma" nil nil]] :instances {}}
        failure (ex-info "injected setup failure" {})]
    (testing "failure after pure attribute preparation does not publish partial Env"
      (with-redefs [matchers/install (fn [& _] (throw failure))]
        (is (identical? failure
                        (try (#'core/setup-env! (Env.) descriptor nil derived)
                             (catch Throwable error error)))))
      (is (= (values previous) (values (session/capture)))))
    (testing "late cache installation failure rolls back every session field"
      (let [restore simp/restore-caches!
            once (atom true)]
        (with-redefs [simp/restore-caches!
                      (fn [snapshot]
                        (if (compare-and-set! once true false)
                          (throw failure)
                          (restore snapshot)))]
          (is (identical? failure
                          (try (#'core/setup-env! (Env.) descriptor nil derived)
                               (catch Throwable error error))))))
      (is (= (values previous) (values (session/capture)))))))
