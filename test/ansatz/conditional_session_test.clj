(ns ansatz.conditional-session-test
  (:require [clojure.test :refer [deftest is use-fixtures]]
            [ansatz.session :as session]
            [ansatz.state :as state]
            [ansatz.recall :as recall]
            [ansatz.tactic.instance :as instance]
            [ansatz.simp-index :as simp-index]
            [ansatz.tactic.simp :as simp])
  (:import [ansatz.kernel Env]))

(defn- target []
  (let [e (Env.) marker (Object.) path (str "conditional-" (gensym))]
    (assoc (session/capture) :env e :instance-index {:new [marker]}
           :discr-trie {:new marker} :simp-trie {:new marker}
           :store {:store-path path} :recall-store-path path
           :synth-cache (atom {:new marker}) :instance-caches {:new marker}
           :simp-index-caches {:path path :rules {"new" [marker]}}
           :simp-caches {:env e :entries {:new marker}})))
(defn- leaves [snapshot] (#'session/leaves snapshot))
(defn- same-state? [snapshot]
  (empty? (#'session/changed-leaves (leaves snapshot) (leaves (session/capture)))))
(defn- synth-cell [] @(requiring-resolve 'ansatz.core/synth-cache))
(defn- cells []
  [[:env state/ansatz-env] [:instance-index state/ansatz-instance-index]
   [:discr-trie state/ansatz-discr-trie] [:simp-trie state/ansatz-simp-trie]
   [:store state/ansatz-store] [:recall-store-path recall/store-path]
   [:synth-cache (synth-cell)]])

(use-fixtures :each
  (fn [f]
    (let [before (session/capture)]
      (try (session/activate! (target)) (f)
           (finally (session/activate! before))))))

(deftest complete-activation-uses-one-cas-and-exact-prepared-leaves
  (let [before (session/capture) prepared (target) attempts (atom 0)
        cas @#'session/env-cas!
        result (with-redefs-fn {#'session/env-cas! (fn [& args] (swap! attempts inc) (apply cas args))}
                 #(session/activate-if-unchanged! before prepared))]
    (is (= :activated (:status result)))
    (is (= 1 @attempts))
    (is (same-state? prepared))))

(deftest every-captured-slot-and-cache-leaf-drift-refuses-before-publication
  (let [mutations (concat
                   (map (fn [[key cell]] [key #(reset! cell (get (leaves (target)) key))]) (cells))
                   [[:instance-caches #(instance/restore-caches! {:foreign :instance})]
                    [:simp-index-caches #(simp-index/restore-caches! {:path "foreign" :rules {}})]
                    [:simp-cache-env #(simp/restore-caches! (assoc (simp/capture-caches) :env (Env.)))]
                    [:simp-cache-entries #(simp/restore-caches! (assoc (simp/capture-caches) :entries {:foreign :entry}))]])]
    (doseq [[key mutate] mutations]
      (let [before (session/capture) prepared (target)]
        (mutate)
        (let [actual (session/capture)
              result (session/activate-if-unchanged! before prepared)]
          (is (= :rejected (:status result)) (str key))
          (is (some #{key} (:changed result)) (str key))
          (is (same-state? actual)))
        (session/activate! before)))))

(deftest stale-cas-does-not-publish-other-slots-or-retry
  (let [before (session/capture) attempts (atom 0)
        result (with-redefs-fn {#'session/env-cas! (fn [& _] (swap! attempts inc) false)}
                 #(session/activate-if-unchanged! before (target)))]
    (is (= :stale-env-cas (:stage result)))
    (is (= 1 @attempts))
    (is (same-state? before))))

(deftest atom-validator-and-watch-failures-before-and-after-each-slot-write
  (doseq [[key cell] (cells) mode [:validator :watch]]
    (let [before (session/capture) prepared (target) desired (get (leaves prepared) key)
          original-validator (get-validator cell) failure (ex-info "slot failure" {:key key :mode mode})
          once (atom true)
          reject (fn [value]
                   (when (and (identical? desired value) (compare-and-set! once true false)) (throw failure))
                   true)]
      (try
        (if (= mode :validator)
          (set-validator! cell reject)
          (add-watch cell ::slot-failure (fn [_ _ _ value] (reject value))))
        (let [result (session/activate-if-unchanged! before prepared)]
          (is (= :failed (:status result)) (str key mode))
          (is (identical? failure (:cause result)))
          (is (= :restored (get-in result [:restoration :status])))
          (is (same-state? before)))
        (finally (remove-watch cell ::slot-failure) (set-validator! cell original-validator))))))

(deftest cache-hooks-failing-before-or-after-write-restore-the-complete-context
  (doseq [[key variable] [[:instance-caches #'instance/restore-caches!]
                          [:simp-index-caches #'simp-index/restore-caches!]
                          [:simp-caches #'simp/restore-caches!]]
          mode [:before :after]]
    (let [before (session/capture) prepared (target) restore @variable once (atom true)
          failure (ex-info "cache failure" {:key key :mode mode})
          result (with-redefs-fn
                   {variable (fn [snapshot]
                               (if (compare-and-set! once true false)
                                 (do (when (= mode :after) (restore snapshot)) (throw failure))
                                 (restore snapshot)))}
                   #(session/activate-if-unchanged! before prepared))]
      (is (identical? failure (:cause result)))
      (is (= :restored (get-in result [:restoration :status])) (str key mode))
      (is (same-state? before)))))

(deftest persistent-watch-errors-preserve-cause-and-verify-restored-state
  (let [before (session/capture) prepared (target) failure (ex-info "persistent watch" {})
        observed-writes (atom [])]
    (try
      (add-watch state/ansatz-env ::persistent
                 (fn [_ _ _ value] (swap! observed-writes conj value) (throw failure)))
      (let [result (session/activate-if-unchanged! before prepared)]
        (is (identical? failure (:cause result)))
        (is (= :restored (get-in result [:restoration :status])))
        (is (some #(identical? failure %) (get-in result [:restoration :errors])))
        (is (empty? (.getSuppressed failure)))
        (is (= 2 (count @observed-writes)))
        (is (identical? (:env prepared) (first @observed-writes)))
        (is (identical? (:env before) (second @observed-writes)))
        (is (same-state? before)))
      (finally (remove-watch state/ansatz-env ::persistent)))))

(deftest restoration-failure-reports-actual-partial-state-and-original-cause
  (let [before (session/capture) prepared (target)
        original (ex-info "late installation" {}) restoration (ex-info "restore instance" {})
        restore-instance instance/restore-caches! instance-attempts (atom 0)
        result (with-redefs [instance/restore-caches!
                             (fn [snapshot]
                               (if (= 2 (swap! instance-attempts inc)) (throw restoration) (restore-instance snapshot)))
                             simp/restore-caches! (fn [_] (throw original))]
                 (session/activate-if-unchanged! before prepared))]
    (is (identical? original (:cause result)))
    (is (= :failed (get-in result [:restoration :status])))
    (is (some #{:instance-caches} (get-in result [:restoration :changed])))
    (is (some #(identical? restoration %) (.getSuppressed original)))
    (is (identical? (:env before) @state/ansatz-env))
    (session/activate! before)))

(deftest silent-env-watch-cannot-produce-false-success-or-overwrite-a-foreign-session
  (let [before (session/capture) prepared (target) foreign (target)]
    (try
      (add-watch state/ansatz-env ::foreign
                 (fn [_ _ _ value]
                   (when (identical? value (:env prepared))
                     (reset! state/ansatz-env (:env foreign))
                     (reset! state/ansatz-store (:store foreign)))))
      (let [result (session/activate-if-unchanged! before prepared)]
        (is (= :failed (:status result)))
        (is (= :conflicted (get-in result [:restoration :status])))
        (is (identical? (:env foreign) @state/ansatz-env))
        (is (identical? (:store foreign) @state/ansatz-store))
        (is (identical? (:instance-index before) @state/ansatz-instance-index)))
      (finally (remove-watch state/ansatz-env ::foreign)))))

(deftest throwing-watch-with-foreign-env-refuses-all-restoration-writes
  (let [before (session/capture) prepared (target) foreign (Env.) failure (ex-info "foreign env" {})]
    (try
      (add-watch state/ansatz-env ::foreign-throw
                 (fn [_ _ _ value]
                   (when (identical? value (:env prepared)) (reset! state/ansatz-env foreign) (throw failure))))
      (let [result (session/activate-if-unchanged! before prepared)]
        (is (identical? failure (:cause result)))
        (is (= :conflicted (get-in result [:restoration :status])))
        (is (identical? foreign @state/ansatz-env))
        (is (identical? (:store before) @state/ansatz-store)))
      (finally (remove-watch state/ansatz-env ::foreign-throw)))))

(deftest silent-late-callback-leaf-write-is-a-conflict
  (let [before (session/capture) prepared (target) restore simp/restore-caches!
        foreign {:foreign :store}
        result (with-redefs [simp/restore-caches! (fn [snapshot] (restore snapshot) (reset! state/ansatz-store foreign))]
                 (session/activate-if-unchanged! before prepared))]
    (is (= :conflicted (get-in result [:restoration :status])))
    (is (identical? foreign @state/ansatz-store))
    (is (identical? (:env prepared) @state/ansatz-env))))

(deftest nested-installation-is-refused-before-nested-publication
  (let [before (session/capture) prepared (target) nested (target) nested-result (atom nil)]
    (try
      (add-watch state/ansatz-env ::nested
                 (fn [_ _ _ value]
                   (when (identical? value (:env prepared))
                     (reset! nested-result (session/activate-if-unchanged! (session/capture) nested)))))
      (is (= :activated (:status (session/activate-if-unchanged! before prepared))))
      (is (= :nested-installation (:stage @nested-result)))
      (finally (remove-watch state/ansatz-env ::nested))))
  (let [before (session/capture) prepared (target)]
    (try
      (add-watch state/ansatz-env ::nested-legacy
                 (fn [_ _ _ value]
                   (when (identical? value (:env prepared)) (session/activate! (target)))))
      (let [result (session/activate-if-unchanged! before prepared)]
        (is (= :failed (:status result)))
        (is (= :ansatz.session/nested-installation (:type (ex-data (:cause result)))))
        (is (same-state? before)))
      (finally (remove-watch state/ansatz-env ::nested-legacy)))))

(deftest real-two-atom-simp-hook-failure-is-verified-by-actual-leaves
  (let [before (session/capture) prepared (target)
        entries-cell @(ns-resolve 'ansatz.tactic.simp 'fun-info-cache)
        original-validator (get-validator entries-cell)
        original (ex-info "late simp hook failure" {})
        restoration (ex-info "reject old simp entries" {})
        restore simp/restore-caches! attempts (atom 0)]
    (try
      (set-validator! entries-cell
                      (fn [entries]
                        (when (and (pos? @attempts)
                                   (identical? entries (get-in before [:simp-caches :entries])))
                          (throw restoration))
                        true))
      (let [result (with-redefs [simp/restore-caches!
                                 (fn [snapshot]
                                   (if (= 1 (swap! attempts inc))
                                     (do (restore snapshot) (throw original))
                                     (restore snapshot)))]
                     (session/activate-if-unchanged! before prepared))]
        (is (identical? original (:cause result)))
        (is (= :failed (get-in result [:restoration :status])))
        (is (= #{:simp-cache-env :simp-cache-entries} (set (get-in result [:restoration :changed]))))
        (is (some #(identical? restoration %) (get-in result [:restoration :errors])))
        (is (identical? (:env before) @state/ansatz-env)))
      (finally (set-validator! entries-cell original-validator) (session/activate! before)))))

(deftest same-env-cas-watch-error-is-an-installation-failure-even-without-identity-change
  (let [before (session/capture) prepared (assoc (target) :env (:env before))
        failure (ex-info "same identity watch" {}) attempts (atom 0)]
    (try
      (add-watch state/ansatz-env ::same-env
                 (fn [& _] (swap! attempts inc) (throw failure)))
      (let [result (session/activate-if-unchanged! before prepared)]
        (is (= :failed (:status result)))
        (is (identical? failure (:cause result)))
        (is (= :restored (get-in result [:restoration :status])))
        (is (= 1 @attempts))
        (is (same-state? before)))
      (finally (remove-watch state/ansatz-env ::same-env)))))
