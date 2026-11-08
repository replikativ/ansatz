(ns ansatz.load-init-test
  (:require [clojure.test :refer [deftest is use-fixtures]]
            [ansatz.core :as a]
            [ansatz.fixtures :as fixtures]
            [ansatz.bundle :as bundle]
            [ansatz.bundle-test :as bundle-test]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.expr :as expr]
            [ansatz.kernel.level :as level]
            [ansatz.export.parser :as parser]
            [ansatz.session :as session]
            [ansatz.state :as state]))

(use-fixtures :once fixtures/isolated-session)
(use-fixtures :each
  (fn [f]
    (session/with-session
      (assoc (session/capture) :env (env/empty-env) :instance-index {} :store nil
             :recall-store-path nil :synth-cache (atom {}))
      #(binding [a/*verbose* false] (f)))))

(defn- snapshot [] (update (into {} (session/capture)) :synth-cache deref))

(deftest repeated-bundle-keeps-models-and-session-state
  (a/load-init!)
  (a/theorem retainedModelA [] True (exact True.intro))
  ;; Exercise preservation of extensions and independent session globals/caches.
  (swap! state/ansatz-env env/with-extension :simp-lemmas #{"retainedModelA"})
  (swap! state/ansatz-env env/with-extension :instances {:local [:instance]})
  (swap! state/ansatz-env env/with-extension :matcher-info {"local" :matcher})
  (swap! state/ansatz-env env/with-extension :eqns {"local" [:equation]})
  (swap! @(ns-resolve 'ansatz.core 'synth-cache) assoc :local :cached)
  (let [current (session/capture)]
    (session/activate!
     (assoc current :store {:store-path "borrowed" :branch "init" :store-map {}}
            :recall-store-path "borrowed" :instance-caches {:local :cached}
            :simp-caches {:env (:env current) :entries {:local :cached}})))
  (let [before (snapshot)]
    (is (identical? (:env before) (a/load-init!)))
    (is (= before (snapshot)))
    (is (= :medium (a/init!)))
    (is (= before (snapshot))))
  (a/theorem retainedModelB [] True (exact retainedModelA))
  (a/load-init!)
  ;; This proof requires both retained declarations and passes check-constant.
  (a/theorem retainedModels [] (And True True)
             (exact (And.intro retainedModelA retainedModelB)))
  (is (some? (env/lookup (a/env) (name/from-string "retainedModels")))))

(deftest explicit-verification-rechecks-trusted-base-without-replacing-session
  (a/load-init!)
  (a/theorem retainedTrustedModel [] True (exact True.intro))
  (let [before (snapshot)
        replay-var (ns-resolve 'ansatz.core 'bundled-medium-env)
        replay @replay-var
        modes (atom [])]
    (with-redefs-fn {replay-var (fn [verify?] (swap! modes conj verify?) (replay verify?))}
      #(is (identical? (:env before) (a/load-init! :verify? true))))
    (is (= [true] @modes))
    (is (= before (snapshot)))
    (is (= :trust (get-in (env/get-extension (a/env) :artifact-profile)
                          [:base :kernel-admission])))))

(deftest failed-isolated-recheck-keeps-the-complete-session
  (a/load-init!)
  (a/theorem retainedAfterFailedCheck [] True (exact True.intro))
  (let [before (snapshot)
        type-expr (expr/sort' (level/succ level/zero))
        invalid (env/mk-def (name/from-string "invalidCheckedBundle") [] type-expr type-expr)]
    (with-redefs [parser/parse-ndjson-string
                  (fn [_] (assoc (parser/mk-parser-state) :decls [invalid]))]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Replay stopped on error"
                            (a/load-init! :verify? true))))
    (is (= before (snapshot)))
    (is (identical? (:env before) (a/env)))))

(deftest additions-during-isolated-recheck-are-retained
  (a/load-init!)
  (let [replay-var (ns-resolve 'ansatz.core 'bundled-medium-env)
        replay @replay-var]
    (with-redefs-fn
      {replay-var (fn [verify?]
                    (let [checked (replay verify?)]
                      (a/theorem addedDuringRecheck [] True (exact True.intro))
                      checked))}
      #(is (identical? (a/load-init! :verify? true) (a/env)))))
  (is (some? (env/lookup (a/env) (name/from-string "addedDuringRecheck")))))

(deftest different-bundle-replaces-session
  (a/load-init!)
  (a/theorem oldBundleModel [] True (exact True.intro))
  (let [{:keys [manifest resources]} (bundle-test/generated-fixture)]
    (bundle/with-verified {:manifest manifest :read-resource resources}
      (fn [_]
        (a/load-init!)
        (is (= manifest (env/get-extension (a/env) :bundled-artifacts)))
        (is (nil? (env/lookup (a/env) (name/from-string "oldBundleModel")))))))
  (a/load-init!)
  (is (some? (env/lookup (a/env) (name/from-string "True")))))

(deftest unmarked-and-store-bases-do-not-count-as-bundled-activation
  (a/load-init!)
  (a/theorem oldSessionModel [] True (exact True.intro))
  ;; Same constants/size are insufficient without the retained manifest identity.
  (swap! state/ansatz-env env/with-extension :bundled-artifacts nil)
  (a/load-init!)
  (is (nil? (env/lookup (a/env) (name/from-string "oldSessionModel"))))
  (let [store-base (env/with-extension (env/empty-env) :artifact-profile
                     {:base {:kind :prepared-store}})
        descriptor {:store-map {:fixture :borrowed} :store-path "fixture" :branch "init"}]
    ((ns-resolve 'ansatz.core 'setup-env!) store-base descriptor nil
                                           {:attrs [] :instances {} :matchers {}})
    (is (identical? descriptor @state/ansatz-store))
    (a/load-init!)
    (is (nil? @state/ansatz-store))
    (is (some? (env/lookup (a/env) (name/from-string "True"))))))
