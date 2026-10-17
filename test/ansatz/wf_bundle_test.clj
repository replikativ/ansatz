(ns ansatz.wf-bundle-test
  "Lazy-prelude cohort guards. Parsing is stubbed where noted: these tests cover
   the resource/session boundary, not prelude kernel replay correctness."
  (:require [clojure.test :refer [deftest is]]
            [ansatz.bundle :as bundle]
            [ansatz.core :as a]
            [ansatz.wf :as wf]
            [ansatz.state :as state]
            [ansatz.kernel.env :as env]
            [ansatz.export.parser :as parser])
  (:import [ansatz.kernel Env]))

(defn- with-environment [environment f]
  (locking state/session-lock
    (let [before @state/ansatz-env]
      (try
        (reset! state/ansatz-env environment)
        (binding [a/*verbose* false] (f))
        (finally (reset! state/ansatz-env before))))))

(deftest lazy-preludes-reject-another-bundle-before-parsing-or-mutation
  (let [manifest (bundle/verify!)
        old-manifest (assoc manifest :artifact/cohort "previous-generation")
        base (env/with-extension (Env.) :bundled-artifacts old-manifest)
        parsed? (atom false)]
    (with-environment base
      (fn []
        (with-redefs [parser/parse-ndjson-string (fn [_] (reset! parsed? true) {:decls []})]
          (doseq [load [wf/wf-fix-ensure-lex-prelude! wf/wf-fix-ensure-sizeof-prelude!]]
            (is (thrown-with-msg? clojure.lang.ExceptionInfo #"do not match requirements" (load)))
            (is (identical? base @state/ansatz-env))))
        (is (false? @parsed?))))))

(deftest lazy-preludes-use-the-matching-scoped-snapshot-without-reopening
  (bundle/with-verified
    (fn [manifest]
      (let [base (env/with-extension (Env.) :bundled-artifacts manifest)
            parsed (atom 0)]
        (with-environment base
          (fn []
            (with-redefs [bundle/classpath-bytes (fn [_] (throw (AssertionError. "snapshot must not reopen")))
                          parser/parse-ndjson-string (fn [_] (swap! parsed inc) {:decls []})]
              (wf/wf-fix-ensure-lex-prelude!)
              (wf/wf-fix-ensure-sizeof-prelude!)
              (is (= 2 @parsed))
              (is (identical? base @state/ansatz-env)))))))))

(deftest independently-checked-environments-without-bundle-provenance-still-use-the-prelude-path
  (let [base (Env.)
        parsed? (atom false)]
    (with-environment base
      (fn []
        (with-redefs [parser/parse-ndjson-string (fn [_] (reset! parsed? true) {:decls []})]
          (wf/wf-fix-ensure-lex-prelude!)
          (is @parsed?)
          (is (identical? base @state/ansatz-env)))))))
