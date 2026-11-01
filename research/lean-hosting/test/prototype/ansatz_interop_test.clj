(ns prototype.ansatz-interop-test
  (:require [clojure.test :refer [deftest is]]
            [ansatz.core :as a]
            [ansatz.state :as state]
            [ansatz.surface.ingest :as ingest]
            [ansatz.export.replay :as replay]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as level]
            [prototype.interop :as interop]
            [prototype.interop-test :as fixtures]
            [prototype.import-ir :as ir]))

(defn linked-lean-identity [_] (throw (ex-info "Only bound during isolated context test" {})))

(deftest checked-ansatz-and-lean-call-in-both-directions
  (let [checked (replay/replay-file-streaming "fixtures/interop-kernel.ndjson")
        session (assoc (fixtures/session :jvm) :kernel-env (:env checked) :kernel-status :checked)
        local-env (atom (:env checked))
        local-instances (atom {})
        local-arities (atom (assoc @ingest/arity-registry "InteropProbe.identity"
                                  {:arity 1 :erased 0 :sym 'prototype.ansatz-interop-test/linked-lean-identity}))]
    (is (zero? (get-in checked [:stats :errors])))
    ;; Temporary registry/context bindings exercise the existing integration seam;
    ;; this is not a production concurrent-session API and changes no global atom.
    (with-redefs [a/ansatz-env local-env state/ansatz-env local-env
                  a/ansatz-instance-index local-instances state/ansatz-instance-index local-instances
                  a/arity-registry local-arities ingest/arity-registry local-arities
                  linked-lean-identity (interop/function session "InteropProbe.identity")]
      (let [host-identity (a/define-verified 'ansatzInteropIdentity '[x :- Nat] 'Nat 'x)
            calls-lean (a/define-verified 'ansatzCallsLean '[x :- Nat] 'Nat '(InteropProbe.identity x))
            bindings (assoc-in fixtures/bindings ["ansatz_host_transform" :fn] (fn [_ x] (host-identity x)))
            session (interop/open-session @fixtures/catalogue (keys (:declarations @fixtures/catalogue)) bindings)]
        (is (= :def (env/ci-tag (env/lookup @local-env (name/from-string "ansatzCallsLean")))))
        (is (= :def (env/ci-tag (env/lookup @local-env (name/from-string "ansatzInteropIdentity")))))
        (is (= 42 (calls-lean 42)))
        (is (= 42 ((interop/function session "InteropProbe.callHost") 42)))))))

(deftest native-macro-output-is-kernel-checked-and-runs-on-jvm
  (let [checked (replay/replay-file-streaming "fixtures/frontend-kernel.ndjson")
        catalogue (ir/index-bundles ["fixtures/frontend.jsonl"])
        session (interop/open-session catalogue (keys (:declarations catalogue)) fixtures/bindings)]
    (is (zero? (get-in checked [:stats :errors])))
    (is (= 43 ((interop/function session "FrontendProbe.answer") 42)))
    ;; A new declaration with a bad body is refused by the same strict kernel.
    (is (thrown? Exception
                 (env/check-constant (:env checked)
                   (env/mk-def (name/from-string "badFrontendResult") []
                     (e/const' (name/from-string "Nat") []) (e/sort' level/zero)))))))
