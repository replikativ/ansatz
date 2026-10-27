(ns ansatz.bundle-activation-test
  (:require [clojure.test :refer [deftest is]]
            [ansatz.bundle :as bundle]
            [ansatz.bundle-test :as bundle-test]
            [ansatz.attrs :as attrs]
            [ansatz.session :as session]
            [ansatz.wf :as wf]
            [ansatz.core :as a]
            [ansatz.state :as state]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.expr :as expr]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as level]
            [ansatz.export.parser :as parser]))

(deftest invalid-bundle-fails-before-proof-state-activation
  (let [atoms [state/ansatz-env state/ansatz-instance-index state/ansatz-store
               state/ansatz-discr-trie state/ansatz-simp-trie]
        before (mapv deref atoms)]
    (with-redefs [bundle/classpath-bytes (fn [& _] (throw (ex-info "invalid cohort" {})))]
      (doseq [load [#(a/init!) #(a/load-init!)]]
        (is (thrown-with-msg? clojure.lang.ExceptionInfo #"invalid cohort" (load)))
        (is (= before (mapv deref atoms)))))))

(deftest bundled-environment-retains-honest-artifact-provenance
  (binding [a/*verbose* false]
    (a/init!)
    (let [manifest (env/get-extension (a/env) :bundled-artifacts nil)]
      (is (= :generated (:bundle/status manifest)))
      (is (= :recorded (:bundle/co-generation manifest)))
      (is (= "4.33.1" (get-in manifest [:producer :lean :version])))
      (is (= 6 (count (:resources manifest)))))))

(deftest unsupported-generated-attributes-fail-before-all-bundled-activation-paths
  (let [candidate (assoc (session/capture) :env (env/empty-env) :instance-index {} :synth-cache (atom {}))]
    (session/with-session candidate
      (fn []
        (let [snapshot #(update (into {} (session/capture)) :synth-cache deref)
              before (snapshot)]
          (doseq [row [{:kind "simp" :name "Fixture.inv" :prio 1000 :post true :inv true}
                       {:kind "simp" :name "Fixture.pre" :prio 1000 :post false :inv false}]]
            (let [{:keys [manifest resources]} (bundle-test/generated-fixture-with-attrs [row])]
              (bundle/with-verified {:manifest manifest :read-resource resources}
                (fn [_]
                  (doseq [activate [#(a/init!) #(a/load-init!)
                                    #((ns-resolve 'ansatz.core 'setup-env!) (env/empty-env))
                                    #(attrs/load-bundled-attrs! {:present? (constantly true)})
                                    #(wf/wf-fix-ensure-lex-prelude!)
                                    #(wf/wf-fix-ensure-sizeof-prelude!)]]
                    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"unsupported consumer semantics" (activate)))
                    (is (= before (snapshot)))))))))))))

(deftest supported-generated-attributes-install-with-decoded-identities-and-priority
  (let [n "Fixture.\"quoted\\λ"
        target "Fixture.\\target\""
        rows [{:kind "simp" :name n :prio 47 :post true :inv false}
              {:kind "csimp" :name "Fixture.f" :target target}]
        {:keys [manifest resources]} (bundle-test/generated-fixture-with-attrs rows)
        candidate (assoc (session/capture) :env (env/empty-env) :instance-index {} :synth-cache (atom {}))]
    (session/with-session candidate
      (fn []
        (bundle/with-verified {:manifest manifest :read-resource resources}
          (fn [_]
            (is (= {:simp-lemmas 1 :csimp 1}
                   (attrs/load-bundled-attrs! {:present? (constantly true)})))
            (is (= #{n} (env/get-extension (a/env) :simp-lemmas #{})))
            (is (= {n 47} (env/get-extension (a/env) :simp-priorities {})))
            (is (= {"Fixture.f" target} (env/get-extension (a/env) :csimp {})))))))))

(deftest bundled-default-recheck-rejects-invalid-definitions-before-activation
  (let [before (session/capture)
        declaration (env/mk-def (name/from-string "invalidBundledDefinition") []
                                (expr/sort' (level/succ level/zero))
                                (expr/sort' (level/succ level/zero)))]
    ;; The type is Type, while the value Type itself has type Type 1.
    ;; TRUST would admit this declaration; the default must reject it.
    (with-redefs [parser/parse-ndjson-string
                  (fn [_] (assoc (parser/mk-parser-state) :decls [declaration]))]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Replay stopped on error"
                            (a/load-init!)))
      (is (identical? (:env before) @state/ansatz-env)))))
