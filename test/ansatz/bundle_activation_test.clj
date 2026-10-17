(ns ansatz.bundle-activation-test
  (:require [clojure.test :refer [deftest is]]
            [ansatz.bundle :as bundle]
            [ansatz.core :as a]
            [ansatz.state :as state]
            [ansatz.kernel.env :as env]))

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
      (is (= :legacy-inventory (:bundle/status manifest)))
      (is (= :unrecorded (:bundle/co-generation manifest)))
      (is (= "4.29.0-rc2" (get-in manifest [:producer :lean :version])))
      (is (= 6 (count (:resources manifest)))))))
