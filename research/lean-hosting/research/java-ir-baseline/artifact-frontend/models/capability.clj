(ns java-matched-prelude-capability-models-v4
  "Negative issuance models; no guest execution or fabricated positive authority."
  (:require [clojure.test :refer [deftest is run-tests]] [clojure.java.io :as io]
            [java-matched-prelude-module-v4 :as module] [java-matched-artifact-base-v1 :as base]
            [java-ir-baseline :as j] [prototype.guarded-kernel-view :as view]))
(deftest caller-graphs-maps-and-public-empty-constructors-cannot-issue-module-lease
  (doseq [forgery [{:graph :fake :audit-pin module/audit-pin}
                   (java_matched_prelude_module_v4.Prepared.) (Object.)]]
    (is (thrown-with-msg? Exception #"Actual fixed Prepared" (module/install! forgery {}))))
  (doseq [forgery [(java_matched_prelude_module_v4.ModuleLease.) {:aggregate :fake :audit-pin module/audit-pin}]]
    (is (thrown-with-msg? Exception #"Actual installed ModuleLease" (module/inspect! forgery)))))
(deftest changed-or-unrecognized-audit-stops-before-any-graph-preparation
  (let [root (doto (io/file "target/module-capability-models") .mkdirs)
        dir (.toFile (java.nio.file.Files/createTempDirectory (.toPath root) "wrong-audit-" (make-array java.nio.file.attribute.FileAttribute 0)))
        file (io/file dir "pair-audit.json") calls (atom 0)]
    (try
      (spit file "{\"schema\":\"matched-prelude-pair-audit/1\",\"checkingShapesEqual\":true}")
      (with-redefs [j/prepare-host-program (fn [& _] (swap! calls inc))]
        (is (thrown-with-msg? Exception #"digest mismatch" (module/prepare! nil dir)))
        (is (zero? @calls)))
      (finally (.delete file) (.delete dir)))))
(deftest forged-aggregate-or-base-token-cannot-open-a-java-checking-view
  (let [opened (atom 0)]
    (with-redefs [view/open-view! (fn [& _] (swap! opened inc))]
      (is (thrown-with-msg? Exception #"Actual installed ModuleLease"
            (base/open-base! {:aggregate :fake :audit-pin module/audit-pin} {:environment :fake}
                             {:lease! (fn []) :write-format 2} {})))
      (is (zero? @opened)))
    (doseq [forgery [(java_matched_artifact_base_v1.Base.) {:basis :trusted-artifact :domain-count 2314}]]
      (is (thrown-with-msg? Exception #"Actual issued matched Base" (base/guard! forgery)))
      (is (thrown-with-msg? Exception #"Actual issued matched Base" (base/with-env! forgery identity))))))
(defn check! [] (run-tests 'java-matched-prelude-capability-models-v4))
