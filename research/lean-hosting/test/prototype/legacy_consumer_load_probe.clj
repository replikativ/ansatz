(ns prototype.legacy-consumer-load-probe
  "Fresh-process standalone regression. Run only in a deliberately materialized
   legacy classpath WITHOUT coherent_consumer_profile.clj or its AOT output.
   Source-only until scheduled by the sole execution lane. No restore/guest work."
  (:require [clojure.java.io :as io]))

(defn -main [& [expected-source-root]]
  (assert (nil? (find-ns 'prototype.coherent-consumer-profile)))
  (doseq [id ["prototype/coherent_consumer_profile.clj"
              "prototype/coherent_consumer_profile__init.class"]]
    (assert (nil? (io/resource id)) (str "Probe classpath must exclude " id)))
  (when expected-source-root
    (doseq [id ["prototype/globals_consumer_factory.clj" "prototype/restore_consumer.clj"]]
      (assert (= (str (.toURL (.toURI (io/file expected-source-root id)))) (str (io/resource id))))))
  (require 'prototype.globals-consumer-factory 'prototype.restore-consumer)
  (assert (nil? (find-ns 'prototype.coherent-consumer-profile)))
  (let [construct (resolve 'prototype.globals-consumer-factory/make-factory)
        rejected? (try (construct {}) false (catch clojure.lang.ExceptionInfo _ true))]
    (assert rejected? "Legacy constructor must retain its exact option/admission checks"))
  (assert (nil? (find-ns 'prototype.coherent-consumer-profile)))
  (println "legacy consumer namespace load without coherent source: PASS"))
