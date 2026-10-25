(require '[clojure.test :as t] '[clojure.data.json :as json])
;; Bounded failure reports never print Worlds, function registries or packets.
(defn report-error [cause]
  (loop [cause cause n 8]
    (when (and cause (pos? n))
      (let [message (or (.getMessage ^Throwable cause) "")]
        (println (.getName (class cause)) (subs message 0 (min 512 (count message)))))
      (recur (.getCause ^Throwable cause) (dec n)))))
(defmethod t/report :error [event]
  (t/inc-report-counter :error) (report-error (:actual event)))
(defmethod t/report :fail [event]
  (t/inc-report-counter :fail)
  (println "ASSERTION_FAILURE" (:file event) (:line event)))
(def seen (atom #{}))
(defmethod t/report :begin-test-var [event] (swap! seen conj (:var event)))
(try
  (require 'prototype.cases-on-preparation-test 'prototype.runtime-abi-test
           'prototype.raw-interop-test 'prototype.program-install-test
           'prototype.kernel-cases-on-raw-test)
  (let [nss ['prototype.cases-on-preparation-test 'prototype.runtime-abi-test
             'prototype.raw-interop-test 'prototype.program-install-test
             'prototype.kernel-cases-on-raw-test]
        expected (set (for [ns nss [_ var] (ns-publics ns) :when (:test (meta var))] var))
        result (apply t/run-tests nss)
        observations @(var-get (ns-resolve 'prototype.kernel-cases-on-raw-test 'observations))
        calls (filter #(contains? #{:raw-annotated-constructor :raw-ordinary-constructor} (:kind %)) observations)
        complete (filter #(= :backend-complete (:kind %)) observations)]
    (when-let [path (System/getProperty "ansatz.raw-cases-on.results")]
      (spit path (json/write-str {:result result :observations observations
                                 :scope "Portable14constructioncomponent+preseal/policy regressions; no kerneladmission/fullfrontend claim."})))
    (assert (= 48 (count expected) (:test result)))
    (assert (= expected @seen))
    (assert (= (set (for [b [:reference :mutable :jvm] d [:annotated :ordinary]] [b d]))
               (set (map (juxt :backend :dataset) complete))))
    (assert (zero? (+ (:fail result) (:error result))))
    (doseq [backend [:reference :mutable :jvm]]
      (assert (= 14 (count (set (map :suffix (filter #(= backend (:backend %)) calls)))))))
    (println "RAW_CASES_ON_PORTABLE_FOURTEEN_PASS")
    (System/exit 0))
  (catch Throwable cause (report-error cause) (System/exit 2)))
