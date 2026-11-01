(require '[ansatz.lean] '[clojure.java.io :as io] '[prototype.raw-interop :as raw])
(load-file "compiler-fixture.clj")
(require '[consumer.compiler-fixture :as fixture] '[prototype.machine :as m])
;; Pattern is an ordinary dependency of ansatz-lean, while compiler namespaces
;; still load only after the user selects represented compilation.
(assert (some? (io/resource "pattern.clj")))
(assert (nil? (find-ns 'pattern.nanopass.dialect)))
(assert (nil? (find-ns 'prototype.typed-tail-execution)))
(let [{:keys [functions options targets]} (fixture/input) world (m/world functions)]
  (doseq [backend [:reference :mutable :jvm]]
    (let [session (raw/open-functions functions {}
                                     (cond-> {:backend backend}
                                       (not= :jvm backend) (assoc :compiler-options options)))]
      (assert (= 55N (:value (raw/call session world (get targets "sum64") [10 0]))))))
  (assert (nil? (find-ns 'pattern.nanopass.dialect)))
  (assert (nil? (find-ns 'prototype.typed-tail-execution)))
  (assert (= world (m/world functions))))
(println :optional-compiler-lazy-loading-passed)
