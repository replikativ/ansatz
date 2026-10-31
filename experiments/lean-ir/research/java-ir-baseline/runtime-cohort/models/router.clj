(ns allocation-heartbeat-cohort-router-checks-v1
  "Pure routing models; no real engine, source grant or HostRequest claim."
  (:require [clojure.test :refer [deftest is]] [allocation-heartbeat-cohort-v1 :as c]
            [artifact-declaration-driver-v4 :as checked-driver]
            [allocation-heartbeat-lab-v1 :as hb] [java-ir-baseline :as j]))
(deftest explicit-service-shape-and-parent-driver-agreement
  (let [service {:handles? (constantly false) :serve! identity}
        attached (c/attach-runtime-service {:driver {}} service)]
    (is (identical? service (:additional-runtime-service attached)))
    (is (identical? service (get-in attached [:driver :additional-runtime-service])))
    (is (nil? (#'c/extra-service {:driver {}})))
    (doseq [bad [{:handles? true :serve! identity} {:handles? identity} (java.util.HashMap. service)]]
      (is (thrown? clojure.lang.ExceptionInfo (c/attach-runtime-service {:driver {}} bad))))
    (is (thrown? clojure.lang.ExceptionInfo (#'c/extra-service
          {:additional-runtime-service service :driver {:additional-runtime-service (assoc service :serve! (fn [x] x))}})))))
(deftest first-call-runtime-routing-hb-extra-and-unclaimed-unknown
  (let [seen (atom []) request (Object.) service {:handles? #(= "extra" %) :serve! #(swap! seen conj [:extra %])}
        session {:driver {:current-ctx (atom {}) :engine (Object.) :additional-runtime-service service}}]
    (with-redefs [j/host-request (fn [_ _] request) j/phase (fn [_ _] "host-call")
                  hb/handles? #(= "heartbeat" %) hb/serve-current! #(swap! seen conj [:hb %])]
      (doseq [symbol ["heartbeat" "extra"]]
        (with-redefs [j/request-value (fn [_ _] symbol)] (c/runtime-service-step! session)))
      (with-redefs [j/request-value (fn [_ _] "unknown")]
        (is (thrown-with-msg? clojure.lang.ExceptionInfo #"unclaimed" (c/runtime-service-step! session)))))
    (is (= [:hb :extra] (mapv first @seen)))
    (is (every? #(identical? session (second %)) @seen))))
(deftest strict-extra-guard-order-ticks-and-fallback
  (let [events (atom []) e (Object.) ctx (atom {})
        service {:handles? #(do (swap! events conj :handles) (= "extra" %))
                 :serve! (fn [_] (swap! events conj :serve))}
        d {:engine e :source :source :current-ctx ctx :additional-runtime-service service}
        child {:driver d :additional-runtime-service service :lab-heartbeat-provider (Object.)}
        phase (atom :idle) ticks (atom 0)
        admission {:adapter {:phase phase} :ticks ticks
                   :authority {:check-source! (fn [_ _] (swap! events conj :source))}
                   :runtime-step! (fn [_] (swap! events conj :original))}]
    (with-redefs [hb/wrap-step (fn [_ actual] (:runtime-step! actual)) hb/handles? (constantly false)
                  j/phase (fn [_ _] "host-call") j/host-request (fn [_ _] (Object.))
                  j/request-value (fn [_ _] "extra")]
      (let [step (c/wrap-runtime-step child admission)]
        (step {:driver d})
        (is (= [:source :handles :serve] @events))
        (is (= 1 @ticks))
        (reset! events []) (reset! phase :retired)
        (is (thrown? clojure.lang.ExceptionInfo (step {:driver d})))
        (is (empty? @events)) (is (= 1 @ticks))
        (reset! phase :idle)
        (is (thrown? clojure.lang.ExceptionInfo (step {:driver (assoc d :engine (Object.))})))
        (is (empty? @events))
        (with-redefs [j/request-value (fn [_ _] "unknown")]
          (step {:driver d})
          (is (= [:source :handles :original] @events))
          (is (= 1 @ticks)))))))

(deftest checked-externs-cannot-be-shadowed-by-catchall-extra-service
  (let [events (atom []) service {:handles? (fn [_] (swap! events conj :handles) true)
                                  :serve! (fn [_] (swap! events conj :serve))}
        e (Object.) d {:engine e :source :source :current-ctx (atom {}) :additional-runtime-service service}
        child {:driver d :additional-runtime-service service :lab-heartbeat-provider (Object.)}
        admission {:adapter {:phase (atom :idle)} :ticks (atom 0)
                   :authority {:check-source! (fn [_ _] (swap! events conj :source))}
                   :runtime-step! (fn [_] (swap! events conj :checked-driver))}]
    (with-redefs [hb/wrap-step (fn [_ actual] (:runtime-step! actual)) hb/handles? (constantly false)
                  j/phase (fn [_ _] "host-call") j/host-request (fn [_ _] (Object.))]
      (doseq [symbol ["lean_elab_add_decl" "lean_add_decl" "lean_run_mod_init_core"]]
        (reset! events [])
        (with-redefs [j/request-value (fn [_ _] symbol)]
          (is (thrown-with-msg? clojure.lang.ExceptionInfo #"unclaimed" (c/runtime-service-step! {:driver d})))
          (is (empty? @events))
          ((c/wrap-runtime-step child admission) {:driver d})
          (is (= [:source :checked-driver] @events)))))))

(deftest finite-and-general-child-select-constructor-before-activation
  (let [seen (atom []) args [:journal :parent :module :text :filename :segments :store]]
    (with-redefs-fn {#'c/prepare-source-child-with! (fn [factory & actual] (swap! seen conj [factory actual]) :prepared)}
      #(do (is (= :prepared (apply c/prepare-source-child! args)))
           (is (= :prepared (apply c/prepare-general-source-child! args)))))
    (is (identical? checked-driver/open-driver (ffirst @seen)))
    (is (identical? checked-driver/open-general-driver (first (second @seen))))
    (is (every? #(= args (vec (second %))) @seen))))
