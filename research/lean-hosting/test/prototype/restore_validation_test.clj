(ns prototype.restore-validation-test
  "Small whole-world checkpoint eligibility tests. These models are neither a
   checked Lean Environment nor a restored native Source or executable authority."
  (:require [clojure.test :refer [deftest is]]
            [prototype.machine :as m]
            [prototype.checkpoint-wire :as wire]
            [prototype.checkpoint-wire-test :as codec]
            [prototype.restore-consumer :as restore]))

(def function-name ["str" ["anonymous"] "validationModel"])
(defn valid-world []
  {:status :done :functions {function-name {:params [] :body [:ret [:tag 0]]}}
   :heap {1 {:kind :ctor :tag 0 :fields [] :rc 1}
          2 {:kind :ctor :tag 0 :fields [(m/->Ref 1)] :rc 1}}
   :globals {function-name {:status :ready :value (m/->Tag 0)}}
   :native-imports [] :eval-const-authorizations {} :next-id 3
   :frames [] :body [] :locals {} :joins {} :events [] :stats {}
   :result (m/->Ref 2)})
(defn validate-world! [world recipes]
  (#'restore/world! world recipes {:io-result (:result world)}))
(defn at-sites [value]
  (let [w (valid-world)]
    {:function (assoc-in w [:functions function-name :body] value)
     :heap (assoc-in w [:heap 1 :fields] value)
     :global (assoc-in w [:globals function-name :value] value)
     :state (assoc w :stats {:sample value})}))
(defn failure-shape [f]
  (try (f) :accepted
       (catch Throwable cause [(.getName (class cause)) (.getMessage cause) (ex-data cause)])))

(deftest completed-world-validation-preserves-original-identities
  (let [world (valid-world) visits (atom 0) validate wire/validate-value!]
    (with-redefs [wire/validate-value! (fn [x] (swap! visits inc) (validate x))
                  wire/wire-value (fn [_] (throw (AssertionError. "world! must not emit discarded wire ASTs")))]
      (let [returned (validate-world! world [])]
        (is (identical? world returned))
        (is (identical? (:functions world) (:functions returned)))
        (is (identical? (get-in world [:functions function-name :body])
                        (get-in returned [:functions function-name :body])))
        (is (identical? (:result world) (:result returned)))
        (is (identical? (get-in world [:heap 2 :fields 0]) (get-in returned [:heap 2 :fields 0])))))
    ;; One function + two heap nodes + one global + state. Exercises all four
    ;; production callsite families rather than testing the visitor in isolation.
    (is (= 5 @visits))))

(deftest malformed-values-are-rejected-at-every-world-partition
  (doseq [value [[(Object.)] (with-meta [1] {:opaque (Object.)})
                 (codec/->MetaVector [1] {:opaque (Object.)})]
          [site world] (at-sites value)]
    (is (not= :accepted (failure-shape #(validate-world! world []))) (name site))))

(deftest custom-sequence-fallbacks-keep-whole-world-acceptance
  (doseq [value [(codec/->MetaVector [1] {:origin :model})
                 (codec/->InitSensitiveVector false)
                 (subvec [0 1 2] 1 3)]
          [site world] (at-sites value)]
    (is (identical? world (validate-world! world [])) (name site)))
  (doseq [[site world] (at-sites (codec/->InitSensitiveVector true))]
    (is (not= :accepted (failure-shape #(validate-world! world []))) (name site))))

(deftest reference-range-and-partition-metadata-gates-remain-active
  (let [world (valid-world)]
    (is (identical? world (validate-world! world [])))
    ;; Dead inactive registers are an explicitly supported checkpoint property.
    (let [inactive (assoc world :locals [ (m/->Ref 999)])]
      (is (identical? inactive (validate-world! inactive []))))
    (is (not= :accepted (failure-shape #(validate-world! (assoc world :stats {:ref (m/->Ref 999)}) []))))
    ;; Model native range metadata exercises range validation without opening or
    ;; claiming a native Source. No native Ref is dereferenced by this model.
    (doseq [id [100 109]]
      (let [w (-> world (assoc :next-id 200) (assoc-in [:globals function-name :value] (m/->Ref id)))]
        (is (identical? w (validate-world! w [{:id "model-range" :base 100 :size 10}])))))
    (let [w (-> world (assoc :next-id 200) (assoc-in [:globals function-name :value] (m/->Ref 110)))]
      (is (not= :accepted (failure-shape #(validate-world! w [{:id "model-range" :base 100 :size 10}])))))
    (doseq [path [[:functions] [:heap] [:globals] [:native-imports]
                  [:eval-const-authorizations]]]
      (is (not= :accepted
                (failure-shape #(validate-world! (update-in world path with-meta {}) [])))))))

(deftest preparation-still-returns-its-transformed-wire-representation
  (let [input {:factory-id "model" :implementation-sha256 (apply str (repeat 64 "a"))
               :catalogue-recipe {:floating -0.0} :kernel-policy {} :trusted-roots [["model"]]}
        result (#'restore/preparation! input)]
    (is (tagged-literal? (get-in result [:catalogue-recipe :floating])))
    (is (instance? Double (get-in input [:catalogue-recipe :floating])))
    (is (not (identical? input result)))))
