(ns original-stdin-configuration-v1
  "Trusted child-only construction through authenticated ORIGINAL guest bodies.
   Uses no graph/module import slot, new Source, runtime handle or synthetic IR."
  (:require [java-ir-baseline :as j]
            [ansatz.research.ir.source-setup :as source]
            [ansatz.research.ir.authenticated-demand :as demand]
            [sequential-frontend-probe :as sp]
            [allocation-heartbeat-cohort-v1 :as cohort]))
(def pins
  [["IO.FS.withIsolatedStreams._redArg._closed_0" "98841c196288d273c67d1828f4d03df6367a7b7e1f6e7e206e3f12eb79a7f74e"]
   ["IO.mkRef._boxed" "b7753cf6e21233284e51ca2dec98c88083991a5438497c1ddde5551a706d1905"]
   ["IO.FS.Stream.ofBuffer" "c98d47dcb02a469b6615689c519e3f000251ce95be5363c67a5354e8fc43108e"]
   ["IO.FS.Stream.ofBuffer._lam_4._boxed" "e832604259e5794a331574c8a391637cde19e6f28ec322fc86a376a87b6c0c83"]
   ["IO.FS.Stream.ofBuffer._lam_0._boxed" "29e0f37498cc280d39c84ad0fa70336c5713b90308e32ee960d4ba28a7afbcac"]
   ["IO.FS.Stream.ofBuffer._lam_1._boxed" "370ad89209e61c6fbe137e22e27d42200c02f50bb90cbaff442868ca0ecbd24a"]
   ["IO.FS.Stream.ofBuffer._lam_3._boxed" "41ab29cdd05e589e44148a3f6051b995992290d55733ab2bd234a1bed4c13ae6"]
   ["IO.FS.Stream.ofBuffer._lam_2._boxed" "27399d0e9fd073070f6cc12f7d726b8c3d91cf17ec30e478eca80a81becfaa35"]
   ["IO.FS.instInhabitedStream.default._lam_5._boxed" "67b99a70a0d3bacecd41baf5e321468782636888e2b7a45febc15918216a7e89"]])
(defn- need [ok message] (when-not ok (throw (ex-info message {:scope :original-child-stdin-configuration-v1}))))
(defn- guard! [child]
  (let [d (:driver child)]
    (source/guard-source! (:code-receipt child) (:source d))
    (need (and (:lab-heartbeat-provider child)
               (identical? (:lab-heartbeat-provider child) (:lab-heartbeat-provider d))) "Actual branch heartbeat provider required")
    (need (= "idle" (j/phase @(:current-ctx d) (:engine d))) "Child stdin configuration requires idle engine")))
(defn- headers! [child]
  (guard! child)
  (let [d (:driver child)]
    (into {} (for [[label sha] pins
                   :let [h (demand/ensure-header! d (sp/typed-name label))]]
               (do (need (and (identical? (:source d) (j/request-value h "source"))
                              (= sha (j/request-value h "originalSha256"))
                              (= (sp/typed-name label) (j/lean-name-data (j/request-value h "name")))
                              (= "fdecl" (j/request-value h "kind")))
                         "Original stdin factory/method Header differs")
                   [label h])))))
(defn configure-child!
  "Run only on a FRESH child AFTER genuine startup. Journal is private custody,
   not printable receipt. Borrow supplied child/Source/Provider unchanged.
   On failure keep journal/actual continuation; no retry or invented cleanup."
  [child journal]
  (need (and (instance? clojure.lang.IAtom journal) (map? @journal)
             (nil? (:stdio-defaults @journal))) "Fresh child stdin ownership journal required")
  (need (= :ready (:state @(:startup-status child))) "Construct stdin only after genuine child startup; never on pristine seed")
  (let [buffer (object-array [nil :pending]) ref (object-array [nil :pending])
        stream (object-array [nil :pending]) default (object-array [nil :unclaimed])
        unit (object-array [nil :pending]) d (:driver child) e (:engine d)
        record {:state :validating :engine e :source (:source d)
                :owners {:buffer buffer :ref ref :stream stream :default default :release-result unit}}]
    (swap! journal assoc :stdio-defaults record)
    (try
      (let [hs (headers! child)]
        (swap! journal assoc-in [:stdio-defaults :state] :constructing-buffer)
        (let [v (cohort/guest-call! child "IO.FS.withIsolatedStreams._redArg._closed_0" [])]
          (aset buffer 0 v) (aset buffer 1 :owned))
        (guard! child)
        (swap! journal assoc-in [:stdio-defaults :state] :constructing-ref)
        (aset buffer 1 :transfer-attempted)
        (let [v (cohort/guest-call! child "IO.mkRef._boxed" [0 (aget buffer 0) 0])]
          ;; Capture every taken result BEFORE further validation/allocation.
          (aset ref 0 v) (aset ref 1 :owned) (aset buffer 1 :transferred))
        (guard! child)
        (swap! journal assoc-in [:stdio-defaults :state] :constructing-stream)
        (aset ref 1 :transfer-attempted)
        (let [v (cohort/guest-call! child "IO.FS.Stream.ofBuffer" [(aget ref 0)])]
          (aset stream 0 v) (aset stream 1 :owned) (aset ref 1 :transferred))
        (guard! child)
        (swap! journal assoc-in [:stdio-defaults :state] :install-attempted)
        ;; BORROWS the stream. Runtime validates actual graph/liveness/source
        ;; method identities BEFORE retaining one engine-disposal-owned default.
        (j/install-stdio-defaults! @(:current-ctx d) e (get hs "IO.FS.Stream.ofBuffer") (aget stream 0))
        (aset default 0 (aget stream 0)) (aset default 1 :engine-dispose-owned)
        (swap! journal assoc-in [:stdio-defaults :state] :external-stream-release-attempted)
        (guard! child)
        (aset stream 1 :release-attempted)
        (j/start-release! @(:current-ctx d) e (aget stream 0) 1)
        (aset stream 1 :release-in-flight)
        (let [boundary (cohort/drive! child 20000)]
          (need (= "complete" (:phase boundary)) "Original stdin external owner release paused; preserve journal")
          (let [v (j/take-result! @(:current-ctx d) e)]
            (aset unit 0 v) (aset unit 1 :owned)
            (aset stream 0 nil) (aset stream 1 :released)
            (need (and (instance? Long v) (= 0 v)) "Stream owner release returned non-Unit")
            (aset unit 1 :consumed)))
        (guard! child)
        (swap! journal assoc-in [:stdio-defaults :state] :ready)
        child)
      (catch Throwable failure
        ;; Do not mutate ownership dispositions after an uncertain native start.
        (swap! journal assoc-in [:stdio-defaults :failure]
               {:message (.getMessage failure) :class (.getName (class failure))})
        (throw (ex-info "Original child stdin configuration failed; preserve private journal/owners" {} failure))))))
