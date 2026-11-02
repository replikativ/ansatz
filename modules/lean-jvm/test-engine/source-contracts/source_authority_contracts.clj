(ns source-authority-contracts
  "Current SDK authority boundaries using genuine portable native captures.
   No native receipt is manufactured and no historical World implementation loads."
  (:require [clojure.test :refer [deftest is run-tests]]
            [clojure.java.io :as io]
            [clojure.data.json :as json]
            [ansatz.lean.jvm.artifact :as artifact]
            [ansatz.lean.jvm.publisher :as publisher]
            [ansatz.lean.jvm.project :as project]
            [ansatz.lean.jvm.startup :as startup]
            [ansatz.lean.jvm.ir :as ir])
  (:import [java.io ByteArrayInputStream ByteArrayOutputStream]
           [java.math BigInteger]
           [java.util Arrays]))

(def ^:dynamic *module-root* ".")
(defn- fixture []
  ;; The checked-in descriptor is independent of the candidate archive.
  (let [root (io/file *module-root* "consumer/resources/lean")
        descriptor (json/read-str (slurp (io/file root "interop.json")))]
    (with-open [input (io/input-stream (io/file root "interop.zip"))]
      {:data (.readAllBytes input) :manifest (get descriptor "manifestSHA256")})))
(defn- load-receipt [{:keys [data manifest]}]
  (artifact/load! (ByteArrayInputStream. data) manifest))
(defn- code [attempt]
  (try (attempt) nil (catch clojure.lang.ExceptionInfo failure (:code (ex-data failure)))))

(deftest an-issued-artifact-is-neither-source-issuance-nor-startup-readiness
  (let [receipt (load-receipt (fixture))
        payload (artifact/authenticated-artifact receipt)
        output (ByteArrayOutputStream.)
        called (atom false)]
    (is (= "lean-native-local-project/2" (:profile payload)))
    (is (thrown? clojure.lang.ExceptionInfo
                 (publisher/prepare-build-bytes! (ir/linked-basis) receipt (byte-array 0))))
    (is (thrown? clojure.lang.ExceptionInfo (artifact/export! receipt output)))
    (is (zero? (.size output)))
    (is (thrown? clojure.lang.ExceptionInfo (startup/open! receipt nil)))
    (is (thrown? clojure.lang.ExceptionInfo
                 (startup/with-ready-engine! receipt (fn [_] (reset! called true)))))
    (is (false? @called))
    ;; Failed attempts cannot alter the actual issued artifact's authority.
    (is (identical? payload (artifact/authenticated-artifact receipt)))))

(deftest caller-bytes-and-stream-lifetime-cannot-alter-issued-artifact-facts
  (let [{:keys [data manifest]} (fixture)
        closed (atom false)
        input (proxy [ByteArrayInputStream] [data] (close [] (reset! closed true)))
        receipt (artifact/load! input manifest)
        payload (artifact/authenticated-artifact receipt)]
    (is (false? @closed))
    (Arrays/fill ^bytes data (byte 0))
    (.close input)
    (is (true? @closed))
    (is (identical? payload (artifact/authenticated-artifact receipt)))
    (is (= manifest (:manifest-sha256 (artifact/authenticated-artifact receipt))))
    ;; A descriptive payload copy is never another issuer token.
    (is (thrown? clojure.lang.ExceptionInfo
                 (publisher/prepare-artifact! (ir/linked-basis) (into {} payload) (byte-array 0))))))

(deftest failed-load-and-same-artifact-peer-cannot-replace-project-authority
  (let [{:keys [data manifest]} (fixture)
        services (project/runtime-service!)
        open #(project/open-artifact! services (ByteArrayInputStream. data) manifest)
        left (open)]
    (try
      (let [right (open)]
        (try
          (let [left-handle (project/lookup-function! left "answer" "nat-to-nat")
                right-handle (project/lookup-function! right "answer" "nat-to-nat")
                invoke #(project/invoke-function! %1 %2 (BigInteger/valueOf 20))]
            (is (= (BigInteger/valueOf 41) (invoke left left-handle)))
            (is (= "EntryRejected" (code #(invoke right left-handle))))
            (is (= "EntryRejected" (code #(project/function-descriptor! right left-handle))))
            (is (thrown? clojure.lang.ExceptionInfo
                         (project/open-artifact! services (ByteArrayInputStream. data) (apply str (repeat 64 "0")))))
            (is (= (BigInteger/valueOf 41) (invoke right right-handle)))
            (project/close! left)
            (is (= "RuntimeBoundary" (code #(invoke left left-handle))))
            (is (= (BigInteger/valueOf 41) (invoke right right-handle))))
          (finally (project/close! right))))
      (finally (project/close! left)))))

(defn check! [module-root]
  (binding [*module-root* module-root] (run-tests 'source-authority-contracts)))
