(ns ansatz-lean-jvm-io-error-checks
  "Partial error projection models; these are not guest/native layout authority."
  (:require [clojure.test :refer [deftest is run-tests]]
            [ansatz.lean.jvm.value :as value] [ansatz.lean.jvm.ir :as ir])
  (:import [ansatz.lean.jvm LeanException] [java.util Map HashMap]
           [java.lang.reflect InvocationTargetException]
           [java.util.concurrent CancellationException]))
(deftype ErrorModel [tag rc fields scalars dead array ref readyTask closure metadata])
(defn- field [name] (doto (.getDeclaredField ErrorModel name) (.setAccessible true)))
(def ctx {:class ErrorModel :node-class ErrorModel :tag (field "tag") :rc (field "rc")
          :fields (field "fields") :scalars (field "scalars")})
(defn- node
  ([message] (node message {}))
  ([message flags]
   (ErrorModel. (:tag (deref (var-get #'value/user-error-layout))) (get flags :rc 1)
                (object-array (get flags :fields [message])) (byte-array (get flags :scalar-bytes 0))
                (get flags :dead false) (get flags :array false) false false nil (:metadata flags))))
(defn- project-failure [failure]
  (let [method (.getDeclaredMethod (Class/forName "ansatz.lean.jvm.Bridge") "failure" (into-array Class [Throwable]))]
    (.setAccessible method true)
    (try (.invoke method nil (object-array [failure]))
         (catch InvocationTargetException wrapper (throw (.getCause wrapper))))))
(defn- guest [details]
  (ex-info "Lean IO entry returned an error" {:code "GuestIOError" :guest-io-error details :private-owner (Object.)}))
(deftest authenticated-user-error-message-is-a-borrowed-immutable-value
  (doseq [message ["" "hello" "λ😀\u0000"]]
    (let [raw (node message)
          details (with-redefs [ir/retain! (fn [& _] (throw (AssertionError. "must not retain")))
                               ir/release! (fn [& _] (throw (AssertionError. "must not release")))]
                    (value/decode-io-error ctx raw))
          ^LeanException error (project-failure (guest details))]
      (is (= {"kind" "userError" "message" message} details))
      (is (= details (.details error)))
      (is (= "GuestIOError" (.code error)))
      (is (nil? (.getCause error)))
      (is (= 1 (.-rc raw)))
      (is (thrown? UnsupportedOperationException (.put ^Map (.details error) "owner" (Object.)))))))
(deftest diagnostic-text-is-bounded-with-explicit-truncation
  (let [message (str (apply str (repeat 2047 "x")) "😀tail")
        details (value/decode-io-error ctx (node message))]
    (is (= 2047 (count (get details "message"))))
    (is (true? (get details "messageTruncated"))))
  (doseq [message [(apply str (repeat 2048 "x")) (apply str (repeat 70000 "x"))]]
    (let [details (value/decode-io-error ctx (node message))]
      (is (= 2048 (count (get details "message"))))
      (is (= (when (> (count message) 2048) true) (get details "messageTruncated")))))
  (let [^LeanException error (project-failure (guest (Map/of "kind" "userError" "message" (apply str (repeat 70000 "x")))))]
    (is (= 2048 (count (get (.details error) "message"))))
    (is (true? (get (.details error) "messageTruncated")))))
(deftest outside-profile-errors-stay-generic-and-malformed-candidates-are-refused
  (is (nil? (value/decode-io-error ctx (long 0))))
  (is (nil? (value/decode-io-error ctx (Object.))))
  (let [raw (node "ignored")]
    (.set ^java.lang.reflect.Field (:tag ctx) raw (long 99))
    (is (nil? (value/decode-io-error ctx raw))))
  (doseq [raw [(node (Object.)) (node "\ud800") (node "\udc00")
               (node "x" {:dead true}) (node "x" {:array true})
               (node "x" {:scalar-bytes 1}) (node "x" {:fields []})
               (node "x" {:rc -1}) (node "x" {:metadata (Object.)})]]
    (is (= "RuntimeBoundary" (try (value/decode-io-error ctx raw) nil
                                  (catch clojure.lang.ExceptionInfo error (:code (ex-data error)))))))
  (is (empty? (.details ^LeanException (project-failure (guest nil))))))
(deftest bridge-allows-only-the-partial-standard-java-value-shape
  (doseq [details [{"kind" "userError" "message" "clojure map"}
                   (HashMap. {"kind" "userError" "message" "mutable"})
                   (Map/of "kind" "otherError" "message" "x")
                   (Map/of "kind" "userError" "message" (Object.))
                   (Map/of "kind" "userError" "message" "x" "owner" (Object.))
                   (Map/of "kind" "userError" "message" "x" "messageTruncated" false)
                   (Map/of "kind" "userError" "message" "\ud800")]]
    (is (empty? (.details ^LeanException (project-failure (guest details))))))
  (let [details (Map/of "kind" "userError" "message" "inner")
        ^LeanException wrapped (project-failure (InvocationTargetException. (guest details)))
        ^LeanException cancelled (project-failure (ex-info "outer" {:code "GuestIOError" :guest-io-error details}
                                                           (CancellationException. "cancelled")))]
    (is (= details (.details wrapped)))
    (is (= "Cancelled" (.code cancelled)))
    (is (empty? (.details cancelled))))
  (is (empty? (.details ^LeanException (project-failure (ex-info "other" {:code "ResourceLimit"
                                                                                 :guest-io-error (Map/of "kind" "userError" "message" "x")}))))))
(deftest diagnostic-decoding-observes-cancellation
  (try
    (.interrupt (Thread/currentThread))
    (is (= "Cancelled" (try (value/decode-io-error ctx (node "x")) nil
                            (catch clojure.lang.ExceptionInfo error (:code (ex-data error))))))
    (finally (Thread/interrupted))))
(defn check! [] (run-tests 'ansatz-lean-jvm-io-error-checks))
