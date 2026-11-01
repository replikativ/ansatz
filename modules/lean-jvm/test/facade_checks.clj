(ns ansatz-lean-jvm-facade-checks
  "Actual Java facade error/lifetime models. No guest or native execution."
  (:require [clojure.test :refer [deftest is run-tests]]
            [ansatz.lean.jvm.project :as project])
  (:import [ansatz.lean.jvm Lean LeanProject LeanException]
           [java.lang.reflect InvocationTargetException]
           [java.security ProviderException] [java.util.concurrent CancellationException]))
(defn- field [object name]
  (let [field (.getDeclaredField (class object) name)] (.setAccessible field true) (.get field object)))
(defn- project-wrapper [lean token]
  (let [constructor (.getDeclaredConstructor LeanProject (into-array Class [Lean Object]))]
    (.setAccessible constructor true)
    (let [project (.newInstance constructor (object-array [lean token]))]
      (.add ^java.util.Set (field lean "projects") project) project)))
(defn- project-failure [failure]
  (let [bridge (Class/forName "ansatz.lean.jvm.Bridge")
        method (.getDeclaredMethod bridge "failure" (into-array Class [Throwable]))]
    (.setAccessible method true)
    (try (.invoke method nil (object-array [failure]))
         (catch InvocationTargetException wrapper (throw (.getCause wrapper))))))
(deftest bounded-ordinary-projection-and-actual-fatal-identity
  (let [failure (ex-info "wrapper" {:private-owner (Object.)}
                         (ProviderException. "provider" (CancellationException. "cancelled")))
        ^LeanException projected (project-failure failure)]
    (is (= "Cancelled" (.code projected)))
    (is (= "java.util.concurrent.CancellationException" (.category projected)))
    (is (nil? (.getCause projected)))
    (is (not (.isInterrupted (Thread/currentThread)))))
  (let [fatal (OutOfMemoryError. "synthetic model")]
    (is (identical? fatal (try (project-failure (ex-info "wrapper" {} fatal)) nil (catch Error actual actual)))))
  (try
    (let [^LeanException projected (project-failure (RuntimeException. (InterruptedException. "stop")))]
      (is (= "Cancelled" (.code projected)))
      (is (.isInterrupted (Thread/currentThread))))
    (finally (Thread/interrupted))))
(deftest lean-close-attempts-all-children-and-preserves-fatal
  (let [lean (Lean/open) first (Object.) second (Object.) third (Object.)
        fatal (AssertionError. "actual host error") visited (atom [])
        children (mapv #(project-wrapper lean %) [first second third])]
    (with-redefs [project/close! (fn [token]
                                  (swap! visited conj token)
                                  (cond (identical? first token) (throw fatal)
                                        (identical? second token) (throw (ex-info "cleanup failed" {:code "RuntimeBoundary"}))))]
      (is (identical? fatal (try (.close lean) nil (catch Error actual actual))))
      (is (= [first second third] @visited))
      (is (.isEmpty ^java.util.Set (field lean "projects")))
      (is (every? #(nil? (field % "token")) children))
      (.close lean)
      (doseq [child children] (.close ^LeanProject child))
      (is (= 3 (count @visited))))))
(defn check! [] (run-tests 'ansatz-lean-jvm-facade-checks))
