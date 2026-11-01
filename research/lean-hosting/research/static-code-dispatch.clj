(ns static-code-dispatch
  "REPL-only cache-admission control. No production dispatch change."
  (:require [prototype.lazy-runtime :as lazy]
            [prepared-interpreter])
  (:import [java.util IdentityHashMap]))

(defn static-bodies [functions]
  (let [seen (IdentityHashMap.)
        children (ns-resolve 'prepared-interpreter 'children)]
    (loop [pending (mapv :body (vals functions))]
      (if-not (seq pending) seen
        (let [body (peek pending) pending (pop pending)]
          (if (or (not (identical? clojure.lang.PersistentVector (class body)))
                  (.containsKey seen body))
            (recur pending)
            (do (.put seen body true)
                (recur (into pending (children body))))))))))

(defn runner [program]
  (let [static (static-bodies (:functions program))
        block-var (ns-resolve 'prototype.lazy-runtime 'block!)
        ordinary @block-var]
    (fn [machine fuel]
      (with-redefs-fn
        {block-var (fn [current body]
                     (when (or (not (identical? current program))
                               (.containsKey ^IdentityHashMap static body))
                       (ordinary current body)))}
        #(lazy/run! program machine fuel)))))
