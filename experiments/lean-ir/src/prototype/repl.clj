(ns prototype.repl
  "Function-only refresh for this experiment's already-loaded runtime namespaces.
   Preserves records, sentinels and resident machine values; not a general ns reloader."
  (:require [clojure.java.io :as io]))

(defn refresh-functions! [namespace source]
  (let [target (or (find-ns namespace) (throw (ex-info "Require namespace first" {:namespace namespace})))]
    (with-open [reader (java.io.PushbackReader. (io/reader source))]
      (binding [*ns* target *read-eval* false]
        (let [read-form #(read {:eof ::eof :read-cond :allow :features #{:clj}} reader)
              header (read-form)]
          (when-not (and (= 'ns (first header)) (= namespace (second header)))
            (throw (ex-info "Refresh source namespace mismatch" {:namespace namespace})))
          (loop [names []]
            (let [form (read-form)]
              (if (= ::eof form) names
                (if (and (seq? form) (contains? #{'defn 'defn-} (first form)))
                  (do (eval form) (recur (conj names (second form))))
                  (recur names))))))))))
