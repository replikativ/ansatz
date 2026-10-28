(ns prototype.code-provenance
  "Host-side identity index of source instructions. Runtime continuations and
   literal payloads are not source code. Discovery is not IR validation."
  (:import [java.util IdentityHashMap]))

(defn- source-vector? [value]
  ;; SubVector may wrap a custom vector with effectful reads.
  (identical? clojure.lang.PersistentVector (class value)))

(defn- children [body]
  (let [op (nth body 0 nil)
        b (nth body 2 nil) c (nth body 3 nil) d (nth body 4 nil)]
    (when (keyword? op)
      (case op
        :let [c]
        :call [d]
        :join [c d]
        :case (when (source-vector? b)
                (into [] (keep #(when (source-vector? %) (nth % 1 nil))) b))
        (:inc :dec :set-tag) [c]
        (:set :scalar-set :host) [d]
        (:del :suspend) [b]
        []))))

(defn admit-body!
  "Add only known syntactic instruction edges, without validating expressions
   or visiting literals, operands, unknown forms or custom containers. Caller
   synchronizes mutations after publishing the index. Returns the same index."
  [^IdentityHashMap index root]
  (loop [pending [root]]
    (when (seq pending)
      (let [body (peek pending) pending (pop pending)]
        (if (or (not (source-vector? body)) (.containsKey index body))
          (recur pending)
          (do (.put index body true)
              (recur (into pending (children body))))))))
  index)

(defn index-functions [functions]
  (let [index (IdentityHashMap.)]
    (doseq [function (vals functions)] (admit-body! index (:body function)))
    index))
