(ns java-ir-name-pool-benchmark
  "Metadata-only comparison harness. No CodeReceipt/source/byte authentication.
   Caller supplies its already authenticated original CAS row sequence. Returned
   Header/source roots are benchmark-owned and are NOT admission receipts."
  (:require [java-ir-baseline :as j] [java-ir-generation-checks :as g])
  (:import [java.util IdentityHashMap List Map ArrayList]))

(defn- graph-counts [roots]
  (let [seen (IdentityHashMap.)]
    (loop [todo (vec roots) counts {}]
      (if (empty? todo) counts
        (let [x (peek todo) todo (pop todo)]
          (if (or (nil? x) (.containsKey seen x)) (recur todo counts)
            (let [_ (.put seen x true)
                  cls (.getName (class x))
                  children (cond (instance? Map x) (mapcat (fn [[k v]] [k v]) x)
                                 (instance? List x) (seq x) :else [])]
              (recur (into todo children) (update counts cls (fnil inc 0))))))))))

(defn build!
  "Same function for old/candidate Java bases. ROWS is a bounded reducible/seq of
   {:row original-string-keyed-map :sha256 actual-raw-sha}, each from authenticated
   actual CAS. Do not benchmark via already constructed candidate CompactNames.
   No guest engine, Program body or kernel Env is created. Caller releases its
   input sequence before heap measurement; retain this return value for the dump.
   Counts describe logical List/Map value reachability, NOT physical backing
   arrays, wrapper delegates, map tables, String bytes or exclusive retained size."
  [basis rows {:keys [max-headers source-description] :or {max-headers 20000}}]
  (when-not (and (integer? max-headers) (<= 1 max-headers 20000)
                 (or (nil? source-description) (string? source-description)))
    (throw (ex-info "Explicit bounded metadata header inventory required" {})))
  (let [ctx (j/prepare-host-program basis [] [])
        source (j/source-binding ctx {:benchmark-only true :description source-description})
        started (System/nanoTime)
        headers (reduce (fn [^ArrayList out {:keys [row sha256]}]
                          (when (>= (.size out) max-headers)
                            (throw (ex-info "Metadata benchmark header bound" {})))
                          (.add out (j/declaration-header source row sha256)) out)
                        (ArrayList.) rows)
        roots (mapcat (fn [h] [(.name h) (g/field h "declaration") (.metadata h)]) headers)
        counts (graph-counts roots)
        names (try (g/field source "names") (catch NoSuchFieldException _ nil))
        pool-counts (when names
                      {:nodes (.size ^Map (g/field names "nodes"))
                       :strings (.size ^Map (g/field names "strings"))})]
    {:schema :original-cas-header-metadata-benchmark-v1
     :header-count (.size headers) :elapsed-ms (/ (- (System/nanoTime) started) 1e6)
     :metadata-union-class-counts counts :pool-counts pool-counts
     :headers headers :source source :benchmark-only true :admission-authority false}))
