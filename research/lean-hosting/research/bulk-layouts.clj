(ns bulk-layouts
  "Research-only static-layout validation and heap lookup controls.
   Scoped, bounded caches; no production defaults or authority is issued."
  (:require [prototype.machine :as m]
            [prototype.scalar :as scalar]
            [prototype.native-heap :as native])
  (:import [java.util IdentityHashMap]))

(defn native-reference-no-seq [world ref]
  (and (m/ref? ref)
       (native/imported? (or (:native-imports world)
                             (:native-imports (:world-context world))) (:id ref))))

(defn layout-no-seq [{:keys [objects usize ssize] :as layout}]
  (when-not (and (integer? objects) (<= 0 objects 1048576)
                 (integer? usize) (<= 0 usize 1048576)
                 (integer? ssize) (<= 0 ssize 1048576)
                 (< objects 256) (< (+ (* 8 usize) ssize) 1024) (pos? (+ usize ssize)))
    (throw (ex-info "Invalid scalar constructor layout" {:layout layout})))
  layout)

(defn benchmark [context n]
  (let [layout scalar/layout! native-reference m/native-reference?
        cache (IdentityHashMap.) counts (atom {:hits 0 :misses 0})
        eligible? #(or (= clojure.lang.PersistentArrayMap (class %))
                       (= clojure.lang.PersistentHashMap (class %)))
        checked-layout (fn [value]
                         (if (and (eligible? value) (.containsKey cache value))
                           (do (swap! counts update :hits inc) value)
                           (let [result (layout value)]
                             (swap! counts update :misses inc)
                             (when (eligible? value)
                               (when (>= (.size cache) 64) (.clear cache))
                               (.put cache value true))
                             result)))
        run (get-in context [:workloads :jvm-private])
        expected ((get-in context [:workloads :reference]) n)
        dispatch (fn [mode]
                   (with-redefs [scalar/layout! (if (#{:layout :both} mode) checked-layout layout)
                                 m/native-reference? (if (#{:native :both} mode) native-reference-no-seq native-reference)]
                     (run n)))]
    ;; Diagnostic counting is disabled in timed layout cache hits below: atom
    ;; updates would be an unrelated allocation source. Misses are warmed first.
    (doseq [_ (range 8) mode [:ordinary :layout :native :both]] (dispatch mode))
    (let [checked-layout-fast (fn [value]
                                (if (and (eligible? value) (.containsKey cache value)) value
                                  (checked-layout value)))]
      {:scope "Paired experimental controls; layout facts are immutable ordinary-map values validated by original function; no native Source in this workload. Cache limited to64 and scoped to benchmark."
       :n n :runs
       (vec (for [trial (range 7)
                  mode (if (even? trial) [:ordinary :layout :native :both :layout-direct :direct-both]
                           [:direct-both :layout-direct :both :native :layout :ordinary])]
              (let [[actual metrics]
                    (prototype.unchanged-program-benchmark/measure
                     #(with-redefs [scalar/layout! (cond (#{:layout :both} mode) checked-layout-fast
                                                         (#{:layout-direct :direct-both} mode) layout-no-seq
                                                         :else layout)
                                    m/native-reference? (if (#{:native :both :direct-both} mode) native-reference-no-seq native-reference)]
                        (run n)))]
                (assert (= expected actual))
                (assoc metrics :trial trial :mode mode))))
       :layout-identities (.size cache) :warmup-counts @counts})))
