(ns prototype.module-init-capabilities
  "Native module-initializer availability over explicitly trusted guest plans.
   Mirrors Lean 4.33.1 ir_interpreter.cpp lean_run_mod_init_core: unavailable
   symbols return IO.ok false, enabling the REAL guest InitAttr fallback.
   This capability never executes, invents or marks module initializers."
  (:require [prototype.machine :as m] [prototype.runtime-string :as string]
            [prototype.runtime-prim :as prim]))

(def signature
  {:params [{:ty "object" :borrow true} {:ty "void" :borrow false}]
   :return-type "object"})
(def ^:private ops {:ref? m/ref? :node m/node})
(defn- fail [message data] (throw (ex-info message data)))

(defn- guard-dependencies [plans [module phase]]
  (when-not (contains? #{:all :runtime :comptime} phase)
    (fail "Unknown module initialization phase" {:module module :phase phase}))
  (let [producer (get plans module)]
    (when-not producer
      (fail "Missing producer module initialization plan" {:module module :phase phase}))
    (when (and (not (:moduleSystem producer)) (not= :all phase))
      (fail "Classic Lean module has no split initialization entry" {:module module :phase phase}))
    ;; Preserve expand's eager traversal/destructuring failures for reachable
    ;; action collections, without constructing or retaining its action list.
    ;; This is not a new strict action-schema validator: legacy opaque action
    ;; payloads remain data. Split :all has no separate local action pass.
    (when-not (and (:moduleSystem producer) (= :all phase))
      (reduce (fn [_ {:keys [action meta]}]
                (when (or (= :all phase) (= (boolean meta) (= :comptime phase)))
                  (do action (boolean meta) nil)))
              nil (:actions producer)))
    (cond->
      (into []
        (comp (filter (fn [{:keys [meta]}]
                        (or (= :all phase) (= (boolean meta) (= :comptime phase)))))
              (map (fn [{:keys [module meta]}]
                     [module (if (or (= :all phase) (not meta)) phase :runtime)])))
        (:imports producer))
      (and (:moduleSystem producer) (= :all phase))
      (conj [module :runtime] [module :comptime]))))

(defn- guard-dependency-graph [plans roots]
  ;; One validated node per reachable [module phase], not one entire transitive
  ;; closure per symbol. Mark on discovery, exactly as plan/expand handles cycles.
  (loop [pending (vec roots) graph {}]
    (if-let [entry (peek pending)]
      (if (contains? graph entry)
        (recur (pop pending) graph)
        (let [children (guard-dependencies plans entry)]
          (recur (into (pop pending) children) (assoc graph entry children))))
      graph)))

(defn- guards-present? [graph root guards]
  ;; Query-local scratch only: never mutate the shared graph or guest guards,
  ;; and never reuse a result/visited set across worlds. Preserve stack order.
  (let [pending (java.util.ArrayDeque.)
        visited (java.util.HashSet.)]
    (.addLast pending root)
    (loop []
      (if (.isEmpty pending)
        true
        (let [entry (.removeLast pending)]
          (cond
            (not (.add visited entry)) (recur)
            (not (contains? guards entry)) false
            :else (let [children (get graph entry)]
                    (dotimes [i (count children)]
                      (.addLast pending (nth children i)))
                    (recur))))))))

(defn make-bindings
  "Options are trusted HOST inputs, never names inferred from guest strings:
   :module-plans maps structured module Names to pinned producer plans;
   :initialized-symbols maps exact native symbols to {:module Name :phase p}.
   Caller must authenticate these plans and mappings against its pinned producer.
   Empty options expose no native initializer symbols.

   A symbol is available only if ALL guards in its producer dependency/phase
   closure are present in this world's :initialized-modules. In particular a
   split :all needs both runtime and comptime guards. Merely entered or failed
   partial phases cannot suppress the guest fallback. Unknown, unentered and
   incomplete entries return false, even for a genuinely empty initializer.
   Guards are snapshot-local and never modified by this capability. Shared
   validated dependency edges are retained once; queries traverse only the
   selected root and never retain per-symbol transitive guard sets."
  ([] (make-bindings {}))
  ([{:keys [module-plans initialized-symbols]
     :or {module-plans {} initialized-symbols {}}}]
   (when-not (and (map? module-plans) (map? initialized-symbols))
     (fail "Expected explicit trusted initializer mappings and plans" {}))
   (doseq [[name producer] module-plans]
     (when-not (and (= "lean-init-plan/1" (:schema producer)) (= name (:module producer)))
       (fail "Invalid trusted producer initialization plan" {:module name})))
   (let [required
         (into {}
           (for [[symbol {:keys [module phase]}] initialized-symbols]
             (do
               (when-not (and (string? symbol) (seq symbol) (not (.contains ^String symbol "\u0000"))
                              (contains? #{:all :runtime :comptime} phase))
                 (fail "Invalid trusted native initializer mapping" {:symbol symbol :module module :phase phase}))
               [symbol [module phase]])))
         graph (guard-dependency-graph module-plans (vals required))]
     {"lean_run_mod_init_core"
      {:signature signature
       :handler
       (fn [_ world [symbol _]]
         (let [symbol (string/string-value ops world symbol)
               guards (or (:initialized-modules world) #{})]
           (when-not (set? guards)
             (fail "World initialization guards must be a set" {}))
           (m/allocate world :ctor 0
             [(if-let [needed (get required symbol)]
                (if (guards-present? graph needed guards) 1 0)
                0)])))}})))

(defn options-from-witness
  "Intersect trusted producer plans with a pinned native symbol metadata witness.
   Caller authenticates the witness artifact (e.g. expected SHA256) before JSON
   decoding it with keyword keys. No native Environment is transported. Symbols
   for modules absent from PLANS and nonexistent classic split entries are NOT
   exposed. This helper does not manufacture module names or package prefixes."
  [module-plans witness]
  (when-not (and (= "lean-module-initializer-symbols/1" (:schema witness))
                 (= "4.33.1" (:leanVersion witness))
                 (= (get prim/pinned-build "lean_get_githash") (:leanCommit witness))
                 (false? (:nativeEnvironmentTransported witness))
                 (= {:wordBits 64 :target (get prim/pinned-build "lean_system_platform_target")}
                    (:runtimeProfile witness))
                 (vector? (:symbols witness)))
    (fail "Untrusted or incompatible module initializer symbol witness" {}))
  {:module-plans module-plans
   :initialized-symbols
   (reduce
     (fn [out {:keys [symbol module phase]}]
       (let [phase ({"all" :all "runtime" :runtime "comptime" :comptime} phase)]
         (when-not (and phase (string? symbol) (seq symbol))
           (fail "Invalid module initializer symbol witness entry" {:symbol symbol}))
         (if-let [producer (get module-plans module)]
           (if (or (:moduleSystem producer) (= :all phase))
             (let [entry {:module module :phase phase}]
               (when (and (contains? out symbol) (not= (get out symbol) entry))
                 (fail "Conflicting module initializer symbol witness" {:symbol symbol}))
               (assoc out symbol entry))
             out)
           out))) {} (:symbols witness))})
