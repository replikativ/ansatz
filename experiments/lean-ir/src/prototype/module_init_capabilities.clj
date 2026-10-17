(ns prototype.module-init-capabilities
  "Native module-initializer availability over explicitly trusted guest plans.
   Mirrors Lean 4.33.1 ir_interpreter.cpp lean_run_mod_init_core: unavailable
   symbols return IO.ok false, enabling the REAL guest InitAttr fallback.
   This capability never executes, invents or marks module initializers."
  (:require [clojure.set :as set] [prototype.module-plan :as plan]
            [prototype.machine :as m] [prototype.runtime-string :as string]
            [prototype.runtime-prim :as prim]))

(def signature
  {:params [{:ty "object" :borrow true} {:ty "void" :borrow false}]
   :return-type "object"})
(def ^:private ops {:ref? m/ref? :node m/node})
(defn- fail [message data] (throw (ex-info message data)))

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
   Guards are snapshot-local and never modified by this capability."
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
               [symbol (:initialized (plan/expand module-plans module phase))])))]
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
                (if (set/subset? needed guards) 1 0)
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
