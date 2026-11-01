(ns prototype.module-plan
  "Pure expansion of producer-ordered module initialization plans.
   Mirrors pinned Lean 4.33.1 Lean/Compiler/LCNF/EmitC.lean:
   emitInitFn, emitLegacyInitFn, and main. Producer action payloads are kept
   unchanged; this namespace does not execute guest code.

   Guards are entered before imports, as in native Lean. A split module's
   legacy :all entry visits every direct import at :all, then its own
   :runtime and :comptime entries. It has no independent local action pass.")

(defn- fail [message data] (throw (ex-info message data)))

(defn expand
  "Expand ROOT's PHASE (:all/:runtime/:comptime) into ordered local actions.
   PLANS maps structured module Names to producer initializationPlan maps.
   ALREADY-INITIALIZED contains [module phase] entry guards. The returned set
   includes guards visited even when an import cycle encounters them again.
   This plans successful execution; it does not model initializer exceptions."
  ([plans root phase] (expand plans root phase #{}))
  ([plans root phase already-initialized]
   (when-not (set? already-initialized)
     (fail "Initialization guards must be a set" {:initialized already-initialized}))
   (letfn [(visit [{:keys [initialized] :as state} module phase]
             (when-not (contains? #{:all :runtime :comptime} phase)
               (fail "Unknown module initialization phase" {:module module :phase phase}))
             (let [plan (get plans module)]
               (when-not plan
                 (fail "Missing producer module initialization plan" {:module module :phase phase}))
               (when (and (not (:moduleSystem plan)) (not= :all phase))
                 (fail "Classic Lean module has no split initialization entry"
                       {:module module :phase phase}))
               (if (contains? initialized [module phase]) state
                 (let [state (update state :initialized conj [module phase])
                       imports (:imports plan)
                       state (reduce (fn [state {:keys [module meta]}]
                                       (if (or (= :all phase) (= (boolean meta) (= :comptime phase)))
                                         (visit state module (if (or (= :all phase) (not meta)) phase :runtime))
                                         state)) state imports)]
                   (if (and (:moduleSystem plan) (= :all phase))
                     (visit (visit state module :runtime) module :comptime)
                     (reduce (fn [state {:keys [action meta]}]
                               (if (or (= :all phase) (= (boolean meta) (= :comptime phase)))
                                 (update state :actions conj {:module module :phase phase
                                                            :action action :meta (boolean meta)})
                                 state)) state (:actions plan)))))))]
     (visit {:actions [] :initialized already-initialized} root phase))))
