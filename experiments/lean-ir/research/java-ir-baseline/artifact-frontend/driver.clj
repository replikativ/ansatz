(ns artifact-declaration-driver-v4
  "Checked declaration driver over one sealed artifact base. No new Run, module
   data, code source, or active-session fork authority is minted here."
  (:require [java-ir-baseline :as j]
            [artifact-declaration-authority-v4 :as authority]
            [artifact-checked-declaration-adapter-v4 :as adapter]))
(defn open-driver [child matched-base finalized-run {:keys [heartbeat-step!] :as options}]
  (when-not (fn? heartbeat-step!) (throw (ex-info "Explicit heartbeat provider required" {})))
  (let [driver (:driver child)
        auth (authority/open-authority driver {:code-receipt (:code-receipt child)
                :finalized-run finalized-run :layout-directory (:layout-directory options)})
        session (adapter/open-session @(:current-ctx driver) (:engine driver)
                  (:configuration child) (:source driver) auth matched-base
                  {:allow-axioms? true :allow-theorems? true :allow-definitions? true
                   :fuel 2000000 :max-declarations 16
                   :projection-limits (fn [] {:max-nodes 100000 :deadline-nanos (+ (System/nanoTime) 10000000000)})})
        begun (atom 0) ticks (atom 0)
        step (fn [s]
               (when (contains? #{:failed :retired} @(:phase session))
                 (throw (ex-info "Terminal artifact adapter" {:phase @(:phase session)})))
               (let [d (:driver s) c @(:current-ctx d) e (:engine d)
                     _ (assert (identical? e (:engine driver)))
                     _ ((:check-source! auth) e (:source driver))
                     _ (swap! ticks inc)
                     request (j/host-request c e)
                     symbol (when request (j/request-value request "symbol"))]
                 (cond
                   (= symbol "lean_io_get_num_heartbeats") (heartbeat-step! s)
                   (or (= :active @(:phase session)) (= symbol "lean_elab_add_decl"))
                   (do
                     (when-not (= :active @(:phase session))
                       (adapter/begin! session request) (swap! begun inc))
                     (let [result (adapter/poll! session)]
                       (when (contains? #{:failed :needs-host} (:status result))
                         (throw (ex-info "Artifact checked adapter boundary" (select-keys result [:status :failure]))))))
                   :else (throw (ex-info "Unsupported frontend runtime boundary" {:phase (j/phase c e) :symbol symbol})))))]
    {:authority auth :adapter session :runtime-step! step :begun begun :ticks ticks}))
