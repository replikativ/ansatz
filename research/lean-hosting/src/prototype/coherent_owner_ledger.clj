(ns prototype.coherent-owner-ledger
  "Local campaign cleanup protocol. Records actual returned owners before checks.
   A started/failed destructive operation is terminal: no automatic retry.
   These host records confer no guest ownership or disposal authority.")

(defn- require! [ok message]
  (when-not ok (throw (ex-info message {:coherent-cleanup-protocol true}))))

(defn claim-execution! [state lease checked prepared]
  (let [before @state]
    (require! (and (= :ready (:phase before))
                   (compare-and-set! state before
                     {:phase :opening :projects [] :receipts [] :lease lease
                      :checked-before-adoption checked :prepared-before-adoption prepared
                      :unsafe-partial? true :owner-phase :before-adoption}))
              "Execution campaign is one-shot")))

(defn adopt! [state operation]
  ;; The initial claim is already unsafe before any validation. Once this call
  ;; starts, the earlier Environment snapshot cannot be independently released.
  (swap! state assoc :unsafe-partial? true :owner-phase :adopting)
  (let [context (operation)]
    (swap! state assoc :resident-context context :unsafe-partial? false :owner-phase :adopted)
    context))

(defn operation!
  "Claim one destructive operation, escrow its actual result, then validate.
   A failed invocation OR validation retains the result and blocks all automatic
   cleanup. A completed key returns its recorded result without calling again."
  ([state key invoke] (operation! state key invoke (constantly true)))
  ([state key invoke validate]
   (let [before @state existing (get-in before [:cleanup-operations key])]
     (if (= :completed (:phase existing))
       (:result existing)
       (do
         (require! (and (nil? existing) (not (:unsafe-partial? before))
                        (not (contains? #{:failed :disposed} (:disposal-phase before)))
                        (compare-and-set! state before
                          (-> before
                              (assoc :unsafe-partial? true :active-cleanup key)
                              (assoc-in [:cleanup-operations key] {:phase :started}))))
                   "Destructive owner operation cannot be retried")
         (try
           (let [result (invoke)]
             (swap! state assoc-in [:cleanup-operations key] {:phase :returned :result result})
             (validate result)
             (swap! state #(-> % (assoc :unsafe-partial? false)
                                 (dissoc :active-cleanup)
                                 (assoc-in [:cleanup-operations key] {:phase :completed :result result})))
             result)
           (catch Throwable failure
             (swap! state #(-> %
                               (assoc :unsafe-partial? true :disposal-phase :failed :disposal-failure failure)
                               (assoc-in [:cleanup-operations key :phase] :failed)
                               (assoc-in [:cleanup-operations key :failure] failure)))
             (throw failure))))))))

(defn release-prefix!
  "Record the returned Context before closing it. Never reconstruct that branch
   by replaying release-prefix, including when a close fails afterward."
  ([state role packet release close close-original?]
   (release-prefix! state role packet release close close-original? (fn [_ invoke] (invoke))))
  ([state role packet release close close-original? observe]
   ;; Observe WHOLE ledger operations, after their result has entered escrow.
   ;; A diagnostic failure must never make a destructive invocation retryable.
   (let [released (observe :prefix-release-and-adoption
                    #(operation! state [role :release]
                       (fn [] (release (:context packet) (:prefix packet)))))]
     (observe :released-context-close
       #(operation! state [role :released-context-close] (fn [] (close (:context released)))))
     (when close-original?
       (observe :original-context-close
         #(operation! state [role :original-context-close] (fn [] (close (:context packet))))))
     released)))

(defn begin-disposal! [state]
  (let [before @state]
    (if (= :disposed (:disposal-phase before))
      :already-disposed
      (do
        (require! (and (nil? (:disposal-phase before)) (not (:unsafe-partial? before))
                       (compare-and-set! state before (assoc before :disposal-phase :disposing)))
                  "Cleanup already begun or canonical owners unresolved; lease retained")
        :claimed))))

(defn retire-prefix!
  "Close a NEW prefix branch in one claimed operation, then optionally close the
   original wrapper. RETIRE must return no runnable Context/owned roots. Never
   reconstruct or retry a destructive partial result, including after close fails."
  ([state role packet retire close close-original?]
   (retire-prefix! state role packet retire close close-original? (fn [_ invoke] (invoke))))
  ([state role packet retire close close-original? observe]
   (let [retired (observe :prefix-release-and-close
                   #(operation! state [role :release-and-close]
                      (fn [] (retire (:context packet) (:prefix packet)))
                      (fn [result]
                        (require! (= :closed (:status result)) "Prefix branch did not report closed"))))]
     (when close-original?
       (observe :original-context-close
         #(operation! state [role :original-context-close] (fn [] (close (:context packet))))))
     retired)))

(defn recover!
  "At most one recovery entry. Never retry cleanup begun by the normal path.
   Preserve the first failure; an independent cleanup error is suppressed."
  [state failure dispose]
  (swap! state assoc :phase :failed :failure failure)
  (when (and (nil? (:disposal-phase @state)) (not (:unsafe-partial? @state)))
    (try (dispose)
         (catch Throwable cleanup
           (when-not (identical? failure cleanup) (.addSuppressed ^Throwable failure cleanup)))))
  (throw failure))
