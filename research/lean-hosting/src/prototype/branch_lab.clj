(ns prototype.branch-lab
  "Bounded Klara/Lean alignment experiment, NOT a resource or sandbox API.
   Trusted fixtures only. Snapshot data carries no settlement authority.
   One family has one adoption right; fork creates competing alternatives,
   not independently spendable copies of that right. No durable recovery."
  (:require [prototype.machine :as m]
            [prototype.mutable :as u]
            [prototype.host-cells-lab :as cells]
            [prototype.lazy-runtime :as lazy]))

(defn runner
  "Reuse this runner across REPL trials. Compiled code is outside snapshots."
  [backend functions]
  (case backend
    :persistent #(m/run (m/resume %1 %2) 10000)
    :mutable #(u/freeze (u/run! (u/resume! (u/thaw %1) %2) 10000))
    :compiled (let [program (lazy/open-program functions)]
                #(u/freeze (lazy/run! program (u/resume! (u/thaw %1) %2) 10000)))))

(defn session
  "TRUSTED provisioning: creates a fresh synthetic family adoption right.
   Creating a second session is a new authority grant, not restoring a branch.
   Pending host requests must not be admitted without classifying the effect."
  ([world basis] (session world basis nil))
  ([world basis store]
   (when-not (#{:suspended :paused :done} (:status world))
     (throw (ex-info "Expected a guest safe point" {})))
   (let [handle (Object.)]
     {:ledger (atom {:family :open
                     :branches {handle {:status :open
                                        :packet (cond-> {:world world :basis basis :outbox []}
                                                  store (assoc :host-store store))}}})
      :initial handle})))

(defn admit-choice
  "Classify the generated fixture's borrowed cell/closure choice request as
   an exposed input suspension. This is the ONLY initial host request admitted;
   pending output or arbitrary IO must not be skipped by session provisioning."
  [world]
  (let [{:keys [symbol arguments dest]} (:host-request world)
        [cell closure] arguments]
    (when-not (and (= :host-call (:status world)) (= :lab/choose symbol)
                   (= 2 (count arguments)) (integer? dest) (<= 0 dest)
                   (m/ref? cell) (m/ref? closure)
                   (= :ref (:kind (m/node world cell)))
                   (= :closure (:kind (m/node world closure)))
                   (= [cell] (:fields (m/node world closure))))
      (throw (ex-info "Unclassified initial host request" {})))
    (-> world (dissoc :host-request) (assoc :status :suspended :resume-var dest))))

(defn- open-entry [state handle]
  (let [entry (get-in state [:branches handle])]
    (when-not (and (= :open (:family state)) (= :open (:status entry)))
      (throw (ex-info "Branch authority is unavailable"
                      {:family (:family state) :branch (:status entry)})))
    entry))

(defn snapshot
  "Inspection only; cannot restore authority in this existing session."
  [{:keys [ledger]} handle]
  (locking ledger (:packet (open-entry @ledger handle))))

(defn- claim! [{:keys [ledger]} handle op]
  (locking ledger
    (let [entry (open-entry @ledger handle)]
      ;; Do not retain terminal snapshots in the authority registry.
      (swap! ledger assoc-in [:branches handle] {:status op})
      (:packet entry))))

(defn- publish! [{:keys [ledger]} handle packets status]
  (locking ledger
    (when-not (= :open (:family @ledger))
      (throw (ex-info "Family settled during execution" {})))
    (let [handles (mapv (fn [_] (Object.)) packets)]
      (swap! ledger
             (fn [s]
               (reduce (fn [s [h packet]]
                         (assoc-in s [:branches h] {:status :open :packet packet}))
                       (assoc-in s [:branches handle] {:status status})
                       (map vector handles packets))))
      handles)))

(defn fork!
  "Consumes parent handle. Both children share data, neither inherits a
   private mutation token. Adoption selects at most one family alternative."
  [session handle]
  (let [packet (claim! session handle :forking)]
    (publish! session handle [packet packet] :forked)))

(defn- transform! [{:keys [ledger] :as session} handle operation]
  (let [packet (claim! session handle :advancing)]
    (try
      (let [packet (operation packet)]
        (first (publish! session handle [packet] :advanced)))
      (catch Throwable cause
        (locking ledger
          (swap! ledger #(-> % (assoc :family :incomplete)
                             (assoc-in [:branches handle] {:status :incomplete}))))
        (throw cause)))))

(defn advance!
  "Reference boundary contract: immutable World at every internal host request.
   Closed descriptors update branch-local cells or defer scalar output."
  [session handle run answer]
  (transform!
   session handle
   (fn [packet]
     (loop [world (run (:world packet) answer) packet packet n 0]
       (if (= :host-call (:status world))
         (let [{:keys [store reply] :as effect}
               (cells/request (:host-store packet) (:host-request world) n)
               packet (cond-> packet
                        store (assoc :host-store store)
                        (contains? effect :intent) (update :outbox conj (:intent effect)))]
           (recur (run world reply) packet (inc n)))
         (assoc packet :world world))))))

(defn scoped-runner
  "Private execution across the CLOSED lab descriptor table. No arbitrary
   handler sees a Machine or a live World. Freeze only at the next exposed
   suspension, pause or completion; forks then use ordinary immutable packets.
   This adapter depends on the experimental Machine control layout."
  [backend functions]
  (if (= backend :persistent)
    ;; The reference path already uses immutable state, so keep its contract.
    (let [run (runner backend functions)]
      (fn [packet answer]
        (loop [world (run (:world packet) answer) packet packet n 0]
          (if (= :host-call (:status world))
            (let [{:keys [store reply] :as effect}
                  (cells/request (:host-store packet) (:host-request world) n)
                  packet (cond-> packet
                           store (assoc :host-store store)
                           (contains? effect :intent) (update :outbox conj (:intent effect)))]
              (recur (run world reply) packet (inc n)))
            (assoc packet :world world)))))
    (let [program (when (= backend :compiled) (lazy/open-program functions))
          _ (when-not (#{:mutable :compiled} backend)
              (throw (ex-info "Unsupported scoped backend" {})))
          run! (if program #(lazy/run! program % 10000) #(u/run! % 10000))]
      (fn [packet answer]
        (let [machine (u/thaw (:world packet))]
          (u/resume! machine answer)
          (loop [packet packet n 0]
            (run! machine)
            (if (= :host-call (aget ^objects (:control machine) 4))
              (let [{:keys [store reply] :as effect}
                    (cells/request (:host-store packet) (aget ^objects (:control machine) 6) n)
                    packet (cond-> packet
                             store (assoc :host-store store)
                             (contains? effect :intent) (update :outbox conj (:intent effect)))]
                (u/resume! machine reply)
                (recur packet (inc n)))
              (assoc packet :world (u/freeze machine)))))))))

(defn advance-scoped! [session handle run answer]
  (transform! session handle #(run % answer)))

(defn discard! [session handle]
  (claim! session handle :discarded)
  nil)

(defn adopt!
  "Claim the single family right BEFORE callbacks. On any exception the
   family stays incomplete; completed receipts remain, and no retry is allowed.
   This offers at-most-once attempts, not transactional or crash-safe IO."
  [{:keys [ledger]} handle emit!]
  (let [packet
        (locking ledger
          (let [packet (:packet (open-entry @ledger handle))]
            (when (some #(#{:advancing :forking} (:status %))
                        (vals (:branches @ledger)))
              (throw (ex-info "A branch operation is still active" {})))
            (when-not (= :done (get-in packet [:world :status]))
              (throw (ex-info "Only completed guests can be adopted" {})))
            ;; Selecting one alternative retires all sibling authorities.
            (reset! ledger {:family :committing :selected handle :completed []})
            packet))]
    (try
      (doseq [intent (:outbox packet)]
        (let [receipt (emit! intent)]
          (swap! ledger update :completed conj {:intent intent :receipt receipt})))
      (swap! ledger assoc :family :adopted)
      packet
      (catch Throwable cause
        (swap! ledger assoc :family :incomplete)
        (throw cause)))))

(defn fixture
  "Handwritten Lean-machine IR: a closure captures the same cell passed to
   its caller. Resume mutates that cell, calls the closure, queues output,
   then returns the observed value. This is not a Lean frontend fixture."
  []
  (let [functions
        {:read {:params [0 1]
                :body [:let 2 [:runtime "lean_st_ref_get"
                               [[:imm m/erased] [:imm m/erased] [:var 0] [:imm m/erased]]]
                       [:return [:var 2]]]}
         :entry {:params [0 1]
                 :body [:suspend 2
                        [:let 5 [:runtime "lean_st_ref_set"
                                 [[:imm m/erased] [:imm m/erased] [:var 0] [:var 2] [:imm m/erased]]]
                         [:call 3 [:closure [:var 1]] [[:imm 0]]
                          [:host :lab/emit [[:var 3]] 4 [:return [:var 3]]]]]]}}
        [world cell] (m/allocate (m/world functions) :ref 253 [0])
        ;; Two real guest owners: direct argument and closure capture.
        world (m/retain world cell 1)
        [world closure] (m/expr world [:closure :read [[:imm cell]]])
        world (assoc world :functions functions)]
    {:world (m/run (m/start world :entry [cell closure]))
     :cell cell :functions functions}))
