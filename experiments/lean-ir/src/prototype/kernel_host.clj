(ns prototype.kernel-host
  "Experimental strict kernel callback. Guest environments stay guest objects;
   Java checking environments are immutable, snapshot-local anchored projections.
   This adapter covers definitions, theorems, safe opaques, explicit unsafe/partial
   mutual blocks, policy-controlled axioms and the exact compiler-marker bootstrap.
   Cancellation is read through actual guest helpers in one cooperative snapshot.
   Native heartbeat/depth accounting is not emulated."
  (:require [prototype.machine :as m]
            [prototype.binding-dependencies :as dependencies]
            [prototype.native-scalar :as native]
            [prototype.kernel-bridge :as bridge]
            [prototype.kernel-declaration :as declaration]
            [prototype.guest-encoding :as encoding]
            [prototype.kernel-projection-snapshot :as snapshot])
  (:import [ansatz.kernel Env ConstantInfo]))

(def signature
  {:params [{:ty "object" :borrow false} {:ty "usize" :borrow false}
            {:ty "usize" :borrow false} {:ty "tobject" :borrow true}
            {:ty "tobject" :borrow true}]
   :return-type "object"})

(defn- anonymous? [value]
  (or (= 0 value) (and (instance? prototype.machine.Tag value) (= 0 (:tag value)))
      (and (native/native-scalar? value) (zero? (native/payload value)))))

(def control-helpers
  {:cancel-is-set ["str" ["str" ["anonymous"] "KernelControlShim"] "cancellationIsSet"]
   :cancel-result ["str" ["str" ["anonymous"] "KernelControlShim"] "cancelledSingleResult"]})

(defn- cancellation-set? [context world cancel helpers]
  (if (anonymous? cancel) [world false]
    (do
      (when-not (vector? (:cancel-is-set helpers))
        (m/fail "Kernel cancellation requires the guest snapshot helper" {}))
      ;; This helper borrows the Option and reads CancelToken.isSet; neither the
      ;; token's private layout nor its Promise/task internals are duplicated.
      (let [[world result] ((:invoke context) world (:cancel-is-set helpers) [cancel m/erased])
            value (native/nat-value {:ref? m/ref? :node m/node} world result)]
        (when-not (contains? #{0 1} value)
          (m/fail "Invalid guest cancellation Bool" {:value value}))
        [world (= 1 value)]))))

(defn- cancelled-result [context world environment declaration helpers]
  (when-not (vector? (:cancel-result helpers))
    (m/fail "Kernel cancellation requires the guest pre-poll helper" {}))
  (let [[world result] ((:invoke context) world (:cancel-result helpers) [environment declaration])]
    (when (anonymous? result)
      (m/fail "Set-token cancellation pre-poll order unsupported for this declaration kind"
              {:checkpoint world}))
    (let [node (when (m/ref? result) (m/node world result))
          _ (when-not (and (= 1 (:tag node)) (bridge/constructor-layout? node 1 0))
              (m/fail "Malformed guest cancellation pre-poll result" {:checkpoint world :result result}))
          error (first (:fields node))
          error-node (when (m/ref? error) (m/node world error))]
      (when-not (and (= 0 (:tag error-node)) (bridge/constructor-layout? error-node 1 0))
        (m/fail "Cancellation helper must return a real kernel Except.error" {:checkpoint world :result result}))
      [(-> world (m/retain error 1) (m/release result 1) (m/release environment 1)) error])))

(defn- witnessed? [helpers]
  (and (vector? (:constant-map helpers)) (vector? (:quot-init? helpers))))

(defn- release-owned [context world value]
  (if-let [release (::release-owned context)]
    (release world value)
    (m/release world value 1)))

(defn- checked-witness [context world environment helpers java-env]
  (let [[world constants] ((:invoke context) world (:constant-map helpers) [environment])
        _ (when-not (m/ref? constants) (m/fail "Invalid guest checked constant map root" {}))
        _ (m/node world constants)
        [world quot-value] ((:invoke context) world (:quot-init? helpers) [environment])
        quot (native/nat-value {:ref? m/ref? :node m/node} world quot-value)]
    (when-not (contains? #{0 1} quot) (m/fail "Invalid guest quotient initialization flag" {}))
    (when (and java-env (not= (= 1 quot) (.isQuotEnabled ^Env java-env)))
      (m/fail "Guest quotient state differs from checked kernel association" {}))
    [(release-owned context world quot-value) {:constant-map constants :quot-init? (= 1 quot)}]))

(defn- protected-map-association [world witness]
  (when witness
    (some (fn [[id entry]]
            (when (and (= (:constant-map witness) (:constant-map entry))
                       (= (:quot-init? witness) (:quot-init? entry))
                       (m/ref? (:anchor entry)) (= id (:id (:anchor entry)))
                       (instance? Env (:env entry))
                       (= (:quot-init? witness) (.isQuotEnabled ^Env (:env entry))))
              (m/node world (:anchor entry))
              entry))
          (:kernel-environments world))))

(defn- lineage [entry]
  (let [provenance (or (:kernel-provenance entry) {:base-basis :strict-fresh})
        basis (:base-basis provenance)]
    (when-not (contains? #{:strict-fresh :trusted-artifact} basis)
      (m/fail "Unrecognized kernel base provenance" {}))
    (when (and (= :trusted-artifact basis)
               (not (and (:artifact-admission provenance)
                         (map? (:base-assumptions provenance))
                         (vector? (:java-guard-segments entry)))))
      (m/fail "Incomplete artifact kernel lineage" {}))
    (assoc (select-keys entry [:java-guard-segments]) :kernel-provenance provenance)))

(defn ^:no-doc association-provenance
  "Borrow validated live-ledger provenance; legacy entries are strict bases.
   Reading this descriptive value grants no association authority."
  [entry]
  (:kernel-provenance (lineage entry)))

(defn- resolve-association*
  "Borrow ENVIRONMENT and resolve only an existing checked association, or its
   header-only view with the SAME protected constant-map Ref and quotient state.
   CONTEXT must invoke identity-authorized :root/:constant-map/:quot-init? helpers.
   Returns [world borrowed-association-entry-or-nil], preserving base provenance
   and historical Java witnesses without a full base scan. A new view owns one root in the ledger;
   all temporary root/map owners are otherwise released. Never creates an empty
   checker environment, reprojects constants, or admits unchecked declarations."
  [context world environment helpers]
  (let [[world root] ((:invoke context) world (:root helpers) [environment])]
    (when-not (m/ref? root) (m/fail "Invalid guest checked environment root" {}))
    (m/node world root)
    (if-let [entry (get-in world [:kernel-environments (:id root)])]
      ;; An existing conflicting anchor must not fall through to derivation.
      [(release-owned context world root)
       (when (and (= root (:anchor entry)) (instance? Env (:env entry)))
         (merge entry (lineage entry)))]
      (if-not (witnessed? helpers)
        [(release-owned context world root) nil]
        (let [[world witness] (checked-witness context world environment helpers nil)
              match (protected-map-association world witness)
              world (release-owned context world (:constant-map witness))]
          (if match
            ;; The old anchor protects the same immutable map; this new root's
            ;; helper-result owner transfers to the ledger exactly once.
            (let [entry (merge {:anchor root :env (:env match)} (lineage match) witness)]
              [(assoc-in world [:kernel-environments (:id root)] entry) entry])
            [(release-owned context world root) nil]))))))

(defn resolve-association
  "Resolve a positive live association, preserving actual helper progress and
   outstanding owner credits on failure. Does no full-base witness scan."
  [context world environment helpers]
  (let [progress (volatile! world) owners (volatile! [])
        invoke (:invoke context)
        context (assoc context
                  :invoke (fn [world target args]
                            (let [[world value] (invoke world target args)]
                              (vreset! progress world) (vswap! owners conj value)
                              [world value]))
                  ::release-owned
                  (fn [world value]
                    (let [world (m/release world value 1)
                          index (first (keep-indexed #(when (= value %2) %1) @owners))]
                      (vreset! progress world)
                      (when (some? index)
                        (vswap! owners #(into (subvec % 0 index) (subvec % (inc index)))))
                      world)))]
    (try
      (let [[world entry] (resolve-association* context world environment helpers)]
        ;; Any surviving root owner has now transferred into the returned ledger.
        (vreset! progress world) (vreset! owners []) [world entry])
      (catch Throwable cause
        (throw (ex-info (or (.getMessage cause) "Kernel association resolution failed")
                        (merge {:checkpoint @progress} (ex-data cause)
                               {:association-resolution-owners @owners
                                :temporary-owners (into (vec @owners) (:temporary-owners (ex-data cause)))})
                        cause))))))

(defn inherit-checked-association
  "Strict-facing resolver. Artifact-derived associations require the explicit
   admitted path; checked additions do not upgrade their base to strict."
  [context world environment helpers]
  (let [[world entry] (resolve-association context world environment helpers)]
    (when (and entry (not= :strict-fresh (get-in entry [:kernel-provenance :base-basis])))
      (throw (ex-info "Strict association cannot inherit an artifact-admitted base"
                      {:checkpoint world :kernel-association entry})))
    [world (:env entry)]))

(defn- associate-input [context world environment helpers]
  (let [[world root] ((:invoke context) world (:root helpers) [environment])]
    (when-not (m/ref? root) (m/fail "Invalid guest checked environment root" {}))
    (if-let [entry (get-in world [:kernel-environments (:id root)])]
      (do
        (when-not (= root (:anchor entry)) (m/fail "Invalid kernel environment anchor" {}))
        ;; An anchored exact root can safely acquire the optional map witness.
        (let [world (if (and (witnessed? helpers) (not (:constant-map entry)))
                      (let [[world witness] (checked-witness context world environment helpers (:env entry))]
                        (assoc-in world [:kernel-environments (:id root)] (merge entry witness)))
                      world)]
          [(m/release world root 1) (:env entry)
           (merge (get-in world [:kernel-environments (:id root)]) (lineage entry))]))
      (let [[world witness] (if (witnessed? helpers)
                              (checked-witness context world environment helpers nil)
                              [world nil])
            ;; Ref equality is guest pointer identity, not host wrapper identity.
            match (protected-map-association world witness)]
        (if match
          ;; The existing map anchor protects this identical immutable map. Keep
          ;; only the new checked-root owner; drop the temporary map owner.
          (let [world (m/release world (:constant-map witness) 1)]
            (let [entry (merge {:anchor root :env (:env match)} (lineage match) witness)]
              [(assoc-in world [:kernel-environments (:id root)] entry) (:env match) entry]))
          (let [[world empty?] ((:invoke context) world (:empty? helpers) [environment])]
            (when-not (= 1 (native/nat-value {:ref? m/ref? :node m/node} world empty?))
              (m/fail "Guest kernel environment has no verified Java association" {:root root}))
            (when (:quot-init? witness) (m/fail "Empty guest kernel has initialized quotients" {}))
            (let [java-env (Env.)
                  entry (merge {:anchor root :env java-env} (lineage nil) witness)]
              [(assoc-in world [:kernel-environments (:id root)]
                         entry) java-env entry])))))))

(def ^:private fixed-helper-roles
  ;; Exactly the helper roles read by this handler and its association/control
  ;; adapters. Do not infer dependencies from arbitrary unused helper-map values.
  [:root :empty? :definition :axiom :error :compiler-marker :definition-any
   :theorem :opaque :mutual :constant-map :quot-init? :cancel-is-set :cancel-result
   :generated :encode-family :generated-nested])

(defn- publication-progress
  "Retain exact post-check helper outcomes until ledger/result transfer.
   The entry Environment is a diagnostic snapshot, not a retry/cleanup grant."
  [context world environment declaration f]
  (let [progress (volatile! world) owners (volatile! []) stage (volatile! :new-group)
        own! (fn [world value]
               (vreset! progress world) (vswap! owners conj value))
        invoke (:invoke context)
        tracked (assoc context
                  :invoke (fn [world target args]
                            (vreset! stage [:helper target])
                            (let [[world value] (invoke world target args)]
                              (own! world value) [world value]))
                  ::release-owned
                  (fn [world value]
                    (vreset! stage :release-helper-owner)
                    (let [world (m/release world value 1)
                          index (first (keep-indexed #(when (= value %2) %1) @owners))]
                      (vreset! progress world)
                      (when (some? index)
                        (vswap! owners #(into (subvec % 0 index) (subvec % (inc index)))))
                      world)))]
    (try
      (let [result (f tracked own!)]
        ;; Returned Except owner and root/map ledger credits transfer together.
        (vreset! owners []) result)
      (catch Throwable cause
        (let [data (ex-data cause)]
          (throw (ex-info (or (.getMessage cause) "Kernel publication failed")
                          (merge {:checkpoint @progress :kernel-publication-stage @stage} data
                                 {:kernel-publication-entry {:checkpoint world :environment environment
                                                             :declaration declaration}
                                  :kernel-publication-temporary-owners @owners
                                  :temporary-owners (into (vec @owners) (:temporary-owners data))})
                          cause)))))))

(defn make-binding
  "Create the lean_elab_add_decl raw binding. HELPERS contains structured names
   :root, :empty?, :definition, :axiom and :error for KernelBridgeShim functions.
   :compiler-marker is additionally required only with :allow-compiler-markers?.
   Optional :theorem/:opaque/:mutual publication helpers enable those kinds.
   :definition-any enables strict unsafe/partial single definitions and complete
   nonsemantic all metadata; legacy :definition remains safe-only.
   :generated plus :encode-family enable checked safe source inductive generation.
   :allow-nested? plus :generated-nested opt into the bounded unary-container
   source profile; broader nested/unsafe families and lossy provenance fail closed.
   Mutual unsafe/partial blocks require :allow-unsafe? true (default false).
   Safe axioms require :allow-axioms? true; they remain declared assumptions.
   Optional :constant-map AND :quot-init? helpers enable header-only derived views.
   Optional :cancel-is-set and :cancel-result enable guest cancellation snapshot
   reads. None stays supported without helpers. An unset token permits ordinary
   checking; a set token returns the real pre-poll/kernel interrupted result for
   single declarations. Unsupported set-token kinds fail explicitly. Helpers
   borrow all inputs. Guest execution does not interleave during Java checking;
   cancellation activated by external concurrent threads is not modeled here.
   Checker fuel is a host limit, not a claim of native heartbeat equivalence.
   The immutable binding declares its fixed :guest-helper-roots and effective
   :kernel-policy from the SAME snapshots captured by its handler. This enables
   independent resident protection; arbitrary custom callbacks remain trusted."
  [helpers {:keys [allow-axioms? allow-compiler-markers? allow-unsafe? allow-nested? checker-fuel] :or {checker-fuel 1000000}}]
  (when-not (and (or (map? helpers) (instance? java.util.Map helpers)) (<= (count helpers) 64))
    (m/fail "Invalid kernel helper map" {}))
  (when-not (and (integer? checker-fuel) (<= 1 checker-fuel Long/MAX_VALUE))
    (m/fail "Invalid kernel checking fuel" {}))
  (let [helpers (into {} helpers)
        allow-axioms? (boolean allow-axioms?)
        allow-compiler-markers? (boolean allow-compiler-markers?)
        allow-unsafe? (boolean allow-unsafe?)
        allow-nested? (boolean allow-nested?)
        policy {:allow-axioms? allow-axioms? :allow-compiler-markers? allow-compiler-markers?
                :allow-unsafe? allow-unsafe? :allow-nested? allow-nested? :checker-fuel checker-fuel}
        roots (dependencies/validate-roots (into [] (keep helpers) fixed-helper-roles))]
  (doseq [key [:root :empty? :definition :axiom :error]]
    (when-not (vector? (get helpers key)) (m/fail "Missing kernel guest helper" {:helper key})))
  (when (and allow-compiler-markers? (not (vector? (:compiler-marker helpers))))
    (m/fail "Missing kernel guest helper" {:helper :compiler-marker}))
  {:signature signature
   :guest-helper-roots roots
   :kernel-policy policy
   :handler
   (fn [context world [environment heartbeats depth declaration cancel]]
     (when-not (and (integer? heartbeats) (<= 0 heartbeats)
                    (integer? depth) (pos? depth)
                    (or (anonymous? cancel) (m/ref? cancel)))
       (m/fail "Unsupported kernel checking controls" {:heartbeats heartbeats :depth depth :cancel cancel}))
     (let [[world cancelled?] (cancellation-set? context world cancel helpers)]
       (if cancelled? (cancelled-result context world environment declaration helpers)
     (let [[world java-env input-association] (associate-input context world environment helpers)
           tag (cond (m/ref? declaration) (:tag (m/node world declaration))
                     (native/native-scalar? declaration) (native/payload declaration)
                     (instance? prototype.machine.Tag declaration) (:tag declaration)
                     (integer? declaration) declaration)
           admission (try
                       (case tag
                         0 (if (and allow-compiler-markers? (bridge/compiler-marker-declaration? world declaration))
                             {:checked (bridge/admit-compiler-marker world java-env declaration checker-fuel)
                              :publication (:compiler-marker helpers)}
                             (if allow-axioms?
                               {:checked (bridge/admit-axiom world java-env declaration checker-fuel)
                                :publication (:axiom helpers)}
                               (m/fail "Axiom admission disabled by host policy" {})))
                         1 (if-let [publication (:definition-any helpers)]
                             (do (when-not (vector? publication)
                                   (m/fail "Missing kernel guest publication helper" {:helper :definition-any}))
                                 {:checked (declaration/admit world java-env declaration
                                             {:allow-unsafe? allow-unsafe? :checker-fuel checker-fuel})
                                  :publication publication})
                             {:checked (bridge/admit-definition world java-env declaration checker-fuel)
                              :publication (:definition helpers)})
                         (2 3 5)
                         (let [key ({2 :theorem 3 :opaque 5 :mutual} tag)
                               publication (get helpers key)]
                           (when-not (vector? publication)
                             (m/fail "Missing kernel guest publication helper" {:helper key}))
                           {:checked (declaration/admit world java-env declaration
                                      {:allow-unsafe? allow-unsafe? :checker-fuel checker-fuel})
                            :publication publication})
                         6 (do
                             (doseq [key [:generated :encode-family]]
                               (when-not (vector? (get helpers key))
                                 (m/fail "Missing source inductive guest helper" {:helper key})))
                             (let [checked (declaration/generate-inductive world java-env declaration
                                             {:checker-fuel checker-fuel :allow-nested? allow-nested?})
                                   key (if (:nested? checked) :generated-nested :generated)]
                               (when-not (vector? (get helpers key))
                                 (m/fail "Missing source inductive guest helper" {:helper key}))
                               {:checked checked :generated? true :publication (get helpers key)}))
                         (m/fail "Unsupported declaration kind at kernel boundary" {:tag tag}))
                       (catch Exception e {:error (.getMessage e)}))]
       (if (contains? admission :error)
         (let [message (or (:error admission) "Kernel admission failed")
               [world result] ((:invoke context) world (:error helpers) [(str message)])]
           [(m/release world environment 1) result])
         (publication-progress context world environment declaration
          (fn [publication-context own!]
           (let [java-next (get-in admission [:checked :env])
               checked (:checked admission)
               constants (or (seq (:constants checked)) (when-let [ci (:constant checked)] [ci]))
               artifact? (= :trusted-artifact (get-in input-association [:kernel-provenance :base-basis]))
               guarded? (or artifact? (vector? (:java-guard-segments input-association)))
               _ (when guarded?
                   (when-not (and (vector? (:java-guard-segments input-association))
                                  (= (.size ^Env java-next) (+ (.size ^Env java-env) (count constants)))
                                  (every? #(nil? (.lookup ^Env java-env (.name ^ConstantInfo %))) constants))
                     (m/fail "Guarded callback requires the complete new CI group" {})))
               new-witness (when guarded?
                             (snapshot/snapshot-segment
                               (into {} (map (fn [^ConstantInfo ci] [(.name ci) ci])) constants)))
               _ (when new-witness (snapshot/validate-segment java-next new-witness))
               ;; Encoding failures are capability/runtime failures and propagate
               ;; their real checkpoint. They are never converted into a pretend
               ;; clean kernel error after a suspended guest helper failed.
               [world generated] (if (:generated? admission)
                                   (encoding/encode-family world (:invoke context)
                                     (get-in admission [:checked :constants])
                                     {:helper (:encode-family helpers)
                                      :original-expressions (get-in admission [:checked :original-expressions])})
                                   [world nil])
               _ (when generated (own! world generated))
               args (cond-> [environment declaration] generated (conj generated))
               [world result] ((:invoke publication-context) world (:publication admission) args)
               ;; Pinned publication IR borrows the generated CI array. The
               ;; kernel retains inserted CIs; the host still owns this wrapper.
               world (if generated (release-owned publication-context world generated) world)
               _ (when new-witness (snapshot/validate-segment java-next new-witness))
               result-node (m/node world result)]
           (when-not (and (= :ctor (:kind result-node)) (= 1 (:tag result-node)) (= 1 (count (:fields result-node))))
             (m/fail "Post-check guest publication failed" {:result result}))
           (let [guest-next (first (:fields result-node))
                 [world root] ((:invoke publication-context) world (:root helpers) [guest-next])]
             (when-not (m/ref? root) (m/fail "Invalid post-check kernel root" {}))
             (when (contains? (:kernel-environments world) (:id root))
               (m/fail "Post-check reused an anchored kernel environment root" {:root root}))
             (let [[world witness] (if (witnessed? helpers)
                                     (checked-witness publication-context world guest-next helpers java-next)
                                     [world nil])]
               (when new-witness (snapshot/validate-segment java-next new-witness))
               [(assoc-in world [:kernel-environments (:id root)]
                          (merge {:anchor root :env java-next}
                                 (cond-> (lineage input-association)
                                   new-witness (update :java-guard-segments (fnil conj []) new-witness))
                                 witness)) result]))))))))))}))
