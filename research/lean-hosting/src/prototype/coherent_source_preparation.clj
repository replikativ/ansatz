(ns prototype.coherent-source-preparation
  "Definitions-only explicit source-import code preparation. Cwd experiments/lean-ir.
   Optimized consumer: original producer artifacts are authenticated by exact pins.
   This file uses globals-consumer-factory; the legacy factory must remain unloaded.
   Wrappers absent from the lazy original closure are independently linked additions.
   Preparation is host-only; explicit check/admission are separate owned guest
   boundaries. No native producer, initializer replay or source close.
   Borrowed catalogue/Store/lease must outlive this controller and every borrower."
  (:require [clojure.data.json :as json]
            [clojure.string :as str]
            [prototype.checkpoint-wire :as wire]
            [prototype.machine :as m]
            [prototype.module-store :as modules]
            [prototype.import-ir :as ir]
            [prototype.declaration-store :as declarations]
            [prototype.runtime-abi :as abi]
            [prototype.raw-interop :as raw]
            [prototype.eval-const :as eval]
            [prototype.source-module :as source-module]
            [prototype.source-import :as source-import]
            [prototype.module-import :as module-import]
            [prototype.guest-encoding :as encoding]
            [prototype.frontend :as frontend]
            [prototype.globals-consumer-factory :as factory]
            [prototype.resident-init-prefix :as prefix]
            [prototype.source-inductive-preparation :as ordinary]
            [prototype.cases-on-preparation :as cases]
            [prototype.compact-import-check :as compact]
            [prototype.full-init-admission :as full-admission]
            [prototype.coherent-stage-guards :as guards]
            [prototype.preparation :as preparation]
            [prototype.runtime-string :as runtime-string])
  (:import [java.io StringReader]
           [ansatz.kernel Env]))

(def profile-id "ansatz-coherent-native-init-source-graph-preparation/1")
(def file-witness-target
  ["str" ["str" ["anonymous"] "RuntimeCompileShim"] "exportEvalConstWitness"])
(def pure-value-target
  ["str" ["str" ["str" ["anonymous"] "SourceModuleImport"] "finalizeClassic"] "_boxed_const_1"])
(def controller-resource "prototype/coherent_source_preparation.clj")
(def controller-entrypoints ["prototype.coherent-source-preparation/prepare-bootstrap-support"
                             "prototype.coherent-source-preparation/check-restored!"
                             "prototype.coherent-source-preparation/prepare!"
                             "prototype.coherent-source-preparation/validate-approved-composition!"
                             "prototype.coherent-source-preparation/assert-initialization-preserved!"
                             "prototype.coherent-source-preparation/validate-prefix-native-bindings!"])
(def admitted-controller-entrypoints
  (mapv #(case %
           "prototype.coherent-source-preparation/check-restored!" "prototype.coherent-source-preparation/admit-restored!"
           "prototype.coherent-source-preparation/prepare!" "prototype.coherent-source-preparation/prepare-admitted!"
           %) controller-entrypoints))

(def helper-row-counts {:graph 247 :export 73 :import 56 :visibility 3 :old-import 43})
(def publication-abi
  {:params [{:ty "object" :borrow false} {:ty "tobject" :borrow true} {:ty "object" :borrow true}]
   :return-type "object"})
(def encoding-abi
  {:params (vec (repeat 4 {:ty "object" :borrow false})) :return-type "object"})
(def eio-abi
  {:params [{:ty "object" :borrow false} {:ty "void" :borrow false}] :return-type "object"})

(def approved-relinks
  (mapv (fn [part]
          (reduce (fn [prefix segment]
                    (if (integer? segment) ["num" prefix (str segment)]
                      ["str" prefix segment]))
                  ["anonymous"] ["_private" "Lean" "Environment" 0 "Lean" part]))
        ["exportIREntries" "getIRExtraConstNames"]))
(def approved-binding-replacements
  #{"lean_compacted_region_read" "lean_compacted_region_free" "lean_eval_const" "lean_elab_add_decl"})

(defonce ^:private state (atom nil))
(defn checkpoint "Borrow entire escrow; never print or serialize this map." [] @state)
(defn- check! [condition message]
  (when-not condition (throw (ex-info message {}))))
(defonce ^:private check-state (atom nil))
(defonce ^:private initialization-baseline (atom nil))
(defn checking-checkpoint
  "Borrow checking/admission escrow and original lease; never serialize this packet." [] @check-state)
(defn- initialization-snapshot [world]
  (select-keys world [:initialized-modules :initializing? :initialization-scope]))
(defn assert-initialization-preserved! [world]
  (check! (and (map? @initialization-baseline)
               (= @initialization-baseline (initialization-snapshot world)))
          "Native initialization state changed during check/admission/preparation")
  {:preserved true :initialized-modules (count (:initialized-modules world))})
(defn- approved-contract [factory]
  (let [{:keys [sha256 contract] :as approved} (factory/coherent-contract factory)
        controller (filter #(= controller-resource (:id %)) (get-in contract [:composition :controllers]))]
    (check! (and (= 1 (count controller))
                 (= (if (:kernel-base-admission contract) admitted-controller-entrypoints controller-entrypoints)
                    (:entrypoints (first controller)))
                 (= sha256 (:consumer-contract-sha256 (factory/descriptor factory))))
            "Actual Factory does not approve this captured controller/entrypoints")
    approved))
(defn check-restored!
  "One fresh strict Init check on the actual Factory's restored precheck branch.
   Keeps the actual compact-check control, latest packet and borrowed resource
   lease in escrow. No certificate reuse, initializer replay, retry or source close."
  [{:keys [factory restored support] :as input}]
  (check! (= #{:factory :restored :support} (set (keys input))) "Exact coherent fresh-check inputs required")
  (let [{:keys [sha256 contract]} (approved-contract factory)
        _ (check! (nil? (:kernel-base-admission contract))
                  "Fresh strict Init check rejects artifact admission mode")
        descriptor (factory/descriptor factory)
        policy (:kernel-policy contract)
        configuration {:trusted-functions (get-in support [:session :functions])
                       :trusted-bindings (get-in support [:session :bindings])
                       :kernel-helpers (:kernel-helpers support)
                       :kernel-policy (assoc policy :fuel (get-in contract [:limits :checker-fuel]))
                       :fuel 500000000}]
    (check! (and (= :restored-precheck (:status restored)) (false? (:strictly-checked? restored))
                 (= sha256 (:consumer-contract-sha256 restored))
                 (= (:producer-preparation descriptor) (:producer-preparation restored))
                 (= factory/kernel-policy policy)) "Actual coherent Factory/precheck identity mismatch")
    (check! (compare-and-set! check-state nil {:phase :checking :entry input :contract-sha256 sha256})
            "Coherent Init check is one-shot; no retry")
    (reset! initialization-baseline (initialization-snapshot (:world restored)))
    (try
      (let [control (compact/prepare (select-keys restored [:world :session :io-result]) configuration)
            _ (swap! check-state assoc :control control)
            checked (compact/check! control)]
        (swap! check-state assoc :phase :returned :result checked)
        (let [world (:world checked) certificate (:certificate checked) env (:environment checked)
              source (:source support) associations (:kernel-environments world)
              node (when (m/ref? env) (m/node world env))]
          (guards/init-facts!
            {:status (:status checked) :constants (count (:constants certificate))
             :projected (count (:projected certificate)) :axioms (set (map str (:axioms certificate)))
             :owned-environment? (and (m/ref? env) node (integer? (:rc node)) (<= 0 (:rc node)))
             :java-env? (instance? Env (:env certificate)) :association-count (count associations)
             :same-association-env? (identical? (:env certificate) (:env (first (vals associations))))
             :projection-source-count (count (:projection-sources certificate))
             :same-projection-source? (identical? source (first (:projection-sources certificate)))
             :single-open-source? (and (= 1 (count (:native-imports world)))
                                      (identical? source (first (:native-imports world))) (false? @(:closed source)))
             :matching-functions? (identical? (:functions world) (get-in checked [:session :functions]))
             :inactive-init? (and (= :done (:status world)) (empty? (:frames world)) (nil? (:host-request world))
                                  (not (:initializing? world)) (not (:initialization-scope world))
                                  (= @initialization-baseline (initialization-snapshot world)))}))
        (assert-initialization-preserved! (:world checked))
        (swap! check-state assoc :phase :checked)
        checked)
      (catch Throwable failure
        (swap! check-state assoc :phase :failed :failure failure)
        (throw failure)))))

(defn admit-restored!
  "Claim this controller's ACTUAL restore/support once for the fixed full Init
   artifact constructor. Retain the original restore/lease, actual result and
   initialization baseline in :admitted escrow. No strict certificate/checking
   flag, source acquisition, finalizer or initializer replay is manufactured."
  [{:keys [factory restored support] :as input}]
  (check! (= #{:factory :restored :support} (set (keys input))) "Exact coherent artifact-admission inputs required")
  (let [{:keys [sha256 contract]} (approved-contract factory)
        _ (check! (= {:basis :trusted-artifact :profile full-admission/supported-profile}
                    (:kernel-base-admission contract))
                  "Artifact Init admission requires the explicit supported contract mode")]
    (check! (compare-and-set! check-state nil {:phase :admitting :entry input :contract-sha256 sha256})
            "Coherent Init admission is one-shot; no retry")
    (reset! initialization-baseline (initialization-snapshot (:world restored)))
    (try
      (let [admitted (full-admission/admit-restored! input)
            _ (swap! check-state assoc :phase :returned :result admitted)
            world (:world admitted) projection (:checked-result admitted) env (:environment admitted)
            source (:source support) associations (:kernel-environments world)
            association (first (vals associations))
            node (when (m/ref? env) (m/node world env))
            provenance (:kernel-provenance projection)]
        (guards/admitted-init-facts!
         {:status (:status admitted) :constants (count (:constants projection))
          :projected (count (:projected projection))
          :axioms (set (map str (get-in projection [:base-assumptions :axioms])))
          :owned-environment? (and (m/ref? env) node (integer? (:rc node)) (<= 0 (:rc node)))
          :java-env? (instance? Env (:env projection)) :association-count (count associations)
          :same-association-env? (identical? (:env projection) (:env association))
          :projection-source-count (count (:projection-sources projection))
          :same-projection-source? (identical? source (first (:projection-sources projection)))
          :single-open-source? (and (= 1 (count (:native-imports world)))
                                   (identical? source (first (:native-imports world))) (false? @(:closed source)))
          :matching-functions? (identical? (:functions world) (get-in admitted [:session :functions]))
          :inactive-init? (and (= :done (:status world)) (empty? (:frames world)) (nil? (:host-request world))
                               (not (:initializing? world)) (not (:initialization-scope world))
                               (= @initialization-baseline (initialization-snapshot world)))
          :base-basis (:base-basis provenance)
          :artifact-admission? (and (:admission admitted)
                                    (identical? (:admission admitted) (:artifact-admission provenance))
                                    (= provenance (:kernel-provenance admitted) (:kernel-provenance association))
                                    (not-any? #(contains? admitted %) [:certificate :strictly-checked?]))})
        (assert-initialization-preserved! world)
        (swap! check-state assoc :phase :admitted)
        admitted)
      (catch Throwable failure
        (swap! check-state assoc :phase :failed :failure failure)
        (throw failure)))))

(defn summary []
  (let [record @state evidence (:evidence record)]
    (merge {:scope profile-id :phase (:phase record)
            :guest-executed false :owner-changes false :source-closed false
            :runnable? (true? (get-in record [:prepared :runnable?]))
            :failure-message (when-let [failure (:failure record)]
                               (let [message (or (.getMessage ^Throwable failure) "")]
                                 (subs message 0 (min 900 (count message)))))}
           evidence)))
(defn- pinned-text [path sha maximum]
  (let [bytes (wire/read-file-bytes path maximum)]
    (check! (= sha (wire/sha256 bytes)) (str "Source-import preparation pin mismatch: " path))
    (wire/utf8-string bytes)))
(def helper-entrypoint-roots
  {"graph" [prefix/graph-assemble-helper]
   "export" [source-module/export-helper]
   "import" (vec (concat (vals source-import/helpers) [source-import/hybrid-assemble-helper pure-value-target]))
   "old-import" (vec (concat (vals source-import/helpers) [pure-value-target]))
   "visibility" [(:is-exporting prefix/reconstruction-helpers)
                  ["str" (:is-exporting prefix/reconstruction-helpers) "_boxed"]]
   "ordinary-publication" [ordinary/generated]
   "ordinary-encoding" [ordinary/encoder encoding/names-helper]
   "eio-builders" [["str" ["str" ["anonymous"] "EIOResultBuilders"] "success"]
                    ["str" ["str" ["anonymous"] "EIOResultBuilders"] "failure"]]
   "cases-on" [cases/helper]})
(defn- lean-name-label [name]
  (loop [name name parts []]
    (if (= ["anonymous"] name) (str/join "." (reverse parts))
      (recur (second name) (conj parts (str (nth name 2)))))))

(defn- helper-spec [contract id]
  (let [found (filter #(= id (:id %)) (get-in contract [:composition :helpers]))]
    (check! (= 1 (count found)) (str "Missing/ambiguous Factory-approved helper: " id))
    (let [roots (get helper-entrypoint-roots id) spec (first found)]
      (check! (and (seq roots)
                   (= (sort (map lean-name-label roots)) (sort (:entrypoints spec))))
              (str "Factory helper entrypoints differ from actual fixed role roots: " id))
      spec)))
(defn- helper-artifact [contract resolve-artifact id]
  (let [{:keys [source-id source-sha256 ir-id ir-sha256]} (helper-spec contract id)
        maximum (get-in contract [:limits :max-helper-bytes])
        source (wire/read-file-bytes (resolve-artifact source-id) maximum)
        ir (wire/read-file-bytes (resolve-artifact ir-id) maximum)]
    (check! (and (= source-sha256 (wire/sha256 source)) (= ir-sha256 (wire/sha256 ir)))
            "Actual helper packet differs from this Factory's approved contract")
    {:source-bytes source :source-sha256 source-sha256 :ir-bytes ir :ir-sha256 ir-sha256
     :max-bytes maximum :max-declarations (get-in contract [:limits :max-helper-declarations])}))
(defn validate-approved-composition!
  "Cheap preflight on this actual Factory. No artifact read, Source or restore."
  [factory]
  (let [{:keys [contract sha256]} (approved-contract factory)
        stages (get-in contract [:composition :stages])
        typed? (boolean (some #{:typed-eio} stages))
        roles (cond-> ["graph" "export" "import" "old-import" "visibility"
                       "ordinary-publication" "ordinary-encoding" "cases-on"]
                typed? (conj "eio-builders"))]
    (guards/profile-stage-prefix! (:profile contract) stages typed?)
    (guards/helper-roles! (get-in contract [:composition :helpers])
                         (into {} (map (fn [role] [role (mapv lean-name-label (get helper-entrypoint-roots role))]) roles)))
    (doseq [role roles] (helper-spec contract role))
    {:consumer-contract-sha256 sha256 :typed-eio? typed? :required-helper-roles roles}))

(defn prepare-bootstrap-support
  "HOST-ONLY independent name-encoder closure over actual authenticated restore.
   No guest call, IO owner transfer, initializer or source close. Returned candidate
   and support must be kept together for check-restored!; old packet is escrow only."
  [factory restored resolve-artifact]
  (let [{:keys [contract sha256]} (approved-contract factory)
        _ (check! (= sha256 (:consumer-contract-sha256 restored)) "Factory/restore composition mismatch")
        artifact (helper-artifact contract resolve-artifact "ordinary-encoding")
        index (ordinary/authenticated-index artifact)
        catalogue (declarations/overlay (:catalogue restored) index)
        _ (doseq [name (keys (:declarations index))] ((:read-declaration catalogue) name))
        original (:trusted-functions restored) bindings (:trusted-bindings restored)
        derived (preparation/complete-functions catalogue original [encoding/names-helper]
                    #(if (contains? bindings (some-> % :ir :extern abi/symbol-for))
                       (raw/lower bindings %) (abi/lower-deferred-catalogue catalogue %)))
        _ (doseq [[name f] original] (check! (identical? f (get derived name)) "Bootstrap support changed original trusted executable"))
        world (:world restored)
        functions (reduce-kv (fn [out name f]
                              (when-let [old (get out name)]
                                (check! (identical? old f) "Bootstrap name encoder collides with actual executable"))
                              (assoc out name f)) (:functions world) derived)
        source (first (:native-imports world))
        _ (check! (and (= 1 (count (:native-imports world))) source) "Original native Source required")
        options (select-keys (:session restored) [:backend :fuel :compile-threshold])
        candidate (assoc restored :world (assoc world :functions functions) :catalogue catalogue
                                  :session (raw/open-functions functions bindings options))
        support {:source source :catalogue catalogue :kernel-helpers factory/helpers
                 :kernel-policy factory/kernel-policy
                 :session (raw/open-functions derived bindings options)}]
    {:candidate candidate :support support
     :profile {:guest-executed false :new-initialization-actions 0 :source-closed false
               :consumer-contract-sha256 sha256}}))

(defn- graph-pins [contract resolve-artifact]
  (into {} (for [[role rows] helper-row-counts
                 :let [{:keys [source-id source-sha256 ir-id ir-sha256]} (helper-spec contract (name role))]]
             [role {:path (resolve-artifact ir-id) :sha256 ir-sha256 :rows rows
                    :source (resolve-artifact source-id) :source-sha256 source-sha256
                    :max-bytes (get-in contract [:limits :max-helper-bytes])
                    :expected-roots (get helper-entrypoint-roots (name role))}])))
(defn- preparation-inputs [factory resolve-artifact]
  (let [{:keys [contract sha256]} (approved-contract factory)
        stages (get-in contract [:composition :stages])
        typed? (boolean (some #{:typed-eio} stages))
        expected (cond-> [:fresh-init :graph-helpers :panic :ordinary-helpers]
                   typed? (conj :typed-eio))
        _ (guards/profile-stage-prefix! (:profile contract) stages typed?)
        ordinary {:publication (assoc (helper-artifact contract resolve-artifact "ordinary-publication")
                                      :expected-root-abi publication-abi)
                  :encoding (assoc (helper-artifact contract resolve-artifact "ordinary-encoding")
                                   :expected-root-abi encoding-abi)}
        eio (when typed? (assoc (helper-artifact contract resolve-artifact "eio-builders")
                               :expected-builder-abis {:ok eio-abi :error eio-abi}))
        redirect (first (get-in contract [:composition :redirects]))
        _ (check! (and (= cases/helper (:target redirect))
                       (= cases/original-row-sha256 (:row-sha256 redirect)))
                  "Factory construction redirect differs from actual preparation target")
        row (wire/read-file-bytes (resolve-artifact (str "cas/" (:row-sha256 redirect))) 65536)
        _ (check! (= (:row-sha256 redirect) (wire/sha256 row)) "Original casesOn CAS row differs from actual Factory contract")]
    {:contract-sha256 sha256 :contract contract :approved-pins (graph-pins contract resolve-artifact)
     :ordinary-artifacts ordinary :eio-builder-artifact eio
     :cases-artifact (helper-artifact contract resolve-artifact "cases-on") :cases-row-bytes row}))

(defn- authenticated-index [pin]
  (let [text (pinned-text (:path pin) (:sha256 pin) (:max-bytes pin))
        rows (mapv #(json/read-str % :key-fn keyword) (str/split-lines text))
        _ (check! (= (:rows pin) (count rows)) "Pinned helper row count changed")
        _ (when (:source pin) (pinned-text (:source pin) (:source-sha256 pin) (:max-bytes pin)))
        index (ir/index-bundles [(StringReader. text)])]
    (doseq [root (:expected-roots pin)]
      (check! (contains? (:declarations index) root) "Factory-declared role entrypoint absent from actual helper artifact"))
    (check! (and (= 1 (count (:manifests index)))
                 (= (dec (:rows pin)) (count (:declarations index))))
            "Pinned helper manifest/declaration count changed")
    (let [manifest (first (:manifests index))]
      (ir/validate-manifest! manifest)
      (check! (= {:target "x86_64-unknown-linux-gnu" :wordBits 64} (:runtimeProfile manifest))
              "Pinned helper target ABI changed")
      (check! (not (contains? manifest :leanCommit))
              "Helper manifest provenance changed; review explicit profile"))
    index))
(defn- helper-indexes [approved-pins]
  (let [export (authenticated-index (:export approved-pins))
        import (authenticated-index (:import approved-pins))
        visibility (authenticated-index (:visibility approved-pins))
        graph (authenticated-index (:graph approved-pins))
        old (authenticated-index (:old-import approved-pins))
        old-manifest (first (:manifests old)) manifest (first (:manifests import))
        actions (get-in manifest [:initializationPlan :actions])
        expected [{:meta false :action {:kind "value" :name pure-value-target :target pure-value-target}}]]
    (check! (empty? (get-in export [:manifests 0 :initializationPlan :actions]))
            "Export helper gained initialization actions")
    (check! (= old-manifest manifest) "Hybrid helper changed original manifest/init plan")
    (check! (= expected actions) "Hybrid helper must retain exactly its existing UInt32 value action")
    (doseq [[name row] (:declarations old)]
      (check! (= row (get-in import [:declarations name])) "Hybrid helper changed an original declaration"))
    (check! (= 13 (- (count (:declarations import)) (count (:declarations old))))
            "Hybrid helper additions differ from reviewed 13 rows")
    (let [row (get-in import [:declarations pure-value-target])
          f (get-in row [:ir :fdecl])]
      (check! (and (= {:role "value" :initializer nil} (:runtime row))
                   (= [] (:dependencies row)) (= [] (:xs f)) (= "tobject" (:type f))
                   (= ["vdecl" {:idx 1} "uint32" {:lit {:v {:num {:v 0}}}}
                       ["vdecl" {:idx 2} "tobject" {:box {:ty "uint32" :x {:idx 1}}}
                        ["ret" {:var {:id {:idx 2}}}]]]
                      (:body f)))
              "Existing helper value no longer boxes UInt32 zero"))
    (check! (and (= 2 (count (:declarations visibility)))
                     (empty? (get-in visibility [:manifests 0 :initializationPlan :actions]))
                     (= #{(:is-exporting prefix/reconstruction-helpers)
                          ["str" (:is-exporting prefix/reconstruction-helpers) "_boxed"]}
                        (set (keys (:declarations visibility)))))
            "Visibility witness exact closure/actions changed")
    (check! (and (= 246 (count (:declarations graph)))
                 (= 173 (count (filter :sourceLocal (vals (:declarations graph)))))
                 (= [] (get-in graph [:manifests 0 :initializationPlan :actions])))
            "Rooted G1 helper inventory/actions changed")
    {:export export :import import :visibility visibility :graph graph}))

(defn- session-options [session]
  {:backend (:backend session) :compile-threshold (:compile-threshold session)
   :fuel 500000000 :cache (or (get-in session [:program :cache]) (:cache session))})

;; Captured HOST definitions. Deliberately not a new closed runtime namespace.
(def panic-symbol "lean_panic_fn_borrowed")
(def panic-target ["str" ["anonymous"] "panicCore"])
(def panic-signature
  {:params [{:ty "erased" :borrow false} {:ty "tobject" :borrow true} {:ty "object" :borrow false}]
   :return-type "tobject"})

(defn make-panic-controller
  "Explicit bounded HOST diagnostic profile for the exact borrowed panic ABI.
   Sink receives only String including newline and must return nil. Its effects
   and finite budget are externally shared across persistent World forks.
   :return preserves nonfatal default semantics; :terminate reports then raises
   named operation failure instead of aborting/exiting this embedding JVM.
   Native backtrace and guest FS.Stream redirection are NOT emulated."
  [{:keys [policy diagnostic-sink] :as spec}]
  (check! (= #{:policy :diagnostic-sink} (set (keys spec))) "Exact panic policy and diagnostic sink required")
  (let [allowed #{:mode :messages? :backtrace? :max-message-bytes :max-output-bytes :max-events}
        expected (if (= :terminate (:mode policy)) (conj allowed :termination) allowed)]
    (check! (and (map? policy) (= expected (set (keys policy)))
                 (contains? #{:return :terminate} (:mode policy)) (boolean? (:messages? policy))
                 (false? (:backtrace? policy)) (fn? diagnostic-sink)
                 (or (= :return (:mode policy)) (contains? #{:abort :exit} (:termination policy)))
                 (integer? (:max-message-bytes policy)) (<= 1 (:max-message-bytes policy) 65536)
                 (integer? (:max-output-bytes policy)) (<= 0 (:max-output-bytes policy) 1048576)
                 (integer? (:max-events policy)) (<= 1 (:max-events policy) 4096))
            "Unsupported/unbounded explicit panic policy"))
  (let [policy (into {} policy) ledger (atom {:events 0 :bytes 0 :poisoned? false :busy? false})
        active (ThreadLocal.)
        handler
        (fn [context world arguments]
          ;; Reject before acquiring another reservation or owner. The same
          ;; handler remains busy through decoding, sink, release and failure.
          (when (.get active) (throw (ex-info "Reentrant panic diagnostic denied" {:panic-reentrant? true})))
          ;; Claim only while holding the monitor. No user sink/callback is
          ;; called under this lock: cross-thread reentry must fail, not wait
          ;; on a sink which itself is synchronously waiting for that thread.
          (locking ledger
            (when (:busy? @ledger)
              (throw (ex-info "Concurrent/reentrant panic diagnostic denied" {:panic-reentrant? true})))
            (swap! ledger assoc :busy? true))
          (.set active true)
          (let [progress (volatile! world) phase (volatile! :entry) reserved? (volatile! false)
                  owners (volatile! {})
                  publish! (fn [w] (vreset! progress w) ((:checkpoint! context) w) w)]
              (try
                (check! (and (map? context) (fn? (:checkpoint! context))
                             (= panic-symbol (:symbol context)) (= panic-signature (:signature context))
                             (vector? arguments) (= 3 (count arguments)) (= m/erased (first arguments)))
                        "Panic requires its matching raw scope and erased type argument")
                (vreset! owners {:default {:value (nth arguments 1) :state :borrowed}
                                 :message {:value (nth arguments 2) :state :owned}})
                (publish! world)
                (vreset! phase :validate-inputs)
                (let [[_ default message] arguments
                      _ (doseq [value [default message] :when (m/ref? value)]
                          (let [rc (:rc (m/node world value))]
                            ;; rc0 is the existing native/persistent exemption;
                            ;; invalid negative/missing RC must never emit.
                            (check! (and (integer? rc) (not (neg? rc)))
                                    "Panic input has invalid reference count")))
                      text (runtime-string/string-value {:ref? m/ref? :node m/node} world message)
                      _ (check! (<= (count text) (:max-message-bytes policy)) "Panic message exceeds finite bound")
                      [_ bytes] (runtime-string/evaluate {:ref? m/ref? :node m/node} world "lean_string_utf8_byte_size" [message])
                      _ (check! (<= bytes (:max-message-bytes policy)) "Panic UTF8 message exceeds finite bound")
                      output-bytes (if (:messages? policy) (inc bytes) 0)
                      old @ledger]
                  (check! (and (not (:poisoned? old)) (< (:events old) (:max-events policy))
                               (<= output-bytes (- (:max-output-bytes policy) (:bytes old))))
                          "Panic diagnostic budget exhausted or poisoned")
                  ;; Reservation precedes ALL owner changes and external effects.
                  (swap! ledger #(-> % (update :events inc) (update :bytes + output-bytes)))
                  (vreset! reserved? true)
                  (vreset! phase :retain-default)
                  (let [retained (m/retain @progress default 1)]
                    (vreset! owners (assoc @owners :default {:value default :state :owned}))
                    (publish! retained))
                  (vreset! phase :report)
                  (when (:messages? policy)
                    (check! (nil? (diagnostic-sink (str text "\n"))) "Panic diagnostic sink must return nil"))
                  (vreset! phase :reported)
                  (when (= :terminate (:mode policy))
                    ;; Native abort/exit occurs BEFORE lean_panic_fn decrefs msg.
                    ;; Keep both host-held owners and canonical checkpoint.
                    (vreset! phase :terminate)
                    (throw (ex-info "Configured Lean panic termination"
                                    {:type :lean-panic-termination :termination (:termination policy)
                                     :native-exit-code (when (= :exit (:termination policy)) 1)
                                     :host-process-terminated? false})))
                  (vreset! phase :release-message)
                  (let [released (m/release @progress message 1)]
                    (vreset! owners (assoc @owners :message {:value message :state :consumed}))
                    (publish! released))
                  (vreset! phase :return)
                  ;; The additional borrowed-default owner becomes caller-owned.
                  [@progress default])
                (catch Throwable cause
                  (when @reserved? (swap! ledger assoc :poisoned? true))
                  (throw (ex-info "Explicit panic handler failed"
                                  (merge (ex-data cause)
                                         {:checkpoint @progress :panic-entry {:world world :arguments arguments}
                                          :panic-policy policy :panic-phase @phase :panic-owners @owners
                                          :panic-ledger (select-keys @ledger [:events :bytes :poisoned?])
                                          :panic-terminal? true}) cause)))
                (finally
                  (locking ledger (swap! ledger assoc :busy? false))
                  (.remove active)))))]
    {:binding {:signature panic-signature :handler handler :guest-helper-roots []
               :panic-policy policy :panic-profile "explicit-host-diagnostic-panic/1"}
     :summary (fn [] (assoc (select-keys @ledger [:events :bytes :poisoned?]) :policy policy))}))

(defn prepare-panic
  "HOST-ONLY exact panicCore capability upgrade before ordinary/profile sealing.
   Preserve old archived code outside this NEW immutable branch. No diagnostic
   runs here. Any existing imported-function authority is upgraded only when it
   is the SAME independently trusted old function; IR/source provenance is intact."
  [candidate configuration panic-configuration]
  (try
    (let [world (:world candidate) session (:session candidate) support (:support candidate)
          trusted (:trusted-functions configuration) bindings (:trusted-bindings configuration)
          catalogue (:catalogue configuration)
          _ (check! (and (identical? (:functions world) (:functions session))
                         (= :done (:status world)) (empty? (:frames world)) (nil? (:host-request world))
                         (identical? catalogue (:catalogue candidate))
                         (identical? trusted (:trusted-functions candidate))
                         (identical? trusted (get-in support [:session :functions]))
                         (identical? bindings (get-in support [:session :bindings]))
                         (= (set (keys bindings)) (set (keys (:bindings session)))))
                    "Panic upgrade requires coherent independent pre-seal state")
          _ (doseq [packet [candidate configuration] key [:graph-profile :graph-install-options :prefix :context]]
              (check! (not (contains? packet key)) "Panic upgrade must precede graph/prefix sealing"))
          _ (doseq [packet [candidate configuration]]
              (check! (nil? (get-in packet [:frontend-configuration :install-options]))
                      "Panic upgrade cannot replace sealed evaluator state"))
          _ (check! (not (contains? bindings panic-symbol)) "Panic symbol already bound; no implicit replacement")
          _ (doseq [[symbol binding] bindings]
              (check! (identical? binding (get-in session [:bindings symbol])) "Panic upgrade binding identity drift"))
          _ (check! (contains? configuration :panic-original-function)
                    "Independently retained original panic presence is required")
          _ (doseq [[name f] trusted :when (not= name panic-target)]
              (check! (identical? f (get-in world [:functions name])) "Panic upgrade executable identity drift"))
          row (if-let [read! (:read-declaration catalogue)] (read! panic-target)
                    (get-in catalogue [:declarations panic-target]))
          ext (get-in row [:ir :extern])
          _ (check! (and (= panic-target (:name row) (:f ext))
                         (= panic-symbol (abi/symbol-for ext)) (nil? (:redirect row))
                         (= panic-signature {:params (mapv #(select-keys % [:ty :borrow]) (:xs ext))
                                             :return-type (:type ext)}))
                    "Actual catalogued panicCore ABI/name/redirect mismatch")
          old (get trusted panic-target)
          expected-old (second (abi/lower-deferred-catalogue catalogue row))
          _ (check! (and old (get-in old [:deferred-extern :symbol])
                         (= panic-symbol (get-in old [:deferred-extern :symbol]))
                         (wire/same-data? old expected-old)) "Old panicCore is not the exact independently catalogued deferred function")
          actual-old (get-in world [:functions panic-target])
          independent-original (:panic-original-function configuration)
          _ (check! (if independent-original
                      (and (identical? independent-original old) (identical? independent-original actual-old))
                      ;; This ONE named trap may predate the independently
                      ;; derived helper closure. Authenticate its full body and
                      ;; ABI from the independent catalogue; never generalize
                      ;; structural equality to any other executable authority.
                      (and actual-old (wire/same-data? actual-old expected-old)))
                    "Original/independently catalogued panic executable mismatch")
          authorized (get-in world [:eval-const-authorizations :functions panic-target])
          _ (when authorized (check! (identical? actual-old authorized) "Imported panic authority differs from actual authenticated old code"))
          controller (make-panic-controller panic-configuration)
          binding (:binding controller)
          function (second (raw/lower {panic-symbol binding} row))
          functions (assoc (:functions world) panic-target function)
          derived (assoc trusted panic-target function)
          next-bindings (assoc bindings panic-symbol binding)
          next-world (cond-> (assoc world :functions functions)
                       authorized (assoc-in [:eval-const-authorizations :functions panic-target] function))
          next-support (assoc support :session (raw/open-functions derived next-bindings (session-options (:session support))))
          next-candidate (assoc candidate :world next-world :trusted-functions derived :support next-support
                                :session (raw/open-functions functions next-bindings (session-options session)))
          next-configuration (assoc configuration :trusted-functions derived :trusted-bindings next-bindings)]
      {:candidate next-candidate :configuration next-configuration :panic-controller controller
       :profile {:id "explicit-preseal-panic-upgrade/1" :relinked [panic-target] :added-binding [panic-symbol]
                 :policy (get-in controller [:binding :panic-policy]) :guest-executed false
                 :imported-function-authority-updated? (boolean authorized)
                 :original-panic-present? (boolean independent-original)}})
    (catch Throwable cause
      (throw (ex-info "Explicit panic pre-seal upgrade failed"
                      {:panic-preseal-entry candidate :panic-preseal-configuration configuration} cause)))))

(def prefix-routing-symbols #{"lean_compacted_region_read" "lean_compacted_region_free" "lean_eval_const"})
(def prefix-kernel-symbol "lean_elab_add_decl")
(def prefix-init-symbol "lean_run_mod_init_core")
(defn validate-prefix-native-bindings!
  "Validate an independently retained prefix-native registry against ORIGINAL
   native authority and the final installed/trusted registry. This validation
   does not grant authority to a candidate map: resident admission must ALSO
   require identity with the separately retained source-preparation result.
   Original read/free/eval/initializer objects stay unchanged in this registry;
   only independently prepared kernel and explicit panic may differ."
  [original prefix-native installed]
  (check! (and (map? original) (map? prefix-native) (map? installed)
               (not (contains? original panic-symbol))
               (= (conj (set (keys original)) panic-symbol)
                  (set (keys prefix-native)) (set (keys installed))))
          "Prefix native original/derived/installed keysets differ")
  (doseq [symbol (conj prefix-routing-symbols prefix-init-symbol prefix-kernel-symbol)]
    (let [old (get original symbol) next (get prefix-native symbol) actual (get installed symbol)]
      (check! (and old (map? (:signature old)) (fn? (:handler old))
                   (= (:signature old) (:signature next) (:signature actual))
                   (fn? (:handler next)) (fn? (:handler actual)))
              "Prefix native callback absent or ABI drift")))
  (check! (= (:kernel-policy (get original prefix-kernel-symbol))
             (:kernel-policy (get prefix-native prefix-kernel-symbol)))
          "Prefix native kernel policy changed")
  (let [panic (get prefix-native panic-symbol)]
    (check! (and (= panic-signature (:signature panic)) (fn? (:handler panic))
                 (= [] (:guest-helper-roots panic))
                 (= "explicit-host-diagnostic-panic/1" (:panic-profile panic)))
            "Prefix native explicit panic profile differs"))
  (doseq [[symbol binding] prefix-native]
    (when-not (contains? prefix-routing-symbols symbol)
      (check! (identical? binding (get installed symbol)) "Prefix native non-routing capability differs from installed trusted authority"))
    (when-not (contains? #{prefix-kernel-symbol panic-symbol} symbol)
      (check! (identical? binding (get original symbol)) "Prefix native replaced unapproved original capability")))
  (check! (identical? (get original prefix-init-symbol) (get prefix-native prefix-init-symbol)) "Prefix native initializer identity changed")
  (check! (identical? (get original prefix-init-symbol) (get installed prefix-init-symbol))
          "Installed native initializer identity changed")
  prefix-native)

(defn make-prefix-native-bindings
  "Create exactly original native callbacks + prepared kernel + explicit panic.
   EXTENDED is independently retained preseal configuration, not World/session
   data. FINAL is the just-created graph registry. Original routing objects are
   deliberately retained for native prefix reconstruction, not replaced with
   hybrid/source graph callbacks. No Source/Store/lease/owner is acquired."
  [original extended final]
  (check! (and (map? original) (map? extended) (map? final)
               (= (conj (set (keys original)) panic-symbol) (set (keys extended)) (set (keys final))))
          "Independent preseal prefix registry keysets differ")
  (doseq [[symbol old] original :when (not (contains? #{prefix-kernel-symbol
                                                       "lean_compacted_region_read" "lean_compacted_region_free"} symbol))]
    (check! (identical? old (get extended symbol)) "Independent preseal replaced unapproved native capability"))
  (doseq [[symbol binding] extended :when (not= symbol "lean_eval_const")]
    (check! (identical? binding (get final symbol)) "Final registry differs from independently retained preseal callbacks"))
  (let [prefix-native (assoc original prefix-kernel-symbol (get extended prefix-kernel-symbol)
                                     panic-symbol (get extended panic-symbol))]
    (validate-prefix-native-bindings! original prefix-native final)))

(def eio-builder-roots
  {:ok ["str" ["str" ["anonymous"] "EIOResultBuilders"] "success"]
   :error ["str" ["str" ["anonymous"] "EIOResultBuilders"] "failure"]})

(defn extend-eio-builders
  "HOST-ONLY pre-seal branch from independently retained candidate/configuration.
   ARTIFACT carries authenticated bytes/digests and independently inspected
   :expected-builder-abis {:ok full-ABI :error full-ABI}. No service capability,
   scope, guest owner or initialization is created. Seal a NEW graph profile
   from the returned registry before opening a new Context/prefix."
  [candidate configuration artifact]
  (try
    (let [world (:world candidate) session (:session candidate)
          trusted (:trusted-functions configuration) bindings (:trusted-bindings configuration)
          support (:support candidate) catalogue (:catalogue configuration)
          _ (check! (and (= :done (:status world)) (empty? (:frames world)) (nil? (:host-request world))
                         (identical? (:functions world) (:functions session))
                         (identical? catalogue (:catalogue candidate))
                         (identical? trusted (:trusted-functions candidate))
                         (identical? trusted (get-in support [:session :functions]))
                         (identical? bindings (get-in support [:session :bindings]))
                         (= (set (keys bindings)) (set (keys (:bindings session)))))
                    "EIO builders require coherent independent pre-seal preparation")
          _ (doseq [packet [candidate configuration]
                    key [:graph-profile :graph-install-options :prefix :context]]
              (check! (not (contains? packet key)) "EIO helpers must precede graph/prefix sealing"))
          _ (doseq [packet [candidate configuration]]
              (check! (nil? (get-in packet [:frontend-configuration :install-options]))
                      "EIO helpers cannot replace sealed evaluator code"))
          _ (doseq [[symbol binding] bindings]
              (check! (identical? binding (get-in session [:bindings symbol])) "EIO pre-seal binding identity drift"))
          _ (doseq [[name f] trusted]
              (check! (identical? f (get-in world [:functions name])) "EIO pre-seal executable identity drift"))
          index (ordinary/authenticated-index artifact)
          manifest (first (:manifests index))
          _ (check! (and (= 4 (count (:declarations index)))
                         (= ["str" ["anonymous"] "EIOResultBuilders"] (get-in manifest [:initializationPlan :module]))
                         (= #{:ok :error} (set (keys (:expected-builder-abis artifact)))))
                    "Expected actual four-row EIO builder local artifact and independent ABI required")
          overlaid (declarations/overlay catalogue index)
          _ (doseq [name (keys (:declarations index))]
              ((:read-declaration overlaid) name))
          _ (doseq [[role name] eio-builder-roots]
              (let [f (get-in ((:read-declaration overlaid) name) [:ir :fdecl])
                    expected (get-in artifact [:expected-builder-abis role])]
                (check! (and (= name (:f f))
                               (= expected {:params (mapv #(select-keys % [:ty :borrow]) (:xs f))
                                            :return-type (:type f)})
                               (= {:params [{:ty "object" :borrow false} {:ty "void" :borrow false}]
                                   :return-type "object"} expected))
                        "EIO builder full ABI differs from actual native profile")))
          derived (preparation/complete-functions overlaid trusted (vals eio-builder-roots)
                    #(abi/lower-catalogue overlaid %))
          functions (reduce-kv (fn [out name f]
                                (when-let [old (get out name)]
                                  (check! (identical? old f) "EIO helper collides with original code"))
                                (assoc out name f)) (:functions world) derived)
          next-world (assoc world :functions functions)
          closure (eval/validate-executables! next-world derived (vals eio-builder-roots))
          _ (doseq [[_ f] closure]
              (check! (not (or (:deferred-extern f) (:deferred-declaration f) (:raw-extern f)
                               (:runtime-initializer f))) "EIO builder must be pure actual allocation code"))
          _ (doseq [[role name] eio-builder-roots]
              (let [f (get derived name)]
                (check! (and (= {:params [1 2]
                                 :body [:let 3 [:ctor (if (= role :ok) 0 1) [[:var 1]]]
                                        [:return [:var 3]]]} f)
                               (= ["object" "void"] (:runtime-param-types (meta f))))
                        "EIO builder body differs from exact actual native allocation helper")))
          _ (doseq [key [:heap :globals :native-imports :kernel-environments :source-modules
                         :source-regions :eval-const-authorizations :stats]]
              (check! (identical? (get world key) (get next-world key)) "EIO pre-seal mutated guest storage"))
          next-support (assoc support :catalogue overlaid
                              :session (raw/open-functions derived bindings (session-options (:session support))))
          next-candidate (assoc candidate :world next-world :catalogue overlaid :trusted-functions derived
                                :support next-support
                                :session (raw/open-functions functions bindings (session-options session)))
          next-configuration (assoc configuration :catalogue overlaid :trusted-functions derived)]
      {:candidate next-candidate :configuration next-configuration
       :profile {:id "ansatz-host-only-eio-builder-preparation/1" :guest-executed false
                 :service-binding-installed false :new-initialization-actions 0
                 :builder-roots eio-builder-roots :added-functions (- (count derived) (count trusted))}})
    (catch Throwable cause
      (throw (ex-info "EIO builder pre-seal preparation failed"
                      {:eio-preseal-entry candidate :eio-preseal-configuration configuration} cause)))))

(defn- retain-base-projection [prepared basis base projection]
  (cond-> (assoc prepared :kernel-projection projection :base-basis basis)
    (= :strict-fresh basis) (assoc :certificate projection :original-checked base)
    (= :trusted-artifact basis) (assoc :checked-result projection :admission (:admission base)
                                     :kernel-provenance (:kernel-provenance projection)
                                     :original-admitted base)))

(defn- prepare-base!
  [basis base {:keys [factory support resolve-artifact] :as input}]
  (let [artifact? (= :trusted-artifact basis)
        key (if artifact? :admitted :checked)
        expected-phase (if artifact? :admitted :checked)
        {:keys [contract]} (approved-contract factory)]
    (check! (and (= #{:factory key :support :resolve-artifact} (set (keys input)))
                 (fn? resolve-artifact)
                 (identical? factory (get-in @check-state [:entry :factory]))
                 (identical? support (get-in @check-state [:entry :support]))
                 (= expected-phase (:phase @check-state)) (identical? base (:result @check-state))
                 (if artifact?
                   (= {:basis :trusted-artifact :profile full-admission/supported-profile} (:kernel-base-admission contract))
                   (nil? (:kernel-base-admission contract))))
            "Exact actual Factory and this controller's matching Init basis/result/support required"))
  (check! (compare-and-set! state nil {:phase :preparing :entry input})
          "Source-import preparation already claimed; no retry")
  (try
    (let [{:keys [contract-sha256 contract approved-pins ordinary-artifacts eio-builder-artifact
                   cases-artifact cases-row-bytes]} (preparation-inputs factory resolve-artifact)
          panic-configuration {:policy {:mode :return :messages? true :backtrace? false
                                         :max-message-bytes 4096 :max-output-bytes 65536 :max-events 16}
                               :diagnostic-sink (fn [text]
                                                  (check! (string? text) "Bounded panic report must be String")
                                                  (swap! state update :panic-reports (fnil conj []) text) nil)}
          world (:world base) actual (:session base) trusted-session (:session support)
          original (:functions trusted-session) native-bindings (:bindings trusted-session)
          source (:source support) catalogue (:catalogue support)
          projection ((if (= :trusted-artifact basis) :checked-result :certificate) base) helpers (:kernel-helpers support)
          init-before (assert-initialization-preserved! world)
          _ (check! (and (= :ok (:status base)) (instance? Env (:env projection))
                         (= :done (:status world)) (empty? (:frames world)) (nil? (:host-request world))
                         (identical? (:functions world) (:functions actual))
                         (= 1 (count (:native-imports world)))
                         (instance? prototype.module_store.Store source) (false? @(:closed source))
                         (identical? source (first (:native-imports world)))
                         (= 1 (count (:projection-sources projection)))
                         (identical? source (first (:projection-sources projection)))
                         (seq original) (seq (:manifests catalogue)))
                    "Original Init/support/source identity invariant failed")
          _ (check! (empty? (get-in world [:eval-const-authorizations :units]))
                    "Source-import preparation requires original pre-user Init world")
          _ (doseq [[name f] original]
              (check! (identical? f (get-in world [:functions name])) "Original independent executable identity drift"))
          _ (doseq [[symbol binding] native-bindings]
              (check! (identical? binding (get-in actual [:bindings symbol])) "Original host binding identity drift"))
          protected-roots (vec (concat (vals helpers)
                                  [frontend/compile-target frontend/header-target
                                   factory/exporter factory/shared-linear-target file-witness-target]))
          _ (eval/validate-executables! world original protected-roots)
          _ (check! (some (fn [association]
                           (and (identical? (:env projection) (:env association))
                                (if (= :trusted-artifact basis)
                                  (and (identical? (:admission base)
                                                   (get-in association [:kernel-provenance :artifact-admission]))
                                       (= (:kernel-provenance projection) (:kernel-provenance base)
                                          (:kernel-provenance association))
                                       (not (contains? base :certificate)))
                                  (not= :trusted-artifact (get-in association [:kernel-provenance :base-basis])))))
                         (vals (:kernel-environments world)))
                    "Original Init association or basis missing")
          indexes (helper-indexes approved-pins)
          overlaid (-> catalogue (declarations/overlay (:export indexes))
                       (declarations/overlay (:import indexes))
                       (declarations/overlay (:visibility indexes))
                       (declarations/overlay (:graph indexes)) source-module/with-ir-export-aliases)
          ;; Force production reconciliation for EVERY G1 overlap before the
          ;; existing-functions shortcut can skip reading an imported row.
          _ (doseq [[name _] (:declarations (:graph indexes))]
              ((:read-declaration overlaid) name))
          routed (source-import/make-hybrid-bindings native-bindings)
          _ (check! (identical? (get native-bindings "lean_run_mod_init_core")
                               (get routed "lean_run_mod_init_core")) "Native initializer capability replaced")
          lower #(if (contains? routed (some-> % :ir :extern abi/symbol-for))
                   (raw/lower routed %) (abi/lower-deferred-catalogue overlaid %))
          roots (vec (distinct (concat [encoding/names-helper source-module/export-helper
                                              source-import/hybrid-assemble-helper module-import/bulk-helper panic-target]
                                             approved-relinks prefix/source-graph-roots
                                             [["str" (:is-exporting prefix/reconstruction-helpers) "_boxed"]]
                                             (vals source-import/helpers)
                                             (vals module-import/helpers))))
          _ (doseq [name approved-relinks]
              (let [old (find original name) actual-entry (find (:functions world) name)]
                (check! (if old
                          (and actual-entry (identical? (val old) (val actual-entry)))
                          (nil? actual-entry))
                        "Export wrapper must be independently trusted or absent from both registries")))
          derived (ir/load-closure overlaid roots lower
                    {:existing-functions (apply dissoc original approved-relinks)})
          _ (doseq [[name f] original :when (not (some #{name} approved-relinks))]
              (check! (identical? f (get derived name)) "Helper preparation replaced an unapproved function"))
          _ (doseq [name (vals helpers)]
              (check! (identical? (get original name) (get derived name)) "Kernel helper identity changed"))
          changes (reduce-kv (fn [out name f]
                               (if (or (identical? f (get original name))
                                       ;; Preserve the actual named old panic until
                                       ;; prepare-panic authenticates it against
                                       ;; its independently derived exact trap.
                                       (and (= name panic-target) (contains? (:functions world) name)))
                                 out (assoc out name f))) {} derived)
          _ (doseq [[name f] changes :when (not (some #{name} approved-relinks))]
              (check! (or (not (contains? (:functions world) name))
                           (identical? f (get-in world [:functions name])))
                      "New independent helper closure collides with original base code"))
          actual-relinks (filterv #(and (contains? original %)
                                        (not (identical? (get original %) (get derived %))))
                                  approved-relinks)
          added-wrappers (filterv #(not (contains? original %)) approved-relinks)
          _ (doseq [name approved-relinks]
              (check! (contains? derived name) "Reviewed export wrapper closure was not independently linked"))
          functions (reduce-kv assoc (:functions world) changes)
          _ (doseq [[name f] (:functions world) :when (not (some #{name} actual-relinks))]
              (check! (identical? f (get functions name)) "Prepared world changed unrelated original function"))
          prepared-world (assoc world :functions functions)
          _ (doseq [key [:heap :globals :native-imports :kernel-environments
                         :source-modules :source-regions :eval-const-authorizations :stats]]
              (check! (identical? (get world key) (get prepared-world key))
                      "Host preparation changed guest storage/ownership/authority"))
          ;; Extend ordinary kernel helpers BEFORE any graph evaluator closure
          ;; captures its registry/catalogue. Every packet below still borrows
          ;; the original base Environment and Source; no guest call occurs.
          preseal-actual (raw/open-functions functions routed (session-options actual))
          preseal-independent (raw/open-functions derived routed (session-options trusted-session))
          preseal-support (assoc support :catalogue overlaid :session preseal-independent)
          panic-result (prepare-panic
                         {:world prepared-world :session preseal-actual :catalogue overlaid
                          :environment (:environment base) :kernel-projection projection
                          :trusted-functions derived :support preseal-support}
                         {:catalogue overlaid :trusted-functions derived :trusted-bindings routed
                          :kernel-helpers helpers :kernel-policy (:kernel-policy support)
                          :panic-original-function (get original panic-target)}
                         panic-configuration)
          _ (swap! state assoc :panic-preseal panic-result)
          ;; Validate the independently derived closure only AFTER the one
          ;; named panic upgrade has reconciled its original trap identities.
          ;; Every other original executable remains identity-preserved.
          _ (eval/validate-executables! (get-in panic-result [:candidate :world])
                                      (get-in panic-result [:configuration :trusted-functions])
                                      (into protected-roots roots))
          ordinary-result (ordinary/prepare-ordinary (:candidate panic-result) (:configuration panic-result)
                                                     ordinary-artifacts)
          ;; Explicit PRIVATE borrowed pre-seal handoff for independently
          ;; reviewed application-builder preparation. No arbitrary callback or
          ;; candidate metadata becomes executable authority. A separate branch
          ;; must seal its own graph/evaluator profile before Context/prefix use.
          _ (swap! state assoc :ordinary-preseal ordinary-result)
          preseal-result (if eio-builder-artifact
                           (extend-eio-builders (:candidate ordinary-result) (:configuration ordinary-result)
                                               eio-builder-artifact)
                           ordinary-result)
          _ (swap! state assoc :before-cases preseal-result)
          original-row (json/read-str (wire/utf8-string cases-row-bytes) :key-fn keyword)
          cases-configuration (assoc (:configuration preseal-result)
                                     :cases-on-original-row-bytes cases-row-bytes
                                     :cases-on-original-function (get-in preseal-result [:configuration :trusted-functions (:name original-row)]))
          cases-result (cases/prepare (:candidate preseal-result) cases-configuration cases-artifact)
          _ (swap! state assoc :preseal cases-result)
          _ (check! (= (get-in preseal-result [:configuration :kernel-policy])
                       (get-in cases-result [:configuration :kernel-policy]))
                    "casesOn preparation changed inherited post-user kernel policy")
          extended-candidate (:candidate cases-result)
          extended-configuration (:configuration cases-result)
          extended-world (:world extended-candidate)
          extended-functions (:functions extended-world)
          extended-trusted (:trusted-functions extended-configuration)
          extended-catalogue (:catalogue extended-configuration)
          extended-routed (:trusted-bindings extended-configuration)
          extended-helpers (:kernel-helpers extended-configuration)
          extended-support (:support extended-candidate)
          _ (check! (and (identical? extended-trusted (:trusted-functions extended-candidate))
                         (identical? extended-trusted (get-in extended-support [:session :functions]))
                         (identical? extended-routed (get-in extended-support [:session :bindings]))
                         (identical? (get native-bindings "lean_run_mod_init_core")
                                     (get extended-routed "lean_run_mod_init_core")))
                    "Ordinary pre-seal actual/independent preparation identity mismatch")
          init-after (assert-initialization-preserved! extended-world)
          preprofile-inventory {:local-heap-entries (count (:heap extended-world))
                                :world-functions (count (:functions extended-world))
                                :independently-trusted-functions (count extended-trusted)
                                (if (= :trusted-artifact basis) :native-admitted-CIs :native-checked-CIs) (count (:constants projection))
                                :double-baseline-admission-entries
                                (* 2 (reduce + (count (:functions extended-world))
                                             (map #(count (get-in extended-world [:eval-const-authorizations %]))
                                                  [:units :unit-digests :declarations :functions])))}
          _ (check! (and (= 65994 (get preprofile-inventory (if (= :trusted-artifact basis) :native-admitted-CIs :native-checked-CIs)))
                         (<= (:local-heap-entries preprofile-inventory) 20000000)
                         (<= (:double-baseline-admission-entries preprofile-inventory) 1000000))
                    "Actual pre-profile scalar inventory exceeds fixed genuine draft limits")
          profile-result (prefix/prepare-source-graph-profile factory/exporter
                    {:witness factory/shared-linear-target :witness-format :typed-ir
                     :catalogue extended-catalogue :trusted-functions extended-trusted :research-traps? true
                     :lower-extern (:consumer-extern-lower extended-configuration)}
                    {:limits {:max-constants 100000 :name-limits {:max-nodes 256 :max-chars 16384}
                              :max-nodes 250000 :max-edges 2000000 :max-bytes 67108864
                              :max-units 1024 :max-declarations 1000000}
                     :graph-limits {:max-modules 1024 :max-roots 4 :max-edges 64 :max-depth 16
                                    :max-names 200000 :max-name-nodes 256 :max-name-bytes 16384
                                    :max-total-name-bytes 67108864 :max-key-bytes 32768
                                    :max-total-key-bytes 134217728}
                     :host-limits {:max-heap-entries 20000000}})
          binding (:eval-binding profile-result)
          install-options (:install-options profile-result)
          _ (check! (and (map? install-options) (fn? (:authorize-source-import install-options))
                         (fn? (:consumer-extern-lower extended-configuration))
                         (identical? (:consumer-extern-lower extended-configuration) (:lower-extern install-options))
                         (identical? extended-trusted (:trusted-functions install-options))
                         (= factory/shared-linear-target (:witness install-options))
                         (= :typed-ir (:witness-format install-options))
                         (false? (:initialize? install-options)))
                    "Graph profile did not return its fixed typed completed-only installer")
          _ (check! (= (:signature binding) (get-in native-bindings ["lean_eval_const" :signature]))
                    "evalConst binding ABI changed")
          bindings (assoc extended-routed "lean_eval_const" binding)
          _ (check! (= (conj (set (keys native-bindings)) panic-symbol) (set (keys bindings))) "Host binding set/addition differs from the exact panic profile")
          _ (doseq [[symbol old] native-bindings :when (not (contains? approved-binding-replacements symbol))]
              (check! (identical? old (get bindings symbol)) "Unapproved host binding replacement"))
          prefix-native-bindings (make-prefix-native-bindings native-bindings extended-routed bindings)
          session (raw/open-functions extended-functions bindings (session-options (:session extended-candidate)))
          independent-session (raw/open-functions extended-trusted bindings (session-options (:session extended-support)))
          global (get-in world [:globals pure-value-target])
          ready? (= :ready (:status global))
          _ (check! (or (nil? global) ready?)
                    "Helper value has an incomplete prior execution; do not replay")
          _ (when ready?
              (check! (= 0 (m/unbox-value world "uint32" (:value global)))
                      "Existing helper UInt32 value is not zero"))
          missing (if ready? [] [pure-value-target])
          prepared (retain-base-projection {:profile profile-id :consumer-contract-sha256 contract-sha256
                    :actual-factory factory :approved-contract contract
                    :prefix-native-bindings prefix-native-bindings
                    :final-configuration extended-configuration :world extended-world :session session
                    :catalogue extended-catalogue :environment (:environment base)
                    :kernel-projection projection :base-basis basis
                    :support (assoc extended-support :catalogue extended-catalogue :session independent-session)
                    :trusted-functions extended-trusted :original-support support
                    :graph-profile (:profile profile-result) :graph-eval-binding binding
                    :graph-install-options (:install-options profile-result)
                    :runnable? ready? :missing-helper-values missing
                    :frontend-configuration
                    {:install-options (:install-options profile-result)}} basis base projection)
          evidence {:consumer-contract-sha256 contract-sha256 :base-basis basis :cases-on-preparation (:profile cases-result)
                    :panic-preparation (:profile panic-result)
                    :ordinary-preparation (:profile ordinary-result)
                    :eio-builder-preparation (when eio-builder-artifact (:profile preseal-result))
                    :initialization-preservation init-after
                    :preprofile-inventory preprofile-inventory
                    :functions (count extended-functions) :independently-trusted-functions (count extended-trusted)
                    :new-functions (- (count extended-trusted) (count original))
                    :approved-export-wrappers approved-relinks
                    :explicit-relinks actual-relinks :added-export-wrappers added-wrappers
                    :binding-replacements (vec (sort approved-binding-replacements))
                    :binding-additions [panic-symbol]
                    :file-witness factory/shared-linear-target :file-witness-format :typed-ir
                    :helper-value-ready ready? :missing-helper-values missing
                    :new-initialization-actions 0 :existing-value-actions 1
                    :per-call-fuel 500000000 :guest-steps-before (get-in world [:stats :steps])
                    :guest-steps-after (get-in extended-world [:stats :steps])
                    :helper-artifact-pins (mapv #(select-keys (get approved-pins %) [:path :sha256 :source :source-sha256])
                                               [:export :import :old-import :visibility :graph])
                    :provenance-limitation "Legacy graph helper manifests have version/ABI only; actual Factory-approved source/IR pins and captured controller source supply separately reviewed provenance. This is not frontend acceptance."}]
      ;; Escrow before every later scalar observer. Packet contains borrowed owners.
      (swap! state assoc :prepared prepared :evidence evidence :prefix-native-bindings prefix-native-bindings
                        :phase (if ready? :prepared :prepared-missing-helper-values))
      (summary))
    (catch Throwable failure
      (swap! state assoc :phase :failed :failure failure)
      (summary))))


(defn prepare!
  "One-shot host-only preparation from this controller's actual strict :checked
   result. Artifact admission uses prepare-admitted! and never the certificate slot."
  [input]
  (prepare-base! :strict-fresh (:checked input) input))

(defn prepare-admitted!
  "One-shot host-only preparation from this controller's actual :admitted result.
   Exact keys are {:factory :admitted :support :resolve-artifact}; retain actual
   artifact projection/token under explicit fields, with no strict certificate."
  [input]
  (prepare-base! :trusted-artifact (:admitted input) input))

(defn ^:no-doc preparation-projection!
  "Borrow the projection only from this controller's actual prepared escrow and
   private strict/admitted result identity. Actual approved composition selects
   its basis; public prepared flags cannot replace that phase/identity boundary."
  [prepared]
  (let [{:keys [contract]} (approved-contract (:actual-factory prepared))
        artifact? (some? (:kernel-base-admission contract))
        phase (if artifact? :admitted :checked)
        base (get prepared (if artifact? :original-admitted :original-checked))
        projection (get base (if artifact? :checked-result :certificate))
        world (:world prepared) source (get-in prepared [:support :source])]
    (check! (and (identical? prepared (:prepared @state))
                 (= phase (:phase @check-state)) (identical? base (:result @check-state))
                 (identical? (:actual-factory prepared) (get-in @check-state [:entry :factory]))
                 (identical? (:original-support prepared) (get-in @check-state [:entry :support]))
                 (identical? projection (:kernel-projection prepared))
                 (instance? Env (:env projection))
                 (= (:environment base) (:environment prepared))
                 (identical? source (get-in prepared [:original-support :source]))
                 (= 1 (count (:native-imports world)))
                 (identical? source (first (:native-imports world))) (false? @(:closed source))
                 (some (fn [association]
                         (and (identical? (:env projection) (:env association))
                              (if artifact?
                                (= (:kernel-provenance projection) (:kernel-provenance association))
                                (not= :trusted-artifact (get-in association [:kernel-provenance :base-basis])))))
                       (vals (:kernel-environments world)))
                 (if artifact?
                   (and (= {:basis :trusted-artifact :profile full-admission/supported-profile}
                           (:kernel-base-admission contract))
                        (not (contains? prepared :certificate))
                        (identical? projection (:checked-result prepared))
                        (identical? (:admission base) (:admission prepared))
                        (identical? (:admission base)
                                    (get-in projection [:kernel-provenance :artifact-admission])))
                   (and (identical? projection (:certificate prepared))
                        (not= :trusted-artifact (get-in projection [:kernel-provenance :base-basis])))))
            "Helper preparation does not retain this controller's actual Init basis/result")
    projection))
