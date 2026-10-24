(ns prototype.typed-eio
  "Synchronous String → EIO String String host adapters for the explicit
   Lean 4.33.1 ABI. A controller keeps effect permission outside persistent
   Worlds; guest helpers construct the actual EIO envelopes."
  (:require [prototype.binding-dependencies :as dependencies]
            [prototype.interop-codec :as codec]
            [prototype.machine :as m]))

(def signature
  {:params [{:ty "object" :borrow false} {:ty "void" :borrow false}]
   :return-type "object"})
(defn- fail [message data] (throw (ex-info message data)))

(defn- specification! [{:keys [builders] :as spec}]
  (when-not (and (map? spec) (= #{:signature :builders :fn} (set (keys spec)))
                 (= signature (:signature spec)) (fn? (:fn spec))
                 (map? builders) (= #{:ok :error} (set (keys builders))))
    (fail "Typed EIO requires the explicit String/world ABI, two guest builders and a host function" {}))
  (dependencies/validate-roots [(:ok builders) (:error builders)])
  (when (= (:ok builders) (:error builders))
    (fail "Typed EIO success and error builders must be distinct" {}))
  spec)

(defn- input-owner! [world value]
  (when (and (m/ref? value) (not (m/native-reference? world value)))
    (let [rc (:rc (m/node world value))]
      (when-not (and (integer? rc) (<= 0 rc))
        (fail "Typed EIO input has no valid owned occurrence" {})))))

(defn- outcome! [value]
  (when-not (and (map? value) (= 1 (count value))
                 (or (= #{:ok} (set (keys value))) (= #{:error} (set (keys value)))))
    (fail "Typed EIO host result must be exactly {:ok String} or {:error String}" {}))
  (first value))

(defn- builders! [world builders]
  ;; Initial profile deliberately accepts only these exact locally emitted
  ;; allocation helpers. Reject absent/wrong/reentrant builders before effects.
  ;; Independent resident admission still owns identity/provenance protection.
  (doseq [[outcome name] builders]
    (let [function (get-in world [:functions name])
          body [:let 3 [:ctor (if (= :ok outcome) 0 1) [[:var 1]]]
                [:return [:var 3]]]]
      (when-not (and (= {:params [1 2] :body body} function)
                     (= ["object" "void"] (:runtime-param-types (meta function))))
        (fail "Typed EIO requires the exact emitted allocation helper profile" {:outcome outcome})))))

(defn- envelope! [world result outcome text]
  ;; Shape witnessed by the actual pinned success/failure builder export.
  ;; Reading borrows; the one-field envelope retains its transferred owner.
  (when-not (m/ref? result) (fail "Typed EIO builder returned no result constructor" {}))
  (let [{:keys [kind tag fields layout scalar-bytes]} (m/node world result)]
    (when-not (and (= :ctor kind) (= (if (= :ok outcome) 0 1) tag)
                   (vector? fields) (= 1 (count fields))
                   (or (nil? layout) (= {:objects 1 :usize 0 :ssize 0} layout))
                   (empty? scalar-bytes)
                   (= text (codec/decode-boxed world :string (first fields))))
      (fail "Typed EIO guest builder returned an invalid outcome envelope" {})))
  result)

(defn controller
  "Return {:binding raw-binding :invoke! scoped-invocation}.

   Specification is exactly {:signature signature
    :builders {:ok success-name :error failure-name} :fn host-function}.
   Both helpers must be independently authenticated, protected guest functions
   with the exact simple allocation bodies emitted for EIOResultBuilders and
   the (owned String, erased world) → EIO String String ABI.
   This factory does not authenticate arbitrary helper code from a name.

   Install :binding as an explicitly admitted application extern before prefix
   preparation. Call (:invoke! controller) with a finite maximum callback count
   and a zero-argument thunk performing the public Project.invoke-io operation.
   No scope exists during compilation. Permission is same-thread, nonreentrant,
   and removed even when the thunk fails. Different calls cannot reuse it.

   The service receives only an immutable String and returns exactly {:ok text}
   or {:error text}. A declared error is a normal Lean EIO result. JVM exceptions
   remain failures with their original cause and canonical raw checkpoints.
   Helpers consume the newly encoded payload; this adapter consumes the original
   input only after envelope validation. Failure retains explicit owner stages;
   no cleanup, retry or rollback occurs here. External effects are not forked."
  [specification]
  (let [{:keys [builders] invoke-host :fn} (specification! specification)
        scope (ThreadLocal.)
        claim! (fn []
                 (let [permit (.get scope)]
                   (when-not (and permit (identical? (Thread/currentThread) (:thread permit))
                                  (pos? @(:remaining permit)) (not @(:inside-host permit))
                                  (not @(:failed permit)))
                     (fail "Typed EIO callback has no active nonreentrant invocation permission" {}))
                   (vswap! (:remaining permit) dec)
                   (vreset! (:inside-host permit) true)
                   permit))
        handler
        (fn [context world values]
          (let [progress (volatile! world) phase (volatile! :entry)
                input-state (volatile! :owned) payload-owner (volatile! nil)
                result-owner (volatile! nil) claimed-permit (volatile! nil)
                publish! (fn [next-world]
                           (vreset! progress next-world)
                           ((:checkpoint! context) next-world))]
            (try
              (when-not (and (map? context) (fn? (:checkpoint! context)) (fn? (:invoke context))
                             (= signature (:signature context))
                             (vector? values) (= 2 (count values)) (= m/erased (second values)))
                (fail "Typed EIO requires its matching raw scope and exact erased world ABI" {}))
              (publish! world)
              (vreset! phase :validate-builders)
              (builders! world builders)
              (vreset! phase :decode-input)
              (input-owner! world (first values))
              (let [text (codec/decode-boxed world :string (first values))
                    _ (vreset! phase :claim-permission)
                    permit (claim!)
                    _ (vreset! claimed-permit permit)
                    _ (vreset! phase :host-call)
                    host-result (invoke-host text)
                    _ (vreset! phase :encode-outcome)
                    [outcome output] (outcome! host-result)
                    [encoded-world payload] (codec/encode-boxed @progress :string output)]
                (vreset! payload-owner {:value payload :state :owned})
                (publish! encoded-world)
                (vreset! phase :build-result)
                (vswap! payload-owner assoc :state :in-helper)
                (let [[built-world result] ((:invoke context) @progress (get builders outcome)
                                            [payload m/erased])]
                  (vreset! payload-owner {:value payload :state :transferred})
                  (vreset! result-owner {:value result :state :owned})
                  (publish! built-world)
                  (vreset! phase :validate-envelope)
                  (envelope! @progress result outcome output)
                  (vreset! phase :release-input)
                  (let [next-world (m/release @progress (first values) 1)]
                    (vreset! progress next-world)
                    (vreset! input-state :released)
                    (publish! next-world))
                  (vreset! phase :return-result)
                  [@progress result]))
              (catch Throwable cause
                (when-let [permit @claimed-permit]
                  (vreset! (:failed permit) true))
                ;; The outer raw scope owns :checkpoint/:checkpoint-session.
                ;; A helper may have progressed beyond our last publication;
                ;; do not replace its canonical packet with our older snapshot.
                (throw (ex-info (or (.getMessage cause) "Typed EIO callback failed")
                         (merge (ex-data cause)
                                {:typed-eio-entry {:world world :arguments values :signature signature}
                                 :typed-eio-input-state @input-state
                                 :typed-eio-payload-owner @payload-owner
                                 :typed-eio-result-owner @result-owner
                                 :typed-eio-phase @phase :typed-eio-terminal? true}) cause)))
              (finally
                (when-let [permit @claimed-permit]
                  (vreset! (:inside-host permit) false))))))
        raw-binding {:signature signature :handler handler
                     :guest-helper-roots [(:ok builders) (:error builders)]}]
    {:binding raw-binding
     :invoke!
     (fn [maximum-calls thunk]
       (when-not (and (integer? maximum-calls) (<= 1 maximum-calls 1024) (fn? thunk))
         (fail "Typed EIO invocation requires a finite callback allowance and a thunk" {}))
       (when (.get scope) (fail "Typed EIO invocation scopes cannot be nested" {}))
       (let [permit {:thread (Thread/currentThread) :remaining (volatile! maximum-calls)
                     :failed (volatile! false)
                     :inside-host (volatile! false)}]
         (.set scope permit)
         (try (thunk) (finally (.remove scope)))))}))
