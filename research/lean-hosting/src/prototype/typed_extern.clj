(ns prototype.typed-extern
  "Optional Nat/String host-value adapters for explicit raw extern bindings.
   Host functions receive immutable decoded values only. Input ownership follows
   the declared ABI; successful results are independently encoded, never Ref
   transfers. Exceptions retain diagnostic ownership packets without cleanup."
  (:refer-clojure :exclude [binding])
  (:require [prototype.interop-codec :as codec]
            [prototype.machine :as m]))

(def ^:private object-types #{"object" "tobject" "tagged"})
(def ^:private value-codecs #{:nat :string})
(defn- fail [message data] (throw (ex-info message data)))

(defn- specification! [{:keys [signature arguments result] :as specification}]
  (when-not (and (map? specification)
                 (= #{:signature :arguments :result :fn} (set (keys specification)))
                 (fn? (:fn specification))
                 (map? signature) (= #{:params :return-type} (set (keys signature)))
                 (vector? (:params signature)) (vector? arguments)
                 (= (count arguments) (count (:params signature)))
                 (contains? object-types (:return-type signature))
                 (contains? value-codecs result))
    (fail "Typed extern requires exact boxed ABI, explicit Nat/String codecs and a host function" {}))
  (doseq [[index parameter argument] (map vector (range) (:params signature) arguments)]
    (when-not (and (map? parameter) (= #{:ty :borrow} (set (keys parameter)))
                   (contains? object-types (:ty parameter)) (boolean? (:borrow parameter))
                   (map? argument) (= #{:codec :ownership} (set (keys argument)))
                   (contains? value-codecs (:codec argument))
                   (= (if (:borrow parameter) :borrowed :owned) (:ownership argument)))
      (fail "Typed extern codec/ownership must match each explicit boxed ABI parameter" {:argument-index index})))
  specification)

(defn- owned-inputs! [world arguments values]
  ;; Count occurrences, not unique Refs. Two owned aliases transfer two owners.
  ;; Persistent/native values have no local RC owner to discharge.
  (doseq [[value owners] (frequencies
                         (keep (fn [[argument value]]
                                 (when (and (= :owned (:ownership argument)) (m/ref? value)) value))
                               (map vector arguments values)))
          :when (not (m/native-reference? world value))]
    (let [rc (:rc (m/node world value))]
      (when-not (and (integer? rc) (or (zero? rc) (<= owners rc)))
        (fail "Typed extern has insufficient owned input occurrences"
              {:value value :owners owners :rc rc}))))
  true)

(defn binding
  "Build a raw binding from exactly
   {:signature {:params [{:ty \"object\" :borrow false} ...] :return-type \"object\"}
    :arguments [{:codec :nat|:string :ownership :owned|:borrowed} ...]
    :result :nat|:string :fn trusted-clojure-function}.

   Signature types/borrow flags are explicit, never inferred. Raw lowering later
   checks the actual Lean extern against this exact ABI. Only boxed object types
   and Nat/String values are supported; no IO/world/Ref/closure/byte adapters.
   The host function receives decoded values by positional application, without
   the raw callback context, world, or guest references. Encoding may share
   immutable host values, but never returns a borrowed/owned input Ref as result.

   Decode borrows inputs. Encode the host result BEFORE consuming owned input
   occurrences once each. Borrowed positions cause no decrement of their own;
   an owned alias may release the same header. Publish scoped raw
   checkpoints after world changes. On any failure, keep exact entry/latest world,
   per-input owner stages, owned encoded result if any, and original cause. No
   finally-drop, implicit guest IO error conversion, rollback or effect retry."
  [specification]
  (let [{:keys [signature arguments result]} (specification! specification)
        invoke-host (:fn specification)]
    {:signature signature
     :handler
     (fn [context world values]
       (let [progress (volatile! world) phase (volatile! :entry)
             owners (volatile! [])
             result-owner (volatile! nil)
             publish! (fn [next-world]
                        (vreset! progress next-world)
                        ((:checkpoint! context) next-world))]
         (try
           (when-not (and (map? context) (fn? (:checkpoint! context))
                          (= signature (:signature context))
                          (vector? values) (= (count arguments) (count values)))
             (fail "Typed extern requires its matching scoped raw callback and exact arity" {}))
           (vreset! owners (mapv (fn [index argument value]
                                  {:index index :value value :ownership (:ownership argument)
                                   :state (:ownership argument)})
                                (range) arguments values))
           ;; Validate synchronous scope before decoding or invoking user code.
           (publish! world)
           (vreset! phase :validate-inputs)
           (owned-inputs! world arguments values)
           (vreset! phase :decode-inputs)
           (let [decoded (mapv (fn [argument value] (codec/decode-boxed world (:codec argument) value))
                               arguments values)
                 _ (vreset! phase :host-call)
                 host-result (apply invoke-host decoded)
                 _ (vreset! phase :encode-result)
                 [next-world encoded] (codec/encode-boxed @progress result host-result)]
             ;; Record the result owner before publishing/consuming anything else.
             (vreset! result-owner {:value encoded :state :owned})
             (publish! next-world)
             (vreset! phase :release-inputs)
             (doseq [[index argument value] (map vector (range) arguments values)
                     :when (= :owned (:ownership argument))]
               (let [next-world (m/release @progress value 1)]
                 (vreset! progress next-world)
                 (vswap! owners assoc-in [index :state] :released)
                 (publish! next-world)))
             (vreset! phase :return-result)
             [@progress encoded])
           (catch Throwable cause
             ;; The raw scope supplies the canonical matching :checkpoint-session.
             ;; Do not invent a session or overwrite a newer child checkpoint.
             (throw (ex-info (or (.getMessage cause) "Typed host extern failed")
                       (merge (ex-data cause)
                              {:typed-extern-entry {:world world :arguments values :signature signature}
                               :typed-extern-checkpoint @progress
                               :typed-extern-input-owners @owners
                               :typed-extern-result-owner @result-owner
                               :typed-extern-phase @phase
                               :typed-extern-terminal? true}) cause))))))}))
