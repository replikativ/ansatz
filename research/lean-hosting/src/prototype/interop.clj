(ns prototype.interop
  "Small-Nat/closure host interop experiment. Host calls materialize guest state;
  reentrant callbacks run in the same guest heap. No arbitrary host-state forks."
  (:refer-clojure :exclude [resolve])
  (:require [prototype.import-ir :as ir]
            [prototype.runtime-abi :as runtime-abi]
            [prototype.interop-codec :as codec]
            [prototype.machine :as m]
            [prototype.mutable :as u]
            [prototype.lazy-runtime :as lazy]
            [prototype.session-compiler-options :as compiler]))

(defn extern-symbol [decl]
  (or (runtime-abi/symbol-for decl)
      (m/fail "Unsupported extern specification" {:extern decl})))

(defn- lower-host [bindings row]
  (if-let [ext (get-in row [:ir :extern])]
    (let [symbol (extern-symbol ext) binding (get bindings symbol)
          params (mapv #(get-in % [:x :idx]) (:xs ext))
          dest (inc (reduce max 0 params))]
      (when-not (and binding (= (count params) (count (:arguments binding)))
                     (= :nat (:result binding)) (fn? (:fn binding)))
        (m/fail "Missing or incompatible host binding" {:symbol symbol :params (:xs ext)}))
      (when-not (and (contains? #{"object" "tobject" "tagged"} (:type ext))
                     (every? true? (map (fn [kind param]
                                         (case kind
                                           :nat (contains? #{"object" "tobject" "tagged"} (:ty param))
                                           :closure (contains? #{"object" "tobject"} (:ty param))
                                           false)) (:arguments binding) (:xs ext))))
        (m/fail "Host adapter is incompatible with runtime types" {:symbol symbol}))
      (doseq [ty (cons (:type ext) (map :ty (:xs ext)))] (ir/type! ty))
      [(:f ext) {:params params :extern {:symbol symbol :params (:xs ext)}
                :body [:host symbol (mapv #(vector :var %) params) dest [:return [:var dest]]]}])
    (ir/lower-declaration row)))

(defn lower [bindings row]
  (let [ext (get-in row [:ir :extern])]
    (if (and ext (or (:redirect row) (runtime-abi/supported? ext)) (not (contains? bindings (extern-symbol ext))))
      (runtime-abi/lower row)
      (lower-host bindings row))))

(defn open-functions
  ([functions bindings backend cache] (open-functions functions bindings backend cache {}))
  ([functions bindings backend cache {:keys [compiler-options] :as options}]
   (when-not (contains? #{:reference :mutable :jvm} backend) (m/fail "Unknown backend" {:backend backend}))
   (let [selection (when (contains? options :compiler-options) (compiler/validate functions compiler-options))
         signatures (reduce (fn [signatures [_ f]]
                              (if-let [{:keys [symbol params]} (:extern f)]
                                (let [shape (mapv #(select-keys % [:ty :borrow]) params)]
                                  (when-let [old (get signatures symbol)]
                                    (when-not (= shape (mapv #(select-keys % [:ty :borrow]) old))
                                      (m/fail "Incompatible declarations for host symbol" {:symbol symbol})))
                                  (assoc signatures symbol params)) signatures)) {} functions)]
     (cond-> {:functions functions :bindings bindings :signatures signatures :backend backend
              :program (when (= :jvm backend) (lazy/open-program functions selection cache)) :fuel 1000000}
       (contains? options :compiler-options) (assoc :compiler-options selection)))))

(defn open-session
  ([catalogue roots bindings] (open-session catalogue roots bindings :jvm))
  ([catalogue roots bindings backend]
   (open-session catalogue roots bindings backend (lazy/code-cache)))
  ([catalogue roots bindings backend cache]
   (open-session catalogue roots bindings backend cache {}))
  ([catalogue roots bindings backend cache options]
   (open-functions (ir/load-closure catalogue roots #(lower bindings %)) bindings backend cache options)))

(defn resolve [session name]
  (if (vector? name)
    (if (contains? (:functions session) name) name (m/fail "Unlinked Lean function" {:name name}))
    (let [found (filter #(= name (ir/name-label %)) (keys (:functions session)))]
      (when-not (= 1 (count found)) (m/fail "Missing or ambiguous Lean name" {:name name}))
      (first found))))

(defn function-ref [name] {:guest/function name})

(defn- nat! [x]
  (when-not (and (integer? x) (<= 0 x 9007199254740991))
    (m/fail "Interop prototype requires small Nat" {:value x})) x)

(defn- argument! [state kind value]
  (case kind
    :nat (nat! value)
    :closure (when-not (and (m/ref? value) (= :closure (:kind (m/node state value))))
               (m/fail "Expected guest closure" {:value value}))
    (m/fail "Unsupported host argument adapter" {:adapter kind})))

(def ^:private control-keys [:body :locals :joins :frames :status :result :resume-var :host-request])
(declare drive!)

(defn- invoke! [context target args]
  (let [{:keys [state session]} context parent @state
        child (if (m/ref? target)
                ;; Borrow for this invocation, then enter through the same boxed
                ;; application path as guest IR, including partial/overapplication.
                (m/call (-> (m/retain parent target 1)
                            (dissoc :result :resume-var :host-request)
                            (assoc :frames [] :status :running :locals {0 target} :joins {}))
                        [:closure [:var 0]] (mapv #(vector :imm %) args) nil nil)
                (m/start (apply dissoc parent control-keys) (resolve session target) args))]
    (reset! state child)
    (try
      (let [result (drive! context) finished @state]
        (reset! state (merge (apply dissoc finished control-keys) (select-keys parent control-keys)))
        result)
      (catch Throwable e
        (reset! state (assoc-in parent [:stats :steps] (get-in @state [:stats :steps])))
        (throw e)))))

(defn- run-until-boundary [session state fuel]
  (case (:backend session)
    :reference (m/run state fuel)
    :mutable (u/freeze (u/run! (u/thaw state) fuel))
    :jvm (u/freeze (lazy/run! (:program session) (u/thaw state) fuel))))

(defn drive! [{:keys [state session step-limit] :as context}]
  (loop []
    (let [remaining (- step-limit (get-in @state [:stats :steps]))
          current (run-until-boundary session @state (max 0 remaining))]
      (reset! state current)
      (case (:status current)
        :done (:result current)
        :host-call
        (let [{:keys [symbol arguments]} (:host-request current)
              {invoke-host :fn kinds :arguments :as binding} (get-in session [:bindings symbol])
              params (get-in session [:signatures symbol])]
          (when-not (and binding (= (count kinds) (count arguments)))
            (m/fail "Invalid host request" {:symbol symbol}))
          (doseq [[kind arg] (map vector kinds arguments)] (argument! current kind arg))
          (let [active (atom true)
                callback (fn [target args]
                           (when-not (and @active (identical? (:owner context) (Thread/currentThread)))
                             (m/fail "Guest callback is outside its synchronous host invocation" {}))
                           (invoke! context target args))
                result (try (nat! (apply invoke-host {:invoke callback} arguments))
                            (finally (reset! active false)))]
            ;; Arguments are borrowed during the handler. Afterwards discharge
            ;; ownership transferred by the caller; borrowed ABI params survive.
            (swap! state (fn [s] (reduce (fn [s [param arg]]
                                          (if (:borrow param) s (m/release s arg 1)))
                                        s (map vector params arguments))))
            (swap! state m/resume result)
            (recur)))
        :paused (m/fail "Interop instruction budget exhausted" {:steps (get-in current [:stats :steps])})
        (m/fail "Unexpected interop boundary" {:status (:status current)})))))

(defn- run-call [session target world args decode]
  (let [initial (m/start world target args)
        state (atom initial)
        result (drive! {:state state :session session
                        :step-limit (+ (get-in initial [:stats :steps]) (:fuel session))
                        :owner (Thread/currentThread)})]
    (try {:value (decode @state result) :state @state}
         (catch clojure.lang.ExceptionInfo e
           ;; In particular, IO errors carry a guest error owner. Keep the
           ;; completed world available for inspecting or releasing that owner.
           (throw (ex-info (.getMessage e) (assoc (ex-data e) :state @state) e))))))

(defn- typed-options! [args {:keys [arguments] :as options}]
  (when-not (and (map? options) (vector? arguments) (contains? options :result)
                 (= (count arguments) (count args)))
    (m/fail "Typed call requires one argument descriptor per value and a result descriptor"
            {:arguments arguments :argument-count (count args)}))
  options)

(defn call
  "Call a linked Lean definition in a heap forked from :initial-world.
   Three arguments retain the small-Nat/function-ref adapter. The fourth
   argument supplies explicit {:arguments [descriptors] :result descriptor}.
   Returned :state owns any allocated guest result; decoding borrows it."
  ([session name args]
   (let [[world args]
         (reduce (fn [[s xs] arg]
                   (if-let [target (and (map? arg) (:guest/function arg))]
                     (let [[s closure] (m/expr s [:closure (resolve session target) []])]
                       [s (conj xs closure)])
                     [s (conj xs (nat! arg))]))
                 [(or (:initial-world session) (m/world (:functions session))) []] args)]
     (run-call session (resolve session name) world args (fn [_ value] (nat! value)))))
  ([session name args options]
   (let [{:keys [arguments result]} (typed-options! args options)
         target (resolve session name)
         params (:params (get (:functions session) target))]
     (when-not (= (count params) (count args))
       (m/fail "Guest arity mismatch" {:target target :expected (count params) :actual (count args)}))
     (let [[world encoded]
           (reduce (fn [[world values] [descriptor value]]
                     (let [[world value] (codec/encode world descriptor value)]
                       [world (conj values value)]))
                   [(or (:initial-world session) (m/world (:functions session))) []]
                   (map vector arguments args))]
       (run-call session target world encoded #(codec/decode %1 result %2))))))

(defn call-io
  "Call an explicitly selected IO entry, appending its erased world argument.
   :result describes the successful IO payload. No IO type is inferred from an
   object return type; when raw parameter metadata exists its last type must
   be void. Guest IO errors throw with their completed :state attached."
  [session name args options]
  (let [{:keys [arguments result]} (typed-options! args options)
        target (resolve session name)
        f (get (:functions session) target)
        runtime-types (:runtime-param-types (meta f))]
    (when-not (= (count (:params f)) (inc (count args)))
      (m/fail "IO entry requires explicit arguments followed by one world token"
              {:target target :expected (count (:params f)) :actual (inc (count args))}))
    (when (and runtime-types (not= "void" (peek runtime-types)))
      (m/fail "IO entry does not have a void world parameter" {:target target :runtime-param-types runtime-types}))
    (call session target (conj (vec args) nil)
          {:arguments (conj arguments :world) :result [:io result]})))

(defn function [session name]
  (resolve session name)
  (fn [& args] (:value (call session name args))))
