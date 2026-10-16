(ns prototype.interop
  "Small-Nat/closure host interop experiment. Host calls materialize guest state;
  reentrant callbacks run in the same guest heap. No arbitrary host-state forks."
  (:refer-clojure :exclude [resolve])
  (:require [prototype.import-ir :as ir]
            [prototype.machine :as m]
            [prototype.mutable :as u]
            [prototype.lazy-runtime :as lazy]))

(defn extern-symbol [decl]
  (or (some #(get-in % [:standard :fn]) (get-in decl [:ext :entries]))
      (m/fail "Unsupported extern specification" {:extern decl})))

(defn lower [bindings row]
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

(defn open-session
  ([catalogue roots bindings] (open-session catalogue roots bindings :jvm))
  ([catalogue roots bindings backend]
   (open-session catalogue roots bindings backend (lazy/code-cache)))
  ([catalogue roots bindings backend cache]
   (when-not (contains? #{:reference :mutable :jvm} backend) (m/fail "Unknown backend" {:backend backend}))
   (let [functions (ir/load-closure catalogue roots #(lower bindings %))
         signatures (reduce (fn [signatures [_ f]]
                              (if-let [{:keys [symbol params]} (:extern f)]
                                (let [shape (mapv #(select-keys % [:ty :borrow]) params)]
                                  (when-let [old (get signatures symbol)]
                                    (when-not (= shape (mapv #(select-keys % [:ty :borrow]) old))
                                      (m/fail "Incompatible declarations for host symbol" {:symbol symbol})))
                                  (assoc signatures symbol params)) signatures)) {} functions)]
     {:functions functions :bindings bindings :signatures signatures :backend backend
      :program (when (= :jvm backend) (lazy/open-program functions {} cache)) :fuel 1000000})))

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
        [child target args]
        (if (m/ref? target)
          ;; Borrow the callback for each invocation; application consumes this
          ;; extra owner and retains its captured fields through normal guest RC.
          (m/apply-target (assoc (m/retain parent target 1) :locals {0 target}) [:closure [:var 0]] args)
          [parent (resolve session target) args])
        child (m/start (apply dissoc child control-keys) target args)]
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

(defn call
  "Call a linked Lean definition from Clojure. Each top-level call has its own
  heap; nested host callbacks share that heap. Results currently must be Nat."
  [session name args]
  (let [[world args]
        (reduce (fn [[s xs] arg]
                  (if-let [target (and (map? arg) (:guest/function arg))]
                    (let [[s closure] (m/expr s [:closure (resolve session target) []])]
                      [s (conj xs closure)])
                    [s (conj xs (nat! arg))]))
                [(m/world (:functions session)) []] args)
        initial (m/start world (resolve session name) args)
        state (atom initial)
        result (drive! {:state state :session session :step-limit (:fuel session) :owner (Thread/currentThread)})]
    {:value (nat! result) :state @state}))

(defn function [session name]
  (resolve session name)
  (fn [& args] (:value (call session name args))))
