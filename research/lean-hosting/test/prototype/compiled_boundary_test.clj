(ns prototype.compiled-boundary-test
  "Actual checker + independent emitted scalar IR in one World. Host anchors and
   callback callers are explicit fixtures, not a hosted Lean Environment/frontend."
  (:require [clojure.test :refer [deftest is]]
            [prototype.kernel-bridge :as bridge]
            [prototype.kernel-bridge-test :as kernel]
            [prototype.typed-tail-test :as fixture]
            [prototype.typed-tail-execution-test :as execution-fixture]
            [prototype.typed-tail-execution :as execution]
            [prototype.raw-interop :as raw]
            [prototype.typed-extern :as typed]
            [prototype.typed-extern-test :as typed-fixture]
            [prototype.interop-codec :as codec]
            [prototype.machine :as m]
            [prototype.mutable :as u]
            [prototype.lazy-runtime :as lazy]
            [ansatz.kernel.name :as name])
  (:import [ansatz.kernel Env]))

(def backends [:reference :mutable :jvm])
(def boundary-text (str "boundary λ" (char 0)))
(def control-keys [:body :locals :joins :frames :status :result :resume-var :host-request])
(def storage-keys [:heap :next-id :globals :events :kernel-environments])

(defn observe-route [events compile]
  (fn [& args]
    (when-let [artifact (apply compile args)]
      (reduce (fn [out key]
                (if-let [execute (get out key)]
                  (assoc out key
                         (fn [machine & args]
                           (let [frames? (u/has-frames? machine)
                                 result (apply execute machine args)]
                             (swap! events conj [(get-in artifact [:specialization :kind]) result frames?])
                             result)))
                  out)) artifact [:execute! :execute-budget!]))))

(defn compiled-helper? [events]
  ;; The captured artifact and executed outcome must belong to the SAME hook.
  ;; context :invoke enters the selected helper without the outer guest frames.
  (boolean (some #{[:typed-tail :specialized false]} events)))

(defn checked-world [functions]
  (let [old-env (kernel/checked-nat-environment)
        [world type] (kernel/constant (m/world functions) "Nat")
        [world body] (kernel/literal world 42)
        [world declaration] (kernel/declaration world "BoundaryAnswer" type body)
        admitted (bridge/admit-definition world old-env declaration)
        ;; This is a host-supplied snapshot anchor for the actual checker result,
        ;; NOT a guest Lean Environment layout or a new checking/source receipt.
        [world anchor] (m/allocate (:world admitted) :ctor 0 [declaration])
        [world sentinel] (m/resource world "compiled-boundary-sentinel")
        world (assoc-in world [:kernel-environments (:id anchor)] {:anchor anchor :env (:env admitted)})]
    {:world world :old-env old-env :admitted admitted :anchor anchor :sentinel sentinel :body body}))

(defn configuration [input] {:typed-tail (execution-fixture/config input)})
(defn session [functions bindings backend input cache fuel]
  (raw/open-functions functions bindings
                      {:backend backend :cache cache :fuel fuel :compiler-options (configuration input)}))

(deftest actual-checker-admission-and-independent-scalar-execution-preserve-worlds
  (let [input (fixture/bundle "scalar-wrapper-programs.jsonl") functions (:runtime input)
        {:keys [world old-env admitted anchor body]} (checked-world functions)
        target (fixture/target (:typed input) "sum64") args [3N 0N]
        initial (m/start world target args) terminal (m/run initial)
        projector (bridge/make-projector world)
        events (atom []) compile execution/compile-entry cache (lazy/code-cache)]
    (is (nil? (.lookup ^Env old-env (name/from-string "BoundaryAnswer"))))
    (is (some? (.lookup ^Env (:env admitted) (name/from-string "BoundaryAnswer"))))
    (is (= 42N (.o0 ^ansatz.kernel.Expr (bridge/project-expr world body projector))))
    (is (= 6N (:result terminal)))
    (with-redefs [execution/compile-entry (observe-route events compile)]
      (doseq [backend backends
              :let [s (session functions {} backend input cache 10000)
                    completed (raw/call s world target args)]]
        (is (= terminal (:state completed)))
        (is (= (execution-fixture/carrier-shape terminal) (execution-fixture/carrier-shape (:state completed))))
        (is (= (select-keys world storage-keys) (select-keys (:state completed) storage-keys)))
        (is (identical? (:env admitted) (get-in completed [:state :kernel-environments (:id anchor) :env])))
        (is (thrown-with-msg? clojure.lang.ExceptionInfo #"different world"
                             (bridge/project-expr (:state completed) body projector)))
        (doseq [fuel (range (+ 2 (get-in terminal [:stats :steps])))
                :let [prefix (:state (raw/advance-to-boundary (assoc s :fuel fuel) initial))
                      expected (m/run initial fuel)]]
          (is (= expected prefix))
          (is (= (execution-fixture/carrier-shape expected) (execution-fixture/carrier-shape prefix)))
          (is (= (select-keys world storage-keys) (select-keys prefix storage-keys)))
          (when (= :paused (:status prefix))
            (let [saved prefix
                  left (raw/continue s (m/resume saved nil))
                  right (raw/continue s (m/resume saved nil))]
              (is (= terminal (:state left) (:state right)))
              (is (= (execution-fixture/carrier-shape terminal)
                     (execution-fixture/carrier-shape (:state left))
                     (execution-fixture/carrier-shape (:state right))))
              (is (= saved prefix))))))
      (is (compiled-helper? @events)))
    (is (= initial (m/start world target args)))
    (is (nil? (.lookup ^Env old-env (name/from-string "BoundaryAnswer"))))))

(defn scalar-callback-program [input signature]
  (let [caller (fixture/name-of "boundaryCaller") callback (fixture/name-of "boundaryCallback")
        trap (fixture/name-of "boundaryTrap")
        symbol "boundary_scalar_callback"]
    {:caller caller :callback callback :trap trap :symbol symbol
     :functions (assoc (:runtime input)
                       trap {:params [] :body [:unreachable]}
                       caller {:params [1 2]
                               :body [:let 9 [:literal 7]
                                      [:call 3 [:direct callback] [[:var 1] [:var 2]]
                                       [:let 4 [:runtime "lean_uint64_add" [[:var 3] [:var 9]]]
                                        [:return [:var 4]]]]]}
                       callback {:params [1 2] :raw-extern {:symbol symbol :signature signature}
                                 :body [:host symbol [[:var 1] [:var 2]] 3 [:return [:var 3]]]})}))

(defn error-of [f] (try (f) nil (catch clojure.lang.ExceptionInfo cause cause)))

(defn reference-helper-return [world target args]
  (merge (apply dissoc (m/run (m/start world target args)) control-keys)
         (select-keys world control-keys)))

(deftest raw-callback-helper-restores-outer-control-and-never-retries-effects
  (let [input (fixture/bundle "scalar-wrapper-programs.jsonl")
        target (fixture/target (:typed input) "sum64")
        signature {:params [{:ty "uint64" :borrow false} {:ty "uint64" :borrow false}] :return-type "uint64"}
        {:keys [caller trap symbol functions]} (scalar-callback-program input signature)
        {:keys [world]} (checked-world functions)
        cache (lazy/code-cache) events (atom []) compile execution/compile-entry
        results (atom []) failures (atom {})]
    (with-redefs [execution/compile-entry (observe-route events compile)]
      (doseq [mode [:success :host-failure :helper-failure] backend backends
              :let [effects (atom 0) controls (atom []) seen (count @events)
                    binding {:signature signature
                             :handler (fn [{:keys [invoke]} current arguments]
                                        (swap! effects inc)
                                        (is (= 1 (count (:frames current))))
                                        (let [[next result] (invoke current target arguments)]
                                          (swap! controls conj [(select-keys current control-keys) (select-keys next control-keys)])
                                          (is (= 55N result))
                                          (is (= (reference-helper-return current target arguments) next))
                                          (is (= (select-keys current storage-keys) (select-keys next storage-keys)))
                                          (case mode
                                            :host-failure (throw (ex-info "boundary effect already happened" {}))
                                            :helper-failure (invoke next trap [])
                                            [next result])))}
                    s (session functions {symbol binding} backend input cache 10000)]]
        (if (not= :success mode)
          (let [cause (error-of #(raw/call s world caller [10N 0N])) data (ex-data cause)]
            (is (some? cause))
            (is (= (select-keys world storage-keys) (select-keys (:checkpoint data) storage-keys)))
            (is (identical? functions (get-in data [:checkpoint-session :functions])))
            (if (= :host-failure mode)
              (do (is (re-find #"effect already happened" (.getMessage cause)))
                  (is (= 1 (count (get-in data [:checkpoint :frames]))))
                  (is (= symbol (get-in data [:checkpoint :host-request :symbol]))))
              (do (is (= {:target trap :argument-count 0} (:failed-helper data)))
                  (is (= symbol (get-in data [:host-boundary-checkpoint :host-request :symbol])))
                  (is (= (second (first @controls)) (select-keys (:helper-entry-checkpoint data) control-keys)))
                  (is (identical? s (:host-boundary-session data)))
                  (is (identical? s (:helper-entry-session data)))))
            (swap! failures update mode (fnil conj []) (:checkpoint data)))
          (let [called (raw/call s world caller [10N 0N])]
            (is (= 62N (:value called)))
            (is (not (m/ref? (:value called))))
            (is (= 7 (get-in called [:state :locals 9])))
            (swap! results conj (:state called))))
        (is (= 1 @effects))
        (is (= 1 (count @controls)))
        (is (apply = (first @controls)))
        (when (and (= :jvm backend) (not= :success mode))
          (is (pos? (:cache-hits (lazy/summary (:program s))))))
        (when (= :jvm backend) (is (compiled-helper? (subvec @events seen)))))
      (is (apply = @results))
      (is (apply = (map execution-fixture/carrier-shape @results)))
      (doseq [snapshots (vals @failures)]
        (is (apply = snapshots))
        (is (apply = (map execution-fixture/carrier-shape snapshots)))))
    (is (empty? (:events world)))
    (is (nil? (:status world)))))

(deftest typed-string-adapter-keeps-alias-owners-and-exact-failure-packets
  (let [input (fixture/bundle "scalar-wrapper-programs.jsonl") target (fixture/target (:typed input) "sum64")
        caller (fixture/name-of "typedBoundaryCaller") callback (fixture/name-of "typedBoundaryCallback")
        symbol "boundary_typed_string" cache (lazy/code-cache) events (atom []) compile execution/compile-entry
        encode codec/encode-boxed]
    (with-redefs [execution/compile-entry (observe-route events compile)]
      (doseq [ownerships [[:owned :owned] [:owned :borrowed]] fail? [false true]
              :let [signature {:params (mapv #(hash-map :ty "tobject" :borrow (= :borrowed %)) ownerships)
                               :return-type "tobject"}
                    functions (assoc (:runtime input)
                                     caller {:params [1 2] :body [:call 3 [:direct callback] [[:var 1] [:var 2]]
                                                                 [:return [:var 3]]]}
                                     callback {:params [1 2] :raw-extern {:symbol symbol :signature signature}
                                               :body [:host symbol [[:var 1] [:var 2]] 3 [:return [:var 3]]]})
                    base (:world (checked-world functions))
                    [world input-ref] (typed-fixture/guest-string base boundary-text)
                    world (m/retain world input-ref 2)
                    snapshots (atom [])]]
        (doseq [backend backends
                :let [effects (atom 0) encodings (atom 0) seen (count @events)
                      adapter (typed/binding
                               {:signature signature
                                :arguments (mapv #(hash-map :codec :string :ownership %) ownerships)
                                :result :string
                                :fn (fn [a b]
                                      (swap! effects inc) (is (= a b))
                                      (if fail? (throw (ex-info "typed boundary host effect happened" {})) a))})
                      binding (assoc adapter :handler
                                     (fn [context current values]
                                       (is (= 1 (count (:frames current))))
                                       (let [[next sum] ((:invoke context) current target [10N 0N])]
                                         (is (= 55N sum))
                                         (is (= (reference-helper-return current target [10N 0N]) next))
                                         (is (= (select-keys current control-keys) (select-keys next control-keys)))
                                         ((:handler adapter) context next values))))
                      s (session functions {symbol binding} backend input cache 10000)]]
          (with-redefs [codec/encode-boxed (fn [current descriptor value]
                                           (swap! encodings inc)
                                           (is (= 3 (:rc (m/node current input-ref))))
                                           (encode current descriptor value))]
            (if fail?
              (let [cause (error-of #(raw/call s world caller [input-ref input-ref])) data (ex-data cause)]
                (is (= :host-call (:typed-extern-phase data)))
                (is (true? (:typed-extern-terminal? data)))
                (is (nil? (:typed-extern-result-owner data)))
                (is (= ownerships (mapv :state (:typed-extern-input-owners data))))
                (is (= [input-ref input-ref] (get-in data [:typed-extern-entry :arguments])))
                (is (= (get-in data [:typed-extern-entry :world]) (:typed-extern-checkpoint data)))
                (is (= 3 (:rc (m/node (:typed-extern-checkpoint data) input-ref))))
                (is (= (select-keys world storage-keys) (select-keys (:checkpoint data) storage-keys)))
                (is (identical? functions (get-in data [:checkpoint-session :functions])))
                (is (zero? @encodings))
                (swap! snapshots conj (:checkpoint data)))
              (let [{:keys [state value]} (raw/call s world caller [input-ref input-ref])
                    owned (count (filter #{:owned} ownerships))]
                (is (= boundary-text (codec/decode-boxed state :string value)))
                (is (string? value))
                (is (not (m/ref? value)))
                (is (not= input-ref value))
                (is (= (- 3 owned) (:rc (m/node state input-ref))))
                (is (= input-ref (get-in state [:locals 1])))
                (is (= input-ref (get-in state [:locals 2])))
                (is (= 1 @encodings))
                ;; String encoding returns an immediate immutable JVM String,
                ;; not an allocated guest Ref. Its release is a no-op; real
                ;; aliased guest input owners remain independently observable.
                (is (= state (m/release state value 1)))
                (is (= (:next-id world) (:next-id state)))
                (is (not (contains? (:heap (m/release state input-ref (- 3 owned))) (:id input-ref))))
                (is (= (:kernel-environments world) (:kernel-environments state)))
                (swap! snapshots conj state))))
          (is (= 1 @effects))
          (is (= 3 (:rc (m/node world input-ref))))
          (when (and (= :jvm backend) fail?)
            (is (pos? (:cache-hits (lazy/summary (:program s))))))
          (when (= :jvm backend) (is (compiled-helper? (subvec @events seen)))))
        (is (apply = @snapshots))))))
