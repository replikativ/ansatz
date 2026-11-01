(ns prototype.typed-eio-test
  "Actual captured Lean IR and real raw transport across all three backends.
   No modeled compiler, and no claim of whole-frontend Project acceptance."
  (:require [clojure.test :refer [deftest is]]
            [clojure.data.json :as json]
            [clojure.string :as str]
            [prototype.typed-eio :as eio]
            [prototype.raw-interop :as raw]
            [prototype.import-ir :as ir]
            [prototype.interop-codec :as codec]
            [prototype.machine :as m]))

(defn name-in [space part] ["str" ["str" ["anonymous"] space] part])
(def builders {:ok (name-in "EIOResultBuilders" "success")
               :error (name-in "EIOResultBuilders" "failure")})
(def backends [:reference :mutable :jvm])
(defn rows [file]
  (mapv #(json/read-str % :key-fn keyword)
        (str/split-lines (slurp (str "fixtures/typed-eio/" file)))))
(def captured-builders (delay (rows "result-builders.ndjson")))
(def captured-app (delay (rows "project-app-eio.ndjson")))
(defn specification [f] {:signature eio/signature :builders builders :fn f})
(defn controller [f] (eio/controller (specification f)))
(defn program [binding]
  (into {} (for [row (concat @captured-builders @captured-app)
                 :when (= "decl" (:kind row))]
             (if (get-in row [:ir :extern])
               (raw/lower {"ansatz_app_eio_text" binding} row)
               (ir/lower-declaration row)))))
(defn fixture [backend f]
  (let [c (controller f) functions (program (:binding c))
        session (raw/open-functions functions {"ansatz_app_eio_text" (:binding c)}
                  {:backend backend :fuel 100000})]
    (assoc c :world (m/world functions) :session session)))
(defn call! [fixture entry value]
  (raw/call (:session fixture) (:world fixture) (name-in "ProjectAppEIO" entry) [value m/erased]))
(defn error-of [thunk] (try (thunk) nil (catch Throwable cause cause)))
(defn has-cause? [error expected]
  (loop [cause error]
    (cond (identical? cause expected) true (nil? cause) false
          :else (recur (.getCause ^Throwable cause)))))

(deftest actual-native-ABI-and-helper-IR-are-explicit
  (let [extern (first (filter #(get-in % [:ir :extern]) @captured-app))
        d (get-in extern [:ir :extern])]
    (is (= eio/signature {:params (mapv #(select-keys % [:ty :borrow]) (:xs d))
                          :return-type (:type d)}))
    (doseq [manifest [(first @captured-app) (first @captured-builders)]]
      (is (= "4.33.1" (:leanVersion manifest)))
      (is (= [] (get-in manifest [:initializationPlan :actions]))))
    (is (= (vec (vals builders)) (:guest-helper-roots (:binding (controller #(hash-map :ok %))))))))

(deftest actual-Lean-wrappers-handle-success-error-and-sequence-unused-result
  (doseq [backend backends text ["" "λ 🦉"]]
    (let [seen (atom []) f (fixture backend #(do (swap! seen conj %) {:ok (str % "!")}))
          original (:world f)
          result ((:invoke! f) 2 #(call! f "twice" text))]
      (is (= [text text] @seen))
      (is (= (str text "!") (codec/decode (:state result) [:io :string] (:value result))))
      (is (identical? original (:world f)))
      (let [released (m/release (:state result) (:value result) 1)]
        (is (empty? (:heap released))))))
  (doseq [backend backends]
    (let [seen (atom []) f (fixture backend #(do (swap! seen conj %) {:error (str "domain:" %)}))
          handled ((:invoke! f) 1 #(call! f "handled" "λ"))
          unhandled ((:invoke! f) 1 #(call! f "run" "λ"))
          error (error-of #(codec/decode (:state unhandled) [:io :string] (:value unhandled)))
          error-value (:guest-error (ex-data error)) error-node (m/node (:state unhandled) error-value)]
      (is (= "domain:λ" (codec/decode (:state handled) [:io :string] (:value handled))))
      (is (= :guest-error (:type (ex-data error))))
      ;; Actual run wrapper, not the host adapter, builds IO.Error.userError.
      (is (= 18 (:tag error-node)))
      (is (= "domain:λ" (codec/decode-boxed (:state unhandled) :string (first (:fields error-node)))))
      (is (= ["λ" "λ"] @seen))
      (is (empty? (:heap (m/release (:state handled) (:value handled) 1))))
      (is (empty? (:heap (m/release (:state unhandled) (:value unhandled) 1)))))))

(deftest permission-is-bounded-same-thread-and-removed-after-failure
  (doseq [backend backends]
    (let [effects (atom 0) f (fixture backend #(do (swap! effects inc) {:ok %}))]
      (is (some? (error-of #(call! f "run" "compile-time"))))
      (is (zero? @effects))
      (let [error (error-of (fn [] ((:invoke! f) 1 #(call! f "twice" "one"))))]
        (is (= :claim-permission (:typed-eio-phase (ex-data error))))
        (is (= 1 @effects)))
      (is (some? (error-of #(call! f "run" "stale"))))
      (is (= 1 @effects))
      (is (some? ((:invoke! f) 1
                  #(let [result (promise)
                         thread (Thread. (fn [] (deliver result (error-of (fn [] (call! f "run" "foreign"))))))]
                     (.start thread) (.join thread 5000)
                     (is (not (.isAlive thread)))
                     (deref result 1000 nil)))))
      (is (= 1 @effects))
      (let [error (error-of #((:invoke! f) 1 (fn [] ((:invoke! f) 1 (fn [] :unused)))))]
        (is (str/includes? (.getMessage ^Throwable error) "cannot be nested"))))))

(deftest service-cannot-reenter-the-guest-during-its-callback
  (doseq [backend backends]
    (let [current (atom nil) rejected (atom nil) effects (atom 0)
          f (fixture backend (fn [text]
                               (swap! effects inc)
                               (reset! rejected (error-of #(call! @current "run" "reentry")))
                               {:ok text}))]
      (reset! current f)
      (let [result ((:invoke! f) 2 #(call! f "run" "outer"))]
        (is (= 1 @effects))
        (is (= :claim-permission (:typed-eio-phase (ex-data @rejected))))
        (is (= "outer" (codec/decode (:state result) [:io :string] (:value result))))
        (is (empty? (:heap (m/release (:state result) (:value result) 1))))))))

(deftest persistent-input-is-not-an-ordinary-RC-owner
  (doseq [backend backends]
    (let [f (fixture backend #(hash-map :ok %))
          [world input] (m/allocate (:world f) :string 249 [])
          world (m/mark-persistent (assoc-in world [:heap (:id input) :text] "persistent") input)
          result ((:invoke! f) 1 #(call! (assoc f :world world) "run" input))]
      (is (= "persistent" (codec/decode (:state result) [:io :string] (:value result))))
      (is (= (m/node world input) (m/node (:state result) input)))
      (is (zero? (:rc (m/node (:state result) input)))))))

(deftest owned-input-survives-host-failure-and-is-consumed-on-normal-domain-outcome
  (doseq [backend backends outcome [:ok :error]]
    (let [f (fixture backend #(hash-map outcome %))
          [world input] (m/allocate (:world f) :string 249 [])
          world (assoc-in world [:heap (:id input) :text] "owned")
          f (assoc f :world world)
          result ((:invoke! f) 1 #(call! f "handled" input))]
      (is (= "owned" (codec/decode (:state result) [:io :string] (:value result))))
      (is (not (contains? (:heap (:state result)) (:id input))))
      (is (= 1 (:rc (m/node world input))))
      (is (empty? (:heap (m/release (:state result) (:value result) 1))))))
  (doseq [backend backends]
    (let [selected (ex-info "host failure" {:checkpoint :forged :typed-eio-phase :forged})
          effects (atom 0) f (fixture backend (fn [_] (swap! effects inc) (throw selected)))
          [world input] (m/allocate (:world f) :string 249 [])
          f (assoc f :world (assoc-in world [:heap (:id input) :text] "retained"))
          error (error-of (fn [] ((:invoke! f) 1 #(call! f "run" input)))) data (ex-data error)]
      (is (has-cause? error selected)) (is (= 1 @effects))
      (is (= :host-call (:typed-eio-phase data)))
      (is (= :owned (:typed-eio-input-state data)))
      (is (= 1 (:rc (m/node (:checkpoint data) input))))
      (is (= backend (get-in data [:checkpoint-session :backend])))
      (is (nil? (:typed-eio-result-owner data))))))

(deftest invalid-ABI-builders-and-world-reject-before-effects
  (let [effects (atom 0) spec (specification #(do (swap! effects inc) {:ok %}))]
    (doseq [bad [(dissoc spec :signature) (assoc spec :extra true)
                 (assoc-in spec [:signature :params 1 :ty] "tagged")
                 (assoc-in spec [:signature :params 0 :borrow] true)
                 (assoc spec :builders {:ok (:ok builders) :error (:ok builders)})]]
      (is (some? (error-of #(eio/controller bad)))))
    (let [f (fixture :reference (:fn spec))]
      (is (some? (error-of #((:invoke! f) 1
                              (fn [] (raw/call (:session f) (:world f)
                                               (name-in "ProjectAppEIO" "hostText") ["x" 0]))))))
      (let [world (assoc-in (:world f) [:functions (:ok builders) :body] [:return [:var 1]])
            session (raw/open-functions (:functions world) {"ansatz_app_eio_text" (:binding f)}
                      {:backend :reference :fuel 10000})]
        (is (some? (error-of #((:invoke! f) 1
                                (fn [] (raw/call session world (name-in "ProjectAppEIO" "run") ["x" m/erased])))))))
      (is (zero? @effects)))))

(deftest malformed-host-outcomes-are-not-guest-domain-errors
  (doseq [backend backends output [{:ok "x" :error "y"} {:value "x"} {:ok 3} {:error (m/->Ref 99)}]]
    (let [effects (atom 0) f (fixture backend (fn [_] (swap! effects inc) output))
          error (error-of (fn [] ((:invoke! f) 1 #(call! f "run" "input")))) data (ex-data error)]
      (is (= 1 @effects)) (is (= :encode-outcome (:typed-eio-phase data)))
      (is (:typed-eio-terminal? data)) (is (not= :guest-error (:type data)))
      (is (nil? (:typed-eio-result-owner data))))))

(deftest caught-host-failure-poisons-the-remaining-invocation-permission
  (doseq [backend backends]
    (let [effects (atom 0) selected (ex-info "terminal effect failure" {})
          f (fixture backend (fn [_] (swap! effects inc) (throw selected)))
          errors ((:invoke! f) 2
                  (fn [] [(error-of #(call! f "run" "first"))
                          (error-of #(call! f "run" "second"))]))]
      (is (has-cause? (first errors) selected))
      (is (= :claim-permission (:typed-eio-phase (ex-data (second errors)))))
      (is (= 1 @effects)))))
