(ns prototype.typed-extern-test
  "Real raw transport/ownership and public resident integration, with explicitly
   modelled compiler envelopes and modified captured IR for facade tests."
  (:require [clojure.test :refer [deftest is]]
            [clojure.data.json :as json]
            [clojure.string :as str]
            [prototype.typed-extern :as sut]
            [prototype.raw-interop :as raw]
            [prototype.machine :as m]
            [prototype.native-scalar :as native]
            [prototype.resident-frontend :as resident]
            [prototype.resident-frontend-test :as resident-model]
            [prototype.hosted-file-test :as hosted-model]))

(def symbol-name "ansatz_app_typed_value")
(def target ["str" ["anonymous"] "typedValue"])
(def backends [:reference :mutable :jvm])
(defn specification [codecs ownerships result f]
  {:signature {:params (mapv (fn [ownership] {:ty "object" :borrow (= :borrowed ownership)}) ownerships)
               :return-type "object"}
   :arguments (mapv (fn [codec ownership] {:codec codec :ownership ownership}) codecs ownerships)
   :result result :fn f})
(defn program [binding]
  (let [params (vec (range 1 (inc (count (get-in binding [:signature :params]))))) dest (inc (count params))]
    {target {:params params :raw-extern {:symbol symbol-name :signature (:signature binding)}
             :body [:host symbol-name (mapv #(vector :var %) params) dest [:return [:var dest]]]}}))
(defn invoke [backend spec prepare]
  (let [binding (sut/binding spec) functions (program binding)
        session (raw/open-functions functions {symbol-name binding} {:backend backend :fuel 10000})
        [world values] (prepare (m/world functions))]
    {:before world :values values :binding binding :session session
     :call #(raw/call session world target values)}))
(defn guest-string [world text]
  (let [[world ref] (m/allocate world :string 249 [])]
    [(assoc-in world [:heap (:id ref) :text] text) ref]))
(defn guest-mpz [world n]
  (let [[world ref] (m/allocate world :mpz 250 [])]
    [(assoc-in world [:heap (:id ref) :integer] n) ref]))
(defn error-of [f] (try (f) nil (catch clojure.lang.ExceptionInfo e e)))

(deftest unsupported-specifications-reject-before-host-execution
  (let [calls (atom 0) base (specification [:nat] [:owned] :nat #(do (swap! calls inc) %))]
    (doseq [bad [(dissoc base :signature) (assoc base :guess-signature true)
                 (assoc base :fn :keyword-is-not-a-function)
                 (assoc-in base [:signature :params 0 :ty] "uint64")
                 (assoc-in base [:signature :params 0 :borrow] 1)
                 (assoc-in base [:signature :return-type] "uint8")
                 (assoc-in base [:signature :params 0 :extra] true)
                 (assoc base :arguments [])
                 (assoc-in base [:arguments 0 :ownership] :borrowed)
                 (assoc-in base [:arguments 0 :ownership] :retain)
                 (assoc-in base [:arguments 0 :codec] :bytes)
                 (assoc-in base [:arguments 0 :codec] :erased)
                 (assoc-in base [:arguments 0 :codec] [:option :nat])
                 (assoc base :result [:io :string]) (assoc base :result :bytes)]]
      (is (some? (error-of #(sut/binding bad)))))
    (is (zero? @calls))))

(deftest boxed-string-owned-and-borrowed-inputs-produce-independent-results
  (doseq [backend backends ownership [:owned :borrowed]]
    (let [seen (atom nil)
          spec (specification [:string] [ownership] :string #(do (reset! seen %) (str % "!")))
          {:keys [before values call]} (invoke backend spec #(let [[w r] (guest-string % "λ 🦉")] [w [r]]))
          called (call) value (first values) after (:state called)]
      (is (= "λ 🦉" @seen)) (is (string? @seen)) (is (not (m/ref? @seen)))
      (is (= "λ 🦉!" (:value called))) (is (not (m/ref? (:value called))))
      (is (= 1 (:rc (m/node before value))))
      (if (= :owned ownership)
        (is (not (contains? (:heap after) (:id value))))
        (is (= (m/node before value) (m/node after value)))))))

(deftest nat-decoding-covers-native-immediates-and-owned-mpz-without-ref-escape
  (doseq [backend backends]
    (let [big (.shiftLeft java.math.BigInteger/ONE 130)
          seen (atom []) spec (specification [:nat] [:owned] :nat #(do (swap! seen conj %) (inc' %)))
          immediate (invoke backend spec (fn [w] [w [(native/native-scalar 42)]]))
          heap (invoke backend spec #(let [[w r] (guest-mpz % big)] [w [r]]))
          result ((:call heap))]
      (is (= 43 (:value ((:call immediate)))))
      (is (= (inc' big) (:value result)))
      (is (every? integer? @seen)) (is (not-any? m/ref? @seen))
      (is (not (contains? (:heap (:state result)) (:id (first (:values heap)))))))))

(deftest aliased-input-occurrences-are-consumed-once-each-and-persistent-values-survive
  (doseq [backend backends ownerships [[:owned :owned] [:owned :borrowed]]]
    (let [spec (specification [:string :string] ownerships :string str)
          {:keys [values call]} (invoke backend spec
                                 #(let [[w r] (guest-string % "x")] [(m/retain w r 1) [r r]]))
          called (call) r (first values)]
      (is (= "xx" (:value called)))
      (if (= [:owned :owned] ownerships)
        (is (not (contains? (:heap (:state called)) (:id r))))
        (is (= 1 (:rc (m/node (:state called) r)))))))
  (let [spec (specification [:string :string] [:owned :owned] :string str)
        {:keys [values call]} (invoke :reference spec
                               #(let [[w r] (guest-string % "persistent")] [(m/mark-persistent w r) [r r]]))
        called (call)]
    (is (= "persistentpersistent" (:value called)))
    (is (zero? (:rc (m/node (:state called) (first values)))))))

(deftest insufficient-alias-owners-and-bad-argument-values-reject-before-host-effects
  (let [calls (atom 0)
        spec (specification [:string :string] [:owned :owned] :string #(do (swap! calls inc) (str %1 %2)))
        fixture (invoke :reference spec #(let [[w r] (guest-string % "x")] [w [r r]]))
        error (error-of (:call fixture)) data (ex-data error)]
    (is (= :validate-inputs (:typed-extern-phase data)))
    (is (zero? @calls))
    (is (= 1 (:rc (m/node (:checkpoint data) (first (:values fixture)))))))
  (doseq [[descriptor value] [[:nat -1] [:string "\ud800"]]]
    (let [calls (atom 0) fixture (invoke :reference
                                (specification [descriptor] [:owned] descriptor #(do (swap! calls inc) %))
                                (fn [w] [w [value]]))
          error (error-of (:call fixture))]
      (is (= :decode-inputs (:typed-extern-phase (ex-data error))))
      (is (zero? @calls)))))

(deftest host-and-result-errors-retain-input-owners-without-finally-cleanup
  (doseq [backend backends [f phase] [[(fn [_] (throw (ex-info "host failure" {:host-failure? true}))) :host-call]
                                    [(fn [_] -1) :encode-result]
                                    [(fn [_] (m/->Ref 1234)) :encode-result]]]
    (let [fixture (invoke backend (specification [:string] [:owned] :nat f)
                          #(let [[w r] (guest-string % "owned")] [w [r]]))
          error (error-of (:call fixture)) data (ex-data error)
          ref (first (:values fixture))]
      (is (= phase (:typed-extern-phase data)))
      (is (:typed-extern-terminal? data))
      (is (= :owned (get-in data [:typed-extern-input-owners 0 :state])))
      (is (= 1 (:rc (m/node (:checkpoint data) ref))))
      (is (identical? (:checkpoint data) (:typed-extern-checkpoint data)))
      (is (nil? (:typed-extern-result-owner data))))))

(deftest failure-preserves-scoped-child-world-and-actual-active-session
  (let [spec (specification [:string] [:owned] :nat (fn [_] (throw (ex-info "typed child failure" {}))))
        typed (sut/binding spec)
        binding (assoc typed :handler
                       (fn [ctx world args]
                         (let [world (assoc world :typed-child-marker true)
                               world ((:checkpoint! ctx) world)
                               world ((:switch-backend! ctx) world :mutable)]
                           ((:handler typed) ctx world args))))
        functions (program binding)
        session (raw/open-functions functions {symbol-name binding} {:backend :jvm :fuel 10000})
        [world ref] (guest-string (m/world functions) "child")
        error (error-of #(raw/call session world target [ref])) data (ex-data error)]
    (is (= :mutable (get-in data [:checkpoint-session :backend])))
    (is (true? (get-in data [:checkpoint :typed-child-marker])))
    (is (identical? (:checkpoint data) (:typed-extern-checkpoint data)))
    (is (= 1 (:rc (m/node (:checkpoint data) ref))))
    (is (= :owned (get-in data [:typed-extern-input-owners 0 :state])))))

(def boxed-name ["str" ["str" ["anonymous"] "answer"] "_boxed"])
(defn extern-bundle [signature]
  (let [parameters (mapv (fn [index param] (assoc param :x {:idx index}))
                         (range 1 (inc (count (:params signature)))) (:params signature))]
    (->> (str/split-lines @hosted-model/captured)
         (map #(json/read-str % :key-fn keyword))
         (map (fn [row]
                (cond
                  (= boxed-name (:name row))
                  (-> row (assoc :dependencies [])
                      (assoc :ir {:extern {:f boxed-name :xs parameters
                                          :type (:return-type signature)
                                          :ext {:entries [{:standard {:backend ["str" ["anonymous"] "all"]
                                                                     :fn symbol-name}}]}}}))
                  (= ["str" ["anonymous"] "answer"] (:name row))
                  (-> row (assoc :dependencies [])
                      (assoc :ir {:fdecl {:f (:name row) :xs parameters :type (:return-type signature)
                                         :info {} :body ["ret" {:var {:id {:idx 1}}}]}}))
                  :else row)))
         (map json/write-str) (str/join "\n"))))

(deftest public-application-branch-admission-preserves-original-authority-and-cache
  (doseq [backend backends]
    (let [seen (atom []) binding (sut/binding (specification [:string] [:owned] :string
                                                           #(do (swap! seen conj %) (str "host:" %))))
          bundle (extern-bundle (:signature binding))
          prepared-base (resident-model/prepared backend true bundle)
          runtime-binding {:signature {:params [] :return-type "object"}
                           :handler (fn [_ world _] [world 0])}
          runtime-bindings {"lean_typed_adapter_preserved_runtime" runtime-binding}
          prior-session (:session prepared-base)
          prepared (assoc prepared-base :session
                          (raw/open-functions (get-in prepared-base [:world :functions]) runtime-bindings
                            (assoc (select-keys prior-session [:backend :fuel :compile-threshold])
                                   :cache (:cache prior-session))))
          configuration {:trusted-functions (get-in prepared [:world :functions]) :trusted-bindings runtime-bindings}
          base (resident/adopt-prepared prepared configuration)
          original (resident/snapshot base)
          denied (error-of #(resident/with-externs base {symbol-name binding}))
          allowed (resident/adopt-prepared original (assoc configuration :application-extern-symbols #{symbol-name}))
          configured (resident/with-externs allowed {symbol-name binding})
          loaded (resident-model/load-identity configured)
          called (resident/call (:context loaded) (:file loaded) hosted-model/answer-name
                                ["λ 🦉"] {:arguments [:string] :result :string})]
      (is (some? denied))
      (is (= "host:λ 🦉" (:value called)))
      (is (= ["λ 🦉"] @seen))
      (is (identical? original (resident/snapshot base)))
      (is (= runtime-bindings (get-in original [:session :bindings])))
      (is (identical? runtime-binding (get-in (resident/snapshot configured)
                                             [:session :bindings "lean_typed_adapter_preserved_runtime"])))
      (is (identical? binding (get-in (resident/snapshot configured) [:session :bindings symbol-name])))
      (is (identical? (get-in original [:session :cache]) (get-in (resident/snapshot configured) [:session :cache])))
      (is (some? (error-of #(resident/with-externs configured {symbol-name binding}))))
      (doseq [ctx [base allowed configured (:context loaded) (:context called)]] (resident/close! ctx)))))

(deftest actual-extern-ABI-must-match-declaration-borrow-flags
  (let [calls (atom 0) binding (sut/binding (specification [:nat] [:borrowed] :nat #(do (swap! calls inc) %)))
        row {:name target :ir {:extern {:f target :xs [{:x {:idx 1} :ty "object" :borrow false}]
                                       :type "object" :ext {:entries [{:standard {:backend ["str" ["anonymous"] "all"]
                                                                                :fn symbol-name}}]}}}}]
    (is (some? (error-of #(raw/lower {symbol-name binding} row))))
    (is (zero? @calls))))

(deftest a-borrowed-view-is-not-an-additional-owner-of-an-owned-alias
  (doseq [backend backends]
    (let [spec (specification [:string :string] [:owned :borrowed] :string str)
          {:keys [values call]} (invoke backend spec #(let [[w r] (guest-string % "view")] [w [r r]]))
          called (call)]
      (is (= "viewview" (:value called)))
      (is (not (contains? (:heap (:state called)) (:id (first values)))))
      (is (not (m/ref? (:value called)))))))

(deftest host-exception-data-cannot-replace-scoped-packets-or-adapter-ownership
  (doseq [backend backends]
    (let [host-data {:checkpoint {:forged true} :checkpoint-session {:backend :forged}
                     :typed-extern-entry :forged :typed-extern-checkpoint :forged
                     :typed-extern-phase :forged :typed-extern-input-owners :forged
                     :typed-extern-result-owner {:value (m/->Ref 99999) :state :transferred}
                     :typed-extern-terminal? false :host-note :diagnostic-only}
          fixture (invoke backend (specification [:string] [:owned] :string
                                                 (fn [_] (throw (ex-info "host supplied diagnostic data" host-data))))
                          #(let [[w r] (guest-string % "held")] [w [r]]))
          error (error-of (:call fixture)) data (ex-data error)]
      (is (= backend (get-in data [:checkpoint-session :backend])))
      (is (not (:forged (:checkpoint data))))
      (is (identical? (:checkpoint data) (:typed-extern-checkpoint data)))
      (is (map? (:typed-extern-entry data)))
      (is (= :host-call (:typed-extern-phase data)))
      (is (= :owned (get-in data [:typed-extern-input-owners 0 :state])))
      (is (nil? (:typed-extern-result-owner data)))
      (is (true? (:typed-extern-terminal? data)))
      (is (= :diagnostic-only (:host-note data)))
      (is (= 1 (:rc (m/node (:checkpoint data) (first (:values fixture)))))))))
