(ns generated-mutual-declaration-models-v1
  "Strict checker/projection models and mocked protocol boundaries. These are
   not actual source commands, native publication or generated-policy issuance."
  (:require [clojure.test :refer [deftest is run-tests]]
            [prototype.machine :as m] [prototype.scalar :as scalar]
            [prototype.kernel-bridge :as bridge]
            [prototype.imported-kernel :as imported]
            [prototype.kernel-projection-snapshot :as snapshot]
            [artifact-checked-declaration-adapter-v4 :as adapter]
            [general-command-receipt-v1 :as command]
            [general-frontend-source-provider-v1 :as provider]
            [java-composite-artifact-base-v1 :as base]
            [ansatz.research.ir.kernel-projection :as projection]
            [java-ir-baseline :as j])
  (:import [ansatz.kernel Env Name Level Expr ConstantInfo] [java.util LinkedHashMap]))
(def nil-tag (m/->Tag 0))
(defn ctor [world tag fields bytes]
  (if (zero? bytes) (m/allocate world :ctor tag (vec fields))
    (let [[world ref] (m/scalar-constructor world tag (vec fields) {:objects (count fields) :usize 0 :ssize bytes})]
      [(assoc-in world [:heap (:id ref) :scalar-bytes]
         (into {} (map #(vector (+ (* 8 (count fields)) %) 0) (range bytes)))) ref])))
(defn byte! [world ref value]
  (let [node (m/node world ref)]
    (assoc-in world [:heap (:id ref) :scalar-bytes]
      (scalar/write-bytes (:layout node) (:scalar-bytes node) {:index 4 :offset 0 :type "uint8" :region :scalar} value))))
(defn guest-name [world text] (ctor world 1 [nil-tag text] 8))
(defn constant [world text]
  (let [[world name] (guest-name world text)] (ctor world 4 [name nil-tag] 8)))
(defn payload [world text type body safety]
  (let [[world name] (guest-name world text) [world val] (ctor world 0 [name nil-tag type] 0)
        [world all] (ctor world 1 [name nil-tag] 0) [world ref] (ctor world 0 [val body nil-tag all] 1)]
    [(byte! world ref safety) ref]))
(defn group [safety-a safety-b]
  (let [[world level] (ctor (m/world {}) 1 [nil-tag] 8) [world type] (ctor world 3 [level] 8)
        [world a] (constant world "a") [world b] (constant world "b")
        [world pa] (payload world "a" type b safety-a) [world pb] (payload world "b" type a safety-b)
        [world tail] (ctor world 1 [pb nil-tag] 0) [world values] (ctor world 1 [pa tail] 0)
        [world declaration] (ctor world 5 [values] 0)]
    {:world world :declaration declaration :values values :payloads [pa pb] :type type}))
(defn checked [g]
  (bridge/admit-mutual-definitions (:world g) (.enableQuot (Env.)) (:declaration g) 1000000 (bridge/make-projector (:world g))))
(deftest native-safety-projection-is-separate-from-existing-safe-single-policy
  (doseq [safety [0 1 2] :let [g (group safety safety) world (:world g) pa (first (:payloads g))
                              ci (:value (bridge/project-with-stats world :definition-val-general pa))]]
    (is (= ({0 1 1 0 2 2} safety) (.safety ^ConstantInfo ci)))
    (is (= ["a"] (mapv str (.all ^ConstantInfo ci))))
    (when (not= safety 1) (is (thrown? Exception (bridge/project-with-stats world :definition-val pa))))))
(deftest unsafe-and-partial-recursive-groups-check-atomically-in-extended-env
  (doseq [safety [0 2] :let [g (group safety safety) before (.enableQuot (Env.)) projector (bridge/make-projector (:world g))
                            result (bridge/admit-mutual-definitions (:world g) before (:declaration g) 1000000 projector)]]
    (is (= 2 (count (:constants result))))
    (is (empty? (.allConstants before)))
    (is (= #{"a" "b"} (set (map #(str (.name ^ConstantInfo %)) (.allConstants ^Env (:env result))))))
    (is (identical? (:declaration g) (:guest-declaration result)))
    (is (every? (fn [^ConstantInfo ci] (identical? ci (.lookupLocal ^Env (:env result) (.name ci)))) (:constants result)))))
(deftest empty-safe-mixed-safety-and-duplicate-groups-reject
  (doseq [[a b] [[1 1] [0 2] [0 1] [2 1]]]
    (is (thrown? Exception (checked (group a b)))))
  (let [g (group 0 0) world (:world g) [world empty] (ctor world 5 [nil-tag] 0)
        [world duplicate-tail] (ctor world 1 [(first (:payloads g)) nil-tag] 0)
        [world duplicate-list] (ctor world 1 [(first (:payloads g)) duplicate-tail] 0)
        [world duplicate] (ctor world 5 [duplicate-list] 0)]
    (doseq [d [empty duplicate]]
      (is (thrown? Exception (bridge/admit-mutual-definitions world (.enableQuot (Env.)) d 1000000 (bridge/make-projector world)))))))
(deftest ill-typed-body-and-malformed-safety-do-not-publish
  (let [g (group 0 0) pa (first (:payloads g)) world (:world g)
        [world zero] (constant world "missing")
        bad-body (assoc-in world [:heap (:id pa) :fields 1] zero)
        bad-safety (byte! world pa 3)]
    (is (thrown? Exception (checked (assoc g :world bad-body))))
    (is (thrown? Exception (bridge/project-with-stats bad-safety :mutual-declaration (:declaration g))))))
(deftest actual-original-payloads-and-unsafe-checking-shape-survive-readback
  (let [g (group 0 0) result (checked g) constants (:constants result)
        candidate {:payloads (into {} (map (fn [^ConstantInfo ci payload]
                                            [(.name ci) {:kind :definition :payload payload :value-projection :definition-val-general}])
                                          constants (:payloads g)))}
        scope {:world (:world g) :projector (bridge/make-projector (:world g))}]
    (with-redefs-fn {#'adapter/descriptor! (fn [& _] {:kind :definition :value-projection :definition-val})
                    #'adapter/fields (fn [_ info] (object-array [info]))}
      #(doseq [[^ConstantInfo ci payload] (map vector constants (:payloads g))]
         (is (nil? (#'adapter/validate-local-info! {} scope candidate (:env result) payload (.name ci))))
         (is (thrown? Exception (#'adapter/validate-local-info! {} scope
                                 (assoc-in candidate [:payloads (.name ci) :payload] (Object.)) (:env result) payload (.name ci))))
         (is (thrown? Exception (#'adapter/validate-local-info! {} scope
                                 (assoc-in candidate [:payloads (.name ci) :kind] :axiom) (:env result) payload (.name ci))))))))
(deftest adapter-candidate-has-all-group-members-in-one-version-snapshot
  (let [g (group 0 0) before (.enableQuot (Env.))
        version {:id 0 :env before :payloads {} :segments []}
        session {:engine (Object.) :basis {} :matched-base (Object.) :source (Object.)
                 :options {:max-declarations 16 :fuel 1000000 :projection-limits (fn [] {})}
                 :published-count (atom 0) :events (atom [])}
        inv (atom {:outer :actual-request :declaration (:declaration g) :payload (:values g)
                   :descriptor {:kind :mutual-definition :declaration-projection :mutual-declaration}})
        guards (atom 0) closed (atom 0)]
    (with-redefs-fn {#'adapter/validate-versions! (fn [_]) #'adapter/validate-candidate! (fn [& _])
                    #'adapter/resolve-base! (fn [& _] version) #'adapter/validate-local-view! (fn [& _])
                    #'adapter/generated-admission! (fn [& _] (swap! guards inc))
                    #'adapter/group-payloads! (fn [& _] (:payloads g))
                    #'base/with-version! (fn [_ env callback] (callback env))
                    #'projection/open-projector (fn [& _] {:world (:world g) :projector (bridge/make-projector (:world g)) :close! #(swap! closed inc)})}
      #(do
         (#'adapter/check-java! session inv)
         (is (= :publish (:stage @inv)))
         (is (= 2 (count (get-in @inv [:candidate :constants]))))
         (is (= 2 (count (get-in @inv [:candidate :payloads]))))
         (is (= 1 (count (get-in @inv [:candidate :segments]))))
         (is (= 1 @guards @closed))
         (is (= [:checked] (mapv :phase @(:events session))))
         (is (zero? @(:published-count session)))
         (is (empty? (.allConstants before)))))))
(deftest generated-admission-needs-issued-active-command-and-live-source-gate
  (let [header (Object.) source (Object.) request {:call {:replyClaimed false}}
        e {:entry {:header header}} context {} session {:engine e :source source}
        capture {:engine e :source source :description {:command-index 0}}
        holder (atom {:status :running :stage :process-command :source source :file-marker (Object.)
                      :frontend {:driver {:engine e :current-ctx (atom context)}}
                      :strict-driver {:adapter session} :capture capture :headers {:entry header}
                      :gate {:stage :replied :receipt :actual-gate :request {:call {:replyClaimed true}}}})
        borrowed (atom 0)]
    (with-redefs-fn {#'command/live! (fn [h] @h) #'command/field (fn [x k] (get x (keyword k)))
                    #'j/phase (fn [& _] "host-call") #'j/host-request (fn [& _] request)
                    #'provider/assert-command-gate! (fn [gate actual-engine actual-source actual-capture]
                                                     (is (= :actual-gate gate)) (is (identical? e actual-engine))
                                                     (is (identical? source actual-source)) (is (identical? capture actual-capture))
                                                     (swap! borrowed inc) nil)}
      #(do
         (is (thrown? Exception (command/assert-generated-admission! session request)))
         (#'command/issue-generated-scope! holder)
         (let [token (:generated-admission-scope @holder)]
           (with-bindings {#'command/*generated-admission* token}
             (is (nil? (command/assert-generated-admission! session request)))
             (is (= 1 @borrowed))
             (is (thrown? Exception (command/assert-generated-admission! (assoc session :other true) request)))
             (swap! holder assoc :stage :cleanup)
             (is (thrown? Exception (command/assert-generated-admission! session request)))
             (swap! holder assoc :stage :process-command)
             (with-redefs [provider/assert-command-gate! (fn [& _] (throw (ex-info "closed or EOF gate" {})))]
               (is (thrown? Exception (command/assert-generated-admission! session request))))
             (#'command/revoke-generated-scope! holder)
             (is (thrown? Exception (command/assert-generated-admission! session request)))))
         (with-bindings {#'command/*generated-admission* (command/->GeneratedAdmissionScope)}
           (is (thrown? Exception (command/assert-generated-admission! session request))))))))
(deftest different-universe-parameters-and-cyclic-lists-reject
  (let [g (group 0 0) pb (second (:payloads g)) world (:world g)
        constant (first (:fields (m/node world pb)))
        [world name] (guest-name world "u") [world params] (ctor world 1 [name nil-tag] 0)
        mismatch (assoc-in world [:heap (:id constant) :fields 1] params)
        cyclic (assoc-in world [:heap (:id (:values g)) :fields 1] (:values g))]
    (is (thrown? Exception (checked (assoc g :world mismatch))))
    (is (thrown? Exception (bridge/project-with-stats cyclic :mutual-declaration (:declaration g))))))
(defn check! [] (run-tests 'generated-mutual-declaration-models-v1))
