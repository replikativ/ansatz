(ns prototype.klara-branch-generated
  "Trusted bounded frontend fixture. Only two explicit lab externs are adapted;
   all generated caller, closure, branch and reference-count instructions survive."
  (:require [prototype.import-ir :as ir]
            [prototype.runtime-abi :as abi]
            [prototype.machine :as m]
            [prototype.coherent-owner-ledger :as owners]))

(def fixture-path "fixtures/klara-branch-ref-closure.jsonl")

(defn- lab-extern [row symbol]
  (let [ext (get-in row [:ir :extern])
        choose? (= symbol "klara_branch_choose")
        expected (if choose?
                   [["tobject" true] ["object" true] ["void" false]]
                   [["tobject" false] ["void" false]])
        params (mapv #(get-in % [:x :idx]) (:xs ext))
        dest (inc (apply max params)) result (inc dest)]
    (when-not (and (= "object" (:type ext))
                   (= expected (mapv (juxt :ty :borrow) (:xs ext))))
      (m/fail "Unexpected lab extern ABI" {:symbol symbol :extern ext}))
    [(:f ext)
     {:params params
      :body [:host (if choose? :lab/choose :lab/emit)
             (mapv #(vector :var %) (if choose? (take 2 params) (take 1 params)))
             dest
             [:let result [:ctor 0 [(if choose? [:var dest] [:imm 0])]]
              [:return [:var result]]]]}]))

(defn functions []
  (let [catalogue (ir/index-bundles [fixture-path])
        entry (first (filter #(= "KlaraBranch.entry" (ir/name-label %))
                             (keys (:declarations catalogue))))]
    (ir/load-closure catalogue [entry]
                     (fn [row]
                       (let [symbol (some-> row :ir :extern abi/symbol-for)]
                         (if (contains? #{"klara_branch_choose" "klara_branch_emit"} symbol)
                           (lab-extern row symbol)
                           (abi/lower row)))))))

(defn fixture []
  (let [functions (functions)
        entry (first (filter #(= "KlaraBranch.entry" (ir/name-label %)) (keys functions)))
        world (m/run (m/start (m/world functions) entry [m/erased]) 10000)
        {:keys [symbol arguments]} (:host-request world)
        [cell closure] arguments]
    (when-not (and (= :host-call (:status world)) (= :lab/choose symbol)
                   (= 2 (count arguments))
                   (= :ref (:kind (m/node world cell)))
                   (= :closure (:kind (m/node world closure)))
                   (= [cell] (:fields (m/node world closure)))
                   (= 2 (:rc (m/node world cell)))
                   (= 1 (:rc (m/node world closure))))
      (m/fail "Generated fixture did not preserve the reference/closure alias" {}))
    {:world world :cell cell :closure closure :functions functions}))

(defn result-value [world]
  (when-not (= :done (:status world)) (m/fail "Expected completed fixture" {}))
  (let [node (m/node world (:result world))]
    (when-not (and (= :ctor (:kind node)) (= 0 (:tag node)) (= 1 (count (:fields node))))
      (m/fail "Expected successful IO result" {}))
    (first (:fields node))))

(defn dispose-result
  "Drop the returned guest owner, then retire non-owning completed control data.
   Dead register slots can contain freed refs; they are not guest roots."
  [world]
  (result-value world)
  (-> (m/release world (:result world) 1)
      (dissoc :result :body :locals :joins :frames :resume-var :host-request)
      (assoc :status :disposed)))


(defn result-disposal-ledger
  "Record the actual trusted fixture return BEFORE checking its shape.
   This host ledger is distinct from family adoption and supplies no authority."
  [world]
  (atom {:unsafe-partial? false :returned-world world
         :returned-owner (:result world)}))

(defn- disposable-fixture-result! [world]
  (let [value (result-value world) result (:result world)
        node (m/node world result)]
    (when-not (and (integer? value) (<= 0 value 9007199254740991)
                   (= #{(:id result)} (set (keys (:heap world))))
                   (= 1 (:rc node)) (empty? (:frames world)))
      (m/fail "Only the sole returned scalar fixture owner can be disposed" {})))
  world)

(defn dispose-recorded-result!
  "Use the existing owner ledger for this one returned owner only. Escrow the
   actual disposed World before post-validation; failures never replay drops.
   This is neither a resident Context nor an atomic family/owner transaction."
  ([state key] (dispose-recorded-result! state key (constantly true)))
  ([state key validate]
   (locking state
     (if (contains? @state :result-disposal-key)
       (when-not (= key (:result-disposal-key @state))
         (m/fail "Returned owner already has a disposal operation key" {}))
       (swap! state assoc :result-disposal-key key)))
   (owners/operation! state key
     (fn []
       ;; Validate the captured World before ANY drop; reject resource payloads,
       ;; extra owners, unfinished guests, and invalid result representations.
       (dispose-result (disposable-fixture-result! (:returned-world @state))))
     (fn [disposed]
       (when-not (and (= :disposed (:status disposed)) (empty? (:heap disposed)))
         (m/fail "Fixture owner cleanup did not finish" {}))
       (validate disposed)))))
