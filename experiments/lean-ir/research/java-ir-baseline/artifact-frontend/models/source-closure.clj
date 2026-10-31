(ns source-closure-checks-v1
  "DAG/control/owner models only; no genuine ModuleData/finalizer is fabricated."
  (:require [clojure.test :refer [deftest is run-tests]]
            [java-source-closure-v1 :as closure]
            [java-source-module-exchange-v1 :as exchange]
            [java-prelude-finalizer-lineage-v1 :as lineage]))
(defn name-of [s] ["str" ["anonymous"] s])
(defn graph-model [f]
  (let [runtime (atom {}) records (atom {})
        make (fn [name parents]
               (let [key (Object.)] (swap! records assoc key {:runtime-holder runtime :file-retired true
                                                             :module (name-of name) :parents parents}) key))]
    (with-redefs-fn {#'exchange/module! (fn [key _] (or (get @records key) (throw (ex-info "Unissued model node" {}))))}
      #(f {:runtime runtime :records records :make make}))))
(deftest source-diamond-preserves-exact-dependency-first-order
  (graph-model
    (fn [{:keys [runtime make]}]
      (let [a (make "A" []) b (make "B" [a]) c (make "C" [a]) d (make "D" [b c])]
        (is (= [a b c d] (#'closure/plan! runtime [d])))
        (is (= [a c b] (#'closure/plan! runtime [c b])))
        (is (thrown? Exception (#'closure/plan! runtime [b b])))))))
(deftest cycles-conflicting-versions-and-unretired-modules-reject
  (graph-model
    (fn [{:keys [runtime records make]}]
      (let [a (make "A" []) b (make "B" [a])]
        (swap! records assoc-in [a :parents] [b])
        (is (thrown? Exception (#'closure/plan! runtime [b]))))
      (let [a1 (make "Same" []) a2 (make "Same" []) b (make "Left" [a1]) c (make "Right" [a2])]
        (is (thrown? Exception (#'closure/plan! runtime [b c]))))
      (let [a (make "NotRetired" [])]
        (swap! records assoc-in [a :file-retired] false)
        (is (thrown? Exception (#'closure/plan! runtime [a])))))))
(deftest explicit-module-depth-and-prefix-conflict-bounds-reject
  (graph-model
    (fn [{:keys [runtime make records]}]
      (let [chain (reduce (fn [previous i] (make (str "M" i) (if previous [previous] []))) nil (range 17))]
        (is (thrown? Exception (#'closure/plan! runtime [chain]))))
      (let [prefix (make "Prefix" [])]
        (swap! records assoc-in [prefix :module] exchange/prelude-name)
        (is (thrown? Exception (#'closure/plan! runtime [prefix])))))))
(deftest returned-finalizer-failure-quarantines-without-owner-discharge
  (let [runtime (atom {:status :open :active (Object.)}) slot (object-array [(Object.) :owned])
        holder (atom {:status :finalizing :runtime-holder runtime :regions-slot slot})
        c (exchange/->SourceClosure) r (exchange/->FinalizedSourceRun)]
    (#'closure/put! @#'closure/closures c holder)
    (#'closure/put! @#'closure/runs r {:closure c :lineage-run ::modeled})
    (with-redefs [lineage/poll! (fn [& _] {:status :failed :failure {:message "modeled"}})]
      (is (= :failed (:status (closure/poll-finalizer! r 1)))))
    (is (= :failed (:status @holder)))
    (is (= :failed (:status @runtime)))
    (is (nil? (:active @runtime)))
    (is (= :owned (aget slot 1)))))
(deftest prepared-closure-owner-transfer-is-once-and-compacts-runtime-anchors
  (let [value (Object.) slots (repeatedly 3 #(object-array [value :owned]))
        rh (atom {:status :open}) holder (atom (zipmap [:state-slot :imports-slot :regions-slot] slots))
        token (exchange/->SourceClosure)]
    (swap! holder assoc :status :prepared :runtime-holder rh)
    (#'closure/put! @#'closure/closures token holder)
    (with-redefs-fn {#'exchange/runtime! deref
                    #'exchange/known-owned-slots! (fn [_ values] (vec (filter #(= :owned (aget ^objects % 1)) values)))}
      (fn []
        (let [packet (closure/take-closure-retirement-owners! token)]
          (is (= 3 (count packet)))
          (is (every? #(identical? value %) packet)))
        (is (every? #(= :external-retirement (aget ^objects % 1)) slots))
        (is (= #{:status :retirement-output} (set (keys @holder))))
        (is (thrown? Exception (closure/take-closure-retirement-owners! token)))))))
(deftest source-finalization-needs-its-private-runtime-marker
  (let [marker (Object.) rh (atom {:status :open :active marker})
        holder (atom {:status :finalizing :runtime-holder rh :attempt-marker marker :selected []
                      :regions-slot (object-array [(Object.) :owned])})]
    (with-redefs-fn {#'exchange/runtime! deref}
      (fn []
        (is (identical? @rh (#'closure/cheap-lease! holder)))
        (swap! rh assoc :active (Object.))
        (is (thrown? Exception (#'closure/cheap-lease! holder)))))))

(deftest invalid-poll-budget-rejects-before-custody-or-quarantine
  (let [marker (Object.) runtime (atom {:status :open :active marker})
        slot (object-array [(Object.) :owned]) holder (atom {:status :finalizing :runtime-holder runtime :regions-slot slot})
        c (exchange/->SourceClosure) r (exchange/->FinalizedSourceRun) calls (atom 0)]
    (#'closure/put! @#'closure/closures c holder)
    (#'closure/put! @#'closure/runs r {:closure c :lineage-run ::modeled})
    (with-redefs [lineage/poll! (fn [& _] (swap! calls inc) {:status :budget})]
      (doseq [budget [nil 0 -1 20001 100000 1.5 "100"]]
        (is (thrown? Exception (closure/poll-finalizer! r budget)))
        (is (= :finalizing (:status @holder)))
        (is (= :open (:status @runtime)))
        (is (identical? marker (:active @runtime)))
        (is (= :owned (aget slot 1))))
      (is (zero? @calls))
      (is (= :budget (:status (closure/poll-finalizer! r 20000))))
      (is (= 1 @calls)))))

(defn check! [] (run-tests 'source-closure-checks-v1))
