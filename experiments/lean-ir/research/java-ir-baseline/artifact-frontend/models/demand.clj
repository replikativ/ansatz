(ns ansatz.research.ir.authenticated-demand-checks
  "Tiny actual Header/CodeRequest checks; source resolver authority is a fixture policy."
  (:require [clojure.test :refer [deftest is run-tests]]
            [java-ir-baseline :as j] [java-ir-baseline-checks :as c]
            [java-ir-extern-checks :as x]
            [ansatz.research.ir.authenticated-demand :as demand]))
(def ^:dynamic *basis* nil)
(def digest (apply str (repeat 64 "a")))
(defn fixture [explicit f]
  (let [ctx (assoc (j/prepare-host-program *basis* [] []) :explicit explicit)
        source (j/source-binding ctx (Object.)) engine (j/machine ctx)
        row (first (x/raw [(c/decl "demandIdentity" [(c/p 1 "object")] "object" (c/ret 1))]))
        live (atom true) calls (atom 0)
        driver {:source source :engine engine :current-ctx (atom ctx) :headers-by-name (atom {}) :requests (atom [])}
        policy {:resolve-row! (fn [actual name]
                               (assert (identical? source (:source actual)))
                               (assert (= (get row "name") (j/lean-name-data name)))
                               {:row row :sha256 digest :source-binding source})
                :check-source! (fn [actual]
                                 (swap! calls inc)
                                 (assert (identical? source (:source actual)))
                                 (when-not @live (throw (ex-info "fixture source lease closed" {}))))}]
    (try (f {:driver (demand/attach driver policy) :source source :row row :policy policy :live live :calls calls})
         (finally (j/close! @(:current-ctx driver) engine)))))
(deftest canonical-memo-is-rechecked-under-live-source-authority
  (fixture true
    (fn [{:keys [driver row live calls]}]
      (let [n (get row "name") h (demand/ensure-header! driver n) count-before @calls]
        (is (identical? h (demand/ensure-header! driver n)))
        (is (> @calls count-before))
        (reset! live false)
        (is (thrown-with-msg? Exception #"source lease closed" (demand/ensure-header! driver n)))
        (is (identical? h (:header (get @(:headers-by-name driver) (demand/exact-name-key n)))))))))
(deftest same-sha-forged-declaration-metadata-cannot-reuse-canonical-memo
  (fixture true
    (fn [{:keys [driver source row]}]
      (let [n (get row "name") key (demand/exact-name-key n)
            forged (j/declaration-header source (assoc-in row ["ir" "fdecl" "info"] {"forged" true}) digest)]
        (swap! (:headers-by-name driver) assoc key {:header forged :sha256 digest})
        (is (thrown-with-msg? Exception #"Canonical Header differs" (demand/ensure-header! driver n)))
        (is (identical? forged (:header (get @(:headers-by-name driver) key))))))))
(deftest foreign-resolver-source-rejects-before-header-memo-publication
  (fixture true
    (fn [{:keys [driver policy]}]
      (let [bad (assoc-in driver [:authenticated-demand :resolve-row!]
                  (fn [d n] (assoc ((:resolve-row! policy) d n) :source-binding (Object.))))]
        (is (thrown-with-msg? Exception #"foreign SourceBinding"
              (demand/ensure-header! bad ["str" ["anonymous"] "demandIdentity"])))
        (is (empty? @(:headers-by-name driver))) (is (empty? @(:requests driver)))))))
(deftest original-body-services-the-actual-request-in-both-drivers
  (doseq [explicit [false true]]
    (fixture explicit
      (fn [{:keys [driver row]}]
        (let [header (demand/ensure-header! driver (get row "name"))
              ctx (j/register-headers @(:current-ctx driver) [header]) e (:engine driver)]
          (j/install-program! ctx e) (reset! (:current-ctx driver) ctx)
          (j/start! ctx e "demandIdentity" [42])
          (when (= "running" (j/phase ctx e)) (j/advance! ctx e 100))
          (is (= "code-call" (j/phase ctx e)))
          (is (= 1 (demand/service-code! driver)))
          (let [ready @(:current-ctx driver)]
            (when (= "running" (j/phase ready e)) (j/advance! ready e 100))
            (is (= "complete" (j/phase ready e)))
            (is (= 42 (j/take-result! ready e)))))))))
(defn check! [basis]
  (binding [*basis* basis] (run-tests 'ansatz.research.ir.authenticated-demand-checks)))
