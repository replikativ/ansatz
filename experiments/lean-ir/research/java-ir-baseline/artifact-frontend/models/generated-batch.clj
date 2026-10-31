(ns general-generated-batch-models-v1
  "Host metadata/link transaction models. Canonical Java validation and genuine
   CommandReceipt issuance are modeled explicitly, not runtime acceptance."
  (:require [clojure.test :refer [deftest is run-tests]]
            [general-generated-batch-v1 :as batch]
            [general-command-receipt-v1 :as command]
            [java-ir-baseline :as j]
            [ansatz.research.ir.source-setup :as source]
            [ansatz.research.ir.authenticated-demand :as demand]))
(defn n [s] ["str" ["anonymous"] s])
(defn row [name body] {:kind "fdecl" :declaration {"f" name "xs" [] "type" "tobject" "body" body}})
(defn fap [name] {"fap" {"c" name "ys" []}})
(defn pap [name] {"pap" {"c" name "ys" []}})
(defn model [f]
  (let [src (Object.) code (Object.) adapter (Object.) marker (atom (Object.))
        original-name (n "Original")
        original {"name" original-name "source" src}
        originals (atom {original-name original})
        baseline {:functions [{"header" original}]}
        engine (atom {"program" baseline}) ctx (atom {:program baseline}) events (atom [])
        leases (atom true) receipts (atom {}) install-failure (atom false) file-marker (Object.) command-index (atom -1)
        driver {:engine engine :source src :current-ctx ctx
                :authenticated-demand {:check-source! (fn [_] (assert @leases))}}
        header! (fn [source raw sha] {"source" source "name" (get raw "name") "raw" raw "sha" sha})
        receipt! (fn [before after]
                   (let [token (Object.)]
                     (swap! receipts assoc token {:driver driver :engine engine :source src :source-receipt code
                                                 :adapter adapter :version-marker @marker :version-id 1
                                                 :file-marker file-marker :command-index (swap! command-index inc)
                                                 :source-policy {:profile :observed-classic-prelude-command-v1 :kind :command
                                                                 :requirements-policy :no-local-initializers-exports-externs-redirects-v1}
                                                 :before-ir before :after-ir after :delta (apply dissoc after (keys before))}) token))]
    (with-redefs-fn
      {#'batch/field (fn [x k] (let [v (if (instance? clojure.lang.IDeref x) @x x)]
                               (get v k (get v (keyword k)
                                 (when (contains? #{"closed" "disposed" "untrackedFailure" "advancing"} k) false)))))
       #'j/phase (fn [& _] "idle") #'j/request-value get #'j/declaration-header header!
       #'source/lookup-entry (fn [receipt name] (assert (identical? code receipt)) (get @originals name))
       #'demand/ensure-header! (fn [d name]
                                (assert (identical? driver d))
                                (or (get @originals name) (throw (ex-info "Unknown original target" {}))))
       #'command/with-command!
       (fn [token binding callback]
         (let [view (get @receipts token)]
           (assert view "Actual model receipt required")
           (assert (and @leases (identical? engine (:engine binding)) (identical? src (:source binding))
                        (identical? adapter (:adapter binding)) (identical? ctx (:current-ctx binding))
                        (identical? @marker (:version-marker view))))
           (try (callback view)
                (finally (assert @leases) (assert (identical? @marker (:version-marker view)))))))
       #'j/register-headers
       (fn [c headers]
         (swap! events conj [:register (mapv #(get % "name") headers)])
         (update-in c [:program :functions]
           (fn [old]
             (reduce (fn [out h]
                       (if-let [present (some #(when (= (get h "name") (get-in % ["header" "name"])) %) out)]
                         (do (assert (identical? h (get present "header"))) out)
                         (conj out {"header" h}))) old headers))))
       #'j/materialize-body
       (fn [c h raw dependencies]
         (swap! events conj [:body (get h "name") (mapv #(get % "name") dependencies)
                            (set (map #(get-in % ["header" "name"]) (get-in c [:program :functions])))])
         (when (get-in raw ["ir" "fdecl" "reject-model"]) (throw (ex-info "Modeled Java validator rejected body" {})))
         (update-in c [:program :bodies] (fnil conj []) (get h "name")))
       #'j/install-program!
       (fn [c e]
         (swap! events conj [:install])
         (when @install-failure (throw (ex-info "Uncertain modeled install" {})))
         (swap! e assoc "program" (:program c)))}
      #(f {:driver driver :adapter adapter :scope (batch/open-scope! driver adapter)
           :ctx ctx :engine engine :baseline baseline :events events :receipt! receipt! :receipts receipts
           :leases leases :marker marker :originals originals :original original-name :install-failure install-failure}))))

(deftest complete-scc-and-dynamic-frontier-preregistered
  (model
    (fn [{:keys [scope receipt! events ctx baseline original]}]
      (let [a (n "arbitraryPrivateHelper") b (n "Second")
            rows {a (row a ["vdecl" (fap b) (pap original) {"ap" {"x" 1 "ys" []}}])
                  b (row b ["vdecl" (fap a) (fap b)])}
            prepared (batch/prepare-batch! scope (receipt! {} rows))]
        (is (= :prepared (:status prepared)))
        (is (= 2 (:row-count prepared)))
        (is (= 1 (:dynamic-ap-count prepared)))
        (is (identical? baseline (:program @ctx)))
        (is (= :register (ffirst @events)))
        (doseq [[_ name deps present] (filter #(= :body (first %)) @events)]
          (is (every? present [a b original]))
          (is (not (some #{name} deps))))
        (is (= {:status :linked :row-count 2} (batch/link-batch! (:batch prepared))))
        (is (= 1 (count (filter #(= :install (first %)) @events))))
        (is (thrown? Exception (batch/link-batch! (:batch prepared))))))))

(deftest successive-batches-reuse-canonical-earlier-local-header
  (model
    (fn [{:keys [scope receipt! events]}]
      (let [a (n "One") b (n "Two") first-ir {a (row a ["ret" "erased"])}
            first-batch (batch/prepare-batch! scope (receipt! {} first-ir))]
        (batch/link-batch! (:batch first-batch))
        (let [second-ir (assoc first-ir b (row b ["vdecl" (pap a)]))
              second-batch (batch/prepare-batch! scope (receipt! first-ir second-ir))]
          (is (= :prepared (:status second-batch)))
          (is (= [a] (nth (last (filter #(= :body (first %)) @events)) 2)))
          (is (= :linked (:status (batch/link-batch! (:batch second-batch))))))))))

(deftest empty-and-unsupported-commands-preserve-history
  (model
    (fn [{:keys [scope receipt! ctx baseline]}]
      (is (= {:status :empty :row-count 0} (batch/prepare-batch! scope (receipt! {} {}))))
      (let [a (n "Unexecutable") ir {a {:kind "extern" :declaration {"f" a}}}]
        (is (= :unsupported (:status (batch/prepare-batch! scope (receipt! {} ir)))))
        (is (identical? baseline (:program @ctx)))
        (let [b (n "Independent") next-ir (assoc ir b (row b ["ret" "erased"]))]
          (is (= :prepared (:status (batch/prepare-batch! scope (receipt! ir next-ir))))))))))

(deftest failed-materialization-never-installs-a-partial-program
  (model
    (fn [{:keys [scope receipt! events ctx baseline]}]
      (let [a (n "A") b (n "Z") rows {a (row a ["ret" "erased"])
                                                     b (assoc-in (row b ["ret" "erased"]) [:declaration "reject-model"] true)}
            result (batch/prepare-batch! scope (receipt! {} rows))]
        (is (= :unsupported (:status result)))
        (is (nil? (:batch result)))
        (is (= 2 (count (filter #(= :body (first %)) @events))))
        (is (not-any? #(= :install (first %)) @events))
        (is (identical? baseline (:program @ctx)))))))

(deftest rejects-forged-receipts-incomplete-history-and-display-collisions
  (model
    (fn [{:keys [scope receipt! receipts]}]
      (is (thrown? AssertionError (batch/prepare-batch! scope {:verified true :delta {}})))
      (let [a (n "A") old {a (row a ["ret" "erased"])}]
        (is (thrown? Exception (batch/prepare-batch! scope (receipt! old old))))
        (let [receipt (receipt! {} old)]
          (swap! receipts assoc-in [receipt :delta] {})
          (is (thrown? Exception (batch/prepare-batch! scope receipt)))))
      (let [num ["num" ["anonymous"] "7"] str (n "7")]
        (is (thrown? Exception (batch/prepare-batch! scope (receipt! {} {num (row num []) str (row str [])}))))))))

(deftest overlap-unresolved-dependencies-and-unwitnessed-policy-are-not-executable
  (model
    (fn [{:keys [scope receipt! receipts original]}]
      (is (= :unsupported (:status (batch/prepare-batch! scope (receipt! {} {original (row original [])})))))))
  (model
    (fn [{:keys [scope receipt!]}]
      (let [a (n "A")]
        (is (= :unsupported (:status (batch/prepare-batch! scope (receipt! {} {a (row a [(fap (n "NotAdmitted"))])}))))))))
  (model
    (fn [{:keys [scope receipt! receipts]}]
      (let [receipt (receipt! {} {})]
        (swap! receipts assoc-in [receipt :source-policy] {:verified true})
        (is (thrown? Exception (batch/prepare-batch! scope receipt)))))))

(deftest stale-version-program-and-revocation-stop-linkage
  (model
    (fn [{:keys [scope receipt! marker events]}]
      (let [a (n "A") prepared (batch/prepare-batch! scope (receipt! {} {a (row a [])}))]
        (reset! marker (Object.))
        (is (thrown? AssertionError (batch/link-batch! (:batch prepared))))
        (is (not-any? #(= :install (first %)) @events)))))
  (model
    (fn [{:keys [scope receipt! ctx engine events]}]
      (let [a (n "A") prepared (batch/prepare-batch! scope (receipt! {} {a (row a [])}))
            other (assoc (:program @ctx) :foreign true)]
        (swap! ctx assoc :program other) (swap! engine assoc "program" other)
        (is (thrown? Exception (batch/link-batch! (:batch prepared))))
        (is (not-any? #(= :install (first %)) @events)))))
  (model
    (fn [{:keys [scope receipt!]}]
      (let [a (n "A") prepared (batch/prepare-batch! scope (receipt! {} {a (row a [])}))]
        (batch/close! scope)
        (is (thrown? Exception (batch/link-batch! (:batch prepared))))))))

(deftest actual-install-failure-quarantines-scope
  (model
    (fn [{:keys [scope receipt! install-failure events]}]
      (let [a (n "A") prepared (batch/prepare-batch! scope (receipt! {} {a (row a [])}))]
        (reset! install-failure true)
        (is (thrown? Exception (batch/link-batch! (:batch prepared))))
        (is (thrown? Exception (batch/link-batch! (:batch prepared))))
        (is (= 1 (count (filter #(= :install (first %)) @events))))))))

(defn check! [] (run-tests 'general-generated-batch-models-v1))

(deftest weak-registry-values-do-not-retain-issued-scope-or-batch-tokens
  (model
    (fn [{:keys [scope receipt!]}]
      (let [name (n "A") prepared (batch/prepare-batch! scope (receipt! {} {name (row name [])}))
            token (:batch prepared)
            sh (.get ^java.util.WeakHashMap @#'batch/scopes scope)
            bh (.get ^java.util.WeakHashMap @#'batch/batches token)
            nested (tree-seq coll? seq @sh)]
        (is (not-any? #(or (identical? scope %) (identical? token %)) nested))
        (is (identical? sh (:scope-holder @bh)))
        (batch/link-batch! token)
        (is (not (contains? @bh :receipt)))
        (batch/close! scope)
        (is (= #{:status :thread} (set (keys @sh))))
        (is (= #{:status :scope-holder} (set (keys @bh))))))))

(deftest unchanged-old-rows-and-unregistered-original-names-remain-protected
  (model
    (fn [{:keys [scope receipt!]}]
      (let [a (n "A") initial {a (row a ["ret" "erased"])}
            prepared (batch/prepare-batch! scope (receipt! {} initial))]
        (batch/link-batch! (:batch prepared))
        (is (thrown? Exception
              (batch/prepare-batch! scope (receipt! initial (assoc-in initial [a :declaration "body"] ["unreachable"]))))))))
  (model
    (fn [{:keys [scope receipt! originals]}]
      (let [a (n "UnregisteredOriginal")]
        (swap! originals assoc a ::authenticated-original-row)
        (is (= :unsupported (:status (batch/prepare-batch! scope (receipt! {} {a (row a [])})))))))))

(deftest inherited-headerless-program-and-source-revocation-are-rejected
  (is (thrown? Exception (#'batch/program-index {:functions [{"header" nil}]} (Object.))))
  (model
    (fn [{:keys [scope receipt! leases events]}]
      (let [a (n "A") prepared (batch/prepare-batch! scope (receipt! {} {a (row a [])}))]
        (reset! leases false)
        (is (thrown? AssertionError (batch/link-batch! (:batch prepared))))
        (is (not-any? #(= :install (first %)) @events))))))

(deftest zero-code-replay-foreign-files-and-skipped-command-indices-are-rejected
  (model
    (fn [{:keys [scope receipt! receipts]}]
      (let [first (receipt! {} {})]
        (is (= :empty (:status (batch/prepare-batch! scope first))))
        (is (thrown? Exception (batch/prepare-batch! scope first)))
        (let [second (receipt! {} {})]
          (swap! receipts assoc-in [second :file-marker] (Object.))
          (is (thrown? Exception (batch/prepare-batch! scope second)))))))
  (model
    (fn [{:keys [scope receipt! receipts]}]
      (let [receipt (receipt! {} {})]
        (swap! receipts assoc-in [receipt :command-index] 1)
        (is (thrown? Exception (batch/prepare-batch! scope receipt)))))))

(deftest issuer-post-check-failure-after-install-quarantines-published-branch
  (model
    (fn [{:keys [scope receipt! leases events]}]
      (let [a (n "A") prepared (batch/prepare-batch! scope (receipt! {} {a (row a [])}))
            original command/with-command!]
        (with-redefs [command/with-command!
                      (fn [receipt binding callback]
                        (original receipt binding
                          (fn [view]
                            (let [result (callback view)]
                              (when (= :linked (:status result)) (reset! leases false)) result))))]
          (is (thrown? AssertionError (batch/link-batch! (:batch prepared)))))
        (is (= 1 (count (filter #(= :install (first %)) @events))))
        (let [holder (.get ^java.util.WeakHashMap @#'batch/scopes scope)]
          (is (= :failed (:status @holder))))))))
