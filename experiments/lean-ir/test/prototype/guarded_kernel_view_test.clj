(ns prototype.guarded-kernel-view-test
  (:require [clojure.test :refer [deftest is]]
            [prototype.guarded-kernel-view :as view]
            [ansatz.export.storage :as storage]
            [ansatz.export.evidence :as evidence]
            [ansatz.kernel.name :as name]
            [org.replikativ.persistent-sorted-set :as pss])
  (:import [ansatz.kernel Env ConstantInfo Expr Level Name]
           [java.nio ByteBuffer]
           [java.util UUID]))
(def limits
  {:declarations 1 :shell-items 256 :expr-nodes 64 :expr-edges 128 :expr-depth 32
   :raw-bytes 4096 :name-nodes 64 :name-chars 256 :name-depth 32
   :level-nodes 64 :level-depth 32 :level-visits 4096})
(def a (name/from-string "View.a"))
(def b (name/from-string "View.b"))
(defn ci [n] (ConstantInfo/mkAxiom n (object-array []) (Expr/sort Level/ZERO_LEVEL false) false))
(defn policy [resolver & [extra]]
  (merge {:domain #{a b} :quot-enabled? true :lease! (fn []) :authenticate-ci! (fn [_ _])
          :resolve! resolver :max-materialized 2 :evidence-limits limits
          :max-total-usage (into {} (map (fn [[k v]] [k (* 2 v)])) limits)} extra))
(defn open-model [entries & [extra]]
  (view/open-resolver-view! (policy (fn [n _] {:constants (select-keys entries [n]) :usage {:declarations 1}}) extra)))

(deftest every-hit-rechecks-lease-and-close-drops-ledger-without-closing-borrowed-store
  (let [live (atom true) leases (atom 0) reads (atom 0) constant (ci a)
        model (view/open-resolver-view!
                (policy (fn [n _] (swap! reads inc) {:constants {n constant} :usage {:declarations 1}})
                  {:lease! #(do (swap! leases inc) (when-not @live (throw (ex-info "Source lease retired" {}))))}))]
    (try
      (view/with-view! model (fn [^Env env]
                              (is (identical? constant (.lookup env a)))
                              (let [before @leases]
                                (is (identical? constant (.lookup env a)))
                                (is (< before @leases)))))
      (is (= 1 @reads))
      (is (= 1 (:snapshot-count (view/inspect! model))))
      (reset! live false)
      (is (thrown-with-msg? Exception #"retired" (view/with-view! model #(.lookup ^Env % a))))
      (reset! live true)
      (is (thrown-with-msg? Exception #"closed or failed" (view/guard! model)))
      (finally (view/close! model) (view/close! model)))
    (is (true? @live)) ; close did not close the borrowed lease/store
    (is (thrown-with-msg? Exception #"closed or failed" (view/inspect! model)))))

(deftest exact-typed-return-and-domain-membership-are-mandatory
  (doseq [result [{:constants {} :usage {}}
                  {:constants {a (ci b)} :usage {}}
                  {:constants {a (ci a) b (ci b)} :usage {}}]]
    (let [model (view/open-resolver-view! (policy (fn [_ _] result)))]
      (try
        (is (thrown? Exception (view/with-view! model #(.lookup ^Env % a))))
        (is (thrown-with-msg? Exception #"closed or failed" (view/guard! model)))
        (finally (view/close! model)))))
  (let [reads (atom 0) model (view/open-resolver-view! (policy (fn [_ _] (swap! reads inc))))]
    (try
      (is (nil? (view/with-view! model #(.lookup ^Env % (name/from-string "Outside")))))
      (is (zero? @reads))
      (finally (view/close! model)))))

(deftest memo-and-historical-ledger-refuse-ci-and-universe-array-mutations
  (doseq [change! [(fn [^ConstantInfo constant _] (set! (.isUnsafe constant) true))
                   (fn [_ levels] (aset ^objects levels 0 (Level/succ Level/ZERO_LEVEL)))]]
    (let [levels (object-array [Level/ZERO_LEVEL])
          constant (ConstantInfo/mkAxiom a (object-array []) (Expr/mkConst b levels false) false)
          model (open-model {a constant b (ci b)})]
      (try
        (view/with-view! model #(.lookup ^Env % a))
        (view/with-view! model #(.lookup ^Env % b))
        (is (= 2 (:snapshot-count (view/inspect! model))))
        (change! constant levels)
        ;; Guarding an unrelated/historical version still checks the old CI.
        (is (thrown? Exception (view/with-view! model #(.lookup ^Env % b))))
        (finally (view/close! model))))))

(deftest authentication-cannot-publish-a-mutated-value-or-use-an-admission-flag
  (let [constant (ci a) model (open-model {a constant}
                                      {:authenticate-ci! (fn [_ ^ConstantInfo value]
                                                           (set! (.isUnsafe value) true) true)})]
    (try
      (is (thrown-with-msg? Exception #"checking shape changed" (view/with-view! model #(.lookup ^Env % a))))
      (finally (view/close! model)))))

(deftest thread-confinement-outer-local-guards-and-shared-external-identity
  (let [model (open-model {a (ci a) b (ci b)})]
    (try
      (is (instance? Throwable @(future (try (view/guard! model) (catch Throwable cause cause)))))
      (view/with-view! model
        (fn [^Env env]
          (let [local (ci (name/from-string "Local")) child (.addConstant env local)]
            (is (.sameExternalView env child))
            (is (.isQuotEnabled child))
            (is (identical? local (.lookup child (.name local))))
            (is (identical? (.lookup env a) (.lookup child a))))))
      (is (= 1 (:materialized-count (view/inspect! model))))
      (finally (view/close! model)))))

(deftest explicit-count-and-total-evidence-budgets-stop-before-publication
  (doseq [extra [{:max-materialized 1}
                 {:max-total-usage (assoc (into {} (map (fn [[k v]] [k (* 2 v)])) limits) :declarations 1)}]]
    (let [model (open-model {a (ci a) b (ci b)} extra)]
      (try
        (view/with-view! model #(.lookup ^Env % a))
        (is (thrown? Exception (view/with-view! model #(.lookup ^Env % b))))
        (finally (view/close! model))))))

(def roots
  {:env-root (UUID/randomUUID) :env-count 2 :names-root (UUID/randomUUID) :names-count 10
   :levels-root (UUID/randomUUID) :levels-count 1 :exprs-root (UUID/randomUUID) :exprs-count 2
   :dag-storage? true :quot-enabled true})
(deftest captured-store-root-mismatch-stops-before-env-or-any-hydration
  (let [loaded (atom 0)]
    (with-redefs-fn {#'storage/branch-loader (fn [& _] {:branch-meta (assoc roots :exprs-root (UUID/randomUUID))
                                                       :evidence-sources {:shell identity}})
                    #'storage/load-env (fn [& _] (swap! loaded inc))}
      #(is (thrown-with-msg? Exception #"roots differ"
             (view/open-view! {:store :borrowed-store :storage :borrowed-pss} "captured"
               (assoc (policy (fn [_ _])) :expected-roots roots)))))
    (is (zero? @loaded))))

(deftest raw-evidence-limits-are-enforced-before-resolving-a-ci
  (let [sort-raw (.array (doto (ByteBuffer/allocate 5) (.put (byte 1)) (.putInt 0)))
        resolver-calls (atom 0)
        sources {:shell (fn [n] {:tag 0 :name n :lps [] :unsafe? false :type-id 0})
                 :expr (constantly sort-raw) :level (constantly Level/ZERO_LEVEL) :name (constantly a)}
        model (view/open-resolver-view!
                (policy (fn [n bounds]
                          (evidence/materialize [n] sources bounds
                            (fn [& args] (swap! resolver-calls inc) (apply storage/resolve-ci-shell args))))
                  {:evidence-limits (assoc limits :raw-bytes 1)}))]
    (try
      (is (thrown-with-msg? Exception #"Store evidence limit" (view/with-view! model #(.lookup ^Env % a))))
      (is (zero? @resolver-calls))
      (finally (view/close! model)))))

(deftest typed-domain-display-collisions-are-rejected-before-source-reads
  (let [n1 (Name/mkStr Name/ANONYMOUS_NAME "x.y")
        n2 (Name/mkStr (Name/mkStr Name/ANONYMOUS_NAME "x") "y")]
    (is (not= n1 n2))
    (is (= (str n1) (str n2)))
    (is (thrown-with-msg? Exception #"display-key collisions"
          (view/open-resolver-view! (policy (fn [_ _]) {:domain #{n1 n2}}))))))


(deftest actual-captured-branch-services-remain-fixed-after-head-change
  (let [head (atom roots) reads (atom []) authenticated (atom [])
        sort-raw (.array (doto (ByteBuffer/allocate 5) (.put (byte 1)) (.putInt 0)))
        app-raw (.array (doto (ByteBuffer/allocate 9) (.put (byte 3)) (.putInt 0) (.putInt 0)))
        tree (fn [cmp entries] (into (pss/sorted-set* {:cmp cmp}) entries))
        trees {(:env-root roots) (tree storage/name-cmp
                                    [[a {:tag 2 :name a :lps [] :all [a] :type-id 0 :value-id 1}]
                                     [b {:tag 0 :name b :lps [] :unsafe? false :type-id 0}]])
               (:exprs-root roots) (tree storage/id-cmp [[0 sort-raw] [1 app-raw]])
               (:names-root roots) (tree storage/id-cmp [[0 a] [1 b]])
               (:levels-root roots) (tree storage/id-cmp [[0 Level/ZERO_LEVEL]])}]
    ;; Exercise real private branch-loader, load-env and full-ci-evidence. Only
    ;; backend IO is modeled; ordinary CI lookup is never invoked on backing Env.
    (with-redefs [storage/store-get (fn [_ key] (swap! reads conj key) @head)
                  pss/restore-by (fn [_ root _] (or (get trees root) (throw (ex-info "Wrong captured root" {}))))
                  storage/open-store (fn [& _] (throw (ex-info "Must borrow actual store" {})))
                  storage/close-store (fn [& _] (throw (ex-info "Must not close borrowed store" {})))]
      (let [model (view/open-view! {:store :borrowed-store :storage :borrowed-pss} "captured"
                    (assoc (policy nil) :expected-roots roots
                           :authenticate-ci! (fn [requested ^ConstantInfo constant]
                                               (is (= requested (.name constant)))
                                               (is (some? (.value constant)))
                                               (swap! authenticated conj requested))))]
        (try
          (reset! head (assoc roots :env-root (UUID/randomUUID)))
          (view/with-view! model
            (fn [^Env environment]
              (let [^ConstantInfo constant (.lookup environment a)]
                (is (some? (.value constant)))
                (is (= Expr/APP (.tag ^Expr (.value constant))))
                (is (identical? constant (.lookup environment a))))))
          (is (= [a] @authenticated))
          (is (= [[:branches "captured"]] @reads))
          (finally (view/close! model)))))))
