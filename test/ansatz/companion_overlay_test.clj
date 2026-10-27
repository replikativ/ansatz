(ns ansatz.companion-overlay-test
  "Pure companion/session models; no export admission or kernel-validity claim."
  (:require [clojure.test :refer [deftest is]]
            [ansatz.companion-overlay :as overlay]
            [ansatz.attrs :as attrs]
            [ansatz.core :as core]
            [ansatz.session :as session]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [ansatz.simp-index :as si]
            [ansatz.state :as state]
            [ansatz.tactic.simp :as simp]
            [ansatz.tactic.proof :as proof])
  (:import [ansatz.kernel Env]))

(def limits {:rows 100 :items 2000 :scalar-bytes 10000 :base-items 1000 :simp-names 100})
(def names #{"C" "role.first" "role.last" "role.simp" "role.matcher" "role.source" "role.target"})
(def matcher-row {:name "role.matcher" :numParams 0 :numDiscrs 0 :uElimPos nil
                  :discrs [] :overlaps [] :alts []})
(def rows {:attrs [{:kind "simp" :name "role.simp" :prio 1000}
                   {:kind "impl" :name "role.source" :target "role.target"}]
           :matchers [matcher-row]
           :instances [{:class "C" :name "role.first" :priority 1000}
                       {:class "C" :name "role.last" :priority 1000}]})
(defn entry [s p] {:name (name/from-string s) :priority p})
(defn model-session []
  (let [index {(name/from-string "C") [(entry "base.high" 2000) (entry "base.tie" 1000) (entry "base.low" 10)]}
        base (-> (Env.)
                 (env/with-extension :instances index)
                 (env/with-extension :simp-lemmas #{"base.simp"})
                 (env/with-extension :custom {:preserve true})
                 (si/with-captured-index {:store-path "captured" :branch "library"} {:base :trie}))]
    (assoc (session/capture) :env base :instance-index index :synth-cache (atom {:old :cache})
           :store {:store-path "captured" :branch "library" :store-map {:borrowed true}}
           :recall-store-path "captured" :discr-trie {:base :recall}
           :simp-trie {:old :trie} :instance-caches {:old :cache}
           :simp-index-caches {:path base :rules {"base" [:cached]}}
           :simp-caches {:env base :entries {:old :cache}})))
(defn prepare
  ([captured] (overlay/prepare-session captured (:env captured) rows names limits))
  ([captured selected] (overlay/prepare-session captured (:env captured) selected names limits)))
(defn error-data [f] (try (f) nil (catch clojure.lang.ExceptionInfo e (ex-data e))))

(deftest pure-preparation-preserves-base-state-and-orders-later-role-instances
  (let [global-before (session/capture)
        base (model-session)
        prepared (prepare base)
        loaded (:env prepared)
        candidates (get (:instance-index prepared) (name/from-string "C"))]
    (is (instance? ansatz.core.ProofContext prepared))
    (is (= ["base.high" "role.last" "role.first" "base.tie" "base.low"] (mapv (comp str :name) candidates)))
    (is (identical? (:instance-index prepared) (env/get-extension loaded :instances nil)))
    (is (= #{"base.simp" "role.simp"} (env/get-extension loaded :simp-lemmas nil)))
    (is (= {"role.source" "role.target"} (env/get-extension loaded :implemented-by nil)))
    (is (= {:preserve true} (env/get-extension loaded :custom nil)))
    (is (= #{"role.simp"} (si/eager-lemma-names loaded {:base :trie})))
    (is (= #{"base.simp" "role.simp"} (si/eager-lemma-names loaded nil)))
    (is (identical? (si/ensure-simp-trie! (:env base)) (si/ensure-simp-trie! loaded)))
    (doseq [k [:store :recall-store-path :discr-trie]] (is (identical? (get base k) (get prepared k))))
    (is (= {} @(:synth-cache prepared)))
    (is (= {} (:instance-caches prepared)))
    (is (nil? (:simp-trie prepared)))
    (is (nil? (:simp-index-caches prepared)))
    (is (= {:env nil :entries {}} (:simp-caches prepared)))
    (is (= {:old :cache} @(:synth-cache base)))
    (is (identical? (:env global-before) (:env (session/capture))))
    (is (identical? (:instance-index global-before) (:instance-index (session/capture))))))

(deftest normalized-idempotence-preserves-existing-instance-order
  (let [first (prepare (model-session))
        second (prepare first)]
    (is (identical? (:instance-index first) (:instance-index second)))
    (is (= (env/get-extension (:env first) :matcher-info nil)
           (env/get-extension (:env second) :matcher-info nil)))
    (is (= (si/eager-lemma-names (:env first) {}) (si/eager-lemma-names (:env second) {})))))

(deftest local-env-instance-registrations-win-over-stale-global-fallback
  (let [base (model-session)
        local-index (update (:instance-index base) (name/from-string "C") conj (entry "local.user" 1))
        base (assoc base :env (env/with-extension (:env base) :instances local-index))
        prepared (prepare base)]
    (is (= "local.user" (str (:name (last (get (:instance-index prepared) (name/from-string "C")))))))))

(deftest conflicts-and-incomplete-role-closure-fail-without-global-mutation
  (let [base (model-session) global-before (session/capture)
        cases [(assoc-in rows [:attrs 0 :prio] 100)
               (assoc-in rows [:matchers 0 :numParams] 1)
               (assoc-in rows [:instances 0 :priority] 20)
               (update rows :instances conj {:class "role.target" :name "role.first" :priority 1000})
               (assoc-in rows [:attrs 1 :target] "missing")
               (assoc-in rows [:attrs 0 :name] "outside-role")
               (assoc-in rows [:attrs 0] {:kind "simp" :name "role.simp" :prio 1000 :post false :inv false})]
        activated (prepare base)]
    (doseq [selected cases]
      (is (some? (error-data #(prepare activated selected)))))
    (is (identical? (:env global-before) (:env (session/capture))))
    (is (identical? (:instance-index global-before) (:instance-index (session/capture))))))

(deftest all-overlay-budgets-are-explicit-and-enforced
  (let [base (model-session)]
    (doseq [key (keys limits)]
      (is (some? (error-data #(overlay/prepare-session base (:env base) rows names (dissoc limits key)))))
      (is (some? (error-data #(overlay/prepare-session base (:env base) rows names (assoc limits key 0)))))
      (doseq [key [:rows :items :scalar-bytes :base-items]]
        (is (= key (:limit (error-data #(overlay/prepare-session base (:env base) rows names (assoc limits key 1)))))))
      (let [selected (update rows :attrs conj {:kind "simp" :name "role.target" :prio 1000})]
        (is (= :simp-names (:limit (error-data #(overlay/prepare-session base (:env base) selected names (assoc limits :simp-names 1))))))))))

(deftest activation-failure-restores-the-complete-previous-session
  (let [before (session/capture) base (model-session) prepared (prepare base)
        failure (ex-info "injected prepared overlay activation failure" {})
        calls (atom 0)]
    (try
      (with-redefs [si/restore-caches! (fn [_] (when (= 1 (swap! calls inc)) (throw failure)))]
        (is (identical? failure (try (session/activate! prepared) nil (catch Throwable e e)))))
      (is (identical? (:env before) (:env (session/capture))))
      (is (= (:instance-index before) (:instance-index (session/capture))))
      (is (= @(:synth-cache before) @(:synth-cache (session/capture))))
      (finally (session/activate! before)))))

(deftest captured-trie-is-independent-of-later-global-store-index-versions
  (let [captured (model-session) original (si/ensure-simp-trie! (:env captured))
        changed (assoc captured :simp-trie {:source (si/index-source (:env captured))
                                            :trie {:later :branch-index}})]
    (session/with-session changed
      (fn []
        (is (identical? original (si/ensure-simp-trie! (:env captured))))
        (is (= {:later :branch-index}
               (si/ensure-simp-trie! (si/with-index-source (:env captured)
                                       (si/index-source (:env captured))))))))))

(deftest lazy-rule-cache-is-scoped-to-env-identity-and-overlay-priority
  (let [before (session/capture)
        base (:env (model-session))
        declaration (env/mk-axiom (name/from-string "role.simp") []
                                  (ansatz.kernel.Expr/sort ansatz.kernel.Level/ZERO_LEVEL false))
        base (.addConstant ^Env base declaration)
        other (env/with-extension base :simp-priorities {"role.simp" 5})
        calls (atom 0)]
    (try
      (with-redefs-fn {#'si/extract-simp-lemma (delay (fn [_ _ priority]
                                                        (swap! calls inc) [{:priority priority}]))
                       #'si/default-simp-priority (delay 1000)}
        (fn []
          (is (= [{:priority 1000}] (si/rules-for base "role.simp")))
          (is (= [{:priority 1000}] (si/rules-for base "role.simp")))
          (is (= 1 @calls))
          (is (= [{:priority 5}] (si/rules-for other "role.simp")))
          (is (= 2 @calls))))
      (finally (session/activate! before)))))

(deftest both-simp-entry-points-preserve-real-local-registration-through-role-overlay
  ;; Stop at lemma extraction: this tests actual candidate assembly in both
  ;; entry points without claiming the model declarations prove any theorem.
  (let [captured (model-session)
        declaration (env/mk-axiom (name/from-string "local.simp") []
                                  (ansatz.kernel.Expr/sort ansatz.kernel.Level/ZERO_LEVEL false))
        base (.addConstant ^Env (:env captured) declaration)
        [registered _] (attrs/import-attrs base ["{\"kind\":\"simp\",\"name\":\"local.simp\",\"prio\":1000}"])
        _ (is (= #{"local.simp"} (si/eager-lemma-names registered {})))
        loaded (:env (prepare (assoc captured :env registered)))
        [ps _] (proof/start-proof loaded (ansatz.kernel.Expr/sort ansatz.kernel.Level/ZERO_LEVEL false))
        stop (ex-info "candidate assembly observed" {})]
    (doseq [operation [simp/simp simp/simp-all]]
      (let [observed (atom nil)]
        (with-redefs [simp/make-simp-lemmas (fn [_ names] (reset! observed (set names)) (throw stop))]
          (is (identical? stop (try (operation ps []) nil (catch Throwable e e)))))
        (is (contains? @observed "role.simp"))
        (is (contains? @observed "local.simp"))
        (is (not (contains? @observed "base.simp")))))))

(deftest captured-index-and-session-preparation-refuse-another-external-view
  (let [captured (model-session)
        other (.withExternalLookup ^Env (:env captured) (fn [_] nil) 0)]
    (is (some? (error-data #(si/ensure-simp-trie! other))))
    (is (some? (error-data #(overlay/prepare-session captured other rows names limits))))))

(deftest captured-eager-registration-state-is-type-and-size-checked
  (let [captured (model-session)]
    (doseq [bad ["not-a-set" #{:not-a-name}]]
      (let [bad-env (env/with-extension (:env captured) si/eager-overlay-key bad)]
        (is (some? (error-data #(prepare (assoc captured :env bad-env)))))))
    (let [large (env/with-extension (:env captured) si/eager-overlay-key #{(apply str (repeat 10000 "x"))})]
      (is (= :scalar-bytes
             (:limit (error-data #(overlay/prepare-session captured large rows names limits))))))))

(deftest equation-owner-overlay-is-idempotent-and-rejects-conflicting-order
  (let [base (model-session)
        selected (assoc rows :attrs [{:kind "unfold-thms" :name "role.source"
                                     :theorems ["role.first" "role.last"]}])
        prepared (prepare base selected)]
    (is (= ["role.first" "role.last"]
           (get (env/get-extension (:env prepared) :simp-unfold-thms {}) "role.source")))
    (is (= (env/get-extension (:env prepared) :simp-unfold-thms {})
           (env/get-extension (:env (prepare prepared selected)) :simp-unfold-thms {})))
    (is (some? (error-data #(prepare prepared
                                    (assoc-in selected [:attrs 0 :theorems]
                                              ["role.last" "role.first"])))))))
