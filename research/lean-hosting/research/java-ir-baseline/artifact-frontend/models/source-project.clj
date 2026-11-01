(ns source-module-project-checks-v1
  "Pure bounded plan and explicit orchestration models; no guest execution."
  (:require [clojure.string :as str] [clojure.test :refer [deftest is run-tests]]
            [source-module-project-v1 :as project]
            [general-frontend-source-provider-v1 :as provider]
            [general-command-receipt-v1 :as command]
            [general-generated-batch-v1 :as batch]
            [java-source-module-exchange-v1 :as exchange]
            [heartbeat-lab-options-proof :as options]
            [source-import-frontend-setup-v1 :as imports])
  (:import [java.nio.file Paths]))
(defn capture [segments]
  (let [text "prelude\nimport Init.Prelude\n"]
    {:module segments :text text :path (Paths/get (str (str/join "/" segments) ".lean") (make-array String 0))
     :sha256 (#'provider/hash-text text) :byte-count (alength (.getBytes text "UTF-8"))}))
(defn entry [name deps] {:capture (capture [name]) :dependencies (mapv vector deps)})
(deftest dependency-order-is-bounded-unique-and-explicit
  (let [planned (project/plan-project [(entry "A" []) (entry "B" ["A"]) (entry "C" ["A" "B"])])]
    (is (= 3 (count planned)))
    (is (= [(#'project/module-name! ["A"]) (#'project/module-name! ["B"])] (:dependencies (last planned)))))
  (doseq [bad [[] [(entry "B" ["A"]) (entry "A" [])]
               [(entry "A" ["A"])]]]
    (is (thrown? Exception (project/plan-project bad))))
  (is (thrown? Exception (project/plan-project [(entry "A" []) (entry "A" [])])))
  (is (thrown? Exception (project/plan-project [(entry "A" []) (entry "B" ["A" "A"])])))
  (is (thrown? Exception (project/plan-project (mapv #(entry (str "M" %) []) (range 17)))))
  (is (thrown? Exception (project/plan-project [{:capture (capture ["Init" "Prelude"]) :dependencies []}]))))
(deftest source-capture-digest-and-typed-module-identity-are-not-labels
  (let [e (entry "A" [])]
    (is (thrown? Exception (project/plan-project [(assoc-in e [:capture :sha256] (apply str (repeat 64 "0")))])))
    (is (thrown? Exception (project/plan-project [(assoc-in e [:capture :module] ["A.B"])])))
    (is (not= (#'project/module-name! ["A" "B"]) ["str" ["anonymous"] "A.B"]))))
(defn execution-model [export-fails? f]
  (let [planned (project/plan-project [(entry "A" [])]) events (atom []) commands (atom [:command :eoi])
        frontend {:runtime-step! identity :deadline-nanos 1 :limits {} :owners (atom {})} bundle {:child {:code-receipt ::code} :frontend frontend
                            :setup-result {:status :prepared :session frontend} :admission {}}
        rh (atom {}) operation (exchange/->Operation)
        _ (#'exchange/publish! @#'exchange/operations operation (atom {:runtime-holder rh}))
        holder (atom {:status :open :thread (Thread/currentThread) :runtime ::runtime :runtime-holder rh
                      :files planned :next-file 0 :modules {} :completed [] :active nil})]
    (with-redefs-fn
      {#'project/cell (fn [_] holder) #'project/live! deref
       #'project/imported-scope! (fn [& _] ::scope)
       #'provider/open-provider! (fn [& _] ::provider) #'provider/callbacks (fn [& _] {})
       #'provider/close! (fn [& _] (swap! events conj :provider-close))
       #'command/source-captures (fn [& _] ::captures)
       #'options/rebase-idle-deadline identity
       #'command/open-command! (fn [& _] ::run)
       #'command/run-command! (fn [& _] (let [kind (first @commands)] (swap! commands rest)
                                         {:status :sealed :receipt kind :summary {:kind kind}}))
       #'batch/prepare-batch! (fn [& _] {:status :empty :row-count 0})
       #'command/rebase-idle-deadline! (fn [& _] (swap! events conj :rebase))
       #'command/retire! (fn [& _] (swap! events conj :command-retire) {:status :retired})
       #'exchange/export-module! (fn [_ receipt _ parents]
                                   (is (= :eoi receipt)) (is (empty? parents))
                                   (swap! events conj :export)
                                   (when export-fails? (throw (ex-info "actual export failure model" {:operation operation}))) ::module)
       #'exchange/with-module! (fn [_ callback] (callback {:module (:module (first planned))}))
       #'exchange/retire-file! (fn [& _] (swap! events conj :file-retire) {:status :retired})
       #'batch/close! (fn [& _] (swap! events conj :scope-close))}
      #(f holder events bundle))))
(deftest genuine-eof-stays-owned-through-export-and-file-retirement
  (execution-model false
    (fn [holder events bundle]
      (is (= :exported (:status (project/compile-next! ::project bundle {:headers {} :layout-directory "layout"}))))
      (is (= [:rebase :command-retire :export :file-retire :provider-close :scope-close] @events))
      (is (= 1 (:next-file @holder)))
      (is (nil? (:active @holder)))
      (is (not (:running? @holder)))
      (is (identical? bundle (get-in @holder [:completed 0 :borrowed-frontend-bundle]))))))
(deftest export-failure-preserves-actual-eof-and-resource-journals-without-unwind
  (execution-model true
    (fn [holder events bundle]
      (is (thrown? Exception (project/compile-next! ::project bundle {:headers {} :layout-directory "layout"})))
      (is (= [:rebase :command-retire :export] @events))
      (is (= :failed (:status @holder)))
      (is (= ::run (get-in @holder [:active :command-run])))
      (is (= :eoi (get-in @holder [:active :receipt])))
      (is (not (:running? @holder)))
      (let [detached (project/detach-journal! ::project)]
        (is (identical? bundle (get-in detached [:active :bundle])))
        (is (instance? java_source_module_exchange_v1.Operation (get-in detached [:active :exchange-operation])))
        (is (= #{:status :thread} (set (keys @holder)))))
      (is (thrown? Exception (project/detach-journal! ::project))))))
(deftest rejected-setup-status-stops-before-project-effects
  (execution-model false
    (fn [holder events bundle]
      (is (thrown? Exception (project/compile-next! ::project (assoc-in bundle [:setup-result :status] :boundary)
                              {:headers {} :layout-directory "layout"})))
      (is (empty? @events)) (is (nil? (:active @holder))) (is (= :open (:status @holder))))))
(deftest lazy-dependencies-reject-before-realizing-any-element
  (let [realized (atom 0) dependencies (map (fn [_] (swap! realized inc) (throw (AssertionError. "must not realize"))) (range))]
    (is (thrown? Exception (project/plan-project [(assoc (entry "A" []) :dependencies dependencies)])))
    (is (zero? @realized))))
(deftest prepared-session-allows-only-explicit-wrapper-fields
  (let [session {:owners (atom {}) :in-flight (atom nil) :runtime-step! identity :deadline-nanos 1 :limits {}}
        frontend (assoc session :runtime-step! (fn [_]) :deadline-nanos 2 :limits {:commands 128})
        bundle {:setup {:status :prepared :session session} :frontend frontend}]
    (is (identical? frontend (#'project/prepared-frontend! bundle)))
    (is (thrown? Exception (#'project/prepared-frontend! (assoc-in bundle [:frontend :owners] (atom {})))))
    (is (thrown? Exception (#'project/prepared-frontend! (assoc-in bundle [:setup :status] :boundary))))))
(deftest same-name-different-parent-capability-cannot-satisfy-project-dependency
  (let [parent (Object.) impostor (Object.) selected (atom parent) name (#'project/module-name! ["A"])
        engine (Object.) source (Object.) ctx (atom {}) driver {:engine engine :source source :current-ctx ctx}
        s {:runtime-holder (atom {:engine engine :source source :driver driver})}
        bundle {:child {:driver driver} :admission {:adapter {}} :source-import {:finalized-run ::run :base ::base}}
        opened (atom 0)]
    (with-redefs-fn
      {#'exchange/with-module! (fn [_ callback] (callback {:module name}))
       #'exchange/with-finalized! (fn [_ callback] (callback {:closure ::closure}))
       #'exchange/with-closure! (fn [_ callback] (callback {:requests [{:module exchange/prelude-name} {:module name}]
                                                          :module-roots [@selected]}))
       #'imports/open-generated-scope! (fn [& _] (swap! opened inc) ::scope)}
      #(do
         (is (= ::scope (#'project/imported-scope! s bundle [parent])))
         (reset! selected impostor)
         (is (thrown? Exception (#'project/imported-scope! s bundle [parent])))
         (is (= 1 @opened))))))
(defn check! [] (run-tests 'source-module-project-checks-v1))
