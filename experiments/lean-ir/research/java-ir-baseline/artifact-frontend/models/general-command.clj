(ns general-command-receipt-checks-v1
  "Pure bounds/IR/capability models. No actual parser or CommandReceipt issuance."
  (:require [clojure.test :refer [deftest is run-tests]]
            [general-command-receipt-v1 :as command]
            [generated-command-receipt-v1 :as finite]
            [artifact-checked-declaration-adapter-v4 :as adapter]
            [artifact-declaration-authority-v4 :as authority]
            [sequential-frontend-probe :as sp]
            [java-ir-baseline :as j]
            [ansatz.research.ir.node-decoder-v1 :as decoder]))
(deftest generic-decoder-policy-cannot-exceed-real-decoder-ceilings
  (let [limits (#'command/decode-limits)]
    (doseq [[key value] (dissoc limits :deadline-nanos)]
      (is (and (integer? value) (pos? value) (<= value (get decoder/defaults key)))))
    (is (integer? (:deadline-nanos limits)))
    (is (= 2000000 (:max-chars limits)))))
(deftest complete-ir-map-keeps-empty-code-and-unsupported-execution-kinds
  (let [a ["str" ["anonymous"] "a"] b ["str" ["anonymous"] "b"]
        f {"fdecl" {"f" a "xs" [] "type" "tobject"}}
        e {"extern" {"f" b "xs" [] "type" "tobject"}}]
    (is (= {} (#'command/ir-map! [] 2)))
    (is (= {a {:kind "fdecl" :declaration (get f "fdecl")}
            b {:kind "extern" :declaration (get e "extern")}}
           (#'command/ir-map! [f e] 2)))
    (is (thrown? Exception (#'command/ir-map! [f f] 2)))
    (is (thrown? Exception (#'command/ir-map! [f e] 1)))
    (is (thrown? Exception (#'command/ir-map! [{"unknown" {"f" a}}] 2)))))
(deftest unissued-runs-and-summaries-cannot-authorize-batches
  (doseq [value [nil {} {:status :sealed} (command/->CommandRun) (command/->CommandReceipt)]]
    (is (thrown? Exception (command/with-command! value identity)))
    (is (thrown? Exception (command/owner-packet value)))
    (is (thrown? Exception (command/rebase-idle-deadline! value 60000)))))
(deftest expired-release-preflight-never-publishes-or-claims-native-work
  (let [value (Object.) slot (object-array [value :owned]) owners (doto (java.util.LinkedHashMap.) (.put :final slot))
        holder (atom {:owners owners :frontend {}}) starts (atom 0)]
    (with-redefs-fn {#'finite/live! (fn [h] @h)
                    #'sp/check-time! (fn [_] (throw (ex-info "expired before release" {})))
                    #'finite/new-slot! (fn [& _] (throw (AssertionError. "No new result slot after expired preflight")))
                    #'j/start-release! (fn [& _] (swap! starts inc))}
      #(is (thrown-with-msg? Exception #"expired before release" (#'finite/release-slot! holder :final))))
    (is (zero? @starts)) (is (= :owned (aget slot 1)))
    (is (identical? value (aget slot 0))) (is (nil? (:operation @holder)))))
(deftest idle-deadline-allowance-preserves-counters-and-rejects-active-or-failed-custody
  (let [used (atom {:instructions 42 :commands 2}) in-flight (atom nil)
        frontend {:driver {:engine (Object.) :current-ctx (atom {})} :used used :in-flight in-flight :deadline-nanos 1}
        version (Object.) session {:phase (atom :replied) :invocation (atom nil) :versions (atom [version])
                 :published-count (atom 0) :options {:max-declarations 16}}
        holder (atom {:status :sealed :stage :sealed :operation nil :version version :publication-watermark 0 :frontend frontend :strict-driver {:adapter session}})
        phase (atom "idle") work (atom nil)]
    (with-redefs-fn {#'command/issued (fn [& _] holder) #'command/live! (fn [h] @h)
                    #'j/phase (fn [& _] @phase) #'command/field (fn [& _] @work)
                    #'adapter/validate-versions! (fn [_] nil)}
      #(do
         (is (= {:status :idle-deadline-rebased :milliseconds 60000 :budget @used}
                (command/rebase-idle-deadline! :modeled-run 60000)))
         (is (identical? used (get-in @holder [:frontend :used])))
         (is (identical? in-flight (get-in @holder [:frontend :in-flight])))
         (is (= {:instructions 42 :commands 2} @used))
         (let [deadline (get-in @holder [:frontend :deadline-nanos])]
           (is (not= 1 deadline))
           (reset! phase "running")
           (is (thrown? Exception (command/rebase-idle-deadline! :modeled-run 60000)))
           (reset! phase "idle") (reset! work (Object.))
           (is (thrown? Exception (command/rebase-idle-deadline! :modeled-run 60000)))
           (reset! work nil) (swap! holder assoc :status :failed)
           (is (thrown? Exception (command/rebase-idle-deadline! :modeled-run 60000)))
           (is (= deadline (get-in @holder [:frontend :deadline-nanos]))))))))
(deftest reflected-failures-report-bounded-owner-free-root-diagnostics
  (let [owner (Object.) root (ex-info (apply str (repeat 1000 "x")) {:owner owner})
        _ (.setStackTrace root (into-array StackTraceElement (repeat 20 (StackTraceElement. "Guest" "method" "file" 42))))
        wrapped (java.lang.reflect.InvocationTargetException. (java.lang.reflect.InvocationTargetException. root))
        result (command/failure-summary wrapped)]
    (is (= "clojure.lang.ExceptionInfo" (:class result)))
    (is (= 900 (count (:message result))))
    (is (= 3 (count (:cause-classes result))))
    (is (= :end (:cause-stop result)))
    (is (= 12 (count (:stack result))))
    (is (= #{:class :message :wrapper-class :cause-classes :cause-stop :stack} (set (keys result))))
    (is (= {:class "Guest" :method "method" :file "file" :line 42} (first (:stack result)))))
  (let [a (Exception. "a") b (Exception. "b")]
    (.initCause a b) (.initCause b a)
    (is (= :cycle (:cause-stop (command/failure-summary a))))))
(deftest observed-map-selects-a-retained-branch-instead-of-latest-publication
  (let [maps (repeatedly 4 #(Object.)) metadata (Object.)
        roots (mapv (fn [m] {:view {:constant-map m :const2mod-map metadata :header-fields [:main :imports :extensions]}}) maps)
        versions (mapv (fn [id m k] {:id id :parent (when (pos? id) 0)
                                     :constant-map (object-array [m :association-owned]) :kernel-root (object-array [k :association-owned])})
                       (range 4) maps roots)
        session {:versions (atom versions) :published-count (atom 3) :options {:max-declarations 16}}
        holder (atom {:strict-driver {:adapter session} :frontend {:driver {}}})
        observation {:environment {:view (assoc (:view (nth roots 2)) :header-fields [:updated-main :imports :extensions])}}]
    (with-redefs-fn {#'authority/environment-view! (fn [_ _ e] (:view e))
                    #'authority/kernel-view! (fn [_ _ k] (:view k))}
      #(do
         (is (identical? (nth versions 2) (#'command/final-version! holder observation)))
         (is (thrown? Exception (#'command/final-version! holder
                                 (assoc-in observation [:environment :view :constant-map] (Object.)))))
         (is (thrown? Exception (#'command/final-version! holder
                                 (assoc-in observation [:environment :view :header-fields] [:main :changed :extensions]))))
         (swap! (:versions session) conj (assoc (nth versions 2) :id 4))
         (is (thrown? Exception (#'command/final-version! holder observation)))))
    (reset! (:versions session) versions)
    (let [state {:version (nth versions 2) :publication-watermark 3}]
      (is (nil? (#'command/selected-version-live! state session)))
      (swap! (:versions session) conj {:id 4 :parent 2}) (reset! (:published-count session) 4)
      (is (thrown? Exception (#'command/selected-version-live! state session))))))
(defn check! [] (run-tests 'general-command-receipt-checks-v1))
