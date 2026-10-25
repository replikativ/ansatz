(ns prototype.continuation-readiness-test
  "Host-only modeled continuations: never restore Source or execute guest code."
  (:require [clojure.test :refer [deftest is]]
            [prototype.resident-init-prefix :as prefix]
            [prototype.eval-const :as executable]))
(defn pv [n] (ns-resolve 'prototype.resident-init-prefix n))
(defn model [root]
  (let [leaf {:body [:return [:literal 1]]}
        functions {:root root :leaf leaf}
        source {:closed (atom false)} anchor {:id :anchor} env (Object.)
        p {:id :prefix} prefix {:state p :checked-env env :source source :checked-anchor anchor}
        binding (Object.) configuration {:trusted-functions functions :trusted-bindings {'host binding}}
        world {:functions functions :source-import-prefixes {:prefix prefix} :native-imports [source]
               :kernel-environments {:anchor {:anchor anchor :env env}}}]
    {:world world :session {:functions functions :bindings {'host binding}}
     :prefix prefix :certificate {:env env} :configuration configuration}))
(defn with-roots [f]
  (with-redefs-fn {(pv 'preparation-roots) [:root]
                  (ns-resolve 'prototype.resident-import 'import-roots) []
                  (pv 'source-graph-roots) [:root]}
    f))
(defn check-ready [state] ((pv 'continuation-readiness!) @state state))
(deftest identity-and-full-boundary
  (with-roots
    (fn []
      (let [s (atom (model {:body [:tail [:direct :leaf] []]})) calls (atom 0)
            original executable/validate-executables!]
        (with-redefs [executable/validate-executables! (fn [& args] (swap! calls inc) (apply original args))]
          (is (true? (check-ready s))) (is (true? (check-ready s))) (is (= 1 @calls))
          (is (= #{:functions :registry :graph? :preparation-roots :import-roots :graph-roots}
                 (set (keys (:readiness-stamp @s)))))
          ;; Equal maps with different identity invalidate independently.
          (let [f (into (hash-map) (get-in @s [:world :functions]))]
            (is (not (identical? f (get-in @s [:world :functions]))))
            (swap! s assoc-in [:world :functions] f) (swap! s assoc-in [:session :functions] f))
          (check-ready s) (is (= 2 @calls))
          (swap! s update-in [:configuration :trusted-functions] #(into (hash-map) %))
          (check-ready s) (is (= 3 @calls))
          ((pv 'continuation-readiness!) @s) (is (= 4 @calls))
          (let [other (atom (dissoc @s :readiness-stamp))] (check-ready other) (is (= 5 @calls))))))))
(deftest mutable-runtime-falls-back
  (with-roots
    (fn []
      (let [targets (object-array [:leaf]) s (atom (model {:body [:return [:literal 0]]
                                                         :runtime-dependencies (seq targets)}))]
        (check-ready s) (is (nil? (:readiness-stamp @s)))
        (aset targets 0 :unauthorized)
        (is (thrown-with-msg? clojure.lang.ExceptionInfo #"authorized program" (check-ready s)))
        (is (nil? (:readiness-stamp @s)))))))
(deftest mutable-body-falls-back-without-extra-reads
  (with-roots
    (fn []
      (let [reads (atom 0) target (atom :leaf)
            arms (reify clojure.lang.Seqable
                   (seq [_] (swap! reads inc) (seq [[0 [:tail [:direct @target] []]]])))
            s (atom (model {:body [:case [:literal 0] arms]}))]
        (check-ready s) (is (nil? (:readiness-stamp @s))) (is (= 1 @reads))
        (reset! target :unauthorized)
        (is (thrown? clojure.lang.ExceptionInfo (check-ready s))) (is (= 2 @reads))))))
(deftest live-scaffold-still-checked
  (with-roots
    (fn []
      (doseq [change [(fn [s] (reset! (get-in s [:prefix :source :closed]) true) s)
                      #(assoc-in % [:session :bindings 'host] (Object.))
                      #(assoc-in % [:world :kernel-environments :anchor :env] (Object.))
                      #(assoc-in % [:session :functions] {})]]
        (let [s (atom (model {:body [:return [:literal 0]]}))]
          (check-ready s) (is (some? (:readiness-stamp @s)))
          (swap! s change) (is (thrown? clojure.lang.ExceptionInfo (check-ready s))))))))
(deftest graph-profile-still-checked
  (with-roots
    (fn []
      (let [profile {:token (Object.)} s (atom (assoc (model {:body [:return [:literal 0]]})
                                               :graph-operation? true
                                               :source-graph {:profile :issued :profile-data profile :profile-token (:token profile)}))
            calls (atom 0) original executable/validate-executables!]
        (with-redefs-fn {(pv 'graph-profile!) (fn [_] profile)
                        #'executable/validate-executables! (fn [& a] (swap! calls inc) (apply original a))}
          (fn []
            (check-ready s) (check-ready s) (is (= 2 @calls))
            (swap! s assoc-in [:source-graph :profile-token] (Object.))
            (is (thrown? clojure.lang.ExceptionInfo (check-ready s)))
            (is (= 2 @calls))))))))

(deftest failure-clears-proof-and-root-change-invalidates
  (with-roots
    (fn []
      (let [s (atom (model {:body [:return [:literal 0]]}))]
        (check-ready s)
        (with-redefs-fn {(pv 'preparation-roots) [:leaf]}
          #(do (check-ready s) (is (= [:leaf] (get-in @s [:readiness-stamp :preparation-roots])))))
        (let [failure (ex-info "model failure" {}) caught (try ((pv 'import-failure!) s failure) (catch Throwable e e))]
          (is (identical? failure (.getCause ^Throwable caught)))
          (is (nil? (:readiness-stamp @s)))
          (is (= :failed (:phase @s))))))))
(deftest literal-mutable-data-is-not-a-dependency
  (with-roots
    (fn []
      (let [reads (atom 0) payload (reify clojure.lang.Seqable (seq [_] (swap! reads inc) (throw (ex-info "literal inspected" {}))))
            s (atom (model {:body [:return [:literal payload]]}))]
        (check-ready s) (check-ready s)
        (is (some? (:readiness-stamp @s))) (is (zero? @reads))))))
(deftest mutable-roots-and-exotic-stored-keys-fall-back
  (let [roots (object-array [:root]) s (atom (model {:body [:return [:literal 0]]}))]
    (with-redefs-fn {(pv 'preparation-roots) (seq roots)
                    (ns-resolve 'prototype.resident-import 'import-roots) []
                    (pv 'source-graph-roots) []}
      #(do (check-ready s) (is (nil? (:readiness-stamp @s)))
           (aset roots 0 :unauthorized)
           (is (thrown? clojure.lang.ExceptionInfo (check-ready s))))))
  (with-roots
    (fn []
      (let [s (atom (model {:body [:return [:literal 0]]})) f (assoc (get-in @s [:world :functions]) (Object.) {:body [:return 0]})]
        (swap! s assoc-in [:world :functions] f) (swap! s assoc-in [:session :functions] f)
        (swap! s assoc-in [:configuration :trusted-functions] f)
        (check-ready s) (is (nil? (:readiness-stamp @s)))))))
(deftest roots-reloaded-during-validation-do-not-get-unearned-proof
  (with-roots
    (fn []
      (let [s (atom (model {:body [:return [:literal 0]]})) original executable/validate-executables!
            roots-var (pv 'preparation-roots) old @roots-var]
        (with-redefs [executable/validate-executables! (fn [& args]
                                                       (alter-var-root roots-var (constantly [:unauthorized]))
                                                       (apply original args))]
          (check-ready s))
        (is (identical? old (get-in @s [:readiness-stamp :preparation-roots])))
        (is (thrown? clojure.lang.ExceptionInfo (check-ready s)))
        (is (nil? (:readiness-stamp @s)))))))

(deftest successful-finish-discards-the-private-stamp
  (let [data {:readiness-stamp {:functions {} :registry {}} :phase :ready
              :world {:functions {}} :configuration {} :used 3}
        result ((pv 'finished-import-state) data)]
    (is (= :finished (:phase result)))
    (is (= 3 (:used result)))
    (is (not (contains? result :readiness-stamp)))
    (is (not (contains? result :world)))
    (is (not (contains? result :configuration)))))

(deftest graph-mode-change-requires-a-new-closure-proof
  (with-roots
    (fn []
      (let [profile {:token (Object.)}
            s (atom (assoc (model {:body [:return [:literal 0]]})
                           :source-graph {:profile :issued :profile-data profile :profile-token (:token profile)}))
            calls (atom 0) original executable/validate-executables!]
        (with-redefs-fn {(pv 'graph-profile!) (fn [_] profile)
                        #'executable/validate-executables! (fn [& args] (swap! calls inc) (apply original args))}
          (fn []
            (check-ready s) (is (= 1 @calls))
            (swap! s assoc :graph-operation? true)
            (check-ready s) (is (= 3 @calls))
            (check-ready s) (is (= 3 @calls))
            (swap! s assoc :graph-operation? false)
            (check-ready s) (is (= 4 @calls))))))))
