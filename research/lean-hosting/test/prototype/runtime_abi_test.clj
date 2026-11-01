(ns prototype.runtime-abi-test
  (:require [clojure.test :refer [deftest is]]
            [prototype.runtime-abi :as abi]
            [prototype.runtime-prim :as prim]
            [prototype.import-ir :as ir]
            [prototype.machine :as m]))

(defn name-of [s] ["str" ["anonymous"] s])
(def source-name (name-of "external"))
(def target-name (name-of "implementation"))
(def param {:x {:idx 1} :ty "object" :borrow false})
(def target-row {:kind "decl" :name target-name :dependencies [] :redirect nil
                 :ir {:fdecl {:f target-name :xs [param] :type "object"
                              :body ["ret" {:var {:id {:idx 1}}}] :info {}}}})
(def extern-row {:kind "decl" :name source-name :dependencies [] :redirect nil
                 :ir {:extern {:f source-name :xs [param] :type "object"
                               :ext {:entries [{:standard {:backend ["str" ["anonymous"] "all"]
                                                           :fn "test_guest_export"}}]}}}})
(def manifest {:kind "manifest" :schema "lean-ir-probe/1" :leanVersion "4.33.1"
               :leanCommit (get prim/pinned-build "lean_get_githash")
               :runtimeProfile {:wordBits 64 :target "x86_64-unknown-linux-gnu"}
               :exports [{:symbol "test_guest_export" :name target-name}]})
(def aliases {:manifests [manifest] :declarations {}})
(def base {:manifests [(assoc manifest :exports [])]
           :declarations {source-name extern-row target-name target-row}})

(deftest alias-overlay-is-metadata-only-and-lazy
  (let [reads (atom [])
        indexed (assoc base :declarations {source-name :source-index target-name :target-index}
                       :read-declaration (fn [name] (swap! reads conj name) (get (:declarations base) name)))
        overlaid (abi/with-export-aliases indexed aliases)]
    (is (empty? @reads))
    (is (identical? (:declarations indexed) (:declarations overlaid)))
    (is (identical? (:read-declaration indexed) (:read-declaration overlaid)))
    (is (= 2 (count (:manifests overlaid))))
    (is (= [source-name {:params [1] :export-redirect target-name
                        :body [:tail [:direct target-name] [[:var 1]]]}]
           (abi/lower-catalogue overlaid extern-row)))
    (is (= [target-name] @reads))
    (is (= [] (:exports (first (:manifests indexed)))))))

(deftest alias-closure-executes-the-actual-selected-guest-body
  (let [catalogue (abi/with-export-aliases base aliases)
        functions (ir/load-closure catalogue [source-name] #(abi/lower-catalogue catalogue %))
        result (m/run (m/start (m/world functions) source-name [42]))]
    (is (= #{source-name target-name} (set (keys functions))))
    (is (= 42 (:result result)))
    (is (not-any? :runtime-extern (vals functions)))))

(deftest overlay-validates-provenance-and-inventory-without-reading-bodies
  (doseq [bad [(assoc manifest :leanCommit "other-build")
               (assoc manifest :leanVersion "4.29.0")
               (assoc-in manifest [:runtimeProfile :wordBits] 32)
               (dissoc manifest :runtimeProfile)
               (assoc manifest :exports [{:symbol "" :name target-name}])
               (assoc manifest :exports [{:symbol "x" :name ["num" ["anonymous"] "-1"]}])
               (assoc manifest :initializationPlan {:actions []})]]
    (is (thrown? clojure.lang.ExceptionInfo
                 (abi/with-export-aliases base {:manifests [bad] :declarations {}}))))
  (is (thrown-with-msg? clojure.lang.ExceptionInfo #"metadata only"
        (abi/with-export-aliases base (assoc aliases :declarations {target-name target-row})))))

(deftest duplicate-aliases-agree-or-fail-explicitly
  (is (= 3 (count (:manifests (abi/with-export-aliases (abi/with-export-aliases base aliases) aliases)))))
  (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Conflicting export targets"
        (abi/with-export-aliases (assoc base :manifests [manifest])
          {:manifests [(assoc-in manifest [:exports 0 :name] (name-of "different"))] :declarations {}}))))

(deftest target-and-signature-failures-never-become-deferred-traps
  (doseq [[expected row-target] [[#"no guest function body" nil]
                                 [#"no guest function body" (assoc target-row :ir {:extern {}})]
                                 [#"name mismatch" (assoc target-row :name (name-of "wrong"))]
                                 [#"signature mismatch" (assoc-in target-row [:ir :fdecl :xs 0 :borrow] true)]
                                 [#"signature mismatch" (assoc-in target-row [:ir :fdecl :xs 0 :ty] "tobject")]
                                 [#"signature mismatch" (assoc-in target-row [:ir :fdecl :type] "tobject")]]]
    (let [catalogue (abi/with-export-aliases (assoc-in base [:declarations target-name] row-target) aliases)]
      (doseq [lower [abi/lower-catalogue abi/lower-deferred-catalogue]]
        (is (thrown-with-msg? clojure.lang.ExceptionInfo expected (lower catalogue extern-row)))))))

(deftest explicit-redirects-are-checked-against-real-selected-bodies
  (let [catalogue (abi/with-export-aliases base aliases)
        explicit (assoc extern-row :redirect {:name target-name :params [param] :type "object"})]
    (is (= (abi/lower-catalogue catalogue extern-row) (abi/lower-catalogue catalogue explicit)))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"signature mismatch"
          (abi/lower-catalogue catalogue (assoc-in explicit [:redirect :params 0 :borrow] true))))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Conflicting explicit"
          (abi/lower-catalogue catalogue (assoc-in explicit [:redirect :name] (name-of "elsewhere")))))))

(deftest aliases-survive-generic-catalogue-views-via-their-manifests
  (let [catalogue (abi/with-export-aliases base aliases)
        view (select-keys catalogue [:manifests :declarations :read-declaration])]
    (is (= (abi/lower-catalogue catalogue extern-row) (abi/lower-catalogue view extern-row)))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Conflicting export targets"
          (abi/lower-catalogue (update catalogue :manifests conj
                               (assoc-in manifest [:exports 0 :name] (name-of "changed"))) extern-row)))))
