(ns prototype.slot-count-test
  (:require [clojure.test :refer [deftest is]]
            [prototype.slot-count :as slots]
            [prototype.walk :as walk]
            [prototype.machine :as m]
            [prototype.mutable :as u])
  (:import [java.lang.ref WeakReference]
           [java.util HashMap ArrayList]))

(defn- functions []
  (assoc {} :entry {:params [2] :body [:let 4 [:prim :inc [[:var 2]]] [:return [:var 4]]]}))

(deftest program-cache-compares-identity-without-code-hashing
  (let [a (functions) b (functions) cache (slots/cache)
        original walk/forms scans (atom 0)]
    (with-redefs [walk/forms (fn [forms] (swap! scans inc) (original forms))]
      (is (= 5 (slots/program-slots a cache)))
      (is (= 1 @scans))
      (is (= 5 (slots/program-slots a cache)))
      (is (= 1 @scans))
      (is (= a b))
      (is (not (identical? a b)))
      (is (= 5 (slots/program-slots b cache)))
      (is (= 2 @scans))
      (is (= 5 (slots/program-slots a cache)))
      (is (= 3 @scans))
      (is (= 101 (slots/program-slots (assoc-in a [:entry :params] [100]) cache)))
      (is (= 4 @scans)))))

(deftest cache-holds-only-a-weak-program-and-scalar-size
  ;; Structural retention assertion avoids relying on GC timing. The cache
  ;; does not contain bodies, a capturing computation, or an old entry chain.
  (let [cache (slots/cache) a (functions) b (assoc-in a [:entry :params] [8])]
    (slots/program-slots a cache)
    (is (= #{:program :slots} (set (keys @cache))))
    (is (instance? WeakReference (:program @cache)))
    (is (identical? a (.get ^WeakReference (:program @cache))))
    (is (= 5 (:slots @cache)))
    (slots/program-slots b cache)
    (is (= #{:program :slots} (set (keys @cache))))
    (is (identical? b (.get ^WeakReference (:program @cache))))
    (is (= 9 (:slots @cache)))
    ;; Clearing a weak referent simulates collection deterministically.
    (.clear ^WeakReference (:program @cache))
    (is (= 9 (slots/program-slots b cache)))
    (is (identical? b (.get ^WeakReference (:program @cache))))))

(deftest mutable-programs-cannot-install-a-stale-cache-entry
  (let [cache (slots/cache) good (functions)]
    (slots/program-slots good cache)
    (doseq [bad [(HashMap. ^java.util.Map good)
                 {:entry (HashMap. ^java.util.Map (:entry good))}
                 {:entry {:params [0] :body [:return [:imm (ArrayList.)]]}}]]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"immutable|mutable" (slots/program-slots bad cache)))
      (is (identical? good (.get ^WeakReference (:program @cache)))))))

(deftest snapshot-local-registers-remain-uncached
  (let [functions (functions)
        base (m/start (m/world functions) :entry [41])
        wider (assoc-in base [:locals 100] 99)
        narrow (u/thaw base)
        wide (u/thaw wider)]
    (is (= 5 (:slots narrow)))
    (is (= 101 (:slots wide)))
    (is (= wider (u/freeze wide)))
    (is (= base (u/freeze (u/thaw base))))
    (is (= 42 (:result (u/freeze (u/run! wide 10)))))
    (is (= 1 (slots/local-slots {})))
    (is (= 201 (slots/local-slots {200 :live}))))

(deftest all-register-bearing-instructions-contribute
  (let [functions {:entry {:params [2] :body [:join 100 [30]
                                             [:host "host" [] 70 [:return [:var 70]]]
                                             [:call 40 [:direct :entry] [[:var 2]]
                                              [:suspend 60 [:jump 100 [[:var 40]]]]]]}}
        cache (slots/cache)]
    (is (= 71 (slots/program-slots functions cache)))
    (is (= 1 (slots/program-slots {} cache))))))

(deftest sizing-never-hashes-program-bodies
  (let [poison (proxy [Object] [] (hashCode [] (throw (AssertionError. "Program body was hashed"))))
        functions {:entry {:params [] :body [:return [:imm poison]]}}
        cache (slots/cache)]
    (is (= 1 (slots/program-slots functions cache)))
    (is (= 1 (slots/program-slots functions cache)))))

(deftest compiler-layout-queries-do-not-evict-the-execution-program
  (let [functions (functions) state (m/start (m/world functions) :entry [41])
        original walk/forms scans (atom 0)]
    (with-redefs [walk/forms (fn [forms] (swap! scans inc) (original forms))]
      (is (= 5 (#'prototype.mutable/slot-count state)))
      (let [before @scans]
        (is (= 5 (u/function-slots (:entry functions))))
        (is (= before @scans))
        (is (= 5 (#'prototype.mutable/slot-count state)))
        (is (= before @scans))))))

(deftest incremental-programs-reuse-unchanged-weak-function-sizes
  ;; Construct fresh identity fixtures on each invocation: this test is rerun
  ;; in a resident REPL whose weak sizing caches may still hold literal maps.
  (let [old (hash-map :params [] :body [:let 12 [:imm 1] [:return [:var 12]]])
        functions {:entry old}
        new (hash-map :params [80] :body [:return [:var 80]])
        original walk/forms scans (atom [])]
    (with-redefs [walk/forms (fn [form] (swap! scans conj form) (original form))]
      (is (= 13 (slots/program-slots functions)))
      (is (= 81 (slots/program-slots (assoc functions :new new))))
      (is (= 13 (slots/program-slots (assoc functions :alias old))))
      (is (= 1 (count (filter #(identical? old %) @scans))))
      (is (= 1 (count (filter #(identical? new %) @scans))))
      ;; A replaced definition gets measured even if its enclosing map retained metadata.
      (is (= 101 (slots/program-slots
                   (assoc-in functions [:entry :params] [100])))))))

(deftest mutable-array-backed-code-cannot-publish-a-stale-size
  (doseq [functions [{:entry {:params (object-array [0]) :body [:return [:var 0]]}}
                     {:entry {:params (seq (object-array [0])) :body [:return [:var 0]]}}
                     {:entry {:params [] :body (object-array [:return [:imm 0]])}}
                     {:entry {:params [] :body [:return [:imm (int-array [0])]]}}
                     {:entry {:params [] :body [:return [:imm (seq (object-array [0]))]]}}]
          count-slots [slots/program-slots #(slots/program-slots % (slots/cache))]]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"immutable|mutable" (count-slots functions)))))
