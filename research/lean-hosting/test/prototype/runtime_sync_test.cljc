(ns prototype.runtime-sync-test
  (:require [prototype.runtime-sync :as sync]
            [prototype.runtime-prim :as runtime]
            [prototype.machine :as m]
            #?(:clj [prototype.mutable :as u])
            #?(:clj [prototype.block-compile :as blocks])
            #?(:clj [prototype.lazy-runtime :as lazy])
            #?(:clj [clojure.test :refer [deftest is]]
               :cljs [cljs.test :refer-macros [deftest is]])))

(defn allocate [world]
  (m/expr world [:runtime "lean_io_basemutex_new" [[:imm m/erased]]]))

(deftest mutex-new-is-a-direct-baseio-external-handle
  (let [initial (m/world {}) [world mutex] (allocate initial)
        expected {:kind :mutex :tag 254 :fields [] :rc 1 :mutex-state :unlocked}]
    (is (= {:arity 1} (get runtime/supported-symbols "lean_io_basemutex_new")))
    (is (= expected (m/node world mutex)))
    (is (empty? (:heap initial)))
    (is (= 1 (count (:heap world))))
    (is (= 1 (get-in world [:stats :allocations])))
    (is (empty? (:heap (m/release world mutex 1))))
    (is (empty? (:events (m/release world mutex 1))))))

(deftest persistent-logical-mutexes-are-snapshot-local-and-fork-safe
  (let [[world mutex] (allocate (m/world {}))
        world (m/mark-persistent world mutex)
        [left left-new] (allocate world) [right right-new] (allocate world)]
    (is (= 0 (:rc (m/node world mutex))))
    (is (= world (m/release world mutex 1)))
    (is (= left-new right-new))
    (is (= left right))
    (is (= 1 (count (:heap world))))
    (is (= :unlocked (:mutex-state (m/node world mutex))))
    #?(:clj (let [machine (u/thaw world) before (u/freeze machine)]
              (u/mark-persistent! machine mutex)
              (is (= before (u/freeze machine)))
              (is (= :unlocked (:mutex-state (m/node (u/freeze machine) mutex))))))))

(deftest mutex-operations-with-unimplemented-blocking-semantics-stay-unadmitted
  (doseq [symbol ["lean_io_basemutex_lock" "lean_io_basemutex_try_lock" "lean_io_basemutex_unlock"]]
    (is (not (contains? runtime/supported-symbols symbol)))
    (is (thrown-with-msg? #?(:clj clojure.lang.ExceptionInfo :cljs js/Error) #"Unsupported synchronization"
          (sync/evaluate {} (m/world {}) symbol [0 m/erased]))))
  (is (thrown-with-msg? #?(:clj clojure.lang.ExceptionInfo :cljs js/Error) #"arity"
        (sync/evaluate {} (m/world {}) "lean_io_basemutex_new" []))))

#?(:clj
   (deftest mutex-allocation-has-identical-fuel-boundaries-in-all-backends
     (let [functions {:new {:params [0]
                           :body [:let 1 [:runtime "lean_io_basemutex_new" [[:var 0]]]
                                  [:return [:var 1]]]}}
           initial (m/start (m/world functions) :new [m/erased])
           eager (blocks/compile-program functions nil {:lexical-joins true})
           delayed (lazy/open-program functions)]
       (doseq [fuel (range 4)]
         (let [expected (m/run initial fuel)]
           (is (= expected (u/freeze (u/run! (u/thaw initial) fuel)))))
         (is (= (m/run initial fuel) (u/freeze (blocks/run! eager (u/thaw initial) fuel))))
         (is (= (m/run initial fuel) (u/freeze (lazy/run! delayed (u/thaw initial) fuel))))))))

#?(:cljs (do (defn -main [] (cljs.test/run-tests 'prototype.runtime-sync-test))
             (set! *main-cli-fn* -main)))
