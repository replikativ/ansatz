(ns prototype.register-layout-test
  (:require [clojure.test :refer [deftest is]]
            [prototype.machine :as m] [prototype.mutable :as u]
            [prototype.slot-count :as slots] [prototype.walk :as walk]
            [prototype.lazy-runtime :as lazy] [prototype.block-compile :as blocks])
  (:import [java.util IdentityHashMap HashMap] [java.lang.ref WeakReference]))

(def inflate {:params [4010] :body [:return [:var 4010]]})
(defn- runners [functions]
  (let [demand (lazy/open-program functions {:compile-threshold 2})
        eager (blocks/compile-program functions nil {:lexical-joins true})
        compact (blocks/compile-program functions nil {:lexical-joins true :compact-registers true})]
    [(fn [snapshot fuel] (u/freeze (u/run! (u/thaw snapshot) fuel)))
     (fn [snapshot fuel] (u/freeze (lazy/run! demand (u/thaw snapshot) fuel)))
     (fn [snapshot fuel] (u/freeze (blocks/run! eager (u/thaw snapshot) fuel)))
     (fn [snapshot fuel] (u/freeze (blocks/run! compact (u/thaw snapshot) fuel)))]))
(defn- all-fuels [initial]
  (let [finished (m/run initial 10000)
        cost (- (get-in finished [:stats :steps]) (get-in initial [:stats :steps]))
        run (runners (:functions initial))]
    (doseq [fuel (range (+ cost 2)) run run]
      (is (= (m/run initial fuel) (run initial fuel))))
    finished))

(deftest callee-widths-shrink-and-saved-caller-storage-is-restored
  (let [functions {:inflate inflate
                   :entry {:params [0] :body [:call 50 [:direct :wide] [[:var 0]] [:return [:var 50]]]}
                   :wide {:params [20] :body [:tail [:direct :tiny] [[:var 20]]]}
                   :tiny {:params [2] :body [:return [:var 2]]}}
        initial (m/start (m/world functions) :entry [42])
        machine (u/thaw initial)
        caller (u/locals-array machine)]
    (is (= 4011 (:slots machine)))
    (is (= 51 (alength ^objects caller)))
    (u/step! machine)
    (is (= 21 (alength ^objects (u/locals-array machine))))
    (u/step! machine)
    (is (= 3 (alength ^objects (u/locals-array machine))))
    (u/step! machine)
    (is (identical? caller (u/locals-array machine)))
    (is (= 42 (:result (all-fuels initial))))
    ;; A fresh explicit start enters ENTRY through the same callee path.
    (let [machine (u/thaw (m/world functions))]
      (u/start! machine :entry [9])
      (is (= 51 (alength ^objects (u/locals-array machine)))))
    (doseq [layouts [{:wide 25} {}]]
      (let [machine (assoc (u/thaw initial) :register-layouts layouts)]
        (u/step! machine)
        (is (= (get layouts :wide 4011) (alength ^objects (u/locals-array machine))))))))

(deftest exact-width-reuse-clears-stale-bindings-without-an-allocation
  (let [f {:params [2] :body [:return [:var 2]]}
        machine (u/thaw (m/world {:inflate inflate :small f}))
        allocator @#'u/registers calls (atom [])]
    (with-redefs-fn {#'u/registers (fn [n bindings] (swap! calls conj n) (allocator n bindings))}
      (fn []
        (u/start! machine :small [1])
        (let [array (u/locals-array machine)]
          (aset ^objects array 0 :stale)
          (u/call-values! machine [:direct :small] [2] nil nil)
          (is (identical? array (u/locals-array machine)))
          (is (= [3] @calls))
          (is (= {2 2} (:locals (u/freeze machine)))))))))

(deftest function-identity-caches-are-local-to-execution-and-never-snapshotted
  (let [f {:params [2] :body [:return [:var 2]]}
        functions {:inflate inflate :first f :alias f}
        machine (u/thaw (m/world functions))
        final-machine (volatile! machine)
        original slots/function-slots queries (atom 0)]
    (with-redefs [slots/function-slots (fn [f] (swap! queries inc) (original f))]
      (u/start! machine :first [1])
      (u/call-values! machine [:direct :alias] [2] nil nil)
      (is (= 1 @queries))
      (let [equal (into {} f)
            _ (is (not (identical? f equal)))
            machine (assoc machine :functions (assoc functions :first equal))]
        (u/call-values! machine [:direct :first] [3] nil nil)
        (is (= 2 @queries))
        (let [edited (assoc f :body [:let 90 [:literal 99] [:return [:var 90]]])
              machine (assoc machine :functions (assoc functions :first edited))]
          (u/call-values! machine [:direct :first] [4] nil nil)
          (vreset! final-machine machine)
          (is (= 3 @queries))
          (is (= 91 (alength ^objects (u/locals-array machine)))))))
    (let [snapshot (u/freeze @final-machine) left (u/thaw snapshot) right (u/thaw snapshot)]
      (is (not (contains? snapshot :function-slot-cache)))
      (is (not (identical? (:function-slot-cache machine) (:function-slot-cache left))))
      (is (not (identical? (:function-slot-cache left) (:function-slot-cache right))))
      (is (.isEmpty ^IdentityHashMap (:function-slot-cache left))))
    ;; Function-only adoption remains safe for pre-existing Machines.
    (let [old (dissoc (u/thaw (m/world functions)) :function-slot-cache)]
      (u/start! old :first [9])
      (is (= 3 (alength ^objects (u/locals-array old)))))))

(deftest public-function-size-cache-is-weak-identity-based-and-validates-code
  (let [poison (proxy [Object] [] (hashCode [] (throw (AssertionError. "Hashed code"))))
        f {:params [9] :body [:return [:imm poison]]}
        original walk/forms scans (atom 0)]
    (with-redefs [walk/forms (fn [x] (swap! scans inc) (original x))]
      (is (= 10 (slots/function-slots f)))
      (is (= 10 (slots/function-slots f)))
      (is (= 1 @scans))
      (is (= 10 (slots/function-slots (into {} f))))
      (is (= 2 @scans)))
    (let [cache (var-get (ns-resolve 'prototype.slot-count 'function-cache))
          buckets ^HashMap (:buckets cache)
          key (System/identityHashCode f)
          entry (first (filter #(identical? f (.get ^WeakReference (first %))) (.get buckets key)))
          reference ^WeakReference (first entry)
          proof (second entry)]
      (is (instance? WeakReference reference))
      (is (identical? f (.get reference)))
      (is (= 2 (count entry)))
      (is (nil? (meta entry)))
      ;; Only weak code identity plus scalar width/eligibility may be retained;
      ;; adding a body/base/delta reference would fail this exact shape check.
      (is (= #{:slots :reusable?} (set (keys proof))))
      (is (nil? (meta proof)))
      (is (= 10 (:slots proof)))
      (is (true? (:reusable? proof)))
      (is (every? #(or (integer? %) (boolean? %)) (vals proof)))
      ;; Deterministically exercise queue cleanup, without relying on forced GC.
      (.clear reference) (.enqueue reference)
      (slots/function-slots {:params [] :body [:return [:imm 7]]})
      (is (not-any? #(identical? reference (first %)) (.get buckets key)))))
  (doseq [function [(HashMap. ^java.util.Map {:params [] :body [:return [:imm 1]]})
                    {:params (object-array [0]) :body [:return [:var 0]]}
                    {:params [] :body [:return [:imm (int-array [0])]]}
                    {:params [] :body [:return [:imm (seq (object-array [0]))]]}]]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"immutable|mutable" (slots/function-slots function)))))

(deftest sparse-joins-host-boundaries-suspensions-and-forks-match-all-backends
  (let [functions {:inflate inflate
                   :entry {:params [1] :body [:join 90 [300] [:return [:var 300]]
                                               [:call 40 [:direct :worker] [[:var 1]] [:jump 90 [[:var 40]]]]]}
                   :worker {:params [7] :body [:let 12 [:prim :inc [[:var 7]]]
                                               [:host "register-test" [[:var 12]] 30
                                                [:suspend 31 [:return [:var 31]]]]]}}
        initial (m/start (m/world functions) :entry [41])
        host (all-fuels initial)]
    (is (= :host-call (:status host)))
    (is (= [42] (get-in host [:host-request :arguments])))
    (doseq [host-value [10 20]]
      (let [suspended (all-fuels (m/resume host host-value))]
        (is (= :suspended (:status suspended)))
        (doseq [answer [70 80]]
          (is (= answer (:result (all-fuels (m/resume suspended answer))))))))
    (is (= host (u/freeze (u/thaw host))))))

(deftest overapplication-surplus-frame-is-width-one-and-ownership-is-unchanged
  (let [functions {:inflate inflate
                   :entry {:params [0 1 2] :body [:join 90 [77] [:return [:var 77]]
                                                  [:call 50 [:closure [:var 0]] [[:var 1] [:var 2]]
                                                   [:jump 90 [[:var 50]]]]]}
                   :first {:params [10] :body [:let 12 [:closure :second [[:var 10]]] [:return [:var 12]]]}
                   :second {:params [100 200] :body [:let 300 [:ctor 8 [[:var 100] [:var 200]]] [:return [:var 300]]]}}
        [world a] (m/resource (m/world functions) :a)
        [world b] (m/resource world :b)
        [world closure] (m/expr world [:closure :first []])
        initial (m/start world :entry [closure a b]) machine (u/thaw initial)]
    (u/run! machine 2)
    (let [frame ^objects (.peekLast ^java.util.ArrayDeque (:frames machine))]
      (is (= 1 (alength ^objects (aget frame 2)))))
    (let [done (all-fuels initial)]
      (is (= [a b] (:fields (m/node done (:result done)))))
      (is (= [[:released :b] [:released :a]] (:events (m/release done (:result done) 1)))))))

(deftest compiled-caller-reuse-observes-edited-callee-width
  (let [body [:tail [:direct :value] [[:imm 42]]]
        functions {:inflate inflate :entry {:params [] :body body}
                   :value {:params [2] :body [:return [:var 2]]}}
        cache (lazy/code-cache)
        old (lazy/open-program functions {} cache)
        _ (lazy/run! old (u/thaw (m/start (m/world functions) :entry [])))
        old-block (.get ^IdentityHashMap (:identity-dispatch old) body)
        edited (assoc-in functions [:value :body] [:let 90 [:prim :inc [[:var 2]]] [:return [:var 90]]])
        new (lazy/open-program edited {} cache)
        initial (m/start (m/world edited) :entry [])
        machine (u/thaw initial)]
    (lazy/run! new machine 1)
    (is (= 91 (alength ^objects (u/locals-array machine))))
    (is (identical? old-block (.get ^IdentityHashMap (:identity-dispatch new) body)))
    (is (= (m/run initial 1) (u/freeze machine)))
    (is (= 43 (:result (all-fuels initial))))))

(defn- restored-frame-widths [machine]
  (mapv #(alength ^objects (aget ^objects % 2)) (:frames machine)))
(defn- restored-join-widths [joins]
  (into {} (map (fn [[id join]] [id (alength ^objects (aget ^objects join 2))])) joins))

(deftest thaw-sizes-active-saved-and-captured-registers-independently
  (let [snapshot (assoc (m/start (m/world {:inflate inflate}) :inflate [0])
                       :body [:return [:imm 0]] :locals {1 :active}
                       :joins {90 {:params [70] :body [:let 200 [:literal 1] [:return [:var 200]]]
                                   :locals {3 :captured}}}
                       :frames [{:dest 150 :body [:let 60 [:literal 42] [:return [:var 60]]]
                                 :locals {7 :saved}
                                 :joins {99 {:params [444] :body [:return [:imm 1]] :locals {}}}}])
        machine (u/thaw snapshot)]
    (is (= 4011 (:slots machine)))
    (is (= 2 (alength ^objects (u/locals-array machine))))
    (is (= {90 201} (restored-join-widths (aget ^objects (:control machine) 2))))
    (is (= [151] (restored-frame-widths machine)))
    (is (= {99 445} (restored-join-widths (aget ^objects (.peekLast ^java.util.ArrayDeque (:frames machine)) 3))))
    (is (= snapshot (u/freeze machine)))
    (is (= 42 (:result (u/freeze (u/run! machine)))))
    (is (= (m/run snapshot) (u/freeze machine)))
    ;; Saved bindings need not fit another frame or the program's global bound.
    (let [wide (assoc-in snapshot [:frames 0 :locals 9000] :outside-program)
          restored (u/thaw wide)]
      (is (= 4011 (:slots restored)))
      (is (= [9001] (restored-frame-widths restored)))
      (is (= wide (u/freeze restored)))
      (is (= (m/run wide) (u/freeze (u/run! restored)))))))

(deftest restoring-pending-unused-destinations-and-empty-contexts
  (let [base (assoc (m/start (m/world {:inflate inflate}) :inflate [0])
                    :body [:return [:imm 42]] :locals {} :frames []
                    :joins {0 {:params [] :body [:return [:imm 0]] :locals {}}})]
    (is (= 1 (alength ^objects (u/locals-array (u/thaw base)))))
    (doseq [[status pending width] [[:host-call {:host-request {:symbol "unused" :arguments [] :dest 875}} 876]
                                    [:suspended {:resume-var 940} 941]]]
      (let [snapshot (merge base {:status status} pending)
            left (u/thaw snapshot) right (u/thaw snapshot)]
        (is (= width (alength ^objects (u/locals-array left))))
        (is (= {0 1} (restored-join-widths (aget ^objects (:control left) 2))))
        (is (= snapshot (u/freeze left)))
        (is (= snapshot (u/freeze right)))
        (doseq [value [7 9]]
          (let [machine (u/resume! (u/thaw snapshot) value)
                expected (m/run (m/resume snapshot value))]
            (is (= expected (u/freeze (u/run! machine))))
            (is (= snapshot (u/freeze right)))))))))

(deftest restoration-memoizes-body-identity-without-walking-runtime-payloads
  (let [poison (proxy [Object] [] (hashCode [] (throw (AssertionError. "Hashed runtime value"))))
        payload (object-array [poison])
        body [:return [:imm payload]]
        snapshot (assoc (m/start (m/world {:inflate inflate}) :inflate [0])
                        :body body :locals {}
                        :frames (mapv (fn [dest] {:dest dest :body body :locals {} :joins {}}) (range 32))
                        :joins {0 {:params [80] :body body :locals {}}})
        measure @#'u/measure-continuation-slots calls (atom 0)
        machine (with-redefs-fn {#'u/measure-continuation-slots
                                 (fn [body fallback] (swap! calls inc) (measure body fallback))}
                  #(u/thaw snapshot))]
    (is (= 1 @calls))
    (is (= 1 (alength ^objects (u/locals-array machine))))
    (is (= (vec (range 1 33)) (restored-frame-widths machine)))
    (is (= {0 81} (restored-join-widths (aget ^objects (:control machine) 2))))
    (is (= snapshot (u/freeze machine)))
    (is (= (m/run snapshot) (u/freeze (u/run! machine))))
    (is (identical? payload (:result (u/freeze machine))))
    (is (not (contains? (u/freeze machine) :body-widths)))))

(defn- all-resumed-cuts [initial]
  (let [end (m/run initial 1000)
        cost (- (get-in end [:stats :steps]) (get-in initial [:stats :steps]))
        run (runners (:functions initial))]
    (doseq [cut (range (inc cost))]
      (let [checkpoint (m/run initial cut)]
        (is (= checkpoint (u/freeze (u/thaw checkpoint))))
        (when (= :paused (:status checkpoint))
          (let [resumed (m/resume checkpoint nil)]
            (doseq [run run]
              (is (= end (run resumed 1000))))))))
    end))

(deftest every-paused-cut-restores-future-branches-joins-and-continuations
  (let [functions {:inflate inflate
                   :entry {:params [1] :body [:join 10 [600]
                                             [:join 11 [700] [:return [:var 700]]
                                              [:jump 11 [[:var 600]]]]
                                             [:call 250 [:direct :worker] [[:var 1]]
                                              [:jump 10 [[:var 250]]]]]}
                   :worker {:params [7] :body [:case [:var 7]
                                               [[0 [:let 800 [:literal 42] [:return [:var 800]]]]
                                                [:default [:host "resume-layout" [] 301
                                                           [:suspend 302 [:return [:var 302]]]]]]]}}]
    (is (= 42 (:result (all-resumed-cuts (m/start (m/world functions) :entry [0])))))
    (let [host (all-resumed-cuts (m/start (m/world functions) :entry [1]))]
      (is (= :host-call (:status host)))
      (doseq [value [5 7]]
        (let [suspended (all-resumed-cuts (m/resume host value))]
          (is (= :suspended (:status suspended)))
          (doseq [answer [42 43]]
            (is (= answer (:result (all-resumed-cuts (m/resume suspended answer)))))))))))

(deftest paused-closure-overapplication-and-tail-transfer-resume-identically
  (let [functions {:inflate inflate
                   :entry {:params [0] :body [:let 3 [:closure :first []]
                                              [:call 400 [:closure [:var 3]] [[:var 0] [:imm 2]]
                                               [:tail [:direct :done] [[:var 400]]]]]}
                   :first {:params [8] :body [:let 9 [:closure :second [[:var 8]]] [:return [:var 9]]]}
                   :second {:params [100 200] :body [:let 300 [:prim :add [[:var 100] [:var 200]]]
                                                    [:return [:var 300]]]}
                   :done {:params [2] :body [:return [:var 2]]}}]
    (is (= 42 (:result (all-resumed-cuts (m/start (m/world functions) :entry [40])))))))
