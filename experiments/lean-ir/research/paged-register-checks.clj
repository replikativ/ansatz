(ns paged-register-checks
  (:require [paged-registers :as paged]
            [prototype.mutable :as u]
            [prototype.machine :as m])
  (:import [prototype.research PagedRegisters]))

(defn- ensure! [ok label data]
  (when-not ok (throw (ex-info (str "Paged register check failed: " label) data))))

(defn bank-check! []
  (let [unbound (Object.) random (java.util.Random. 4821)
        initial (PagedRegisters. 131 unbound)]
    (loop [i 0 bank initial expected (vec (repeat 131 unbound)) versions []]
      (if (= i 500)
        {:operations i :saved-versions (count versions)}
        (let [op (.nextInt random 4)
              [bank expected versions]
              (case op
                0 (let [slot (.nextInt random 131) value (when (odd? i) (long i))]
                    (.set bank slot value) [bank (assoc expected slot value) versions])
                1 (let [saved (.snapshot bank)]
                    (ensure! (identical? saved (.snapshot bank)) :snapshot-reuse {})
                    (ensure! (try (.set saved 0 :bad) false (catch IllegalStateException _ true)) :read-only {})
                    [bank expected (conj versions [saved expected])])
                2 (if (seq versions)
                    (let [[saved prior] (nth versions (.nextInt random (count versions)))]
                      [(.fork ^PagedRegisters saved) prior versions])
                    [bank expected versions])
                3 (do (.clear bank) [bank (vec (repeat 131 unbound)) versions]))]
          (ensure! (= expected (vec (.toArray ^PagedRegisters bank))) :current {:operation i})
          (doseq [[^PagedRegisters saved prior] versions]
            (ensure! (= prior (vec (.toArray saved))) :retained-version {:operation i}))
          (recur (inc i) bank expected versions))))))

(defn boundary-check! []
  (let [unbound (Object.) slots [0 15 16 31 32 127 128 130]]
    (doseq [slot slots]
      (let [parent (PagedRegisters. 131 unbound)
            _ (.set parent slot :before)
            saved (.snapshot parent)
            left (.fork saved) right (.fork saved)]
        (.set parent slot :parent)
        (.set left slot nil)
        (.set right (mod (inc slot) 131) :right)
        (ensure! (= :before (.get saved slot)) :boundary-saved {:slot slot})
        (ensure! (nil? (.get left slot)) :boundary-left {:slot slot})
        (ensure! (= :before (.get right slot)) :boundary-right {:slot slot})
        (.clear parent) (.clear left)
        (ensure! (= :before (.get saved slot) (.get right slot)) :clear-isolation {:slot slot})
        (ensure! (try (.clear saved) false (catch IllegalStateException _ true)) :read-only-clear {})))
    {:slots slots :two-forks-and-clear :ok}))

(def wide-functions
  {:entry {:params [130]
           :body [:join 42 [129]
                  [:let 127 [:prim :add [[:var 130] [:var 129]]] [:return [:var 127]]]
                  [:join 43 [128] [:jump 42 [[:var 128]]]
                   [:let 130 [:literal 100]
                    [:call 126 [:direct :worker] [[:var 130]] [:jump 43 [[:var 126]]]]]]]}
   :worker {:params [130]
            :body [:suspend 129
                   [:let 128 [:prim :add [[:var 129] [:var 130]]] [:return [:var 128]]]]}})

(defn prefixes!
  "Compare every fuel prefix with the independent persistent interpreter,
   including resume after pause and two independent forks after suspension."
  [functions entry args threshold]
  (let [initial (m/start (m/world functions) entry args)
        completed (m/run initial 10000)
        steps (get-in completed [:stats :steps])]
    (paged/with-runtime
     threshold
     (fn []
       (doseq [fuel (range (+ 2 steps))]
         (let [machine (u/run! (u/thaw initial) fuel)
               saved (u/freeze machine)]
           (ensure! (= (m/run initial fuel) saved) :fuel-prefix {:fuel fuel})
           (when (= :paused (:status saved))
             (ensure! (= completed (u/freeze (u/run! (u/resume! machine nil) 10000))) :pause-resume {:fuel fuel}))
           (when (contains? #{:suspended :host-call} (:status saved))
             (doseq [answer [10 20]]
               (let [resumed (m/resume saved answer)
                     finished (m/run resumed 10000)
                     remaining (- (get-in finished [:stats :steps]) (get-in saved [:stats :steps]))]
                 (doseq [budget (range (+ 2 remaining))]
                   (let [branch (u/resume! (u/thaw saved) answer)
                         actual (u/freeze (u/run! branch budget))]
                     (ensure! (= (m/run resumed budget) actual)
                              :fork-resume-prefix {:fuel fuel :answer answer :budget budget})
                     (when (= :paused (:status actual))
                       (ensure! (= finished (u/freeze (u/run! (u/resume! branch nil) 10000)))
                                :fork-pause-resume {:answer answer :budget budget}))))))
             (ensure! (= saved (u/freeze machine)) :parent-unchanged {:fuel fuel}))))))
    {:prefixes (+ 2 steps) :completion (:status completed)}))

(defn check! []
  {:bank (bank-check!)
   :boundaries (boundary-check!)
   :wide (prefixes! wide-functions :entry [3] 64)
   :host (prefixes! (assoc-in wide-functions [:worker :body]
                              [:host "research-ping" [[:var 130]] 129
                               [:let 128 [:prim :add [[:var 129] [:var 130]]] [:return [:var 128]]]])
                    :entry [3] 64)
   :forced-small (prefixes! wide-functions :entry [3] 1)
   :dense-control (prefixes! wide-functions :entry [3] Long/MAX_VALUE)})
