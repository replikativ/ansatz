(ns prototype.native-call-test
  (:require [clojure.test :refer [deftest is]]
            [prototype.native-call :as fusion]
            [prototype.mutable :as u]
            [prototype.machine :as m]
            [prototype.slot-count :as slots]
            [prototype.native-scalar :as native]
            [prototype.native-nat :as nat]
            [prototype.runtime-prim :as runtime]))

(defn- ensure! [ok label data]
  (is ok (str label))
  (when-not ok (throw (ex-info (str "Wrapper fusion check failed: " label) data))))

(defn wrapper
  ([symbol] (wrapper symbol [1 2]))
  ([symbol params]
   (let [dest (inc (reduce max 0 params))]
     {:params params :runtime-extern symbol
      :body [:let dest [:runtime symbol (mapv #(vector :var %) params)] [:return [:var dest]]]})))

(defn functions [symbol]
  {:entry {:params [0 1] :body [:call 2 [:direct :nat] [[:var 0] [:var 1]] [:return [:var 2]]]}
   :nat (wrapper symbol)})

(defn- snapshot [s]
  (let [world (u/freeze s)]
    {:world world :result-class (class (:result world))
     :local-classes (update-vals (:locals world) class)
     :frame-local-classes (mapv #(update-vals (:locals %) class) (:frames world))}))

(defn- attempt [driver initial fuel setup]
  (try
    (let [s (setup (u/thaw initial))
          outcome (try (driver s fuel) :ok
                       (catch Throwable t {:class (class t) :message (ex-message t) :data (ex-data t)}))]
      {:outcome outcome :state (snapshot s)})
    (catch Throwable t
      {:outcome {:class (class t) :message (ex-message t) :data (ex-data t)}
       :state :unavailable-before-checkpoint})))

(defn prefixes!
  ([fs args] (prefixes! fs args identity))
  ([fs args setup]
   (let [program (fusion/open-program fs) initial (m/start (m/world fs) :entry args)]
     (doseq [fuel [-1 0 1 2 3 4 5 7 20 0N 1N 4N 1.5 nil]]
       (let [expected (attempt u/run! initial fuel setup)
             actual (attempt #(fusion/run! program %1 %2) initial fuel setup)]
         (ensure! (= expected actual) :prefix {:args args :fuel fuel :expected expected :actual actual})))
     {:wrappers (count (:wrappers program)) :sites (.size ^java.util.IdentityHashMap (:calls program)) :prefixes 14})))

(defn arithmetic! []
  (vec (for [symbol ["lean_nat_add" "lean_nat_sub" "lean_nat_dec_eq" "lean_nat_dec_lt" "lean_nat_mod"]
             args [[20 22] [22 22] [23 5] [23 0] [Long/MAX_VALUE 1] [-1 22]
                   [20N 22N] [(int 20) (int 22)] [:bad 22]]]
         (prefixes! (functions symbol) args))))

(defn eligibility! []
  (let [base (functions "lean_nat_add")
        cases [(assoc base :nat (wrapper "lean_nat_add" [1 1]))
               (assoc base :nat (wrapper "lean_nat_add" [-1 2]))
               (assoc-in base [:entry :body 4] false)
               (assoc-in base [:entry :body 1] "bad-destination")
               (assoc-in base [:entry :body 3] [[:var 0]])
               (assoc-in base [:nat :body] [:return [:imm 777]])]]
    (doseq [fs cases]
      (ensure! (zero? (.size ^java.util.IdentityHashMap (:calls (fusion/open-program fs)))) :ineligible-site {})
      (prefixes! fs [20 22]))
    (let [bad (assoc base :nat {:params [Long/MAX_VALUE 2] :runtime-extern "lean_nat_add" :body [:unsupported]})]
      (ensure! (empty? (:wrappers (fusion/open-program bad))) :oversized-parameters {}))
    (let [mutable (java.util.HashMap. base)]
      (ensure! (empty? (:wrappers (fusion/open-program mutable))) :mutable-function-table {}))
    (prefixes! base [20 22] #(assoc % :register-layouts {:nat 2}))
    (prefixes! base [20 22]
               (fn [s] (.put ^java.util.IdentityHashMap (:function-slot-cache s) (:nat base) 2) s))
    (prefixes! base [20 22]
               (fn [s] (.put ^java.util.IdentityHashMap (:function-slot-cache s) (:nat base) 3) s))
    (prefixes! base [20 22] #(assoc % :function-slot-cache (java.util.HashMap.)))
    (prefixes! (assoc base :entry {:params [] :body [:call 0 [:direct :nat] [[:imm 20] [:imm 22]]
                                                  [:return [:var 0]]]}) []
               (fn [s] (aset ^objects (:control s) 1 (make-array String 1)) s))
    (let [program (fusion/open-program base) edited (assoc-in base [:nat :body] [:return [:imm 777]])]
      (ensure! (try (fusion/run! program (u/thaw (m/start (m/world edited) :entry [20 22])) 20)
                    false (catch clojure.lang.ExceptionInfo t
                            (= "Fusion program does not match machine code identity" (ex-message t))))
               :program-identity {}))
    {:ineligible-programs (count cases) :layouts-and-cache :ok :identity :ok}))

(defn invalidations! []
  (let [fs (functions "lean_nat_add") initial (m/start (m/world fs) :entry [20 22])
        program (fusion/open-program fs)
        numeric-var (ns-resolve 'prototype.runtime-prim 'numeric)
        operations-var (ns-resolve 'prototype.runtime-prim 'scalar-operations)
        changes [{numeric-var (fn [& _] 777)}
                 {operations-var (assoc @operations-var "lean_nat_add" :nat-sub)}
                 {#'slots/function-slots (fn [_] 0)}
                 {#'u/step! (fn [s] s)}
                 {#'u/add-steps! (fn [& _] nil)}
                 {#'u/set-body! (fn [& _] nil)}
                 {(ns-resolve 'prototype.mutable 'expr!) (fn [& _] 777)}
                 {(ns-resolve 'prototype.mutable 'call!) (fn [& _] nil)}
                 {#'u/call-step-with! (fn [& _] nil)}
                 {#'u/run-prepared! (fn [& _] nil)}
                 {(ns-resolve 'prototype.mutable 'prepared-driver-roots) :invalid}
                 {(ns-resolve 'prototype.native-call 'generation) (Object.)}
                 {(ns-resolve 'prototype.native-nat 'owner) (Object.)}
                 {(ns-resolve 'prototype.slot-count 'program-layout-generation) (Object.)}]]
    (with-redefs-fn
      {(ns-resolve 'prototype.slot-count 'program-layout-generation) (Object.)}
      #(ensure! (not (identical? (:call-token program) (u/call-step-token)))
                :layout-generation-withdraws {}))
    (doseq [replacements changes]
      (with-redefs-fn
        replacements
        #(doseq [fuel [0 1 2 3 4 20]]
           (ensure! (= (attempt u/run! initial fuel identity)
                       (attempt (fn [s budget] (fusion/run! program s budget)) initial fuel identity))
                    :invalidation {:fuel fuel :vars (mapv str (keys replacements))}))))
    {:changed-roots-and-registry (count changes)}))

(def nested
  {:entry {:params [130]
           :body [:join 50 [129] [:return [:var 129]]
                  [:let 130 [:literal 100]
                   [:call 128 [:direct :worker] [[:var 130]] [:jump 50 [[:var 128]]]]]]}
   :worker {:params [130]
            :body [:join 60 [129] [:return [:var 129]]
                   [:call 128 [:direct :nat] [[:var 130] [:imm 3]]
                    [:suspend 127 [:jump 60 [[:var 128]]]]]]}
   :nat (wrapper "lean_nat_add")})

(defn forks! [fs]
  (let [program (fusion/open-program fs) initial (m/start (m/world fs) :entry [3])
        completed (m/run initial 1000) total (get-in completed [:stats :steps])]
    (doseq [fuel (range (+ 2 total))]
      (let [parent (fusion/run! program (u/thaw initial) fuel)
            saved (u/freeze parent)]
        (ensure! (= (m/run initial fuel) saved) :nested-prefix {:fuel fuel})
        (when (= :paused (:status saved))
          (ensure! (= completed (u/freeze (fusion/run! program (u/resume! parent nil) 1000)))
                   :nested-pause-resume {:fuel fuel}))
        (when (contains? #{:suspended :host-call} (:status saved))
          (doseq [answer [10 20]
                  :let [resumed (m/resume saved answer) done (m/run resumed 1000)
                        remaining (- (get-in done [:stats :steps]) (get-in saved [:stats :steps]))]
                  budget (range (+ 2 remaining))]
            (let [branch (u/resume! (u/thaw saved) answer)
                  actual (u/freeze (fusion/run! program branch budget))]
              (ensure! (= (m/run resumed budget) actual) :resumed-prefix {:budget budget})
              (when (= :paused (:status actual))
                (ensure! (= done (u/freeze (fusion/run! program (u/resume! branch nil) 1000)))
                         :resumed-pause {:budget budget}))))
          (ensure! (= saved (u/freeze parent)) :parent-unchanged {}))))
    {:prefixes (+ 2 total) :peak (get-in completed [:stats :max-frames]) :forks 2}))

(defn routes! []
  (let [fs (functions "lean_nat_add") program (fusion/open-program fs)
        census (volatile! {}) initial (m/start (m/world fs) :entry [20 22])
        actual (u/freeze (fusion/run! program (u/thaw initial) 20 true census))]
    (ensure! (= {:fused 1} @census) :positive-route {:census @census})
    (ensure! (= (m/run initial 20) actual) :positive-reference {})
    (let [tail (assoc-in fs [:entry :body] [:tail [:direct :nat] [[:var 0] [:var 1]]])
          closure (assoc-in fs [:entry :body]
                            [:let 2 [:closure :nat []]
                             [:call 3 [:closure [:var 2]] [[:var 0] [:var 1]] [:return [:var 3]]]])]
      (prefixes! tail [20 22]) (prefixes! closure [20 22]))
    (prefixes! fs [(native/native-scalar 20) 22])
    (let [world (assoc (m/world fs) :heap {0 {:kind :mpz :tag 250 :fields [] :rc 0
                                           :integer 184467440737095516160N}} :next-id 1)
          initial (m/start world :entry [(m/->Ref 0) 22])]
      (doseq [fuel (range 8)]
        (ensure! (= (attempt u/run! initial fuel identity)
                    (attempt #(fusion/run! program %1 %2) initial fuel identity))
                 :reference-operand {:fuel fuel})))
    {:positive-census @census :tail-closure-native-and-ref :ok}))

(defn budget-edges! []
  (let [fs (functions "lean_nat_add") program (fusion/open-program fs)
        initial (m/start (m/world fs) :entry [20 22])
        starts [initial (assoc-in initial [:stats :steps] (- Long/MAX_VALUE 3))
                (assoc-in initial [:stats :steps] (- Long/MAX_VALUE 2))
                (m/run initial 0) (m/run initial 20)]
        fuels [0 1 2 3 4 7 (int 0) (int 3) 3N 3/2]]
    (doseq [start starts fuel fuels]
      (ensure! (= (attempt u/run! start fuel identity)
                  (attempt #(fusion/run! program %1 %2) start fuel identity))
               :budget-edge {:fuel fuel :stats (:stats start) :status (:status start)}))
    (let [calls ^java.util.IdentityHashMap (:calls program)
          before (java.util.IdentityHashMap. calls)]
      (fusion/run! program (u/thaw initial) 20)
      (ensure! (and (= (.size before) (.size calls))
                    (every? #(identical? (.get before %) (.get calls %)) (.keySet before))
                    (identical? fs (:functions program)))
               :program-immutable {}))
    {:starts (count starts) :budgets (count fuels) :program-immutable :ok}))

(defn check! []
  {:arithmetic-cases (count (arithmetic!))
   :eligibility (eligibility!) :invalidation (invalidations!) :routes (routes!)
   :budget-edges (budget-edges!)
   :forks (forks! nested)
   :host (forks! (assoc-in nested [:worker :body 4 4]
                          [:host "wrapper-research" [[:var 128]] 127 [:jump 60 [[:var 128]]]]))})

(deftest guarded-arithmetic-and-carriers (arithmetic!))
(deftest ineligible-code-layouts-and-programs (eligibility!))
(deftest redefined-rules-and-registries-withdraw (invalidations!))
(deftest selected-and-fallback-routes (routes!))
(deftest exact-budget-and-counter-boundaries (budget-edges!))
(deftest nested-call-join-and-suspension-forks (forks! nested))
(deftest nested-host-response-forks
  (forks! (assoc-in nested [:worker :body 4 4]
                    [:host "wrapper-research" [[:var 128]] 127 [:jump 60 [[:var 128]]]])))

(deftest prepared-budget-does-not-follow-counter-deltas
  (let [fs (functions "lean_nat_add") initial (m/start (m/world fs) :entry [20 22])
        sites (java.util.IdentityHashMap.)
        dispatch (fn ^long [s ^long _] (u/add-steps! s 17) (long 3))]
    (.put sites (:body initial) true)
    (doseq [fuel [0 3]]
      (let [expected (with-redefs [u/step! (fn [s] (u/add-steps! s 17) s)]
                       (attempt u/run! initial (if (zero? fuel) 0 1) identity))
            actual (attempt #(u/run-prepared! %1 %2 sites dispatch) initial fuel identity)]
        (ensure! (= expected actual) :counter-independent-budget {:fuel fuel})))))

(deftest call-bridge-captures-fallback-before-argument-reads
  (let [fs (functions "lean_nat_add") initial (m/start (m/world fs) :entry [20 22])
        original u/call-values! read u/read-local
        attempt-one
        (fn [step]
          (let [s (u/thaw initial) reads (volatile! [])]
            (with-redefs [u/call-values! original
                          u/read-local (fn [locals id]
                                         (vswap! reads conj id)
                                         (alter-var-root #'u/call-values! (constantly (fn [& _] (throw (ex-info "Wrong selected root" {})))))
                                         (read locals id))]
              (step s))
            {:state (snapshot s) :reads @reads}))]
    (ensure! (= (attempt-one u/step!)
                (attempt-one (fn [s]
                               (u/call-step-with! s (fn [selected s target args dest continuation]
                                                     (ensure! (identical? original selected) :selected-call {})
                                                     (selected s target args dest continuation))))))
             :bridge-order {})))
