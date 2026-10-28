(ns prepared-interpreter-checks
  "Bounded research checks. Load prepared-interpreter once first. No Source/Init."
  (:require [prepared-interpreter :as p]
            [prototype.machine :as m]
            [prototype.mutable :as u])
  (:import [java.util ArrayList]))

(def ^:dynamic *prepare-program* p/prepare-program)
(def ^:dynamic *step!* p/step!)
(def ^:dynamic *run!* p/run!)

(defn- ensure! [ok label data]
  (when-not ok (throw (ex-info (str "Prepared interpreter check failed: " label) data))))

(defn- outcome [f]
  (try (f) {:kind :ok}
       (catch Throwable error
         {:kind :error :class (class error) :message (ex-message error)
          :data (ex-data error)})))

(def ^:private storage-functions
  ;; Reserve ordinary local storage without asking slot-count to inspect the
  ;; deliberately malformed/mutable syntax used by some execution checks.
  {:storage {:params (vec (range 16)) :body [:return [:imm nil]]}})

(defn- machine [functions body locals]
  (let [snapshot (assoc (m/world storage-functions)
                        :status :running :body [:return [:imm nil]]
                        ;; thaw sizes the active continuation independently of
                        ;; global function width. Reserve real local storage.
                        :locals (assoc locals 15 ::storage-dead) :joins {} :frames [])
        result (assoc (u/thaw snapshot) :functions functions)]
    (u/set-body! result body)
    result))

(defn compare-prefixes!
  "Compare every frozen prefix and exact exception through <=199 steps.
  Deliberately malformed syntax reaches execution, not register preparation."
  ([functions body locals] (compare-prefixes! functions body locals 199))
  ([functions body locals limit]
   (let [program (*prepare-program* functions)
         ordinary (machine functions body locals)
         candidate (machine functions body locals)]
     (loop [n 0]
       (ensure! (= (u/freeze ordinary) (u/freeze candidate)) :prefix {:step n})
       (if (not= :running (u/status ordinary))
         {:steps n :status (u/status ordinary) :prepared (:prepared-lets program)}
         (do
           (ensure! (< n limit) :bounded {:limit limit :step n})
           (let [expected (outcome #(u/step! ordinary))
                 actual (outcome #(*step!* program candidate))]
             (ensure! (= expected actual) :outcome {:step n :expected expected :actual actual})
             (if (= :error (:kind expected))
               (do (ensure! (= (u/freeze ordinary) (u/freeze candidate))
                            :error-checkpoint {:step n :error expected})
                   {:steps (inc n) :error expected :prepared (:prepared-lets program)})
               (recur (inc n))))))))))

(defn- raw-case! [body locals]
  (compare-prefixes! {:main {:params [] :body body}} body locals))

(defn basic-checks! []
  (let [return [:return [:var 3]]
        samples
        [[:literal [:let 3 [:literal nil] return] {}]
         [:dead-binding [:let 3 [:literal :live] return] {0 :dead 1 nil}]
         [:ctor-project [:let 0 [:ctor 7 [[:imm nil] [:imm 42]]]
                         [:let 3 [:project [:var 0] 1] return]] {}]
         [:empty-ctor [:let 3 [:ctor 9 []] return] {}]
         [:runtime [:let 3 [:runtime "lean_nat_add" [[:imm 20] [:imm 22]]] return] {}]
         [:prim [:let 0 [:prim :inc [[:imm 20]]]
                 [:let 1 [:prim :dec [[:var 0]]]
                  [:let 3 [:prim :add [[:var 0] [:var 1]]] return]]] {}]
         [:zero [:let 3 [:prim :zero? [[:imm 0]]] return] {}]
         [:scalar-get [:let 0 [:box "uint64" [:imm 42]]
                       [:let 3 [:scalar-get [:var 0]
                                {:index 0 :offset 0 :type "uint64" :region :scalar}]
                        return]] {}]
         [:bad-destination [:let "bad" [:literal 1] return] {}]
         [:negative-destination [:let -1 [:literal 1] return] {}]
         [:bad-prim-input [:let 3 [:prim :inc [[:imm :bad]]] return] {}]
         [:bad-prim-arity [:let 3 [:prim :add [[:imm 1]]] return] {}]
         [:prim-overflow [:let 3 [:prim :inc [[:imm 9007199254740991]]] return] {}]
         [:unbound [:let 3 [:prim :add [[:var 0] [:var 1]]] return] {0 nil}]
         [:bad-project [:let 3 [:project [:imm nil] 0] return] {}]
         [:unsupported [:let 3 [:unbox "uint8" [:imm 7]] return] {}]
         [:trap [:trap :research []] {}]]]
    (mapv (fn [[label body locals]]
            (let [result (raw-case! body locals)]
              (when (contains? #{:literal :dead-binding :ctor-project :empty-ctor
                                 :runtime :prim :zero :scalar-get :unsupported} label)
                (ensure! (= :done (:status result)) :valid-sample-completed
                         {:sample label :result result}))
              [label result])) samples)))

(defn argument-order-check! []
  (let [body [:let 3 [:prim :add [[:var 0] [:var 1]]] [:return [:var 3]]]
        functions {:main {:params [] :body body}}
        program (*prepare-program* functions)
        original u/read-local
        execute (fn [step]
                  (let [s (machine functions body {0 :invalid 1 2})
                        seen (atom [])
                        result (with-redefs [u/read-local
                                             (fn [locals slot]
                                               (swap! seen conj slot)
                                               (original locals slot))]
                                 (outcome #(step s)))]
                    {:outcome result :reads @seen :world (u/freeze s)}))
        expected (execute u/step!)
        actual (execute #(*step!* program %))]
    (ensure! (= expected actual) :all-reads-before-validation {:expected expected :actual actual})
    (ensure! (= [0 1] (:reads actual)) :both-reads {:actual actual})
    :ok))

(defn generic-value-change-check! []
  (let [value-var (ns-resolve 'prototype.mutable 'value)
        value-original @value-var
        read-original u/read-local]
    (mapv
     (fn [[label expression]]
       (let [body [:let 3 expression [:return [:var 3]]]
             functions {:main {:params [] :body body}}
             program (*prepare-program* functions)
             execute
             (fn [step]
               (let [s (machine functions body {0 20}) log (atom [])
                     result
                     (with-redefs-fn
                       {value-var value-original
                        #'u/read-local
                        (fn [locals slot]
                          (swap! log conj [:read slot])
                          (alter-var-root value-var
                                          (constantly
                                           (fn [_ operand]
                                             (swap! log conj [:changed-value operand (meta operand)])
                                             100)))
                          (read-original locals slot))}
                       #(outcome (fn [] (step s))))]
                 {:outcome result :calls @log :world (u/freeze s)}))
             expected (execute #(u/step! %))
             actual (execute #(*step!* program %))]
         (ensure! (= expected actual) :generic-value-change
                  {:case label :expected expected :actual actual})
         (ensure! (some #(= :changed-value (first %)) (:calls actual))
                  :generic-value-hook-exercised {:case label})
         label))
     [[:args2 [:prim :add [[:var 0] (with-meta [:imm 2] {:original :operand})]]]
      [:args3 [:ctor 7 [[:var 0] [:imm 2] [:imm 3]]]]
      [:args-many [:ctor 7 [[:var 0] [:imm 2] [:imm 3] [:imm 4]]]]])))

(defn fallback-checks! []
  (let [body [:let 3 [:literal :static] [:return [:var 3]]]
        functions {:main {:params [] :body body}}
        program (*prepare-program* functions)
        dynamic-body [:let 3 [:literal :dynamic] [:return [:var 3]]]
        candidate (machine functions dynamic-body {})
        ordinary (machine functions dynamic-body {})]
    (u/step! ordinary)
    (*step!* program candidate)
    (ensure! (= (u/freeze ordinary) (u/freeze candidate)) :dynamic-body {})
    (let [operands (ArrayList. ^java.util.Collection [[:imm 1] [:imm 2]])
          mutable-body [:let 3 [:prim :add operands] [:return [:var 3]]]
          mutable-functions {:main {:params [] :body mutable-body}}
          mutable-program (*prepare-program* mutable-functions)
          a (machine mutable-functions mutable-body {})
          b (machine mutable-functions mutable-body {})]
      (ensure! (zero? (:prepared-lets mutable-program)) :mutable-operands-not-captured {})
      (.set operands 0 [:imm 40])
      (u/step! a)
      (*step!* mutable-program b)
      (ensure! (= (u/freeze a) (u/freeze b)) :mutated-operands {})
      (ensure! (= 42 (get-in (u/freeze b) [:locals 3])) :observed-mutation {}))
    (let [other (assoc functions :other {:params [] :body [:return [:imm 1]]})]
      (ensure! (= :error (:kind (outcome #(*step!* program (machine other body {})))))
               :program-identity {}))
    (let [sub-body (subvec (conj body :ignored) 0 (count body))
          sub-functions {:main {:params [] :body sub-body}}]
      (ensure! (zero? (:prepared-lets (*prepare-program* sub-functions)))
               :subvector-body-fallback {}))
    :ok))

(defn hook-fallback-checks! []
  (let [body [:let 3 [:prim :inc [[:var 0]]] [:return [:var 3]]]
        functions {:main {:params [] :body body}}
        ;; Prepare first, then replace roots: no user-installed root is learned.
        program (*prepare-program* functions)
        hook-vars (mapv #(ns-resolve 'prototype.mutable %) '[step! expr! value bump! ctl])]
    (mapv
     (fn [hook-var]
       (let [original @hook-var
             execute (fn [step]
                       (let [s (machine functions body {0 41}) seen (atom [])
                             result (with-redefs-fn
                                      {hook-var (fn [& arguments]
                                                  (swap! seen conj (count arguments))
                                                  (apply original arguments))}
                                      #(outcome (fn [] (step s))))]
                         {:outcome result :calls @seen :world (u/freeze s)}))
             expected (execute #(u/step! %))
             actual (execute #(*step!* program %))]
         (ensure! (= expected actual) :hook-fallback
                  {:hook (str hook-var) :expected expected :actual actual})
         (str hook-var))) hook-vars)))

(defn helper-selection-checks! []
  (let [field-var (ns-resolve 'prototype.mutable 'field-at)
        node-var (ns-resolve 'prototype.mutable 'node)
        allocate-var (ns-resolve 'prototype.mutable 'allocate!)
        read-original u/read-local
        ;; An immediate pointer into a deterministic local heap avoids a setup
        ;; read which might consume the hook before the expression under test.
        cases [[:node node-var [:project [:var 0] 0] {0 (m/->Ref 0)}]
               [:field field-var [:project [:var 0] 0] {0 (m/->Ref 0)}]
               [:allocate allocate-var [:ctor 7 [[:var 0]]] {0 42}]]]
    (mapv
     (fn [[label target expression locals]]
       (let [body [:let 3 expression [:return [:var 3]]]
             functions {:main {:params [] :body body}}
             program (*prepare-program* functions)
             original @target
             execute
             (fn [step]
               (let [s (machine functions body locals)
                     calls (atom [])
                     replacement (fn [& args]
                                   (swap! calls conj :replacement)
                                   (apply original args))]
                 ;; Seed identical owned storage, without executing guest code.
                 (.put ^java.util.Map (:heap s) 0
                       {:kind :ctor :tag 0 :fields (object-array [42]) :rc 1})
                 (aset ^objects (:control s) 3 1)
                 (let [result
                       (with-redefs-fn
                         {target original
                          #'u/read-local (fn [array slot]
                                           (alter-var-root target (constantly replacement))
                                           (read-original array slot))}
                         #(outcome (fn [] (step s))))]
                   {:outcome result :calls @calls :world (u/freeze s)})))
             expected (execute u/step!)
             actual (execute #(*step!* program %))]
         (ensure! (= expected actual) :helper-root-observation
                  {:helper label :expected expected :actual actual})
         (ensure! (empty? (:calls actual)) :helper-selected-before-operands {:helper label})
         label)) cases)))

(defn fork-resume-check! []
  (let [functions
        {:entry {:params [7]
                 :body [:join 42 [9]
                        [:let 13 [:prim :add [[:var 7] [:var 9]]] [:return [:var 13]]]
                        [:let 7 [:literal 100]
                         [:call 14 [:direct :worker] [[:var 7]] [:jump 42 [[:var 14]]]]]]}
         :worker {:params [5] :body [:suspend 11 [:return [:var 11]]]}}
        initial (m/start (m/world functions) :entry [3])
        program (*prepare-program* functions)
        parent (*run!* program (u/thaw initial) 100)
        saved (u/freeze parent)]
    (ensure! (= :suspended (:status saved)) :fork-suspended {})
    (ensure! (= 1 (count (:frames saved))) :fork-caller-frame {})
    (ensure! (= 3 (get-in saved [:frames 0 :joins 42 :locals 7])) :fork-captured-join {})
    (ensure! (= 100 (get-in saved [:frames 0 :locals 7])) :fork-caller-local {})
    (doseq [answer [10 20]]
      (let [ordinary (u/resume! (u/thaw saved) answer)
            candidate (u/resume! (u/thaw saved) answer)]
        (loop [n 0]
          (ensure! (= (u/freeze ordinary) (u/freeze candidate)) :fork-prefix {:answer answer :step n})
          (when (= :running (u/status ordinary))
            (ensure! (< n 100) :fork-bound {})
            (u/step! ordinary)
            (*step!* program candidate)
            (recur (inc n))))
        (ensure! (= (+ 3 answer) (:result (u/freeze candidate))) :fork-answer {:answer answer})
        (ensure! (= saved (u/freeze parent)) :fork-parent-unchanged {})))
    {:status :ok :forks 2 :captured-frames (count (:frames saved))}))

(defn check!
  "Run bounded raw-IR checks. Optional variant map supplies :prepare-program,
  :step! and :run! without redefining protocol-provider Vars."
  ([]
   {:basic (basic-checks!)
    :argument-order (argument-order-check!)
    :generic-value-change (generic-value-change-check!)
    :fallback (fallback-checks!)
    :hook-fallback (hook-fallback-checks!)
    :helper-selection (helper-selection-checks!)
    :fork-resume (fork-resume-check!)})
  ([variant]
   (binding [*prepare-program* (get variant :prepare-program *prepare-program*)
             *step!* (get variant :step! *step!*)
             *run!* (get variant :run! *run!*)]
     (check!))))
