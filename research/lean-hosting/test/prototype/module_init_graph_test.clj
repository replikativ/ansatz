(ns prototype.module-init-graph-test
  "Differential host-only tests. No raw/guest/compiler execution is needed."
  (:require [clojure.test :refer [deftest is testing]]
            [clojure.set :as set]
            [prototype.module-init-capabilities :as capability]
            [prototype.module-plan :as plan]
            [prototype.machine :as m]))

(defn name-of [x] ["str" ["anonymous"] (str x)])
(defn producer [name split imports]
  {:schema "lean-init-plan/1" :module name :moduleSystem split
   :imports (mapv (fn [[module meta]] {:module module :meta meta}) imports)
   :actions [{:meta false :action {:kind "value" :name name :target name}}]})
(defn symbol-of [[name phase]] (str (nth name 2) "/" (clojure.core/name phase)))
(defn entries [plans]
  (vec (for [[name p] plans phase (if (:moduleSystem p) [:all :runtime :comptime] [:all])]
         [name phase])))
(defn available [binding guards symbol]
  (let [world (assoc (m/world {}) :initialized-modules guards)
        [after value] ((:handler binding) nil world [symbol m/erased])]
    {:value (:fields (m/node after value)) :before world :after after :root value}))
(defn subsets [xs]
  (reduce (fn [sets x] (into sets (map #(conj % x)) sets)) [#{}] xs))
(defn bindings-for [plans]
  (capability/make-bindings
    {:module-plans plans
     :initialized-symbols (into {} (for [[module phase :as entry] (entries plans)]
                                    [(symbol-of entry) {:module module :phase phase}]))}))

(deftest shared-graph-matches-plan-expand-for-complete-and-partial-worlds
  (let [[a b c d] (mapv name-of ["A" "B" "C" "D"])
        examples
        {:classic-diamond {a (producer a false [[b false] [c true]])
                           b (producer b false [[d false]])
                           c (producer c false [[d true]]) d (producer d false [])}
         :classic-cycle {a (producer a false [[b false]]) b (producer b false [[a true]])}
         :self-cycle {a (producer a true [[a true] [a false]])}
         :split-cycle {a (producer a true [[b true] [b false]])
                       b (producer b true [[a false]])}
         :split-diamond {a (producer a true [[b false] [c true]])
                         b (producer b true [[d true]])
                         c (producer c true [[d false]]) d (producer d true [])}
         :mixed-classic-root {a (producer a false [[b false]])
                              b (producer b true [[c true]]) c (producer c true [])}}]
    (doseq [[label plans] examples]
      (testing (name label)
        (let [roots (entries plans) universe (set roots)
              worlds (if (<= (count roots) 9) (subsets roots)
                         (distinct (concat [#{} universe]
                                           (map hash-set roots)
                                           (map #(disj universe %) roots)
                                           [(set (filter #(= :all (second %)) roots))])))
              binding (get (bindings-for plans) "lean_run_mod_init_core")]
          (doseq [[module phase :as root] roots
                  :let [needed (:initialized (plan/expand plans module phase))]
                  guards worlds]
            (let [expected (if (set/subset? needed guards) [1] [0])
                  result (available binding guards (symbol-of root))]
              (is (= expected (:value result)) (str label " " (symbol-of root) " partial=" (count guards)))
              (is (= guards (get-in result [:after :initialized-modules])))
              (is (= (:heap (:before result)) (:heap (m/release (:after result) (:root result) 1))))))))))

(deftest entry-guard-does-not-prove-cycle-or-diamond-completion
  (let [[a b c d] (mapv name-of ["A" "B" "C" "D"])
        plans {a (producer a false [[b false] [c false]])
               b (producer b false [[d false]])
               c (producer c false [[d false]]) d (producer d false [[b false]])}
        binding (get (bindings-for plans) "lean_run_mod_init_core")]
    (is (= [0] (:value (available binding #{[a :all]} (symbol-of [a :all])))))
    (is (= [0] (:value (available binding #{[a :all] [b :all] [c :all]} (symbol-of [a :all])))))
    (is (= [1] (:value (available binding #{[a :all] [b :all] [c :all] [d :all]} (symbol-of [a :all])))))
    (is (= [0] (:value (available binding #{[a :all] [b :all] [c :all] [d :all]} "unknown"))))))

(deftest guard-graph-retains-direct-edges-rather-than-per-root-closures
  (let [names (mapv name-of (range 80))
        plans (into {} (map-indexed (fn [i name]
                                     [name (producer name false (if (zero? i) [] [[(nth names (dec i)) false]]))]) names))
        roots (entries plans)
        graph (#'capability/guard-dependency-graph plans roots)]
    (is (= 80 (count graph)))
    (is (= 79 (reduce + (map count (vals graph)))))
    (is (= 80 (count (:initialized (plan/expand plans (peek names) :all)))))
    (is (= [1] (:value (available (get (bindings-for plans) "lean_run_mod_init_core")
                                  (set roots) (symbol-of [(peek names) :all])))))))

(deftest invalid-reachable-entry-fails-before-capability-publication
  (let [[a b] (mapv name-of ["A" "B"])
        options {:module-plans {a (producer a true [[b false]])}
                 :initialized-symbols {"A" {:module a :phase :all}}}]
    (is (thrown-with-msg? Exception #"Missing producer" (capability/make-bindings options))))
  (let [a (name-of "A")]
    (is (thrown-with-msg? Exception #"Classic Lean module"
                         (capability/make-bindings {:module-plans {a (producer a false [])}
                                                   :initialized-symbols {"A" {:module a :phase :runtime}}}))))
  (let [binding (get (capability/make-bindings) "lean_run_mod_init_core")]
    (is (thrown-with-msg? Exception #"must be a set" (available binding [:wrong] "unknown"))))))

(deftest malformed-reachable-action-collection-still-fails-at-construction
  (let [a (name-of "A") b (name-of "B")]
    (doseq [split [false true]
            :let [plans {a (producer a split [[b false]])
                         b (assoc (producer b split []) :actions 42)}]]
      (is (thrown? Exception (plan/expand plans a :all)))
      (is (thrown? Exception (bindings-for plans))))
    ;; Payloads are opaque here, as before. No action execution or new strict
    ;; action-schema policy is smuggled into a guard-availability optimization.
    (let [plans {a (assoc (producer a true []) :actions [{:action [:opaque-data] :meta false}])}
          binding (get (bindings-for plans) "lean_run_mod_init_core")]
      (is (= [1] (:value (available binding (:initialized (plan/expand plans a :all))
                                    (symbol-of [a :all]))))))))
