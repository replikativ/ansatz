(ns prototype.deep-ir-test
  (:require [clojure.test :refer [deftest is]]
            [prototype.import-ir :as ir]
            [prototype.machine :as m]
            [prototype.mutable :as u]
            [prototype.block-compile :as blocks]
            [prototype.lazy-runtime :as lazy]
            [prototype.fingerprint :as fingerprint]
            [prototype.walk :as walk]))

(def root ["str" ["anonymous"] "deepRoot"])
(def leaf ["str" ["anonymous"] "leaf"])
(def callback ["str" ["anonymous"] "callback"])
(defn- var-arg [i] {:var {:id {:idx i}}})
(defn- parameter [i ty] {:x {:idx i} :ty ty :borrow false})
(defn- row [name params body]
  {:kind "decl" :name name :runtime {:role "ordinary"}
   :ir {:fdecl {:f name :xs params :type "object" :body body}}})
(defn- literal [i n continuation]
  ["vdecl" {:idx i} "object" {:lit {:v {:num {:v n}}}} continuation])
(defn- call-return [name args]
  ["vdecl" {:idx 5001} "object" {:fap {:c name :ys args}} ["ret" (var-arg 5001)]])
(defn- catalogue [& rows]
  {:manifests [] :declarations (into {} (map (juxt :name identity)) rows)})

(defn- deep-functions []
  (let [raw (reduce (fn [continuation i] (literal i i continuation))
                    (call-return leaf [(var-arg 4000)]) (range 4000 -1 -1))]
    (ir/load-closure (catalogue (row root [] raw)
                               (row leaf [(parameter 0 "object")] ["ret" (var-arg 0)])) [root])))

(deftest four-thousand-declarations-lower-link-and-run
  (let [functions (deep-functions)
        normalized (:body (get functions root))
        result (m/run (m/start (m/world functions) root []) 5000)]
    (is (= 4001 (count (filter #(and (vector? %) (= :let (first %))) (walk/forms normalized)))))
    (is (= 1 (count (filter #(and (vector? %) (= :tail (first %))) (walk/forms normalized)))))
    (is (= #{root leaf} (set (keys functions))))
    (is (= :done (:status result)))
    (is (= 4000 (:result result)))
    (is (= 4003 (get-in result [:stats :steps])))))

(defn- check-linear-state [expected actual]
  ;; Reused compiled code may keep the previous program's equivalent immutable
  ;; continuation node. Structural equality itself recurses on a deep vector,
  ;; so compare that code by its stack-safe key and all execution data directly.
  (is (= (fingerprint/key (:body expected)) (fingerprint/key (:body actual))))
  (is (= (dissoc expected :functions :body) (dissoc actual :functions :body))))

(deftest deep-linear-regions-preserve-all-backends-and-pause-boundaries
  (let [functions (deep-functions)
        initial (m/start (m/world functions) root [])
        completed (m/run initial 5000)
        eager-plain (blocks/compile-program functions)
        eager-lexical (blocks/compile-program functions nil {:lexical-joins true})
        demand (lazy/open-program functions)
        runners [#(u/run! %1 %2)
                 #(blocks/run! eager-plain %1 %2)
                 #(blocks/run! eager-lexical %1 %2)
                 #(lazy/run! demand %1 %2)]]
    (doseq [fuel [0 1 127 128 129 255 256 257 4001 4002 4003 4004]
            run runners]
      (let [machine (run (u/thaw initial) fuel)
            captured (u/freeze machine)]
        (check-linear-state (m/run initial fuel) captured)
        (when (= :paused (:status captured))
          (check-linear-state completed (u/freeze (run (u/resume! machine nil) 5000))))))
    (is (> (:compiled-blocks eager-plain) 1))
    (is (> (:compiled (lazy/summary demand)) 1))))

(deftest independent-equivalent-deep-programs-reuse-compiled-code
  (let [functions (deep-functions)
        copied-functions (deep-functions)
        initial (m/start (m/world functions) root [])
        copied-initial (m/start (m/world copied-functions) root [])
        eager (blocks/compile-program functions nil {:lexical-joins true})
        reused (blocks/compile-program copied-functions eager {:lexical-joins true})
        cache (lazy/code-cache)
        original (lazy/open-program functions {} cache)
        copied (lazy/open-program copied-functions {} cache)]
    (is (not (identical? (get-in functions [root :body]) (get-in copied-functions [root :body]))))
    (is (= 0 (:compiled-blocks reused)))
    (is (= (:compiled-blocks eager) (:reused-blocks reused)))
    (lazy/run! original (u/thaw initial) 5000)
    (check-linear-state (m/run copied-initial 5000)
                        (u/freeze (lazy/run! copied (u/thaw copied-initial) 5000)))
    (is (= 0 (:compiled (lazy/summary copied))))
    (is (pos? (:cache-hits (lazy/summary copied))))
    (doseq [run [#(blocks/run! reused %1 %2) #(lazy/run! copied %1 %2)]
            fuel [0 1 127 128 129]]
      (let [machine (run (u/thaw copied-initial) fuel)
            captured (u/freeze machine)]
        (check-linear-state (m/run copied-initial fuel) captured)
        (check-linear-state (m/run copied-initial 5000)
                            (u/freeze (run (u/resume! machine nil) 5000)))))))

(deftest nested-joins-cases-closures-and-persistent-flags
  (let [joined (call-return leaf [(var-arg 2)])
        branch ["vdecl" {:idx 3} "object" {:pap {:c callback :ys []}}
                ["inc" {:idx 3} 1 true true
                 ["dec" {:idx 3} 1 true true ["jmp" {:idx 1} [(var-arg 0)]]]]]
        raw ["jdecl" {:idx 1} [(parameter 2 "object")] joined
             ["case" root {:idx 0} "object"
              [["ctor" {:cidx 0} branch] ["default" ["ret" "erased"]]]]]
        normalized (ir/body raw)
        expected [:join 1 [2] [:tail [:direct leaf] [[:var 2]]]
                  [:case [:var 0]
                   [[0 [:let 3 [:closure callback []]
                        [:inc [:var 3] 1 [:dec [:var 3] 1 [:jump 1 [[:var 0]]] true] true]]]
                    [:default [:return [:imm m/erased]]]]]]
        functions (ir/load-closure
                   (catalogue (row root [(parameter 0 "object")] raw)
                              (row leaf [(parameter 0 "object")] ["ret" (var-arg 0)])
                              (row callback [] ["ret" "erased"])) [root])]
    (is (= expected normalized))
    (is (= (first (get-in expected [4 2])) (ir/alternative ["ctor" {:cidx 0} branch])))
    (is (= #{root leaf callback} (set (keys functions))))
    ;; Run the default branch: the other branch deliberately exercises static
    ;; persistence annotations on a newly allocated closure and must not run.
    (is (= m/erased (:result (m/run (m/start (m/world functions) root [(m/->Tag 1)]) 100))))))

(deftest generic-walk-is-stack-safe-and-preserves-preorder
  (let [sample [nil [1 []] {:a '(2 3)}]]
    (is (= (vec (tree-seq coll? seq sample)) (vec (walk/forms sample)))))
  (let [deep (nth (iterate vector :end) 12000)
        forms (walk/forms deep)]
    (is (= 12001 (count forms)))
    (is (= :end (last forms))))
  (is (= [nil] (vec (walk/forms nil)))))

(deftest deep-persistent-graph-matches-reference-without-replacing-fields
  (let [[world root] (reduce (fn [[world tail] _] (m/allocate world :ctor 1 [tail]))
                             [(m/world {}) (m/->Tag 0)] (range 4001))
        expected (m/mark-persistent world root)
        machine (u/thaw world)
        fields (:fields (.get ^java.util.Map (:heap machine) (:id root)))]
    (u/mark-persistent! machine root)
    (let [marked (u/freeze machine)]
      (is (= (:heap expected) (:heap marked)))
      (is (every? #(zero? (:rc %)) (vals (:heap marked))))
      (is (identical? fields (:fields (.get ^java.util.Map (:heap machine) (:id root)))))
      (is (every? #(= 1 (:rc %)) (vals (:heap world)))))))

(deftest deep-profile-validation-and-ordinary-type-guards-remain-enforced
  (let [scalar ["vdecl" {:idx 4001} "object" {:box {:ty "uint64" :x {:idx 0}}}
                ["ret" (var-arg 4001)]]
        raw (reduce (fn [continuation i] (literal i i continuation)) scalar (range 4000 -1 -1))
        root-row (row root [] raw)
        without-profile (catalogue root-row)
        manifest {:schema "lean-ir-probe/1" :leanVersion "4.33.1"
                  :runtimeProfile {:wordBits 64 :target "x86_64-unknown-linux-gnu"}}]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"explicit runtime profile"
                         (ir/load-closure without-profile [root])))
    (is (= #{root} (set (keys (ir/load-closure (assoc without-profile :manifests [manifest]) [root])))))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Unsupported runtime profile"
                         (ir/load-closure (assoc without-profile :manifests [(assoc-in manifest [:runtimeProfile :wordBits] 32)]) [root]))))
  (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Unsupported imported runtime type"
                       (ir/lower-declaration (row root [(parameter 0 "float128")] ["ret" "erased"]))))
  (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Unknown alternative"
                       (ir/body ["case" root {:idx 0} "object" [["invalid"]]]))))
