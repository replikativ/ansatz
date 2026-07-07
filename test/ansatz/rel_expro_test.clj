;; expro — type-directed OPEN-GRAMMAR term synthesis (not a finite candidate
;; set): enumerate well-typed terms from a grammar, constrain by I/O examples
;; via kernel reduction, kernel-certify the result.
(ns ansatz.rel-expro-test
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [ansatz.rel :as r]
            [ansatz.rel.barliman :as b]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.reduce :as red]
            [ansatz.export.parser :as parser]
            [ansatz.export.replay :as replay]))

(def ^:private init-medium-env
  (delay
    (let [f "test-data/init-medium.ndjson"]
      (when (.exists (java.io.File. f))
        (:env (replay/replay (:decls (parser/parse-ndjson-file f))))))))

(def ^:dynamic *env* nil)

(use-fixtures :once
  (fn [f]
    (binding [*env* (or @init-medium-env
                        (throw (ex-info "init-medium.ndjson not found" {})))]
      (f))))

;; grammar: two Nat locals a,b plus the constructors/ops {Nat.succ, Nat.add}
(def ^:private a-id 50)
(def ^:private b-id 51)
(def ^:private lctx
  (delay (-> (red/empty-lctx)
             (red/lctx-add-local a-id "a" b/NAT)
             (red/lctx-add-local b-id "b" b/NAT))))
(def ^:private cands [[3 "Nat.succ"] [2 "Nat.add"]])

(defn- eval-at
  "Close term `t` (over the locals a,b) into (λ a b. t) and apply to inputs —
   the kernel reduces it, so === against the expected output is a real test."
  [t av bv]
  (let [body (e/abstract-many t [a-id b-id])
        f (e/lam "a" b/NAT (e/lam "b" b/NAT body :default) :default)]
    (e/app (e/app f (b/lit av)) (b/lit bv))))

(defn- synth [examples depth n]
  (r/run n (r/state *env* :lctx @lctx)
         (r/fresh b/NAT
                  (fn [g]
                    (r/all (r/expro g cands depth)
                           (r/project*
                            (fn [s]
                              (let [t (r/zonk s g)]
                                (apply r/all
                                       (for [[av bv out] examples]
                                         (r/=== (eval-at t av bv) (b/lit out)))))))
                           (fn [s] (r/unit (assoc s :t (r/zonk s g) :g g))))))))

(deftest open-grammar-enumeration
  (testing "expro enumerates the OPEN grammar (nested terms), not a finite list"
    (let [terms (->> (r/run 8 (r/state *env* :lctx @lctx)
                            (r/fresh b/NAT
                                     (fn [g] (r/all (r/expro g cands 2)
                                                    (fn [s] (r/unit (assoc s :t (r/zonk s g))))))))
                     (map #(e/->string (:t %)))
                     set)]
      ;; leaves, and both operators, appear in the enumerated grammar
      (is (contains? terms "?fv50"))
      (is (some #(clojure.string/includes? % "Nat.add") terms))
      (is (some #(clojure.string/includes? % "Nat.succ") terms)))))

(deftest synthesize-structure-from-examples
  (testing "synthesize the STRUCTURE Nat.add a b (depth-1 app) from I/O examples"
    (let [sols (map :t (synth [[2 3 5] [4 1 5]] 2 6))
          strs (set (map e/->string sols))]
      ;; add a b and add b a both satisfy (add is commutative on these inputs)
      (is (contains? strs "(Nat.add ?fv50 ?fv51)"))
      (is (every? #(= "Nat.add" (some-> % e/app-fn e/app-fn e/const-name
                                        ansatz.kernel.name/->string))
                  sols)
          "every solution is add-headed — succ/leaf terms were pruned by the examples"))))

(deftest synthesize-nested-and-certify
  (testing "depth-2 nesting: succ(add a b) etc. from t(2,3)=6,t(4,1)=6; certify"
    (let [sols (synth [[2 3 6] [4 1 6]] 2 4)
          strs (set (map #(e/->string (:t %)) sols))]
      (is (seq sols) "found depth-2 nested solutions")
      (is (some #(or (clojure.string/starts-with? % "(Nat.succ (Nat.add")
                     (clojure.string/starts-with? % "(Nat.add")) strs))
      ;; the synthesized term, closed over a,b:Nat, strictly kernel-certifies
      (let [s (first sols)
            c (r/certify s (:g s))]
        (is (:ok? c) "kernel verifies (λ a b. <synthesized>) : Nat → Nat → Nat")))))
