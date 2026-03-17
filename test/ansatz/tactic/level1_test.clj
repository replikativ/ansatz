(ns ansatz.tactic.level1-test
  (:require [clojure.test :refer [deftest testing is run-tests]]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.env :as env]
            [ansatz.tactic.basic :as basic]
            [ansatz.tactic.proof :as proof]
            [ansatz.tactic.extract :as extract]
            [ansatz.tactic.simp :as simp]
            [ansatz.tactic.omega :as omega]
            [ansatz.tactic.grind :as grind]
            [ansatz.export.parser :as parser]
            [ansatz.export.replay :as replay]))

(def ^:private test-env
  (delay
    (let [f "test-data/init-medium.ndjson"]
      (when (.exists (java.io.File. f))
        (:env (replay/replay (:decls (parser/parse-ndjson-file f))))))))

(defn- env [] (or @test-env (throw (ex-info "no env" {}))))
(def ^:private nat (e/const' (name/from-string "Nat") []))
(def ^:private u1 (lvl/succ lvl/zero))
(def ^:private prop (e/sort' lvl/zero))
(defn- nat-eq [a b] (e/app* (e/const' (name/from-string "Eq") [u1]) nat a b))
(defn- hadd [a b]
  (e/app* (e/const' (name/from-string "HAdd.hAdd") [lvl/zero lvl/zero lvl/zero])
          nat nat nat (e/app* (e/const' (name/from-string "instHAdd") [lvl/zero])
                              nat (e/const' (name/from-string "instAddNat") []))
          a b))
(defn- fh [ps n] (some (fn [[id d]] (when (= n (:name d)) id)) (:lctx (proof/current-goal ps))))

(deftest test-grind-transitivity
  (if-not (try (Class/forName "smt.EGraph") true (catch Exception _ false))
    (is true "skipped: zustand not available")
    (let [goal (e/forall' "a" nat (e/forall' "b" nat (e/forall' "c" nat
                                                                (e/forall' "h1" (nat-eq (e/bvar 2) (e/bvar 1))
                                                                           (e/forall' "h2" (nat-eq (e/bvar 2) (e/bvar 1))
                                                                                      (nat-eq (e/bvar 4) (e/bvar 2)) :default) :default) :default) :default) :default)
          [ps _] (proof/start-proof (env) goal)
          ps (basic/intros ps ["a" "b" "c" "h1" "h2"])
          ps (grind/grind ps)]
      (is (proof/solved? ps))
      (extract/verify ps))))

(deftest test-induction-rfl
  (let [goal (e/forall' "n" nat (nat-eq (e/bvar 0) (e/bvar 0)) :default)
        [ps _] (proof/start-proof (env) goal)
        ps (basic/intro ps "n")]
    (let [ps (basic/induction ps (fh ps "n"))
          ps (basic/rfl ps)
          ps (basic/rfl ps)]
      (is (proof/solved? ps))
      (extract/verify ps))))

