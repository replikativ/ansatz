(ns ansatz.tactic.level1-test
  (:require [clojure.test :refer [deftest is]]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]
            [ansatz.tactic.basic :as basic]
            [ansatz.tactic.proof :as proof]
            [ansatz.tactic.extract :as extract]
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
(defn- nat-eq [a b] (e/app* (e/const' (name/from-string "Eq") [u1]) nat a b))
(defn- fh [ps n] (some (fn [[id d]] (when (= n (:name d)) id)) (:lctx (proof/current-goal ps))))

(deftest test-grind-transitivity
  (let [goal (e/forall' "a" nat (e/forall' "b" nat (e/forall' "c" nat
                                                              (e/forall' "h1" (nat-eq (e/bvar 2) (e/bvar 1))
                                                                         (e/forall' "h2" (nat-eq (e/bvar 2) (e/bvar 1))
                                                                                    (nat-eq (e/bvar 4) (e/bvar 2)) :default) :default) :default) :default) :default)
        [ps _] (proof/start-proof (env) goal)
        ps (basic/intros ps ["a" "b" "c" "h1" "h2"])
        ps (grind/grind ps)]
    (is (proof/solved? ps))
    (extract/verify ps)))

(deftest test-induction-rfl
  (let [goal (e/forall' "n" nat (nat-eq (e/bvar 0) (e/bvar 0)) :default)
        [ps _] (proof/start-proof (env) goal)
        ps1 (basic/intro ps "n")
        ps2 (basic/induction ps1 (fh ps1 "n"))
        ps3 (basic/rfl ps2)
        ps4 (basic/rfl ps3)]
    (is (proof/solved? ps4))
    (extract/verify ps4)))

