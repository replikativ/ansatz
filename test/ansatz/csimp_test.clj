(ns ansatz.csimp-test
  "#7: a/csimp surface macro = Lean's @[csimp]. Prove a verified `f = g`, register f→g in the :csimp
   Env extension, and codegen emits g wherever f appears (guarded by lowerability, so inherited
   compiler-internal targets that aren't in the store are skipped). a/implemented_by is the named
   alias of a/foreign (the @[implemented_by] correspondence)."
  (:require [clojure.test :refer [deftest is use-fixtures]]
            [ansatz.core :as a]
            [ansatz.codegen :as cg]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]))

(use-fixtures :once (fn [f] (a/load-init!) (binding [a/*verbose* false] (f))))

(defn- head-syms [code] (set (filter symbol? (tree-seq coll? seq code))))

(deftest csimp-verified-replacement-drives-codegen
  (binding [a/*verbose* false]
    ;; two verified fns, definitionally equal (cs-slow n →δ Nat.add n 0 →ι n; cs-fast n →δ n)
    (a/defn ^{:- Nat} cs-slow [^{:- Nat} n] (Nat.add n 0))
    (a/defn ^{:- Nat} cs-fast [^{:- Nat} n] n)
    ;; @[csimp]: prove cs-slow = cs-fast pointwise (rfl — both whnf to n), register cs-slow→cs-fast
    (a/csimp cs-eq [n :- Nat] (= Nat (cs-slow n) (cs-fast n)) (rfl))
    (is (= "cs-fast" (get (env/get-extension (a/env) :csimp {}) "cs-slow"))
        "a/csimp kernel-verified cs-slow = cs-fast and registered f→g into :csimp")
    ;; codegen now compiles cs-slow AS cs-fast (the verified replacement)
    (let [code (cg/ansatz->clj (a/env)
                               (e/app (e/const' (name/from-string "cs-slow") []) (e/lit-nat 5)) [])
          syms (head-syms code)]
      (is (contains? syms (symbol "cs-fast")) "codegen lowered cs-slow as its verified replacement")
      (is (not (contains? syms (symbol "cs-slow"))) "the original head cs-slow is gone"))))

(deftest csimp-guard-skips-unlowerable-target
  ;; The lowerability guard is what makes inheriting Lean's compiler-internal @[csimp]
  ;; (Nat.rec→Nat.recCompiled, List.length→List.lengthTR) safe: a target absent from the store must
  ;; NOT replace a working head with an unrunnable one.
  (binding [a/*verbose* false]
    (a/defn ^{:- Nat} cs-keep [^{:- Nat} n] n)
    (let [env  (env/update-extension (a/env) :csimp {} assoc "cs-keep" "No.Such.Target")
          code (cg/ansatz->clj env (e/app (e/const' (name/from-string "cs-keep") []) (e/lit-nat 5)) [])
          syms (head-syms code)]
      (is (contains? syms (symbol "cs-keep")) "unlowerable csimp target → original head kept")
      (is (not (contains? syms (symbol "No.Such.Target"))) "the bogus target is never emitted"))))

(deftest implemented-by-is-foreign-alias
  ;; a/implemented_by names the @[implemented_by] correspondence — same trusted-hole semantics as
  ;; a/foreign: a Clojure impl asserted at a kernel type, runnable.
  (binding [a/*verbose* false]
    (a/implemented_by ib-inc [x :- Nat] Nat (fn [x] (inc x)))
    (is (some? (env/lookup (a/env) (name/from-string "ib-inc"))) "the typed hole is in the env")
    (is (= 5 (ib-inc 4)) "and the Clojure impl runs")))
