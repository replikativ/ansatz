(ns ansatz.indexed-inductive-test
  "Tests for indexed inductive families (Vec, Fin, etc.)."
  (:require [clojure.test :refer [deftest testing is use-fixtures]]
            [ansatz.core :as a]
            [ansatz.inductive :as ind]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.tc :as tc]
            [ansatz.export.parser :as parser]
            [ansatz.export.replay :as replay]))

;; ============================================================
;; Environment setup
;; ============================================================

(def ^:private init-env
  (delay
    (let [f "test-data/init-medium.ndjson"]
      (when (.exists (java.io.File. f))
        (:env (replay/replay (:decls (parser/parse-ndjson-file f))))))))

(defn- ensure-tvec []
  (when-not (env/lookup (a/env) (name/from-string "TVec"))
    (ind/define-inductive (a/env) "TVec"
      '[alpha Type]
      [['nil [] [0]]
       ['cons ['a 'alpha 'n 'Nat 'tail '(TVec alpha n)] ['(+ n 1)]]]
      :indices '[n Nat])))

(defn- with-init-env [f]
  (when-let [env @init-env]
    (reset! a/ansatz-env env)
    (f)))

(use-fixtures :once with-init-env)

;; ============================================================
;; Vec: length-indexed vector
;; ============================================================

(deftest test-vec-definition
  (testing "Define Vec (alpha : Type) : Nat -> Type"
    (ensure-tvec)
    ;; Check all declarations exist
    (is (some? (env/lookup (a/env) (name/from-string "TVec"))))
    (is (some? (env/lookup (a/env) (name/from-string "TVec.nil"))))
    (is (some? (env/lookup (a/env) (name/from-string "TVec.cons"))))
    (is (some? (env/lookup (a/env) (name/from-string "TVec.rec"))))))

(deftest test-vec-types
  (testing "Vec constructor types are correct"
    ;; Re-define if not present
    (ensure-tvec)
    ;; Vec.nil Nat : Vec Nat 0
    (let [st (tc/mk-tc-state (a/env))
          nat (e/const' (name/from-string "Nat") [])
          nil-nat (e/app (e/const' (name/from-string "TVec.nil") []) nat)
          ty (tc/infer-type st nil-nat)
          ty-str (e/->string ty)]
      (is (clojure.string/includes? ty-str "TVec"))
      (is (clojure.string/includes? ty-str "0")))
    ;; Vec.cons Nat 42 0 nil : Vec Nat (0 + 1)
    (let [st (tc/mk-tc-state (a/env))
          nat (e/const' (name/from-string "Nat") [])
          nil-nat (e/app (e/const' (name/from-string "TVec.nil") []) nat)
          cons-term (e/app* (e/const' (name/from-string "TVec.cons") [])
                            nat (e/lit-nat 42) (e/lit-nat 0) nil-nat)
          ty (tc/infer-type st cons-term)
          ty-str (e/->string ty)]
      (is (clojure.string/includes? ty-str "TVec"))
      (is (clojure.string/includes? ty-str "HAdd") "return type has n+1"))))

(deftest test-vec-recursor-structure
  (testing "Vec.rec has correct structure (motive takes index + major)"
    (ensure-tvec)
    (let [rec-ci (env/lookup (a/env) (name/from-string "TVec.rec"))]
      (is (some? rec-ci))
      (is (= 1 (.numParams rec-ci)) "1 param (alpha)")
      (is (= 1 (.numIndices rec-ci)) "1 index (n)")
      (is (= 1 (.numMotives rec-ci)) "1 motive")
      (is (= 2 (.numMinors rec-ci)) "2 minors (nil, cons)"))))

(deftest test-vec-backward-compat
  (testing "Non-indexed types still work"
    (ind/define-inductive (a/env) "TColor2"
      '[]
      [['red []] ['green []] ['blue []]])
    (is (some? (env/lookup (a/env) (name/from-string "TColor2"))))
    (is (some? (env/lookup (a/env) (name/from-string "TColor2.red"))))
    (is (some? (env/lookup (a/env) (name/from-string "TColor2.rec"))))
    (let [rec-ci (env/lookup (a/env) (name/from-string "TColor2.rec"))]
      (is (= 0 (.numIndices rec-ci)) "non-indexed type has 0 indices"))))

;; ============================================================
;; Fin: bounded natural (simpler indexed family)
;; ============================================================

(deftest test-fin-definition
  (testing "Define Fin : Nat -> Type (bounded naturals)"
    ;; Fin : Nat → Type
    ;; Fin.zero : Fin (n + 1) — for any n
    ;; Fin.succ : Fin n → Fin (n + 1)
    ;; Note: zero and succ both have implicit n, which appears as a field here
    (ind/define-inductive (a/env) "TFin"
      '[]
      [['zero ['n 'Nat] ['(+ n 1)]]
       ['succ ['n 'Nat 'i '(TFin n)] ['(+ n 1)]]]
      :indices '[n Nat])
    (is (some? (env/lookup (a/env) (name/from-string "TFin"))))
    (is (some? (env/lookup (a/env) (name/from-string "TFin.zero"))))
    (is (some? (env/lookup (a/env) (name/from-string "TFin.succ"))))
    (is (some? (env/lookup (a/env) (name/from-string "TFin.rec"))))
    (let [rec-ci (env/lookup (a/env) (name/from-string "TFin.rec"))]
      (is (= 0 (.numParams rec-ci)) "0 params")
      (is (= 1 (.numIndices rec-ci)) "1 index (n)"))))
