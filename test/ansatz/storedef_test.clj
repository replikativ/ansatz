(ns ansatz.storedef-test
  "Equation-driven runtime compilation of plain store defs (ansatz.codegen.storedef):
   a recursive store def compiles from its exported f.eq_def theorem into a Clojure fn
   with `recur` at tail self-calls, interned under its dotted Lean name in
   ansatz.storedef.runtime and registered {:arity :erased :sym} — which re-activates the
   csimp TR rewrites through the #62 lowerability guard. Store-backed cases skip
   gracefully when the booted store carries no equation lemmas."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [ansatz.core :as a]
            [ansatz.codegen :as cg]
            [ansatz.codegen.storedef :as sd]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.name :as name]))

(use-fixtures :once (fn [f] (a/load-init!) (binding [a/*verbose* false] (f))))

(defn- has-decl? [n] (some? (env/lookup (a/env) (name/from-string n))))

;; ── pure form-rewrite units (no store needed) ────────────────────────────────

(deftest form-beta-exposes-tail-positions
  (let [beta @#'sd/form-beta]
    (is (= '(let [x 1] x) (beta '((fn [x] x) 1))))
    (testing "application of a let (curried chain) pushes inside"
      (is (= '(let [x 1] (let [y 2] (f x y)))
             (beta '(((fn [x] (fn [y] (f x y))) 1) 2)))))))

(deftest rewrite-self-recur-vs-named
  (let [rw @#'sd/rewrite-self
        dsym (symbol "Fake.self")]
    (testing "tail self-call becomes recur, erased prefix stripped"
      (is (= '(if c 0 (recur t (inc n)))
             (rw (list 'if 'c 0 (list dsym 'A 't '(inc n))) dsym 'self_ 1 3))))
    (testing "self-call under an inner fn boundary takes the named call, never recur"
      (let [out (rw (list 'if 'c 0 (list 'fn '[k] (list dsym 'A 'k 'n))) dsym 'self_ 1 3)]
        (is (= '(if c 0 (fn [k] (self_ k n))) out))))
    (testing "non-tail self-call takes the named call"
      (is (= '(if c 0 (inc (self_ t n)))
             (rw (list 'if 'c 0 (list 'inc (list dsym 'A 't 'n))) dsym 'self_ 1 3))))
    (testing "arity-mismatched self-call fails the rewrite"
      (is (nil? (rw (list dsym 'A 't) dsym 'self_ 1 3))))))

;; ── store-backed integration (skips without exported equation lemmas) ────────

(deftest compile-recursive-store-def-with-recur
  (if-not (has-decl? "List.lengthTRAux.eq_def")
    (is true "store carries no equation lemmas — skipped")
    (let [entry (sd/compile-store-def! (a/env) "List.lengthTRAux")]
      (is (some? entry) "List.lengthTRAux compiles from its eq_def")
      (is (= 2 (:arity entry)))
      (is (= 1 (:erased entry)))
      (let [f @(resolve (:sym entry))]
        (is (= 3 (f [10 20 30] 0)))
        (testing "tail self-call became recur: depth far beyond the JVM stack"
          (is (= 100000 (f (range 100000) 0))))))))

(deftest compile-wrapper-and-cross-def-chain
  (if-not (has-decl? "List.reverseAux.eq_def")
    (is true "store carries no equation lemmas — skipped")
    (let [entry (sd/compile-store-def! (a/env) "List.reverse")]
      (is (some? entry) "non-recursive wrapper compiles via its value, worker via eq_def")
      (let [f @(resolve (:sym entry))]
        (is (= [3 2 1] (into [] (f [1 2 3]))))
        (is (= 100000 (count (f (range 100000)))))))))

(deftest codegen-fall-through-compiles-plain-store-head
  (if-not (has-decl? "List.lengthTRAux.eq_def")
    (is true "store carries no equation lemmas — skipped")
    (let [term (e/app* (e/const' (name/from-string "List.lengthTRAux") [lvl/zero])
                       (e/const' (name/from-string "Nat") []))
          code (cg/ansatz->clj (a/env) term [])]
      (is (some #(and (symbol? %) (= "ansatz.storedef.runtime" (namespace %)))
                (tree-seq coll? seq code))
          "plain store head lowered to the interned qualified var"))))

(deftest csimp-does-not-hijack-native-lowerings
  ;; List.length has a native `count` builtin; even with List.lengthTR compilable, the
  ;; csimp swap must keep the native lowering.
  (when (has-decl? "List.length")
    (let [csimp-t @#'cg/csimp-target]
      (is (nil? (csimp-t (a/env) "List.length"))))))

;; ── unified emitter: own a/defn (no store equations needed — runs everywhere) ─
;; An accumulator-style defn (self-call args CHANGE) fails the structural IH rewrite and
;; auto-routes to the WF path (GuessLex), so this exercises the wf.clj emitter wiring.

(deftest own-defn-tail-recursion-becomes-recur
  (binding [a/*verbose* false]
    (a/defn ^{:- Nat} sdt-len-acc [^{:- (List Nat)} xs ^{:- Nat} n]
      (match xs (List Nat) Nat
             (nil n)
             (cons [h t] (sdt-len-acc t (Nat.succ n)))))
    (is (= 3 (sdt-len-acc [1 2 3] 0)))
    (testing "tail-recursive accumulator defn runs at depths that overflowed the closure cascade"
      (is (= 100000 (sdt-len-acc (range 100000) 0))))
    (testing "registry entry carries :surface provenance"
      (is (= :surface (:provenance (get @ansatz.surface.ingest/arity-registry "sdt-len-acc")))))
    (testing "curried value-position call style still works"
      (is (= 4 ((sdt-len-acc [1 2 3]) 1))))))

(deftest own-defn-non-tail-still-correct
  (binding [a/*verbose* false]
    (a/defn ^{:- Nat} sdt-len [^{:- (List Nat)} xs]
      (match xs (List Nat) Nat
             (nil Nat.zero)
             (cons [h t] (Nat.succ (sdt-len t)))))
    (is (= 3 (sdt-len [1 2 3])))
    (is (= 5000 (sdt-len (range 5000))) "non-tail recursion stays correct (stack-bound as before)")))

;; ── long literals + promoting arithmetic ─────────────────────────────────────

(deftest nat-literals-emit-longs-and-arithmetic-promotes
  (binding [a/*verbose* false]
    (a/defn ^{:- Nat} sdt-add3 [^{:- Nat} k] (Nat.add k 3))
    (testing "literal-seeded arithmetic stays primitive long"
      (is (instance? Long (sdt-add3 4)))
      (is (= 7 (sdt-add3 4))))
    (a/defn ^{:- Nat} sdt-sq [^{:- Nat} k] (Nat.mul k k))
    (testing "overflow promotes to bigint (unbounded Nat semantics) instead of throwing"
      (let [big (long (Math/pow 2 40))
            r (sdt-sq big)]
        (is (= (*' big big) r))))))

(deftest kill-switch-restores-old-behavior
  (binding [cg/*compile-store-defs* false]
    (when (has-decl? "List.lengthTRAux.eq_def")
      (sd/reset-cache!)
      ;; with the switch off, nothing new lands in the runtime ns via codegen fall-through
      (let [term (e/app* (e/const' (name/from-string "List.eraseIdxTR") [lvl/zero])
                         (e/const' (name/from-string "Nat") []))
            code (cg/ansatz->clj (a/env) term [])]
        (is (not-any? #(and (symbol? %) (= "ansatz.storedef.runtime" (namespace %)))
                      (tree-seq coll? seq code)))))))
