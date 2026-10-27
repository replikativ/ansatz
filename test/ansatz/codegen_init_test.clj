(ns ansatz.codegen-init-test
  "Runtime/kernel inventory for the bundled Init vocabulary."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [ansatz.core :as a]
            [ansatz.codegen :as cg]
            [ansatz.codegen.storedef :as sd]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.malli :as am]
            [ansatz.surface.elaborate :as elab])
  (:import [ansatz.kernel TypeChecker]))

(use-fixtures :once (fn [f] (a/load-init!) (binding [a/*verbose* false] (f))))

(defn- nat-list [xs]
  (reduce (fn [tail x] (list 'List.cons 'Nat x tail)) '(List.nil Nat) (reverse xs)))

(defn- compare-kernel! [application schema]
  (let [term (elab/elaborate (a/env) application)
        tc (TypeChecker. (a/env))
        kernel (#'am/decode-val #(.whnf (.getReducer tc) %) schema term)
        runtime (eval (cg/ansatz->clj (a/env) term []))
        runtime (if (= :sequential (when (vector? schema) (first schema))) (or runtime ()) runtime)
        runtime (if (= :maybe (when (vector? schema) (first schema)))
                  (when runtime (first runtime)) runtime)]
    (is (= kernel runtime) (pr-str application))))

(deftest foldl-runtime-agrees-with-kernel
  (binding [*ns* (the-ns 'ansatz.codegen-init-test)]
    (eval '(ansatz.core/defn foldl-runtime-probe [xs :- (List Nat)] Nat
             (List.foldl (fn [n :- Nat, x :- Nat] (+ n x)) 0 xs)))
    (eval '(ansatz.core/theorem foldl-runtime-kernel []
             (= (foldl-runtime-probe (List.cons Nat 1 (List.cons Nat 2 (List.nil Nat)))) 3)
             (rfl)))
    (doseq [xs [[] [1] [1 2] [2 0 5 3]]]
      (compare-kernel! (list 'foldl-runtime-probe (nat-list xs)) :int))
    (is (= 100000 ((ns-resolve *ns* 'foldl-runtime-probe) (repeat 100000 1))))
    ;; Order-sensitive step, nonzero seed, and both partial application positions.
    (doseq [xs [[] [1 2 3]]]
      (let [step '(fn [n :- Nat, x :- Nat] (+ (* n 10) x))]
        (compare-kernel! (list 'List.foldl step 7 (nat-list xs)) :int)
        (compare-kernel! (list 'let ['g (list 'List.foldl step 7)] (list 'g (nat-list xs))) :int)
        (compare-kernel! (list 'let ['g (list 'List.foldl step)] (list 'g 7 (nat-list xs))) :int)))))

(deftest compiled-globals-resolve-in-another-namespace
  (let [a-ns (or (find-ns 'ansatz.runtime-origin) (create-ns 'ansatz.runtime-origin))
        b-ns (or (find-ns 'ansatz.runtime-caller) (create-ns 'ansatz.runtime-caller))]
    (doseq [n [a-ns b-ns]]
      (binding [*ns* n] (clojure.core/refer 'clojure.core)))
    (binding [*ns* a-ns]
      (eval '(ansatz.core/defn origin-inc [n :- Nat] Nat (+ n 1)))
      (eval '(ansatz.core/defn origin-seed [] Nat 9)))
    (binding [*ns* b-ns]
      (is (nil? (ns-resolve b-ns 'origin-inc)))
      (eval '(ansatz.core/defn caller-inc [n :- Nat] Nat (origin-inc n)))
      (eval '(ansatz.core/defn caller-value [n :- Nat] Nat
               (let [f origin-inc] (f (+ n origin-seed)))))
      (is (= 5 ((ns-resolve b-ns 'caller-inc) 4)))
      (is (= 14 ((ns-resolve b-ns 'caller-value) 4))))))

;; Each available declaration is compiled on small closed inputs, and either
;; agrees with kernel WHNF or reports a named compiler limitation. Missing APIs
;; are explicit inventory entries, since the bundled medium tier is not full Init.
(def ^:private list-api
  '[foldl foldr map filter filterMap flatMap append reverse length get? head? tail
    zip zipWith take drop any all find? contains elem replicate range sum lookup])

(defn- list-probes [xs]
  {'foldl (list 'List.foldl '(fn [n :- Nat, x :- Nat] (+ n x)) 0 xs)
   'foldr (list 'List.foldr '(fn [x :- Nat, n :- Nat] (+ x n)) 0 xs)
   'map (list 'List.map '(fn [x :- Nat] (+ x 1)) xs)
   'filter (list 'List.filter '(fn [x :- Nat] (Nat.ble 2 x)) xs)
   'filterMap (list 'List.filterMap '(fn [x :- Nat] (Option.some Nat x)) xs)
   'flatMap (list 'List.flatMap '(fn [x :- Nat] (List.cons Nat x (List.nil Nat))) xs)
   'append (list 'List.append xs xs)
   'reverse (list 'List.reverse xs)
   'length (list 'List.length xs)
   'get? (list 'List.get? xs 1)
   'head? (list 'List.head? xs)
   'tail (list 'List.tail xs)
   'zip (list 'List.zip xs xs)
   'zipWith (list 'List.zipWith '(fn [x :- Nat, y :- Nat] (+ x y)) xs xs)
   'take (list 'List.take 2 xs)
   'drop (list 'List.drop 2 xs)
   'any (list 'List.any xs '(fn [x :- Nat] (Nat.beq x 2)))
   'all (list 'List.all xs '(fn [x :- Nat] (Nat.ble x 9)))
   'find? (list 'List.find? '(fn [x :- Nat] (Nat.beq x 2)) xs)
   'contains (list 'List.contains xs 2)
   'elem (list 'List.elem 2 xs)
   'replicate '(List.replicate 3 2)
   'range '(List.range 3)
   'sum (list 'List.sum xs)
   'lookup '(List.lookup 1 (List.cons (Prod Nat Nat) (Prod.mk Nat Nat 1 7) (List.nil (Prod Nat Nat))))})

(def ^:private result-schemas
  {'foldl :int 'foldr :int 'length :int 'sum :int
   'get? [:maybe :int] 'head? [:maybe :int] 'find? [:maybe :int] 'lookup [:maybe :int]
   'any :boolean 'all :boolean 'contains :boolean 'elem :boolean
   'zip [:sequential [:tuple :int :int]]})

(deftest bundled-init-runtime-inventory
  (doseq [f list-api]
    (let [cname (str "List." f)]
      (testing cname
        (if-not (env/lookup (a/env) (name/from-string cname))
          (println "Init runtime unavailable:" cname "— declaration absent from bundled Init")
          (doseq [xs [[] [1 2 3]]]
            (try
              (compare-kernel! (get (list-probes (nat-list xs)) f)
                               (get result-schemas f [:sequential :int]))
              (catch clojure.lang.ExceptionInfo ex
                (if (= :codegen-error (:kind (ex-data ex)))
                  (do (is (not (#{'foldl 'length 'zipWith} f))
                          (str cname " must remain executable: " (ex-message ex)))
                      (is (string? (:declaration (ex-data ex))))
                      (is (seq (:reason (ex-data ex))))
                      (println "Init runtime unavailable:" cname "—" (ex-message ex)))
                  (throw ex)))))))))
  (doseq [[application schema]
          [['(Nat.add 3 4) :int] ['(Nat.sub 3 4) :int] ['(Nat.mul 3 4) :int]
           ['(Nat.div 7 2) :int] ['(Nat.mod 7 2) :int] ['(Nat.pow 2 3) :int]
           ['(Nat.beq 2 3) :boolean] ['(Nat.ble 2 3) :boolean]
           ['(Bool.and true false) :boolean] ['(Bool.or false true) :boolean]
           ['(Bool.not false) :boolean]
           ['(Option.getD (Option.some Nat 3) 9) :int]
           ['(Option.getD (Option.none Nat) 9) :int]
           ['(Prod.fst (Prod.mk Nat Nat 2 3)) :int]
           ['(Prod.snd (Prod.mk Nat Nat 2 3)) :int]]]
    (compare-kernel! application schema)))

(deftest type-and-proposition-values-erase-before-lowering
  (binding [*ns* (the-ns 'ansatz.codegen-init-test)]
    (eval '(ansatz.core/defn prop-runtime-probe [p :- Prop] Prop (And p p)))
    (eval '(ansatz.core/theorem prop-probe-kernel [p :- Prop]
             (= (prop-runtime-probe p) (And p p)) (rfl)))
    (eval '(ansatz.core/theorem prop-probe-hypothesis
             [p :- Prop, h :- (prop-runtime-probe p)] p
             (exact (And.left h))))
    (eval '(ansatz.core/defn ignore-proposition [p :- Prop, n :- Nat] Nat (+ n 1)))
    (eval '(ansatz.core/defn pass-proposition [n :- Nat] Nat
             (ignore-proposition (prop-runtime-probe True) n)))
    (eval '(ansatz.core/defn runtime-type [] Type Nat))
    (eval '(ansatz.core/defn ignore-type [t :- Type, n :- Nat] Nat (+ n 2)))
    (eval '(ansatz.core/defn pass-type [n :- Nat] Nat (ignore-type runtime-type n)))
    (eval '(ansatz.core/defn ignore-proof [p :- Prop, h :- p, n :- Nat] Nat n))
    (eval '(ansatz.core/defn pass-proof [n :- Nat] Nat (ignore-proof True True.intro n)))
    (eval '(ansatz.core/defn ignore-predicate [p :- (=> Nat Prop), n :- Nat] Nat (+ n 3)))
    (eval '(ansatz.core/defn pass-predicate [n :- Nat] Nat
             (let [p (fn [x :- Nat] (Eq Nat x x))] (ignore-predicate p n))))
    (is (nil? ((ns-resolve *ns* 'prop-runtime-probe) nil)))
    (is (nil? (var-get (ns-resolve *ns* 'runtime-type))))
    (doseq [form '[Nat (And True True) True.intro (fn [x :- Nat] (Eq Nat x x))]]
      (is (nil? (cg/ansatz->clj (a/env) (elab/elaborate (a/env) form) []))
          (pr-str form)))
    (doseq [n [0 3 12]]
      (compare-kernel! (list 'pass-proposition n) :int)
      (compare-kernel! (list 'pass-type n) :int)
      (compare-kernel! (list 'pass-proof n) :int)
      (compare-kernel! (list 'pass-predicate n) :int))))
