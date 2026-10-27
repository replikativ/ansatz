(ns ansatz.codegen-init-test
  "Runtime/kernel inventory for the bundled Init vocabulary."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [ansatz.core :as a]
            [ansatz.codegen :as cg]
            [ansatz.codegen.storedef :as sd]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as level]
            [ansatz.malli :as am]
            [ansatz.surface.elaborate :as elab]
            [ansatz.tactic.instance :as instance]
            [ansatz.deriving :as deriving])
  (:import [ansatz.kernel TypeChecker]))

(use-fixtures :once (fn [f] (a/load-init! :verify? true) (binding [a/*verbose* false] (f))))

(defn- nat-list [xs]
  (reduce (fn [tail x] (list 'List.cons 'Nat x tail)) '(List.nil Nat) (reverse xs)))

(defn- compare-kernel! [application schema]
  (let [term (if (instance? ansatz.kernel.Expr application)
               application (elab/elaborate (a/env) application))
        tc (TypeChecker. (a/env))
        kernel (#'am/decode-val #(.whnf (.getReducer tc) %) schema term)
        runtime (eval (cg/ansatz->clj (a/env) term []))
        runtime (if (= :sequential (when (vector? schema) (first schema))) (or runtime ()) runtime)
        runtime (if (= :maybe (when (vector? schema) (first schema)))
                  (when runtime (first runtime)) runtime)]
    (is (= kernel runtime) (pr-str application))))

(deftest foldl-runtime-agrees-with-kernel
  (is (= :eq-def (:provenance (sd/compile-store-def! (a/env) "List.foldl")))
      "foldl compiles its exported direct equation body")
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

;; Every bundled runtime API must compile and agree with kernel reduction.
;; Lean 4.33.1 Init/GetElem.lean uses List.get?Internal behind GetElem?.getElem?;
;; the older List.get? spelling is no longer a declaration.
(def ^:private list-api
  '[foldl foldr map filter filterMap flatMap append reverse length get?Internal head? tail
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
   'get?Internal (list 'List.get?Internal xs 1)
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
   'get?Internal [:maybe :int] 'head? [:maybe :int] 'find? [:maybe :int] 'lookup [:maybe :int]
   'any :boolean 'all :boolean 'contains :boolean 'elem :boolean
   'zip [:sequential [:tuple :int :int]]})

(deftest bundled-init-runtime-inventory
  (doseq [f list-api]
    (let [cname (str "List." f)]
      (testing cname
        (is (some? (env/lookup (a/env) (name/from-string cname)))
            (str cname " must be present in bundled Init"))
        (doseq [xs [[] [5] [1 2 3] [0 10] [2 2]]]
          (compare-kernel! (get (list-probes (nat-list xs)) f)
                           (get result-schemas f [:sequential :int]))))))
  (doseq [[application schema]
          [['(Nat.add 3 4) :int] ['(Nat.sub 3 4) :int] ['(Nat.mul 3 4) :int]
           ['(Nat.div 7 2) :int] ['(Nat.mod 7 2) :int] ['(Nat.pow 2 3) :int]
           ['(Nat.beq 2 3) :boolean] ['(Nat.ble 2 3) :boolean]
           ['(Bool.and true false) :boolean] ['(Bool.or false true) :boolean]
           ['(Bool.not false) :boolean]
           ['(Option.getD (Option.some Nat 3) 9) :int]
           ['(Option.getD (Option.none Nat) 9) :int]
           ['(List.lookup 1 (List.nil (Prod Nat Nat))) [:maybe :int]]
           ['(List.lookup 2 (List.cons (Prod Nat Nat) (Prod.mk Nat Nat 1 7)
                                      (List.nil (Prod Nat Nat)))) [:maybe :int]]
           ['(List.filterMap (fn [x :- Nat]
                              (if (Nat.beq x 2) (Option.some Nat x) (Option.none Nat)))
                            (List.cons Nat 1 (List.cons Nat 2 (List.nil Nat)))) [:sequential :int]]
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

(deftest dependent-let-types-erase-their-applications
  (binding [*ns* (the-ns 'ansatz.codegen-init-test)]
    (eval '(ansatz.core/defn let-ignore-type [t :- Type, n :- Nat] Nat n))
    (let [nat (e/const' (name/from-string "Nat") [])
          type0 (e/sort' (level/from-nat 1))
          type1 (e/sort' (level/from-nat 2))
          call (e/app* (e/const' (name/from-string "let-ignore-type") [])
                       (e/app (e/bvar 0) (e/lit-nat 0)) (e/lit-nat 7))
          value (e/lam "n" nat nat :default)
          bodies [(e/let' "T" type1 type0
                          (e/let' "f" (e/forall' "n" nat (e/bvar 1) :default) value call))
                  (e/let' "T" type1 type0
                          (e/let' "U" type1 (e/bvar 0)
                                  (e/let' "f" (e/forall' "n" nat (e/bvar 1) :default) value
                                          (e/let' "g" (e/forall' "n" nat (e/bvar 2) :default)
                                                  (e/bvar 0) call))))]]
      (doseq [[i body] (map-indexed vector bodies)]
        (let [ci (env/mk-def (name/from-string (str "dependentLetType" i)) [] nat body)
              checked (env/check-constant (a/env) ci)
              tc (TypeChecker. checked)]
          (is (.isDefEq tc body (e/lit-nat 7)))
          (is (= 7 (eval (cg/ansatz->clj checked body [])))))))))

(deftest compiled-list-search-retains-its-equality-instance
  (let [nat (e/const' (name/from-string "Nat") [])
        never-equal (e/app* (e/const' (name/from-string "BEq.mk") [level/zero]) nat
                            (e/lam "x" nat
                                   (e/lam "y" nat (e/const' (name/from-string "Bool.false") []) :default)
                                   :default))
        application (elab/elaborate (a/env) '(List.contains (List.cons Nat 2 (List.nil Nat)) 2))
        [head args] (e/get-app-fn-args application)
        application (apply e/app* head (assoc (vec args) 1 never-equal))]
    ;; The ordinary Nat instance returns true on [2]; this instance returns false.
    (compare-kernel! application :boolean)))

(deftest native-natural-decisions-agree-with-kernel
  (doseq [native '[Nat.decEq Nat.decLe Nat.decLt]
          [x y] [[2 2] [2 3] [3 2]]
          application [(list native x y) (list 'let ['f native] (list 'f x y))]]
    (let [decision (elab/elaborate (a/env) application)
          tc (TypeChecker. (a/env))
          decision-type (.whnf (.getReducer tc) (.inferType tc decision))
          proposition (first (second (e/get-app-fn-args decision-type)))
          term (e/app* (e/const' (name/from-string "Decidable.decide") []) proposition decision)]
      (compare-kernel! term :boolean))))

(deftest partially-applied-constructors-agree-with-kernel
  (let [constructor (e/const' (name/from-string "Prod.mk") [level/zero level/zero])
        nat (e/const' (name/from-string "Nat") [])
        partial (e/app* constructor nat nat)
        type (.inferType (TypeChecker. (a/env)) partial)
        term (e/app (e/lam "f" type (e/app* (e/bvar 0) (e/lit-nat 2) (e/lit-nat 7)) :default)
                    partial)]
    (compare-kernel! term [:tuple :int :int]))
  (compare-kernel! '(List.zip (List.cons Nat 1 (List.cons Nat 2 (List.nil Nat)))
                              (List.cons Nat 7 (List.nil Nat))) [:sequential [:tuple :int :int]])
  (let [constructor (e/const' (name/from-string "Prod.mk") [level/zero level/zero])
        nat (e/const' (name/from-string "Nat") [])
        type (.inferType (TypeChecker. (a/env)) constructor)
        term (e/app (e/lam "f" type (e/app* (e/bvar 0) nat nat (e/lit-nat 2) (e/lit-nat 7)) :default)
                    constructor)]
    (compare-kernel! term [:tuple :int :int])))
(deftest computational-equality-uses-operand-dictionary
  (binding [*ns* (the-ns 'ansatz.codegen-init-test)]
    (eval '(ansatz.core/defn bool-equality [b :- Bool] Bool
             ((fn [x :- Bool] (= x true)) b)))
    (eval '(ansatz.core/defn nat-equality [x :- Nat, y :- Nat] Bool (= x y)))
    (eval '(ansatz.core/defn int-equality [x :- Int, y :- Int] Bool (= x y)))
    (eval '(ansatz.core/inductive EqualityColor [] (red) (blue) :deriving [DecidableEq]))
    (eval '(ansatz.core/defn color-equality [x :- EqualityColor, y :- EqualityColor] Bool (= x y)))
    (eval '(ansatz.core/structure EqualityToken []))
    (swap! a/ansatz-env deriving/derive-decidable-eq! "EqualityToken" [["mk" []]])
    (eval '(ansatz.core/defn token-equality [x :- EqualityToken, y :- EqualityToken] Bool (= x y)))
    (doseq [[application expected]
            [['(bool-equality true) true] ['(bool-equality false) false]
             ['(nat-equality 3 3) true] ['(nat-equality 3 4) false]
             ['(int-equality (Int.negSucc 2) (Int.negSucc 2)) true]
             ['(int-equality (Int.negSucc 2) (Int.ofNat 3)) false]
             ['(color-equality (EqualityColor.red) (EqualityColor.red)) true]
             ['(color-equality (EqualityColor.red) (EqualityColor.blue)) false]
             ['(token-equality (EqualityToken.mk) (EqualityToken.mk)) true]]]
      (compare-kernel! application :boolean)
      (is (= expected (eval (cg/ansatz->clj (a/env) (elab/elaborate (a/env) application) [])))))))

(deftest computational-equality-requires-registered-instance
  (let [saved (a/env)
        inst-name (name/from-string "instDecidableEqBool")
        ci (env/lookup saved inst-name)
        alias (name/from-string "booleanDecisionDictionary")
        custom (env/check-constant saved
                 (env/mk-def alias [] (.type ci) (e/const' inst-name [])))
        unregistered (env/with-extension custom :instances {})]
    (try
      (reset! a/ansatz-env unregistered)
      (is (thrown? clojure.lang.ExceptionInfo
                   (elab/elaborate (a/env) '(fn [b :- Bool] (= b true)))))
      (swap! a/ansatz-env instance/add-instance alias)
      (is (re-find #"booleanDecisionDictionary"
                   (e/->string (elab/elaborate (a/env) '(fn [b :- Bool] (= b true))))))
      (finally (reset! a/ansatz-env saved)))))

(deftest string-equality-uses-registered-dictionary
  (binding [*ns* (the-ns 'ansatz.codegen-init-test)]
    (eval '(ansatz.core/defn string-equality [x :- String, y :- String] Bool (= x y)))
    (doseq [[x y expected] [["hello" "hello" true] ["hello" "world" false]
                            ["é" "é" true] ["" "a" false]]]
      (let [application (list 'string-equality x y)]
        (compare-kernel! application :boolean)
        (is (= expected (eval (cg/ansatz->clj (a/env) (elab/elaborate (a/env) application) []))))))))

(deftest parameterized-equality-elaborates-at-full-carrier
  (doseq [[rhs expected] [[true true] [false false]]]
    (let [application (list '(fn [x :- (List Bool), y :- (List Bool)] (= x y))
                            '(List.cons Bool true (List.nil Bool))
                            (list 'List.cons 'Bool rhs '(List.nil Bool)))
          term (elab/elaborate-check (a/env) application (e/const' (name/from-string "Bool") []))
          tc (TypeChecker. (a/env))]
      (is (= expected (#'am/decode-val #(.whnf (.getReducer tc) %) :boolean term)))
      (is (= expected (eval (cg/ansatz->clj (a/env) term [])))))))
