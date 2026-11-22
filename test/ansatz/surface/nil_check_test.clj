(ns ansatz.surface.nil-check-test
  "Clojure nil checks in an a/defn body are accepted where they mean the same as a Lean construct
   and refused elsewhere (doc/clojure-contract.md, Nil checks). Ansatz does not model Clojure's
   truthiness: `if-some` is `Option.elim`, `if-let` only where an Option's values never run as nil
   or false, `some?`/`nil?` are `Option.isSome`/`isNone`, `(seq xs)` is a test only.

   Each accepted form is checked three ways: the kernel term's shape, the kernel's own reduction
   against the compiled function, and the compiled function against clojure.core on generated
   inputs (ansatz.clj-check, nil included)."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [ansatz.core :as a]
            [ansatz.fixtures :as fixtures]
            [ansatz.clj-check :as cc]
            [ansatz.codegen :as cg]
            [ansatz.codegen.lean-runtime :as rt]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.surface.data :as data]
            [ansatz.surface.elaborate :as elab]
            [ansatz.surface.ingest :as ingest])
  (:import [ansatz.kernel TypeChecker]))

(def ^:private this-ns 'ansatz.surface.nil-check-test)

(defn- define! [form]
  (binding [*ns* (the-ns this-ns) a/*verbose* false]
    (eval form)))

(def ^:private accepted
  '[(ansatz.core/defn ^Nat nc-if-some [^{:- (Option Nat)} o] (if-some [x o] (+ x 1) 0))
    (ansatz.core/defn ^Nat nc-if-some-bool [^{:- (Option Bool)} o] (if-some [x o] (if x 1 2) 3))
    (ansatz.core/defn ^{:- (List Nat)} nc-if-some-list [^{:- (Option (List Nat))} o] (if-some [ys o] ys [7]))
    (ansatz.core/defn ^{:- (List Nat)} nc-when-some [^{:- (Option Nat)} o] (when-some [x o] [x x]))
    (ansatz.core/defn ^Nat nc-if-let [^{:- (Option Nat)} o] (if-let [x o] (* x 2) 7))
    (ansatz.core/defn ^Int nc-if-let-int [^{:- (Option Int)} o] (if-let [x o] (- x) 7))
    (ansatz.core/defn ^{:- (List Nat)} nc-when-let [^{:- (Option Nat)} o] (when-let [x o] [x]))
    (ansatz.core/defn ^Nat nc-if-let-bool [^Bool p] (if-let [x p] (if x 1 3) 2))
    (ansatz.core/defn ^Bool nc-some [^{:- (Option Nat)} o] (some? o))
    (ansatz.core/defn ^Bool nc-nil [^{:- (Option Nat)} o] (nil? o))
    (ansatz.core/defn ^Bool nc-empty [^{:- (List Nat)} xs] (empty? xs))
    (ansatz.core/defn ^Nat nc-seq [^{:- (List Nat)} xs] (if (seq xs) 1 0))
    (ansatz.core/defn ^Nat nc-seq-cond [^{:- (List Nat)} xs ^Bool p] (cond (and p (seq xs)) 1 (seq xs) 2 :else 3))
    (ansatz.core/defn ^Bool nc-not-seq [^{:- (List Nat)} xs] (not (seq xs)))
    (ansatz.core/defn ^Nat nc-or [^{:- (Option Nat)} o] (or o 0))
    (ansatz.core/defn ^Nat nc-or-nary [^{:- (Option Nat)} o ^{:- (Option Nat)} q] (or o q 5))
    (ansatz.core/defn ^Bool nc-not [^Bool p] (not p))
    ;; the narrowed binder in a recursive definition (guarded Nat recursion, then structural)
    (ansatz.core/defn ^Nat nc-rec [^Nat n ^{:- (Option Nat)} o]
      (if (<= n 0) 0 (if-some [x o] (+ x (nc-rec (- n 1) o)) (nc-rec (- n 1) o))))
    (ansatz.core/defn ^Nat nc-rec-wf [^Nat n ^{:- (Option Nat)} o]
      :termination-by n
      (if (<= n 0) 0 (if-let [x o] (+ x (nc-rec-wf (- n 1) o)) 1)))
    (ansatz.core/defn ^Nat nc-struct [^{:- (List (Option Nat))} xs]
      (match-as xs (List (Option Nat)) Nat (nil 0) (cons [h t] (if-some [x h] (+ x (nc-struct t)) (nc-struct t)))))
    (ansatz.core/defn ^Nat nc-or-rec [^{:- (List (Option Nat))} xs]
      (match-as xs (List (Option Nat)) Nat (nil 0) (cons [h t] (+ (or h 10) (nc-or-rec t)))))
    ;; a match on the narrowed binder, and if-some nested in a match alternative
    (ansatz.core/defn ^Nat nc-match-x [^{:- (Option (List Nat))} o]
      (if-some [ys o] (match-as ys (List Nat) Nat (nil 100) (cons [h t] h)) 7))
    (ansatz.core/defn ^Nat nc-nested [^{:- (List (Option Nat))} xs ^{:- (Option Nat)} q]
      (match-as xs (List (Option Nat)) Nat (nil 0)
                (cons [h t] (if-some [x h] (if-some [y q] (+ x y) x) 2))))
    (ansatz.core/defn ^Nat nc-loop [^{:- (Option Nat)} o ^Nat n]
      (loop [i n acc 0] (if (== i 0) acc (recur (dec i) (if-some [x o] (+ acc x) acc)))))])

(defn- init-once [f]
  (binding [a/*verbose* false]
    (a/load-init!)
    (doseq [form accepted] (define! form))
    (f)))

(use-fixtures :once fixtures/isolated-session init-once)

(defn- defined [sym] @(ns-resolve this-ns sym))

(defn- refusal
  "The refusal ex-data of evaluating `form`, or :accepted."
  [form]
  (try (define! form) :accepted
       (catch Throwable t
         (or (some #(let [d (ex-data %)] (when (= :clj/refused (:kind d)) d))
                   (take-while some? (iterate #(.getCause ^Throwable %) t)))
             (throw t)))))

(defn- reason [form] (let [r (refusal form)] (if (map? r) (:reason r) r)))

;; ── kernel term shape ──────────────────────────────────────────────────────────────────────

(defn- head-name [x]
  (let [[h _] (e/get-app-fn-args x)]
    (when (e/const? h) (name/->string (e/const-name h)))))

(defn- body [kname]
  (loop [v (.value ^ansatz.kernel.ConstantInfo (env/lookup (a/env) (name/from-string (str kname))))]
    (if (e/lam? v) (recur (e/lam-body v)) v)))

(deftest kernel-terms
  (testing "if-some / if-let are Option.elim o else (fun x => then)"
    (doseq [f '[nc-if-some nc-if-some-bool nc-if-some-list nc-when-some nc-if-let nc-when-let nc-match-x]]
      (is (= "Option.elim" (head-name (body f))) (str f)))
    (let [[_ args] (e/get-app-fn-args (body 'nc-if-some))
          then (nth args 4)]
      (is (e/lam? then) "the then branch binds x")
      (is (= "Nat" (head-name (e/lam-type then))) "x has the Option's element type")))
  (testing "if-let on a Bool is Clojure's (let [x p] (if x …))"
    (is (= "Bool.rec" (head-name (e/let-body (body 'nc-if-let-bool))))))
  (testing "predicates"
    (is (= "Option.isSome" (head-name (body 'nc-some))))
    (is (= "Option.isNone" (head-name (body 'nc-nil))))
    (is (= "List.isEmpty" (head-name (body 'nc-empty))))
    (is (= "Bool.not" (head-name (body 'nc-not))))
    (let [[_ args] (e/get-app-fn-args (body 'nc-not-seq))]
      (is (= "Bool.not" (head-name (body 'nc-not-seq))))
      (is (= "Bool.not" (head-name (first args))) "(seq xs) is !xs.isEmpty")))
  (testing "(seq xs) as a test"
    (let [[_ args] (e/get-app-fn-args (body 'nc-seq))]
      (is (= "Bool.rec" (head-name (body 'nc-seq))))
      (is (= "Bool.not" (head-name (last args))))))
  (testing "(or o d) is Option.getD, n-ary folding right"
    (is (= "Option.getD" (head-name (body 'nc-or))))
    (let [[_ args] (e/get-app-fn-args (body 'nc-or-nary))]
      (is (= "Option.getD" (head-name (body 'nc-or-nary))))
      (is (= "Option.getD" (head-name (last args)))))))

;; ── the kernel's reduction against the compiled function ───────────────────────────────────

(defn- kernel->runtime
  "The runtime value of a closed kernel value of descriptor `d`, read off the kernel's reduction."
  [whnf d x]
  (let [x (whnf x)
        [_ as] (e/get-app-fn-args x)
        h (head-name x)]
    (case (first d)
      :nat (long (e/lit-nat-val x))
      :bool (case h "Bool.true" true "Bool.false" false)
      :list (case h
              "List.nil" nil
              "List.cons" (cons (kernel->runtime whnf (second d) (nth as 1))
                                (kernel->runtime whnf d (nth as 2)))))))

(defn- agrees-with-kernel! [application d]
  (let [term (elab/elaborate (a/env) application)
        tc (doto (TypeChecker. (a/env)) (.setFuel 200000000))
        whnf #(.whnf (.getReducer tc) %)
        kernel (kernel->runtime whnf d term)
        runtime (eval (cg/ansatz->clj (a/env) term []))]
    (is (= kernel (if (= :list (first d)) (seq runtime) runtime)) (pr-str application))
    kernel))

(deftest kernel-and-runtime-agree
  (let [some3 '(Option.some Nat 3)
        none '(Option.none Nat)
        xs '(List.cons Nat 4 (List.nil Nat))
        empty '(List.nil Nat)]
    (is (= 4 (agrees-with-kernel! (list 'nc-if-some some3) [:nat])))
    (is (= 0 (agrees-with-kernel! (list 'nc-if-some none) [:nat])))
    (is (= [3 3] (agrees-with-kernel! (list 'nc-when-some some3) [:list [:nat]])))
    (is (nil? (agrees-with-kernel! (list 'nc-when-some none) [:list [:nat]])))
    (is (= 6 (agrees-with-kernel! (list 'nc-if-let some3) [:nat])))
    (is (= 7 (agrees-with-kernel! (list 'nc-if-let none) [:nat])))
    (is (= 2 (agrees-with-kernel! '(nc-if-let-bool Bool.false) [:nat])))
    (is (true? (agrees-with-kernel! (list 'nc-some some3) [:bool])))
    (is (true? (agrees-with-kernel! (list 'nc-nil none) [:bool])))
    (is (true? (agrees-with-kernel! (list 'nc-empty empty) [:bool])))
    (is (= 1 (agrees-with-kernel! (list 'nc-seq xs) [:nat])))
    (is (true? (agrees-with-kernel! (list 'nc-not-seq empty) [:bool])))
    (is (= 3 (agrees-with-kernel! (list 'nc-or some3) [:nat])))
    (is (= 0 (agrees-with-kernel! (list 'nc-or none) [:nat])))
    (is (= 5 (agrees-with-kernel! (list 'nc-or-nary none none) [:nat])))
    (is (= 6 (agrees-with-kernel! (list 'nc-rec 2 some3) [:nat])))
    (is (= 4 (agrees-with-kernel! (list 'nc-match-x (list 'Option.some '(List Nat) xs)) [:nat])))))

;; ── the compiled function against clojure.core ─────────────────────────────────────────────

(deftest compiled-functions-agree-with-clojure
  (doseq [f '[nc-if-some nc-if-some-bool nc-if-some-list nc-when-some nc-if-let nc-if-let-int
              nc-when-let nc-if-let-bool nc-some nc-nil nc-empty nc-seq nc-seq-cond nc-not-seq
              nc-or nc-or-nary nc-not nc-rec nc-rec-wf nc-loop]]
    (let [r (cc/check-clojure! (ns-resolve this-ns f))]
      (is (= :agree (:status r)) (str f " " (pr-str r)))
      (is (pos? (:agree r 0)) (str f " ran")))))

(deftest nil-and-values-cross-unchanged
  (testing "an Option argument is nil or the value, as Clojure passes it"
    (is (= [0 1 6] (mapv (defined 'nc-if-some) [nil 0 5])))
    (is (= [3 2 1] (mapv (defined 'nc-if-some-bool) [nil false true])))
    (is (= [[7] [] [1]] (mapv #(vec ((defined 'nc-if-some-list) %)) [nil [] [1]]))
        "some [] is not none: if-some tests for nil only"))
  (testing "some of a value that runs as nil is boxed, and if-some takes the then branch"
    (is (nil? (seq ((defined 'nc-if-some-list) (rt/some-of nil)))) "some [] binds ys to the empty list")
    (is (= [7] (vec ((defined 'nc-if-some-list) nil)))))
  (testing "recursion through the narrowed binder"
    (is (= [0 6 0] [((defined 'nc-rec) 0 3) ((defined 'nc-rec) 2 3) ((defined 'nc-rec) 2 nil)]))
    (is (= [0 6 1] [((defined 'nc-rec-wf) 0 3) ((defined 'nc-rec-wf) 2 3) ((defined 'nc-rec-wf) 2 nil)]))
    (is (= 3 ((defined 'nc-struct) [1 nil 2])))
    (is (= 13 ((defined 'nc-or-rec) [1 nil 2])))
    (is (= [6 0] [((defined 'nc-loop) 2 3) ((defined 'nc-loop) nil 3)])))
  (testing "a match on the narrowed binder, if-some nested in a match"
    (is (= [7 100 5] (mapv (defined 'nc-match-x) [nil [] [5 6]])))
    (is (= [0 2 9 4] [((defined 'nc-nested) [] 1) ((defined 'nc-nested) [nil] 1)
                      ((defined 'nc-nested) [4] 5) ((defined 'nc-nested) [4] nil)]))))

;; ── refusals ───────────────────────────────────────────────────────────────────────────────

(deftest if-let-where-truthiness-differs
  (doseq [t '[Bool (Option Nat) (List Nat) Unit]]
    (is (= :truthiness-differs
           (reason (list 'ansatz.core/defn (with-meta 'nc-r-if-let {:- 'Nat})
                         [(with-meta 'o {:- (list 'Option t)})] '(if-let [x o] 1 2))))
        (pr-str t)))
  (is (= :truthiness-differs
         (reason '(ansatz.core/defn ^Nat nc-r-when-let [^{:- (Option Bool)} o] (when-let [x o] 1)))))
  (testing "a type variable may run as nil"
    (is (= :truthiness-differs
           (reason '(ansatz.core/defn ^Nat nc-r-poly [^{:- Type} α ^{:- (Option α)} o] (if-let [x o] 1 2))))))
  (testing "a structure whose one relevant field is an Option runs as that Option"
    (is (= :truthiness-differs
           (reason '(ansatz.core/defn ^Nat nc-r-sub [^{:- (Option (Subtype (lam [y (Option Nat)] (Eq (Option Nat) y y))))} o]
                      (if-let [x o] 1 2)))))
    (testing "a registered structure runs as a record, which is never nil, whatever its fields"
      (define! '(ansatz.core/structure NcOptBox [] (v (Option Nat))))
      (define! '(ansatz.core/defn ^Nat nc-opt-box [^{:- (Option NcOptBox)} o] (if-let [b o] 1 2)))
      (let [box @(ns-resolve this-ns '->NcOptBox)]
        (is (= [2 1 1] (mapv (defined 'nc-opt-box) [nil (box nil) (box 3)])))
        (is (= [2 1 1] (mapv #(if-let [b %] 1 2) [nil (box nil) (box 3)])) "as in Clojure"))))
  (testing "(or o d) where the Option's values can be false"
    (is (= :truthiness-differs
           (reason '(ansatz.core/defn ^Bool nc-r-or [^{:- (Option Bool)} o] (or o true)))))
    (is (= :non-bool-test
           (reason '(ansatz.core/defn ^{:- (Option Nat)} nc-r-or2 [^{:- (Option Nat)} o ^{:- (Option Nat)} q] (or o q))))
        "or over two Options (Option.or) is not in the core surface")))

(deftest not-optional
  (is (= :not-optional (reason '(ansatz.core/defn ^Nat nc-r-1 [^Nat a] (if-some [x a] x 0)))))
  (is (= :not-optional (reason '(ansatz.core/defn ^Nat nc-r-2 [^Nat a] (if-let [x a] x 0)))))
  (is (= :not-optional (reason '(ansatz.core/defn ^Bool nc-r-3 [^Nat a] (some? a)))))
  (is (= :not-optional (reason '(ansatz.core/defn ^Bool nc-r-4 [^{:- (List Nat)} xs] (nil? xs)))))
  (is (re-find #"empty\?" (:hint (refusal '(ansatz.core/defn ^Bool nc-r-5 [^{:- (List Nat)} xs] (nil? xs)))))))

(deftest nil-branches-follow-the-nil-at-type-rule
  (is (= :nil-at-type (reason '(ansatz.core/defn ^Nat nc-r-6 [^{:- (Option Nat)} o] (when-some [x o] x)))))
  (is (= :nil-at-type (reason '(ansatz.core/defn ^Nat nc-r-7 [^{:- (Option Nat)} o] (if-some [x o] x)))))
  (is (= :multi-form-body (reason '(ansatz.core/defn ^{:- (List Nat)} nc-r-8 [^{:- (Option Nat)} o]
                                     (when-some [x o] [x] [x x]))))))

(deftest seq-is-a-test-only
  (is (= :seq-value (reason '(ansatz.core/defn ^{:- (List Nat)} nc-r-9 [^{:- (List Nat)} xs] (seq xs)))))
  (is (= :seq-value (reason '(ansatz.core/defn ^Bool nc-r-10 [^Bool p ^{:- (List Nat)} xs] (and p (seq xs)))))
      "the and's value would be the seq")
  (is (= :seq-value (reason '(ansatz.core/defn ^Bool nc-r-11 [^Bool p ^{:- (List Nat)} xs] (or (seq xs) p)))))
  (is (= :not-a-list (reason '(ansatz.core/defn ^Bool nc-r-12 [^String s] (empty? s)))))
  (is (= :not-a-list (reason '(ansatz.core/defn ^Nat nc-r-13 [^{:- (Option Nat)} o] (if (seq o) 1 0))))))

(deftest non-bool-tests-name-the-explicit-form
  (let [hint (fn [form] (let [r (refusal form)] (is (= :non-bool-test (:reason r)) (pr-str form)) (:hint r)))]
    (is (re-find #"some\?.*if-some" (hint '(ansatz.core/defn ^Nat nc-h-1 [^{:- (Option Nat)} o] (if o 1 2)))))
    (is (re-find #"seq.*empty\?" (hint '(ansatz.core/defn ^Nat nc-h-2 [^{:- (List Nat)} xs] (if xs 1 2)))))
    (is (re-find #"compare" (hint '(ansatz.core/defn ^Nat nc-h-3 [^Nat n] (if n 1 2)))))
    (is (re-find #"compare" (hint '(ansatz.core/defn ^Bool nc-h-4 [^Int n] (not n)))))))

(deftest outside-a-clojure-body
  (testing "^:lean keeps the macroexpansion (no Option.elim, no Option.isNone)"
    (is (not= :accepted
              (try (define! '(ansatz.core/defn ^{:- Nat :lean true} nc-lean [^{:- (Option Nat)} o]
                               (if-some [x o] x 0)))
                   :accepted
                   (catch Throwable _ :failed))))))

(deftest value-predicates-fall-back-to-option
  (testing "with the EDN Value surface installed, some?/nil? on an Option still mean isSome/isNone"
    (let [regs [ingest/term-elaborator-registry ingest/elaborator-registry
                ingest/keyword-access-registry ingest/comparison-registry]
          saved (mapv deref regs)]
      (try
        (data/install-surface!)
        (define! '(ansatz.core/defn ^Bool nc-vsome [^{:- (Option Nat)} o] (some? o)))
        (define! '(ansatz.core/defn ^Bool nc-vnil [^{:- (Option Nat)} o] (nil? o)))
        (is (= "Option.isSome" (head-name (body 'nc-vsome))))
        (is (= [false true] (mapv (defined 'nc-vsome) [nil 0])))
        (is (= [true false] (mapv (defined 'nc-vnil) [nil 0])))
        (is (= :not-optional (reason '(ansatz.core/defn ^Bool nc-vnat [^Nat a] (some? a)))))
        (finally (doseq [[r v] (map vector regs saved)] (reset! r v)))))))
