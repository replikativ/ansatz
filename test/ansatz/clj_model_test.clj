(ns ansatz.clj-model-test
  "PR G1: the kernel model of plain Clojure (ansatz.clj-model), its translator, the boundary
   codecs and `a/foreign ^:model` — a foreign function becomes a definition from its source."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [ansatz.core :as a]
            [ansatz.fixtures :as fixtures]
            [ansatz.clj-check :as cc]
            [ansatz.clj-model :as m]
            [ansatz.clj-model.translate :as tr]
            [ansatz.clj-model.boundary :as b]
            [ansatz.codegen :as cg]
            [ansatz.surface.data :as data]
            [ansatz.surface.ingest :as ingest]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]))

(defn- define-models!
  "The modelled functions the tests use, defined once Init and the codecs are in place. The
   identities (one per boundary type) check that the kernel's dec_R, by evaluation, and the
   runtime, the compiled dec_R on the result, agree."
  []
  (a/foreign ^:model clamp [x :- Int, lo :- Int, hi :- Int] Int
             (fn [x lo hi] (cond (< x lo) lo (> x hi) hi :else x)))
  (a/foreign ^:model add-total [m :- Value] Value
             (fn [m] (assoc m :total (+ (:a m) (:b m)))))
  (a/foreign ^:model id-nat [x :- Int] Nat (fn [x] x))
  (a/foreign ^:model id-int [x :- Int] Int (fn [x] x))
  (a/foreign ^:model id-bool [x :- Bool] Bool (fn [x] x))
  (a/foreign ^:model id-str [x :- String] String (fn [x] x))
  (a/foreign ^:model id-val [x :- Value] Value (fn [x] x))
  (a/foreign ^:model not-a-string [x :- Int] String (fn [x] (if (pos? x) "pos" x)))
  (a/foreign ^:model succ-int [x :- Int] Int (fn [x] (+ x 1)))
  (a/defn use-succ [x :- Int] Int (succ-int x))
  (a/defn use-succ-map [xs :- (List Int)] (List Int) (List.map succ-int xs)))

(defn- setup [f]
  (binding [a/*verbose* false]
    (a/load-init!)
    (data/install-value-type!)
    (b/install-codecs!)
    (define-models!)
    (f)))

(use-fixtures :once fixtures/isolated-session setup)

(defn- run-op [k & xs]
  (if-let [{v :some} (m/opt-value (apply (m/model-fn k) (map m/edn->cljv xs)))]
    (m/cljv->edn v)
    :none))

(defn- const [s] (e/const' (name/from-string s) []))

(defn- proves? [prop tactics]
  (try (binding [a/*verbose* false]
         (a/prove-theorem (gensym "clj-model-fact") '[] prop tactics))
       true
       (catch Throwable _ false)))

;; ── The model ───────────────────────────────────────────────────────────────────────────

(deftest constructors-are-fixed
  (is (= 15 (count m/ctors)))
  (is (= '[vnil vbool vlong vdouble vchar vstr vkw vsym vcons ventry vlist vlseq vvec vmap vset]
         (mapv first m/ctors))
      "append-only: the runtime representation and every exhaustive match depend on this order")
  (is (= 15 (alength (.ctors ^ansatz.kernel.ConstantInfo (env/lookup (a/env) (name/from-string "CljM.V")))))))

(deftest ops-at-runtime
  (doseq [[k args expected]
          [["CljM.add" [1 2] 3] ["CljM.add" [Long/MAX_VALUE 1] :none] ["CljM.add" [9223372036854775808N 1] 9223372036854775809N]
           ["CljM.sub" [-1 Long/MIN_VALUE] :none] ["CljM.sub" [5 3] 2] ["CljM.mul" [3 4] 12]
           ["CljM.neg" [Long/MIN_VALUE] :none] ["CljM.inc" [1.5] 2.5] ["CljM.num" [nil] nil] ["CljM.num" ["a"] :none]
           ["CljM.lt" [1 2] true] ["CljM.lt" [1 2.0] :none] ["CljM.ge" [2 2] true] ["CljM.zeroQ" [-0.0] true]
           ["CljM.eq" [[1 2] '(1 2)] true] ["CljM.eq" [{:a 1 :b [1]} {:b '(1) :a 1}] true] ["CljM.eq" [1 1.0] false]
           ["CljM.eq" [Double/NaN Double/NaN] :none] ["CljM.eq" [nil ()] false] ["CljM.eq" [#{1 2} #{2 1}] true]
           ["CljM.get" [{:a 1} :a] 1] ["CljM.get3" [{:a nil} :a 5] nil] ["CljM.get3" [{} :a 5] 5]
           ["CljM.get" [[1 2 3] 1] 2] ["CljM.get" [[1 2 3] 4294967297] :none] ["CljM.get" [5 :a] nil]
           ["CljM.assoc" [{:a 1 :b 2} :a 3] {:a 3 :b 2}] ["CljM.assoc" [[1 2] 2 9] [1 2 9]] ["CljM.assoc" [[1 2] 3 9] :none]
           ["CljM.dissoc" [{:a 1 :b 2} :a] {:b 2}] ["CljM.count" [nil] 0] ["CljM.count" ["ab"] :none]
           ["CljM.not" [0] false] ["CljM.not" [nil] true] ["CljM.intQ" [9223372036854775808N] false]]]
    (is (m/strict= expected (apply run-op k args)) (str k " " (pr-str args)))))

(deftest option-results-decode-in-the-runtime-representation
  ;; No G1 dec_R yields `some x` with x running as nil (their payloads are numbers, booleans,
  ;; strings and Value vectors); the model's own `Option (Option V)` lookup does: an absent key
  ;; is `some none`, which runs as a SomeBox around nil.
  (let [find (m/model-fn "CljM.find")
        chain (m/edn->cljv {:a 1})
        entries (nth chain 1)
        absent (find (m/edn->cljv :b) entries)
        present (find (m/edn->cljv :a) entries)]
    (is (instance? ansatz.codegen.lean_runtime.SomeBox absent))
    (is (= {:some nil} (m/opt-value absent)) "some none")
    (is (= {:some (m/edn->cljv 1)} (m/opt-value present)) "some (some 1)")
    (is (nil? (m/opt-value nil)) "none"))
  (is (= {:some false} (m/opt-value ((m/model-fn "CljM.decBool") (m/edn->cljv false)))) "some false is false"))

(deftest kernel-spot-checks
  (testing "the kernel evaluates the model to the same answers"
    (is (proves? '(= (Option CljM.V) (CljM.add (CljM.V.vlong 2) (CljM.V.vlong 3)) (Option.some (CljM.V.vlong 5))) '[(rfl)]))
    (is (proves? '(= Bool (Option.isSome (CljM.add (CljM.V.vlong 9223372036854775807) (CljM.V.vlong 1))) false) '[(rfl)]))
    (is (proves? '(= Bool (Option.isSome (CljM.sub (CljM.V.vlong -1) (CljM.V.vlong -9223372036854775808))) false) '[(rfl)]))
    (is (proves? '(= Bool (CljM.truthy (CljM.V.vlist CljM.V.vnil)) true) '[(rfl)]))
    (is (proves? '(= (Option CljM.V) (CljM.get (CljM.V.vmap (CljM.V.ventry (CljM.V.vkw "a") (CljM.V.vlong 1) CljM.V.vnil))
                                               (CljM.V.vkw "a"))
                     (Option.some (CljM.V.vlong 1))) '[(rfl)]))))

(deftest runtime-codec
  (doseq [x [nil true 0 -1 Long/MIN_VALUE 9223372036854775808N 1.5 -0.0 \a "s" :a :ns/k 'sym () '(1 2) [1 [2]]
             {:a 1 :b {:c [nil]}} #{1 :a} (map inc [0 1]) (map inc [])]]
    (is (m/strict= x (m/cljv->edn (m/edn->cljv x))) (pr-str x)))
  (testing "strict= keeps what = forgets"
    (is (not (m/strict= [1] '(1))))
    (is (not (m/strict= '(1) (map identity [1]))))
    (is (not (m/strict= 1 1.0)))
    (is (not (m/strict= 0.0 -0.0)))
    (is (m/strict= Double/NaN Double/NaN))
    (is (m/strict= 1 1N))
    (is (m/strict= {:a [1] :b 2} (hash-map :b 2 :a [1])))))

(deftest clojure-facts-the-model-relies-on
  ;; UNSURE 6 of the plan, settled by running Clojure 1.12.0 (G.4 rows check the model against them)
  (let [throws? (fn [f] (try (f) false (catch Throwable _ true)))
        sub (fn [a b] (- a b))
        big (zipmap (range 9) (range 9))]
    (is (throws? #(sub -1 Long/MIN_VALUE)) "boxed - negates its second operand: MIN_VALUE throws")
    (is (= Long/MAX_VALUE (- -1 Long/MIN_VALUE)) "the primitive path does not (both operands literals)")
    (is ((fn [x] (= x x)) Double/NaN) "a boxed NaN equals itself (identity), so = on NaN is no claim")
    (is (not (= Double/NaN (Double. Double/NaN))))
    (is (instance? clojure.lang.PersistentHashMap (dissoc big 0)) "dissoc keeps a hash map a hash map")
    (is (list? (rest [1])) "(rest [1]) is () — an EmptyList, list?")
    (is (nil? (+ nil)) "(+ nil) is (cast Number nil)")
    (is (nil? (get "abc" :a)))))

;; ── Translation ─────────────────────────────────────────────────────────────────────────

(deftest refusals
  (doseq [[form reason]
          '[[(fn [x] (map inc x)) :higher-order] [(fn [x & y] x) :varargs] [(fn [[a b]] a) :destructuring]
            [(fn [x] (let [{:keys [a]} x] a)) :destructuring] [(fn [x] (println x) x) :multi-form-body]
            [(fn [x] (Math/abs x)) :interop] [(fn [x] (.length x)) :interop] [(fn [x] Long/MAX_VALUE) :interop]
            [(fn [x] (loop [i x] i)) :recursion] [(fn [x] (self x)) :recursion] [(fn [x] (str x)) :unmodelled-fn]
            [(fn [x] (swap! x inc)) :mutable-state] [(fn [x] (try x (catch Exception e nil))) :try-catch]
            [(fn [x] (case x 1 2 3)) :dispatch] [(fn ([x] x) ([x y] y)) :multi-arity] [(fn [x] (re-find #"a" x)) :regex]
            [(fn [x] (iterate inc x)) :lazy-infinite] [(fn [x] (eval x)) :eval] [(fn [x] *out*) :dynamic-var]
            [(fn [x] inc) :escaping-fn] [(fn [x] (fn [y] y)) :escaping-fn] [(fn [f x] (f x)) :higher-order]]]
    (let [data (try (tr/translate form 'ansatz.clj-model-test 'self) nil
                    (catch clojure.lang.ExceptionInfo ex (ex-data ex)))]
      (is (= :clj/refused (:kind data)) (pr-str form))
      (is (= reason (:reason data)) (pr-str form))
      (is (contains? tr/refusal-reasons (:reason data))))))

(deftest macros-expand-in-the-source-namespace
  (let [{:keys [body]} (tr/translate '(fn [a b] (when-some [x a] (cond-> x (pos? b) inc)))
                                     'ansatz.clj-model-test 'f)]
    (is (seq? body))
    (is (not-any? #{'when-some 'cond-> 'clojure.core/let} (flatten (seq body))))))

;; ── a/foreign ^:model ────────────────────────────────────────────────────────────────────

(deftest clamp-is-a-definition-and-proves-conforming
  (let [ci (env/lookup (a/env) (name/from-string "clamp"))]
    (is (.isDef ^ansatz.kernel.ConstantInfo ci) "an a/foreign ^:model name is a definition, not an axiom")
    (is (= "irreducible" (get (env/get-extension (a/env) :reducibility-status {}) "clamp"))))
  (is (= [3 1 2] [(clamp 5 1 3) (clamp -2 1 3) (clamp 2 1 3)]))
  (is (= :tested (b/status 'clamp)))
  (is (= :conforming (:status (cc/check-model! 'clamp :runs 30))))
  (binding [a/*verbose* false]
    (a/conforms clamp
                (simp [clamp.clj CljM.encInt CljM.lt CljM.ltL CljM.gt CljM.truthy])
                (split)
                (all_goals (simp [CljM.decInt CljM.lt CljM.ltL CljM.truthy]))
                (split)
                (all_goals (rfl))))
  (is (= :proved (b/status 'clamp)))
  (is (some? (env/lookup (a/env) (name/from-string "clamp.conforms"))))
  (is (some? (env/lookup (a/env) (name/from-string "clamp.spec"))) "f.spec from the generic lemma")
  (is (= 3 (clamp 5 1 3)) "the :proved runtime is the impl"))

(deftest value-showcase-is-tested-with-witnesses
  (is (= {:a 1 :b 2 :total 3} (data/value->edn (add-total (data/edn->value {:a 1 :b 2})))))
  (is (thrown? ArithmeticException (add-total (data/edn->value {:a Long/MAX_VALUE :b 1})))
      "the runtime is the user's function: it throws on overflow")
  (let [{:keys [status faithful witnesses]} (cc/check-model! 'add-total :runs 40)
        clj (map :clojure witnesses)]
    (is (= :nonconforming status))
    (is (zero? (:model-bug faithful)))
    (is (pos? (:agree faithful)))
    (is (some #(= "java.lang.ArithmeticException" (:threw %)) clj) "an overflow witness")
    (is (some #(#{"java.lang.NullPointerException" "java.lang.ClassCastException"} (:threw %)) clj)
        "a non-int witness")))

(deftest boundary-agrees-per-type
  (testing "Nat: dec requires 0 ≤ i"
    (is (= 5 (id-nat 5)))
    (is (= :clj-model/nonconforming (:kind (try (id-nat -1) nil (catch clojure.lang.ExceptionInfo ex (ex-data ex))))))
    (is (proves? '(= Nat (id-nat 5) 5) '[(rfl)]))
    (is (proves? '(= Nat (id-nat -1) 0) '[(rfl)]) "the kernel's d_Nat where the runtime refuses"))
  (testing "Int"
    (is (= -7 (id-int -7)))
    (is (proves? '(= Int (id-int -7) -7) '[(rfl)])))
  (testing "Bool"
    (is (false? (id-bool false)))
    (is (proves? '(= Bool (id-bool true) true) '[(rfl)])))
  (testing "String"
    (is (= "pos" (not-a-string 1)))
    (is (= :clj-model/nonconforming
           (:kind (try (not-a-string -1) nil (catch clojure.lang.ExceptionInfo ex (ex-data ex))))))
    (is (proves? '(= String (not-a-string 1) "pos") '[(rfl)]))
    (is (proves? '(= String (not-a-string -1) "") '[(rfl)])))
  (testing "Value: ofValue/toValue? as edn->value/value->edn"
    (doseq [x [nil {:a 1 :b [1 "s" :k]} [1 2.5] #{3} {:a {:b nil}}]]
      (is (= (data/edn->value x) (id-val (data/edn->value x))) (pr-str x)))
    (is (= :clj-model/nonconforming
           (:kind (try (id-val (data/edn->value (zipmap (range 9) (range 9)))) nil
                       (catch clojure.lang.ExceptionInfo ex (ex-data ex)))))
        "a map over 8 entries has hash order: toValue? is none")
    (is (proves? '(= Value (id-val (Value.vmap (Value.ventry (Value.vkw "a") (Value.vint 1) Value.vnil)))
                     (Value.vmap (Value.ventry (Value.vkw "a") (Value.vint 1) Value.vnil))) '[(rfl)]))
    (is (proves? '(= Value (id-val (Value.vmap (Value.ventry (Value.vkw "a") (Value.vint 1)
                                                             (Value.ventry (Value.vkw "a") (Value.vint 2) Value.vnil))))
                     (Value.vmap (Value.ventry (Value.vkw "a") (Value.vint 1) Value.vnil))) '[(rfl)])
        "ofValue dedupes first-wins, like value->edn")))

(deftest an-untranslatable-source-is-refused-at-definition
  (let [data (try (binding [a/*verbose* false]
                    (eval '(ansatz.core/foreign ^:model bad-model [x :- Int] Int (fn [x] (str x)))))
                  nil
                  (catch Throwable t (some #(when (:kind (ex-data %)) (ex-data %)) (take-while some? (iterate #(.getCause ^Throwable %) t)))))]
    (is (= :unmodelled-fn (:reason data)))))

;; ── Review risk: once f has a value, codegen must call the impl, never the model ──────────

(deftest codegen-calls-the-impl-not-the-model
  (let [env (a/env)
        syms (fn [code] (set (filter symbol? (tree-seq coll? seq code))))
        app (cg/ansatz->clj env (e/lam "x" (const "Int") (e/app (const "succ-int") (e/bvar 0)) :default) [])
        value (cg/ansatz->clj env (const "succ-int") [])]
    (is (contains? (syms app) 'ansatz.clj-model-test/succ-int) "FAP through the arity registry")
    (is (= 'ansatz.clj-model-test/succ-int value) "value position")
    (is (not-any? #(re-find #"CljM|succ-int\.clj|succ-int\$dot\$clj" (str %)) (syms app)))
    (is (contains? @ingest/arity-registry "succ-int") "registered: storedef compilation is never reached")
    (is (nil? (get (env/get-extension env :csimp {}) "succ-int")))
    (is (not= ansatz.kernel.ConstantInfo/HINTS_ABBREV
              (.getHints ^ansatz.kernel.ConstantInfo (env/lookup env (name/from-string "succ-int"))))
        "not an abbrev: codegen never inlines its value"))
  (testing "where the model says none (kernel: d_R = 0), the runtime runs the impl, which throws"
    (is (= 5 (use-succ 4)))
    (is (thrown? ArithmeticException (use-succ Long/MAX_VALUE)))
    (is (= [2 3] (vec (use-succ-map [1 2]))))
    (is (thrown? ArithmeticException (doall (use-succ-map [Long/MAX_VALUE]))))
    (is (proves? '(= Int (succ-int 9223372036854775807) 0) '[(rfl)])
        "the :tested gap, visible: the kernel's value where the model has no claim")))
