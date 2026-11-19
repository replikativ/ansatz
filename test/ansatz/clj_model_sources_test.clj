(ns ansatz.clj-model-sources-test
  "PR G2b: destructuring, `a/defmodel` and source lookup, and the List/Option/Prod/Float/
   structure/Subtype boundary codecs of the Clojure model."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [ansatz.core :as a]
            [ansatz.fixtures :as fixtures]
            [ansatz.clj-check :as cc]
            [ansatz.clj-model :as m]
            [ansatz.clj-model.translate :as tr]
            [ansatz.clj-model.boundary :as b]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [ansatz.surface.data :as data]))

;; A plain defn in a source file: the model finds its source with clojure.repl/source-fn.
(defn pair-sum [[a b]] (+ a b))

(a/defmodel clamp-total
  "Sum of :a and :b, at most 100."
  [{:keys [a b] :or {b 0}}]
  (min 100 (+ a b)))

(defn- define-models! []
  (a/structure Pt [] (x Int) (y Int))
  (a/foreign ^:model total [m :- Value] Int clamp-total)
  (a/foreign ^:model psum [p :- (Prod Int Int)] Int pair-sum)
  (a/foreign ^:model swap [p :- (Prod Int Int)] (Prod Int Int) (fn [[a b]] [b a]))
  (a/foreign ^:model incs [xs :- (List Int)] (List Int) (fn [xs] (mapv inc xs)))
  (a/foreign ^:model id-list [xs :- (List Int)] (List Int) (fn [xs] xs))
  (a/foreign ^:model len-of [xs :- (List Int)] Nat (fn [xs] (count xs)))
  (a/foreign ^:model first-of [xs :- (List Int)] (Option Int) (fn [xs] (first xs)))
  (a/foreign ^:model pos-or-none [x :- Int] (Option Int) (fn [x] (when (pos? x) x)))
  (a/foreign ^:model id-float [x :- Float] Float (fn [x] x))
  (a/foreign ^:model pt-flip [p :- Pt] Pt (fn [{:keys [x y]}] {:x y :y x}))
  (a/foreign ^:model small-inc [n :- (Subtype Int (fn [i :- Int] (< i 100)))] Int (fn [n] (inc n))))

(defn- setup [f]
  (binding [a/*verbose* false]
    (a/load-init!)
    (data/install-value-type!)
    (b/install-codecs!)
    (define-models!)
    (f)))

(use-fixtures :once fixtures/isolated-session setup)

(defn- proves? [prop tactics]
  (try (binding [a/*verbose* false] (a/prove-theorem (gensym "clj-model-fact") '[] prop tactics)) true
       (catch Throwable _ false)))

(deftest destructuring
  (testing "Clojure's destructure, over modelled functions"
    (doseq [form '[(fn [c] (let [[a b & r :as all] c] [a b r all]))
                   (fn [m] (let [{:keys [a b] :or {b 5} :as all} m] [a b all]))
                   (fn [m] (let [{x :a [y z] :b, :strs [s]} m] [x y z s]))
                   (fn [[k v]] [v k])]]
      (is (map? (tr/translate form 'ansatz.clj-model-sources-test 'f)) (pr-str form))))
  (testing "keyword arguments (a seq destructured as a map) are no claim, not a refusal"
    (let [{:keys [counts]} (cc/run-model-row {:id :showcase/kwargs :form '(let [{:keys [a]} m] a)
                                              :params '[[m :seqable]]})]
      (is (zero? (:model-bug counts)))
      (is (pos? (:agree counts)))))
  (testing "what Clojure itself rejects is refused"
    (is (= :destructuring (:reason (try (tr/translate '(fn [x] (let [[a & b c] x] a)) 'ansatz.clj-model-sources-test 'f)
                                        (catch clojure.lang.ExceptionInfo ex (ex-data ex))))))))

(deftest sources
  (testing "a/defmodel records the source; the foreign function translates it"
    (is (= :defmodel (get-in (b/info 'total) [:source-info :from])))
    (is (= 30 (total (data/edn->value {:a 10 :b 20}))))
    (is (= 100 (total (data/edn->value {:a 99 :b 20}))))
    (is (= 7 (total (data/edn->value {:a 7}))) ":or default")
    (is (proves? '(= Int (total (Value.vmap (Value.ventry (Value.vkw "a") (Value.vint 4) Value.vnil))) 4) '[(rfl)]))
    (is (zero? (get-in (cc/check-model! 'total :runs 40) [:faithful :model-bug]))))
  (testing "a plain defn from a source file: clojure.repl/source-fn, with the file's hash"
    (let [{:keys [from file sha256]} (:source-info (b/info 'psum))]
      (is (= :source-fn from))
      (is (re-find #"clj_model_sources_test" (str file)))
      (is (= 64 (count sha256))))
    (is (= 5 (psum [2 3]))))
  (testing "a REPL defn has no source: refused"
    (let [data (try (binding [*ns* (the-ns 'ansatz.clj-model-sources-test) a/*verbose* false]
                      (eval '(defn repl-fn [x] x))
                      (eval '(ansatz.core/foreign ^:model repl-model [x :- Int] Int repl-fn)))
                    nil
                    (catch Throwable t (some #(when (:kind (ex-data %)) (ex-data %))
                                             (take-while some? (iterate #(.getCause ^Throwable %) t)))))]
      (is (= :no-source (:reason data))))))

(deftest codecs-agree-per-type
  (testing "List"
    (is (= [2 3] (vec (incs [1 2]))))
    (is (= [] (vec (id-list []))))
    (is (proves? '(= (List Int) (incs (List.cons 1 (List.cons 2 List.nil))) (List.cons 2 (List.cons 3 List.nil))) '[(rfl)]))
    (is (thrown? ArithmeticException (incs [Long/MAX_VALUE])) "the impl throws on overflow (no claim in the model)")
    (is (= [1 2] (vec (id-list (list 1 2))))))
  (testing "Option: none is nil"
    (is (= 5 (pos-or-none 5)))
    (is (nil? (pos-or-none -5)))
    (is (proves? '(= (Option Int) (pos-or-none -5) Option.none) '[(rfl)]))
    (is (= :clj-model/no-codec (:kind (try (b/codec '(Option (List Int))) nil (catch Exception ex (ex-data ex)))))
        "nil would be ambiguous")
    (is (map? (b/codec '(Option Bool))) "false is not nil"))
  (testing "Prod, Float, a structure, a Subtype parameter"
    (is (= [2 1] (vec (swap [1 2]))))
    (is (= 1.5 (id-float 1.5)))
    (is (= {:x 2 :y 1} (into {} (pt-flip ((resolve 'ansatz.clj-model-sources-test/->Pt) 1 2)))))
    (is (proves? '(= Pt (pt-flip (Pt.mk 1 2)) (Pt.mk 2 1)) '[(rfl)]))
    (is (= 6 (small-inc 5)))
    (is (= :clj-model/no-codec (:kind (try (b/define-modelled 'bad-sub '[x :- Int] '(Subtype Int (fn [i :- Int] (< i 1)))
                                             '(fn [x] x) identity 'ansatz.clj-model-sources-test)
                                           nil (catch Exception ex (ex-data ex)))))
        "a Subtype has no default value: parameters only")))

(deftest default-script-splits-compound-parameters
  (is (= '[(cases p) (induction xs) (cases o)]
         (take 3 (ansatz.clj-model.proof/default-script 'g '[[p (Prod Int Int)] [xs (List Int)] [o (Option Int)] [n Int]])))))

(deftest prod-conformance-is-proved
  (is (= :tested (b/status 'swap)))
  (binding [a/*verbose* false]
    (a/conforms swap))
  (is (= :proved (b/status 'swap)))
  (is (some? (env/lookup (a/env) (name/from-string "swap.spec"))))
  (is (= [4 3] (vec (swap [3 4]))) "the :proved runtime decodes the impl's vector"))

(deftest list-conformance-is-proved
  (testing "count over a List codec: the default script (induction on a List parameter)"
    (binding [a/*verbose* false]
      (a/conforms len-of))
    (is (= :proved (b/status 'len-of)))
    (is (= 3 (len-of [4 5 6]))))
  (testing "first into an Option codec: the default script"
    (binding [a/*verbose* false]
      (a/conforms first-of))
    (is (= :proved (b/status 'first-of)))
    (is (= [4 nil] [(first-of [4 5]) (first-of [])]))))
