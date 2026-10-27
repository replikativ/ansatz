(ns prototype.continuation-layout-test
  (:require [clojure.test :refer [deftest is use-fixtures]]
            [prototype.continuation-layout :as layout]
            [prototype.mutable :as mutable])
  (:import [java.util HashMap ArrayList]
           [java.lang.ref WeakReference ReferenceQueue]))

(use-fixtures :each
  (fn [f]
    (with-redefs-fn {#'layout/cache {:buckets (HashMap.) :queue (ReferenceQueue.) :owner (volatile! nil)}} f)))
(defn legacy [body fallback] (#'mutable/measure-continuation-slots body fallback))
(defn width [body fallback generation]
  (layout/width body fallback legacy (constantly true) generation))
(defn entry [body] (#'layout/cached-entry body))
(defn entry-count []
  (reduce + 0 (map #(.size ^ArrayList %) (.values ^HashMap (:buckets @#'layout/cache)))))

(deftest every-instruction-and-expression-matches-reference-sizing
  (let [generation (Object.) end [:return [:var 17]]
        expressions [[:literal (object-array [1])] [:ctor :opaque [[:var 80]]]
                     [:scalar-ctor :opaque [[:var 81]]] [:closure :opaque [[:var 82]]]
                     [:runtime :opaque [[:var 83]]] [:prim :opaque [[:var 84]]]
                     [:project [:var 85] :opaque] [:shared? [:var 86]]
                     [:scalar-get [:var 87] :opaque] [:box :opaque [:var 88]]
                     [:unbox :opaque [:var 89]] [:unknown-expression :opaque]]
        bodies (concat (map #(vector :let 2 % end) expressions)
                       [[:call 40 [:direct :opaque] [[:var 70]] end]
                        [:call 40 [:closure [:var 90]] [[:var 70]] end]
                        [:tail [:direct :opaque] [[:var 71]]]
                        [:tail [:closure [:var 91]] [[:var 72]]]
                        [:return [:var 12]] [:read-global :opaque] [:global :opaque]
                        [:unreachable] [:begin-init :opaque :opaque [[:var 73]]]
                        [:publish-global :opaque [:var 74]] [:publish-io-global :opaque :opaque [:var 75]]
                        [:join 0 [99] [:return [:var 99]] end] [:jump :opaque [[:var 76]]]
                        [:case [:var 3] [[0 [:return [:var 100]]] [:default end]]]
                        [:trap :opaque [[:var 77]]] [:del [:var 78] end]
                        [:set-tag [:var 79] :opaque end] [:inc [:var 80] :opaque end]
                        [:dec [:var 81] :opaque end]
                        [:set [:var 82] :opaque [:var 83] end]
                        [:scalar-set [:var 84] :opaque [:var 85] end]
                        [:suspend 101 end] [:host :opaque [[:var 86]] 102 end]
                        [:unknown-instruction (object-array [:opaque])]])]
    (doseq [body bodies fallback [1 200]]
      (is (= (legacy body fallback) (width body fallback generation)))
      (is (entry body))
      (is (= (legacy body fallback) (width body fallback generation))))))

(deftest cold-root-computes-all-suffixes-and-shared-branches-without-recursion
  (let [generation (Object.) suffix [:return [:var 500]]
        chain (reduce (fn [body _] [:host "no-op" [] 2 body]) suffix (range 10000))
        root [:case [:imm 0] [[0 chain] [:default chain]]]]
    (is (= 501 (width root 1 generation)))
    (is (= 10002 (entry-count)))
    (is (= 501 (nth (entry suffix) 2)))
    (is (= 501 (nth (entry chain) 2)))
    (let [before (entry chain)]
      (is (= 501 (width chain 1 generation)))
      (is (identical? before (entry chain))))))

(deftest opaque-live-payloads-are-never-hashed-compared-or-walked
  (let [generation (Object.)
        poison (proxy [Object] []
                 (hashCode [] (throw (AssertionError. "hashed payload")))
                 (equals [_] (throw (AssertionError. "compared payload"))))
        payload (object-array [poison])
        tail [:return [:imm payload]]
        body (with-meta [:let 90 [:literal payload] tail] {:owner poison})]
    (is (= 91 (width body 2 generation)))
    (aset payload 0 (Object.))
    (is (= 91 (width body 2 generation)))
    (is (= 1 (width tail 2 generation)))
    (is (= 2 (entry-count)))))

(deftest equal-bodies-fallback-and-owner-generation-do-not-share-stale-evidence
  (let [generation (Object.) body [:unknown-instruction] equal (with-meta body {:distinct true})]
    (is (= 5 (width body 5 generation)))
    (is (nil? (entry equal)))
    (is (= 9 (width equal 9 generation)))
    (is (= 2 (entry-count)))
    (is (= 100 (width body 100 generation)))
    (is (= 2 (entry-count)))
    (is (= 100 (second (entry body))))
    (let [before (entry body)]
      (is (= 3 (width body 3 (Object.))))
      (is (= 1 (entry-count)))
      (is (not (identical? before (entry body)))))))

(deftest unsupported-nested-control-publishes-no-partial-sibling-proofs
  (let [generation (Object.) left [:return [:var 7]] tail [:return [:var 1]]
        operands (object-array [[:var 20]])
        right [:let 2 [:prim :inc operands] tail]
        root [:join 0 [] left right]]
    (is (= (legacy root 1) (width root 1 generation)))
    (is (zero? (entry-count)))
    (aset operands 0 [:var 200])
    (is (= 201 (width root 1 generation)))
    (is (zero? (entry-count)))
    (doseq [body [nil false [] [:let 0 [:literal 1] nil]
                  [:case [:imm 0] (list [0 tail])]]]
      (is (= (legacy body 30) (width body 30 generation)))
      (is (zero? (entry-count))))
    (let [bad [:join 0 [] false tail]
          old (try (legacy bad 30) nil (catch Exception error error))
          actual (try (width bad 30 generation) nil (catch Exception error error))]
      (is (instance? Exception old))
      (is (= (class old) (class actual)))
      (is (= (.getMessage ^Exception old) (.getMessage ^Exception actual)))
      (is (zero? (entry-count))))))

(deftest changed-owner-or-analysis-rules-use-the-original-scanner
  (let [generation (Object.) body [:let 2 [:prim :inc [[:var 30]]] [:return [:var 2]]]
        legacy-calls (atom 0)
        fallback (fn [body n] (swap! legacy-calls inc) (legacy body n))
        owner-vars [#'mutable/measure-continuation-slots #'mutable/expression-slots
                    #'mutable/operands-slots #'mutable/operand-slots #'mutable/ids-slots]
        leaf-vars [#'layout/id-classes #'layout/frozen-id? #'layout/vector?* #'layout/ids-width
                   #'layout/operand-width #'layout/operands-width #'layout/target-width
                   #'layout/expression-width #'layout/branch-bodies #'layout/description #'layout/analyze
                   #'layout/ensure-owner! #'layout/drain! #'layout/cached-entry #'layout/cached-width #'layout/remember!]]
    (is (= 31 (layout/width body 1 fallback #'mutable/builtin-continuation-layout? generation)))
    (is (zero? @legacy-calls))
    (doseq [rule (concat owner-vars leaf-vars)]
      (is (= 31 (layout/width body 1 fallback #'mutable/builtin-continuation-layout? generation)))
      (let [original @rule replacement (if (fn? original) (fn [& args] (apply original args))
                                        (with-meta original {:changed true}))]
        (with-redefs-fn {rule replacement}
          #(let [before @legacy-calls]
             (is (= 31 (layout/width body 1 fallback #'mutable/builtin-continuation-layout? generation)))
             (is (= (inc before) @legacy-calls))))))
    (is (= 31 (layout/width body 1 fallback #'mutable/builtin-continuation-layout? generation)))
    (is (= 21 @legacy-calls))
    ;; A changed eligibility helper must not execute before its identity guard.
    (with-redefs-fn {#'layout/frozen-id? (fn [& _] (throw (AssertionError. "changed eligibility helper")))}
      #(is (= 31 (layout/width body 1 fallback #'mutable/builtin-continuation-layout? generation))))
    (is (= 22 @legacy-calls))
    (with-redefs-fn {#'layout/cached-width (constantly 999999)}
      #(is (= 31 (layout/width body 1 fallback #'mutable/builtin-continuation-layout? generation))))
    (is (= 23 @legacy-calls))
    (is (zero? (entry-count)))))

(deftest changes-during-analysis-discard-all-staged-widths
  (let [generation (Object.) left [:return [:var 5]] tail [:return [:var 1]]
        right [:host "ping" [] 2 tail] body [:join 0 [] left right]
        lookups (atom 0) descriptor @#'layout/description calls (atom 0)
        buckets (proxy [HashMap] []
                  (get [key]
                    ;; Change a semantic rule after the left child was staged.
                    (when (= 4 (swap! lookups inc))
                      (alter-var-root #'layout/description
                                      (constantly (fn [& _] (throw (IllegalStateException. "changed during scan"))))))
                    (proxy-super get key)))]
    (try
      (with-redefs-fn {#'layout/cache {:buckets buckets :queue (ReferenceQueue.) :owner (volatile! nil)}}
        #(do
           (is (= 6 (layout/width body 1 (fn [body n] (swap! calls inc) (legacy body n))
                                   (constantly true) generation)))
           (is (= 4 @lookups))
           (is (= 1 @calls))
           (is (zero? (entry-count)))))
      (finally (alter-var-root #'layout/description (constantly descriptor))))))

(deftest cache-values-are-weak-identity-and-scalars-and-queue-cleanup-is-deterministic
  (let [generation (Object.) body [:return [:var 7]]]
    (is (= 8 (width body 1 generation)))
    (let [[reference fallback slots :as proof] (entry body)
          hash (System/identityHashCode body)]
      (is (= 3 (count proof)))
      (is (nil? (meta proof)))
      (is (instance? WeakReference reference))
      (is (identical? body (.get ^WeakReference reference)))
      (is (= [1 8] [fallback slots]))
      (.clear ^WeakReference reference)
      (.enqueue ^WeakReference reference)
      (is (= 1 (width [:return [:imm 0]] 1 generation)))
      (is (not-any? #(identical? reference (first %))
                    (.get ^HashMap (:buckets @#'layout/cache) hash))))))
