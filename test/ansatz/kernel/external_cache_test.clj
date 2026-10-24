(ns ansatz.kernel.external-cache-test
  "Real external lookup views and independently well-typed declarations. A
   descriptive store ID cannot authorize sharing a different handler's cache."
  (:require [clojure.test :refer [deftest is testing]])
  (:import [ansatz.kernel Env Name Level Expr ConstantInfo TypeChecker Reducer]))

(def ^:private declaration-name (Name/fromString "ExternalCache.x"))
(def ^:private local-name (Name/fromString "ExternalCache.local"))
(def ^:private result-name (Name/fromString "ExternalCache.result"))
(defn- sort-at [n]
  (Expr/sort (nth (iterate #(Level/succ %) Level/ZERO_LEVEL) n) false))
(defn- definition [nm n]
  ;; Sort n : Sort (n+1), so these are real, individually valid definitions.
  (ConstantInfo/mkDefWithHints nm (object-array []) (sort-at (inc n)) (sort-at n)
                               ConstantInfo/REDUCIBILITY_ABBREV (byte 0) (object-array [nm])))
(defn fixture []
  (let [a (definition declaration-name 0) b (definition declaration-name 1)
        calls (atom {:a 0 :b 0})
        fa (fn [n] (swap! calls update :a inc) (when (= declaration-name n) a))
        fb (fn [n] (swap! calls update :b inc) (when (= declaration-name n) b))
        base (.withExtension (Env.) :diagnostic-store-id "same-store-and-branch")]
    {:a a :b b :fa fa :fb fb :base base :calls calls}))
(defn- ci-shape [^ConstantInfo ci]
  (when ci
    [(.tag ci) (.name ci) (vec (.levelParams ci)) (.type ci) (.value ci)
     (.getHintsCode ci) (.safety ci) (vec (.all ci))]))
(defn- changed-view [^Env env handler filtered?]
  (if filtered? (.withExternalLookupFiltered env handler 1 (constantly true))
      (.withExternalLookup env handler 1)))
(defn- accepted? [^Env env ^ConstantInfo ci]
  (try (TypeChecker/checkConstant env ci) true (catch RuntimeException _ false)))

(deftest changing-handler-isolates-both-views-before-either-query
  (doseq [filtered? [false true] order [[:a :b] [:b :a]]]
    (let [{:keys [a b fa fb base calls]} (fixture)
          _ (is (identical? a (.lookupLocal (TypeChecker/checkConstant (Env.) a) declaration-name)))
          _ (is (identical? b (.lookupLocal (TypeChecker/checkConstant (Env.) b) declaration-name)))
          av (.withExternalLookup ^Env base fa 1)
          bv (changed-view av fb filtered?) views {:a av :b bv} expected {:a a :b b}]
      (is (not= (ci-shape a) (ci-shape b)))
      (is (= (.getExtension av :diagnostic-store-id) (.getExtension bv :diagnostic-store-id)))
      (is (false? (.sameExternalView av bv)))
      (doseq [key (concat order (reverse order))]
        (is (identical? (get expected key) (.lookup ^Env (get views key) declaration-name))))
      (is (= {:a 1 :b 1} @calls)))))

(deftest independently-routed-forks-do-not-populate-the-empty-common-base
  (doseq [order [[:a :b] [:b :a]]]
    (let [{:keys [a b fa fb base calls]} (fixture)
          av (.withExternalLookup (.fork ^Env base) fa 1)
          bv (.withExternalLookupFiltered (.fork ^Env base) fb 1 (constantly true))
          views {:a av :b bv} expected {:a a :b b}]
      (is (nil? (.lookup ^Env base declaration-name)))
      (doseq [key order]
        (is (identical? (expected key) (.lookup ^Env (views key) declaration-name)))
        (is (nil? (.lookup ^Env base declaration-name))))
      (is (= {:a 1 :b 1} @calls)))))

(deftest changed-handler-cannot-turn-a-wrong-universe-declaration-into-a-proof
  (doseq [filtered? [false true] order [[:a :b] [:b :a]]]
    (let [{:keys [fa fb base]} (fixture)
          av (.withExternalLookup ^Env base fa 1) bv (changed-view av fb filtered?)
          views {:a av :b bv}
          value (Expr/mkConst declaration-name [] false)
          candidate (ConstantInfo/mkDefWithHints result-name (object-array []) (sort-at 1) value
                                                 ConstantInfo/REDUCIBILITY_ABBREV (byte 0) (object-array [result-name]))]
      (doseq [key order] (.lookup ^Env (get views key) declaration-name))
      (is (accepted? av candidate))
      (is (false? (accepted? bv candidate))))))

(deftest cached-and-uncached-views-have-the-same-complete-declarations-and-kernel-results
  (doseq [filtered? [false true]]
    (let [{:keys [a b fa fb base]} (fixture)
          av (.withExternalLookup ^Env base fa 1)
          bv (changed-view av fb filtered?)
          au (.withExternalLookupUncached ^Env base fa 1)
          bu (changed-view (.withExternalLookupUncached ^Env base fb 1) fb filtered?)
          expr (Expr/mkConst declaration-name [] false)]
      ;; Repeated interleaving exercises both source caches, not only one hit.
      (dotimes [_ 3]
        (doseq [[view uncached expected] [[av au a] [bv bu b]]]
          (is (= (ci-shape expected) (ci-shape (.lookup ^Env view declaration-name))
                 (ci-shape (.lookup ^Env uncached declaration-name))))
          (is (= (.type ^ConstantInfo expected) (.inferType (TypeChecker. view) expr)
                 (.inferType (TypeChecker. uncached) expr)))
          (is (= (.value ^ConstantInfo expected) (.whnf (Reducer. view) expr)
                 (.whnf (Reducer. uncached) expr)))
          (is (nil? (.lookup ^Env view (Name/fromString "ExternalCache.missing")))))))))

(deftest same-handler-forks-and-visibility-views-share-only-visible-cache-hits
  (let [{:keys [a fa base calls]} (fixture)
        av (.withExternalLookup ^Env base fa 1)
        same (.withExternalLookup av fa 99)
        visible (.withExternalLookupFiltered av fa 1 (constantly true))
        hidden (.withExternalLookupFiltered av fa 1 (constantly false))]
    (is (identical? a (.lookup visible declaration-name)))
    (is (nil? (.lookup hidden declaration-name)))
    (is (= 1 (:a @calls)))
    (doseq [view [av same (.fork av) (.enableQuot av) (.withExtension av :local-marker true)]]
      (is (identical? a (.lookup ^Env view declaration-name))))
    (is (= 1 (:a @calls)))
    ;; Clearing only the predicate is safe for the same immutable handler.
    (is (identical? a (.lookup (.withExternalLookup hidden fa 1) declaration-name))))
  (let [{:keys [a b fa fb base calls]} (fixture)
        av (.withExternalLookup ^Env base fa 1) bv (.withExternalLookup av fb 1)
        back (.withExternalLookup bv fa 1)]
    (is (identical? a (.lookup av declaration-name)))
    (is (identical? b (.lookup bv declaration-name)))
    (is (identical? a (.lookup back declaration-name)))
    (is (= {:a 2 :b 1} @calls))))

(deftest explicitly-uncached-mode-survives-all-external-handler-withers
  (let [calls (atom 0)
        handler (fn [n] (swap! calls inc) (when (= declaration-name n) (definition n 0)))
        replacement (fn [n] (swap! calls inc) (when (= declaration-name n) (definition n 1)))
        initial (.withExternalLookupUncached (Env.) handler 1)]
    (doseq [view [initial (.withExternalLookup initial handler 1)
                  (.withExternalLookup initial replacement 1)
                  (.withExternalLookupFiltered initial handler 1 (constantly true))
                  (.withExternalLookupFiltered initial replacement 1 (constantly true))
                  (.withExternalLookupUncached initial replacement 1)]]
      (let [before @calls first (.lookup ^Env view declaration-name) second (.lookup ^Env view declaration-name)]
        (is (= (+ 2 before) @calls))
        (is (not (identical? first second)))
        (is (= (ci-shape first) (ci-shape second)))))))

(deftest removing-or-throwing-handlers-cannot-read-the-previous-cache
  (doseq [filtered? [false true]]
    (let [{:keys [a fa base]} (fixture) av (.withExternalLookup ^Env base fa 1)
          _ (.lookup av declaration-name)
          absent (changed-view av nil filtered?)
          failure (ex-info "selected external read failure" {})
          failed (changed-view av (fn [_] (throw failure)) filtered?)]
      (is (nil? (.lookup absent declaration-name)))
      (is (identical? failure (try (.lookup failed declaration-name) nil (catch Throwable cause cause))))
      (is (identical? a (.lookup av declaration-name)))))
  (let [{:keys [fa base]} (fixture) av (.withExternalLookup ^Env base fa 1)]
    (.lookup av declaration-name)
    (is (nil? (.lookup (.withExternalLookupUncached av nil 0) declaration-name)))))

(deftest local-shadow-quotient-and-extension-state-survive-all-source-withers
  (doseq [filtered? [false true]]
    (let [{:keys [a fa fb base calls]} (fixture)
          original (.withExternalLookup ^Env base fa 1) _ (.lookup original declaration-name)
          local (definition declaration-name 2) extra (definition local-name 0)
          shadow (-> original (.addOrReplaceConstant local) (.addConstant extra)
                     (.enableQuot) (.withExtension :retained-extension {:local true}))
          changed (changed-view shadow fb filtered?)
          hidden (.withExternalLookupFiltered shadow fb 1 (constantly false))]
      (doseq [view [shadow changed hidden (.withExternalLookupUncached shadow fb 1)]]
        (is (identical? local (.lookup ^Env view declaration-name))))
      (is (identical? extra (.lookup changed local-name)))
      (is (.isQuotEnabled changed))
      (is (= {:local true} (.getExtension changed :retained-extension)))
      (is (nil? (.lookup original local-name)))
      (is (identical? a (.lookup original declaration-name)))
      (is (zero? (:b @calls))))))
