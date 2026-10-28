(ns ansatz.meta.match.match-test
  (:require [clojure.test :refer [deftest is testing]]
            [ansatz.core :as a]
            [ansatz.export.parser :as parser]
            [ansatz.export.replay :as replay]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.reduce :as red]
            [ansatz.kernel.tc :as tc]
            [ansatz.meta.constructions.util :as u]
            [ansatz.meta.tactic.cases :as c]
            [ansatz.meta.match.basic :as b]
            [ansatz.meta.match.match :as m]
            [ansatz.meta.match.matcher-info :as mi]
            [ansatz.matchers :as imported]))

(def environment (delay (binding [a/*verbose* false] (a/load-init!))))
(def extra-oracle
  (delay
    (with-open [in (java.util.zip.GZIPInputStream.
                    (java.io.FileInputStream. "test-data/kernel-reference/matcher-values.ndjson.gz"))]
      (parser/with-parser-state
        (parser/parse-ndjson-string (slurp in))
        (fn [parsed]
          (let [base (:env (replay/replay (:decls parsed) :stop-on-error? true))
                [out stats] (imported/import-matchers base
                              "test-data/kernel-reference/matcher-values-matchers.ndjson")]
            (when-not (= {:loaded 4} stats)
              (throw (ex-info "Incomplete matcher oracle metadata" {:stats stats})))
            out))))))
(defn ctor [n & fields] (b/ctor (name/from-string n) [] [] fields))
(def nat (u/const' "Nat" []))
(def bool (u/const' "Bool" []))

(defn bool-matcher []
  (let [ctx (c/context @environment)]
    (m/mk-matcher ctx {:matcher-name "MatcherReference.bool.match_1"
                       :match-type (e/forall' "b" bool nat :default)
                       :discr-infos [(mi/discr-info)]
                       :lhss [(b/alt-lhs nil [] [(ctor "Bool.false")])
                              (b/alt-lhs nil [] [(ctor "Bool.true")])]})))

(deftest boolean-matcher-is-checked-and-has-unit-thunk-alternatives
  (let [{:keys [env matcher info counter-examples unused-alt-idxs]} (bool-matcher)
        motive (e/lam "_" bool nat :default)
        alt0 (e/lam "_" (u/const' "Unit" []) (e/lit-nat 13) :default)
        alt1 (e/lam "_" (u/const' "Unit" []) (e/lit-nat 21) :default)]
    (is (empty? counter-examples))
    (is (empty? unused-alt-idxs))
    (is (= [true true] (mapv :unit-thunk (:alts info))))
    (is (= info (mi/get-matcher-info-core? env "MatcherReference.bool.match_1")))
    (doseq [[value expected] [["Bool.false" 13] ["Bool.true" 21]]]
      (is (= (e/lit-nat expected)
             (red/whnf env (u/app matcher [motive (u/const' value []) alt0 alt1])))))))

(deftest nat-value-and-wildcard-matcher-uses-dependent-value-cases
  (let [ctx (c/context @environment)
        x (u/local-decl ctx "x" nat)
        result (m/mk-matcher ctx {:matcher-name "MatcherReference.literal.match_1"
                                  :match-type (e/forall' "n" nat nat :default)
                                  :discr-infos [(mi/discr-info)]
                                  :lhss [(b/alt-lhs nil [] [(b/val-pattern (e/lit-nat 0))])
                                         (b/alt-lhs nil [(u/decl ctx x)] [(b/var-pattern (e/fvar-id x))])]})
        motive (e/lam "_" nat nat :default)
        first (e/lam "_" (u/const' "Unit" []) (e/lit-nat 40) :default)
        last (e/lam "x" nat (e/bvar 0) :default)]
    (is (= [[0 1]] (:overlaps (:info result))))
    (doseq [[n expected] [[0 40] [1 1] [5 5]]]
      (is (= (e/lit-nat expected)
             (red/whnf (:env result) (u/app (:matcher result) [motive (e/lit-nat n) first last])))))))

(deftest nested-constructor-patterns-preserve-first-match-order
  (let [ctx (c/context @environment)
        x (u/local-decl ctx "x" nat) y (u/local-decl ctx "y" nat)
        result (m/mk-matcher ctx {:matcher-name "MatcherReference.nested.match_1"
                                  :match-type (e/forall' "n" nat nat :default)
                                  :discr-infos [(mi/discr-info)]
                                  :lhss [(b/alt-lhs nil [] [(ctor "Nat.zero")])
                                         (b/alt-lhs nil [] [(ctor "Nat.succ" (ctor "Nat.zero"))])
                                         (b/alt-lhs nil [(u/decl ctx x)] [(ctor "Nat.succ" (b/var-pattern (e/fvar-id x)))])
                                         (b/alt-lhs nil [(u/decl ctx y)] [(b/var-pattern (e/fvar-id y))])]})]
    (is (= [3] (:unused-alt-idxs result)))
    (doseq [[n expected] [[0 10] [1 20] [4 3]]]
      (is (= (e/lit-nat expected)
             (red/whnf (:env result)
                       (u/app (:matcher result)
                              [(e/lam "_" nat nat :default) (e/lit-nat n)
                               (e/lam "_" (u/const' "Unit" []) (e/lit-nat 10) :default)
                               (e/lam "_" (u/const' "Unit" []) (e/lit-nat 20) :default)
                               (e/lam "x" nat (e/bvar 0) :default)
                               (e/lam "x" nat (e/lit-nat 99) :default)])))))))

(deftest missing-constructor-produces-a-counterexample
  (let [ctx (c/context @environment)
        result (m/mk-matcher ctx {:matcher-name "MatcherReference.incomplete.match_1"
                                  :match-type (e/forall' "b" bool nat :default)
                                  :discr-infos [(mi/discr-info)]
                                  :lhss [(b/alt-lhs nil [] [(ctor "Bool.false")])]})]
    (is (nil? (:matcher result)))
    (is (seq (:counter-examples result)))
    (is (nil? (env/lookup (:env result) (name/from-string "MatcherReference.incomplete.match_1"))))))

(deftest empty-inductive-match-eliminates-through-false
  (let [ctx (c/context @environment)
        result (m/mk-matcher ctx {:matcher-name "MatcherReference.empty.match_1"
                                  :match-type (e/forall' "x" (u/const' "False" []) nat :default)
                                  :discr-infos [(mi/discr-info)] :lhss []})]
    (is (empty? (:counter-examples result)))
    (is (some? (env/lookup (:env result) (name/from-string "MatcherReference.empty.match_1"))))
    (is (contains? (u/fold-constants conj #{} (:value result)) (name/from-string "False.elim")))))

(deftest missing-cases-follow-leans-counterexample-stack-order
  (let [ctx (c/context @environment)
        result (m/mk-matcher ctx {:matcher-name "MatcherReference.missing.match_1"
                                  :match-type (e/forall' "b" bool nat :default)
                                  :discr-infos [(mi/discr-info)] :lhss []})]
    (is (= ["Bool.true" "Bool.false"]
           (mapv (fn [example] (str (:ctor-name (first example)))) (:counter-examples result))))))

(def init-patterns
  ;; Restated from Init/Prelude.lean Nat.add/mul/pow/beq/ble, Option.getD,
  ;; List.append/concat/foldl; Init/Data/{Option,List}/Basic.lean for the rest.
  '[["Nat.add.match_1" [[a Nat.zero] [a (Nat.succ b)]]]
    ["Nat.mul.match_1" [[_ 0] [a (Nat.succ b)]]]
    ["Nat.pow.match_1" [[0] [(Nat.succ n)]]]
    ["Nat.beq.match_1" [[Nat.zero Nat.zero] [Nat.zero (Nat.succ _)]
                        [(Nat.succ _) Nat.zero] [(Nat.succ n) (Nat.succ m)]]]
    ["Nat.decEq.match_1" [[Bool.true] [Bool.false]]]
    ["Nat.ble.match_1" [[Nat.zero _] [(Nat.succ _) Nat.zero] [(Nat.succ n) (Nat.succ m)]]]
    ["Option.getD.match_1" [[(Option.some x)] [Option.none]]]
    ["Option.isSome.match_1" [[(Option.some _)] [Option.none]]]
    ["Option.bind.match_1" [[Option.none _] [(Option.some a) f]]]
    ["List.append.match_1" [[List.nil bs] [(List.cons a as) bs]]]
    ["List.concat.match_1" [[List.nil b] [(List.cons a as) b]]]
    ["List.reverseAux.match_1" [[List.nil r] [(List.cons a l) r]]]
    ["List.foldl.match_1" [[a List.nil] [a (List.cons b l)]]]
    ["List.dropLast.match_1" [[List.nil] [(List.cons _ List.nil)] [(List.cons a as)]]]
    ;; Init/WF.lean: nested Decidable matches, the outer pair match, and lex's wf match.
    ["Prod.Lex.instDecidableRelOfDecidableEq.match_1" [[(Decidable.isTrue h)] [(Decidable.isFalse h)]]]
    ["Prod.Lex.instDecidableRelOfDecidableEq.match_3" [[(Decidable.isTrue h)] [(Decidable.isFalse h)]]]
    ["Prod.Lex.instDecidableRelOfDecidableEq.match_5" [[(Prod.mk a b) (Prod.mk c d)]]]
    ["Prod.lex.match_1" [[(Prod.mk a b)]]]])

(defn- pattern-from-source [ctx type form]
  (if (integer? form)
    [(b/val-pattern (u/app (u/const' "OfNat.ofNat" [lvl/zero]) [nat (e/lit-nat form) (e/app (u/const' "instOfNatNat" []) (e/lit-nat form))])) []]
    (let [ctor-name (if (seq? form) (first form) form)
          ci (when (symbol? ctor-name) (env/lookup (:env @ctx) (name/from-string (str ctor-name))))]
      (if (and ci (.isCtor ci))
        (let [[f args] (e/get-app-fn-args (u/whnf ctx type))
              us (e/const-levels f) params (subvec args 0 (.numParams ci))
              head (u/app (e/const' (.name ci) us) params)]
          (loop [ct (u/infer-type ctx head) fs [] ds [] forms (seq (when (seq? form) (rest form)))]
            (if-let [form (first forms)]
              (let [ct (u/whnf ctx ct)
                    [p more] (pattern-from-source ctx (e/forall-type ct) form)]
                (recur (e/instantiate1 (e/forall-body ct) (b/pattern-to-expr p))
                       (conj fs p) (into ds more) (next forms)))
              [(b/ctor (.name ci) us params fs) ds])))
        (let [x (u/local-decl ctx (str form) type)] [(b/var-pattern (e/fvar-id x)) [(u/decl ctx x)]])))))

(defn- lhs-from-source [ctx match-type forms]
  (loop [type match-type forms (seq forms) pats [] ds []]
    (if-let [form (first forms)]
      (let [type (u/whnf ctx type)
            [p more] (pattern-from-source ctx (e/forall-type type) form)]
        (recur (e/instantiate1 (e/forall-body type) (b/pattern-to-expr p))
               (next forms) (conj pats p) (into ds more)))
      (b/alt-lhs nil ds pats))))

(defn- replace-motive-sort [type result]
  (if (e/forall? type)
    (e/forall' (e/forall-name type) (e/forall-type type)
               (replace-motive-sort (e/forall-body type) result) (e/forall-info type))
    result))

(defn- alpha-rename [x]
  (let [go alpha-rename]
    (case (e/tag x)
      :lam (e/lam "_" (go (e/lam-type x)) (go (e/lam-body x)) (e/lam-info x))
      :forall (e/forall' "_" (go (e/forall-type x)) (go (e/forall-body x)) (e/forall-info x))
      :app (e/app (go (e/app-fn x)) (go (e/app-arg x)))
      :let (e/let' "_" (go (e/let-type x)) (go (e/let-value x)) (go (e/let-body x)))
      :mdata (e/mdata (e/mdata-data x) (go (e/mdata-expr x)))
      :proj (e/proj (e/proj-type-name x) (e/proj-idx x) (go (e/proj-struct x)))
      x)))

(deftest generated-init-matchers-agree-with-lean-exports
  (doseq [[n rows] init-patterns]
    (testing n
      (let [oracle-env (if (env/lookup @environment (name/from-string n)) @environment @extra-oracle)
            ctx (c/context oracle-env)
            oracle (env/lookup! oracle-env (name/from-string n))
            info (or (imported/matcher-info oracle-env n)
                     (throw (ex-info "Matcher oracle metadata missing" {:matcher n})))
            ;; Use only the discriminant telescope and closure parameters from the
            ;; oracle. Patterns above are source restatements; neither the exported
            ;; alternatives nor the value are used to construct the matcher.
            [_ rest-type] (u/forall-telescope ctx (.type oracle) (:num-params info))
            match-type (replace-motive-sort (e/forall-type rest-type)
                                            (if (some? (:u-elim-pos info)) nat (u/const' "True" [])))
            lhss (mapv #(lhs-from-source ctx match-type %) rows)
            result (m/mk-matcher ctx {:matcher-name (str "Fresh." n) :match-type match-type
                                      :discr-infos (mapv mi/discr-info (:discrs info)) :lhss lhss})
            fresh (env/lookup! (:env result) (name/from-string (str "Fresh." n)))
            levels (zipmap (.levelParams fresh) (map lvl/param (.levelParams oracle)))
            differences (vec (for [[label actual expected] [[:type (.type fresh) (.type oracle)]
                                                            [:value (.value fresh) (.value oracle)]]
                                   :let [actual (e/instantiate-level-params actual levels)]
                                   :when (not= (alpha-rename actual) (alpha-rename expected))] label))]
        (is (empty? differences) (str n " structural differences after alpha renaming: " differences))
        (when (seq differences)
          (println "Fresh type:" (e/->string (.type fresh)))
          (println "Lean type:" (e/->string (.type oracle))))
        (is (= info (:info result)) (str n " MatcherInfo"))
        (is (= (count (.levelParams oracle)) (count (.levelParams fresh))) n)
        (doseq [[label actual expected] [[:type (.type fresh) (.type oracle)] [:value (.value fresh) (.value oracle)]]]
          (let [actual (e/instantiate-level-params actual levels)]
            (is (tc/is-def-eq (tc/mk-tc-state (:env result)) actual expected) (str n " " label))))))))
