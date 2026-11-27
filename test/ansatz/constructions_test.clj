(ns ansatz.constructions-test
  "Constructions compared with Lean v4.33.1 exports, plus frontend admission.
   Oracle: test/lean/constructions.lean; regenerate the oracle with test/lean/export_constructions.sh."
  (:require [clojure.test :refer [deftest is testing]]
            [clojure.string :as str]
            [clojure.walk :as walk]
            [ansatz.core :as a]
            [ansatz.test-env :as test-env]
            [ansatz.inductive :as ind]
            [ansatz.export.parser :as parser]
            [ansatz.export.replay :as replay]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.tc :as tc]
            [ansatz.meta.constructions.cases-on :as cases]
            [ansatz.meta.constructions.rec-on :as rec]
            [ansatz.meta.constructions.brec-on :as brec]
            [ansatz.meta.constructions.no-confusion :as nc]
            [ansatz.kernel.cases-on :as kernel-cases])
  (:import [java.util.zip GZIPInputStream]
           [ansatz.kernel TypeChecker]))

(def oracle
  (delay
    (with-open [in (GZIPInputStream. (java.io.FileInputStream. "test-data/kernel-reference/constructions.ndjson.gz"))]
      (let [parsed (parser/parse-ndjson-string (slurp in))]
        (try (test-env/with-instance-registry (:env (replay/replay (:decls parsed))))
             (finally (.close ^java.io.Closeable (:exprs parsed))))))))

(defn- lookup [env n] (env/lookup env (name/from-string n)))
(defn- rename-expr [x rename]
  (letfn [(go [x]
              (case (e/tag x)
                :const (e/const' (name/from-string (rename (str (e/const-name x)))) (e/const-levels x))
                :app (e/app (go (e/app-fn x)) (go (e/app-arg x)))
                :lam (e/lam (e/lam-name x) (go (e/lam-type x)) (go (e/lam-body x)) (e/lam-info x))
                :forall (e/forall' (e/forall-name x) (go (e/forall-type x)) (go (e/forall-body x)) (e/forall-info x))
                :let (e/let' (e/let-name x) (go (e/let-type x)) (go (e/let-value x)) (go (e/let-body x)))
                :proj (e/proj (name/from-string (rename (str (e/proj-type-name x)))) (e/proj-idx x) (go (e/proj-struct x)))
                :mdata (go (e/mdata-expr x))
                x))]
    (go x)))

(defn- compare-decl [out actual expected rename]
  (let [a (lookup out actual) b (lookup @oracle expected)]
    (is (some? a) (str "generated " actual))
    (is (some? b) (str "Lean oracle " expected))
    (when (and a b)
      (is (= (count (.levelParams a)) (count (.levelParams b))) actual)
      (let [levels (zipmap (.levelParams a) (map lvl/param (.levelParams b)))
            st (tc/mk-tc-state out)]
        (doseq [[label x y] [[:type (.type a) (.type b)] [:value (.value a) (.value b)]]]
          (let [x (rename-expr (e/instantiate-level-params x levels) rename)
                exact? (= x y)]
            (when-not exact? (println "Constructions defeq comparison:" expected label))
            (is (or exact? (tc/is-def-eq st x y)) (str expected " " label))))))))

(deftest init-and-nested-recursor-auxiliaries-match-lean
  (doseq [n ["Nat" "List" "Option" "Prod" "Bool" "Fin" "Or" "Eq" "T10Reference.Vec" "T10Reference.Rose"
             "T10Reference.Inf" "T10Reference.Tree" "T10Reference.Forest"]]
    (testing n
      (doseq [[suffix f] [["casesOn" cases/mk-cases-on] ["recOn" rec/mk-rec-on]]]
        (let [target (str "T10Fresh." n "." suffix)
              out (f @oracle n target)]
          (compare-decl out target (str n "." suffix) #(str/replace % "T10Fresh." "")))))))

(deftest below-and-brec-on-match-lean
  (doseq [n ["Nat" "List" "T10Reference.Rec" "T10Reference.Vec" "T10Reference.Rose"
             "T10Reference.Inf" "T10Reference.Tree" "T10Reference.Forest"]]
    (let [info (lookup @oracle n)
          recs (cons [n (str n ".rec") (str n ".below") (str n ".brecOn")]
                     (when (= (str (first (.all info))) n)
                       (for [i (range (.numNested info))]
                         [n (str n ".rec_" (inc i)) (str n ".below_" (inc i)) (str n ".brecOn_" (inc i))])))]
      (doseq [[_ rn bn brn] recs]
        (let [below-target (str "T10Fresh." bn)
              brec-target (str "T10Fresh." brn)
              out (brec/mk-below-from-rec @oracle rn (.numParams info) below-target)
              out (brec/mk-brec-on-from-rec out rn (.numParams info) (vec (.all info)) brec-target)]
          (compare-decl out below-target bn #(str/replace % "T10Fresh." ""))
          (doseq [s [".go" "" ".eq"]]
            (compare-decl out (str brec-target s) (str brn s) #(str/replace % "T10Fresh." ""))))))))

(deftest no-confusion-matches-lean
  (doseq [n ["Nat" "List" "Option" "Prod" "Bool" "Fin" "T10Reference.Vec" "T10Reference.Rose" "T10Reference.Assoc"]]
    (let [nct (str "T10Fresh." n ".noConfusionType")
          nc-name (str "T10Fresh." n ".noConfusion")
          out (nc/mk-no-confusion-type @oracle n nct)
          out (nc/mk-no-confusion-core-imp out n nc-name nct)]
      (doseq [s ["noConfusionType" "noConfusion"]]
        (compare-decl out (str "T10Fresh." n "." s) (str n "." s) #(str/replace % "T10Fresh." ""))))))

(def user-specs
  [["Empty" [] [] []]
   ["Unit" [] [['unit []]] []]
   ["Enum" [] [['a []] ['b []] ['c []]] []]
   ["Rec" [] [['z []] ['s '[n T10Generated.Rec]]] []]
   ["Vec" '[a Type] [['nil [] [0]] ['cons '[n Nat x a xs (T10Generated.Vec a n)] ['(Nat.succ n)]]] [:indices '[n Nat]]]
   ["Spin" [] [['pure '[v Nat]] ['await '[id Nat k (=> Nat T10Generated.Spin)]]
               ['yield '[v Nat k T10Generated.Spin]]] []]
   ["Branch" '[A Type] [['leaf '[n Nat] ['n]]
                        ['node '[n Nat k (forall [m Nat j (Fin (Nat.succ m))] (T10Generated.Branch A m))] ['n]]]
    [:indices '[n Nat]]]
   ["Inf" [] [['node '[children (=> Nat T10Generated.Inf)]]] []]
   ["Rose" [] [['node '[children (List T10Generated.Rose)]]] []]
   ["Assoc" '[S Type] [['mk '[add (=> S S S) assoc (forall [a S b S c S] (= S (add (add a b) c) (add a (add b c))))]]] []]
   ["Disj" '[p Prop q Prop] [['left '[h p]] ['right '[h q]]] [:in 'Prop]]])

(deftest frontend-generates-all-applicable-constructions
  (let [saved @a/ansatz-env]
    (try
      (doseq [[n ps cs opts] user-specs]
        (let [n (str "T10Generated." n)
              ref (str/replace n "T10Generated." "T10Reference.")
              out (apply ind/define-inductive @oracle n ps cs opts)
              ;; Compare every exported auxiliary, including ctor helpers and nested auxiliaries.
              auxiliaries (filter #(and (str/starts-with? (str (.name %)) (str ref "."))
                                        (or (.isDef %) (.isThm %))) (env/all-constants @oracle))]
          (is (seq auxiliaries) ref)
          (let [actual (lookup out (str n ".rec"))
                expected (lookup @oracle (str ref ".rec"))
                levels (zipmap (.levelParams actual) (map lvl/param (.levelParams expected)))
                type (rename-expr (e/instantiate-level-params (.type actual) levels)
                                  #(str/replace % "T10Generated." "T10Reference."))]
            (is (tc/is-def-eq (tc/mk-tc-state @oracle) type (.type expected))
                (str ref " recursor type")))
          (doseq [ci auxiliaries]
            (let [expected (str (.name ci)) actual (str/replace expected "T10Reference." "T10Generated.")]
              (compare-decl out actual expected #(str/replace % "T10Generated." "T10Reference."))))))
      (finally (reset! a/ansatz-env saved)))))

(deftest functional-recursive-fields-compute-in-kernel-and-runtime
  (let [saved @a/ansatz-env]
    (try
      (reset! a/ansatz-env @oracle)
      (binding [*ns* (the-ns 'ansatz.constructions-test) a/*verbose* false]
        (run! #(eval (walk/postwalk-replace {'spin-rec (symbol "@Spin.rec.{1}")
                                             'nat-rec (symbol "@Nat.rec.{1}")
                                             'spin-cases (symbol "@Spin.casesOn.{1}")} %))
              '[(a/inductive Spin []
                             (pure [v Nat]) (await [id Nat] [k (=> Nat Spin)]) (yield [v Nat] [k Spin]))
                (a/defn spin-bind [s :- Spin, f :- (=> Nat Spin)] Spin
                  (spin-rec (fn [_ :- Spin] Spin) f
                            (fn [id :- Nat, k :- (=> Nat Spin), ih :- (=> Nat Spin)]
                              (Spin.await id (fn [x :- Nat] (ih x))))
                            (fn [v :- Nat, k :- Spin, ih :- Spin] (Spin.yield v ih)) s))
                (a/defn spin-run [fuel :- Nat, s :- Spin] Nat
                  (nat-rec (fn [_ :- Nat] (=> Spin Nat))
                           (fn [_ :- Spin] 0)
                           (fn [n :- Nat, ih :- (=> Spin Nat)]
                             (fn [s :- Spin]
                               (spin-cases (fn [_ :- Spin] Nat) s
                                           (fn [v :- Nat] v)
                                           (fn [id :- Nat, k :- (=> Nat Spin)] (ih (k id)))
                                           (fn [v :- Nat, k :- Spin] (ih k))))) fuel s))
                (a/theorem spin-bind-pure [v :- Nat, f :- (=> Nat Spin)]
                           (= Spin (spin-bind (Spin.pure v) f) (f v)) (rfl))
                (a/defn spin-program [n :- Nat] Nat
                  (spin-run 4
                            (spin-bind (Spin.await n (fn [x :- Nat] (Spin.yield 9 (Spin.pure x))))
                                       (fn [x :- Nat] (Spin.pure (+ x 2))))))
                (a/theorem spin-program-kernel [n :- Nat]
                           (= Nat (spin-program n) (+ n 2)) (rfl))
                (a/defn spin-fuel-program [fuel :- Nat] Nat
                  (spin-run fuel (Spin.await 3 (fn [x :- Nat] (Spin.yield 9 (Spin.pure (+ x 2)))))))
                (a/theorem spin-fuel-exhausted [] (= Nat (spin-fuel-program 2) 0) (rfl))
                (a/theorem spin-fuel-sufficient [] (= Nat (spin-fuel-program 3) 5) (rfl))])
        (doseq [suffix ["casesOn" "recOn" "below" "brecOn" "noConfusion"]]
          (is (some? (lookup (a/env) (str "Spin." suffix)))))
        (doseq [n (range 8)]
          (is (= (+ n 2) ((deref (ns-resolve *ns* 'spin-program)) n))))
        (is (= [0 0 0 5 5]
               (mapv (deref (ns-resolve *ns* 'spin-fuel-program)) (range 5)))))
      (finally (reset! a/ansatz-env saved)))))

;; Lean 4.36 mkCasesOnViaProjs? / mkRecOnViaCasesOn? (test/lean-parity/dsl/cases_on_projs.lean)
(deftest prop-structure-cases-on-computes-on-opaque-proofs
  (let [saved @a/ansatz-env]
    (try
      (binding [a/*verbose* false *ns* (the-ns 'ansatz.constructions-test)]
        (let [out (ind/define-inductive @test-env/bundled-init-env "PBoth" '[p Prop q Prop]
                    [['mk '[left p right q]]] :in 'Prop)
              cases (lookup out "PBoth.casesOn")
              body (loop [v (.value cases)] (if (e/lam? v) (recur (e/lam-body v)) v))
              [h args] (e/get-app-fn-args body)]
          (testing "casesOn applies the minor to the projections of the major"
            (is (e/bvar? h))
            (is (= [(e/proj (name/from-string "PBoth") 0 (e/bvar 1)) (e/proj (name/from-string "PBoth") 1 (e/bvar 1))]
                   (vec args))))
          (testing "recOn is casesOn"
            (is (= (e/const' (name/from-string "PBoth.casesOn") (mapv lvl/param (.levelParams cases)))
                   (.value (lookup out "PBoth.recOn")))))
          (testing "both compute on an opaque proof; the recursor permutation does not"
            (reset! a/ansatz-env out)
            (doseq [elim ["casesOn" "recOn"]]
              (eval (list 'ansatz.core/theorem (symbol (str "pboth-" elim "-computes")) '[p :- Prop, q :- Prop, h :- (PBoth p q)]
                          (list '= 'Nat (list (symbol (str "@PBoth." elim ".{1}")) 'p 'q '(fn [_ :- (PBoth p q)] Nat) 'h
                                              '(fn [a :- p, b :- q] 7)) 7)
                          '(rfl)))
              (is (some? (lookup (a/env) (str "pboth-" elim "-computes")))))
            ;; the recursor permutation elaborates and type-checks, but is not 7 on a variable
            (let [rec-app (ansatz.surface.elaborate/elaborate
                           (a/env) (list 'fn '[p :- Prop, q :- Prop, h :- (PBoth p q)]
                                         (list (symbol "@PBoth.rec.{1}") 'p 'q '(fn [_ :- (PBoth p q)] Nat)
                                               '(fn [a :- p, b :- q] 7) 'h)))
                  st (tc/mk-tc-state (a/env))
                  ty (tc/infer-type st rec-app)]
              (is (some? ty))
              (is (not (tc/is-def-eq st rec-app
                                     (ansatz.surface.elaborate/elaborate
                                      (a/env) '(fn [p :- Prop, q :- Prop, h :- (PBoth p q)] 7)))))))
          (testing "a dependent second proof field"
            (let [out (ind/define-inductive (a/env) "PDep" '[p Prop q (=> p Prop)] [['mk '[hp p hq (q hp)]]] :in 'Prop)]
              (reset! a/ansatz-env out)
              (eval (list 'ansatz.core/theorem 'pdep-cases-computes '[p :- Prop, q :- (=> p Prop), h :- (PDep p q)]
                          (list '= 'Nat (list (symbol "@PDep.casesOn.{1}") 'p 'q '(fn [_ :- (PDep p q)] Nat) 'h
                                              '(fn [a :- p, b :- (q a)] 7)) 7)
                          '(rfl)))
              (is (some? (lookup (a/env) "pdep-cases-computes")))))
          (testing "an Exists-like proposition (Prop elimination only) keeps the recursor"
            (let [out (ind/define-inductive @test-env/bundled-init-env "PEx" '[α Type p (=> α Prop)]
                        [['intro '[w α h (p w)]]] :in 'Prop)
                  body (loop [v (.value (lookup out "PEx.casesOn"))] (if (e/lam? v) (recur (e/lam-body v)) v))]
              (is (= "PEx.rec" (str (e/const-name (e/get-app-fn body)))))))))
      (finally (reset! a/ansatz-env saved)))))

(defn- alias-prop-structure
  "`AliasBoth (p q : Prop) : header` with `mk (hp : p) (hq : q)`, admitted at the kernel level with
   Name binders, as an import would carry it; `header` a reducible alias chain ending in Prop.
   With `:unchecked` the declarations are added without checking, `:rec-type`/`:rec-levels`
   overriding the recursor's."
  [env header & {:keys [unchecked rec-type rec-levels]}]
  (let [N name/from-string
        prop (e/sort' lvl/zero)
        nm (N "AliasBoth") T (fn [p q] (e/app* (e/const' nm []) p q))
        ind (env/mk-induct nm [] (e/forall' (N "p") prop (e/forall' (N "q") prop (e/const' (N header) []) :default) :default)
                           :num-params 2 :ctors [(N "AliasBoth.mk")])
        mk-app (fn [p q hp hq] (e/app* (e/const' (N "AliasBoth.mk") []) p q hp hq))
        cty (e/forall' (N "p") prop
                       (e/forall' (N "q") prop
                                  (e/forall' (N "hp") (e/bvar 1)
                                             (e/forall' (N "hq") (e/bvar 1) (T (e/bvar 3) (e/bvar 2)) :default) :default)
                                  :implicit) :implicit)
        ctor (env/mk-ctor (N "AliasBoth.mk") [] cty nm 0 2 2)
        un (N "u")
        rty (or rec-type
                (e/forall' (N "p") prop
                           (e/forall' (N "q") prop
                                      (e/forall' (N "motive") (e/forall' (N "t") (T (e/bvar 1) (e/bvar 0)) (e/sort' (lvl/param un)) :default)
                                                 (e/forall' (N "mk") (e/forall' (N "hp") (e/bvar 2)
                                                                                (e/forall' (N "hq") (e/bvar 2)
                                                                                           (e/app (e/bvar 2) (mk-app (e/bvar 4) (e/bvar 3) (e/bvar 1) (e/bvar 0)))
                                                                                           :default) :default)
                                                            (e/forall' (N "t") (T (e/bvar 3) (e/bvar 2)) (e/app (e/bvar 2) (e/bvar 0)) :default)
                                                            :default) :implicit) :implicit) :implicit))
        rn (N "AliasBoth.rec")
        rec #(env/mk-recursor rn (or rec-levels [un]) rty :all [nm] :num-params 2 :num-motives 1 :num-minors 1 :rules %)]
    (if unchecked
      (reduce env/add-constant env [ind ctor (rec [])])
      (let [rules (vec (TypeChecker/generateExpectedRecursorRules env (env/mk-inductive-bundle [] 2 false [ind] [ctor] [(rec [])]) 0 1000000))]
        (env/check-inductive-bundle env (env/mk-inductive-bundle [] 2 false [ind] [ctor] [(rec rules)]))))))

(defn- with-alias-chain
  "`env` with reducible `PropAlias0 := Prop`, `PropAliasᵢ := PropAliasᵢ₋₁` up to `n`."
  [env n]
  (reduce (fn [env i]
            (env/check-constant env (env/mk-def (name/from-string (str "PropAlias" i)) [] (e/sort' (lvl/succ lvl/zero))
                                                (if (zero? i) (e/sort' lvl/zero) (e/const' (name/from-string (str "PropAlias" (dec i))) []))
                                                :hints :abbrev)))
          env (range (inc n))))

(deftest pure-cases-on-builder-uses-projections-where-lean-does
  (let [env @test-env/bundled-init-env
        and-cases (kernel-cases/make-declaration env (name/from-string "And"))
        body (loop [v (.value and-cases)] (if (e/lam? v) (recur (e/lam-body v)) v))]
    (is (e/proj? (e/app-arg body)) "And.casesOn: the minor applied to projections")
    (is (tc/is-def-eq (tc/mk-tc-state env) (.type and-cases) (.type (lookup env "And.casesOn"))))
    (is (some? (env/check-constant env (env/mk-def (name/from-string "And.casesOnViaProjs")
                                                   (vec (.levelParams and-cases)) (.type and-cases) (.value and-cases)))))
    (let [ex (kernel-cases/make-declaration env (name/from-string "Exists"))
          body (loop [v (.value ex)] (if (e/lam? v) (recur (e/lam-body v)) v))]
      (is (= "Exists.rec" (str (e/const-name (e/get-app-fn body))))))
    (testing "the projection path honours the shared local limit"
      (is (= :cases-on/local-limit
             (try (kernel-cases/make-declaration env (name/from-string "And") {:max-locals 1}) nil
                  (catch clojure.lang.ExceptionInfo ex (:type (ex-data ex)))))))
    (testing "a header that ends in a reducible alias for Prop is Prop-valued, in both builders"
      (let [out (alias-prop-structure (with-alias-chain env 0) "PropAlias0")
            d (kernel-cases/make-declaration out (name/from-string "AliasBoth"))
            body (loop [v (.value d)] (if (e/lam? v) (recur (e/lam-body v)) v))
            meta-out (cases/mk-cases-on out "AliasBoth" "AliasBoth.casesOnMeta")
            meta-body (loop [v (.value (lookup meta-out "AliasBoth.casesOnMeta"))] (if (e/lam? v) (recur (e/lam-body v)) v))
            rec-out (rec/mk-rec-on out "AliasBoth" "AliasBoth.recOnFallback")
            rec-body (loop [v (.value (lookup rec-out "AliasBoth.recOnFallback"))] (if (e/lam? v) (recur (e/lam-body v)) v))]
        (is (e/proj? (e/app-arg body)))
        (is (some? (env/check-constant out d)))
        (is (e/proj? (e/app-arg meta-body)) "the meta builder too")
        (is (= "AliasBoth.rec" (str (e/const-name (e/get-app-fn rec-body)))) "recOn without casesOn: the recursor")))
    (testing "reducing the header is charged to the work budget"
      (let [out (alias-prop-structure (with-alias-chain env 400) "PropAlias400")]
        (is (some? (kernel-cases/make-declaration out (name/from-string "AliasBoth"))))
        (is (= :cases-on/work-limit
               (try (kernel-cases/make-declaration out (name/from-string "AliasBoth") {:max-work 300}) nil
                    (catch clojure.lang.ExceptionInfo ex (:type (ex-data ex))))))))
    (testing "the projection path validates the recursor it copies from"
      (let [base (with-alias-chain env 0)
            bad-levels (alias-prop-structure base "PropAlias0" :unchecked true
                                             :rec-levels [(name/from-string "u") "not-a-name"])
            open-result (alias-prop-structure base "PropAlias0" :unchecked true
                                              :rec-type (e/forall' (name/from-string "p") (e/sort' lvl/zero) (e/bvar 7) :default))]
        (is (= :cases-on/invalid-recursor
               (try (kernel-cases/make-declaration bad-levels (name/from-string "AliasBoth")) nil
                    (catch clojure.lang.ExceptionInfo ex (:type (ex-data ex))))))
        (is (= :cases-on/open-expression
               (try (kernel-cases/make-declaration open-result (name/from-string "AliasBoth")) nil
                    (catch clojure.lang.ExceptionInfo ex (:type (ex-data ex))))))))))
