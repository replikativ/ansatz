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
            [ansatz.meta.constructions.util :as u]
            [ansatz.meta.constructions.ctor-idx :as ctor-idx])
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

;; ---------------------------------------------------------------------------
;; Enum noConfusion against both preludes (test/lean-parity/dsl/enum_no_confusion.lean)
;; ---------------------------------------------------------------------------

(defn- with-lean-4-36-enum-helpers
  "Add Lean v4.36.0's Init/Core.lean `noConfusionTypeEnum` / `noConfusionEnum` (two universe
   levels, tag `f : α → Nat`, no codomain or DecidableEq dictionary) to an environment
   that has neither (the bundled Init export omits both)."
  [env]
  (let [ctx (u/context env)
        un (name/from-string "u") wn (name/from-string "w")
        U (lvl/param un) W (lvl/param wn)
        nat (u/const' "Nat" []) bool (u/const' "Bool" [])
        ff (u/const' "Bool.false" []) tt (u/const' "Bool.true" [])
        a (u/local-decl ctx "α" (e/sort' U) :implicit)
        f (u/local-decl ctx "f" (u/mk-arrow ctx a nat))
        p (u/local-decl ctx "P" (e/sort' W))
        x (u/local-decl ctx "x" a) y (u/local-decl ctx "y" a)
        beq (u/app (u/const' "Nat.beq" []) [(e/app f x) (e/app f y)])
        cases (fn [motive t fls tru]
                (u/app (u/const' "Bool.casesOn" [(u/get-level ctx (e/app motive tt))]) [motive t fls tru]))
        sort-w (e/lam (name/from-string "b") bool (e/sort' W) :default)
        ;; ((f x).beq (f y)).casesOn P (P → P)
        env (u/add-definition env ctx "noConfusionTypeEnum" [un wn] [a f p x y] (e/sort' W)
                              (cases sort-w beq p (u/mk-arrow ctx p p)))
        _ (u/set-env! ctx env)
        _ (u/implicit! ctx [p x y])
        h (u/local-decl ctx "h" (u/mk-eq ctx x y))
        b (u/local-decl ctx "b" bool)
        motive (u/mk-lambda-fvars ctx [b] (u/mk-arrow ctx (u/mk-eq ctx beq b)
                                                      (cases sort-w b p (u/mk-arrow ctx p p))))
        h1 (u/local-decl ctx "h'" (u/mk-eq ctx beq ff))
        fls (u/mk-lambda-fvars
             ctx [h1]
             (u/app (u/const' "False.elim" [W])
                    [(cases sort-w ff p (u/mk-arrow ctx p p))
                     (u/app (u/const' "Nat.ne_of_beq_eq_false" [])
                            [(e/app f x) (e/app f y) h1
                             (u/app (u/const' "congrArg" [U (lvl/succ lvl/zero)]) [a nat x y f h])])]))
        h2 (u/local-decl ctx "h'" (u/mk-eq ctx beq tt))
        q (u/local-decl ctx "a" p)]
    (u/add-definition env ctx "noConfusionEnum" [un wn] [a f p x y h]
                      (u/app (u/const' "noConfusionTypeEnum" [U W]) [a f p x y])
                      (e/app (cases motive beq fls (u/mk-lambda-fvars ctx [h2 q] q))
                             (u/mk-eq-refl ctx beq)))))

(defn- sort-poly-enum
  "`inductive n : Sort u` with nullary constructors, admitted at the kernel level as Lean 4.36
   does (the DSL's parameterless form defaults to Type): with two or more constructors it
   eliminates only into Prop, with one into any Sort. Then the DSL's construction sequence."
  [base n ctors]
  (let [un (name/from-string "u") U (lvl/param un)
        nm (name/from-string n) T (e/const' nm [U])
        cn #(name/from-string (str n "." %))
        ind (env/mk-induct nm [un] (e/sort' U) :ctors (mapv cn ctors))
        cis (vec (map-indexed (fn [i c] (env/mk-ctor (cn c) [un] T nm i 0 0)) ctors))
        large? (= 1 (count ctors))
        vn (name/from-string "u_1")
        rlps (if large? [vn un] [un])
        k (count ctors)
        ;; ∀ {motive : T → Sort}, motive c₀ → … → ∀ t, motive t
        body (e/forall' (name/from-string "t") T (e/app (e/bvar (inc k)) (e/bvar 0)) :default)
        body (reduce (fn [b i] (e/forall' (name/from-string (nth ctors i))
                                          (e/app (e/bvar i) (e/const' (cn (nth ctors i)) [U])) b :default))
                     body (reverse (range k)))
        rty (e/forall' (name/from-string "motive")
                       (e/arrow T (e/sort' (if large? (lvl/param vn) lvl/zero))) body :implicit)
        rn (name/from-string (str n ".rec"))
        rec #(env/mk-recursor rn rlps rty :all [nm] :num-motives 1 :num-minors k :rules %)
        rules (vec (TypeChecker/generateExpectedRecursorRules
                    base (env/mk-inductive-bundle [un] 0 false [ind] cis [(rec [])]) 0 1000000))
        env (env/check-inductive-bundle base (env/mk-inductive-bundle [un] 0 false [ind] cis [(rec rules)]))
        env (rec/mk-rec-on env n)
        env (cases/mk-cases-on env n)
        env (ctor-idx/mk-ctor-idx env n)]
    (nc/mk-no-confusion env n)))

(defn- binder-infos [t]
  (loop [t t acc []] (if (e/forall? t) (recur (e/forall-body t) (conj acc (e/forall-info t))) acc)))

(defn- enum-no-confusion-body
  "The helper application under `T.noConfusion`'s four binders `{P} {x y} h`."
  [env n]
  (let [v (.value (lookup env (str n ".noConfusion")))]
    (-> v e/lam-body e/lam-body e/lam-body e/lam-body)))

(deftest enum-no-confusion-follows-the-helper-telescope
  (let [saved @a/ansatz-env
        color [['red []] ['green []] ['blue []]]]
    (try
      (binding [a/*verbose* false]
        (testing "Lean 4.36 prelude: two levels, `noConfusionEnum T T.ctorIdx P x y h`"
          (let [base (with-lean-4-36-enum-helpers @test-env/bundled-init-env)
                out (ind/define-inductive base "T36.Color" [] color)
                [hd args] (e/get-app-fn-args (enum-no-confusion-body out "T36.Color"))
                v (lvl/param (first (.levelParams (lookup out "T36.Color.noConfusion"))))
                st (tc/mk-tc-state out)
                c #(e/const' (name/from-string (str "T36.Color." %)) [])
                nct (fn [p a b] (e/app* (e/const' (name/from-string "T36.Color.noConfusionType") [lvl/zero])
                                        p (c a) (c b)))
                p (e/const' (name/from-string "True") [])]
            (is (= "noConfusionEnum" (str (e/const-name hd))))
            (is (= [(lvl/succ lvl/zero) v] (vec (e/const-levels hd))))
            (is (= 6 (count args)) "α f P x y h: no codomain or dictionary")
            (is (= "T36.Color.ctorIdx" (str (e/const-name (nth args 1)))))
            (let [nct-ci (lookup out "T36.Color.noConfusionType")
                  [th targs] (e/get-app-fn-args (-> (.value nct-ci) e/lam-body e/lam-body e/lam-body))]
              (is (= "noConfusionTypeEnum" (str (e/const-name th))))
              (is (= [(lvl/succ lvl/zero) (lvl/param (first (.levelParams nct-ci)))] (vec (e/const-levels th))))
              (is (= ["T36.Color" "T36.Color.ctorIdx"] (mapv #(str (e/const-name %)) (subvec targs 0 2))))
              (is (= [(e/bvar 2) (e/bvar 1) (e/bvar 0)] (subvec targs 2)) "P x y")
              (is (= [:default :default :default] (binder-infos (.type nct-ci))))
              (is (= [:implicit :implicit :implicit :default]
                     (binder-infos (.type (lookup out "T36.Color.noConfusion"))))))
            (is (tc/is-def-eq st (nct p "red" "blue") p) "distinct constructors: P")
            (is (tc/is-def-eq st (nct p "green" "green") (e/arrow p p)) "equal constructors: P → P")
            ;; red ≠ green := fun h => Color.noConfusion h
            (let [eq (e/app* (e/const' (name/from-string "Eq") [(lvl/succ lvl/zero)])
                             (e/const' (name/from-string "T36.Color") []) (c "red") (c "green"))
                  fls (e/const' (name/from-string "False") [])]
              (is (env/verifies? out (e/arrow eq fls)
                                 (e/lam (name/from-string "h") eq
                                        (e/app* (e/const' (name/from-string "T36.Color.noConfusion") [lvl/zero])
                                                fls (c "red") (c "green") (e/bvar 0))
                                        :default))))
            (testing "one constructor: `P → P` and the identity"
              (let [out (ind/define-inductive base "T36.Solo" [] [['only []]])
                    body (enum-no-confusion-body out "T36.Solo")]
                (is (and (e/lam? body) (= (e/bvar 0) (e/lam-body body))))))))
        (testing "sort-polymorphic enums (Lean tests/elab/issue14904.lean)"
          (let [base (with-lean-4-36-enum-helpers @test-env/bundled-init-env)
                b2 (sort-poly-enum base "T36.Bool2" ["true" "false"])
                u2 (sort-poly-enum base "T36.Unit2" ["unit"])]
            (doseq [s ["ctorIdx" "noConfusionType" "noConfusion"]]
              (is (nil? (lookup b2 (str "T36.Bool2." s))) (str "Bool2 eliminates only into Prop: no " s))
              (is (some? (lookup u2 (str "T36.Unit2." s))) (str "Unit2." s)))
            (is (= (e/bvar 0) (e/lam-body (enum-no-confusion-body u2 "T36.Unit2"))))))
        (testing "Lean 4.33.1 prelude: three levels, codomain Nat and instDecidableEqNat"
          (let [out (ind/define-inductive @oracle "T33.Color" [] color)
                [hd args] (e/get-app-fn-args (enum-no-confusion-body out "T33.Color"))]
            (is (= "noConfusionEnum" (str (e/const-name hd))))
            (is (= 3 (count (e/const-levels hd))))
            (is (= ["Nat" "instDecidableEqNat" "T33.Color.ctorIdx"]
                   (mapv #(str (e/const-name %)) (subvec args 1 4)))))))
      (finally (reset! a/ansatz-env saved)))))
