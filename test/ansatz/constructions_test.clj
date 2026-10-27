(ns ansatz.constructions-test
  "Constructions compared with Lean v4.33.1 exports, plus frontend admission.
   Oracle: test/lean/constructions.lean; regenerate the oracle with test/lean/export_constructions.sh."
  (:require [clojure.test :refer [deftest is testing]]
            [clojure.string :as str]
            [ansatz.core :as a]
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
            [ansatz.meta.constructions.no-confusion :as nc])
  (:import [java.util.zip GZIPInputStream]))

(def oracle
  (delay
    (with-open [in (GZIPInputStream. (java.io.FileInputStream. "test-data/kernel-reference/constructions.ndjson.gz"))]
      (let [parsed (parser/parse-ndjson-string (slurp in))]
        (try (:env (replay/replay (:decls parsed)))
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
          (doseq [ci auxiliaries]
            (let [expected (str (.name ci)) actual (str/replace expected "T10Reference." "T10Generated.")]
              (compare-decl out actual expected #(str/replace % "T10Generated." "T10Reference."))))))
      (finally (reset! a/ansatz-env saved)))))
