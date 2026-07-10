(ns ansatz.datatype-test
  (:require [ansatz.datatype :as dt]
            [clojure.test :refer [deftest is testing]]))

(dt/defdatatype stlc
  {:rules [{:name :lookup-hit
            :head [lookup ?env ?x ?t]
            :body [[conso [?x ?t] ?rest ?env]]}

           {:name :lookup-miss
            :head [lookup ?env ?x ?t]
            :body [[conso [?y ?v] ?rest ?env]
                   [!= ?y ?x]
                   [lookup ?rest ?x ?t]]}

           {:name :var
            :head [!- ?env ?x ?t]
            :body [[symbolo ?x]
                   [lookup ?env ?x ?t]]}

           {:name :int-lit
            :head [!- ?env ?n :int]
            :body [[integero ?n]]}

           {:name :true-lit
            :head [!- ?env true :bool]}

           {:name :false-lit
            :head [!- ?env false :bool]}

           {:name :lam
            :head [!- ?env [:lam ?x ?body] [:-> ?tx ?tbody]]
            :body [[symbolo ?x]
                   [conso [?x ?tx] ?env ?env2]
                   [!- ?env2 ?body ?tbody]]}

           {:name :app
            :head [!- ?env [:app ?rator ?rand] ?t]
            :body [[!- ?env ?rator [:-> ?t-rand ?t]]
                   [!- ?env ?rand ?t-rand]]}

           {:name :if
            :head [!- ?env [:if ?c ?then ?else] ?t]
            :body [[!- ?env ?c :bool]
                   [!- ?env ?then ?t]
                   [!- ?env ?else ?t]]}]})

(dt/defsequentdatatype tiny-stlc
  {:relation t*
   :rules [{:name :int-lit
            :conclusion [:of ?n :int]
            :where [[integero ?n]]}

           {:name :true-lit
            :conclusion [:of true :bool]}

           {:name :false-lit
            :conclusion [:of false :bool]}

           {:name :lam
            :conclusion [:of [:lam ?x ?body] [:-> ?tx ?tbody]]
            :premises [{:assumptions [[:of ?x ?tx]]
                        :conclusion [:of ?body ?tbody]}]}

           {:name :app
            :conclusion [:of [:app ?rator ?rand] ?t]
            :premises [[:of ?rator [:-> ?t-rand ?t]]
                       [:of ?rand ?t-rand]]}

           {:name :if
            :conclusion [:of [:if ?c ?then ?else] ?t]
            :premises [[:of ?c :bool]
                       [:of ?then ?t]
                       [:of ?else ?t]]}]})

(dt/defsequentdatatype left-demo
  {:relation prove
   :rules [{:name :pair-left
            :assumptions [[:pair ?x ?y]]
            :premises [{:assumptions [[:left ?x] [:right ?y]]
                        :conclusion ?goal}]
            :conclusion ?goal}]})

(defn- rule-names [proof]
  (when (and (vector? proof) (= :rule (first proof)))
    (cons (second proof) (mapcat rule-names (dt/derivation-premises proof)))))

(deftest datatype-inferrs-identity-type
  (let [answer (first (dt/solve stlc 1 ['?t] '[!- () [:lam x x] ?t] {:proof? true}))
        ty (get answer '?t)]
    (is (= :-> (first ty)))
    (is (= (second ty) (nth ty 2)))
    (is (= [:lam :var :lookup-hit] (vec (rule-names (:proof answer)))))))

(deftest datatype-checks-application-and-branches
  (testing "identity applied to an integer"
    (is (= [{'?t :int}]
           (dt/solve stlc 1 ['?t] '[!- () [:app [:lam x x] 7] ?t]))))
  (testing "if branches constrain to one type"
    (is (= [{'?t :int}]
           (dt/solve stlc 1 ['?t] '[!- () [:if true 1 2] ?t]))))
  (testing "ill-typed branches fail"
    (is (empty? (dt/solve stlc 1 ['?t] '[!- () [:if true 1 false] ?t])))))

(deftest datatype-context-lookup-is-relational
  (is (= [{'?t :bool}]
         (dt/solve stlc 1 ['?t] '[lookup ([x :bool] [x :int]) x ?t])))
  (is (= [{'?x 'y}]
         (dt/solve stlc 1 ['?x] '[lookup ([x :int] [y :bool]) ?x :bool]))))

(deftest datatype-can-run-backward-to-synthesize-a-term-shape
  (let [answer (first (dt/solve stlc 1 ['?expr] '[!- () ?expr [:-> ?a ?a]]))
        expr (get answer '?expr)]
    (is (= :lam (first expr)))
    (is (seq (:constraints answer)))))

(deftest sequent-datatype-uses-context-assumptions
  (let [answer (first (dt/solve tiny-stlc 1 ['?t]
                                '[t* () [:of [:lam x x] ?t]]
                                {:proof? true}))
        ty (get answer '?t)]
    (is (= :-> (first ty)))
    (is (= (second ty) (nth ty 2)))
    (is (= [:lam :by-assumption] (vec (rule-names (:proof answer))))))
  (is (= [{'?t :int}]
         (dt/solve tiny-stlc 1 ['?t]
                   '[t* () [:of [:app [:lam x x] 7] ?t]]))))

(deftest sequent-datatype-can-use-left-assumptions
  (let [answer (first (dt/solve left-demo 1 []
                                '[prove ([:pair a b]) [:left a]]
                                {:proof? true}))]
    (is answer)
    (is (= [:pair-left :by-assumption] (vec (rule-names (:proof answer))))))
  (is (empty? (dt/solve left-demo 1 []
                        '[prove ([:pair a b]) [:left c]]))))
