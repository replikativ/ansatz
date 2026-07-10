(ns ansatz.datatype-cert-test
  (:require [ansatz.core :as a]
            [ansatz.datatype :as dt]
            [ansatz.datatype.cert :as dt-cert]
            [ansatz.datatype-test :as dt-test]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [clojure.test :refer [deftest is testing]]))

(defn- call
  [s & args]
  (apply list (symbol s) args))

(defn- install-stlc-kernel! []
  (binding [a/*verbose* false]
    (a/load-init!)
    (when-not (env/lookup (a/env) (name/from-string "DTStlcHasType"))
      (a/inductive DTStlcTy []
        (tint)
        (tbool)
        (tarr [dom DTStlcTy] [cod DTStlcTy]))

      (a/inductive DTStlcExpr []
        (evar [x Nat])
        (eint [n Nat])
        (etrue)
        (efalse)
        (elam [x Nat] [body DTStlcExpr])
        (eapp [rator DTStlcExpr] [rand DTStlcExpr])
        (eif [c DTStlcExpr] [br-then DTStlcExpr] [br-else DTStlcExpr]))

      (a/inductive DTStlcEnv []
        (empty)
        (extend [rest DTStlcEnv] [x Nat] [t DTStlcTy]))

      (a/inductive DTStlcLookup [] :in Prop
        :indices [env DTStlcEnv x Nat ty DTStlcTy]
        (hit [rest DTStlcEnv] [x Nat] [t DTStlcTy]
          :where [(DTStlcEnv.extend rest x t) x t])
        (miss [rest DTStlcEnv] [y Nat] [v DTStlcTy]
              [x Nat] [t DTStlcTy]
              [hne (Not (Eq y x))]
              [tail (DTStlcLookup rest x t)]
          :where [(DTStlcEnv.extend rest y v) x t]))

      (a/inductive DTStlcHasType [] :in Prop
        :indices [env DTStlcEnv expr DTStlcExpr ty DTStlcTy]
        (intLit [env DTStlcEnv] [n Nat]
          :where [env (DTStlcExpr.eint n) (DTStlcTy.tint)])
        (trueLit [env DTStlcEnv]
          :where [env (DTStlcExpr.etrue) (DTStlcTy.tbool)])
        (falseLit [env DTStlcEnv]
          :where [env (DTStlcExpr.efalse) (DTStlcTy.tbool)])
        (var [env DTStlcEnv] [x Nat] [t DTStlcTy]
             [hlookup (DTStlcLookup env x t)]
          :where [env (DTStlcExpr.evar x) t])
        (lam [env DTStlcEnv] [x Nat] [body DTStlcExpr]
              [tx DTStlcTy] [tbody DTStlcTy]
              [hbody (DTStlcHasType (DTStlcEnv.extend env x tx) body tbody)]
          :where [env (DTStlcExpr.elam x body) (DTStlcTy.tarr tx tbody)])
        (app [env DTStlcEnv] [rator DTStlcExpr] [rand DTStlcExpr]
             [tx DTStlcTy] [t DTStlcTy]
             [hfn (DTStlcHasType env rator (DTStlcTy.tarr tx t))]
             [harg (DTStlcHasType env rand tx)]
          :where [env (DTStlcExpr.eapp rator rand) t])
        (ifExpr [env DTStlcEnv] [c DTStlcExpr]
                [br-then DTStlcExpr] [br-else DTStlcExpr] [t DTStlcTy]
                [hc (DTStlcHasType env c (DTStlcTy.tbool))]
                [ht (DTStlcHasType env br-then t)]
                [he (DTStlcHasType env br-else t)]
          :where [env (DTStlcExpr.eif c br-then br-else) t])))))

(defn- var-id
  [ids x]
  (or (get @ids x)
      (let [id (count @ids)]
        (swap! ids assoc x id)
        id)))

(defn- ty-form
  [ty]
  (cond
    (= :int ty) (call "DTStlcTy.tint")
    (= :bool ty) (call "DTStlcTy.tbool")
    (and (vector? ty) (= :-> (first ty)))
    (call "DTStlcTy.tarr" (ty-form (second ty)) (ty-form (nth ty 2)))
    :else
    (throw (ex-info "Cannot encode STLC type" {:type ty}))))

(declare expr-form)

(defn- env-form
  [ids entries]
  (if-let [s (seq entries)]
    (let [[[x ty] & rest-entries] s]
      (call "DTStlcEnv.extend"
            (env-form ids rest-entries)
            (var-id ids x)
            (ty-form ty)))
    (call "DTStlcEnv.empty")))

(defn- expr-form
  [ids expr]
  (cond
    (integer? expr) (call "DTStlcExpr.eint" expr)
    (true? expr) (call "DTStlcExpr.etrue")
    (false? expr) (call "DTStlcExpr.efalse")
    (symbol? expr) (call "DTStlcExpr.evar" (var-id ids expr))

    (and (vector? expr) (= :lam (first expr)))
    (call "DTStlcExpr.elam"
          (var-id ids (second expr))
          (expr-form ids (nth expr 2)))

    (and (vector? expr) (= :app (first expr)))
    (call "DTStlcExpr.eapp"
          (expr-form ids (second expr))
          (expr-form ids (nth expr 2)))

    (and (vector? expr) (= :if (first expr)))
    (call "DTStlcExpr.eif"
          (expr-form ids (second expr))
          (expr-form ids (nth expr 2))
          (expr-form ids (nth expr 3)))

    :else
    (throw (ex-info "Cannot encode STLC expression" {:expr expr}))))

(defn- judgment-form
  [ids judgment]
  (let [[rel entries expr ty] judgment]
    (when-not (= '!- rel)
      (throw (ex-info "Expected has-type judgment" {:judgment judgment})))
    (call "DTStlcHasType"
          (env-form ids entries)
          (expr-form ids expr)
          (ty-form ty))))

(defn- nat-neq-proof
  [ids cache lhs rhs]
  (let [lhs-id (var-id ids lhs)
        rhs-id (var-id ids rhs)]
    (when (= lhs-id rhs-id)
      (throw (ex-info "Cannot prove Nat inequality for identical variable IDs"
                      {:lhs lhs :rhs rhs :id lhs-id})))
    (or (get @cache [lhs-id rhs-id])
        (let [[_ proof] (binding [a/*verbose* false]
                          (a/prove-law [] (list 'Not (list 'Eq 'Nat lhs-id rhs-id)) '[(decide)]))]
          (swap! cache assoc [lhs-id rhs-id] proof)
          proof))))

(defn- stlc-certifier
  [ids neq-proofs]
  (dt/certifier
   dt-test/stlc
   {:encoders {:env (partial env-form ids)
               :expr (partial expr-form ids)
               :ty ty-form
               :var (partial var-id ids)}
    :side {:nat-neq (fn [_ctx lhs rhs]
                      (nat-neq-proof ids neq-proofs lhs rhs))}
    :rules {:lookup-hit
            {:term [:call "DTStlcLookup.hit"
                    [:encode :env '?rest]
                    [:encode :var '?x]
                    [:encode :ty '?t]]}

            :lookup-miss
            {:term [:call "DTStlcLookup.miss"
                    [:encode :env '?rest]
                    [:encode :var '?y]
                    [:encode :ty '?v]
                    [:encode :var '?x]
                    [:encode :ty '?t]
                    [:side :nat-neq '?y '?x]
                    [:premise 0 :term]]}

            :var
            {:term [:call "DTStlcHasType.var"
                    [:encode :env '?env]
                    [:encode :var '?x]
                    [:encode :ty '?t]
                    [:premise 0 :term]]}

            :int-lit
            {:term [:call "DTStlcHasType.intLit"
                    [:encode :env '?env]
                    '?n]}

            :true-lit
            {:term [:call "DTStlcHasType.trueLit"
                    [:encode :env '?env]]}

            :false-lit
            {:term [:call "DTStlcHasType.falseLit"
                    [:encode :env '?env]]}

            :lam
            {:term [:call "DTStlcHasType.lam"
                    [:encode :env '?env]
                    [:encode :var '?x]
                    [:encode :expr '?body]
                    [:encode :ty '?tx]
                    [:encode :ty '?tbody]
                    [:premise 0 :term]]}

            :app
            {:term [:call "DTStlcHasType.app"
                    [:encode :env '?env]
                    [:encode :expr '?rator]
                    [:encode :expr '?rand]
                    [:encode :ty '?t-rand]
                    [:encode :ty '?t]
                    [:premise 0 :term]
                    [:premise 1 :term]]}

            :if
            {:term [:call "DTStlcHasType.ifExpr"
                    [:encode :env '?env]
                    [:encode :expr '?c]
                    [:encode :expr '?then]
                    [:encode :expr '?else]
                    [:encode :ty '?t]
                    [:premise 0 :term]
                    [:premise 1 :term]
                    [:premise 2 :term]]}}}))

(defn- check-reconstructed!
  [judgment]
  (let [ids (atom {})
        neq-proofs (atom {})
        certifier (stlc-certifier ids neq-proofs)]
    (dt-cert/certify
     (a/env)
     dt-test/stlc
     certifier
     (fn [judgment _proof-artifact]
       (judgment-form ids judgment))
     judgment
     {:fuel 5000000 :timeout-ms 10000})))

(deftest datatype-derivation-reconstructs-ansatz-proof
  (install-stlc-kernel!)
  (testing "identity function"
    (let [report (check-reconstructed! '[!- () [:lam x x] [:-> :int :int]])]
      (is (:ok? report) (pr-str report))))
  (testing "identity application"
    (let [report (check-reconstructed! '[!- () [:app [:lam x x] 7] :int])]
      (is (:ok? report) (pr-str report))))
  (testing "nested lambda references an outer binder through lookup-miss"
    (let [report (check-reconstructed! '[!- () [:lam y [:lam x y]] [:-> :int [:-> :bool :int]]])]
      (is (:ok? report) (pr-str report)))))
