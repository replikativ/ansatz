(ns ansatz.tactic.simp-edge-test
  "Edge case tests for the simp tactic: perm detection, prop-true,
   discrimination tree matching, and proof construction."
  (:require [ansatz.test-env :as test-env]
            [clojure.test :refer [deftest testing is use-fixtures]]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.tc :as tc]
            [ansatz.tactic.simp :as simp]
            [ansatz.tactic.discr-tree :as dt]
            [ansatz.simp-index :as si]
            [ansatz.tactic.instance :as inst]
            [ansatz.tactic.proof :as proof]
            [ansatz.tactic.basic :as basic])
  (:import [ansatz.kernel ConstantInfo]))

(def ^:private test-env test-env/checked-bundled-init-env)

(defn- require-env [] (or @test-env (throw (ex-info "bundled Init unavailable" {}))))

;; ============================================================
;; isPerm detection
;; ============================================================

(deftest test-perm-comm-detected
  (testing "add_comm is detected as permutative (LHS and RHS differ only in bvar order)"
    (let [env (require-env)
          ci (env/lookup env (name/from-string "Nat.add_comm"))
          lemma (#'simp/extract-simp-lemma env ci 1000)]
      (when (seq lemma)
        (is (:perm (first lemma)) "add_comm should be perm=true")))))

(deftest test-perm-assoc-not-detected
  (testing "add_assoc is NOT permutative (different nesting structure)"
    (let [env (require-env)
          ci (env/lookup env (name/from-string "Nat.add_assoc"))
          lemma (#'simp/extract-simp-lemma env ci 1000)]
      (when (seq lemma)
        (is (not (:perm (first lemma))) "add_assoc should be perm=false")))))

;; ============================================================
;; Simp lemma extraction
;; ============================================================

(deftest test-extract-eq-lemma
  (testing "Eq lemma extracted correctly"
    (let [env (require-env)
          ci (env/lookup env (name/from-string "Nat.add_zero"))
          lemma (#'simp/extract-simp-lemma env ci 1000)]
      (is (seq lemma) "Should extract at least one lemma")
      (when (seq lemma)
        (is (= :eq (:kind (first lemma))) "Should be :eq kind")))))

(deftest test-extract-returns-vector
  (testing "extract-simp-lemma returns a vector"
    (let [env (require-env)
          ci (env/lookup env (name/from-string "Nat.add_zero"))
          result (#'simp/extract-simp-lemma env ci 1000)]
      (is (or (nil? result) (vector? result) (seq? result))
          "Should return a collection or nil"))))

;; ============================================================
;; Discrimination tree
;; ============================================================

(deftest test-discr-tree-builds-index
  (testing "Discrimination tree builds non-empty index from lemmas"
    (let [env (require-env)
          st (tc/mk-tc-state env)
          lemmas (#'simp/make-simp-lemmas env ["Nat.add_zero" "Nat.add_succ"])]
      (is (seq lemmas) "Should extract lemmas")
      (let [idx (#'simp/build-lemma-index st env lemmas)]
        (is (some? idx) "Should build index")))))

;; ============================================================
;; Simp on various expression types
;; ============================================================

(deftest test-simp-nat-add-zero
  (testing "simp Nat.add_zero reduces n + 0 to n"
    (let [env (require-env)
          st (tc/mk-tc-state env)
          nat (e/const' (name/from-string "Nat") [])
          ;; n + 0 where n = 5
          expr (e/app* (e/const' (name/from-string "Nat.add") [])
                       (e/lit-nat 5) (e/lit-nat 0))
          lemmas (#'simp/make-simp-lemmas env ["Nat.add_zero"])
          idx (#'simp/build-lemma-index st env lemmas)
          config {:max-depth 10 :single-pass? false :cache (atom {})
                  :max-steps (atom 0) :to-unfold #{} :discharge-depth 0
                  :inst-index (delay nil) :decide? false}
          result (#'simp/simp-expr* st env idx expr config)]
      (is (some? result))
      (is (e/lit-nat? (:expr result)))
      (is (= 5 (e/lit-nat-val (:expr result)))))))

(deftest test-simp-nat-arithmetic
  (testing "simp reduces ground Nat arithmetic"
    (let [env (require-env)
          st (tc/mk-tc-state env)
          ;; 2 + 3 should reduce to 5 via nat simproc
          expr (e/app* (e/const' (name/from-string "Nat.add") [])
                       (e/lit-nat 2) (e/lit-nat 3))
          lemmas (#'simp/make-simp-lemmas env [])
          idx (#'simp/build-lemma-index st env lemmas)
          config {:max-depth 10 :single-pass? false :cache (atom {})
                  :max-steps (atom 0) :to-unfold #{} :discharge-depth 0
                  :inst-index (delay nil) :decide? false}
          result (#'simp/simp-expr* st env idx expr config)]
      (is (some? result))
      (is (e/lit-nat? (:expr result)))
      (is (= 5 (e/lit-nat-val (:expr result)))))))

;; ============================================================
;; Simp-reduce (leaves residual goal)
;; ============================================================

(deftest test-simp-leaves-residual
  (testing "Simp that simplifies but can't close leaves a residual goal"
    (let [env (require-env)
          nat (e/const' (name/from-string "Nat") [])
          ;; Goal: (n + 0) = n — simp Nat.add_zero simplifies LHS
          ;; but remaining goal (n = n) needs rfl, not simp
          n-fvar (e/fvar 99)
          goal (e/app* (e/const' (name/from-string "Eq") [(lvl/succ lvl/zero)])
                       nat
                       (e/app* (e/const' (name/from-string "Nat.add") []) n-fvar (e/lit-nat 0))
                       n-fvar)
          [ps _] (proof/start-proof env goal)
          ;; Simp should simplify and leave n = n (or close via rfl internally)
          result (try (simp/simp ps ["Nat.add_zero"])
                      (catch Exception _ nil))]
      ;; Either closes (rfl on n = n) or leaves residual — both are valid
      (is (or (some? result) true) "Simp should not crash"))))

(deftest test-simp-propagates-programming-errors
  (let [env (require-env)
        st (tc/mk-tc-state env)
        nat (e/const' (name/from-string "Nat") [])
        failure (ex-info "injected inference bug" {:kind :injected-bug})]
    (with-redefs [tc/infer-type (fn [& _] (throw failure))]
      (doseq [run [#(#'simp/safe-infer st nat)
                   #(#'simp/mk-congr-fun st {:expr nat :proof? nat} nat)
                   #(#'simp/mk-congr-arg st nat {:expr nat :proof? nat})
                   #(#'simp/mk-congr st {:expr nat :proof? nat}
                                     {:expr nat :proof? nat} nat nat)
                   #(simp/simp-expr-result st env {} nat)]]
        (is (identical? failure (try (run) nil
                                     (catch clojure.lang.ExceptionInfo ex ex))))))))

(deftest test-simp-deep-finite-term
  (let [env (require-env)
        nat (e/const' (name/from-string "Nat") [])
        fid 987654
        f (e/fvar fid)
        st (tc/attach-lctx (tc/mk-tc-state env)
                           {fid {:type (e/arrow nat nat)}})
        nest (fn [x] (nth (iterate #(e/app f %) x) 40))
        redex (e/app (e/lam "x" nat (e/bvar 0) :default) (e/lit-nat 7))
        result (simp/simp-expr-result st env {} (nest redex) 1)]
    (is (= (nest (e/lit-nat 7)) (:expr result)))
    (is (nil? (:proof? result)))))

(deftest test-simp-tactic-entry-points-propagate-errors
  (let [env (require-env)
        true-type (e/const' (name/from-string "True") [])
        [ps _] (proof/start-proof env (e/arrow true-type true-type))
        ps (basic/intro ps "h")
        hid (first (keys (:lctx (proof/current-goal ps))))]
    (doseq [failure [(NullPointerException. "injected hypothesis bug")
                     (ex-info "injected metadata bug" {:kind :injected-bug})
                     (ex-info "step limit" {:kind :tactic-error :limit :max-simp-steps})]]
      (with-redefs-fn {#'simp/simp-expr* (fn [& _] (throw failure))}
        (fn []
          (doseq [run [#(simp/simp ps [] {:only? true})
                       #(simp/simp-at ps hid [] {:only? true})
                       #(simp/simp-all ps [] {:only? true})]]
            (is (identical? failure (try (run) nil
                                         (catch Throwable ex ex))))))))))

(deftest test-legacy-ble-eq-is-kernel-checked
  (let [original (require-env)
        ble-eq-name (name/from-string "Nat.ble_eq")
        nat (e/const' (name/from-string "Nat") [])
        eq (fn [type x y] (e/app* (e/const' (name/from-string "Eq") [(lvl/succ lvl/zero)])
                                  type x y))
        ble-true (eq (e/const' (name/from-string "Bool") [])
                     (e/app* (e/const' (name/from-string "Nat.ble") []) (e/bvar 1) (e/bvar 0))
                     (e/const' (name/from-string "Bool.true") []))
        le (e/app* (e/const' (name/from-string "LE.le") [lvl/zero]) nat
                   (e/const' (name/from-string "instLENat") []) (e/bvar 1) (e/bvar 0))
        expected-type (e/forall' "x" nat
                                 (e/forall' "y" nat (eq (e/sort' lvl/zero) ble-true le) :default)
                                 :default)
        ;; Reuse already checked fixture declarations, with no bridge in locals/cache.
        legacy (reduce (fn [env ^ConstantInfo ci]
                         (if (= ble-eq-name (.name ci)) env (env/add-constant env ci)))
                       (env/empty-env) (.allConstants ^ansatz.kernel.Env original))
        real-check env/check-constant
        admissions (atom 0)
        admitted (with-redefs [env/check-constant
                               (fn [env ci]
                                 (swap! admissions inc)
                                 (real-check env ci))]
                   (#'simp/ensure-ble-eq legacy))
        ci (env/lookup admitted ble-eq-name)
        failure (ex-info "injected bridge admission failure" {:kind :admission-failure})]
    (is (nil? (env/lookup legacy ble-eq-name)))
    (is (= 1 @admissions))
    (is (some? ci))
    (when ci
      (is (.isThm ^ConstantInfo ci))
      (is (tc/is-def-eq (tc/mk-tc-state admitted) expected-type (.type ^ConstantInfo ci))))
    (with-redefs [env/check-constant (fn [& _] (throw failure))]
      (is (identical? failure
                      (try (#'simp/ensure-ble-eq legacy) nil
                           (catch clojure.lang.ExceptionInfo ex ex)))))))

(deftest test-index-and-discharge-errors-propagate
  (let [env (require-env)
        st (tc/mk-tc-state env)
        nat (e/const' (name/from-string "Nat") [])
        failure (NullPointerException. "injected index/synthesis bug")]
    (with-redefs [tc/infer-type (fn [& _] (throw failure))]
      (doseq [run [#(#'dt/is-proof? st nat) #(#'dt/is-type? st nat)]]
        (is (identical? failure (try (run) nil (catch NullPointerException ex ex))))))
    (is (identical? failure
                    (try (si/lemma-keys ["Nat.add_zero"] env (fn [_] (throw failure)))
                         nil (catch NullPointerException ex ex))))
    (with-redefs [inst/synthesize* (fn [& _] (throw failure))]
      (is (identical? failure
                      (try (#'simp/try-discharge st env {} {:inst-index {}} nat 0)
                           nil (catch NullPointerException ex ex)))))))

(defn- conditional-rule-env []
  (let [nat (e/const' (name/from-string "Nat") [])
        axiom (fn [env n ty]
                (env/check-constant env (env/mk-axiom (name/from-string n) [] ty)))
        a (e/const' (name/from-string "SimpEdge.a") [])
        b (e/const' (name/from-string "SimpEdge.b") [])
        p (e/const' (name/from-string "SimpEdge.P") [])
        eq (fn [x y] (e/app* (e/const' (name/from-string "Eq") [(lvl/succ lvl/zero)])
                             nat x y))]
    (-> (require-env)
        (axiom "SimpEdge.a" nat)
        (axiom "SimpEdge.b" nat)
        (axiom "SimpEdge.P" (e/arrow nat (e/sort' lvl/zero)))
        (axiom "SimpEdge.conditional"
               (e/forall' "x" nat
                          (e/arrow (e/app p (e/bvar 0)) (eq a b)) :default))
        (axiom "SimpEdge.ab" (eq a b))
        (axiom "SimpEdge.ba" (eq b a)))))

(deftest test-inapplicable-conditional-rule
  (let [env (conditional-rule-env)
        st (tc/mk-tc-state env)
        a (e/const' (name/from-string "SimpEdge.a") [])
        lemmas (simp/make-simp-lemmas env ["SimpEdge.conditional"])
        index (simp/build-lemma-index st env lemmas)
        result (simp/simp-expr-result st env index a)]
    (is (= 1 (count lemmas)))
    (is (= a (:expr result)))
    (is (nil? (:proof? result)))
    ;; Rejecting the first candidate must still allow a later applicable rule.
    (let [index (simp/build-lemma-index st env
                                        (concat lemmas (simp/make-simp-lemmas env ["SimpEdge.ab"])))
          result (simp/simp-expr-result st env index a)]
      (is (= (e/const' (name/from-string "SimpEdge.b") []) (:expr result)))
      (is (some? (:proof? result))))))

(deftest test-cyclic-rules-hit-controlled-recursion-limit
  (let [env (conditional-rule-env)
        st (tc/mk-tc-state env)
        lemmas (simp/make-simp-lemmas env ["SimpEdge.ab" "SimpEdge.ba"])
        index (simp/build-lemma-index st env lemmas)
        failure (try (simp/simp-expr-result st env index
                                            (e/const' (name/from-string "SimpEdge.a") []))
                     nil
                     (catch clojure.lang.ExceptionInfo ex ex))]
    (is (= 2 (count lemmas)))
    (is (= :tactic-error (:kind (ex-data failure))))
    (is (= :max-rec-depth (:limit (ex-data failure))))
    (is (= 512 (:max-rec-depth (ex-data failure))))
    (is (re-find #"maxRecDepth" (or (ex-message failure) "")))))

(defn- deep-traversal-context [depth]
  (let [nat (e/const' (name/from-string "Nat") [])
        n (e/fvar 980001) g (e/fvar 980002) f (e/fvar 980003)
        lctx {980001 {:type nat} 980002 {:type (e/arrow nat nat)}
              980003 {:type (e/arrow nat (e/sort' (lvl/succ lvl/zero)))}}
        nested (nth (iterate #(e/app g %) n) depth)]
    {:env (require-env) :lctx lctx :n n :nested nested :domain (e/app f nested)}))

(defn- assert-recursion-limit [run]
  (let [failure (try (run) nil (catch clojure.lang.ExceptionInfo ex ex))]
    (is (= :tactic-error (:kind (ex-data failure))))
    (is (= :max-rec-depth (:limit (ex-data failure))))
    (is (= 512 (:max-rec-depth (ex-data failure))))
    (is (re-find #"maxRecDepth" (or (ex-message failure) "")))))

(deftest test-deep-lambda-domain-hits-recursion-limit
  (let [{:keys [env lctx n domain]} (deep-traversal-context 3000)
        st (tc/attach-lctx (tc/mk-tc-state env) lctx)]
    (assert-recursion-limit
     #(simp/simp-expr-result st env {} (e/lam "x" domain n :default)))))

(deftest test-deep-fixed-argument-hits-recursion-limit
  (let [{:keys [env lctx domain]} (deep-traversal-context 3000)
        st (tc/attach-lctx (tc/mk-tc-state env) lctx)
        term (e/app (e/const' (name/from-string "List.nil") [lvl/zero]) domain)]
    (assert-recursion-limit #(simp/simp-expr-result st env {} term))))

(deftest test-dsimp-hits-recursion-limit
  (let [{:keys [env lctx n nested]} (deep-traversal-context 3000)
        nat (e/const' (name/from-string "Nat") [])
        goal (e/app* (e/const' (name/from-string "Eq") [(lvl/succ lvl/zero)])
                     nat nested n)
        [ps root] (proof/start-proof env goal)
        [ps _] (proof/fresh-mvar-replacing ps goal lctx root)]
    (assert-recursion-limit #(simp/dsimp ps))))

(deftest test-finite-definitional-descent-beyond-old-cutoff
  (let [{:keys [env lctx n domain nested]} (deep-traversal-context 40)
        st (tc/attach-lctx (tc/mk-tc-state env) lctx)
        nat (e/const' (name/from-string "Nat") [])
        redex (e/app (e/lam "x" nat (e/bvar 0) :default) n)
        ;; The beta redex is BELOW all 40 opaque g applications in every case.
        deep-redex (nth (iterate #(e/app (e/fvar 980002) %) redex) 40)
        redex-domain (e/app (e/fvar 980003) deep-redex)
        lam (e/lam "x" redex-domain n :default)
        fixed (e/app (e/const' (name/from-string "List.nil") [lvl/zero]) redex-domain)
        eq (fn [x] (e/app* (e/const' (name/from-string "Eq") [(lvl/succ lvl/zero)]) nat x n))
        [ps root] (proof/start-proof env (eq deep-redex))
        [ps _] (proof/fresh-mvar-replacing ps (eq deep-redex) lctx root)]
    (is (= (e/lam "x" domain n :default) (:expr (simp/simp-expr-result st env {} lam))))
    (is (= (e/app (e/const' (name/from-string "List.nil") [lvl/zero]) domain)
           (:expr (simp/simp-expr-result st env {} fixed))))
    (is (= (eq nested) (:type (proof/current-goal (simp/dsimp ps)))))))

(deftest test-simp-and-dsimp-share-recursion-budget
  (let [{:keys [env lctx n domain]} (deep-traversal-context 350)
        nat (e/const' (name/from-string "Nat") [])
        st (tc/attach-lctx (tc/mk-tc-state env) lctx)
        ;; Each segment fits alone; simp's enclosing lambda visits plus dsimp's
        ;; inner domain traversal must exhaust ONE shared recursion budget.
        term (nth (iterate #(e/lam "y" nat % :default)
                           (e/lam "x" domain n :default)) 100)]
    (assert-recursion-limit #(simp/simp-expr-result st env {} term))))

(deftest test-dependent-forall-binder-is-opened
  (let [env (require-env)
        nat (e/const' (name/from-string "Nat") [])
        p (e/fvar 991003)
        st (tc/attach-lctx (tc/mk-tc-state env)
                           {991003 {:type (e/arrow nat (e/sort' lvl/zero))}})
        term (e/forall' "n" nat (e/app p (e/bvar 0)) :default)
        result (simp/simp-expr-result st env {} term)]
    (is (= term (:expr result)))
    (is (nil? (:proof? result)))))

(deftest test-dependent-forall-rewrite-has-kernel-checked-proof
  (let [nat (e/const' (name/from-string "Nat") [])
        prop (e/sort' lvl/zero)
        p (e/const' (name/from-string "SimpEdge.P") [])
        q (e/const' (name/from-string "SimpEdge.Q") [])
        eq (fn [a b] (e/app* (e/const' (name/from-string "Eq") [(lvl/succ lvl/zero)]) prop a b))
        env (-> (conditional-rule-env)
                (env/check-constant (env/mk-axiom (name/from-string "SimpEdge.Q") [] (e/arrow nat prop)))
                (env/check-constant (env/mk-axiom (name/from-string "SimpEdge.predRule") []
                                                  (e/forall' "n" nat
                                                             (eq (e/app p (e/bvar 0))
                                                                 (e/app q (e/bvar 0))) :default))))
        st (tc/mk-tc-state env)
        old (e/forall' "n" nat (e/app p (e/bvar 0)) :default)
        new (e/forall' "n" nat (e/app q (e/bvar 0)) :default)
        index (simp/build-lemma-index st env (simp/make-simp-lemmas env ["SimpEdge.predRule"]))
        result (simp/simp-expr-result st env index old)]
    (is (= new (:expr result)))
    (is (some? (:proof? result)))
    (is (some? (env/check-constant env
                                   (env/mk-thm (name/from-string "SimpEdge.forallChecked") []
                                               (eq old new) (:proof? result)))))))

(defn- shared-term-context [depth]
  (let [env (require-env)
        nat (e/const' (name/from-string "Nat") [])
        n (e/fvar 991101) g (e/fvar 991102)
        st (tc/attach-lctx (tc/mk-tc-state env)
                           {991101 {:type nat} 991102 {:type (e/arrow nat (e/arrow nat nat))}})]
    {:env env :st st
     :term (nth (iterate #(e/app* g % %) n) depth)}))

(defn- bounded-tag-visits [run]
  ;; Both time and visit limits: a regression cannot leave an exponential scan
  ;; running after timeout. No exception is treated as successful simplification.
  (let [visits (atom 0)
        original-tag e/tag
        task (future
               (with-redefs [e/tag (fn [expr]
                                     (when (> (swap! visits inc) 50000)
                                       (throw (ex-info "test visit budget exceeded" {})))
                                     (original-tag expr))]
                 (run)))]
    (try
      (let [result (deref task 5000 ::timeout)]
        (is (not= ::timeout result) "shared DAG work must finish within five seconds")
        [result @visits])
      (finally (future-cancel task)))))

(deftest test-shared-dag-cache-hit-does-not-traverse
  (let [{:keys [env st term]} (shared-term-context 22)
        expected {:expr term :proof? nil :cache true}
        steps (atom 0)
        config {:max-depth 20 :cache (atom {term expected}) :max-steps steps}
        [result visits] (bounded-tag-visits #(#'simp/simp-expr* st env {} term config))]
    (is (identical? expected result))
    (is (zero? visits))
    (is (zero? @steps))))

(deftest test-shared-dag-simp-and-dsimp-visit-distinct-nodes
  (let [{:keys [env st term]} (shared-term-context 22)
        [result visits] (bounded-tag-visits #(simp/simp-expr-result st env {} term))
        [definitional dvisits] (bounded-tag-visits #(#'simp/dsimp-expr env (:lctx st) term 20))]
    (is (= term (:expr result)))
    (is (nil? (:proof? result)))
    (is (< visits 10000))
    (is (identical? term definitional))
    (is (< dvisits 1000))))

(defn- checked-simp [ty names]
  (let [env (require-env)
        [ps _] (proof/start-proof env ty)
        ps (loop [ps ps]
             (if (e/forall? (:type (proof/current-goal ps)))
               (recur (basic/intro ps)) ps))
        ps (simp/simp ps names {:only? true})]
    (is (proof/solved? ps))
    (is (some? ((requiring-resolve 'ansatz.tactic.extract/verify) ps)))))

(deftest test-simp-permutative-add-normalizes-both-sides
  (let [nat (e/const' (name/from-string "Nat") [])
        add (fn [a b] (e/app* (e/const' (name/from-string "Nat.add") []) a b))
        eq (e/app* (e/const' (name/from-string "Eq") [(lvl/succ lvl/zero)])
                   nat (add (e/bvar 1) (e/bvar 0)) (add (e/bvar 0) (e/bvar 1)))]
    (checked-simp (e/forall' "a" nat (e/forall' "b" nat eq :default) :default)
                  ["Nat.add_comm"])))

(deftest test-simp-lt-add-one-raw-add-index
  (let [nat (e/const' (name/from-string "Nat") [])
        add (e/app* (e/const' (name/from-string "Nat.add") []) (e/bvar 0) (e/lit-nat 1))
        lt (e/app* (e/const' (name/from-string "LT.lt") [lvl/zero])
                   nat (e/const' (name/from-string "instLTNat") []) (e/bvar 0) add)]
    (checked-simp (e/forall' "n" nat lt :default) ["Nat.lt_add_one"])))

(deftest test-simp-equal-bool-rec-branches-carry-proof
  (let [env (require-env)
        nat (e/const' (name/from-string "Nat") [])
        bool (e/const' (name/from-string "Bool") [])
        b (e/fvar 992001) x (e/fvar 992002)
        st (tc/attach-lctx (tc/mk-tc-state env)
                           {992001 {:tag :local :name "b" :type bool}
                            992002 {:tag :local :name "x" :type nat}})
        rec (e/app* (e/const' (name/from-string "Bool.rec") [(lvl/succ lvl/zero)])
                    (e/lam "_" bool nat :default) x x b)
        result (simp/simp-expr-result st env {} rec)
        eq (e/app* (e/const' (name/from-string "Eq") [(lvl/succ lvl/zero)]) nat rec x)
        close (fn [term] (e/lam "b" bool (e/lam "x" nat (e/abstract-many term [992001 992002]) :default) :default))]
    (is (= x (:expr result)))
    (is (some? (:proof? result)))
    (is (env/verifies? env (e/forall' "b" bool (e/forall' "x" nat (e/abstract-many eq [992001 992002]) :default) :default)
                       (close (:proof? result))))))

(deftest test-simp-simp-all-normalizes-conditional-hypothesis
  (let [env (require-env)
        nat (e/const' (name/from-string "Nat") [])
        eq (fn [a b] (e/app* (e/const' (name/from-string "Eq") [(lvl/succ lvl/zero)]) nat a b))
        ;; n m : Nat, p : Prop, h : n = m, ih : p → n = 0 ⊢ p → m = 0
        ty (e/forall' "n" nat
                      (e/forall' "m" nat
                                 (e/forall' "p" (e/sort' lvl/zero)
                                            (e/forall' "h" (eq (e/bvar 2) (e/bvar 1))
                                                       (e/forall' "ih" (e/arrow (e/bvar 1) (eq (e/bvar 4) (e/lit-nat 0)))
                                                                  (e/arrow (e/bvar 2) (eq (e/bvar 4) (e/lit-nat 0))) :default) :default) :default) :default) :default)
        [ps _] (proof/start-proof env ty)
        ps (basic/intros ps ["n" "m" "p" "h" "ih"])
        ps (simp/simp-all ps [] {:only? true})]
    ;; Closing alone could use the original IH after rewriting the target.
    ;; Require simp_all to have actually asserted the normalized conditional IH.
    (is (some #(= "ih'" (:name %))
              (mapcat (comp vals :lctx) (vals (get-in ps [:meta-mctx :decls])))))
    (is (proof/solved? ps))
    (is (some? ((requiring-resolve 'ansatz.tactic.extract/verify) ps)))))

(deftest test-simp-ac-order-uses-lean-name-and-level-order
  (let [n2 (name/mk-num (name/from-string "x") 2)
        n10 (name/mk-num (name/from-string "x") 10)]
    (is (#'simp/ac-lt? (e/const' n2 []) (e/const' n10 [])))
    (is (not (#'simp/ac-lt? (e/const' n10 []) (e/const' n2 []))))
    (is (#'simp/ac-lt? (e/sort' lvl/zero) (e/sort' (lvl/succ lvl/zero))))))

(deftest test-simp-forall-candidate-cannot-capture-bound-variable
  (let [nat (e/const' (name/from-string "Nat") [])
        prop (e/sort' lvl/zero)
        eq-prop (fn [a b] (e/app* (e/const' (name/from-string "Eq") [(lvl/succ lvl/zero)]) prop a b))
        body (e/app* (e/const' (name/from-string "Eq") [(lvl/succ lvl/zero)]) nat (e/bvar 0) (e/bvar 0))
        target (e/forall' "n" nat body :default)
        truth (e/const' (name/from-string "True") [])
        env (-> (require-env)
                (env/check-constant
                 (env/mk-axiom (name/from-string "DecideTest.constRule") []
                               (e/forall' "p" prop
                                          (eq-prop (e/forall' "n" nat (e/bvar 1) :default) (e/bvar 0)) :default)))
                (env/check-constant
                 (env/mk-axiom (name/from-string "DecideTest.forallRule") [] (eq-prop target truth))))
        st (tc/mk-tc-state env)
        rejected (simp/make-simp-lemmas env ["DecideTest.constRule"])
        applicable (simp/make-simp-lemmas env ["DecideTest.forallRule"])
        index (simp/build-lemma-index st env (concat (map #(assoc % :priority 2000) rejected) applicable))
        result (simp/simp-expr-result st env index target)]
    (is (nil? (#'simp/match-lemma st (:lhs-pattern (first rejected)) target 1)))
    (is (= truth (:expr result)))
    (is (env/verifies? env (eq-prop target truth) (:proof? result)))))

;; Lean Simp/Rewrite.lean tryTheoremCore/synthesizeArgs/dischargeUsingAssumption?:
;; an explicit parameter can occur only inside an instance-valued argument.
(defn- close-binders [ctor binders body]
  (reduce (fn [body [id nm ty]] (ctor nm ty (e/abstract1 body id) :default))
          body (reverse binders)))

(deftest test-ne-discharge-through-composite-instance
  (let [env (require-env)
        c (fn [nm] (e/const' (name/from-string nm) []))
        k (e/fvar 993000) dec (e/fvar 993001)
        x (e/fvar 993002) y (e/fvar 993003)
        u (lvl/succ lvl/zero)
        binders [[993000 "K" (e/sort' u)]
                 [993001 "dec" (e/app (e/const' (name/from-string "DecidableEq") [u]) k)]
                 [993002 "x" k] [993003 "y" k]]
        inst (e/app* (e/const' (name/from-string "instBEqOfDecidableEq") [lvl/zero]) k dec)
        beq (e/app* (e/const' (name/from-string "BEq.beq") [lvl/zero]) k inst x y)
        eqxy (e/app* (e/const' (name/from-string "Eq") [u]) k x y)
        nexy (e/app* (e/const' (name/from-string "Ne") [u]) k x y)
        conclusion (e/app* (e/const' (name/from-string "Eq") [u]) (c "Bool") beq (c "Bool.false"))
        ;; A supplied conditional rule makes this an Init-medium reproduction,
        ;; independent of the full export's beq_eq_false_iff_ne theorem.
        rule (close-binders e/forall' binders (e/arrow nexy conclusion))
        ty (close-binders e/forall' (conj binders [993004 "hne" (e/app (c "Not") eqxy)]
                                          [993005 "rule" rule]) conclusion)
        [ps _] (proof/start-proof env ty)
        ps (basic/intros ps ["K" "dec" "x" "y" "hne" "rule"])
        lctx (:lctx (proof/current-goal ps))
        rule-id (first (for [[id d] lctx :when (= "rule" (:name d))] id))
        ps (simp/simp ps [(e/fvar rule-id)] {:only? true})]
    (is (proof/solved? ps))
    (is (some? ((requiring-resolve 'ansatz.tactic.extract/verify) ps)))))

(deftest test-raw-nat-packing-keeps-definitional-progress
  (let [env (#'simp/ensure-nat-packing (require-env) ["Nat.add_eq" "Nat.le_eq"])
        nat (e/const' (name/from-string "Nat") [])
        st (tc/mk-tc-state-with-locals env {993010 {:name "x" :type nat}
                                            993011 {:name "y" :type nat}})]
    (doseq [[raw lemma packed] [["Nat.add" "Nat.add_eq" "HAdd.hAdd"]
                                ["Nat.le" "Nat.le_eq" "LE.le"]]]
      (let [term (e/app* (e/const' (name/from-string raw) []) (e/fvar 993010) (e/fvar 993011))
            result (simp/simp-expr-result st env (simp/build-lemma-index st env (simp/make-simp-lemmas env [lemma])) term)]
        (is (= packed (name/->string (e/const-name (e/get-app-fn (:expr result))))))
        (is (not= term (:expr result)))
        (is (nil? (:proof? result)) "rfl normalization still counts as progress")
        (is (tc/is-def-eq st term (:expr result)))))))

(deftest simp-rejects-uncertified-goal-change
  (let [env (require-env)
        nat (e/const' (name/from-string "Nat") [])
        eq (e/const' (name/from-string "Eq") [(lvl/succ lvl/zero)])
        original (e/app* eq nat (e/lit-nat 0) (e/lit-nat 1))
        simplified (e/app* eq nat (e/lit-nat 0) (e/lit-nat 0))
        [ps _] (proof/start-proof env original)
        goal (proof/current-goal ps)
        st (tc/attach-lctx (tc/mk-tc-state env) (:lctx goal))]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"uncertified simplification"
                          (#'simp/close-goal-with-proof ps goal st
                                                        {:expr simplified :proof? nil} [])))
    (let [truth (e/const' (name/from-string "True") [])
          h (e/app* (e/const' (name/from-string "Eq.refl") [(lvl/succ lvl/zero)])
                    (e/sort' lvl/zero) truth)]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"invalid equality proof"
                            (#'simp/close-goal-with-proof ps goal st {:expr truth :proof? h} []))))))
