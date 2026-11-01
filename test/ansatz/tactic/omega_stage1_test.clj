(ns ansatz.tactic.omega-stage1-test
  "Stage 1 contracts; arithmetic counterparts are in test/lean/omega_stage1.lean."
  (:require [clojure.test :refer [deftest is testing]]
            [ansatz.core :as a]
            [ansatz.conformance-support :as cs]
            [ansatz.test-env :as te]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.tc :as tc]
            [ansatz.kernel.reduce :as red]
            [ansatz.kernel.level :as lvl]
            [ansatz.tactic.proof :as proof]
            [ansatz.tactic.basic :as basic]
            [ansatz.tactic.extract :as extract]
            [ansatz.tactic.decide :as decide]
            [ansatz.tactic.omega :as omega]
            [ansatz.tactic.omega.frontend :as f]
            [ansatz.tactic.omega.core :as c]
            [ansatz.tactic.omega.omega-m :as m]))

(defn- const-expr [s] (e/const' (name/from-string s) []))

(def ^:private examples
  '[[stage1_carrier [b :- Bool, x :- Nat, y :- Nat, k :- (<= x y), h :- (= Bool b true)]
     (< x (+ y 1)) [(omega)]]
    [stage1_symbolic [x :- Nat, d :- Nat, h :- (<= (Nat.div x d) x), k :- (<= Nat 3 x)]
     (<= Nat 1 (Nat.div x 3)) [(omega)]]
    [stage1_nonlinear [x :- Nat, y :- Nat, z :- Nat, h :- (<= (* x y) z), k :- (<= z x)]
     (<= (* x y) x) [(omega)]]
    [stage1_nonprop [f :- (=> Nat Nat), x :- Nat, y :- Nat, h :- (<= x y)]
     (< x (+ y 1)) [(omega)]]
    [stage1_branches [x :- Nat, y :- Nat, hx :- (<= Nat 3 x), hy :- (<= Nat 5 y),
                      h :- (Or (= (Nat.div x 3) 0) (= (Nat.div y 5) 0))]
     False [(omega)]]
    [stage1_skip [p :- Prop, q :- Prop, x :- Nat, k :- (<= Nat 2 x),
                  h :- (Or p q), h2 :- (Or (= x 0) (= x 1))]
     False [(omega)]]])

(deftest useful-facts-survive-unsupported-inputs
  (cs/check-suite "omega stage1" (cs/run-suite 'ansatz.tactic.omega-stage1-test [] examples) {}))

(deftest implementation-exceptions-escape
  (let [st (tc/mk-tc-state @te/bundled-init-env)
        error (IllegalStateException. "inference sentinel")]
    (with-redefs [tc/infer-type (fn [& _] (throw error))]
      (is (identical? error
                      (try (#'f/reify-term st (m/mk-state) (e/fvar 123))
                           (catch IllegalStateException ex ex))))
      (is (identical? error
                      (try (f/decides? @te/bundled-init-env (const-expr "False")
                                       (red/lctx-add-local {} 123 "x" (const-expr "Nat")))
                           (catch IllegalStateException ex ex))))))
  (let [error (IllegalArgumentException. "reconstruction sentinel")
        nat (const-expr "Nat")
        goal (e/forall' "x" nat
                        (e/app* (const-expr "Nat.le") (e/lit-nat 0) (e/bvar 0)) :default)
        [ps _] (proof/start-proof @te/bundled-init-env goal)
        ps (basic/intros ps ["x"])]
    (with-redefs [c/extract-proof (fn [& _] (throw error))]
      (is (identical? error
                      (try (omega/omega ps)
                           (catch IllegalArgumentException ex ex))))))
  (doseq [error [(IllegalStateException. "decide sentinel")
                 (ex-info "type sentinel" {:kind :type-error})]]
    (with-redefs [decide/decide (fn [_] (throw error))]
      (is (identical? error
                      (try (omega/omega (first (proof/start-proof @te/bundled-init-env (const-expr "False"))))
                           (catch IllegalStateException ex ex)
                           (catch clojure.lang.ExceptionInfo ex ex)))))))

(deftest named-resources
  (doseq [[limit value] [[:work 0] [:depth 0]]]
    (let [ex (binding [m/*work-limit* (if (= limit :work) value 1000)
                       m/*depth-limit* (if (= limit :depth) value 128)]
               (try (f/decides? @te/bundled-init-env (const-expr "False") {})
                    (catch clojure.lang.ExceptionInfo ex ex)))]
      (is (= {:kind :tactic-error :tactic :omega :limit limit :value value}
             (ex-data ex)))))
  (let [ex (binding [m/*depth-limit* 0]
             (try (c/extract-proof {} nil [] 0)
                  (catch clojure.lang.ExceptionInfo ex ex)))]
    (is (= :depth (:limit (ex-data ex))))))

(defn- coordinate [i] (conj (vec (repeat i 0)) 1))
(defn- no-proof [& _] nil)

(deftest structural-solver-termination-beyond-100
  (testing "all 130 easy equalities are eliminated"
    (let [p (reduce (fn [p i] (c/add-equality p 0 (coordinate i) nil no-proof))
                    (c/mk-problem) (range 130))
          [_ result] (c/solve-equalities (m/mk-state) p no-proof no-proof)]
      (is (:possible result))
      (is (empty? (:equalities result)))
      (is (= 130 (count (:eliminations result))))))
  (testing "all 130 one-sided FM variables are eliminated"
    (let [p (reduce (fn [p i] (c/add-inequality p 0 (coordinate i) nil no-proof))
                    (c/mk-problem) (range 130))
          ;; Classifying the dense coordinate table now counts as work too.
          [_ result] (binding [m/*work-limit* 2000000]
                       (c/run-omega (m/mk-state) p no-proof no-proof))]
      (is (:possible result))
      (is (empty? (:constraints result))))))

(deftest fresh-hard-equality-uses-the-atom-allocator
  (let [[state _] (m/lookup (m/mk-state) :unused (constantly []))
        [state _] (m/lookup state :x (constantly []))
        [state _] (m/lookup state :y (constantly []))
        ;; Current coefficients do not mention index 2. It is still reserved.
        p (c/add-equality (c/mk-problem) -5 [6 7] nil no-proof)
        [state _] (#'c/solve-hard-equality state p [6 7] (fn [& _] :fresh) no-proof)]
    (is (= 2 (get-in state [:atoms :y])))
    (is (= 3 (get-in state [:atoms :fresh])))
    (is (= :y (get-in state [:idx->expr 2])))))

(deftest exact-elimination-preference
  (let [d (fn [i lower upper exact]
            {:var i :lowerBounds (repeat lower nil) :upperBounds (repeat upper nil)
             :lowerExact exact :upperExact exact})]
    (is (= 1 (:var (c/fourier-motzkin-select [(d 0 1 1 false) (d 1 2 2 true)]))))
    (is (= 2 (:var (c/fourier-motzkin-select [(d 0 1 1 false) (d 1 2 2 true) (d 2 1 0 false)]))))))

(deftest lookup-and-transactions
  (let [h (const-expr "True.intro")
        [s [i facts]] (m/lookup (m/mk-state) :x (constantly [h]))
        [s' [j again]] (m/lookup s :x (fn [_] (throw (IllegalStateException. "reanalyzed"))))]
    (is (= [0 [h] 0 nil] [i facts j again]))
    (is (= s s'))
    (is (= [:value s {:original :proof}]
           (m/without-modifying-state s {:original :proof}
                                      (fn [_ _] [:value {} {}]))))))

(deftest more-than-eight-generations
  ;; A controlled analyzer exposes one new Nat atom per round, each with an
  ;; actual Int.natCast_nonneg proof. The thirteenth round supplies h : x12 < 0.
  ;; Reconstruct and kernel-check False: it needs the last generated nonnegative
  ;; fact and h, so dropping the tail of the worklist cannot pass this test.
  (let [nat (const-expr "Nat")
        false-type (const-expr "False")
        ids (range 100 113)
        xs (mapv e/fvar ids)
        bad (e/app* (e/const' (name/from-string "LT.lt") [lvl/zero])
                    nat (const-expr "instLTNat") (last xs) (e/lit-nat 0))
        body (e/arrow bad false-type)
        goal (reduce (fn [acc [id x]]
                       (e/forall' "x" nat (e/abstract1 acc id) :default))
                     body (reverse (map vector ids xs)))
        [ps _] (proof/start-proof @te/bundled-init-env goal)
        ps (basic/intros ps (conj (mapv #(str "x" %) (range 13)) "h"))
        g (proof/current-goal ps)
        lctx (:lctx g)
        locals (into {} (map (fn [[id d]] [(:name d) (e/fvar id)])) lctx)
        h (get locals "h")
        nonneg (fn [x]
                 (let [term (e/app (const-expr "Int.natCast_nonneg") x)
                       st (tc/attach-lctx (tc/mk-tc-state (:env ps)) lctx)]
                   {:type (tc/infer-type st term) :proof term}))
        st (tc/attach-lctx (tc/mk-tc-state (:env ps)) lctx)
        seen (atom 0)
        run #'f/analyze-nonnegativity
        original @run
        initial (assoc (f/mk-meta-problem (c/mk-problem))
                       :facts [(nonneg (get locals "x0"))])
        [table m _]
        (with-redefs-fn
          {run (fn [st table p]
                 (let [[table p] (original st table p)
                       n (:next-idx table)]
                   (if (> n @seen)
                     (do (reset! seen n)
                         [table (update p :facts (fnil conj [])
                                        (if (< n 13)
                                          (nonneg (get locals (str "x" n)))
                                          {:type (tc/infer-type st h) :proof h}))])
                     [table p])))}
          #(f/process-facts st (m/mk-state) initial))
        [table result] (c/run-omega-solver table (:problem m))
        term (c/prove-false-from-justification (:env ps) result (c/build-atoms-expr table))
        ps (proof/assign-mvar ps (:id g) {:kind :exact :term term})]
    (is (= 13 @seen))
    (is (false? (:possible result)))
    (is (some? (extract/verify ps)))))

(deftest branches-own-distinct-fresh-atoms
  (a/load-init!)
  (let [tables (atom [])
        v #'f/run-omega-solver
        original @v
        theorem (first (filter #(= 'stage1_branches (first %)) examples))]
    (with-redefs-fn {v (fn [table problem]
                         (swap! tables conj table)
                         (original table problem))}
      #(is (= :ok (cs/attempt theorem 60000))))
    (is (some (fn [[left right]]
                (some (fn [[i atom]]
                        (and (contains? (:div-atoms left) i)
                             (contains? (:div-atoms right) i)
                             (not= atom (get-in right [:idx->int-expr i]))))
                      (:idx->int-expr left)))
              (for [left @tables right @tables] [left right]))
        "the alternatives allocate different quotient expressions at the same fresh index")))

(deftest invalid-generated-facts-fail-at-analysis
  (let [st (tc/mk-tc-state @te/bundled-init-env)
        ex (try (#'f/enqueue-fact st (m/mk-state) (c/mk-problem)
                                  (const-expr "False") (const-expr "True.intro"))
                (catch clojure.lang.ExceptionInfo ex ex))]
    (is (= :omega-implementation-error (:kind (ex-data ex))))
    (is (= :analyze-atom (:operation (ex-data ex))))))

(deftest large-scale-is-one-multiplication
  ;; `1000000000 * x` over Nat: Lean's mul_eval route builds ONE product proof, whatever the
  ;; literal. The former Nat bridge expanded it into a billion additions (and needed a work
  ;; budget to stop); now it finishes within a small budget and adds nothing.
  (let [nat (const-expr "Nat")
        x (e/fvar 123)
        st (tc/attach-lctx (tc/mk-tc-state @te/bundled-init-env)
                           (red/lctx-add-local {} 123 "x" nat))
        expr (e/app* (const-expr "Nat.mul") (e/lit-nat 1000000000) x)
        additions (atom 0)
        work (atom 0)
        build c/mk-add-eval-proof
        [_ lc prf] (binding [m/*work* work m/*work-limit* 24 m/*depth-limit* 128]
                     (with-redefs [c/mk-add-eval-proof (fn [& args]
                                                         (swap! additions inc)
                                                         (apply build args))]
                       (let [[t lc prf] (#'f/reify-term st (m/mk-state) expr)]
                         ;; force the delayed proof under the same budget
                         [t lc (prf (c/build-atoms-expr (m/mk-state)))])))]
    (is (= 1000000000 (first (:coeffs lc))))
    (is (zero? @additions) "no repeated additions")
    (is (< @work 24) "within a small work budget")
    (is (some? (:proof prf)))))

(deftest delayed-eval-descent-is-accounted
  (let [lc (c/mk-lc 0)
        atoms (c/build-atoms-expr (m/mk-state))]
    (doseq [operation [:add :sub :neg]
            limit [:depth :work]]
      (testing (str operation " delayed descent / " limit)
        (let [leaf (c/mk-eval-rfl-proof lc)
              delayed (nth (iterate (fn [child]
                                      (case operation
                                        :add (c/mk-add-eval-proof lc lc child leaf)
                                        :sub (c/mk-sub-eval-proof lc lc child leaf)
                                        :neg (c/mk-neg-eval-proof lc child)))
                                    leaf) 40)
              work (atom 0)
              ex (binding [m/*work* work
                           m/*work-limit* (if (= limit :work) 12 1000)
                           m/*depth-limit* (if (= limit :depth) 8 128)]
                   (try (delayed atoms)
                        (catch clojure.lang.ExceptionInfo ex ex)))]
          (is (= {:kind :tactic-error :tactic :omega :limit limit
                  :value (if (= limit :work) 12 8)} (ex-data ex)))
          (is (> @work 1) "the guard is reached through recursive delayed children"))))))

(defn- wide-fm-problem []
  (reduce (fn [p i]
            (let [coeffs [1 i]
                  bounds (c/mk-constraint -100 100)]
              (c/add-constraint p (c/mk-fact coeffs bounds
                                             (c/justification-assumption i bounds coeffs)))))
          (c/mk-problem) (range 1 51)))

(deftest wide-fm-combinations-consume-work
  ;; Lean Core.fourierMotzkin pairs all 50 lower and 50 upper bounds on x.
  ;; Enter the real cross product; one unchecked step used to allocate all 2500.
  (let [p (wide-fm-problem)
        work (atom 0)
        combinations (atom 0)
        build c/justification-combo
        ex (binding [m/*work* work m/*work-limit* 120]
             (with-redefs [c/justification-combo (fn [& args]
                                                   (swap! combinations inc)
                                                   (apply build args))]
               (try (c/run-omega (m/mk-state) p no-proof no-proof)
                    (catch clojure.lang.ExceptionInfo ex ex))))]
    (is (= {:kind :tactic-error :tactic :omega :limit :work :value 120} (ex-data ex)))
    (is (pos? @combinations) "the positive budget reaches actual pair construction")
    (is (< @combinations 120) "the cross product cannot complete 2500 unchecked pairs")
    (is (= 121 @work))))

(deftest fm-classification-consumes-work
  (let [p (wide-fm-problem)
        work (atom 0)
        classified (atom 0)
        scale c/constraint-scale
        ex (binding [m/*work* work m/*work-limit* 5]
             (with-redefs [c/constraint-scale (fn [& args]
                                                (swap! classified inc)
                                                (apply scale args))]
               (try (c/fourier-motzkin-data p)
                    (catch clojure.lang.ExceptionInfo ex ex))))]
    (is (= {:kind :tactic-error :tactic :omega :limit :work :value 5} (ex-data ex)))
    (is (pos? @classified))
    (is (< @classified 100) "classification stops before traversing every fact/coordinate")
    (is (= 6 @work))))

(deftest unsupported-carrier-is-visited-before-useful-fact
  (a/load-init!)
  (let [events (atom [])
        add-fact f/add-fact
        theorem (first (filter #(= 'stage1_carrier (first %)) examples))]
    ;; Facts are popped from the end: h is deliberately declared after k. Observe
    ;; the real add-fact calls, without replacing the queue or the arithmetic.
    (with-redefs [f/add-fact
                  (fn [st table m {:keys [type proof] :as fact}]
                    (let [[head args] (e/get-app-fn-args type)
                          bool-eq? (and (e/const? head)
                                        (= (e/const-name head) (name/from-string "Eq"))
                                        (= 3 (count args))
                                        (= (first args) (const-expr "Bool")))
                          local-name (when (e/fvar? proof)
                                       (:name (red/lctx-lookup (:lctx st) (e/fvar-id proof))))
                          [table' m' n :as result] (add-fact st table m fact)]
                      (cond
                        bool-eq? (swap! events conj {:tag :unsupported :n n
                                                     :unchanged? (and (= table table') (= m m'))})
                        (= local-name "k") (swap! events conj {:tag :useful :n n}))
                      result))]
      (is (= :ok (cs/attempt theorem 60000))
          "the final kernel-checked arithmetic proof needs k : x ≤ y"))
    (is (= [:unsupported :useful] (mapv :tag @events)))
    (is (= 0 (:n (first @events))) "unsupported Bool equality contributes zero facts")
    (is (true? (:unchanged? (first @events))))
    (is (pos? (or (:n (second @events)) 0)) "the useful Nat fact is processed afterward")))

(deftest int-negation-certificates-use-int-universe
  (let [env @te/bundled-init-env
        int (const-expr "Int")
        x (e/fvar 123)
        st (tc/attach-lctx (tc/mk-tc-state env) (red/lctx-add-local {} 123 "x" int))
        neg (c/mk-int-neg x)
        [state _] (m/lookup (m/mk-state) x (constantly []))
        atoms (c/build-atoms-expr state)
        delayed (c/mk-neg-eval-proof (c/lc-coordinate 0) (c/mk-coordinate-eval-proof 0))
        result (delayed atoms)
        expected (e/app* (e/const' (name/from-string "Eq") [(lvl/succ lvl/zero)])
                         int (:lhs result) (:rhs result))]
    (is (= [lvl/zero] (e/const-levels (e/get-app-fn neg))))
    (is (tc/is-def-eq st int (tc/infer-type st neg)))
    (is (tc/is-def-eq st expected (tc/infer-type st (:proof result))))))

(deftest easy-equality-substitutions-and-copies-consume-work
  ;; Core.solveEasyEquality must account inside its fold, including the ci=0
  ;; copy path. Each positive budget permits some real work, never all 2500 facts.
  (doseq [coefficient [0 1]]
    (let [p (reduce (fn [p i] (c/add-inequality p 0 [coefficient i 1] nil no-proof))
                    (c/add-equality (c/mk-problem) 0 [1] nil no-proof)
                    (range 1 2501))
          work (atom 0)
          inserted (atom 0)
          combinations (atom 0)
          insert c/add-constraint
          combo c/justification-combo
          ex (binding [m/*work* work m/*work-limit* 12]
               (with-redefs [c/add-constraint (fn [& args]
                                                (swap! inserted inc)
                                                (apply insert args))
                             c/justification-combo (fn [& args]
                                                     (swap! combinations inc)
                                                     (apply combo args))]
                 (try (c/solve-equalities (m/mk-state) p no-proof no-proof)
                      (catch clojure.lang.ExceptionInfo ex ex))))]
      (is (= {:kind :tactic-error :tactic :omega :limit :work :value 12} (ex-data ex)))
      (is (pos? @inserted))
      (is (< @inserted 12))
      (is (if (zero? coefficient) (zero? @combinations) (pos? @combinations)))
      (is (= 13 @work)))))

(deftest quantified-int-goals-bypass-ground-decide
  (let [int (const-expr "Int")
        x (e/bvar 0)
        neg-x (e/app* (e/const' (name/from-string "Neg.neg") [lvl/zero])
                      int (const-expr "Int.instNegInt") x)
        body (e/app* (e/const' (name/from-string "Eq") [(lvl/succ lvl/zero)])
                     int (c/mk-int-add neg-x x) (e/app (const-expr "Int.ofNat") (e/lit-nat 0)))
        goal (e/forall' "x" int body :default)
        calls (atom 0)]
    (doseq [run [omega/omega f/omega]]
      (let [[ps _] (proof/start-proof @te/bundled-init-env goal)]
        (with-redefs [decide/decide (fn [_]
                                      (swap! calls inc)
                                      (throw (IllegalStateException. "quantified decide was attempted")))]
          (is (some? (extract/verify (run ps)))))))
    (is (zero? @calls))))
