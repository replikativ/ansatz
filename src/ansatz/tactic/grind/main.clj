(ns ansatz.tactic.grind.main
  "Logical refutation engine; Lean Grind/{Main,Finish,Intro,Core,Propagate}.lean, v4.33.1."
  (:require [ansatz.kernel.expr :as e]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.tc :as tc]
            [ansatz.kernel.reduce :as red]
            [ansatz.eqns :as eqns]
            [ansatz.matchers :as matchers]
            [ansatz.state :as state]
            [ansatz.tactic.basic :as basic]
            [ansatz.tactic.proof :as proof]
            [ansatz.tactic.grind.action :as action]
            [ansatz.tactic.grind.solvers :as solvers]
            [ansatz.tactic.grind.theorem :as theorem]
            [ansatz.tactic.grind.ctor :as ctor]
            [ansatz.tactic.grind.core :as core]
            [ansatz.tactic.grind.split :as split]
            [ansatz.tactic.grind.normalize :as normalize]
            [ansatz.tactic.grind.simp :as simp]
            [ansatz.tactic.grind.intro :as intro]
            [ansatz.tactic.grind.forall-prop :as forall-prop]
            [ansatz.tactic.grind.egraph :as eg]
            [ansatz.tactic.grind.proof :as gp]))

(defn- c [n] (e/const' (name/from-string n) []))
(def ^:private true-expr (c "True"))
(def ^:private false-expr (c "False"))
(defn- app [n & args] (reduce e/app (c n) args))
(defn- neg [p] (e/app (c "Not") p))
(defonce ^:private next-lambda-id (atom -1000))
(defn- lambda [p f]
  (let [id (swap! next-lambda-id dec)]
    (e/lam "h" p (e/abstract1 (f (e/fvar id)) id) :default)))
(defn- false-elim [p h] (e/app* (e/const' (name/from-string "False.elim") [lvl/zero]) p h))
(defn- eq-mp [p q h hp]
  (e/app* (e/const' (name/from-string "Eq.mp") [lvl/zero]) p q h hp))
(defn- prop-eq [p q forward backward]
  (app "propext" p q (app "Iff.intro" p q forward backward)))
(defn- eq-true [p hp]
  (prop-eq p true-expr (lambda p (fn [_] (c "True.intro")))
           (lambda true-expr (fn [_] hp))))
(defn- eq-false [p hn]
  (prop-eq p false-expr hn (lambda false-expr #(false-elim p %))))

(defn- known [branch p]
  (let [gs (:graph branch) st (:tc branch)]
    (cond
      (= p true-expr) {:yes (c "True.intro")}
      (= p false-expr) {:no (lambda false-expr identity)}
      (get-in branch [:facts p]) {:yes (get-in branch [:facts p :proof])}
      (and (eg/get-enode gs p) (eg/is-eq-true gs p))
      {:yes (eq-mp true-expr p (gp/mk-eq-proof gs st true-expr p) (c "True.intro"))}
      (and (eg/get-enode gs p) (eg/is-eq-false gs p))
      {:no (lambda p #(eq-mp p false-expr (gp/mk-eq-proof gs st p false-expr) %))})))

(defn truth
  "Proof-producing propositional propagation (Propagate.lean). No graph flag is a proof."
  ([branch p] (truth branch p #{}))
  ([branch p visited]
   (or (known branch p)
       (when (and (not (contains? visited p)) (or (e/app? p) (e/forall? p)))
         (let [visited (conj visited p)
               recur-truth #(truth branch % visited)
               [h args] (e/get-app-fn-args p)
               head (when (e/const? h) (name/->string (e/const-name h)))
               [a b] args]
           (case head
             "Eq" (let [[_ a b] args gs (:graph branch)]
                    (when (and (eg/get-enode gs a) (eg/get-enode gs b) (eg/is-eqv gs a b))
                      {:yes (gp/mk-eq-proof gs (:tc branch) a b)}))
             "Not" (let [{:keys [yes no]} (recur-truth a)]
                     (cond no {:yes no}
                           yes {:no (lambda p #(e/app % yes))}))
             "And" (let [ta (recur-truth a) tb (recur-truth b)]
                     (cond
                       (and (:yes ta) (:yes tb)) {:yes (app "And.intro" a b (:yes ta) (:yes tb))}
                       (:no ta) {:no (lambda p #(e/app (:no ta) (app "And.left" a b %)))}
                       (:no tb) {:no (lambda p #(e/app (:no tb) (app "And.right" a b %)))}))
             "Or" (let [ta (recur-truth a) tb (recur-truth b)]
                    (cond
                      (:yes ta) {:yes (app "Or.inl" a b (:yes ta))}
                      (:yes tb) {:yes (app "Or.inr" a b (:yes tb))}
                      (and (:no ta) (:no tb))
                      {:no (lambda p #(app "Or.elim" a b false-expr % (:no ta) (:no tb)))}))
             "Iff" (let [ta (recur-truth a) tb (recur-truth b)]
                     (cond
                       (and (:yes ta) (:yes tb))
                       {:yes (app "Iff.intro" a b (lambda a (fn [_] (:yes tb)))
                                  (lambda b (fn [_] (:yes ta))))}
                       (and (:no ta) (:no tb))
                       {:yes (app "Iff.intro" a b (lambda a #(false-elim b (e/app (:no ta) %)))
                                  (lambda b #(false-elim a (e/app (:no tb) %))))}
                       (and (:yes ta) (:no tb))
                       {:no (lambda p #(e/app (:no tb) (e/app (app "Iff.mp" a b %) (:yes ta))))}
                       (and (:no ta) (:yes tb))
                       {:no (lambda p #(e/app (:no ta) (e/app (app "Iff.mpr" a b %) (:yes tb))))}))
             (when (and (e/forall? p) (zero? (e/bvar-range (e/forall-body p)))
                        (theorem/prop? (:tc branch) (e/forall-type p)))
               (let [a (e/forall-type p) b (e/forall-body p)
                     ta (recur-truth a) tb (recur-truth b)]
                 (cond (:yes tb) {:yes (lambda a (fn [_] (:yes tb)))}
                       (:no ta) {:yes (lambda a #(false-elim b (e/app (:no ta) %)))}
                       (and (:yes ta) (:no tb)) {:no (lambda p #(e/app (:no tb) (e/app % (:yes ta))))})))))))))

(defn- enqueue [branch p hp gen]
  (if (get-in branch [:facts p]) branch
      (update branch :raw-facts conj {:prop p :proof hp :gen gen})))

(defn- by-cases [p q yes no]
  (app "Classical.byCases" p q (lambda p yes) (lambda (neg p) no)))

(defn- propagate-negation [branch p hn gen]
  ;; Propagate.lean / ForallProp.lean: refuting logical connectives emits
  ;; ordinary checked propositions; fresh lambda locals never enter the graph.
  (let [[h args] (e/get-app-fn-args p)
        head (when (e/const? h) (name/->string (e/const-name h)))
        [a b] args]
    (if-let [fact (or (forall-prop/propagate-forall-prop-down (:tc branch) p hn gen)
                      (forall-prop/propagate-exists-down (:tc branch) p hn gen))]
      (enqueue branch (:prop fact) (:proof fact) (:gen fact))
      (case head
        "Not" (enqueue branch a
                       (app "Decidable.byContradiction" a (app "Classical.propDecidable" a) hn) gen)
        "And" (let [result (app "Or" (neg a) (neg b))
                    hp (by-cases a result
                                 (fn [ha] (app "Or.inr" (neg a) (neg b)
                                               (lambda b #(e/app hn (app "And.intro" a b ha %)))))
                                 (fn [hna] (app "Or.inl" (neg a) (neg b) hna)))]
                (enqueue branch result hp gen))
        "Or" (-> branch
                 (enqueue (neg a) (lambda a #(e/app hn (app "Or.inl" a b %))) gen)
                 (enqueue (neg b) (lambda b #(e/app hn (app "Or.inr" a b %))) gen))
        "Iff" (let [left (app "And" a (neg b)) right (app "And" (neg a) b)
                    result (app "Or" left right)
                    hp (by-cases a result
                                 (fn [ha]
                                   (by-cases b result
                                             (fn [hb] (false-elim result
                                                                  (e/app hn (app "Iff.intro" a b
                                                                                 (lambda a (fn [_] hb))
                                                                                 (lambda b (fn [_] ha))))))
                                             (fn [hnb] (app "Or.inl" left right (app "And.intro" a (neg b) ha hnb)))))
                                 (fn [hna]
                                   (by-cases b result
                                             (fn [hb] (app "Or.inr" left right (app "And.intro" (neg a) b hna hb)))
                                             (fn [hnb] (false-elim result
                                                                   (e/app hn (app "Iff.intro" a b
                                                                                  (lambda a #(false-elim b (e/app hna %)))
                                                                                  (lambda b #(false-elim a (e/app hnb %))))))))))]
                (enqueue branch result hp gen))
        (if (and (e/forall? p) (zero? (e/bvar-range (e/forall-body p)))
                 (theorem/prop? (:tc branch) (e/forall-type p)))
          (let [a (e/forall-type p) b (e/forall-body p)
                hp (app "Decidable.byContradiction" a (app "Classical.propDecidable" a)
                        (lambda (neg a) (fn [hna] (e/app hn (lambda a #(false-elim b (e/app hna %)))))))
                hnq (lambda b (fn [hb] (e/app hn (lambda a (fn [_] hb)))))]
            (-> branch (enqueue a hp gen) (enqueue (neg b) hnq gen))) branch)))))

(defn- internalize-proposition [gs prop gen]
  ;; Internalize.lean internalizeImpl (.forallE): expose the domain and a closed
  ;; body. In particular, an instantiated premise p (f a) must join p b's class
  ;; before ForallProp propagation reconstructs its proof modulo f a = b.
  (let [gs (eg/internalize gs prop gen)]
    (if (e/forall? prop)
      (cond-> (internalize-proposition gs (e/forall-type prop) gen)
        (zero? (e/bvar-range (e/forall-body prop)))
        (internalize-proposition (e/forall-body prop) gen)) gs)))

(defn- assert-fact [branch {:keys [prop proof gen]}]
  (if (get-in branch [:facts prop]) branch
      (let [gs (internalize-proposition (:graph branch) prop gen)
            branch (-> branch (assoc :graph gs) (assoc-in [:facts prop] {:proof proof :gen gen}))
            [h args] (e/get-app-fn-args prop)
            head (when (e/const? h) (name/->string (e/const-name h)))
            branch (assoc branch :graph (eg/assert-eq gs prop true-expr (eq-true prop proof)))
          ;; ForallProp.propagateForallPropDown/addLocalEMatchTheorems: activate
          ;; whenever a quantified fact becomes true, including cases and derived
          ;; facts. Pattern unavailability leaves the fact intact; no catch hides
          ;; malformed metadata. The persistent branch owns theorem activation.
            branch (if (e/forall? prop)
                     (if-let [thm (theorem/compile-theorem (:tc branch)
                                                           (if (e/fvar? proof) [:local (e/fvar-id proof)]
                                                               [:local-fact prop])
                                                           proof prop [])]
                       (update branch :theorems conj (assoc thm :gen gen)) branch)
                     branch)]
        (case head
          "Eq" (let [[_ a b] args]
                 (update branch :graph #(-> % (eg/internalize a gen) (eg/internalize b gen)
                                            (eg/assert-eq a b proof))))
          "Not" (let [p (first args)]
                  (-> branch
                      (update :graph #(-> % (eg/internalize p gen)
                                          (eg/assert-eq p false-expr (eq-false p proof))))
                      (propagate-negation p proof gen)))
          "And" (let [[p q] args]
                  (-> branch (enqueue p (app "And.left" p q proof) gen)
                      (enqueue q (app "And.right" p q proof) gen)))
          "Iff" (let [[p q] args]
                  (-> branch (enqueue (e/arrow p q) (app "Iff.mp" p q proof) gen)
                      (enqueue (e/arrow q p) (app "Iff.mpr" p q proof) gen)))
          branch))))

(defn- drain [branch]
  ;; Intro.assertAll / Core.processNewFactsImpl: every new fact goes through one queue.
  (loop [branch branch]
    (if (or (get-in branch [:graph :inconsistent]) (empty? (:raw-facts branch))) branch
        (let [fact (first (:raw-facts branch))
              branch (update branch :raw-facts subvec 1)]
          (recur (assert-fact branch fact))))))

(defn- propagate [branch]
  (let [branch (-> branch (update :graph normalize/propagate (:tc branch))
                   (update :graph simp/preprocess (:tc branch)))
        branch (normalize/propagate-decide-up branch truth)
        branch (normalize/propagate-decide-down branch truth)
        branch (normalize/propagate-ite branch truth)
        branch (normalize/activate-comparison-theorems branch)
        branch (split/activate-intro-theorems branch)
        branch (if (and (not (:normalization-theorems-active branch))
                        (seq (get-in branch [:graph :app-map (name/from-string "Nat.le")])))
                 (-> branch (assoc :normalization-theorems-active true)
                     (update :theorems into (simp/normalization-theorems (:tc branch)))) branch)
        constructors (ctor/propagate (:graph branch) (:tc branch) (:ctor-seen branch))
        branch (-> branch (assoc :ctor-seen (:seen constructors))
                   (update :raw-facts into (:facts constructors)))
        branch (reduce
                (fn [branch [p {:keys [proof gen]}]]
                  (let [[h args] (e/get-app-fn-args p)
                        head (when (e/const? h) (name/->string (e/const-name h)))]
                    (cond
                      (and (e/forall? p) (zero? (e/bvar-range (e/forall-body p))))
                      (if-let [hp (:yes (truth branch (e/forall-type p)))]
                        (enqueue branch (e/forall-body p) (e/app proof hp) gen)
                        (if-let [hnb (:no (truth branch (e/forall-body p)))]
                          (if-let [fact (forall-prop/eq-false-of-imp-eq-true (:tc branch) p proof hnb gen)]
                            (enqueue branch (:prop fact) (:proof fact) (:gen fact)) branch) branch))
                      (= head "Or")
                      (let [[a b] args ta (truth branch a) tb (truth branch b)]
                        (cond
                          (:no ta) (enqueue branch b
                                            (app "Or.elim" a b b proof
                                                 (lambda a #(false-elim b (e/app (:no ta) %)))
                                                 (lambda b identity)) gen)
                          (:no tb) (enqueue branch a
                                            (app "Or.elim" a b a proof (lambda a identity)
                                                 (lambda b #(false-elim a (e/app (:no tb) %)))) gen)
                          :else branch))
                      :else branch))) branch (:facts branch))]
    ;; Recompute each parent's logical value from its children. Hiding only the
    ;; parent avoids using its asserted truth to justify that same truth.
    (reduce (fn [b [p node]]
              ;; Core.lean stops propagating as soon as the graph is inconsistent;
              ;; the driver reconstructs False before processing further facts.
              (if (get-in b [:graph :inconsistent]) (reduced b)
                  (let [view (-> b (update :facts dissoc p) (update-in [:graph :enodes] dissoc p))
                        value (truth view p)
                        gs (:graph b)]
                    (cond
                      (and (eg/is-eq-false gs p)
                           (or (e/forall? p)
                               (let [[h _] (e/get-app-fn-args p)]
                                 (and (e/const? h) (= "Exists" (name/->string (e/const-name h)))))))
                      (propagate-negation b p (:no (known b p)) (:gen node))
                  ;; Propagate.lean propagateEqDown (and other down propagators):
                  ;; a proposition that joins True needs assertion too. In particular
                  ;; Nat.beq_eq can make a=b true before its endpoints are merged.
                      (and (eg/is-eq-true gs p) (not (get-in b [:facts p])))
                      (enqueue b p (:yes (known b p)) (:gen node))
                      (and (:yes value) (not (eg/is-eq-true gs p)))
                      (enqueue b p (:yes value) (:gen node))
                      (and (:no value) (not (eg/is-eq-false gs p)))
                      (update b :graph eg/assert-eq p false-expr (eq-false p (:no value)))
                      :else b)))) branch (:enodes (:graph branch)))))

(defn- contradiction [branch]
  (or (get-in branch [:facts false-expr :proof])
      (when-let [[a b] (get-in branch [:graph :value-conflict])]
        (core/close-goal-with-values-eq (:graph branch) (:tc branch) a b))
      (when (eg/is-eqv (:graph branch) true-expr false-expr)
        (eq-mp true-expr false-expr (gp/mk-eq-proof (:graph branch) (:tc branch) true-expr false-expr)
               (c "True.intro")))
      (some (fn [[p {:keys [proof]}]]
              (when-let [hn (:no (truth (-> branch (update :facts dissoc p)
                                            (update-in [:graph :enodes] dissoc p)) p))]
                (e/app hn proof))) (:facts branch))))

(defn- instantiate [branch]
  (let [config (:config branch)
        instances (for [thm (:theorems branch)
                        m (theorem/matches (:graph branch) thm config)
                        :let [fact (theorem/instantiate (:tc branch) thm m #(:yes (truth branch %)))]
                        :when (and fact (not (contains? (:seen branch) (:key fact)))
                                   (not (get-in branch [:facts (:prop fact)])))] fact)]
    (if (and (seq instances) (< (:rounds branch) (:ematch config)))
      (do (action/budget! config :ematch (:rounds branch))
          (reduce (fn [b fact]
                    (if (or (contains? (:seen b) (:key fact)) (get-in b [:facts (:prop fact)])) b
                        (do (action/budget! config :instances (:num-instances b))
                            (-> b (update :seen conj (:key fact)) (update :num-instances inc)
                                (update :raw-facts conj fact)))))
                  (update branch :rounds inc) instances)) branch)))

(defn- check-exhausted! [branch]
  (let [config (:config branch)
        pending (for [thm (:theorems branch)
                      m (theorem/matches (:graph branch) thm (assoc config :gen Long/MAX_VALUE))
                      :let [fact (theorem/instantiate (:tc branch) thm m #(:yes (truth branch %)))]
                      :when (and fact (not (contains? (:seen branch) (:key fact)))
                                 (not (get-in branch [:facts (:prop fact)])))] m)]
    (when (some #(>= (:gen %) (:gen config)) pending)
      (action/budget! config :gen (:gen config)))
    (when (seq pending) (action/budget! config :ematch (:rounds branch)))))

(defn- split-candidate [branch]
  ;; Split.checkDisjunctStatus: an asserted disjunction is ready until a disjunct holds.
  (or (some (fn [[p {:keys [proof gen]}]]
              (let [[h args] (e/get-app-fn-args p)]
                (when (and (e/const? h) (= "Or" (name/->string (e/const-name h)))
                           (not (contains? (:resolved branch) p))
                           (not-any? #(:yes (truth branch %)) args))
                  {:kind :or :expr p :args args :proof proof :gen gen}))) (:facts branch))
      ;; Init/Grind/Config.lean splitImp defaults to false. Downward implication
      ;; propagation remains unconditional; arbitrary implication splitting is
      ;; opt-in, avoiding speculative splits on every residual E-match premise.
      (when (get-in branch [:config :split-imp]) (split/check-forall-status branch truth))
      (some (fn [[expr node]]
              (when (normalize/bool-rec? expr)
                (let [cond (last (e/get-app-args expr))]
                  (when-not (normalize/bool-value (:graph branch) cond)
                    {:kind :bool :expr cond :gen (:gen node)}))))
            (:enodes (:graph branch)))
      ;; Surface Nat comparisons are Bool-valued rather than Lean's decide
      ;; terms. Expose their values with the existing checked Bool case split.
      (some (fn [[expr node]]
              (let [[h args] (e/get-app-fn-args expr)]
                (when (and (e/const? h) (= 2 (count args))
                           (contains? #{"Nat.blt" "Nat.ble" "Nat.beq"}
                                      (name/->string (e/const-name h)))
                           (not (normalize/bool-value (:graph branch) expr)))
                  {:kind :bool :expr expr :gen (:gen node)})))
            (:enodes (:graph branch)))
      ;; Split.checkIteCondStatus: split a conditional whose condition is still unknown.
      (some (fn [[expr node]]
              (let [[h args] (e/get-app-fn-args expr)]
                (when (and (e/const? h) (<= 5 (count args))
                           (contains? #{"ite" "dite"} (name/->string (e/const-name h)))
                           (not (contains? (:resolved branch) expr))
                           (not (seq (truth branch (second args)))))
                  {:kind :imp :expr expr :args [(second args)] :gen (:gen node)})))
            (:enodes (:graph branch)))
      (split/check-default-split-status branch truth)))

(declare solve)

(defn- split-next [branch candidate]
  ;; Split.splitCore: first nonrecursive alternative is free; subsequent ones count.
  ;; Every fork retains the persistent graph and uses distinct local proof contexts.
  (if (= :inductive (:kind candidate)) (split/split-core branch candidate solve)
      (let [{:keys [expr args proof gen]} candidate
            [a b] args config (:config branch)
            _ (action/budget! config :splits (:num-splits branch))
            solve-alt (fn [p extra]
                        (let [[ps id] (proof/alloc-id (:ps branch))
                              fv (e/fvar id)
                              st (tc/attach-lctx (tc/mk-tc-state (:env ps))
                                                 (red/lctx-add-local (:lctx (:tc branch)) id "h" p))
                              branch (-> branch (assoc :ps ps :tc st :rounds 0)
                                         (update :resolved conj expr)
                                         (update :num-splits + extra)
                                         (enqueue p fv (inc gen)))
                              hfalse (solve branch)]
                          (e/lam "h" p (e/abstract1 hfalse id) :default)))]
        (case (:kind candidate)
          :or (app "Or.elim" a b false-expr proof (solve-alt a 0) (solve-alt b 1))
          :imp (app "Classical.byCases" a false-expr (solve-alt a 0) (solve-alt (neg a) 1))
          (let [bool-type (c "Bool")
                eq-bool (e/const' (name/from-string "Eq") [(lvl/succ lvl/zero)])
                false-case (e/app* eq-bool bool-type expr (c "Bool.false"))
                true-case (e/app* eq-bool bool-type expr (c "Bool.true"))
                motive (e/lam "b" bool-type
                              (e/arrow (e/app* eq-bool bool-type expr (e/bvar 0)) false-expr) :default)
                refl (gp/mk-eq-refl (:tc branch) expr)]
            (e/app* (e/const' (name/from-string "Bool.rec") [lvl/zero]) motive
                    (solve-alt false-case 0) (solve-alt true-case 1) expr refl))))))

(defn solve [branch]
  ;; Finish.mkFinish: fixed-point propagation, solvers <|> instantiate <|> splitNext.
  (loop [branch branch iteration 0]
    (when (.isInterrupted (Thread/currentThread)) (action/fail! "interrupted" {}))
    (action/budget! (:config branch) :iterations iteration)
    (let [branch (drain branch)]
      (if-let [hfalse (contradiction branch)] hfalse
              (if-let [existential (intro/candidate branch)]
                (intro/eliminate branch existential solve)
                (let [next (drain (propagate branch))]
                  (if (or (not= (:facts branch) (:facts next))
                          (not= (:theorems branch) (:theorems next))
                          (not= (get-in branch [:graph :gmt]) (get-in next [:graph :gmt])))
                    (recur next (inc iteration))
                    (if-let [hfalse (solvers/check branch)] hfalse
                            (let [next (instantiate branch)]
                              (if (seq (:raw-facts next))
                                (recur next (inc iteration))
                                (if-let [candidate (split-candidate branch)]
                                  (split-next branch candidate)
                                  (do (check-exhausted! branch)
                                      (action/fail! "stuck" {:facts (vec (keys (:facts branch)))
                                                             :rounds (:rounds branch) :instances (:num-instances branch)})))))))))))))

(defn- introduce [ps]
  (loop [ps ps]
    (let [goal (proof/current-goal ps)
          st (tc/attach-lctx (tc/mk-tc-state (:env ps)) (:lctx goal))
          type (#'tc/cached-whnf st (:type goal))]
      (if (e/forall? type) (recur (basic/intro ps)) ps))))

(defn- grind-goal
  "Stage 2 entry point. Retains one proof-producing graph per branch.
   Definition hints expand through the checked equation inventory."
  ([ps hints options]
   (let [config (action/configure options)
         ps (introduce ps)
         goal (proof/current-goal ps)
         st (tc/attach-lctx (tc/mk-tc-state (:env ps)) (:lctx goal))
         target (:type goal)
         _ (when-not (theorem/prop? st target) (action/fail! "target is not a proposition" {:target target}))
         ;; Intro.intro: byContra after introducing binders; the continuation is a real term.
         [ps id] (proof/alloc-id ps)
         hn (e/fvar id)
         st (tc/attach-lctx (tc/mk-tc-state (:env ps)) (red/lctx-add-local (:lctx goal) id "hnot" (neg target)))
         theorems (into [] (mapcat #(theorem/for-hint st %)) hints)
         gs (assoc (eg/mk-grind-state (:env ps)) :proof-producing? true :simp-context (simp/mk-context st))
         gs (reduce #(eg/internalize %1 %2 0) gs [(c "Bool.true") (c "Bool.false")
                                                  (e/lit-nat 0) (c "Ordering.eq") target])
         branch {:ps ps :tc st :graph gs :config config :facts {} :raw-facts []
                 :theorems theorems :seen #{} :rounds 0 :num-instances 0 :num-splits 0 :resolved #{} :ctor-seen #{} :exists-seen #{}}
         branch (reduce (fn [b [fid decl]]
                          (if (and (= :local (:tag decl)) (theorem/prop? st (:type decl)))
                            (enqueue b (:type decl) (e/fvar fid) 0) b))
                        branch (:lctx goal))
         hfalse (solve (if (= target false-expr) branch (enqueue branch (neg target) hn 0)))
         term (if (= target false-expr) hfalse
                  (app "Decidable.byContradiction" target (app "Classical.propDecidable" target)
                       (e/lam "hnot" (neg target) (e/abstract1 hfalse id) :default)))]
     (proof/assign-mvar ps (:id goal) {:kind :exact :term term}))))

(defn grind
  "Run the refutation engine independently on each open goal. The executable
   surface historically applies grind after induction to all generated goals;
   this is Lean's `all_goals grind`, with no exception swallowing."
  ([ps] (grind ps [] {}))
  ([ps hints] (grind ps hints {}))
  ([ps hints options]
   ;; the Nat.ble/Nat.beq Bool bridges grind activates (normalize/activate-comparison-theorems)
   ;; must exist in the env; derive Nat.ble_eq when the env lacks it, as simp does
   (binding [action/*config* (action/configure options)
             simp/*state* (simp/mk-state)]
     (let [ensure (requiring-resolve 'ansatz.tactic.simp/ensure-ble-eq)
           ps (if-let [env' (ensure (:env ps))] (assoc ps :env env') ps)
           ;; Lean Grind/EMatchTheorem asks Meta.Match for matcher equations
           ;; when a matcher definition is supplied as a hint.
           ps (reduce (fn [ps hint]
                        (let [nm (str hint)]
                          (if (and (matchers/matcher-info (:env ps) nm)
                                   (not (seq (eqns/eqns-for (:env ps) nm)))
                                   (env/lookup @state/ansatz-env (name/from-string nm)))
                            (do ((requiring-resolve 'ansatz.tactic.match-eqns/get-equations-for) nm)
                                (assoc ps :env @state/ansatz-env))
                            ps)))
                      ps hints)]
       (reduce (fn [ps gid]
                 (if (proof/mvar-assigned? ps gid) ps
                     (grind-goal (assoc ps :goals (into [gid] (remove #{gid} (:goals ps)))) hints options)))
               ps (:goals ps))))))
