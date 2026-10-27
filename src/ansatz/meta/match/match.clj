(ns ansatz.meta.match.match
  "Lean/Meta/Match/Match.lean, withAlts, process transitions, solveCnstrs,
   mkMatcherAuxDefinition and mkMatcher (55f80e10a3). The process worklist
   makes Lean's withIncRecDepth guard explicit without consuming JVM frames."
  (:require [ansatz.kernel.expr :as e]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.tc :as tc]
            [ansatz.meta.fvar-subst :as subst]
            [ansatz.meta.constructions.util :as u]
            [ansatz.meta.tactic.cases :as c]
            [ansatz.meta.match.basic :as b]
            [ansatz.meta.match.matcher-info :as mi]
            [ansatz.meta.match.case-values :as cv]))

(defn- with-alt-locals! [ctx alt]
  (c/set-lctx! ctx (reduce (fn [lctx d] (assoc lctx (:id d) d)) (:lctx @ctx) (:fvar-decls alt))))

(defn with-eqs [ctx lhs rhs discr-infos]
  (vec (keep (fn [[a b info]]
               (when-let [h (:h-name? info)] (u/local-decl ctx h (u/mk-eq-heq ctx a b))))
             (map vector lhs rhs discr-infos))))

(defn with-alts [ctx motive discrs discr-infos lhss]
  (let [base (:lctx @ctx)]
    (loop [lhss (seq lhss) alts [] minors [] infos []]
      (if-let [lhs (first lhss)]
        (do
          (c/set-lctx! ctx (reduce (fn [lctx d] (assoc lctx (:id d) d))
                                  (reduce (fn [lctx m] (assoc lctx (e/fvar-id m) (u/decl ctx m))) base minors)
                                  (:fvar-decls lhs)))
          (let [xs (mapv (comp e/fvar :id) (:fvar-decls lhs))
                args (mapv b/pattern-to-expr (:patterns lhs))
                eqs (with-eqs ctx discrs args discr-infos)
                type (u/mk-forall-fvars ctx xs (u/mk-forall-fvars ctx eqs (u/app motive args)))
                unit? (and (empty? xs) (empty? eqs))
                type (if unit? (u/mk-arrow ctx (u/const' "Unit" []) type) type)
                ;; Pattern variables are bound in the minor's type, not captured parameters.
                _ (c/set-lctx! ctx (apply dissoc (:lctx @ctx) (map e/fvar-id (concat xs eqs))))
                minor (u/local-decl ctx (str "h_" (inc (count alts))) type)
                rhs (u/app minor (if unit? [(u/const' "Unit.unit" [])] xs))
                alt (b/alt (:ref lhs) (count alts) rhs (:fvar-decls lhs) (:patterns lhs))]
            (recur (next lhss) (conj alts alt) (conj minors minor)
                   (conj infos (mi/alt-param-info (count xs) 0 unit?)))))
        {:alts alts :minors minors :alt-infos infos}))))

(defn solve-cnstrs [ctx state id alt]
  (c/with-goal! ctx id)
  (let [base (:lctx @ctx)]
    (loop [alt alt]
      (c/set-lctx! ctx base)
      (with-alt-locals! ctx alt)
      (let [local? #(and (e/fvar? %) (b/alt-is-local-decl (e/fvar-id %) alt))
            cnstrs (mapv (fn [[a b]] (if (or (local? b) (and (not (e/fvar? a)) (e/fvar? b))) [b a] [a b]))
                         (:cnstrs alt))
            solution (first (keep-indexed
                             (fn [i [a b]]
                               (when (and (local? a) (not (c/depends-on? b (e/fvar-id a)))
                                          (tc/is-def-eq @ctx (u/infer-type ctx a) (u/infer-type ctx b)))
                                 [i (e/fvar-id a) b])) cnstrs))]
        (if solution
          (let [[i id v] solution]
            (recur (b/alt-replace-fvar-id id v
                                        (assoc alt :cnstrs (into (subvec cnstrs 0 i) (subvec cnstrs (inc i)))))))
          (let [remaining (filterv (fn [[a b]] (not (or (tc/is-def-eq @ctx a b) (e/fvar? a)))) cnstrs)
                rhs (c/zonk ctx (:rhs alt))]
            (when (seq remaining)
              (c/tactic-error! "Dependent match elimination failed: could not solve constraints"
                               {:constraints remaining :alternative (:idx alt)}))
            (when-not (tc/is-def-eq @ctx (c/goal-type ctx id) (u/infer-type ctx rhs))
              (c/tactic-error! "Dependent elimination failed: alternative type mismatch"
                               {:expected (c/goal-type ctx id) :actual (u/infer-type ctx rhs)
                                :alternative (:idx alt)}))
            (c/set-lctx! ctx base)
            (c/assign! ctx id rhs)
            (swap! state update :used conj (:idx alt))))))))

(defn- record-overlaps! [state winner others]
  (doseq [other others]
    (swap! state update :overlaps mi/overlaps-insert (:idx winner) (:idx other))))

(defn process-leaf [ctx state p]
  (if-let [alt (first (:alts p))]
    (do (solve-cnstrs ctx state (:mvar-id p) alt)
        (record-overlaps! state alt (rest (:alts p))))
    (swap! state update :counter-examples conj (:examples p))))

(defn process-ex-falso [ctx p]
  (let [id (:mvar-id p) target (c/goal-type ctx id)
        child (c/fresh-mvar! ctx (u/const' "False" []))]
    (c/assign! ctx id (u/app (u/const' "False.elim" [(u/get-level ctx target)])
                             [target (e/mvar child)]))
    (assoc p :mvar-id child)))

(defn- done? [pat var] (and (= :inaccessible (:tag pat)) (= (:e pat) var)))
(defn- first-pat [alt] (first (:patterns alt)))
(defn- has-pattern [p tag] (some #(= tag (:tag (first-pat %))) (:alts p)))
(defn- refutable? [p]
  (case (:tag p) (:var :inaccessible) false :as (refutable? (:p p)) true))
(defn has-independent-patterns [p]
  (some (fn [alt]
          (loop [vars (:vars p) pats (:patterns alt)]
            (when-let [pat (first pats)]
              (cond (done? pat (first vars)) (recur (rest vars) (rest pats))
                    (#{:var :inaccessible :as} (:tag pat)) true
                    :else false)))) (:alts p)))

(defn process-independent-patterns [ctx p]
  (let [base (:lctx @ctx)]
    (update p :alts
            (fn [alts]
              (mapv (fn [alt]
                      (c/set-lctx! ctx base)
                      (with-alt-locals! ctx alt)
                      (let [n (count (take-while true? (map done? (:patterns alt) (:vars p))))
                            pat (get (:patterns alt) n) v (get (:vars p) n)
                            prefix (mapv b/inaccessible (take (inc n) (:vars p)))]
                        (case (:tag pat)
                          :inaccessible (-> alt
                                            (assoc :patterns (into prefix (drop (inc n) (:patterns alt))))
                                            (update :cnstrs conj [v (:e pat)]))
                          :var (let [id (:fvar-id pat)
                                     alt (assoc alt :patterns (into prefix (drop (inc n) (:patterns alt))))]
                                 (if (tc/is-def-eq @ctx (u/infer-type ctx (e/fvar id)) (u/infer-type ctx v))
                                   (b/alt-replace-fvar-id id v alt)
                                   (update alt :cnstrs conj [(e/fvar id) v])))
                          :as (assoc-in (b/alt-replace-fvar-id
                                         (:h-id pat) (u/mk-eq-refl ctx v)
                                         (b/alt-replace-fvar-id (:var-id pat) v alt))
                                        [:patterns n] (:p pat))
                          alt))) alts)))))

(defn- drop-first-var [p]
  (-> p (update :vars #(vec (rest %)))
      (update :alts #(mapv (fn [alt] (update alt :patterns (comp vec rest))) %))))

(defn- move-to-front [p i]
  (let [move (fn [xs] (into [(nth xs i)] (concat (take i xs) (drop (inc i) xs))))]
    (-> p (update :vars move) (update :alts #(mapv (fn [alt] (update alt :patterns move)) %)))))

(defn expand-nat-value-pattern [ctx p]
  (update p :alts
          #(mapv (fn [alt]
                   (let [pat (first-pat alt)]
                     (if (and (= :val (:tag pat)) (some? (cv/get-nat-value? ctx (:e pat))))
                       (assoc-in alt [:patterns 0]
                                 (let [n (cv/get-nat-value? ctx (:e pat))]
                                   (if (zero? n) (b/ctor (name/from-string "Nat.zero") [] [] [])
                                       (b/ctor (name/from-string "Nat.succ") [] [] [(b/val-pattern (e/lit-nat (dec n)))]))))
                       alt))) %)))

(defn- constructor-app? [ctx x]
  (#'c/constructor-app? ctx x))

(defn process-non-variable [ctx p]
  (let [x (first (:vars p)) xs (vec (rest (:vars p)))
        ctor (constructor-app? ctx x)]
    (if (and ctor (has-pattern p :ctor))
      (let [fields (subvec (:args ctor) (.numParams (:info ctor)))
            alts (keep (fn [alt]
                         (let [pat (first-pat alt) ps (rest (:patterns alt))]
                           (case (:tag pat)
                             :ctor (when (= (:ctor-name pat) (.name (:info ctor)))
                                     (assoc alt :patterns (into (:fields pat) ps)))
                             :inaccessible (assoc alt :patterns (into (mapv b/inaccessible fields) ps))))) (:alts p))]
        (assoc p :vars (into fields xs) :alts (vec alts)))
      (-> p (assoc :vars xs)
          (update :alts #(mapv (fn [alt]
                                (let [pat (first-pat alt)]
                                  (cond-> (update alt :patterns (comp vec rest))
                                    (not= :inaccessible (:tag pat))
                                    (update :cnstrs conj [x (b/pattern-to-expr pat)])))) %))))))

(defn process-constructor [ctx p]
  (let [x (first (:vars p)) xs (vec (rest (:vars p)))
        subgoals (c/cases ctx (:mvar-id p) (e/fvar-id x))]
    (mapv (fn [{:keys [mvar-id ctor-name fields subst]}]
            (let [alts (filterv (fn [alt] (let [pat (first-pat alt)]
                                           (or (= :inaccessible (:tag pat)) (= ctor-name (:ctor-name pat))))) (:alts p))
                  alts (mapv #(b/alt-apply-fvar-subst subst %) alts)
                  alts (mapv (fn [alt]
                               (let [pat (first-pat alt)]
                                 (assoc alt :patterns
                                        (into (if (= :ctor (:tag pat)) (:fields pat) (mapv b/inaccessible fields))
                                              (rest (:patterns alt)))))) alts)
                  ex {:tag :ctor :ctor-name ctor-name
                      :xs (mapv #(if (e/fvar? %) {:tag :var :fvar-id (e/fvar-id %)} {:tag :underscore}) fields)}]
              (assoc p :mvar-id mvar-id :vars (mapv #(subst/apply subst %) (concat fields xs)) :alts alts
                     :examples (mapv #(b/example-apply-fvar-subst subst
                                                                 (b/example-replace-fvar-id (e/fvar-id x) ex %)) (:examples p)))))
          subgoals)))

(defn process-value [ctx p]
  (let [x (first (:vars p)) xs (vec (rest (:vars p)))
        values (vec (distinct (keep #(let [pat (first-pat %)] (when (= :val (:tag pat)) (:e pat))) (:alts p))))
        complete? (and (seq (:alts p)) (every? (complement refutable?) (:patterns (last (:alts p)))))
        subgoals (cv/case-values ctx (:mvar-id p) (e/fvar-id x) values (not complete?))]
    (mapv (fn [i {:keys [mvar-id subst]}]
            (if (< i (count values))
              (let [v (nth values i)
                    alts (filterv #(let [pat (first-pat %)]
                                     (or (= :inaccessible (:tag pat)) (= (:e pat) v))) (:alts p))]
                (assoc p :mvar-id mvar-id :vars (mapv #(subst/apply subst %) xs)
                       :alts (mapv #(update (b/alt-apply-fvar-subst subst %) :patterns (comp vec rest)) alts)
                       :examples (mapv #(b/example-apply-fvar-subst subst
                                                                   (b/example-replace-fvar-id (e/fvar-id x) {:tag :val :e v} %))
                                       (:examples p))))
              (assoc p :mvar-id mvar-id :alts (filterv #(= :inaccessible (:tag (first-pat %))) (:alts p)))))
          (range) subgoals)))

(defn process [ctx state problem]
  (loop [pending [[problem 0]]]
    (when-let [[p depth] (peek pending)]
      (when (>= depth 1000) (c/tactic-error! "match: maximum recursion depth (1000) exceeded" {}))
      (c/with-goal! ctx (:mvar-id p))
      (let [more (pop pending) x (first (:vars p))
            first-alt (first (:alts p))
            refutable-pos (first (keep-indexed (fn [i pat] (when (refutable? pat) i)) (:patterns first-alt)))
            next-problems
            (cond
              (empty? (:vars p)) (do (process-leaf ctx state p) [])
              (and (empty? (:alts p)) (not= (c/goal-type ctx (:mvar-id p)) (u/const' "False" [])))
              [(process-ex-falso ctx p)]
              (has-independent-patterns p) [(process-independent-patterns ctx p)]
              (and (seq (:alts p)) (every? #(done? (first-pat %) x) (:alts p))) [(drop-first-var p)]
              (and refutable-pos (pos? refutable-pos)) [(move-to-front p refutable-pos)]
              (and first-alt (nil? refutable-pos) (next (:alts p)))
              (do (record-overlaps! state first-alt (rest (:alts p))) [(assoc p :alts [first-alt])])
              (and (some #(let [pat (first-pat %)] (and (= :val (:tag pat)) (some? (cv/get-nat-value? ctx (:e pat))))) (:alts p))
                   (or (not (e/fvar? x)) (has-pattern p :ctor))) [(expand-nat-value-pattern ctx p)]
              (not (e/fvar? x)) [(process-non-variable ctx p)]
              (has-pattern p :ctor) (process-constructor ctx p)
              (empty? (:alts p))
              (let [t (u/whnf ctx (u/infer-type ctx x))
                    ci (when (e/const? (e/get-app-fn t)) (env/lookup (:env @ctx) (e/const-name (e/get-app-fn t))))]
                ;; Lean avoids splitting recursive types forever when no alternative remains.
                (if (and ci (.isInduct ci) (not (.isRec ci))) (process-constructor ctx p)
                    [(assoc p :vars (vec (rest (:vars p))))]))
              (and (has-pattern p :val) (has-pattern p :inaccessible)) (process-value ctx p)
              (has-pattern p :val) [(expand-nat-value-pattern ctx p)]
              :else (c/tactic-error! "Failed to compile pattern matching: stuck" {:problem p}))]
        (recur (into more (map #(vector % (inc depth)) (reverse next-problems))))))))

(defn- expr-fvars [expr]
  (let [ids (volatile! #{})]
    (subst/map-expr-fvars (fn [id] (vswap! ids conj id) (e/fvar id)) expr)
    @ids))
(defn- level-params [expr]
  (let [out (volatile! []) seen (volatile! #{})]
    (letfn [(level [l]
              (case (lvl/tag l)
                :param (let [n (lvl/param-name l)] (when-not (contains? @seen n)
                                                    (vswap! seen conj n) (vswap! out conj n)))
                :succ (level (lvl/succ-pred l))
                :max (do (level (lvl/max-lhs l)) (level (lvl/max-rhs l)))
                :imax (do (level (lvl/imax-lhs l)) (level (lvl/imax-rhs l))) nil))
            (visit [x]
              (case (e/tag x)
                :sort (level (e/sort-level x))
                :const (doseq [l (e/const-levels x)] (level l))
                :app (do (visit (e/app-fn x)) (visit (e/app-arg x)))
                :lam (do (visit (e/lam-type x)) (visit (e/lam-body x)))
                :forall (do (visit (e/forall-type x)) (visit (e/forall-body x)))
                :let (do (visit (e/let-type x)) (visit (e/let-value x)) (visit (e/let-body x)))
                :mdata (visit (e/mdata-expr x))
                :proj (visit (e/proj-struct x)) nil))]
      (visit expr) @out)))

(defn mk-matcher-aux-definition [ctx n type value info lps]
  (let [ci (u/mk-definition-val-inferring-unsafe (:env @ctx) n lps type value :abbrev)
        out (env/check-constant (:env @ctx) ci)]
    (mi/add-matcher-info out n info)))

(defn mk-matcher
  "Compile MkMatcherInput {:matcher-name :match-type :discr-infos :lhss}.
   Returns MatcherResult and :env containing the kernel-checked declaration.
   MatchType and patterns may reference existing locals; closure parameters
   precede motive, discriminants and alternatives, as in Lean's Closure."
  [ctx {:keys [matcher-name match-type discr-infos lhss]}]
  (let [nd (count discr-infos)]
    (doseq [lhs lhss]
      (when-not (= nd (count (:patterns lhs)))
        (c/tactic-error! "Incorrect number of patterns in match alternative"
                         {:expected nd :actual (count (:patterns lhs))})))
    (let [all-lctx (:lctx @ctx)
          ;; withCleanLCtxFor: retain only input dependencies before case splitting.
          declarations (reduce (fn [lctx lhs]
                                 (reduce (fn [lctx d] (assoc lctx (:id d) d)) lctx (:fvar-decls lhs)))
                               all-lctx lhss)
          needed (reduce into (expr-fvars match-type) (map b/alt-lhs-collect-fvars lhss))
          needed (loop [ids needed]
                   (let [next (into ids (mapcat (fn [id]
                                                 (let [d (get declarations id)]
                                                   (concat (when (:type d) (expr-fvars (:type d)))
                                                           (when (:value d) (expr-fvars (:value d)))))) ids))]
                     (if (= ids next) ids (recur next))))
          pattern-ids (set (mapcat #(map :id (:fvar-decls %)) lhss))
          base (apply dissoc (select-keys all-lctx needed) pattern-ids)
          _ (c/set-lctx! ctx base)
          [discrs body] (u/forall-telescope ctx match-type nd)
          elim (u/get-level ctx body)
          elim-name (name/from-string (str "_match.u_" (swap! (:next-id @ctx) inc)))
          gen (if (lvl/level-zero? elim) lvl/zero (lvl/param elim-name))
          motive (u/local-decl ctx "motive" (u/mk-forall-fvars ctx discrs (e/sort' gen)))
          {:keys [alts minors alt-infos]} (with-alts ctx motive discrs discr-infos lhss)
          named? (boolean (some :h-name? discr-infos))
          process-discrs (if named? (first (u/forall-telescope ctx match-type nd)) discrs)
          eqs (when named? (with-eqs ctx discrs process-discrs discr-infos))
          eq-mask (mapv #(= "Eq" (str (e/const-name (e/get-app-fn (u/infer-type ctx %))))) eqs)
          target (u/mk-forall-fvars ctx eqs (u/app motive process-discrs))
          _ (c/set-lctx! ctx (apply dissoc (:lctx @ctx) (map e/fvar-id eqs)))
          root-lctx (:lctx @ctx)
          goal (c/fresh-mvar! ctx target)
          state (atom {:used #{} :overlaps [] :counter-examples []})
          _ (process ctx state (b/problem goal process-discrs alts (mapv #(hash-map :tag :var :fvar-id (e/fvar-id %)) process-discrs)))
          unused (vec (remove (:used @state) (range (count lhss))))]
      (c/set-lctx! ctx root-lctx)
      (if (seq (:counter-examples @state))
        {:matcher nil :counter-examples (:counter-examples @state) :unused-alt-idxs unused :env (:env @ctx)}
        (let [args (vec (concat [motive] discrs minors))
              type (u/mk-forall-fvars ctx args (u/app motive discrs))
              value (c/zonk ctx (e/mvar goal))
              value (if named?
                      (let [refls (mapv (fn [eq? x]
                                          (if eq? (u/mk-eq-refl ctx x)
                                              (u/app (u/const' "HEq.refl" [(u/get-level ctx (u/infer-type ctx x))])
                                                     [(u/infer-type ctx x) x])))
                                        eq-mask (keep (fn [[x info]] (when (:h-name? info) x))
                                                      (map vector discrs discr-infos)))]
                        (u/app (u/mk-lambda-fvars ctx process-discrs value) (concat discrs refls))) value)
              value (u/mk-lambda-fvars ctx args value)
              free (into (expr-fvars type) (expr-fvars value))
              free (loop [ids free]
                     (let [next (into ids (mapcat #(expr-fvars (:type (get root-lctx %))) ids))]
                       (if (= ids next) ids (recur next))))
              params (mapv e/fvar (sort free))
              ;; Closure.mkValueTypeClosureAux visits the open type and value
              ;; before processing captured local declarations, in reverse index order.
              lps (vec (distinct (concat (level-params type) (level-params value)
                                        (mapcat #(level-params (:type (u/decl ctx %))) (reverse params)))))
              type (u/mk-forall-fvars ctx params type)
              value (u/mk-lambda-fvars ctx params value)
              pos (when-not (lvl/level-zero? gen) (.indexOf lps elim-name))
              info (mi/matcher-info (count params) nd alt-infos pos discr-infos (:overlaps @state))
              out (mk-matcher-aux-definition ctx matcher-name type value info lps)
              levels (mapv #(if (= % elim-name) elim (lvl/param %)) lps)
              matcher (u/app (u/const' matcher-name levels) params)]
          {:matcher matcher :counter-examples [] :unused-alt-idxs unused
           :env out :type type :value value :info info})))))
