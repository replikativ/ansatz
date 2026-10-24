(ns ansatz.bundle-semantic-policy-test
  "Synthetic CI shapes only: deliberately not kernel/native proof receipts.
   Body presence and field safety never authenticate the bodies or their axioms."
  (:require [clojure.test :refer [deftest is]]
            [ansatz.bundle-semantic-policy :as policy]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as l]
            [ansatz.kernel.name :as n])
  (:import [ansatz.kernel ConstantInfo Expr Name]))

(def limits
  {:inputs {:declarations 100 :templates 100 :registrations 100 :name-components 10000
            :name-bytes 100000 :name-depth 64 :level-slots 1000}
   :comparison {:pairs 10000 :edges 100000 :items 100000 :scalar-bytes 1000000 :depth 128}})
(def type' (e/sort' l/zero))
(def body (e/bvar 0))
(defn error [f] (try (f) nil (catch clojure.lang.ExceptionInfo cause cause)))
(defn reason [f] (:reason (ex-data (error f))))
(defn const' [name levels] (e/const' name (vec levels)))
(defn equality-type [source target us vs]
  (e/app* (const' (n/from-string "Eq") [(l/succ l/zero)]) type'
          (const' source us) (const' target vs)))
(defn specimen
  ([] (specimen {}))
  ([{:keys [kind safety unsafe? value us vs parameters witness-parameters source-name]
     :or {kind :theorem safety :safe unsafe? false value body us [] vs [] parameters []}}]
   (let [source (or source-name (n/from-string "Policy.f")) target (n/from-string "Policy.g")
         witness (n/from-string "Policy.w")
         witness-parameters (or witness-parameters parameters)
         type (equality-type source target us vs)
         make-axiom #(env/mk-axiom % parameters type')
         make-witness #(case kind
                         :theorem (env/mk-thm witness witness-parameters type value)
                         :definition (env/mk-def witness witness-parameters type value :hints :abbrev :safety safety)
                         :opaque (env/mk-opaque witness witness-parameters type value :unsafe? unsafe?)
                         :axiom (env/mk-axiom witness witness-parameters type))]
     {:role [(make-axiom source) (make-axiom target) (make-witness)]
      :templates (cond-> [(make-axiom source) (make-axiom target)] (= kind :axiom) (conj (make-witness)))
      :rows [{:source source :target target :witness witness :global-ordinal 0}]})))
(defn compare' [{:keys [role rows templates]}]
  (policy/compare-role-bounded role rows templates limits))

(deftest diagnostic-results-carry-no-native-proof-or-activation-authority
  (doseq [kind [:theorem :definition :opaque]]
    (let [result (compare' (specimen {:kind kind}))]
      (is (= :none (:authority result)))
      (is (= :pending (:native-binding result) (:proof-assumptions result)))
      (is (= :pending-lossless-native-eqv-bridge (:implemented-by result)))
      (is (= [{:row-index 0 :global-ordinal 0 :witness-kind kind}] (:registrations result)))
      (is (= 2 (:axiom-comparison-count result))))))

(deftest exact-equality-arity-and-direct-constant-endpoints-are-required
  (let [base (specimen) ^ConstantInfo witness (last (:role base))
        exact (.type witness)
        alternatives [(e/app (const' (n/from-string "Eq") []) type')
                      (e/app exact body)
                      (e/forall' (n/from-string "x") type' exact :default)
                      (const' (n/from-string "Policy.eqAlias") [])
                      (e/mdata nil exact)]]
    (doseq [type alternatives]
      (let [changed (env/mk-thm (.name witness) [] type body)]
        (is (some? (error #(compare' (assoc base :role (assoc (:role base) 2 changed))))))))))

(deftest endpoint-names-and-ordered-distinct-parameter-universes-are-exact
  (let [u-name (n/from-string "u") v-name (n/from-string "v")
        u (l/param u-name) v (l/param v-name)]
    (is (= 1 (count (:registrations (compare' (specimen {:parameters [u-name v-name] :us [u v] :vs [u v]}))))))
    (doseq [[us vs] [[[u v] [v u]] [[u u] [u u]] [[l/zero] [l/zero]] [[u] [v]]]]
      (is (some? (error #(compare' (specimen {:parameters [u-name v-name] :us us :vs vs}))))))
    (let [base (specimen) row (first (:rows base))]
      (is (= :witness-endpoints
             (reason #(compare' (assoc base :rows [(assoc row :source (:target row) :target (:source row))]))))))))

(deftest unused-witness-universe-parameters-are-not-an-extra-native-condition
  (let [u (n/from-string "u") unused (n/from-string "unused")]
    (is (= 1 (count (:registrations
                    (compare' (specimen {:parameters [u] :witness-parameters [u unused]
                                         :us [(l/param u)] :vs [(l/param u)]}))))))))

(deftest repeated-registration-sources-stay-in-original-order
  (let [base (specimen) second-name (n/from-string "Policy.secondWitness")
        second-witness (env/mk-def second-name [] (.type ^ConstantInfo (last (:role base))) body :hints :abbrev)
        row (first (:rows base))
        rows [(assoc row :global-ordinal 4)
              (assoc row :witness second-name :global-ordinal 12)
              (assoc row :global-ordinal 25)]
        result (compare' (assoc base :role (conj (:role base) second-witness) :rows rows))]
    (is (= [4 12 25] (mapv :global-ordinal (:registrations result))))
    (is (= [:theorem :definition :theorem] (mapv :witness-kind (:registrations result))))
    (is (= :invalid-registration-order
           (reason #(compare' (assoc base :rows [(assoc row :global-ordinal 4) (assoc row :global-ordinal 4)])))))))

(deftest witness-must-be-in-this-role-and-have-safe-body-bearing-fields
  (let [base (specimen)]
    (is (= :registration-outside-role
           (reason #(compare' (assoc base :role (into [] (take 2 (:role base)))))))))
  (doseq [options [{:kind :axiom} {:kind :definition :safety :unsafe}
                   {:kind :definition :safety :partial} {:kind :opaque :unsafe? true}]]
    (is (= :witness-kind-or-safety (reason #(compare' (specimen options))))))
  (is (some? (error #(compare' (specimen {:value nil}))))))

(deftest axiom-templates-compare-type-universe-order-and-safety-not-just-name
  (let [u (n/from-string "u") v (n/from-string "v")
        base (specimen {:parameters [u v]}) ^ConstantInfo original (first (:role base))
        changes [(env/mk-axiom (.name original) [u v] (e/sort' (l/succ l/zero)))
                 (env/mk-axiom (.name original) [v u] type')
                 (env/mk-axiom (.name original) [u v] type' :unsafe? true)]]
    (doseq [changed changes]
      (is (= :axiom-template-mismatch
             (reason #(compare' (assoc base :role (assoc (:role base) 0 changed)))))))))

(deftest all-observed-axioms-need-templates-but-unused-catalog-entries-are-allowed
  (let [base (specimen)
        extra (env/mk-axiom (n/from-string "Policy.otherRoleAxiom") [] type')]
    (is (= :missing-axiom-template (reason #(compare' (assoc base :templates [])))))
    (is (= 2 (:axiom-comparison-count (compare' (update base :templates conj extra)))))
    (is (= :missing-axiom-template (reason #(compare' (update base :role conj extra)))))
    (is (= :non-axiom-template (reason #(compare' (assoc base :templates [(last (:role base))])))))))

(deftest runtime-marker-comparison-does-not-discharge-safe-proof-assumptions
  (let [base (specimen)
        name (n/from-string "Synthetic.compilerMarker")
        marker #(env/mk-axiom name [] type' :unsafe? true)
        result (compare' (-> base (update :role conj (marker)) (update :templates conj (marker))))]
    (is (= 3 (:axiom-comparison-count result)))
    (is (= :pending (:proof-assumptions result)))
    (is (= :none (:authority result)))))

(deftest structural-name-segments-never-fall-back-to-dotted-text
  (doseq [[actual alias] [[(n/from-string "Policy.f") (Name/mkStr Name/ANONYMOUS_NAME "Policy.f")]
                         [(Name/mkNum Name/ANONYMOUS_NAME 666) (Name/mkStr Name/ANONYMOUS_NAME "666")]]]
    (let [base (specimen {:source-name actual}) row (first (:rows base))]
      (is (= (str actual) (str alias)))
      (is (= :registration-outside-role
             (reason #(compare' (assoc base :rows [(assoc row :source alias)]))))))))

(deftest count-name-and-level-slot-budgets-refuse-explicitly
  (let [{:keys [role rows templates]} (specimen)
        compare-with #(policy/compare-role-bounded role rows templates %)]
    (doseq [key [:declarations :templates :name-components :name-bytes]]
      (is (some? (error #(compare-with (assoc-in limits [:inputs key] 1))))))
    (is (some? (error #(compare-with (assoc-in limits [:comparison :items] 1)))))
    (is (some? (error #(compare-with (update limits :inputs dissoc :level-slots))))))
  (let [u (n/from-string "u") base (specimen {:parameters [u] :us [(l/param u)] :vs [(l/param u)]})]
    (is (some? (error #(policy/compare-role-bounded (:role base) (:rows base) (:templates base)
                                                   (assoc-in limits [:inputs :level-slots] 1)))))))

(deftest combined-comparisons-share-one-invocation-budget
  (let [make #(env/mk-axiom (n/from-string %) [] type')
        f (make "Budget.f") ft (make "Budget.f") g (make "Budget.g") gt (make "Budget.g")
        run (fn [role templates items]
              (policy/compare-role-bounded role [] templates (assoc-in limits [:comparison :items] items)))
        minimum (loop [low 1 high 4096]
                  (if (= low high) low
                      (let [mid (quot (+ low high) 2)]
                        (if (error #(run [f] [ft] mid)) (recur (inc mid) high) (recur low mid)))))]
    (is (= 1 (:axiom-comparison-count (run [f] [ft] minimum))))
    (is (= 1 (:axiom-comparison-count (run [g] [gt] minimum))))
    (is (some? (error #(run [f g] [ft gt] minimum))))))

(deftest shared-expression-dags-stay-bounded-and-identical-cycles-fail-closed
  (let [graph (nth (iterate #(e/app % %) body) 20)
        name (n/from-string "Policy.shared")
        make #(env/mk-axiom name [] graph)]
    (is (= 1 (:axiom-comparison-count (policy/compare-role-bounded [(make)] [] [(make)] limits)))))
  (let [cycle (e/app body body) field (.getField Expr "o0") original (.o0 ^Expr cycle)
        value (env/mk-axiom (n/from-string "Policy.cycle") [] cycle)]
    (.setAccessible field true)
    (try
      (.set field cycle cycle)
      (is (some? (error #(policy/compare-role-bounded [value] [] [value] limits))))
      (finally (.set field cycle original)))))

(deftest arbitrary-vectors-and-registration-success-flags-are-refused
  (let [reads (atom 0)
        custom (proxy [clojure.lang.APersistentVector] []
                 (count [] (swap! reads inc) (throw (AssertionError. "custom count must not run")))
                 (nth [i] (swap! reads inc) (throw (AssertionError. "custom nth must not run"))))
        base (specimen)]
    (is (= :unsupported-vector
           (reason #(policy/compare-role-bounded custom (:rows base) (:templates base) limits))))
    (is (zero? @reads))
    (is (= :invalid-registration
           (reason #(compare' (update base :rows (fn [rows] [(assoc (first rows) :verified true)]))))))))

(deftest safety-interpretation-follows-the-native-variant-not-unused-mutable-flags
  (doseq [kind [:theorem :definition]]
    (let [base (specimen {:kind kind}) ^ConstantInfo witness (last (:role base))]
      ;; Native THM safety is always false; DEF derives it from .safety. Neither
      ;; variant interprets the mutable boolean used by AXIOM/OPAQUE declarations.
      (set! (.isUnsafe witness) true)
      (is (= kind (:witness-kind (first (:registrations (compare' base))))))))
  (let [base (specimen {:kind :definition}) ^ConstantInfo witness (last (:role base))]
    (set! (.safety witness) (byte 3))
    (is (some? (error #(compare' base))))))

(deftest unknown-map-keys-are-rejected-before-hash-callbacks
  (let [hashes (atom 0)
        unknown (proxy [Object] []
                  (hashCode [] (swap! hashes inc) (throw (AssertionError. "unknown key hash must not run"))))
        base (specimen) row (first (:rows base))
        bad-row (array-map :source (:source row) :target (:target row)
                           :global-ordinal 0 unknown (:witness row))
        bad-limits (array-map :inputs (:inputs limits) unknown (:comparison limits))]
    (is (= :invalid-registration (reason #(compare' (assoc base :rows [bad-row])))))
    (is (= :explicit-finite-limits-required
           (reason #(policy/compare-role-bounded (:role base) (:rows base) (:templates base) bad-limits))))
    (is (zero? @hashes))))
