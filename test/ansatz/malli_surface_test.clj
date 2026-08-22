(ns ansatz.malli-surface-test
  "The gradual dependently-typed on-ramp: malli function schemas as a/defn signatures.
   The porting story under test is a one-token diff — `defn` → `a/defn`, schemas unchanged."
  (:require [clojure.test :refer [deftest testing is]]
            [malli.core :as m]
            [ansatz.core :as a]
            [ansatz.malli]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]))

(defonce ^:private booted (delay (binding [a/*verbose* false] (a/load-init!))))

;; ordinary malli-instrumented Clojure style: schema FIRST, then the definition
(m/=> msf-add2 [:=> [:cat :int :int] :int])
(m/=> msf-len  [:=> [:cat [:sequential :int]] :int])

(deftest test-malli-schema-as-signature
  (testing "a/defn with a PLAIN param vector reads the m/=> registry: params/ret from the
            schema, body kernel-verified, runtime compiled"
    @booted
    (binding [a/*verbose* false]
      (when-not (env/lookup (a/env) (name/from-string "msf-add2"))
        ;; eval in THIS ns — the m/=> registry is namespace-keyed, like instrumentation
        (binding [*ns* (find-ns 'ansatz.malli-surface-test)]
          (eval '(ansatz.core/defn msf-add2 [x y]
                   (match x Nat Nat (zero y) (succ [k] (+ 1 (msf-add2 k y))))))))
      (is (some? (env/lookup (a/env) (name/from-string "msf-add2")))
          "schema-signed recursive function kernel-verified")
      ;; the kernel type came from the schema: ∀ (x y : Nat), Nat
      (let [ty (e/->string (.type (env/lookup (a/env) (name/from-string "msf-add2"))))]
        (is (re-find #"Nat" ty) "Nat signature from :int schema"))
      ;; and it runs
      (is (= 7 (clojure.core/long ((deref (ns-resolve 'ansatz.malli-surface-test 'msf-add2)) 3 4))) "runtime agrees")))
  (testing "collection schemas: [:sequential :int] → List Nat"
    @booted
    (binding [a/*verbose* false]
      (when-not (env/lookup (a/env) (name/from-string "msf-len"))
        (binding [*ns* (find-ns 'ansatz.malli-surface-test)]
          (eval '(ansatz.core/defn msf-len [xs]
                   (match xs (List Nat) Nat (nil 0) (cons [h t] (+ 1 (msf-len t))))))))
      (is (some? (env/lookup (a/env) (name/from-string "msf-len"))) "List-typed via schema")
      (is (= 3 (clojure.core/long ((deref (ns-resolve 'ansatz.malli-surface-test 'msf-len)) (list 1 2 3)))) "runtime agrees"))))

(m/=> msf-rec [:=> [:cat [:map [:a :int] [:b :boolean]]] :int])
(m/=> msf-ref [:=> [:cat [:int {:min 2}]] :int])

(deftest test-malli-comprehensive-shapes
  (testing "[:map …] params land as synthesized named-field records"
    @booted
    (binding [a/*verbose* false]
      (when-not (env/lookup (a/env) (name/from-string "msf-rec"))
        (binding [*ns* (find-ns 'ansatz.malli-surface-test)]
          (eval '(ansatz.core/defn msf-rec [r] 7))))
      (let [ty (e/->string (.type (env/lookup (a/env) (name/from-string "msf-rec"))))]
        (is (re-find #"MalliRec_a_b" ty) "record schema became a named record signature"))))
  (testing "[:int {:min 2}] params land as Subtype refinements"
    @booted
    (binding [a/*verbose* false]
      (when-not (env/lookup (a/env) (name/from-string "msf-ref"))
        (binding [*ns* (find-ns 'ansatz.malli-surface-test)]
          (eval '(ansatz.core/defn msf-ref [n] 7))))
      (let [ty (e/->string (.type (env/lookup (a/env) (name/from-string "msf-ref"))))]
        (is (re-find #"Subtype" ty) "bounded int became a Subtype refinement")
        (is (re-find #"LE\.le" ty) "the bound is carried as a Prop"))))
  (testing "domain-type registry: register once, reference by keyword (ansatz-side registry)"
    @booted
    ((requiring-resolve 'ansatz.malli/register-type!) :msf/age [:int {:min 0}])
    (let [t ((requiring-resolve 'ansatz.malli/schema->type-expr) :msf/age)]
      (is (re-find #"Nat" (e/->string t)) "registered :msf/age resolves through to Nat"))))

(deftest test-malli-schema-honest-errors
  (testing "a registered but untranslatable schema THROWS (no approximate lifting)"
    @booted
    (m/=> msf-bad [:=> [:cat [:or :int :string]] :int])
    (is (thrown? Exception
                 (binding [*ns* (find-ns 'ansatz.malli-surface-test)]
                   (eval '(ansatz.core/defn msf-bad [m] 0))))
        "[:or …] sum schemas are rejected (no kernel sum mapping yet)")))

(deftest test-differential-lane
  (testing "the generative differential check: compiled runtime ≡ kernel evaluation on
            schema-generated inputs (the guard for well-typed-but-source-unfaithful bugs)"
    @booted
    (binding [a/*verbose* false]
      (when-not (env/lookup (a/env) (name/from-string "msf-add2"))
        (binding [*ns* (find-ns 'ansatz.malli-surface-test)]
          (eval '(ansatz.core/defn msf-add2 [x y]
                   (match x Nat Nat (zero y) (succ [k] (+ 1 (msf-add2 k y))))))))
      (let [r ((requiring-resolve 'ansatz.malli/check-verified!)
               'ansatz.malli-surface-test 'msf-add2 :runs 15)]
        (is (= 15 (:ok r)) "15/15 generated inputs agree runtime vs kernel")))))

(m/=> msf-bump [:=> [:cat [:int {:min 1}]] :int])

(deftest test-subtype-param-ergonomics
  (testing "a refined param ([:int {:min 1}] → Subtype) is used directly as its carrier:
            body references auto-coerce to .val, the refinement erases at runtime"
    @booted
    (binding [a/*verbose* false]
      (when-not (env/lookup (a/env) (name/from-string "msf-bump"))
        (binding [*ns* (find-ns 'ansatz.malli-surface-test)]
          (eval '(ansatz.core/defn msf-bump [n] (+ n 1)))))
      (let [ci (env/lookup (a/env) (name/from-string "msf-bump"))]
        (is (some? ci) "arithmetic over the refined param verifies")
        (is (re-find #"Subtype" (e/->string (.type ci))) "the binder keeps the refinement")
        (is (= 6 (clojure.core/long ((deref (ns-resolve 'ansatz.malli-surface-test 'msf-bump)) 5)))
            "runtime takes the raw carrier value")))))

(m/=> msf-dot [:=> [:cat [:map [:x :int] [:y :int]]] :int])

(deftest test-named-field-records
  (testing "[:map [:x :int] [:y :int]] synthesizes a named-field structure: keyword access
            elaborates to kernel projections, runtime values are plain Clojure maps"
    @booted
    (binding [a/*verbose* false]
      (when-not (env/lookup (a/env) (name/from-string "msf-dot"))
        (binding [*ns* (find-ns 'ansatz.malli-surface-test)]
          (eval '(ansatz.core/defn msf-dot [p] (+ (:x p) (:y p))))))
      (let [ci (env/lookup (a/env) (name/from-string "msf-dot"))]
        (is (some? ci) "keyword access over the schema'd record param verifies")
        (is (re-find #"MalliRec_x_y" (e/->string (.type ci)))
            "the binder is the synthesized named record type")
        (is (= 5 (clojure.core/long ((deref (ns-resolve 'ansatz.malli-surface-test 'msf-dot))
                                     {:x 2 :y 3})))
            "runtime takes a plain Clojure map")))))

(deftest test-opaque-gradual-scalars
  ;; The general (total) functor: opaque scalars with no sharp native rep route to the gradual `Opaque`
  ;; carrier instead of throwing — so a realistic event record (timestamp/status/uuid) can be MODELED,
  ;; carried, and keyed (group-by/join) while precise fields keep the full optimizer algebra.
  @booted
  (binding [a/*verbose* false]
    (let [opq? (fn [t] (= "Opaque" (let [[h _] (e/get-app-fn-args t)]
                                     (and (e/const? h) (name/->string (e/const-name h))))))]
      (testing "opaque scalars -> Opaque (was: throw 'unsupported scalar schema')"
        (doseq [s [:keyword :uuid :symbol :any :some 'keyword? 'uuid? 'any?]]
          (is (opq? (ansatz.malli/schema->type-expr s)) (str s " -> Opaque"))))
      (testing "ensure-opaque! installs the axioms (idempotent)"
        (ansatz.malli/ensure-opaque!)
        (is (some? (env/lookup (a/env) (name/from-string "Opaque"))) "Opaque : Type")
        (is (some? (env/lookup (a/env) (name/from-string "instDecidableEqOpaque"))) "DecidableEq Opaque"))
      (testing "[:enum ...] maps to its members' type (string->String, int->Nat); a keyword
                enum is a CLOSED set, so it synthesizes an inductive rather than carrying as Opaque"
        (is (re-find #"String" (e/->string (ansatz.malli/schema->type-expr [:enum "x" "y"]))))
        (is (re-find #"Nat"    (e/->string (ansatz.malli/schema->type-expr [:enum 1 2]))))
        (is (re-find #"MalliEnum_a_b" (e/->string (ansatz.malli/schema->type-expr [:enum :a :b]))))
        (is (not (opq? (ansatz.malli/schema->type-expr [:enum :a :b])))
            "a closed member set is an ADT, not the gradual carrier")
        (is (opq? (ansatz.malli/schema->type-expr [:enum :a "b"]))
            "a HETEROGENEOUS enum still has no single sharp type"))
      (testing "precise scalars unchanged (still sharp native types)"
        (is (re-find #"Nat"    (e/->string (ansatz.malli/schema->type-expr [:int {:min 0}]))))
        (is (re-find #"String" (e/->string (ansatz.malli/schema->type-expr :string))))))))

(deftest test-collection-and-map-schema-shapes
  ;; the compound/regex collection schemas carto's own m/=> annotations exercise: [:map-of],
  ;; the [:* …]/[:+ …]/[:? …] regex-sequence family, and a fieldless [:map] (was: throw).
  @booted
  (binding [a/*verbose* false]
    (let [->s  (fn [s] (e/->string (ansatz.malli/schema->type-expr s)))
          opq? (fn [s] (= "Opaque" (let [[h _] (e/get-app-fn-args (ansatz.malli/schema->type-expr s))]
                                     (and (e/const? h) (name/->string (e/const-name h))))))]
      (testing "[:map-of K V] -> association List of key/value Prods"
        (is (re-find #"List.*Prod.*String.*Nat" (->s [:map-of :string :int])))
        (is (re-find #"List.*Prod.*String.*List.*Nat" (->s [:map-of :string [:sequential :int]]))))
      (testing "regex-sequence element schemas: :* / :+ -> List, :? -> Option"
        (is (re-find #"List.*Nat"    (->s [:* :int])))
        (is (re-find #"List.*String" (->s [:+ :string])))
        (is (re-find #"Option.*Nat"  (->s [:? :int]))))
      (testing "a fieldless map (bare :map, [:map], map?) carries as gradual Opaque"
        (is (opq? :map)   "bare :map -> Opaque")
        (is (opq? [:map]) "[:map] with no entries -> Opaque")
        (is (opq? 'map?)  "map? predicate -> Opaque"))
      (testing "a [:map] WITH fields still synthesizes a named record (not Opaque)"
        (is (re-find #"MalliRec" (->s [:map [:status :keyword] [:n :int]]))))
      (testing "carto's own [:=> [:cat :string [:sequential :string] [:* :any]] :map] fully translates"
        (let [sig (ansatz.malli/fn-schema->signature
                   [:=> [:cat :string [:sequential :string] [:* :any]] :map])
              tx  (fn [marker] (e/->string (ansatz.malli/schema->type-expr (second marker))))]
          (is (= 3 (count (:param-types sig))))
          (is (= ["String" "(List.{0} String)" "(List.{0} Opaque)"]
                 (mapv tx (:param-types sig)))
              "string + list-of-string + variadic [:* :any] rest-arg")
          (is (= "Opaque" (tx (:ret-type sig))) ":map return carries as Opaque"))))))
;; ── differential lane past Nat / Bool / (List Nat) ───────────────────────────────────────

(m/=> msf-echo [:=> [:cat :string] :string])
(m/=> msf-pair-sum [:=> [:cat [:map [:a :int] [:b :int]]] :int])

(deftest test-differential-lane-carries-strings
  (testing "a String argument and result round-trip through the codec, so check-verified!
            can compare them instead of throwing on (long \"…\")"
    @booted
    (binding [a/*verbose* false]
      (when-not (env/lookup (a/env) (name/from-string "msf-echo"))
        (binding [*ns* (find-ns 'ansatz.malli-surface-test)]
          (eval '(ansatz.core/defn msf-echo [s] s))))
      (let [r ((requiring-resolve 'ansatz.malli/check-verified!)
               'ansatz.malli-surface-test 'msf-echo :runs 10)]
        (is (= 10 (:ok r)) "10/10 generated strings agree runtime vs kernel")))))

(deftest test-differential-lane-carries-map-records
  (testing "a named-field [:map] argument rides its synthesized record through the codec:
            the type layer already built MalliRec_a_b, and the lane can now encode a value
            into its constructor and read the result back"
    @booted
    (binding [a/*verbose* false]
      (when-not (env/lookup (a/env) (name/from-string "msf-pair-sum"))
        (binding [*ns* (find-ns 'ansatz.malli-surface-test)]
          (eval '(ansatz.core/defn msf-pair-sum [p] (+ (:a p) (:b p))))))
      (let [r ((requiring-resolve 'ansatz.malli/check-verified!)
               'ansatz.malli-surface-test 'msf-pair-sum :runs 10)]
        (is (= 10 (:ok r)) "10/10 generated records agree runtime vs kernel")))))

(deftest test-differential-lane-refuses-what-it-cannot-carry
  (testing "a shape the codec cannot round-trip is refused at GENERATION, where the message
            names the gap — not later, where an ill-typed term reads as a divergence"
    @booted
    (let [gen (deref (requiring-resolve 'ansatz.malli/gen-schema))]
      (is (thrown? clojure.lang.ExceptionInfo (gen [:map]))
          "a fieldless [:map] is the Opaque carrier and has no values to generate")
      (is (thrown? clojure.lang.ExceptionInfo (gen :uuid)))
      (testing "an OPEN scalar has no closed carrier: Opaque is an axiom with no constructors,
                so there is no value to encode and the refusal says so"
        (doseq [s [:keyword :symbol :any 'keyword? 'any?]]
          (is (thrown-with-msg? clojure.lang.ExceptionInfo #"no closed values" (gen s))
              (str s " is an open set"))))
      (is (thrown? clojure.lang.ExceptionInfo (gen [:enum :a "b"]))
          "a HETEROGENEOUS enum has no single carrier")
      (testing "and the shapes it CAN carry are accepted"
        (is (some? (gen :string)))
        (is (some? (gen [:map [:a :int]])))
        (is (some? (gen [:maybe :int])))
        (is (some? (gen [:sequential :boolean])))
        (is (some? (gen [:tuple :int :string])))
        (is (some? (gen [:map-of :string :int])))
        (is (some? (gen [:enum :a :b]))
            "a homogeneous keyword enum is a closed set and rides its synthesized inductive")))))

(defn- msf-verify
  "Define `form` in this namespace once (the kernel env is global, so a redefinition is a
   hard error) and run the differential check over it."
  [fn-sym form runs]
  (binding [a/*verbose* false]
    (when-not (env/lookup (a/env) (name/from-string (name fn-sym)))
      (binding [*ns* (find-ns 'ansatz.malli-surface-test)]
        (eval form)))
    ((requiring-resolve 'ansatz.malli/check-verified!)
     'ansatz.malli-surface-test fn-sym :runs runs)))

(deftest test-differential-lane-carries-tuples
  (testing "a [:tuple A B …] rides a right-nested Prod both ways — the subject CONSTRUCTS its
            result, so a carry-only codec would not see it"
    @booted
    (m/=> msf-tuple-swap [:=> [:cat [:tuple :int :string]] [:tuple :string :int]])
    (let [r (msf-verify 'msf-tuple-swap
                        '(ansatz.core/defn msf-tuple-swap [p]
                           (Prod.mk String Nat (Prod.snd Nat String p) (Prod.fst Nat String p)))
                        10)]
      (is (= 10 (:ok r)) "10/10 generated tuples agree runtime vs kernel"))
    (is (= ["hi" 7] ((deref (ns-resolve 'ansatz.malli-surface-test 'msf-tuple-swap)) [7 "hi"]))
        "the compiled runtime takes and returns a plain Clojure vector")))

(deftest test-differential-lane-carries-map-of
  (testing "a [:map-of K V] rides a List of key/value Prods"
    @booted
    (m/=> msf-mapof-len [:=> [:cat [:map-of :string :int]] :int])
    (let [r (msf-verify 'msf-mapof-len
                        '(ansatz.core/defn msf-mapof-len [mm] (List.length (Prod String Nat) mm))
                        10)]
      (is (= 10 (:ok r)) "10/10 generated maps agree runtime vs kernel"))
    (is (= 3 (clojure.core/long ((deref (ns-resolve 'ansatz.malli-surface-test 'msf-mapof-len))
                                 {"a" 1 "b" 2 "c" 3})))
        "the compiled runtime takes a plain Clojure map")))

(deftest test-differential-lane-carries-keyword-enums
  (testing "a homogeneous keyword [:enum …] rides the inductive ensure-enum! synthesizes, and
            the compiled runtime yields the KEYWORD the schema declares"
    @booted
    (m/=> msf-enum-pick [:=> [:cat :boolean [:enum :a :b :c] [:enum :a :b :c]] [:enum :a :b :c]])
    (let [r (msf-verify 'msf-enum-pick
                        '(ansatz.core/defn msf-enum-pick [b x y] (if b x y))
                        12)]
      (is (= 12 (:ok r)) "12/12 generated members agree runtime vs kernel"))
    (let [f (deref (ns-resolve 'ansatz.malli-surface-test 'msf-enum-pick))]
      (is (= :a (f true :a :c)))
      (is (= :c (f false :a :c))))
    (testing "ensure-enum! is idempotent and ORDER-sensitive — a reordering is a different type"
      (is (= (e/->string (ansatz.malli/ensure-enum! [:a :b]))
             (e/->string (ansatz.malli/ensure-enum! [:a :b]))))
      (is (not= (e/->string (ansatz.malli/ensure-enum! [:a :b]))
                (e/->string (ansatz.malli/ensure-enum! [:b :a])))))))

(deftest test-decode-reduces-at-every-descent
  (testing "whnf is WEAK head normal form, so a constructor's ARGUMENTS come back unreduced.
            A subject that builds a compound result from a COMPUTED part is the case that
            catches a decoder which only reduces the top of the term."
    @booted
    (m/=> msf-computed-head [:=> [:cat [:sequential :int]] [:sequential :int]])
    (let [r (msf-verify 'msf-computed-head
                        '(ansatz.core/defn msf-computed-head [l] (cons (+ (List.length Nat l) 1) l))
                        10)]
      (is (= 10 (:ok r)) "10/10 agree; before the fix this threw 'undecodable kernel value'"))
    (is (= [3 7 8] (vec ((deref (ns-resolve 'ansatz.malli-surface-test 'msf-computed-head)) [7 8])))
        "the head is the computed length + 1")))
