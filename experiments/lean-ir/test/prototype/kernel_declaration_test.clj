(ns prototype.kernel-declaration-test
  (:require [clojure.test :refer [deftest is]]
            [prototype.kernel-declaration :as declaration]
            [prototype.imported-kernel :as imported] [prototype.module-data :as data]
            [prototype.kernel-bridge-test :as guest] [prototype.machine :as m]
            [ansatz.kernel.name :as name])
  (:import [ansatz.kernel ConstantInfo Env TypeChecker]))

(defn fixture []
  (let [loaded (data/load-file (m/world {}) "fixtures/imported-kernel-native.jsonl")
        entries (imported/module-constants (:world loaded) (first (:roots loaded)))]
    {:world (:world loaded)
     :values (into {} (map (fn [{:keys [guest ^ConstantInfo constant]}] [(str (.name constant)) guest])) entries)}))
(defn base-env [{:keys [world values]}]
  (TypeChecker/checkConstant (Env.) (imported/project-constant world (get values "A")) 1000000))
(defn guest-list [world values]
  (reduce (fn [[world tail] value] (guest/ctor world 1 [value tail] 0))
          [world guest/nil-tag] (reverse values)))
(defn mutual [world safety body-second]
  (let [[world type] (guest/constant world "A")
        [world f-body] (guest/constant world "g")
        [world g-body] (guest/constant world body-second)
        [world f] (guest/declaration world "f" type f-body)
        [world g] (guest/declaration world "g" type g-body)
        f (first (:fields (m/node world f)))
        g (first (:fields (m/node world g)))
        world (-> world (guest/scalar! f 0 "uint8" safety) (guest/scalar! g 0 "uint8" safety))
        [world list] (guest-list world [f g])
        [world decl] (guest/ctor world 5 [list] 0)]
    {:world world :declaration decl :definitions [f g] :list list}))

(deftest authentic-native-theorem-and-safe-opaque-use-strict-admission
  (let [{:keys [world values] :as fixture} (fixture) env (base-env fixture)
        theorem (get values "identityProof") opaque (get values "hiddenA")]
    ;; thmDecl/opaqueDecl wrappers have precisely the same first-four layout
    ;; as the actual transported ConstantInfo variant. No fixture rewriting.
    (doseq [[kind ref] [[:theorem theorem] [:opaque opaque]]]
      (let [result (declaration/admit world env ref)
            ^ConstantInfo constant (:constant result)]
        (is (= kind (:kind result)))
        (is (identical? world (:world result)))
        (is (= ref (:guest-declaration result)))
        (is (= (.tag (imported/project-constant world ref)) (.tag constant)))
        (is (nil? (.lookup ^Env env (.name constant))))
        (is (identical? constant (.lookup ^Env (:env result) (.name constant))))
        (is (thrown? Exception (declaration/admit world (:env result) ref)))))))

(deftest malformed-theorems-and-opaque-bodies-fail-without-environment-mutation
  (let [{:keys [world values] :as fixture} (fixture) env (base-env fixture)
        theorem (get values "identityProof") thm (first (:fields (m/node world theorem)))
        opaque (get values "hiddenA") opq (first (:fields (m/node world opaque)))
        ;; A has type Sort1; it is neither a proof of identity nor a missing-name escape.
        invalid-proof (assoc-in world [:heap (:id thm) :fields 1] (second (:fields (m/node world opq))))
        [world missing] (guest/constant world "Missing")
        invalid-opaque (assoc-in world [:heap (:id opq) :fields 1] missing)
        [world not-prop] (guest/ctor world 0 (:fields (m/node world opq)) 0)
        [world not-prop-decl] (guest/ctor world 2 [not-prop] 0)]
    (is (thrown? Exception (declaration/admit invalid-proof env theorem)))
    (is (thrown-with-msg? Exception #"not a proposition" (declaration/admit world env not-prop-decl)))
    (is (thrown? Exception (declaration/admit invalid-opaque env opaque)))
    (is (nil? (.lookup ^Env env (name/from-string "identityProof"))))
    (is (nil? (.lookup ^Env env (name/from-string "hiddenA"))))
    (is (thrown-with-msg? Exception #"Unsafe source opaque"
          (declaration/admit (guest/scalar! world opq 0 "uint8" 1) env opaque {:allow-unsafe? true})))))

(deftest mutual-unsafe-and-partial-definitions-check-all-headers-and-bodies
  (let [{base-world :world :as fixture} (fixture) env (base-env fixture)]
    (doseq [safety [0 2]]
      (let [{:keys [world declaration definitions]} (mutual base-world safety "f")
            result (declaration/admit world env declaration {:allow-unsafe? true})
            constants (:constants result)]
        (is (= :mutual-definitions (:kind result)))
        (is (= ["f" "g"] (mapv #(str (.name ^ConstantInfo %)) constants)))
        (is (= [safety safety] (mapv #(case (.safety ^ConstantInfo %) 1 0 2 2) constants)))
        (is (identical? world (:world result)))
        (is (= declaration (:guest-declaration result)))
        (is (every? #(some? (.lookup ^Env (:env result) (name/from-string %))) ["f" "g"]))
        (is (every? #(nil? (.lookup ^Env env (name/from-string %))) ["f" "g"]))
        (is (thrown-with-msg? Exception #"explicit host policy"
              (declaration/admit world env declaration)))))))

(deftest mutual-metadata-contracts-and-invalid-bodies-reject-atomically
  (let [{base-world :world :as fixture} (fixture) env (base-env fixture)
        {:keys [world declaration definitions list]} (mutual base-world 0 "f")
        [f g] definitions
        mixed (guest/scalar! world g 0 "uint8" 2)
        safe (-> world (guest/scalar! f 0 "uint8" 1) (guest/scalar! g 0 "uint8" 1))
        [world u] (guest/guest-name world "u")
        [world params] (guest-list world [u])
        g-base (first (:fields (m/node world g)))
        mismatched (assoc-in world [:heap (:id g-base) :fields 1] params)
        [world duplicates] (guest-list world [f f])
        [world duplicate-decl] (guest/ctor world 5 [duplicates] 0)
        [world empty-decl] (guest/ctor world 5 [guest/nil-tag] 0)
        cyclic (assoc-in world [:heap (:id list) :fields 1] list)]
    (doseq [[world ref message] [[mixed declaration #"same safety"] [safe declaration #"unsafe or partial"]
                                 [mismatched declaration #"same universe level parameters"]
                                 [world duplicate-decl #"Duplicate mutual"] [world empty-decl #"empty mutual"]
                                 [cyclic declaration #"Cyclic source"]]]
      (is (thrown-with-msg? Exception message (declaration/admit world env ref {:allow-unsafe? true}))))
    (let [{:keys [world declaration]} (mutual base-world 0 "Missing")]
      (is (thrown? Exception (declaration/admit world env declaration {:allow-unsafe? true}))))
    (is (nil? (.lookup ^Env env (name/from-string "f"))))
    (is (nil? (.lookup ^Env env (name/from-string "g"))))))

(deftest source-inductive-and-quotient-generation-is-explicitly-not-admitted
  (let [[world type] (guest/ctor (m/world {}) 3 [guest/nil-tag] 8)
        [world n] (guest/guest-name world "Tiny")
        [world c] (guest/guest-name world "Tiny.mk")
        [world ind-type] (guest/constant world "Tiny")
        [world ctor] (guest/ctor world 0 [c ind-type] 0)
        [world ctors] (guest-list world [ctor])
        [world ind] (guest/ctor world 0 [n type ctors] 0)
        [world types] (guest-list world [ind])
        [world declaration] (guest/ctor world 6 [guest/nil-tag 0 types] 1)
        projected (declaration/project-declaration world declaration)]
    (is (= :inductive (:kind projected)))
    (is (= "Tiny" (str (get-in projected [:types 0 :name]))))
    (is (= "Tiny.mk" (str (get-in projected [:types 0 :constructors 0 :name]))))
    (is (false? (:unsafe? projected)))
    (is (thrown-with-msg? Exception #"complete generated constant family"
          (declaration/admit world (Env.) declaration))))
  (doseq [quot [4 (m/->Tag 4)]]
    (is (= :quotient (:kind (declaration/project-declaration (m/world {}) quot))))
    (is (thrown-with-msg? Exception #"complete generated constant family"
          (declaration/admit (m/world {}) (Env.) quot)))))

(deftest single-definitions-preserve-safety-specific-native-checking-rules
  (let [{:keys [world values] :as source} (fixture) env (base-env source)
        unsafe (get values "unsafeA") value (first (:fields (m/node world unsafe)))
        partial-world (guest/scalar! world value 0 "uint8" 2)
        unsafe-result (declaration/admit world env unsafe {:allow-unsafe? true})
        partial-result (declaration/admit partial-world env unsafe {:allow-unsafe? true})
        [world type] (guest/constant world "A")
        [world body] (guest/constant world "singleRec")
        [world recursive] (guest/declaration world "singleRec" type body)
        payload (first (:fields (m/node world recursive)))
        unsafe-world (guest/scalar! world payload 0 "uint8" 0)
        recursive-partial (guest/scalar! world payload 0 "uint8" 2)]
    (is (= :definition (:kind unsafe-result)))
    (is (= 1 (.safety ^ConstantInfo (:constant unsafe-result))))
    (is (= 2 (.safety ^ConstantInfo (:constant partial-result))))
    (is (identical? partial-world (:world partial-result)))
    (is (thrown-with-msg? Exception #"explicit host policy" (declaration/admit world env unsafe)))
    (is (some? (.lookup ^Env (:env (declaration/admit unsafe-world env recursive {:allow-unsafe? true}))
                         (name/from-string "singleRec"))))
    ;; Native single .partial checks before adding its own header, in SAFE mode.
    (is (thrown? Exception (declaration/admit recursive-partial env recursive {:allow-unsafe? true})))
    (is (nil? (.lookup ^Env env (name/from-string "singleRec"))))))
