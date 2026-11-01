(ns research.checked-delta-checks
  (:require [clojure.test :refer [deftest is run-tests]]
            [research.checked-delta :as delta]
            [prototype.imported-kernel :as imported]
            [prototype.imported-kernel-test :as fixture]
            [prototype.kernel-bridge-test :as guest]
            [prototype.module-store :as store]
            [prototype.machine :as m]
            [ansatz.kernel.level :as level]
            [ansatz.kernel.name :as name])
  (:import [ansatz.kernel Env ConstantInfo]))

(def helpers {:root ["checked-root"] :constants ["checked-constants"] :quot-init? ["checked-quot"]})
(def helper-leaf ["checked-helper-leaf"])
(defn functions []
  (let [f (fn [] {:params [1] :body [:return [:var 1]]})]
    {(helpers :root) (assoc (f) :runtime-dependencies [helper-leaf])
     (helpers :constants) (f) (helpers :quot-init?) (f) helper-leaf (f)}))
(defn context [functions root values quot]
  {:trusted-functions functions :bindings {} :trusted-bindings {}
   :invoke (fn [world target _]
             (cond
               (= target (helpers :root)) [(m/retain world root 1) root]
               (= target (helpers :quot-init?)) [world quot]
               (= target (helpers :constants))
               (m/allocate (reduce #(m/retain %1 %2 1) world values) :array 246 values)
               :else (throw (ex-info "Unexpected test helper invocation" {:target target}))))})
(defn issue
  ([] (issue (fixture/loaded)))
  ([loaded] (issue loaded (fixture/values loaded)))
  ([loaded values]
   (let [world (:world loaded)
         certificate (imported/verify-constants world values fixture/policy)
         functions (functions) [world root] (m/allocate (assoc world :functions functions) :ctor 0 [])
         context (context functions root values (if (.isQuotEnabled ^Env (:env certificate)) 1 0))
         world (imported/associate-checked context world root helpers certificate)
         [world cap] (delta/capture-base context world root helpers certificate)]
     {:world world :cap cap :context context :root root :values values :certificate certificate
      :functions functions :refs (fixture/by-name loaded)})))
(defn add-definition [world refs label body-name]
  (let [a (get refs "A") cv (first (:fields (m/node world (fixture/payload world a))))
        type (nth (:fields (m/node world cv)) 2)
        [world body] (guest/constant world body-name)]
    (guest/declaration world label type body)))

(deftest extension-checks-only-new-groups-against-the-exact-base
  (let [{:keys [world cap context values certificate refs]} (issue)
        [world first-ref] (add-definition world refs "deltaFirst" "aliasA")
        [world second-ref] (add-definition world refs "deltaSecond" "deltaFirst")
        world (assoc-in world [:functions ["unrelated-new-source-function"]] {:params [] :body [:return [:imm 0]]})
        result (with-redefs [imported/verify-constants (fn [& _] (throw (ex-info "Whole baseline checker called again" {})))]
                 (delta/verify-extension context world (into values [second-ref first-ref]) cap {}))]
    (is (= 19 (count (:constants result))))
    (is (= 2 (count (:new-order result))))
    (is (= ["deltaFirst" "deltaSecond"] (mapv #(str (second %)) (:new-order result))))
    (is (not (identical? (:env result) (:env certificate))))
    (doseq [[n ci] (:projected certificate)]
      (is (identical? ci (.lookup ^Env (:env result) n))))
    (is (nil? (.lookup ^Env (:env certificate) (name/from-string "deltaFirst"))))
    (is (identical? (:kernel-environments world) (:kernel-environments (:world result)))))
  (let [{:keys [world cap context values certificate]} (issue)
        result (delta/verify-extension context world values cap {})]
    (is (identical? (:env certificate) (:env result)))))

(deftest inherited-references-shapes-and-domain-cannot-change
  (let [{:keys [world cap context values refs]} (issue)
        alias (get refs "aliasA") payload (fixture/payload world alias)
        [changed replacement-expression] (guest/constant world "Tiny")
        changed (assoc-in changed [:heap (:id payload) :fields 1] replacement-expression)
        node (m/node world alias) [replaced replacement] (m/allocate world :ctor (:tag node) (:fields node))]
    (is (thrown-with-msg? Exception #"shape changed" (delta/verify-extension context changed values cap {})))
    (is (thrown-with-msg? Exception #"Missing or replaced" (delta/verify-extension context world (filterv #(not= alias %) values) cap {})))
    (is (thrown-with-msg? Exception #"Missing or replaced" (delta/verify-extension context replaced (mapv #(if (= alias %) replacement %) values) cap {})))
    (is (thrown-with-msg? Exception #"Duplicate" (delta/verify-extension context world (conj values alias) cap {})))
    (is (thrown-with-msg? Exception #"issued live" (delta/verify-extension context world values {:verified true :env (:env (:certificate (issue)))} {})))))

(deftest current-helper-invoker-closure-anchor-and-quotient-are-checked
  (let [{:keys [world cap context values root functions]} (issue)
        changed (assoc-in world [:functions helper-leaf] {:params [1] :body [:return [:imm 0]]})
        rebound (assoc context :trusted-functions (:functions changed))]
    (is (thrown-with-msg? Exception #"helper executable identity" (delta/verify-extension context changed values cap {})))
    (is (thrown-with-msg? Exception #"protected helper closure" (delta/verify-extension rebound changed values cap {})))
    (is (thrown-with-msg? Exception #"quotient state" (delta/verify-extension (research.checked-delta-checks/context functions root values 0) world values cap {})))
    (is (thrown-with-msg? Exception #"association" (delta/verify-extension context (assoc-in world [:kernel-environments (:id root) :env] (Env.)) values cap {})))
    (is (thrown-with-msg? Exception #"helper executable identity" (delta/verify-extension context (update world :functions dissoc helper-leaf) values cap {})))))

(deftest protected-raw-helper-bindings-require-independent-and-stable-owners
  (let [{:keys [world context root values certificate functions]} (issue)
        symbol "research_checked_root"
        functions (update functions (helpers :root) assoc :raw-extern {:symbol symbol})
        world (assoc world :functions functions)
        binding {:handler (fn [_] :authorized)} replacement {:handler (fn [_] :different)}
        context (assoc context :trusted-functions functions
                       :bindings {symbol binding} :trusted-bindings {symbol binding})
        [world cap] (delta/capture-base context world root helpers certificate)]
    (is (identical? (:env certificate) (:env (delta/verify-extension context world values cap {}))))
    (is (thrown-with-msg? Exception #"independent identity"
                         (delta/verify-extension (assoc context :bindings {symbol replacement}) world values cap {})))
    (is (thrown-with-msg? Exception #"protected helper closure"
                         (delta/verify-extension (assoc context :bindings {symbol replacement} :trusted-bindings {symbol replacement})
                                                 world values cap {})))))

(deftest new-proofs-axioms-and-unsafe-bodies-still-use-the-kernel
  (let [{:keys [world cap context values refs]} (issue)
        proof (get refs "identityProof") proof-payload (fixture/payload world proof)
        [constant _ all] (:fields (m/node world proof-payload))
        [world bad-value] (guest/constant world "A")
        constant-node (m/node world constant)
        [world bad-name] (guest/guest-name world "badNewProof")
        [world all] (guest/ctor world 1 [bad-name guest/nil-tag] 0)
        [world cv] (guest/ctor world 0 (assoc (:fields constant-node) 0 bad-name) 0)
        [world payload] (guest/ctor world 0 [cv bad-value all] 0)
        [world bad-proof] (guest/ctor world 2 [payload] 0)
        [world safe-def] (add-definition world refs "newUnsafe" "aliasA")
        unsafe (fixture/payload world safe-def)
        world (guest/scalar! world unsafe 0 "uint8" 0)
        a (get refs "A") cv (first (:fields (m/node world (fixture/payload world a))))
        type (nth (:fields (m/node world cv)) 2)
        [world axiom] (guest/axiom-declaration world "newAssumption" type)]
    (is (thrown? Exception (delta/verify-extension context world (conj values bad-proof) cap {})))
    (is (thrown-with-msg? Exception #"axiom" (delta/verify-extension context world (conj values axiom) cap {})))
    (is (= 18 (count (:constants (delta/verify-extension context world (conj values axiom) cap {:allow-axioms? true})))))
    (is (thrown-with-msg? Exception #"unsafe/partial" (delta/verify-extension context world (conj values safe-def) cap {})))
    (is (= 18 (count (:constants (delta/verify-extension context world (conj values safe-def) cap {:allow-unsafe? true})))))))

(deftest capture-rejects-unanchored-incomplete-and-external-environments
  (let [{:keys [world context root values certificate]} (issue)]
    (is (thrown-with-msg? Exception #"positive checked association"
                         (delta/capture-base context (dissoc world :kernel-environments) root helpers certificate)))
    (is (thrown-with-msg? Exception #"incomplete Java"
                         (delta/capture-base context world root helpers (update certificate :projected dissoc (first (keys (:projected certificate)))))))
    (is (thrown-with-msg? Exception #"Lazy/external"
                         (delta/capture-base context world root helpers
                                             (assoc certificate :env (.withExternalLookup ^Env (:env certificate) (fn [_] nil) 999)))))
    (is (thrown-with-msg? Exception #"enumeration"
                         (delta/capture-base (assoc context :invoke (:invoke (research.checked-delta-checks/context (:functions world) root [] 1)))
                                             world root helpers certificate)))))

(deftest immutable-source-lease-shadow-and-identity-are-mandatory
  (let [loaded (store/load-file (m/world {}) "fixtures/imported-kernel-native.jsonl")
        other (store/load-file (m/world {}) "fixtures/imported-kernel-native.jsonl")]
    (try
      (let [{:keys [world cap context values certificate]} (issue loaded)
            calls (atom 0) project imported/project-constant
            result (with-redefs [imported/project-constant (fn [& args] (swap! calls inc) (apply project args))]
                     (delta/verify-extension context world values cap {}))]
        (is (zero? @calls))
        (is (identical? (:env certificate) (:env result)))
        (is (thrown-with-msg? Exception #"source identity"
                             (delta/verify-extension context (assoc world :native-imports [(:source other)]) values cap {})))
        (is (thrown-with-msg? Exception #"shadowed"
                             (delta/verify-extension context (assoc-in world [:heap (:id (first values))] {:kind :ctor :tag 0 :fields [] :rc 1}) values cap {})))
        (.close ^java.io.Closeable (:source loaded))
        (is (thrown-with-msg? Exception #"lease is closed" (delta/verify-extension context world values cap {}))))
      (finally (.close ^java.io.Closeable (:source loaded)) (.close ^java.io.Closeable (:source other))))))

(deftest new-inductive-bundle-is-checked-as-a-complete-group
  (let [loaded (fixture/loaded) refs (fixture/by-name loaded) full (fixture/values loaded)
        ;; The native fixture also exports Tiny.recOn, which depends on the
        ;; family. It cannot remain in an independently checked base.
        tiny (set (for [[label ref] refs :when (or (= "Tiny" label) (.startsWith ^String label "Tiny."))] ref))
        base-values (filterv #(not (contains? tiny %)) full)
        {:keys [world context cap certificate]} (issue loaded base-values)
        checked (delta/verify-extension context world full cap {})
        recursor (m/node world (fixture/payload world (get refs "Tiny.rec")))
        rules (nth (:fields recursor) 6) rule (first (:fields (m/node world rules)))
        type (nth (:fields (m/node world (first (:fields recursor)))) 2)
        changed (assoc-in world [:heap (:id rule) :fields 2] type)]
    (is (= 13 (count (:constants certificate))))
    (is (= 17 (count (:constants checked))))
    (is (= :inductive (ffirst (:new-order checked))))
    (is (= 2 (count (:new-order checked))))
    (doseq [omitted [(get refs "Tiny.mk") (get refs "Tiny.rec")]]
      (is (thrown? Exception (delta/verify-extension context world (filterv #(not= omitted %) full) cap {}))))
    (is (thrown? Exception (delta/verify-extension context changed full cap {})))
    (is (nil? (.lookup ^Env (:env certificate) (name/from-string "Tiny"))))))

(defn- mutual-pair [world]
  (let [[world level] (guest/ctor world 1 [guest/nil-tag] 8)
        [world type] (guest/ctor world 3 [level] 8)
        [world a] (guest/constant world "deltaA") [world b] (guest/constant world "deltaB")
        [world da] (guest/declaration world "deltaA" type b)
        [world db] (guest/declaration world "deltaB" type a)
        pa (fixture/payload world da) pb (fixture/payload world db)
        na (first (:fields (m/node world (first (:fields (m/node world pa))))))
        nb (first (:fields (m/node world (first (:fields (m/node world pb))))))
        [world tail] (guest/ctor world 1 [nb guest/nil-tag] 0)
        [world all] (guest/ctor world 1 [na tail] 0)
        world (-> world (assoc-in [:heap (:id pa) :fields 3] all) (assoc-in [:heap (:id pb) :fields 3] all))]
    {:safe world :unsafe (-> world (guest/scalar! pa 0 "uint8" 0) (guest/scalar! pb 0 "uint8" 0))
     :a da :b db}))

(deftest new-unsafe-mutual-group-and-safe-cycle-retain-existing-policy
  (let [{:keys [world context cap values]} (issue)
        {:keys [safe unsafe a b]} (mutual-pair world)
        result (delta/verify-extension context unsafe (into values [b a]) cap {:allow-unsafe? true})]
    (is (= 19 (count (:constants result))))
    (is (= :mutual (ffirst (:new-order result))))
    (is (thrown-with-msg? Exception #"Incomplete.*mutual"
                         (delta/verify-extension context unsafe (conj values a) cap {:allow-unsafe? true})))
    (is (thrown-with-msg? Exception #"unsafe/partial"
                         (delta/verify-extension context unsafe (into values [a b]) cap {})))
    (is (thrown-with-msg? Exception #"recursive"
                         (delta/verify-extension context safe (into values [a b]) cap {})))))

(defn- exception [thunk]
  (try (thunk) nil (catch clojure.lang.ExceptionInfo e e)))
(defn- allocating-context [context]
  (assoc context :invoke
         (fn [world target args]
           (let [[world scratch] (m/allocate world :ctor 0 [])
                 world (m/release world scratch 1)]
             ((:invoke context) world target args)))))

(deftest late-failures-publish-actual-helper-progress-and-owner-evidence
  (let [{:keys [world context cap values refs root]} (issue)
        [changed replacement] (guest/constant world "Tiny")
        changed (assoc-in changed [:heap (:id (fixture/payload changed (get refs "aliasA"))) :fields 1] replacement)
        late (exception #(delta/verify-extension (allocating-context context) changed values cap {}))
        packet (ex-data late)]
    (is (= :inherited-shapes (:stage packet)))
    (is (= (+ 2 (:next-id changed)) (:next-id (:checkpoint packet))))
    (is (= (+ 2 (get-in changed [:stats :allocations])) (get-in packet [:checkpoint :stats :allocations])))
    (is (= [] (:temporary-owners packet)))
    (is (= (:rc (m/node changed root)) (:rc (m/node (:checkpoint packet) root))))
    (let [[world bad] (add-definition world refs "badLate" "aliasA")
          cv (first (:fields (m/node world (fixture/payload world (get refs "A")))))
          sort-one (nth (:fields (m/node world cv)) 2)
          world (assoc-in world [:heap (:id (fixture/payload world bad)) :fields 1] sort-one)
          failure (exception #(delta/verify-extension (allocating-context context) world (conj values bad) cap {}))]
      (is (= :check (first (:stage (ex-data failure)))))
      (is (= (+ 2 (:next-id world)) (get-in (ex-data failure) [:checkpoint :next-id]))))
    (let [failing (assoc context :invoke
                         (fn [world target args]
                           (if (= target (helpers :quot-init?))
                             (throw (ex-info "injected quotient helper failure" {:checkpoint world}))
                             ((:invoke context) world target args))))
          failure (exception #(delta/verify-extension failing world values cap {})) packet (ex-data failure)]
      (is (= [:helper :quot-init?] (:stage packet)))
      (is (= [root] (:temporary-owners packet)))
      (is (= (inc (:rc (m/node world root))) (:rc (m/node (:checkpoint packet) root))))
      (is (= (:rc (m/node world root)) (:rc (m/node (m/release (:checkpoint packet) root 1) root)))))
    (let [release m/release
          failure (with-redefs [m/release (fn [world value n]
                                           (if (= value root)
                                             (throw (ex-info "injected helper owner release failure" {}))
                                             (release world value n false)))]
                    (exception #(delta/verify-extension context world values cap {})))
          packet (ex-data failure)]
      (is (= :helper-release (:stage packet)))
      (is (= [root 1] (:temporary-owners packet)))
      (is (= (inc (:rc (m/node world root))) (:rc (m/node (:checkpoint packet) root)))))))

(deftest retained-java-base-mutation-is-rejected-before-checking-additions
  (let [{:keys [world cap context values certificate]} (issue)
        ^ConstantInfo ci (get (:projected certificate) (name/from-string "aliasA"))
        original (.value ci)]
    (try
      (set! (.value ci) (.type ci))
      (is (thrown-with-msg? Exception #"Inherited Java ConstantInfo"
                           (delta/verify-extension context world values cap {})))
      (finally (set! (.value ci) original)))
    (is (identical? (:env certificate) (:env (delta/verify-extension context world values cap {})))))
  (let [{:keys [world cap context values certificate]} (issue)
        ^ConstantInfo ci (get (:projected certificate) (name/from-string "Tiny"))
        original (aget (.ctors ci) 0)]
    (try
      (aset (.ctors ci) 0 (name/from-string "MissingCtor"))
      (is (thrown-with-msg? Exception #"Inherited Java ConstantInfo"
                           (delta/verify-extension context world values cap {})))
      (finally (aset (.ctors ci) 0 original))))
  (let [{:keys [world cap context values certificate]} (issue)
        [levels captured] (first (filter #(seq (second %)) (#'delta/expression-array-witnesses certificate)))]
    (is (some? levels) "Fixture includes a nested nonempty CONST universe array")
    (let [original (aget ^objects levels 0)]
      (try
        (aset ^objects levels 0 (level/succ original))
        (is (thrown-with-msg? Exception #"Java expression universe array changed"
                             (delta/verify-extension context world values cap {})))
        (finally (aset ^objects levels 0 original))))))

(deftest quotient-bootstrap-can-extend-a-checked-nonquotient-base
  (let [loaded (fixture/loaded) full (fixture/values loaded) refs (fixture/by-name loaded)
        quartet (set (map refs ["Quot" "Quot.mk" "Quot.lift" "Quot.ind"]))
        {:keys [world cap context certificate]} (issue loaded (filterv #(not (contains? quartet %)) full))
        checked (delta/verify-extension context world full cap {})]
    (is (false? (.isQuotEnabled ^Env (:env certificate))))
    (is (true? (.isQuotEnabled ^Env (:env checked))))
    (is (= 4 (count (:new-order checked))))
    (is (= 17 (count (:constants checked))))
    (is (thrown-with-msg? Exception #"all four canonical"
                         (delta/verify-extension context world (filterv #(not= % (get refs "Quot.ind")) full) cap {})))))

(defn check! [] (run-tests 'research.checked-delta-checks))
