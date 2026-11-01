(ns prototype.imported-kernel-test
  (:require [clojure.test :refer [deftest is]] [clojure.set :as set] [prototype.imported-kernel :as imported]
            [prototype.module-data :as data] [prototype.machine :as m]
            [prototype.kernel-bridge-test :as guest] [prototype.scalar :as scalar]
            [ansatz.kernel.name :as name]
            [prototype.kernel-projection-snapshot :as snapshot])
  (:import [ansatz.kernel Env ConstantInfo Expr Level Name]))

(def policy {:allow-axioms? true :allow-unsafe? true})
(defn loaded [] (data/load-file (m/world {}) "fixtures/imported-kernel-native.jsonl"))
(defn entries [loaded] (mapcat #(imported/module-constants (:world loaded) %) (:roots loaded)))
(defn values [loaded] (mapv :guest (entries loaded)))
(defn by-name [loaded] (into {} (map (fn [{:keys [^ConstantInfo constant guest]}] [(str (.name constant)) guest])) (entries loaded)))
(defn payload [world ci] (first (:fields (m/node world ci))))

(deftest native-all-eight-constant-variants-are-strictly-replayed
  ;; Fixture producer: pinned4.33.1 ModuleDataTransport single KernelImportProbe,
  ;; native address-free DAG roundtrip verified; source is fixtures/lean/KernelImportProbe.lean.
  (let [loaded (loaded) world (:world loaded) before world refs (by-name loaded)
        result (imported/verify-module-data world (:roots loaded) policy)
        reversed (imported/verify-constants world (vec (reverse (values loaded))) policy)
        ^Env checked (:env result)]
    (is (= 17 (count (:constants result))))
    (is (= (set (range 8)) (set (map #(.tag ^ConstantInfo (:constant %)) (entries loaded)))))
    (is (= (set (keys (:constants result))) (set (keys (:constants reversed)))))
    (is (.isQuotEnabled checked))
    (is (= #{"A"} (set (map str (:axioms result)))))
    (is (= refs (into {} (map (fn [[k v]] [(str k) v])) (:constants result))))
    (is (= before world))
    (is (nil? (.lookup (Env.) (name/from-string "aliasA"))))
    (is (= 1 (.safety ^ConstantInfo (.lookup checked (name/from-string "unsafeA")))))))

(deftest policy-and-malformed-dependencies-cannot-publish-a-partial-environment
  (let [loaded (loaded) world (:world loaded) refs (by-name loaded)
        alias (get refs "aliasA")
        [changed missing] (guest/constant world "Missing")
        changed (assoc-in changed [:heap (:id (payload world alias)) :fields 1] missing)]
    (is (thrown-with-msg? Exception #"axiom admission" (imported/verify-constants world (values loaded) {:allow-unsafe? true})))
    (is (thrown-with-msg? Exception #"unsafe/partial" (imported/verify-constants world (values loaded) {:allow-axioms? true})))
    (is (thrown-with-msg? Exception #"Unresolved" (imported/verify-constants changed (values loaded) policy)))
    (is (not (contains? world :kernel-environments)))
    (is (thrown-with-msg? Exception #"Duplicate imported" (imported/verify-constants world [(get refs "A") (get refs "A")] policy)))
    (is (= 17 (count (:constants (imported/verify-module-data world (concat (:roots loaded) (:roots loaded)) policy)))))))

(deftest imported-inductive-rules-and-members-are-checked
  (let [loaded (loaded) world (:world loaded) refs (by-name loaded)
        recursor (m/node world (payload world (get refs "Tiny.rec")))
        rules (nth (:fields recursor) 6)
        rule (first (:fields (m/node world rules)))
        type (nth (:fields (m/node world (first (:fields recursor)))) 2)
        invalid (assoc-in world [:heap (:id rule) :fields 2] type)]
    (is (thrown? Exception (imported/verify-constants invalid (values loaded) policy)))
    (is (thrown-with-msg? Exception #"constructor group"
          (imported/verify-constants world (filterv #(not= % (get refs "Tiny.mk")) (values loaded)) policy)))))

(deftest quotient-kind-and-signature-must-both-match
  (let [loaded (loaded) world (:world loaded) refs (by-name loaded)
        quot (get refs "Quot") qval (payload world quot)
        invalid-kind (guest/scalar! world qval 0 "uint8" 1)
        base (first (:fields (m/node world qval)))
        [world bad-type] (guest/ctor world 3 [guest/nil-tag] 8)
        invalid-type (assoc-in world [:heap (:id base) :fields 2] bad-type)]
    (is (thrown-with-msg? Exception #"name/kind" (imported/project-constant invalid-kind quot)))
    (is (thrown-with-msg? Exception #"quotient declaration" (imported/verify-constants invalid-type (values loaded) policy)))))

(def helper-names {:root ["root"] :constants ["constants"] :quot-init? ["quot"]})
(defn context [root constants quot?]
  {:invoke (fn [world target _]
             (cond (= target (:root helper-names)) [(m/retain world root 1) root]
                   (= target (:constants helper-names)) (m/allocate world :array 246 constants)
                   (= target (:quot-init? helper-names)) [world quot?]))})
(deftest association-checks-exact-guest-coverage-and-retains-an-anchor
  (let [loaded (loaded) world (:world loaded)
        certificate (imported/verify-constants world (values loaded) policy)
        [world root] (m/allocate world :ctor 0 [])
        ctx (context root (values loaded) 1)
        associated (imported/associate-checked ctx world root helper-names certificate)
        entry (get-in associated [:kernel-environments (:id root)])]
    (is (identical? (:env certificate) (:env entry)))
    (is (= root (:anchor entry)))
    (is (= 2 (:rc (m/node associated root))))
    (is (= 1 (:rc (m/node world root))))
    (is (nil? (:kernel-environments world)))
    (is (= (:next-id world) (dec (:next-id associated))))
    (is (thrown-with-msg? Exception #"differs from checked constants"
          (imported/associate-checked (context root [] 1) world root helper-names certificate)))
    (is (thrown-with-msg? Exception #"quotient state"
          (imported/associate-checked (context root (values loaded) 0) world root helper-names certificate)))
    (is (thrown-with-msg? Exception #"already anchored"
          (imported/associate-checked ctx associated root helper-names certificate)))))

(deftest exact-compiler-marker-policy-does-not-enable-other-unsafe-axioms
  (let [[world level] (guest/ctor (m/world {}) 1 [guest/nil-tag] 8)
        [world type] (guest/ctor world 3 [level] 8)
        [world marker] (guest/compiler-marker world "lcAny" type)
        [world other] (guest/compiler-marker world "notAMarker" type)
        checked (imported/verify-constants world [marker] {:allow-compiler-markers? true})]
    (is (= 1 (count (:constants checked))))
    (is (.isUnsafe ^ConstantInfo (.lookup ^Env (:env checked) (name/from-string "lcAny"))))
    (is (thrown-with-msg? Exception #"axiom admission"
          (imported/verify-constants world [other] {:allow-compiler-markers? true})))))

(deftest unsafe-mutual-bodies-are-checked-together-while-safe-cycles-fail
  (let [[world level] (guest/ctor (m/world {}) 1 [guest/nil-tag] 8)
        [world type] (guest/ctor world 3 [level] 8)
        [world a] (guest/constant world "a") [world b] (guest/constant world "b")
        [world da] (guest/declaration world "a" type b)
        [world db] (guest/declaration world "b" type a)
        pa (payload world da) pb (payload world db)
        na (first (:fields (m/node world (first (:fields (m/node world pa))))))
        nb (first (:fields (m/node world (first (:fields (m/node world pb))))))
        [world tail] (guest/ctor world 1 [nb guest/nil-tag] 0)
        [world all] (guest/ctor world 1 [na tail] 0)
        world (-> world (assoc-in [:heap (:id pa) :fields 3] all)
                        (assoc-in [:heap (:id pb) :fields 3] all))
        unsafe (-> world (guest/scalar! pa 0 "uint8" 0) (guest/scalar! pb 0 "uint8" 0))
        checked (imported/verify-constants unsafe [db da] {:allow-unsafe? true})]
    (is (= 2 (count (:constants checked))))
    (is (= :mutual (ffirst (:order checked))))
    (is (thrown-with-msg? Exception #"recursive"
          (imported/verify-constants world [da db])))))

(deftest certificate-cannot-be-reused-after-a-fork-changes-a-constant
  (let [loaded (loaded) world (:world loaded) refs (by-name loaded)
        certificate (imported/verify-constants world (values loaded) policy)
        alias (get refs "aliasA")
        [world replacement] (guest/constant world "Tiny")
        changed (assoc-in world [:heap (:id (payload world alias)) :fields 1] replacement)
        [changed root] (m/allocate changed :ctor 0 [])]
    (is (thrown-with-msg? Exception #"checked projection"
          (imported/associate-checked (context root (values loaded) 1) changed root helper-names certificate)))))

(deftest quotient-bootstrap-requires-the-equality-family-and-complete-primitive-set
  (let [loaded (loaded) world (:world loaded) refs (by-name loaded)
        eq (get refs "Eq")
        base (first (:fields (m/node world (payload world eq))))
        [world axiom-value] (guest/ctor world 0 [base] 1)
        [world fake-eq] (guest/ctor world 0 [axiom-value] 0)
        values-without-eq-family (mapv (fn [[label value]] (if (= "Eq" label) fake-eq value))
                                   (remove (fn [[label _]] (.startsWith ^String label "Eq.")) refs))]
    (is (thrown-with-msg? Exception #"all four canonical"
          (imported/verify-constants world (filterv #(not= % (get refs "Quot.ind")) (values loaded)) policy)))
    (is (thrown-with-msg? Exception #"canonical checked Eq family"
          (imported/verify-constants world values-without-eq-family policy)))))

(deftest imported-association-optionally-anchors-exact-constant-map-witness
  (let [loaded (loaded) world (:world loaded)
        certificate (imported/verify-constants world (values loaded) policy)
        [world root] (m/allocate world :ctor 0 [])
        [world constants] (m/allocate world :ctor 0 [])
        old-context (context root (values loaded) 1)
        helpers (assoc helper-names :constant-map ["constant-map"])
        ctx {:invoke (fn [world target args]
                        (if (= target ["constant-map"])
                          [(m/retain world constants 1) constants]
                          ((:invoke old-context) world target args)))}
        associated (imported/associate-checked ctx world root helpers certificate)
        entry (get-in associated [:kernel-environments (:id root)])]
    (is (= constants (:constant-map entry)))
    (is (true? (:quot-init? entry)))
    (is (= 2 (:rc (m/node associated constants))))
    (is (= 1 (:rc (m/node world constants))))
    (is (nil? (:kernel-environments world)))))

(deftest complete-ordinary-imports-require-each-native-recursor
  (let [loaded (loaded) world (:world loaded) refs (by-name loaded)
        tiny-rec (get refs "Tiny.rec")
        rec-base (first (:fields (m/node world (payload world tiny-rec))))
        [renamed extra-name] (guest/guest-name world "Tiny.extraRec")
        renamed (assoc-in renamed [:heap (:id rec-base) :fields 0] extra-name)]
    (is (thrown-with-msg? Exception #"ordinary recursor group"
          (imported/verify-constants world (filterv #(not= tiny-rec %) (values loaded)) policy)))
    ;; Exact-set validation rejects an unexpected recursor even when its all
    ;; header, type and rules still belong to the correct ordinary family.
    (is (thrown-with-msg? Exception #"ordinary recursor group"
          (imported/verify-constants renamed (values loaded) policy))))
  (let [loaded (data/load-file (m/world {}) "fixtures/raw-inductive-native.jsonl")
        world (:world loaded)
        selected (filterv (fn [{:keys [^ConstantInfo constant]}]
                            (let [label (str (.name constant))]
                              (some #(or (= % label) (.startsWith label (str % "."))) ["MyNat" "Even" "Odd"])))
                          (entries loaded))
        refs (mapv :guest selected)
        odd-rec (:guest (first (filter #(= "Odd.rec" (str (.name ^ConstantInfo (:constant %)))) selected)))]
    (is (some? odd-rec))
    (is (= (count refs) (count (:constants (imported/verify-constants world refs policy)))))
    (is (thrown-with-msg? Exception #"ordinary recursor group"
          (imported/verify-constants world (filterv #(not= odd-rec %) refs) policy)))))

(deftest imported-mutual-headers-require-the-same-ordered-universe-list
  (doseq [safety [0 2]
          right [["u" "w"] ["v" "u"] ["u"] ["u" "v" "w"]]]
    (let [[world level] (guest/ctor (m/world {}) 1 [guest/nil-tag] 8)
          [world type] (guest/ctor world 3 [level] 8)
          [world da] (guest/declaration world "a" type type)
          [world db] (guest/declaration world "b" type type)
          pa (payload world da) pb (payload world db)
          ba (first (:fields (m/node world pa))) bb (first (:fields (m/node world pb)))
          na (first (:fields (m/node world ba))) nb (first (:fields (m/node world bb)))
          [world tail] (guest/ctor world 1 [nb guest/nil-tag] 0)
          [world all] (guest/ctor world 1 [na tail] 0)
          make-params (fn [world labels]
                        (reduce (fn [[world tail] label]
                                  (let [[world n] (guest/guest-name world label)]
                                    (guest/ctor world 1 [n tail] 0)))
                                [world guest/nil-tag] (reverse labels)))
          [world left-params] (make-params world ["u" "v"])
          [world right-params] (make-params world right)
          world (-> world
                    (assoc-in [:heap (:id pa) :fields 3] all)
                    (assoc-in [:heap (:id pb) :fields 3] all)
                    (assoc-in [:heap (:id ba) :fields 1] left-params)
                    (assoc-in [:heap (:id bb) :fields 1] right-params)
                    (guest/scalar! pa 0 "uint8" safety)
                    (guest/scalar! pb 0 "uint8" safety))]
      ;; Failure is explicitly from grouping, before checker/body validation.
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"same ordered universe"
            (imported/verify-constants world [da db] {:allow-unsafe? true})))
      (let [matching (assoc-in world [:heap (:id bb) :fields 1] left-params)
            projected (mapv #(hash-map :constant (imported/project-constant matching %)) [da db])]
        (is (= :mutual (first (:key (first (#'imported/groups projected))))))))))

;; Frozen pre-extraction plan construction: compare behavior and traversal order,
;; while retaining the old containers to make the lifetime negative control real.
(defn- historical-checking-plan [groups names]
  (let [by-key (into {} (map #(vector (:key %) %) groups))
        name->group (into {} (mapcat (fn [group] (map #(vector % (:key group)) (:names group))) groups))
        missing (set/difference (reduce set/union #{} (map :dependencies groups)) (set names))]
    (when (seq missing)
      (throw (ex-info "Unresolved imported kernel dependencies" {:missing missing})))
    (let [blockers (into {} (map (fn [group] [(:key group) (set (map name->group (:dependencies group)))]) groups))
          dependents (persistent!
                       (reduce-kv (fn [out key dependencies]
                                    (reduce (fn [out dependency]
                                              (assoc! out dependency (conj (get out dependency []) key)))
                                            out dependencies))
                                  (transient {}) blockers))
          degrees (into {} (map (fn [[key deps]] [key (count deps)]) blockers))
          ready (mapv :key (filter #(zero? (get degrees (:key %))) groups))]
      {:groups groups :by-key by-key :dependents dependents :degrees degrees :ready ready})))

(defn- plan-schedule [plan total]
  (loop [queue (:ready plan) cursor 0 degrees (:degrees plan)]
    (if (= cursor (count queue)) {:order queue :remaining (- total cursor)}
      (let [[degrees queue]
            (reduce (fn [[degrees queue] dependent]
                      (let [degree (dec (get degrees dependent))]
                        [(assoc degrees dependent degree)
                         (if (zero? degree) (conj queue dependent) queue)]))
                    [degrees queue] (get-in plan [:dependents (nth queue cursor)]))]
        (recur queue (inc cursor) degrees)))))

(defn- synthetic-groups [dependencies]
  (let [names (mapv #(name/from-string (str "PlanProbe." %)) (range (count dependencies)))]
    (mapv (fn [i deps]
            {:key [:single (nth names i)] :members [(Object.)]
             :names #{(nth names i)} :dependencies (set (map names deps))})
          (range) dependencies)))

(defn- build-only-identity-leaks [result groups]
  (let [allowed (java.util.IdentityHashMap.) forbidden (java.util.IdentityHashMap.)]
    (doseq [group groups]
      (.put allowed (:key group) true)
      (doseq [member (:members group)] (.put allowed member true)))
    (.put forbidden groups :group-vector)
    (doseq [group groups [label value] [[:group group] [:names (:names group)]
                                      [:dependencies (:dependencies group)]]]
      (when-not (.containsKey allowed value) (.put forbidden value label)))
    (loop [todo [result] seen (java.util.IdentityHashMap.) leaks []]
      (when (> (.size seen) 10000) (throw (ex-info "Identity walk exceeded tiny test bound" {})))
      (if (empty? todo) leaks
        (let [value (peek todo) todo (pop todo)]
          (cond
            (.containsKey allowed value) (recur todo seen leaks)
            (.containsKey forbidden value) (recur todo seen (conj leaks (.get forbidden value)))
            (.containsKey seen value) (recur todo seen leaks)
            :else (do (.put seen value true)
                      (recur (cond (map? value) (into todo (mapcat identity value))
                                   (coll? value) (into todo value)
                                   :else todo)
                             seen leaks))))))))

(deftest compact-checking-plan-preserves-historical-edges-degrees-and-order
  (let [native (loaded)
        projected (mapv #(hash-map :constant (imported/project-constant (:world native) %)) (values native))
        native-groups (#'imported/groups projected)
        cases (conj (mapv synthetic-groups
                         [[] [[]] [[] [0] [0] [1 2]] [[] [0] [1] [2]]
                          [[] [] [] []] [[1] [0]] [[] [0] [0] [0] [1 2 3]]])
                    native-groups)]
    (doseq [groups cases]
      (let [names (mapcat :names groups)
            old (historical-checking-plan groups names)
            plan (#'imported/checking-plan groups names)]
        (is (= (select-keys old [:dependents :degrees :ready])
               (select-keys plan [:dependents :degrees :ready])))
        (is (= (count groups) (:group-count plan)))
        (is (= (plan-schedule old (count groups)) (plan-schedule plan (:group-count plan))))
        (is (= (into {} (map (fn [[key group]] [key (:members group)])) (:by-key old))
               (:members-by-key plan)))
        (doseq [group groups]
          (is (identical? (:members group) (get (:members-by-key plan) (:key group))))
          (is (some #(identical? (:key group) %) (keys (:members-by-key plan)))))))))

(deftest compact-checking-plan-does-not-retain-build-only-group-containers
  (let [native (loaded)
        projected (mapv #(hash-map :constant (imported/project-constant (:world native) %)) (values native))]
    (let [groups (synthetic-groups [[] [0]])]
      ;; Each forbidden category is detected even without a parent group/vector.
      (is (= #{:group :names :dependencies}
             (set (build-only-identity-leaks
                    [{:hidden (first groups)} {:hidden (:names (first groups))}
                     {:hidden (:dependencies (second groups))}] groups)))))
    (doseq [groups [(synthetic-groups [[] [0] [0] [1 2]]) (#'imported/groups projected)]]
      (let [names (mapcat :names groups)
            old (historical-checking-plan groups names)
            plan (#'imported/checking-plan groups names)]
        ;; The historical result really retains forbidden input identities.
        (is (seq (build-only-identity-leaks old groups)))
        (is (empty? (build-only-identity-leaks plan groups)))))))

(deftest compact-checking-plan-preserves-missing-dependency-error-data
  (let [groups (synthetic-groups [[] [0]])
        missing (name/from-string "PlanProbe.missing")
        invalid (assoc-in groups [1 :dependencies] #{missing})
        names (mapcat :names groups)
        failure (fn [build]
                  (try (build invalid names) nil
                       (catch clojure.lang.ExceptionInfo cause
                         [(.getMessage cause) (ex-data cause)])))]
    (is (= ["Unresolved imported kernel dependencies" {:missing #{missing}}]
           (failure #'imported/checking-plan)))
    (is (= (failure historical-checking-plan) (failure #'imported/checking-plan)))))


(defrecord AlternateCIRef [id])
(defn alternate-ci-carrier [world]
  (let [scope (Object.) live (atom true) reads (atom []) checks (atom 0)
        encode (fn [v] (if (m/ref? v) (->AlternateCIRef (:id v)) v))
        operations {:ref? #(instance? AlternateCIRef %)
                    :check! #(do (swap! checks inc)
                                 (when-not @live (throw (ex-info "Alternate carrier closed" {}))))
                    :node (fn [current v]
                            (when-not (and @live (identical? current scope))
                              (throw (ex-info "Alternate carrier scope mismatch/closed" {})))
                            (swap! reads conj (:id v))
                            (let [node (m/node world (m/->Ref (:id v)))]
                              (update node :fields #(mapv encode %))))}]
    {:world scope :operations operations :encode encode :live live :reads reads :checks checks}))

(deftest all-eight-imported-variants-use-the-same-carrier-semantic-core
  (let [loaded (loaded) world (:world loaded) refs (values loaded)
        carrier (alternate-ci-carrier world)
        project (imported/make-constant-projector (:world carrier) (:operations carrier)
                  {:max-visits 1000000 :max-rule-nodes 1000})]
    (doseq [guest refs]
      (let [old (imported/project-constant world guest)
            alternate (project (:world carrier) ((:encode carrier) guest))
            inventory (imported/project-constant-name-kind (:world carrier) ((:encode carrier) guest)
                        {:max-nodes 100 :max-chars 1000} (:operations carrier))]
        (is (= (imported/checking-shape old) (imported/checking-shape alternate)))
        (is (= {:name (.name ^ConstantInfo old) :kind (.tag ^ConstantInfo old)} inventory))))
    (is (pos? @(:checks carrier)))
    (reset! (:live carrier) false)
    ;; A prior semantic memo hit must still consult the exact carrier lifetime.
    (is (thrown-with-msg? Exception #"closed" (project (:world carrier) ((:encode carrier) (first refs)))))
    (is (thrown-with-msg? Exception #"different world" (project (Object.) ((:encode carrier) (first refs)))))))

(deftest bounded-imported-inventory-does-not-touch-types-or-values
  (let [loaded (loaded) world (:world loaded) guest (get (by-name loaded) "aliasA")
        base (first (:fields (m/node world (payload world guest))))
        type (nth (:fields (m/node world base)) 2)
        carrier (alternate-ci-carrier world)
        result (imported/project-constant-name-kind (:world carrier) ((:encode carrier) guest)
                 {:max-nodes 100 :max-chars 1000} (:operations carrier))]
    (is (= "aliasA" (str (:name result))))
    (is (= ConstantInfo/DEF (:kind result)))
    (is (not (some #{(:id type)} @(:reads carrier))))
    (is (thrown-with-msg? Exception #"spine-node limit"
          (imported/project-constant-name-kind (:world carrier) ((:encode carrier) guest)
            {:max-nodes 1 :max-chars 1000} (:operations carrier))))))

(deftest recursor-rule-list-shares-the-carrier-lifetime-and-total-visit-budget
  (let [loaded (loaded) world (:world loaded) refs (by-name loaded)
        guest (get refs "Tiny.rec") carrier (alternate-ci-carrier world)
        rules (nth (:fields (m/node world (payload world guest))) 6)
        cyclic (assoc-in world [:heap (:id rules) :fields 1] rules)
        too-short (imported/make-constant-projector (:world carrier) (:operations carrier)
                    {:max-visits 1 :max-rule-nodes 1000})]
    (is (thrown-with-msg? Exception #"total visit limit"
          (too-short (:world carrier) ((:encode carrier) guest))))
    (is (thrown-with-msg? Exception #"Cyclic imported kernel list"
          (imported/project-constant cyclic guest)))
    ;; Explicitly duplicate the genuine rule entry to exercise the list bound
    ;; without assuming the fixture has a multi-constructor inductive.
    (let [rule (first (:fields (m/node world rules)))
          [extended extra] (guest/ctor world 1 [rule rules] 0)
          extended (assoc-in extended [:heap (:id (payload world guest)) :fields 6] extra)
          carrier (alternate-ci-carrier extended)]
      (is (thrown-with-msg? Exception #"rule-list limit"
            ((imported/make-constant-projector (:world carrier) (:operations carrier)
               {:max-visits 1000000 :max-rule-nodes 1})
             (:world carrier) ((:encode carrier) guest)))))))

(deftest value-only-snapshot-validation-is-safe-inside-uncached-lazy-lookup
  (let [n (name/from-string "Guarded") levels (object-array [Level/ZERO_LEVEL])
        type (Expr/mkConst n levels false)
        ci (ConstantInfo/mkAxiom n (object-array []) type false)
        segment (snapshot/snapshot-segment {n ci}) lookups (atom 0)
        guarded (.withExternalLookupUncached (Env.)
                  (fn [requested]
                    (swap! lookups inc)
                    (snapshot/validate-segment-values segment)
                    (when (= n requested) ci)) 1)]
    (is (identical? segment (snapshot/validate-segment-values segment)))
    (is (zero? @lookups))
    (is (identical? ci (.lookup ^Env guarded n)))
    (is (= 1 @lookups))
    (is (identical? segment (snapshot/validate-segment guarded segment)))
    (is (thrown-with-msg? Exception #"Lazy/external" (snapshot/validate-segments guarded [segment])))
    (set! (.isUnsafe ci) true)
    (is (thrown-with-msg? Exception #"checking shape changed" (.lookup ^Env guarded n)))
    (set! (.isUnsafe ci) false)
    (aset levels 0 (Level/succ Level/ZERO_LEVEL))
    (is (thrown-with-msg? Exception #"universe array changed" (snapshot/validate-segment-values segment)))))

(deftest carrier-import-retains-full-hints-mutual-all-and-every-safety-code
  (doseq [safety [0 1 2] height [0 4294967295]]
    (let [loaded (loaded) initial (:world loaded) guest (get (by-name loaded) "aliasA")
          p (payload initial guest)
          [world hints] (guest/ctor initial 2 [] 4)
          world (-> world (guest/scalar! hints 0 "uint32" height)
                    (guest/scalar! p 0 "uint8" safety)
                    (assoc-in [:heap (:id p) :fields 2] hints))
          carrier (alternate-ci-carrier world)
          ^ConstantInfo ci ((imported/make-constant-projector (:world carrier) (:operations carrier)
                              {:max-visits 1000000 :max-rule-nodes 100})
                            (:world carrier) ((:encode carrier) guest))]
      (is (= height (.getHintsCode ci)))
      (is (= ({0 1, 1 0, 2 2} safety) (.safety ci)))
      (is (= ["aliasA"] (mapv str (.all ci))))
      (is (= (imported/checking-shape (imported/project-constant world guest))
             (imported/checking-shape ci))))))
