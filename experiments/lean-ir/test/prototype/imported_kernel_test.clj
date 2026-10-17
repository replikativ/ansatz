(ns prototype.imported-kernel-test
  (:require [clojure.test :refer [deftest is]] [prototype.imported-kernel :as imported]
            [prototype.module-data :as data] [prototype.machine :as m]
            [prototype.kernel-bridge-test :as guest] [prototype.scalar :as scalar]
            [ansatz.kernel.name :as name])
  (:import [ansatz.kernel Env ConstantInfo]))

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
