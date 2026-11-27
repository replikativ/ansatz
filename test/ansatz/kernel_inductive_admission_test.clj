(ns ansatz.kernel-inductive-admission-test
  "Inductive admission against Lean v4.36.0's `environment::add_inductive` (inductive.cpp).

   Each test names the finding of the K4 kernel audit it pins. The import path
   (`check-inductive-bundle`) must derive every judgment from the declaration — the type and
   constructor sequence — and compare the exported records with what it generates; metadata on
   the records must never decide admission. The Lean outcomes cited here are observed with
   Lean v4.36.0 in test/lean-parity/kernel/*.lean."
  (:require [clojure.test :refer [deftest testing is]]
            [ansatz.test-env :as te]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.reduce :as red])
  (:import [ansatz.kernel ConstantInfo ConstantInfo$RecursorRule Env InductiveBundle Reducer]))

;; ============================================================
;; Helpers
;; ============================================================

(def ^:private fuel 5000000)

(defn- n [s] (name/from-string s))
(defn- c ([s] (e/const' (n s) [])) ([s lvls] (e/const' (n s) lvls)))
(def ^:private l0 lvl/zero)
(def ^:private l1 (lvl/succ lvl/zero))
(def ^:private prop (e/sort' l0))
(def ^:private type0 (e/sort' l1))
(defn- pi [nm dom body] (e/forall' nm dom body :default))
(defn- ipi [nm dom body] (e/forall' nm dom body :implicit))
(defn- lam [nm dom body] (e/lam nm dom body :default))
(defn- bv [i] (e/bvar i))
(defn- P [s] (lvl/param (n s)))

(def ^:private base (delay @te/bundled-init-env))

(defn- rejection
  "The kernel's message if the exported records are rejected, nil if admitted."
  [^Env env records]
  (let [inds (filterv #(.isInduct ^ConstantInfo %) records)
        ^ConstantInfo i0 (first inds)]
    (try (env/check-inductive-bundle
          env (env/mk-inductive-bundle (vec (.levelParams i0)) (.numParams i0) (.isUnsafe i0)
                                       inds
                                       (filterv #(.isCtor ^ConstantInfo %) records)
                                       (filterv #(.isRecursor ^ConstantInfo %) records))
          fuel)
         nil
         (catch Throwable ex (or (.getMessage ex) (str ex))))))

(defn- admits? [env records] (nil? (rejection env records)))

(defn- arity [ex] (loop [ex ex k 0] (if (e/forall? ex) (recur (e/forall-body ex) (inc k)) k)))

(defn- occurs? [ex names]
  (cond (e/const? ex) (contains? names (e/const-name ex))
        (e/app? ex) (or (occurs? (e/app-fn ex) names) (occurs? (e/app-arg ex) names))
        (or (e/forall? ex) (e/lam? ex)) (or (occurs? (.o1 ex) names) (occurs? (.o2 ex) names))
        :else false))

(defn- domains [ex] (loop [ex ex out []] (if (e/forall? ex) (recur (e/forall-body ex) (conj out (e/forall-type ex))) out)))

(defn- generate
  "The records the kernel generates for a declaration (Lean's `inductive_decl`):
   `types` is [[name type [[ctor-name ctor-type] ...]] ...]. Returns [env records], the records
   in Lean's order: inductives, constructors, recursors (auxiliary ones last).
   (Pre-K4 kernel: metadata derived here, recursors from InductiveChecker by reflection.)"
  [^Env env lps np types & {:keys [unsafe? num-nested] :or {num-nested 0}}]
  (let [names (set (map (comp n first) types))
        all (mapv (comp n first) types)
        doms (for [[_ _ cs] types [_ ct] cs d (domains ct)] d)
        rec? (boolean (some #(occurs? % names) doms))
        refl? (boolean (some #(and (e/forall? %) (occurs? % names)) doms))
        inds (vec (for [[nm ty cs] types]
                    (env/mk-induct (n nm) lps ty :num-params np :num-indices (- (arity ty) np) :all all
                                   :ctors (mapv (comp n first) cs) :num-nested num-nested
                                   :rec? rec? :reflexive? refl?)))
        ctors (vec (for [[nm _ cs] types [i [cn ct]] (map-indexed vector cs)]
                     (env/mk-ctor (n cn) lps ct (n nm) i np (- (arity ct) np))))
        recs (if (pos? num-nested)
               (let [env' (env/check-inductive-bundle env (env/mk-inductive-bundle lps np false inds ctors []) fuel)]
                 (vec (keep #(env/lookup env' (n %))
                            (concat (map #(str (first %) ".rec") types)
                                    (map #(str (ffirst types) ".rec_" %) (range 1 10))))))
               (let [bundle0 (env/mk-inductive-bundle lps np false inds ctors [])
                     klass (Class/forName "ansatz.kernel.InductiveChecker")
                     k (doto (.getDeclaredConstructor klass (into-array Class [Env InductiveBundle Long/TYPE]))
                         (.setAccessible true))
                     ic (.newInstance k (object-array [env bundle0 (long fuel)]))
                     m (doto (.getDeclaredMethod klass "generateAndCheckRecursors" (into-array Class []))
                         (.setAccessible true))]
                 (vec (.invoke m ic (object-array [])))))
        records (vec (concat inds ctors recs))]
    [(env/check-inductive-bundle env (env/mk-inductive-bundle lps np false inds ctors recs) fuel) records]))

(defn- by-name [records s] (first (filter #(= (n s) (.name ^ConstantInfo %)) records)))

(defn- replace-record [records s f]
  (mapv #(if (= (n s) (.name ^ConstantInfo %)) (f %) %) records))

(defn- induct-with
  [^ConstantInfo ci & {:keys [all ctors rec? num-params num-nested]}]
  (ConstantInfo/mkInduct (.name ci) (.levelParams ci) (.type ci)
                         (int (or num-params (.numParams ci))) (.numIndices ci)
                         (or all (.all ci)) (or ctors (.ctors ci))
                         (int (or num-nested (.numNested ci)))
                         (boolean (if (some? rec?) rec? (.isRec ci)))
                         (.isReflexive ci) (.isUnsafe ci)))

(defn- ctor-with [^ConstantInfo ci & {:keys [num-params]}]
  (ConstantInfo/mkCtor (.name ci) (.levelParams ci) (.type ci) (.inductName ci) (.cidx ci)
                       (int (or num-params (.numParams ci))) (.numFields ci) (.isUnsafe ci)))

(defn- rec-with [^ConstantInfo ci & {:keys [name lps type rules]}]
  (ConstantInfo/mkRecursor (or name (.name ci)) (or lps (.levelParams ci)) (or type (.type ci))
                           (.all ci) (.numParams ci) (.numIndices ci) (.numMotives ci)
                           (.numMinors ci) (or rules (.rules ci)) (.isK ci) (.isUnsafe ci)))

(defn- rename-levels [ex from to]
  (Reducer/instantiateLevelParams ex (java.util.HashMap. {(n from) (P to)})))

;; ============================================================
;; Finding 2 — one constructor sequence, a bijection with the records
;; ============================================================

(deftest f2-constructor-membership-is-a-bijection
  (let [[_ honest] (generate @base [] 0 [["KE" prop []]])
        intro (env/mk-ctor (n "KE.intro") [] (c "KE") (n "KE") 0 0 0)]
    (testing "control: the empty proposition is admitted"
      (is (admits? @base honest)))
    (testing "a constructor record outside the inductive's constructor list is rejected"
      ;; KE.rec eliminates into every universe with no minor premise; with KE.intro admitted
      ;; too, the environment proves False.
      (is (re-find #"KE.intro" (str (rejection @base (conj honest intro))))))
    (testing "a constructor listed by the inductive but absent from the records is rejected"
      (is (some? (rejection @base (replace-record honest "KE" #(induct-with % :ctors (into-array ansatz.kernel.Name [(n "KE.intro")])))))))
    (testing "duplicate constructor records are rejected"
      (let [[_ unit] (generate @base [] 0 [["KU" type0 [["KU.mk" (c "KU")]]]])]
        (is (some? (rejection @base (conj unit (by-name unit "KU.mk")))))))
    (testing "an ordinary family without its recursor record is rejected"
      (let [[_ unit] (generate @base [] 0 [["KU" type0 [["KU.mk" (c "KU")]]]])]
        (is (re-find #"KU.rec" (str (rejection @base (filterv #(not (.isRecursor ^ConstantInfo %)) unit)))))))))

;; ============================================================
;; Finding 3 — metadata is derived, never taken from the records
;; ============================================================

(deftest f3-mutual-all-cannot-hide-a-negative-occurrence
  ;; mutual A, B with B.mk : (B → Nat) → B; Lean: "arg #1 of 'B.mk' has a non positive
  ;; occurrence of the datatypes being declared" (NestedPositivity.lean). B.all = [A] used to
  ;; drop B from the occurrence test.
  (let [A (n "KA") B (n "KB")
        inds [(env/mk-induct A [] type0 :all [A B] :ctors [(n "KA.mk")] :rec? true)
              (env/mk-induct B [] type0 :all [A] :ctors [(n "KB.mk")] :rec? true)]
        ctors [(env/mk-ctor (n "KA.mk") [] (pi "b" (c "KB") (c "KA")) A 0 0 1)
               (env/mk-ctor (n "KB.mk") [] (pi "f" (pi "x" (c "KB") (c "Nat")) (c "KB")) B 0 0 1)]]
    (is (re-find #"non positive occurrence" (str (rejection @base (into inds ctors)))))))

(deftest f3-record-metadata-is-compared
  (testing "a false isRec (which would enable structure eta on a recursive family) is rejected"
    (let [[_ honest] (generate @base [] 0 [["KR" type0 [["KR.mk" (pi "f" (pi "x" (c "Nat") (c "KR")) (c "KR"))]]]])]
      (is (admits? @base honest))
      (is (re-find #"isRec" (str (rejection @base (replace-record honest "KR" #(induct-with % :rec? false))))))))
  (testing "a wrong constructor numParams (where projections find fields) is rejected"
    (let [W (c "KW")
          [_ honest] (generate @base [] 1 [["KW" (pi "α" type0 type0)
                                            [["KW.mk" (ipi "α" type0 (pi "a" (bv 0) (e/app W (bv 1))))]]]])]
      (is (admits? @base honest))
      (is (re-find #"numParams" (str (rejection @base (replace-record honest "KW.mk" #(ctor-with % :num-params 0)))))))))

;; ============================================================
;; Finding 4 — nested positivity goes through the auxiliary block
;; ============================================================

(deftest f4-contravariant-container-is-not-a-positive-nesting
  ;; Lean: Bad.mk : Contra Bad → Bad is rejected — `_nested.Contra_1.mk` has the field
  ;; `Bad → Nat` (NestedPositivity.lean). numNested = 0 used to skip the auxiliary block.
  (let [[env _] (generate @base [] 1 [["KContra" (pi "α" type0 type0)
                                       [["KContra.mk" (ipi "α" type0 (pi "f" (pi "x" (bv 0) (c "Nat"))
                                                                         (e/app (c "KContra") (bv 1))))]]]])
        bad (n "KBad")
        records [(env/mk-induct bad [] type0 :all [bad] :ctors [(n "KBad.mk")])
                 (env/mk-ctor (n "KBad.mk") [] (pi "c" (e/app (c "KContra") (c "KBad")) (c "KBad")) bad 0 0 1)]]
    (is (re-find #"non positive occurrence" (str (rejection env records))))))

;; ============================================================
;; Findings 5 and 6 — recursor rules are compared structurally, in the record's universes
;; ============================================================

(deftest f5-ill-typed-rule-rhs-is-rejected
  ;; `(fun (x : Nat) => mk) Prop` beta-reduces to the generated `mk`, but is ill-typed.
  (let [[_ honest] (generate @base [] 0 [["KU5" type0 [["KU5.mk" (c "KU5")]]]])
        ^ConstantInfo rec (by-name honest "KU5.rec")
        ^ConstantInfo$RecursorRule rule (first (.rules rec))
        rhs (.rhs rule)                 ; fun motive mk => mk
        bad-rhs (lam (e/lam-name rhs) (e/lam-type rhs)
                     (let [inner (e/lam-body rhs)]
                       (lam (e/lam-name inner) (e/lam-type inner)
                            (e/app (lam "x" (c "Nat") (bv 1)) prop))))
        tampered (replace-record honest "KU5.rec"
                                 #(rec-with % :rules (into-array ConstantInfo$RecursorRule
                                                                 [(env/mk-recursor-rule (.ctor rule) (.nfields rule) bad-rhs)])))]
    (is (admits? @base honest))
    (is (re-find #"rule" (str (rejection @base tampered))))))

(deftest f6-recursor-universe-renaming-applies-to-rules
  (let [[_ honest] (generate @base [] 0 [["KU6" type0 [["KU6.mk" (c "KU6")]]]])
        ^ConstantInfo rec (by-name honest "KU6.rec")
        u (str (first (.levelParams rec)))
        renamed-type (rename-levels (.type rec) u "v")
        lps (into-array Object [(n "v")])]
    (testing "type renamed but rules still in the generator's universe: rejected"
      (is (some? (rejection @base (replace-record honest "KU6.rec" #(rec-with % :lps lps :type renamed-type))))))
    (testing "type and rules renamed consistently: admitted"
      (let [rules (into-array ConstantInfo$RecursorRule
                              (for [^ConstantInfo$RecursorRule r (.rules rec)]
                                (env/mk-recursor-rule (.ctor r) (.nfields r) (rename-levels (.rhs r) u "v"))))]
        (is (admits? @base (replace-record honest "KU6.rec" #(rec-with % :lps lps :type renamed-type :rules rules))))))))

;; ============================================================
;; Finding 7 — uniform occurrences are checked on the syntax
;; ============================================================

(deftest f7-nonuniform-occurrence-under-a-beta-redex-is-rejected
  ;; Lean: "invalid occurrence of datatype 'T' being declared: it must be applied to the
  ;; parameters and universe levels of the mutual declaration" (Admission.lean).
  (let [T (n "KT7")
        redex (e/app (lam "x" type0 (c "Unit")) (e/app (c "KT7") (c "Nat")))
        records [(env/mk-induct T [] (pi "α" type0 type0) :num-params 1 :all [T] :ctors [(n "KT7.mk")])
                 (env/mk-ctor (n "KT7.mk") [] (ipi "α" type0 (pi "a" redex (e/app (c "KT7") (bv 1)))) T 0 1 1)]]
    (is (re-find #"invalid occurrence of datatype 'KT7'" (str (rejection @base records))))))

;; ============================================================
;; Finding 10 — closedness and the reserved `_nested` prefix
;; ============================================================

(deftest f10-closedness-and-reserved-prefix
  (testing "a universe metavariable in the header (Lean: declaration has metavariables)"
    (let [I (n "KI10")]
      (is (re-find #"metavariables"
                   (str (rejection @base [(env/mk-induct I [] (e/sort' (lvl/mvar 7)) :all [I] :ctors [])]))))))
  (testing "a free variable in a constructor (Lean: declaration has free variables)"
    (let [I (n "KI10b")]
      (is (re-find #"free variables"
                   (str (rejection @base [(env/mk-induct I [] type0 :all [I] :ctors [(n "KI10b.mk")])
                                          (env/mk-ctor (n "KI10b.mk") [] (pi "a" (e/fvar 1) (c "KI10b")) I 0 0 1)]))))))
  (testing "a reference to `_nested.*` (Lean: it uses the reserved prefix '_nested')"
    (let [env (env/check-constant @base (env/mk-axiom (n "_nested.KX_1") [] type0) fuel)
          I (n "KI10c")]
      (is (re-find #"reserved prefix '_nested'"
                   (str (rejection env [(env/mk-induct I [] type0 :all [I] :ctors [(n "KI10c.mk")])
                                        (env/mk-ctor (n "KI10c.mk") [] (pi "a" (c "_nested.KX_1") (c "KI10c")) I 0 0 1)])))))))

;; ============================================================
;; Finding 11 — field universes use `is_geq`, mutual headers `is_equivalent`
;; ============================================================

(def ^:private s11 (lvl/imax (P "a") (P "b")))
(defn- hdr11 [l] (pi "P" (e/sort' (P "a")) (pi "Q" (e/sort' (P "b")) (e/sort' l))))
(defn- ctor11 [I field]
  (ipi "P" (e/sort' (P "a")) (ipi "Q" (e/sort' (P "b")) (pi "f" field (e/app* I (bv 2) (bv 1))))))
(def ^:private PQ (pi "x" (bv 1) (bv 1)))

(deftest f11-field-universe-uses-lean-is-geq
  (testing "s = imax a b; a field of Sort s does not fit Sort (imax c s) (Lean rejects)"
    (let [I (n "KI4")
          lps [(n "a") (n "b") (n "c")]]
      (is (re-find #"too big"
                   (str (rejection @base [(env/mk-induct I lps (hdr11 (lvl/imax (P "c") s11)) :num-params 2 :all [I] :ctors [(n "KI4.mk")])
                                          (env/mk-ctor (n "KI4.mk") lps (ctor11 (c "KI4" [(P "a") (P "b") (P "c")]) PQ) I 0 2 1)]))))))
  (testing "a field of Sort (imax s b) fits Sort s (Lean accepts)"
    (let [[_ honest] (generate @base [(n "a") (n "b")] 2
                               [["KI5" (hdr11 s11)
                                 [["KI5.mk" (ctor11 (c "KI5" [(P "a") (P "b")]) (pi "g" PQ (bv 1)))]]]])]
      (is (admits? @base honest))))
  (testing "mutual headers Sort s and Sort (max s b) are not equivalent (Lean rejects)"
    (let [M1 (n "KM1") M2 (n "KM2") lps [(n "a") (n "b")]]
      (is (re-find #"same universe"
                   (str (rejection @base [(env/mk-induct M1 lps (hdr11 s11) :num-params 2 :all [M1 M2] :ctors [])
                                          (env/mk-induct M2 lps (hdr11 (lvl/level-max s11 (P "b"))) :num-params 2 :all [M1 M2] :ctors [])])))))))

;; ============================================================
;; Nested occurrences: identity up to binder names; canonical auxiliary recursor names
;; ============================================================

(deftest nested-occurrences-are-identified-up-to-binder-names
  ;; Lean: numNested = 1, T.rec has two motives (NestedAndRecursor.lean).
  (let [[env _] (generate @base [] 1 [["KC" (pi "f" (pi "x" (c "Nat") (c "Nat")) (pi "α" type0 type0))
                                       [["KC.mk" (ipi "f" (pi "x" (c "Nat") (c "Nat"))
                                                      (ipi "α" type0 (pi "a" (bv 0) (e/app* (c "KC") (bv 2) (bv 1)))))]]]])
        idx (lam "x" (c "Nat") (bv 0))
        idy (lam "y" (c "Nat") (bv 0))
        [env' _] (generate env [] 0 [["KTn" type0
                                      [["KTn.node" (pi "a" (e/app* (c "KC") idx (c "KTn"))
                                                       (pi "b" (e/app* (c "KC") idy (c "KTn")) (c "KTn")))]]]]
                           :num-nested 1)]
    (is (= 1 (.numNested ^ConstantInfo (env/lookup env' (n "KTn")))))
    (is (= 2 (.numMotives ^ConstantInfo (env/lookup env' (n "KTn.rec")))))))

(deftest nested-auxiliary-recursor-must-carry-its-canonical-name
  (let [[_ honest] (generate @base [] 0 [["KTree" type0
                                          [["KTree.node" (pi "c" (e/app (c "List" [l0]) (c "KTree")) (c "KTree"))]]]]
                             :num-nested 1)]
    (is (some? (by-name honest "KTree.rec_1")))
    (is (admits? @base honest))
    (testing "the auxiliary recursor under a temporary name is rejected"
      (is (some? (rejection @base (replace-record honest "KTree.rec_1" #(rec-with % :name (n "List.nested_1.rec")))))))
    (testing "a missing auxiliary recursor is rejected"
      (is (some? (rejection @base (filterv #(not= (n "KTree.rec_1") (.name ^ConstantInfo %)) honest)))))))

;; ============================================================
;; Adjacent: the Clojure reducer's Quot.ind major premise
;; ============================================================

(deftest quot-ind-major-is-argument-four
  ;; Quot.ind {α} {r} {β} (mk : ∀ a, β (Quot.mk r a)) (q : Quot r) : β q — the major is
  ;; argument 4 of 5, as in Lean's quot_reduce_rec (mk_pos = 4) and the Java reducer.
  (let [env @base
        u [l1]
        alpha (c "Nat")
        r (lam "a" alpha (lam "b" alpha prop))
        beta (lam "q" (e/app* (c "Quot" u) alpha r) prop)
        mk (e/fvar 4242)
        a (e/lit-nat 3)
        q (e/app* (c "Quot.mk" u) alpha r a)
        term (e/app* (c "Quot.ind" u) alpha r beta mk q)]
    (is (= (e/app mk a) (red/whnf-no-delta env term)))))
