(ns prototype.recursor-metadata-contract-test
  (:require [clojure.test :refer [deftest is testing]]
            [prototype.module-data :as data] [prototype.imported-kernel :as imported]
            [prototype.machine :as machine] [ansatz.kernel.env :as env])
  (:import [ansatz.kernel ConstantInfo Env Name TypeChecker]))

(def native-constants
  (delay
    (let [loaded (data/load-file (machine/world {}) "fixtures/raw-inductive-native.jsonl")]
      (into {} (map (fn [{:keys [^ConstantInfo constant]}] [(str (.name constant)) constant]))
        (imported/module-constants (:world loaded) (first (:roots loaded)))))))

(defn- bundle [labels]
  (let [inds (mapv @native-constants labels) ^ConstantInfo first-ind (first inds)]
    (env/mk-inductive-bundle (vec (.levelParams first-ind)) (.numParams first-ind)
      (.isUnsafe first-ind) inds
      (mapv #(get @native-constants (str %)) (mapcat #(seq (.ctors ^ConstantInfo %)) inds))
      (mapv #(get @native-constants (str % ".rec")) labels))))

(defn- rec-with [^ConstantInfo rec changes]
  (let [values (merge {:all (.all rec) :params (.numParams rec) :indices (.numIndices rec)
                      :motives (.numMotives rec) :minors (.numMinors rec)
                      :k? (.isK rec) :unsafe? (.isUnsafe rec)} changes)]
    (ConstantInfo/mkRecursor (.name rec) (.levelParams rec) (.type rec) (:all values)
      (:params values) (:indices values) (:motives values) (:minors values)
      (.rules rec) (:k? values) (:unsafe? values))))

(deftest pinned-native-k-nonk-indexed-and-mutual-recursor-metadata-admits
  ;; Native artifact types/rules/flags are used unchanged. MyNat supplies the
  ;; dependency for indexed AtZero and the mutual Even/Odd family.
  (reduce (fn [checked labels]
            (let [b (bundle labels) next-env (TypeChecker/checkInductiveBundle checked b 1000000)]
              (doseq [^ConstantInfo rec (.recursors b)]
                (is (identical? rec (.lookup next-env (.name rec))))
                (is (nil? (.lookup checked (.name rec)))))
              next-env))
    (Env.) [["TinyEnum"] ["EmptyType"] ["EmptyProp"] ["UnitProp"]
            ["MyNat"] ["AtZero"] ["Even" "Odd"]])
  (is (.isK ^ConstantInfo (get @native-constants "UnitProp.rec")))
  (is (not (.isK ^ConstantInfo (get @native-constants "TinyEnum.rec")))))

(deftest each-computational-field-is-checked-before-admission
  (doseq [label ["TinyEnum" "UnitProp"]]
    (let [b (bundle [label]) ^ConstantInfo rec (first (.recursors b))]
      (doseq [[field changes] [[:all {:all (object-array [(Name/fromString "Wrong")])}]
                              [:params {:params (inc (.numParams rec))}]
                              [:indices {:indices (inc (.numIndices rec))}]
                              [:motives {:motives (inc (.numMotives rec))}]
                              [:minors {:minors (inc (.numMinors rec))}]
                              [:k? {:k? (not (.isK rec))}]
                              [:unsafe? {:unsafe? (not (.isUnsafe rec))}]]]
        (testing (str label " " field)
          (let [before (Env.) bad (rec-with rec changes)
                bad-bundle (env/mk-inductive-bundle (vec (.levelParams b)) (.numParams b)
                             (.isUnsafe b) (.inductives b) (.ctors b) [bad])]
            ;; Type and every computation RHS remain the actual native values.
            (is (identical? (.type rec) (.type bad)))
            (is (identical? (.rules rec) (.rules bad)))
            (is (thrown-with-msg? RuntimeException #"computational metadata mismatch"
                  (TypeChecker/checkInductiveBundle before bad-bundle 1000000)))
            (is (empty? (.allConstants before)))))))))

(deftest unsafe-family-flags-must-agree-with-the-bundle
  ;; This is a marker projection of the native non-K TinyEnum family, not a
  ;; second native oracle. Pinned inductive.cpp propagates m_is_unsafe to all CIs.
  (let [b (bundle ["TinyEnum"]) ^ConstantInfo ind (first (.inductives b))
        unsafe-ind (ConstantInfo/mkInduct (.name ind) (.levelParams ind) (.type ind)
                     (.numParams ind) (.numIndices ind) (.all ind) (.ctors ind)
                     (.numNested ind) (.isRec ind) (.isReflexive ind) true)
        unsafe-ctors (mapv (fn [^ConstantInfo c]
                           (ConstantInfo/mkCtor (.name c) (.levelParams c) (.type c)
                             (.inductName c) (.cidx c) (.numParams c) (.numFields c) true)) (.ctors b))
        ^ConstantInfo rec (first (.recursors b)) unsafe-rec (rec-with rec {:unsafe? true})
        unsafe-bundle (env/mk-inductive-bundle [] 0 true [unsafe-ind] unsafe-ctors [unsafe-rec])
        checked (TypeChecker/checkInductiveBundle (Env.) unsafe-bundle 1000000)]
    (is (identical? unsafe-rec (.lookup checked (.name unsafe-rec))))
    (is (thrown-with-msg? RuntimeException #"computational metadata mismatch"
          (TypeChecker/checkInductiveBundle (Env.)
            (env/mk-inductive-bundle [] 0 true [unsafe-ind] unsafe-ctors [rec]) 1000000)))))

(deftest mutual-recursor-all-order-is-computational-metadata
  (let [nat-env (TypeChecker/checkInductiveBundle (Env.) (bundle ["MyNat"]) 1000000)
        b (bundle ["Even" "Odd"]) ^ConstantInfo rec (first (.recursors b))
        bad (rec-with rec {:all (object-array (reverse (seq (.all rec))))})
        bad-bundle (env/mk-inductive-bundle [] 0 false (.inductives b) (.ctors b)
                     (cons bad (rest (.recursors b))))]
    (is (thrown-with-msg? RuntimeException #"computational metadata mismatch"
          (TypeChecker/checkInductiveBundle nat-env bad-bundle 1000000)))
    (is (nil? (.lookup nat-env (.name rec))))))

(deftest original-constructor-descriptor-derives-k-instead-of-defaulting-false
  ;; Reflect the OLD binary descriptor, as used by an already loaded source
  ;; generator. This exercises the compatibility constructor in a fresh JVM;
  ;; it does not load or redefine classes in the resident frontend process.
  (let [generator (Class/forName "ansatz.kernel.RecursorGenerator")
        ctor (.getDeclaredConstructor generator
               (into-array Class [Env ansatz.kernel.InductiveBundle Long/TYPE
                 (class (object-array 0)) Boolean/TYPE java.util.ArrayList
                 (class (int-array 0)) (class (make-array ansatz.kernel.Expr 0))
                 ansatz.kernel.Level Long/TYPE]))
        flag (.getDeclaredField generator "kTarget")]
    (.setAccessible ctor true)
    (.setAccessible flag true)
    (doseq [[labels expected] [[["UnitProp"] true] [["TinyEnum"] false]
                              [["EmptyProp"] false] [["SmallEq"] true]
                              [["Even" "Odd"] false]]]
      (let [b (bundle labels)
            checked (reduce (fn [^Env e ci] (.addConstant e ci)) (Env.)
                      (concat (.inductives b) (.ctors b)))
            instance (.newInstance ctor
                       (object-array [checked b (long 1000000) (object-array 0) false
                         (java.util.ArrayList.) (int-array (count labels))
                         (make-array ansatz.kernel.Expr (count labels))
                         ansatz.kernel.Level/ZERO_LEVEL (long 1)]))]
        (is (= expected (.getBoolean flag instance)) (str labels))))))
