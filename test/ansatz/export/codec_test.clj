(ns ansatz.export.codec-test
  "The CBOR (boring) store codec — the only codec of store format 1: every kernel value
   round-trips, a PSS index persists and restores through it, and node addresses are content
   hashes (the same library imported twice has the same roots)."
  (:require [clojure.test :refer [deftest is testing]]
            [boring.core :as boring]
            [org.replikativ.persistent-sorted-set :as pss]
            [ansatz.export.codec :as codec]
            [ansatz.export.storage :as storage]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as nm]
            [ansatz.kernel.level :as lvl])
  (:import [ansatz.kernel Name Level Expr ConstantInfo ConstantInfo$RecursorRule]
           [ansatz.export.types CIShell]))

(def ^:private reg (codec/registry (fn [_] nil)))

(defn- rt [v] (boring/decode (boring/encode v {:registry reg}) {:registry reg}))

(defn- tmp-dir [tag]
  (let [f (java.io.File/createTempFile (str "ansatz-codec-" tag) "")]
    (.delete f) (.mkdirs f) (.deleteOnExit f) (.getPath f)))

;; ---- values covering every constructor tag ----

(def ^:private a-name (nm/from-string "Nat.add_comm"))
(def ^:private num-name (Name/mkNum a-name 7))
(def ^:private lvls [lvl/zero (lvl/succ lvl/zero) (lvl/level-max lvl/zero (lvl/succ lvl/zero))
                     (lvl/imax lvl/zero (lvl/succ lvl/zero)) (lvl/param "u")])
(def ^:private nat (e/const' (nm/from-string "Nat") []))

(deftest names-and-levels-round-trip
  (testing "every Name tag, including the nested prefix chain and a numeric segment"
    (is (= Name/ANONYMOUS_NAME (rt Name/ANONYMOUS_NAME)))
    (is (= a-name (rt a-name)))
    (is (= "Nat.add_comm" (nm/->string (rt a-name))) "the segments survive, not just equality")
    (is (= num-name (rt num-name))))
  (testing "every Level tag"
    (doseq [l lvls] (is (= l (rt l)) (str "level " l)))))

(deftest exprs-round-trip
  (testing "every Expr tag, nested"
    (let [u (lvl/param "u")
          body (e/app* (e/const' (nm/from-string "HAdd.hAdd") [lvl/zero]) nat (e/bvar 0) (e/lit-nat 1))
          exprs [(e/bvar 3)
                 (e/sort' u)
                 (e/const' (nm/from-string "Eq") [u lvl/zero])
                 (e/app nat (e/lit-nat 2))
                 (e/lam "x" nat body :default)
                 (e/forall' "x" nat body :implicit)
                 (e/let' "x" nat (e/lit-nat 0) body)
                 (e/lit-nat 12345678901234)
                 (e/lit-str "hello ∀ λ")
                 (e/mdata {:pp true} body)
                 (e/proj (nm/from-string "Prod") 1 body)
                 (e/fvar 42)]]
      (doseq [x exprs]
        (is (= x (rt x)) (str "expr tag " (.tag ^Expr x)))))))

(deftest constant-infos-round-trip
  (testing "an axiom, a definition, a theorem and a recursor with its rules"
    (let [lps (into-array Object ["u"])
          ty (e/forall' "n" nat nat :default)
          v (e/lam "n" nat (e/bvar 0) :default)
          cis [(ConstantInfo/mkAxiom a-name lps ty false)
               (ConstantInfo/mkDef a-name lps ty v 0 (byte 0) (into-array Object [a-name]))
               (ConstantInfo/mkThm a-name lps ty v (into-array Object [a-name]))
               (ConstantInfo/mkQuot a-name lps ty (nm/from-string "Quot.mk"))
               (ConstantInfo/mkCtor a-name lps ty (nm/from-string "Nat") 0 1 2 false)
               (ConstantInfo/mkRecursor a-name lps ty (into-array Object [a-name])
                                        1 0 1 2
                                        (into-array ConstantInfo$RecursorRule
                                                    [(ConstantInfo$RecursorRule.
                                                      (nm/from-string "Nat.succ") 1 v)])
                                        false false)]]
      (doseq [^ConstantInfo ci cis]
        (let [ci' ^ConstantInfo (rt ci)]
          (is (= (.tag ci) (.tag ci')) "tag")
          (is (= (.name ci) (.name ci')) "name")
          (is (= (.type ci) (.type ci')) "type")
          (is (= (seq (.levelParams ci)) (seq (.levelParams ci'))) "level params")))
      (testing "a recursor's rules survive with their fields"
        (let [^ConstantInfo r (rt (last cis))
              ^ConstantInfo$RecursorRule rule (first (.rules r))]
          (is (= 1 (count (.rules r))))
          (is (= (nm/from-string "Nat.succ") (.ctor rule)))
          (is (= 1 (.nfields rule)))
          (is (= v (.rhs rule))))))))

(deftest ci-shells-round-trip
  (testing "the id-carrying shell an env branch stores (theorem and inductive shapes)"
    (let [thm (CIShell. {:tag 2 :name a-name :lps ["u"] :type-id 11 :value-id 12 :all [a-name]})
          ind (CIShell. {:tag 5 :name a-name :lps [] :type-id 3
                         :num-params 1 :num-indices 0 :all [a-name] :ctors [a-name]
                         :num-nested 0 :is-rec true :is-reflexive false :is-unsafe false})]
      (is (= (.data thm) (.data ^CIShell (rt thm))))
      (is (= (.data ind) (.data ^CIShell (rt ind)))))))

;; ---- through the actual store ----

(defn- write-store! [dir entries]
  (let [sm (storage/open-store dir)
        st (:storage sm)
        pss (reduce conj (pss/sorted-set* {:cmp storage/id-cmp :storage st
                                           :branching-factor 8 :ref-type :weak})
                    entries)
        root (pss/store pss)]
    (storage/flush-writes! st)
    (storage/close-store sm)
    root))

(defn- read-store [dir root ids]
  (let [sm (storage/open-store dir)
        p (pss/restore-by storage/id-cmp root (:storage sm))]
    (mapv (fn [i] (nth (pss/lookup p [(long i) nil]) 1)) ids)))

(def ^:private entries
  (vec (for [i (range 200)] [(long i) (nm/from-string (str "Some.Long.Namespace.decl_" i))])))

(deftest pss-index-persists-through-the-cbor-codec
  (testing "a PSS whose leaves hold kernel Names stores and restores"
    (let [dir (tmp-dir "boring")
          root (write-store! dir entries)]
      (is (= [(nm/from-string "Some.Long.Namespace.decl_0")
              (nm/from-string "Some.Long.Namespace.decl_137")]
             (read-store dir root [0 137])))
      (is (.isDirectory (storage/blobs-dir dir)) "blobs live under <store>/blobs"))))

(deftest node-addresses-are-content-hashes
  (testing "the same entries imported twice yield the same root — addresses are a function
            of content, not of the run"
    (let [root-a (write-store! (tmp-dir "ca-a") entries)
          root-b (write-store! (tmp-dir "ca-b") entries)]
      (is (= root-a root-b))))
  (testing "and a different library yields a different root"
    (is (not= (write-store! (tmp-dir "ca-c") entries)
              (write-store! (tmp-dir "ca-d") (conj entries [(long 200) (nm/from-string "Extra")]))))))
