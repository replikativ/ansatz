;; Copyright (c) 2026 Simmis GmbH. All rights reserved.
;; Buffer type handlers for CIC types + PSS nodes in konserve-lmdb.

(ns cic.export.lmdb-handlers
  "ITypeHandler implementations for CIC kernel types and PSS nodes.
   Used with konserve-lmdb buffer encoder for fast LMDB storage."
  (:require [konserve-lmdb.buffer :as buf])
  (:import [cic.kernel Name Level Expr ConstantInfo ConstantInfo$RecursorRule]
           [org.replikativ.persistent_sorted_set Leaf Branch Settings]
           [java.nio ByteBuffer]
           [java.util UUID List]))

(set! *warn-on-reflection* true)

;; Wrapper type for CI-shells so LMDB buffer handler dispatch works correctly.
;; Without this, PersistentArrayMap would intercept all small Clojure maps.
(deftype CIShell [^clojure.lang.IPersistentMap data])

;;; Type tags (0x40-0xFF range for custom types)
(def ^:const TAG_NAME    (byte 0x40))
(def ^:const TAG_LEVEL   (byte 0x41))
(def ^:const TAG_EXPR    (byte 0x42))
(def ^:const TAG_CI      (byte 0x43))
(def ^:const TAG_RECRULE (byte 0x44))
(def ^:const TAG_LEAF    (byte 0x45))
(def ^:const TAG_BRANCH  (byte 0x46))

;;; Name handler

(defn create-name-handler []
  (reify buf/ITypeHandler
    (type-tag [_] TAG_NAME)
    (type-class [_] Name)
    (encode-type [_ buf value encode-fn]
      (let [^ByteBuffer b buf
            ^Name n value
            tag (int (.tag n))]
        (.put b (byte tag))
        (case tag
          0 nil ;; anonymous
          1 (do (encode-fn b (.prefix n))
                (encode-fn b (.str n)))
          2 (do (encode-fn b (.prefix n))
                (.putLong b (.num n))))))
    (decode-type [_ buf decode-fn]
      (let [^ByteBuffer b buf
            tag (int (.get b))]
        (case tag
          0 Name/ANONYMOUS_NAME
          1 (Name/mkStr (decode-fn b) (decode-fn b))
          2 (Name/mkNum (decode-fn b) (.getLong b)))))))

;;; Level handler

(defn create-level-handler []
  (reify buf/ITypeHandler
    (type-tag [_] TAG_LEVEL)
    (type-class [_] Level)
    (encode-type [_ buf value encode-fn]
      (let [^ByteBuffer b buf
            ^Level l value
            tag (int (.tag l))]
        (.put b (byte tag))
        (case tag
          0 nil ;; zero
          1 (encode-fn b (.o0 l))
          2 (do (encode-fn b (.o0 l)) (encode-fn b (.o1 l)))
          3 (do (encode-fn b (.o0 l)) (encode-fn b (.o1 l)))
          4 (encode-fn b (.o0 l)))))
    (decode-type [_ buf decode-fn]
      (let [^ByteBuffer b buf
            tag (int (.get b))]
        (case tag
          0 Level/ZERO_LEVEL
          1 (Level/succ (decode-fn b))
          2 (Level/max (decode-fn b) (decode-fn b))
          3 (Level/imax (decode-fn b) (decode-fn b))
          4 (Level/param (decode-fn b)))))))

;;; Expr handler

(defn create-expr-handler []
  (reify buf/ITypeHandler
    (type-tag [_] TAG_EXPR)
    (type-class [_] Expr)
    (encode-type [_ buf value encode-fn]
      (let [^ByteBuffer b buf
            ^Expr e value
            tag (int (.tag e))]
        (.put b (byte tag))
        (case tag
          0  (.putLong b (.longVal e))                              ;; BVAR
          1  (encode-fn b (.o0 e))                                  ;; SORT
          2  (do (encode-fn b (.o0 e)) (encode-fn b (vec (.o1 e))))  ;; CONST
          3  (do (encode-fn b (.o0 e)) (encode-fn b (.o1 e)))       ;; APP
          4  (do (encode-fn b (.o0 e)) (encode-fn b (.o1 e))        ;; LAM
                 (encode-fn b (.o2 e)) (encode-fn b (.o3 e)))
          5  (do (encode-fn b (.o0 e)) (encode-fn b (.o1 e))        ;; FORALL
                 (encode-fn b (.o2 e)) (encode-fn b (.o3 e)))
          6  (do (encode-fn b (.o0 e)) (encode-fn b (.o1 e))        ;; LET
                 (encode-fn b (.o2 e)) (encode-fn b (.o3 e)))
          7  (encode-fn b (.o0 e))                                  ;; LIT_NAT
          8  (encode-fn b (.o0 e))                                  ;; LIT_STR
          9  (do (encode-fn b (.o0 e)) (encode-fn b (.o1 e)))       ;; MDATA
          10 (do (encode-fn b (.o0 e)) (.putLong b (.longVal e))    ;; PROJ
                 (encode-fn b (.o1 e)))
          11 (.putLong b (.longVal e)))))                           ;; FVAR
    (decode-type [_ buf decode-fn]
      (let [^ByteBuffer b buf
            tag (int (.get b))]
        (case tag
          0  (Expr/bvar (.getLong b))
          1  (let [l (decode-fn b)] (Expr/sort l (Level/hasParam l)))
          2  (let [n (decode-fn b)
                   ls (decode-fn b)
                   hp (some #(Level/hasParam %) ls)]
               (Expr/mkConst n ls (boolean hp)))
          3  (Expr/app (decode-fn b) (decode-fn b))
          4  (Expr/lam (decode-fn b) (decode-fn b) (decode-fn b) (decode-fn b))
          5  (Expr/forall (decode-fn b) (decode-fn b) (decode-fn b) (decode-fn b))
          6  (Expr/mkLet (decode-fn b) (decode-fn b) (decode-fn b) (decode-fn b))
          7  (let [v (decode-fn b)]
               (Expr/litNat (if (instance? java.math.BigInteger v) v (biginteger v))))
          8  (Expr/litStr (decode-fn b))
          9  (Expr/mdata (decode-fn b) (decode-fn b))
          10 (let [n (decode-fn b) idx (.getLong b) s (decode-fn b)]
               (Expr/proj n idx s))
          11 (Expr/fvar (.getLong b)))))))

;;; RecursorRule handler

(defn create-recursor-rule-handler []
  (reify buf/ITypeHandler
    (type-tag [_] TAG_RECRULE)
    (type-class [_] ConstantInfo$RecursorRule)
    (encode-type [_ buf value encode-fn]
      (let [^ByteBuffer b buf
            ^ConstantInfo$RecursorRule r value]
        (encode-fn b (.ctor r))
        (.putInt b (.nfields r))
        (encode-fn b (.rhs r))))
    (decode-type [_ buf decode-fn]
      (let [^ByteBuffer b buf
            ctor (decode-fn b)
            nfields (.getInt b)
            rhs (decode-fn b)]
        (ConstantInfo$RecursorRule. ctor nfields rhs)))))

;;; ConstantInfo handler

(defn create-ci-handler []
  (reify buf/ITypeHandler
    (type-tag [_] TAG_CI)
    (type-class [_] ConstantInfo)
    (encode-type [_ buf value encode-fn]
      (let [^ByteBuffer b buf
            ^ConstantInfo ci value
            tag (int (.tag ci))]
        (.put b (byte tag))
        ;; Common fields
        (encode-fn b (.name ci))
        (encode-fn b (vec (.levelParams ci)))
        (encode-fn b (.type ci))
        ;; Variant-specific
        (case tag
          0 (.put b (if (.isUnsafe ci) (byte 1) (byte 0)))           ;; AXIOM
          1 (do (encode-fn b (.value ci))                             ;; DEF
                (.putInt b (.hints ci))
                (.put b (.safety ci))
                (encode-fn b (vec (.all ci))))
          2 (do (encode-fn b (.value ci))                             ;; THM
                (encode-fn b (vec (.all ci))))
          3 (do (encode-fn b (.value ci))                             ;; OPAQUE
                (encode-fn b (vec (.all ci)))
                (.put b (if (.isUnsafe ci) (byte 1) (byte 0))))
          4 (encode-fn b (.quotKind ci))                              ;; QUOT
          5 (do (.putInt b (.numParams ci))                           ;; INDUCT
                (.putInt b (.numIndices ci))
                (encode-fn b (vec (.all ci)))
                (encode-fn b (vec (.ctors ci)))
                (.putInt b (.numNested ci))
                (.put b (if (.isRec ci) (byte 1) (byte 0)))
                (.put b (if (.isReflexive ci) (byte 1) (byte 0)))
                (.put b (if (.isUnsafe ci) (byte 1) (byte 0))))
          6 (do (encode-fn b (.inductName ci))                        ;; CTOR
                (.putInt b (.cidx ci))
                (.putInt b (.numParams ci))
                (.putInt b (.numFields ci))
                (.put b (if (.isUnsafe ci) (byte 1) (byte 0))))
          7 (do (encode-fn b (vec (.all ci)))                         ;; RECURSOR
                (.putInt b (.numParams ci))
                (.putInt b (.numIndices ci))
                (.putInt b (.numMotives ci))
                (.putInt b (.numMinors ci))
                (encode-fn b (vec (.rules ci)))
                (.put b (if (.isK ci) (byte 1) (byte 0)))
                (.put b (if (.isUnsafe ci) (byte 1) (byte 0)))))))
    (decode-type [_ buf decode-fn]
      (let [^ByteBuffer b buf
            tag (int (.get b))
            name (decode-fn b)
            lps (into-array Object (decode-fn b))
            type (decode-fn b)]
        (case tag
          0 (ConstantInfo/mkAxiom name lps type (= 1 (.get b)))
          1 (let [value (decode-fn b)
                  hints (.getInt b)
                  safety (.get b)
                  all (into-array Object (decode-fn b))]
              (ConstantInfo/mkDef name lps type value hints safety all))
          2 (let [value (decode-fn b)
                  all (into-array Object (decode-fn b))]
              (ConstantInfo/mkThm name lps type value all))
          3 (let [value (decode-fn b)
                  all (into-array Object (decode-fn b))
                  unsafe (= 1 (.get b))]
              (ConstantInfo/mkOpaque name lps type value all unsafe))
          4 (ConstantInfo/mkQuot name lps type (decode-fn b))
          5 (let [num-params (.getInt b)
                  num-indices (.getInt b)
                  all (into-array Object (decode-fn b))
                  ctors (into-array Name (decode-fn b))
                  num-nested (.getInt b)
                  is-rec (= 1 (.get b))
                  is-refl (= 1 (.get b))
                  is-unsafe (= 1 (.get b))]
              (ConstantInfo/mkInduct name lps type num-params num-indices
                                     all ctors num-nested is-rec is-refl is-unsafe))
          6 (let [induct-name (decode-fn b)
                  cidx (.getInt b)
                  num-params (.getInt b)
                  num-fields (.getInt b)
                  is-unsafe (= 1 (.get b))]
              (ConstantInfo/mkCtor name lps type induct-name cidx num-params num-fields is-unsafe))
          7 (let [all (into-array Object (decode-fn b))
                  num-params (.getInt b)
                  num-indices (.getInt b)
                  num-motives (.getInt b)
                  num-minors (.getInt b)
                  rules (into-array ConstantInfo$RecursorRule (decode-fn b))
                  is-k (= 1 (.get b))
                  is-unsafe (= 1 (.get b))]
              (ConstantInfo/mkRecursor name lps type all num-params num-indices
                                       num-motives num-minors rules is-k is-unsafe)))))))

;;; PSS Leaf handler

(defn create-leaf-handler [^Settings settings]
  (reify buf/ITypeHandler
    (type-tag [_] TAG_LEAF)
    (type-class [_] Leaf)
    (encode-type [_ buf leaf encode-fn]
      (let [^ByteBuffer b buf
            ^Leaf l leaf
            keys (.keys l)
            n (.size ^List keys)]
        (.putInt b n)
        (dotimes [i n]
          (encode-fn b (.get ^List keys i)))))
    (decode-type [_ buf decode-fn]
      (let [^ByteBuffer b buf
            n (.getInt b)
            keys (java.util.ArrayList. n)]
        (dotimes [_ n]
          (.add keys (decode-fn b)))
        (Leaf. ^List keys settings)))))

;;; PSS Branch handler

(defn create-branch-handler [^Settings settings]
  (reify buf/ITypeHandler
    (type-tag [_] TAG_BRANCH)
    (type-class [_] Branch)
    (encode-type [_ buf branch encode-fn]
      (let [^ByteBuffer b buf
            ^Branch br branch
            level (.level br)
            keys (.keys br)
            addresses (.addresses br)
            n (.size ^List keys)]
        (.putInt b level)
        (.putInt b n)
        (dotimes [i n]
          (encode-fn b (.get ^List keys i)))
        (dotimes [i n]
          (let [^UUID addr (.get ^List addresses i)]
            (if addr
              (do (.putLong b (.getMostSignificantBits addr))
                  (.putLong b (.getLeastSignificantBits addr)))
              (do (.putLong b 0) (.putLong b 0)))))))
    (decode-type [_ buf decode-fn]
      (let [^ByteBuffer b buf
            level (.getInt b)
            n (.getInt b)
            keys (java.util.ArrayList. n)
            addresses (java.util.ArrayList. n)]
        (dotimes [_ n]
          (.add keys (decode-fn b)))
        (dotimes [_ n]
          (let [msb (.getLong b)
                lsb (.getLong b)]
            (.add addresses
                   (if (and (zero? msb) (zero? lsb))
                     nil
                     (UUID. msb lsb)))))
        (Branch. (int level) ^List keys ^List addresses settings)))))

;;; CI-shell handler (compact map with expr IDs instead of Expr objects)

(def ^:const TAG_CI_SHELL (byte 0x47))

(defn create-ci-shell-handler []
  (reify buf/ITypeHandler
    (type-tag [_] TAG_CI_SHELL)
    (type-class [_] CIShell)
    (encode-type [_ buf value encode-fn]
      (let [^ByteBuffer b buf
            m (.data ^CIShell value)
            tag (int (:tag m))]
        (.put b (byte tag))
        ;; Common fields
        (encode-fn b (:name m))
        (encode-fn b (:lps m))
        (.putInt b (int (:type-id m)))
        ;; Variant-specific
        (case tag
          0 (.put b (if (:unsafe? m) (byte 1) (byte 0)))              ;; AXIOM
          1 (do (.putInt b (int (:value-id m)))                        ;; DEF
                (encode-fn b (:hints m))
                (encode-fn b (:safety m))
                (encode-fn b (:all m)))
          2 (do (.putInt b (int (:value-id m)))                        ;; THM
                (encode-fn b (:all m)))
          3 (do (.putInt b (int (:value-id m)))                        ;; OPAQUE
                (encode-fn b (:all m))
                (.put b (if (:unsafe? m) (byte 1) (byte 0))))
          4 (encode-fn b (:quot-kind m))                               ;; QUOT
          5 (do (.putInt b (int (:num-params m)))                      ;; INDUCT
                (.putInt b (int (:num-indices m)))
                (encode-fn b (:all m))
                (encode-fn b (:ctors m))
                (.putInt b (int (:num-nested m)))
                (.put b (if (:is-rec m) (byte 1) (byte 0)))
                (.put b (if (:is-reflexive m) (byte 1) (byte 0)))
                (.put b (if (:is-unsafe m) (byte 1) (byte 0))))
          6 (do (encode-fn b (:induct-name m))                        ;; CTOR
                (.putInt b (int (:cidx m)))
                (.putInt b (int (:num-params m)))
                (.putInt b (int (:num-fields m)))
                (.put b (if (:is-unsafe m) (byte 1) (byte 0))))
          7 (do (encode-fn b (:all m))                                 ;; RECURSOR
                (.putInt b (int (:num-params m)))
                (.putInt b (int (:num-indices m)))
                (.putInt b (int (:num-motives m)))
                (.putInt b (int (:num-minors m)))
                ;; rules: vec of {:ctor Name, :nfields int, :rhs-id int}
                (let [rules (:rules m)]
                  (.putInt b (int (count rules)))
                  (doseq [r rules]
                    (encode-fn b (:ctor r))
                    (.putInt b (int (:nfields r)))
                    (.putInt b (int (:rhs-id r)))))
                (.put b (if (:is-k m) (byte 1) (byte 0)))
                (.put b (if (:is-unsafe m) (byte 1) (byte 0)))))))
    (decode-type [_ buf decode-fn]
      (let [^ByteBuffer b buf
            tag (int (.get b))
            name (decode-fn b)
            lps (decode-fn b)
            type-id (.getInt b)]
        (CIShell.
         (case tag
           0 {:tag 0 :name name :lps lps :type-id type-id
              :unsafe? (= 1 (.get b))}
           1 (let [value-id (.getInt b)
                   hints (decode-fn b)
                   safety (decode-fn b)
                   all (decode-fn b)]
               {:tag 1 :name name :lps lps :type-id type-id
                :value-id value-id :hints hints :safety safety :all all})
           2 (let [value-id (.getInt b)
                   all (decode-fn b)]
               {:tag 2 :name name :lps lps :type-id type-id
                :value-id value-id :all all})
           3 (let [value-id (.getInt b)
                   all (decode-fn b)
                   unsafe (= 1 (.get b))]
               {:tag 3 :name name :lps lps :type-id type-id
                :value-id value-id :all all :unsafe? unsafe})
           4 {:tag 4 :name name :lps lps :type-id type-id
              :quot-kind (decode-fn b)}
           5 (let [num-params (.getInt b)
                   num-indices (.getInt b)
                   all (decode-fn b)
                   ctors (decode-fn b)
                   num-nested (.getInt b)
                   is-rec (= 1 (.get b))
                   is-refl (= 1 (.get b))
                   is-unsafe (= 1 (.get b))]
               {:tag 5 :name name :lps lps :type-id type-id
                :num-params num-params :num-indices num-indices
                :all all :ctors ctors :num-nested num-nested
                :is-rec is-rec :is-reflexive is-refl :is-unsafe is-unsafe})
           6 (let [induct-name (decode-fn b)
                   cidx (.getInt b)
                   num-params (.getInt b)
                   num-fields (.getInt b)
                   is-unsafe (= 1 (.get b))]
               {:tag 6 :name name :lps lps :type-id type-id
                :induct-name induct-name :cidx cidx
                :num-params num-params :num-fields num-fields
                :is-unsafe is-unsafe})
           7 (let [all (decode-fn b)
                   num-params (.getInt b)
                   num-indices (.getInt b)
                   num-motives (.getInt b)
                   num-minors (.getInt b)
                   num-rules (.getInt b)
                   rules (vec (for [_ (range num-rules)]
                                {:ctor (decode-fn b)
                                 :nfields (.getInt b)
                                 :rhs-id (.getInt b)}))
                   is-k (= 1 (.get b))
                   is-unsafe (= 1 (.get b))]
               {:tag 7 :name name :lps lps :type-id type-id
                :all all :num-params num-params :num-indices num-indices
                :num-motives num-motives :num-minors num-minors
                :rules rules :is-k is-k :is-unsafe is-unsafe})))))))

;;; Factory

(defn create-all-handlers
  "Create all CIC + PSS type handlers for use with konserve-lmdb."
  [^Settings settings]
  [(create-name-handler)
   (create-level-handler)
   (create-expr-handler)
   (create-ci-handler)
   (create-recursor-rule-handler)
   (create-leaf-handler settings)
   (create-branch-handler settings)
   (create-ci-shell-handler)])
