(ns ansatz.export.codec
  "The kernel's durable value codec in CBOR (boring), alongside the Fressian one in
   ansatz.export.storage.

   WHY. A cold `env/lookup` on Mathlib spends its time decoding names-PSS leaves: 384
   `[id Name]` entries, 35 KB of Fressian per leaf, ~1.45 ms to decode one — Fressian reads a
   string char-by-char (`readUTF8Chars` → `StringBuffer.append`). Measured on the same leaf
   re-encoded: flat Fressian 1.41 ms (the nesting is not the problem — the format is), packed
   UTF-8 + `new String` 0.99 ms, **boring/CBOR 0.33 ms at 14 KB against 34 KB**. Through a
   konserve-lmdb store the whole leaf fetch is 0.28 ms against 2.9 ms on the filestore, i.e.
   ~10x per cold miss.

   WHAT. One boring tag-registry carrying (a) the kernel element types — Name, Level, Expr,
   ConstantInfo, RecursorRule, CIShell — with exactly the part-vectors the Fressian handlers
   write, and (b) the canonical PSS node/root handlers from
   `org.replikativ.persistent-sorted-set.cbor`, so a PSS index serialises through this codec
   the same way it does through Fressian. Elements nest: a part-vector holding a Name recurses
   through the registry, as under Fressian.

   MIGRATION. konserve records the serializer id in every blob header, so a store opened with
   BOTH serializers reads its existing Fressian blobs and writes new ones as CBOR — no
   migration step is required for correctness, only for the speed (see scripts/, and
   `ansatz.export.storage/open-store`'s `:codec` option).

   TAG NUMBERS are from CBOR's First-Come-First-Served range (>= 32768) and are durable wire
   state: an id's meaning must never change, and a new type takes the next free number."
  (:require [boring.core :as boring]
            [ansatz.export.types]
            [org.replikativ.persistent-sorted-set.cbor :as pss-cbor])
  (:import [ansatz.kernel Name Level Expr ConstantInfo ConstantInfo$RecursorRule]
           [ansatz.export.types CIShell]))

(def ^:const name-tag 41000)
(def ^:const level-tag 41001)
(def ^:const expr-tag 41002)
(def ^:const ci-tag 41003)
(def ^:const recursor-rule-tag 41004)
(def ^:const ci-shell-tag 41005)

;; ---- Name / Level ----

(defn- name->parts [^Name n]
  (case (int (.tag n))
    0 [0]
    1 [1 (.prefix n) (.str n)]
    2 [2 (.prefix n) (.num n)]))

(defn- parts->name [parts]
  (case (int (nth parts 0))
    0 Name/ANONYMOUS_NAME
    1 (Name/mkStr (nth parts 1) (nth parts 2))
    2 (Name/mkNum (nth parts 1) (long (nth parts 2)))))

(defn- level->parts [^Level l]
  (case (int (.tag l))
    0 [0]
    1 [1 (.o0 l)]
    2 [2 (.o0 l) (.o1 l)]
    3 [3 (.o0 l) (.o1 l)]
    4 [4 (.o0 l)]))

(defn- parts->level [parts]
  (case (int (nth parts 0))
    0 Level/ZERO_LEVEL
    1 (Level/succ (nth parts 1))
    2 (Level/max (nth parts 1) (nth parts 2))
    3 (Level/imax (nth parts 1) (nth parts 2))
    4 (Level/param (nth parts 1))))

;; ---- Expr ----

(defn- expr->parts [^Expr e]
  (case (int (.tag e))
    0  [0 (.longVal e)]                                ;; BVAR
    1  [1 (.o0 e)]                                     ;; SORT
    2  [2 (.o0 e) (.o1 e)]                             ;; CONST
    3  [3 (.o0 e) (.o1 e)]                             ;; APP
    4  [4 (.o0 e) (.o1 e) (.o2 e) (.o3 e)]             ;; LAM
    5  [5 (.o0 e) (.o1 e) (.o2 e) (.o3 e)]             ;; FORALL
    6  [6 (.o0 e) (.o1 e) (.o2 e) (.o3 e)]             ;; LET
    7  [7 (.o0 e)]                                     ;; LIT_NAT
    8  [8 (.o0 e)]                                     ;; LIT_STR
    9  [9 (.o0 e) (.o1 e)]                             ;; MDATA
    10 [10 (.o0 e) (.longVal e) (.o1 e)]               ;; PROJ
    11 [11 (.longVal e)]))                             ;; FVAR

(defn- parts->expr [parts]
  (case (int (nth parts 0))
    0  (Expr/bvar (long (nth parts 1)))
    1  (let [l (nth parts 1)] (Expr/sort l (Level/hasParam l)))
    2  (let [n (nth parts 1)
             ls (nth parts 2)]
         (Expr/mkConst n ls (boolean (some #(Level/hasParam %) ls))))
    3  (Expr/app (nth parts 1) (nth parts 2))
    4  (Expr/lam (nth parts 1) (nth parts 2) (nth parts 3) (nth parts 4))
    5  (Expr/forall (nth parts 1) (nth parts 2) (nth parts 3) (nth parts 4))
    6  (Expr/mkLet (nth parts 1) (nth parts 2) (nth parts 3) (nth parts 4))
    7  (Expr/litNat (nth parts 1))
    8  (Expr/litStr (nth parts 1))
    9  (Expr/mdata (nth parts 1) (nth parts 2))
    10 (Expr/proj (nth parts 1) (long (nth parts 2)) (nth parts 3))
    11 (Expr/fvar (long (nth parts 1)))))

;; ---- ConstantInfo + its recursor rules ----

(defn- rule->parts [^ConstantInfo$RecursorRule r]
  [(.ctor r) (int (.nfields r)) (.rhs r)])

(defn- parts->rule [parts]
  (ConstantInfo$RecursorRule. (nth parts 0) (int (nth parts 1)) (nth parts 2)))

(defn- ci->parts [^ConstantInfo ci]
  (let [tag (int (.tag ci))
        base [tag (.name ci) (vec (.levelParams ci)) (.type ci)]]
    (case tag
      0 (conj base (.isUnsafe ci))                                             ;; AXIOM
      1 (conj base (.value ci) (int (.hints ci)) (int (.safety ci)) (vec (.all ci))) ;; DEF
      2 (conj base (.value ci) (vec (.all ci)))                                ;; THM
      3 (conj base (.value ci) (vec (.all ci)) (.isUnsafe ci))                 ;; OPAQUE
      4 (conj base (.quotKind ci))                                             ;; QUOT
      5 (conj base (int (.numParams ci)) (int (.numIndices ci)) (vec (.all ci)) ;; INDUCT
              (vec (.ctors ci)) (int (.numNested ci))
              (.isRec ci) (.isReflexive ci) (.isUnsafe ci))
      6 (conj base (.inductName ci) (int (.cidx ci))                           ;; CTOR
              (int (.numParams ci)) (int (.numFields ci)) (.isUnsafe ci))
      7 (conj base (vec (.all ci)) (int (.numParams ci)) (int (.numIndices ci)) ;; RECURSOR
              (int (.numMotives ci)) (int (.numMinors ci)) (vec (.rules ci))
              (.isK ci) (.isUnsafe ci)))))

(defn- parts->ci [parts]
  (let [tag (int (nth parts 0))
        nm (nth parts 1)
        lps (into-array Object (nth parts 2))
        ty (nth parts 3)]
    (case tag
      0 (ConstantInfo/mkAxiom nm lps ty (boolean (nth parts 4)))
      1 (ConstantInfo/mkDef nm lps ty (nth parts 4)
                            (int (nth parts 5)) (byte (int (nth parts 6)))
                            (into-array Object (nth parts 7)))
      2 (ConstantInfo/mkThm nm lps ty (nth parts 4) (into-array Object (nth parts 5)))
      3 (ConstantInfo/mkOpaque nm lps ty (nth parts 4)
                               (into-array Object (nth parts 5)) (boolean (nth parts 6)))
      4 (ConstantInfo/mkQuot nm lps ty (nth parts 4))
      5 (ConstantInfo/mkInduct nm lps ty
                               (int (nth parts 4)) (int (nth parts 5))
                               (into-array Object (nth parts 6))
                               (into-array Name (nth parts 7))
                               (int (nth parts 8))
                               (boolean (nth parts 9)) (boolean (nth parts 10))
                               (boolean (nth parts 11)))
      6 (ConstantInfo/mkCtor nm lps ty (nth parts 4) (int (nth parts 5))
                             (int (nth parts 6)) (int (nth parts 7)) (boolean (nth parts 8)))
      7 (ConstantInfo/mkRecursor nm lps ty
                                 (into-array Object (nth parts 4))
                                 (int (nth parts 5)) (int (nth parts 6))
                                 (int (nth parts 7)) (int (nth parts 8))
                                 (into-array ConstantInfo$RecursorRule (nth parts 9))
                                 (boolean (nth parts 10)) (boolean (nth parts 11))))))

;; ---- CIShell (the id-carrying shell an env branch stores) ----

(defn- shell->parts [^CIShell shell]
  (let [m (.data shell)
        tag (int (:tag m))
        base [tag (:name m) (:lps m) (:type-id m)]]
    (case tag
      0 (conj base (:unsafe? m))
      1 (conj base (:value-id m) (:hints m) (:safety m) (:all m))
      2 (conj base (:value-id m) (:all m))
      3 (conj base (:value-id m) (:all m) (:unsafe? m))
      4 (conj base (:quot-kind m))
      5 (conj base (:num-params m) (:num-indices m) (:all m) (:ctors m)
              (:num-nested m) (:is-rec m) (:is-reflexive m) (:is-unsafe m))
      6 (conj base (:induct-name m) (:cidx m) (:num-params m) (:num-fields m) (:is-unsafe m))
      7 (conj base (:all m) (:num-params m) (:num-indices m) (:num-motives m)
              (:num-minors m) (:rules m) (:is-k m) (:is-unsafe m)))))

(defn- parts->shell [parts]
  (let [tag (int (nth parts 0))
        nm (nth parts 1)
        lps (nth parts 2)
        type-id (int (nth parts 3))]
    (CIShell.
     (case tag
       0 {:tag 0 :name nm :lps lps :type-id type-id :unsafe? (boolean (nth parts 4))}
       1 {:tag 1 :name nm :lps lps :type-id type-id :value-id (int (nth parts 4))
          :hints (nth parts 5) :safety (nth parts 6) :all (nth parts 7)}
       2 {:tag 2 :name nm :lps lps :type-id type-id :value-id (int (nth parts 4))
          :all (nth parts 5)}
       3 {:tag 3 :name nm :lps lps :type-id type-id :value-id (int (nth parts 4))
          :all (nth parts 5) :unsafe? (boolean (nth parts 6))}
       4 {:tag 4 :name nm :lps lps :type-id type-id :quot-kind (nth parts 4)}
       5 {:tag 5 :name nm :lps lps :type-id type-id
          :num-params (int (nth parts 4)) :num-indices (int (nth parts 5))
          :all (nth parts 6) :ctors (nth parts 7) :num-nested (int (nth parts 8))
          :is-rec (boolean (nth parts 9)) :is-reflexive (boolean (nth parts 10))
          :is-unsafe (boolean (nth parts 11))}
       6 {:tag 6 :name nm :lps lps :type-id type-id
          :induct-name (nth parts 4) :cidx (int (nth parts 5))
          :num-params (int (nth parts 6)) :num-fields (int (nth parts 7))
          :is-unsafe (boolean (nth parts 8))}
       7 {:tag 7 :name nm :lps lps :type-id type-id
          :all (nth parts 4) :num-params (int (nth parts 5)) :num-indices (int (nth parts 6))
          :num-motives (int (nth parts 7)) :num-minors (int (nth parts 8))
          :rules (nth parts 9) :is-k (boolean (nth parts 10))
          :is-unsafe (boolean (nth parts 11))}))))

;; ---- the registry ----

(defn install-elements
  "Register the kernel element types on `registry`. Public so an embedder can build its own
   codec over kernel values (the counterpart of ansatz-element-write-handlers)."
  [registry]
  (-> registry
      (boring/register-tag name-tag Name name->parts parts->name)
      (boring/register-tag level-tag Level level->parts parts->level)
      (boring/register-tag expr-tag Expr expr->parts parts->expr)
      (boring/register-tag ci-tag ConstantInfo ci->parts parts->ci)
      (boring/register-tag recursor-rule-tag ConstantInfo$RecursorRule rule->parts parts->rule)
      (boring/register-tag ci-shell-tag CIShell shell->parts parts->shell)))

(defn registry
  "The full store codec: kernel elements + canonical PSS node/root handlers.

   `resolve-storage` is pss-cbor's root resolver `(fn [root-meta] IStorage)` — the storage a
   root resolves to does not exist until the store is open, so callers pass
   `(fn [_] @storage-cell)` over a write-once cell, exactly as konserve-lmdb.pss does."
  ([resolve-storage] (registry resolve-storage {}))
  ([resolve-storage {:keys [default-bf] :or {default-bf 512}}]
   (-> (boring/tag-registry)
       (install-elements)
       (pss-cbor/install {:default-bf default-bf
                          :resolve-storage resolve-storage
                          :resolve-cmp (fn [_] compare)}))))
