(ns ansatz.proof-cache
  "A cache of the proof terms `prove-theorem` builds, so loading a namespace again does not run
   its tactics again. It plays the role of Lean's .olean files for proofs, with one difference:
   a cached term is still checked by the kernel when it is used, against the statement as it
   elaborates now, so the cache cannot make the environment admit anything the kernel rejects.
   A stale or damaged entry fails that check, and the theorem is then proved by its tactics as if
   there were no entry.

   An entry is keyed by the theorem's name, its elaborated statement, the names it intros and
   its tactic script (SHA-256). It holds the theorems the tactics added to the environment
   (auxiliary lemmas) and then the theorem itself, in a small binary format: a DAG of names,
   levels and expressions, each written once, followed by the declarations. The constants they
   reference are not written; the kernel resolves them in its environment.

   What a hit reuses is a valid proof, not the tactic run. The recorded auxiliary theorems are
   replayed (kernel-checked); nothing else the tactics did is: their diagnostic output
   (`trace_state`), and whether they would succeed now, are not observed. A tactic run that
   changed an environment extension, the external view or the quotient state is never stored.
   Any failure to compute a key, encode or decode is a miss, never an error of the declaration.

   Off unless a directory is set: the system property `ansatz.proof-cache` or the environment
   variable `ANSATZ_PROOF_CACHE`, or `*dir*` bound directly. It is not used for proofs in an
   isolated ProofContext. One directory can be shared by several projects: keys are content
   digests."
  (:require [ansatz.export.writer :as writer]
            [clojure.java.io :as io]
            [clojure.walk])
  (:import [ansatz.kernel ConstantInfo Env Expr Level Name]
           [clojure.lang Keyword]
           [java.io ByteArrayOutputStream DataInputStream DataOutputStream OutputStream]
           [java.nio.charset StandardCharsets]
           [java.nio.file Files StandardCopyOption]
           [java.security DigestOutputStream MessageDigest]
           [java.util ArrayDeque ArrayList HashMap IdentityHashMap]))

(set! *warn-on-reflection* true)

(def ^:private entry-format
  "Bump when the entry layout or the key changes; old entries are then never read."
  "ansatz-proof-cache/3")

(def ^:private max-entry-bytes
  "Entries larger than this are not read (a proof term of this size is far beyond any seen)."
  (* 64 1024 1024))

(def ^:dynamic *dir*
  "The cache directory (a string or File), or nil for no cache."
  (not-empty (or (System/getProperty "ansatz.proof-cache") (System/getenv "ANSATZ_PROOF_CACHE"))))

(def stats
  "Counts since load: :hit, :miss, :rejected (an entry that is unreadable, has the wrong shape or
   that the kernel refused), :stored, :uncacheable (the tactics changed an environment
   extension, the external view or the quotient state, or added a constant that is not a plain
   theorem)."
  (atom {}))

(defn- count! [k] (swap! stats update k (fnil inc 0)))

;; ============================================================
;; Encoding: records in dependency order, each child written before its parent
;; ============================================================

(def ^:private r-end 0)
(def ^:private r-name-str 1)
(def ^:private r-name-num 2)
(def ^:private r-level 3)
(def ^:private r-expr 4)
(def ^:private r-thm 5)

(deftype ^:private Enc [^DataOutputStream out ^HashMap names ^HashMap levels ^IdentityHashMap exprs])

(defn- enc ^Enc [^OutputStream os]
  (let [names (HashMap.)]
    (.put names Name/ANONYMOUS_NAME (int 0))
    (Enc. (DataOutputStream. os) names (HashMap.) (IdentityHashMap.))))

(defn- write-str! [^DataOutputStream o ^String s]
  (let [b (.getBytes s StandardCharsets/UTF_8)]
    ;; UTF-8 replaces an unpaired surrogate: such a string would not come back as written
    (when-not (= s (String. b StandardCharsets/UTF_8))
      (throw (ex-info "proof-cache: a string UTF-8 cannot represent exactly" {})))
    (.writeInt o (alength b))
    (.write o b)))

(defn- read-str ^String [^DataInputStream in]
  (let [n (.readInt in)]
    (when-not (<= 0 n (.available in))
      (throw (ex-info "proof-cache: a string length beyond the entry" {:length n})))
    (let [b (byte-array n)]
      (.readFully in b)
      ;; strict: malformed bytes are an error, not U+FFFD in a string literal
      (str (.decode (doto (.newDecoder StandardCharsets/UTF_8)
                      (.onMalformedInput java.nio.charset.CodingErrorAction/REPORT)
                      (.onUnmappableCharacter java.nio.charset.CodingErrorAction/REPORT))
                    (java.nio.ByteBuffer/wrap b))))))

(defn- name-id ^long [^Enc e ^Name n]
  (if-let [i (.get ^HashMap (.names e) n)]
    (long i)
    (let [p (name-id e (.prefix n))
          ^DataOutputStream o (.out e)
          i (.size ^HashMap (.names e))]
      (if (= Name/STR (.tag n))
        (do (.writeByte o r-name-str) (.writeInt o p) (write-str! o (.str n)))
        (do (.writeByte o r-name-num) (.writeInt o p) (.writeLong o (.num n))))
      (.put ^HashMap (.names e) n (int i))
      i)))

(defn- obj-ref
  "A binder name, level parameter name or binder info, as [kind payload]; the names it needs
   are written now."
  [^Enc e o]
  (cond (nil? o) [0 nil]
        (instance? Name o) [1 (name-id e o)]
        (string? o) [2 o]
        (keyword? o) [3 (subs (str o) 1)]
        :else (throw (ex-info "proof-cache: an object it cannot write" {:class (class o)}))))

(defn- write-obj! [^DataOutputStream o [kind x]]
  (.writeByte o (int kind))
  (case (int kind) 0 nil 1 (.writeInt o (int x)) (2 3) (write-str! o x)))

(defn- read-obj [^DataInputStream in ^ArrayList names]
  (case (int (.readByte in))
    0 nil
    1 (.get names (.readInt in))
    2 (read-str in)
    3 (keyword (read-str in))))

(defn- level-id ^long [^Enc e ^Level l]
  (if-let [i (.get ^HashMap (.levels e) l)]
    (long i)
    (let [t (int (.tag l))
          a (case t 0 nil (1 2 3) (level-id e (.o0 l)) 4 (obj-ref e (.o0 l))
                  (throw (ex-info "proof-cache: a level metavariable" {})))
          b (case t (2 3) (level-id e (.o1 l)) nil)
          ^DataOutputStream o (.out e)
          i (.size ^HashMap (.levels e))]
      (.writeByte o r-level) (.writeByte o t)
      (case t 0 nil 1 (.writeInt o (int a)) (2 3) (do (.writeInt o (int a)) (.writeInt o (int b)))
            4 (write-obj! o a))
      (.put ^HashMap (.levels e) l (int i))
      i)))

(defn- expr-children [^Expr x]
  (case (int (.tag x))
    3 [(.o0 x) (.o1 x)]
    (4 5) [(.o1 x) (.o2 x)]
    6 [(.o1 x) (.o2 x) (.o3 x)]
    10 [(.o1 x)]
    []))

(defn- emit-expr! [^Enc e ^Expr x]
  (let [^IdentityHashMap ids (.exprs e)
        cid (fn [c] (int (.get ids c)))
        t (int (.tag x))
        ;; every id this record refers to is assigned (and its record written) before it starts
        payload
        (case t
          0 (.longVal x)
          1 (level-id e (.o0 x))
          2 [(obj-ref e (.o0 x)) (mapv #(level-id e %) (seq (.o1 x)))]
          3 [(cid (.o0 x)) (cid (.o1 x))]
          (4 5) [(obj-ref e (.o0 x)) (cid (.o1 x)) (cid (.o2 x)) (obj-ref e (.o3 x))]
          6 [(obj-ref e (.o0 x)) (cid (.o1 x)) (cid (.o2 x)) (cid (.o3 x))]
          7 (str (.o0 x))
          8 (.o0 x)
          10 [(obj-ref e (.o0 x)) (.longVal x) (cid (.o1 x))]
          (throw (ex-info "proof-cache: an expression it does not write (mdata, fvar or mvar)"
                          {:tag t})))
        ^DataOutputStream o (.out e)]
    (.writeByte o r-expr) (.writeByte o t)
    (case t
      0 (.writeLong o (long payload))
      1 (.writeInt o (int payload))
      2 (let [[n ls] payload] (write-obj! o n) (.writeInt o (count ls)) (doseq [l ls] (.writeInt o (int l))))
      3 (let [[f a] payload] (.writeInt o (int f)) (.writeInt o (int a)))
      (4 5) (let [[n ty b bi] payload]
              (write-obj! o n) (.writeInt o (int ty)) (.writeInt o (int b)) (write-obj! o bi))
      6 (let [[n ty v b] payload]
          (write-obj! o n) (.writeInt o (int ty)) (.writeInt o (int v)) (.writeInt o (int b)))
      (7 8) (write-str! o payload)
      10 (let [[n i s] payload] (write-obj! o n) (.writeLong o (long i)) (.writeInt o (int s))))
    (.put ids x (int (.size ids)))))

(defn- expr-id
  "Write `root` and its subterms (each once, children first) without recursion; its id."
  ^long [^Enc e ^Expr root]
  (let [^IdentityHashMap ids (.exprs e)
        stack (ArrayDeque.)]
    (.push stack root)
    (while (not (.isEmpty stack))
      (let [^Expr x (.peek stack)]
        (if (.containsKey ids x)
          (.pop stack)
          (let [pending (remove #(.containsKey ids %) (expr-children x))]
            (if (seq pending)
              (doseq [c pending] (.push stack c))
              (do (.pop stack) (emit-expr! e x)))))))
    (long (.get ids root))))

(defn- write-thm! [^Enc e ^ConstantInfo ci]
  ;; the reader rebuilds `all` as [name]; anything else would not round-trip
  (when-not (and (.isThm ci) (= [(.name ci)] (vec (.all ci))))
    (throw (ex-info "proof-cache: only plain theorems are written" {:name (str (.name ci))})))
  (let [n (obj-ref e (.name ci))
        lps (mapv #(obj-ref e %) (.levelParams ci))
        ty (expr-id e (.type ci))
        v (expr-id e (.value ci))
        ^DataOutputStream o (.out e)]
    (.writeByte o r-thm)
    (write-obj! o n)
    (.writeInt o (count lps)) (doseq [lp lps] (write-obj! o lp))
    (.writeInt o (int ty)) (.writeInt o (int v))))

(defn- read-entry
  "The theorems of an entry, in order."
  [^DataInputStream in]
  (when-not (= entry-format (read-str in))
    (throw (ex-info "proof-cache: another entry format" {})))
  (let [names (doto (ArrayList.) (.add Name/ANONYMOUS_NAME))
        levels (ArrayList.)
        exprs (ArrayList.)
        lvl (fn ^Level [^long i] (.get levels (int i)))
        ex (fn ^Expr [^long i] (.get exprs (int i)))]
    (loop [thms []]
      (let [r (int (.readByte in))]
        (condp = r
          r-end (if (zero? (.available in))
                  thms
                  (throw (ex-info "proof-cache: bytes after the end of the entry" {})))
          r-name-str (let [p (.readInt in)] (.add names (Name/mkStr (.get names p) (read-str in))) (recur thms))
          r-name-num (let [p (.readInt in)] (.add names (Name/mkNum (.get names p) (.readLong in))) (recur thms))
          r-level
          (let [t (int (.readByte in))]
            (.add levels
                  (case t
                    0 Level/ZERO_LEVEL
                    1 (Level/succ (lvl (.readInt in)))
                    2 (let [a (lvl (.readInt in))] (Level/max a (lvl (.readInt in))))
                    3 (let [a (lvl (.readInt in))] (Level/imax a (lvl (.readInt in))))
                    4 (Level/param (read-obj in names))))
            (recur thms))
          r-expr
          (let [t (int (.readByte in))]
            (.add exprs
                  (case t
                    0 (Expr/bvar (.readLong in))
                    1 (let [l (lvl (.readInt in))] (Expr/sort l (Level/hasParam l)))
                    2 (let [n (read-obj in names)
                            ls (let [k (.readInt in)]
                                 (when-not (<= 0 (* 4 k) (.available in))
                                   (throw (ex-info "proof-cache: a count beyond the entry" {:count k})))
                                 (vec (repeatedly k #(lvl (.readInt in)))))]
                        (Expr/mkConst n ls (boolean (some #(Level/hasParam %) ls))))
                    3 (let [f (ex (.readInt in))] (Expr/app f (ex (.readInt in))))
                    (4 5) (let [n (read-obj in names) ty (ex (.readInt in)) b (ex (.readInt in))
                                bi (read-obj in names)]
                            (if (= t 4) (Expr/lam n ty b bi) (Expr/forall n ty b bi)))
                    6 (let [n (read-obj in names) ty (ex (.readInt in)) v (ex (.readInt in))]
                        (Expr/mkLet n ty v (ex (.readInt in))))
                    7 (Expr/litNat (java.math.BigInteger. (read-str in)))
                    8 (Expr/litStr (read-str in))
                    10 (let [n (read-obj in names) i (.readLong in)] (Expr/proj n i (ex (.readInt in))))))
            (recur thms))
          r-thm
          (let [n (read-obj in names)
                lps (let [n (.readInt in)]
                      (when-not (<= 0 n (.available in))
                        (throw (ex-info "proof-cache: a count beyond the entry" {:count n})))
                      (vec (repeatedly n #(read-obj in names))))
                ty (ex (.readInt in))
                v (ex (.readInt in))]
            (recur (conj thms (ConstantInfo/mkThm n (into-array Object lps) ty v (into-array Object [n]))))))))))

;; ============================================================
;; Keys and entries
;; ============================================================

(defn- without-positions
  "`form` with the reader's source positions removed from all metadata, keeping the rest
   (type hints such as ^Nat on fn binders, which the elaborator reads)."
  [form]
  (clojure.walk/postwalk
   (fn [x]
     (if-let [m (and (instance? clojure.lang.IObj x) (meta x))]
       (let [m' (dissoc m :line :column :end-line :end-column :file :source)
             ;; type forms in metadata (^{:- (List Nat)}) carry reader positions of their own
             m' (into {} (map (fn [[k v]] [k (without-positions v)])) m')]
         (with-meta x (not-empty m')))
       x))
   form))

(defn- entry-key*
  [thm-name ^Expr goal-type intro-names tactic-forms]
  (when *dir*
    (let [script (binding [*print-length* nil *print-level* nil *print-meta* true
                           *print-namespace-maps* false *print-dup* false *print-readably* true]
                   (pr-str (without-positions [intro-names tactic-forms])))]
      (when-not (.contains ^String script "#object[")
        (let [md (MessageDigest/getInstance "SHA-256")
              os (DigestOutputStream. (OutputStream/nullOutputStream) md)
              e (enc os)
              ^DataOutputStream o (.out e)]
          (write-str! o entry-format) (write-str! o (str thm-name)) (write-str! o script)
          (expr-id e goal-type)
          (.flush o)
          (let [sb (StringBuilder.)]
            (doseq [b (.digest md)] (.append sb (format "%02x" (bit-and (int b) 0xff))))
            (.toString sb)))))))

(defn entry-key
  "The key of a theorem's entry, or nil when there is no cache, the script has no stable
   printed form (it holds an object that prints with its identity), or the statement cannot be
   encoded (mdata, a metavariable): the theorem is then proved without the cache."
  [thm-name goal-type intro-names tactic-forms]
  (try (entry-key* thm-name goal-type intro-names tactic-forms)
       (catch Exception _ nil)
       ;; a deeply nested script or statement must not fail the declaration either
       (catch StackOverflowError _ nil)))

(defn- entry-file ^java.io.File [^String k]
  (io/file (str *dir*) (subs k 0 2) (subs k 2)))

(defn lookup
  "The theorems of entry `k` (auxiliary ones first, the theorem last), nil when there is no
   entry, or ::unreadable."
  [k]
  (let [f (entry-file k)]
    (when (.isFile f)
      (try
        (when (> (.length f) max-entry-bytes)
          (throw (ex-info "proof-cache: entry larger than the budget" {:bytes (.length f)})))
        (with-open [in (DataInputStream. (java.io.ByteArrayInputStream. (Files/readAllBytes (.toPath f))))]
          (read-entry in))
        (catch Throwable _ ::unreadable)))))

(defn- dependency-order
  "The constants `cis` ordered so that each comes after those of `cis` it references."
  [cis]
  (let [by-name (into {} (map (fn [^ConstantInfo ci] [(.name ci) ci])) cis)
        refs (fn [^ConstantInfo ci]
               (let [acc (java.util.LinkedHashSet.)]
                 (writer/expr-constants (.type ci) acc)
                 (writer/expr-constants (.value ci) acc)
                 (remove #(= (.name ci) %) (filter by-name acc))))]
    (loop [todo (vec (keys by-name)) done #{} out []]
      (if-let [n (peek todo)]
        (if (done n)
          (recur (pop todo) done out)
          (let [pending (remove done (refs (by-name n)))]
            (if (seq pending)
              (recur (into todo pending) done out)
              (recur (pop todo) (conj done n) (conj out (by-name n))))))
        out))))

(defn added-constants
  "The theorems `after` holds that `before` does not, in dependency order, or ::uncacheable
   when the step between them did anything else: changed an environment extension, the
   external view or the quotient state, replaced or dropped an earlier local constant, or added
   a constant that is not a plain theorem (default `all` list)."
  [^Env before ^Env after]
  (cond
    (not (identical? (. before (extensions)) (. after (extensions)))) ::uncacheable
    (not (.sameExternalView before after)) ::uncacheable
    (not= (.isQuotEnabled before) (.isQuotEnabled after)) ::uncacheable
    ;; the same local overlay: nothing added (with an external store `size` does not show it)
    (.sameLocals before after) []
    :else
    (let [locals (.allConstants after)
          added (filterv (fn [^ConstantInfo ci] (nil? (.lookupLocal before (.name ci)))) locals)
          ;; every earlier local kept, identically; a tactic that replaced or dropped one (e.g. by
          ;; switching to a sibling env) cannot be replayed as an addition
          kept? (and (= (.localCount after) (+ (.localCount before) (count added)))
                     (every? (fn [^ConstantInfo ci]
                               (let [old (.lookupLocal before (.name ci))]
                                 (or (nil? old) (identical? old ci))))
                             locals))]
      ;; the entry stores theorems with the default `all` list only
      (if (and kept? (every? (fn [^ConstantInfo ci] (and (.isThm ci) (= [(.name ci)] (vec (.all ci))))) added))
        (dependency-order added)
        ::uncacheable))))

(defn store!
  "Write entry `k`: the added theorems `aux` (dependency order) and then the theorem `thm`.
   A failure to write only means no entry."
  [k aux ^ConstantInfo thm]
  (try
    (let [f (entry-file k)
          dir (doto (.getParentFile f) (.mkdirs))
          tmp (java.io.File/createTempFile "entry" ".tmp" dir)
          bytes (ByteArrayOutputStream.)
          e (enc bytes)]
      (write-str! (.out e) entry-format)
      (doseq [ci (conj (vec aux) thm)] (write-thm! e ci))
      (.writeByte ^DataOutputStream (.out e) r-end)
      (.flush ^DataOutputStream (.out e))
      (Files/write (.toPath tmp) (.toByteArray bytes) ^"[Ljava.nio.file.OpenOption;" (make-array java.nio.file.OpenOption 0))
      (Files/move (.toPath tmp) (.toPath f)
                  (into-array java.nio.file.CopyOption [StandardCopyOption/ATOMIC_MOVE
                                                        StandardCopyOption/REPLACE_EXISTING]))
      (count! :stored))
    (catch Throwable _ nil)))

(defn replay
  "Check entry `k` into `env`: its auxiliary theorems with `check-constant`, then the theorem
   `cname` with the statement `goal-type` (elaborated now, not read from the entry) and the
   entry's proof term, as `prove-theorem` checks the term its tactics built. Returns the new env,
   or nil when there is no usable entry or the kernel rejects a constant."
  [k ^Env env ^Name cname ^Expr goal-type check-constant mk-thm]
  (let [cis (lookup k)]
    (cond
      (nil? cis) (do (count! :miss) nil)
      (= ::unreadable cis) (do (count! :rejected) nil)
      :else
      (let [^ConstantInfo thm (peek cis)]
        (if (and thm (= cname (.name thm)) (empty? (.levelParams thm)))
          (try
            (let [env' (reduce check-constant env (pop cis))
                  env' (check-constant env' (mk-thm cname [] goal-type (.value thm)))]
              (count! :hit)
              env')
            (catch Throwable _ (count! :rejected) nil))
          (do (count! :rejected) nil))))))
