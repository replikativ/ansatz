;; Copyright (c) 2026 Christian Weilbach. All rights reserved.
;; lean4export NDJSON parser.

(ns ansatz.export.parser
  "Parser for lean4export NDJSON format (version 3.1.0).
   Reads line-by-line, building up interned tables of Names, Levels, Exprs,
   then emitting Declarations."
  (:require [clojure.data.json :as json]
            [clojure.java.io :as io]
            [clojure.string]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.env :as env])
  (:import [java.util ArrayList]
           [ansatz.kernel ExprStore]))

;; ============================================================
;; Indexed table — ArrayList for O(1) access, much less memory
;; than a Clojure PersistentHashMap for sequential integer keys
;; ============================================================

(defn- mk-indexed-table
  "Create an ArrayList-backed indexed table with an optional initial entry."
  ([] (ArrayList.))
  ([init-idx init-val]
   (let [^ArrayList al (ArrayList. 1024)]
     ;; Pad up to init-idx
     (dotimes [_ init-idx] (.add al nil))
     (.add al init-val)
     al)))

(defn- table-set! [^ArrayList table idx val]
  ;; Extend if needed
  (while (<= (.size table) idx)
    (.add table nil))
  (.set table idx val))

;; ============================================================
;; Parser state
;; ============================================================

(defn mk-parser-state []
  (let [names  (mk-indexed-table 0 (name/anonymous))
        levels (mk-indexed-table 0 lvl/zero)]
    {:names  names                                   ;; index -> Name
     :levels levels                                  ;; index -> Level
     :exprs  (ExprStore. names levels)               ;; file-backed expr store
     :decls  []                     ;; accumulated declarations
     :meta   nil}))                 ;; metadata from first line

;; ============================================================
;; Name resolution
;; ============================================================

(defn- resolve-name [st idx]
  (let [^ArrayList names (:names st)]
    (if (and (>= idx 0) (< idx (.size names)))
      (.get names idx)  ;; nil is valid (anonymous name)
      (throw (ex-info (str "Unknown name index: " idx) {:idx idx})))))

(defn- resolve-level [st idx]
  (let [^ArrayList levels (:levels st)]
    (if (and (>= idx 0) (< idx (.size levels)))
      (let [v (.get levels idx)]
        (if (some? v)
          v
          (throw (ex-info (str "Unknown level index: " idx) {:idx idx}))))
      (throw (ex-info (str "Unknown level index: " idx) {:idx idx})))))

(defn- resolve-expr [st idx]
  (.resolve ^ExprStore (:exprs st) (int idx)))

;; ============================================================
;; Binder info parsing
;; ============================================================

(defn- parse-binder-info [s]
  (case s
    "default" :default
    "implicit" :implicit
    "strictImplicit" :strict-implicit
    "instImplicit" :inst-implicit
    :default))

;; ============================================================
;; Line parsers
;; ============================================================

(defn- parse-name-line [st obj]
  (let [idx (get obj "in")]
    (cond
      (contains? obj "str")
      (let [data (get obj "str")
            pre (resolve-name st (get data "pre"))
            s (get data "str")]
        (table-set! (:names st) idx (name/mk-str pre s))
        st)

      (contains? obj "num")
      (let [data (get obj "num")
            pre (resolve-name st (get data "pre"))
            i (get data "i")]
        (table-set! (:names st) idx (name/mk-num pre i))
        st)

      :else (throw (ex-info "Unknown name variant" {:obj obj})))))

(defn- parse-level-line [st obj]
  (let [idx (get obj "il")]
    (cond
      (contains? obj "succ")
      (do (table-set! (:levels st) idx (lvl/succ (resolve-level st (get obj "succ"))))
          st)

      (contains? obj "max")
      (let [[a b] (get obj "max")]
        (table-set! (:levels st) idx (lvl/level-max (resolve-level st a) (resolve-level st b)))
        st)

      (contains? obj "imax")
      (let [[a b] (get obj "imax")]
        (table-set! (:levels st) idx (lvl/imax (resolve-level st a) (resolve-level st b)))
        st)

      (contains? obj "param")
      (do (table-set! (:levels st) idx (lvl/param (resolve-name st (get obj "param"))))
          st)

      :else (throw (ex-info "Unknown level variant" {:obj obj})))))

(defn- parse-expr-line [st obj]
  (let [idx (int (get obj "ie"))
        ^ExprStore exprs (:exprs st)]
    (cond
      (contains? obj "bvar")
      (do (.storeBvar exprs idx (long (get obj "bvar"))) st)

      (contains? obj "sort")
      (do (.storeSort exprs idx (int (get obj "sort"))) st)

      (contains? obj "const")
      (let [data (get obj "const")
            us (get data "us")
            level-ids (int-array (count us) (map int us))]
        (.storeConst exprs idx (int (get data "name")) level-ids)
        st)

      (contains? obj "app")
      (let [data (get obj "app")]
        (.storeApp exprs idx (int (get data "fn")) (int (get data "arg")))
        st)

      (contains? obj "lam")
      (let [data (get obj "lam")]
        (.storeLam exprs idx
                   (ExprStore/binderInfoToByte (parse-binder-info (get data "binderInfo")))
                   (int (get data "name"))
                   (int (get data "type"))
                   (int (get data "body")))
        st)

      (contains? obj "forallE")
      (let [data (get obj "forallE")]
        (.storeForall exprs idx
                      (ExprStore/binderInfoToByte (parse-binder-info (get data "binderInfo")))
                      (int (get data "name"))
                      (int (get data "type"))
                      (int (get data "body")))
        st)

      (contains? obj "letE")
      (let [data (get obj "letE")]
        (.storeLet exprs idx
                   (int (get data "name"))
                   (int (get data "type"))
                   (int (get data "value"))
                   (int (get data "body")))
        st)

      (contains? obj "proj")
      (let [data (get obj "proj")]
        (.storeProj exprs idx
                    (int (get data "typeName"))
                    (int (get data "idx"))
                    (int (get data "struct")))
        st)

      (contains? obj "natVal")
      (do (.storeLitNat exprs idx (biginteger (get obj "natVal"))) st)

      (contains? obj "strVal")
      (do (.storeLitStr exprs idx (get obj "strVal")) st)

      (contains? obj "mdata")
      (let [data (get obj "mdata")]
        (.storeMdata exprs idx (int (get data "expr")))
        st)

      :else (throw (ex-info "Unknown expr variant" {:obj obj})))))

;; ============================================================
;; Declaration parsers
;; ============================================================

(defn- parse-level-params [st params]
  (mapv #(resolve-name st %) params))

(defn- parse-hints [h]
  (cond
    (= h "opaque") :opaque
    (= h "abbrev") :abbrev
    (map? h) {:regular (get h "regular")}
    :else :opaque))

(defn- parse-safety [s]
  (case s
    "safe" :safe
    "unsafe" :unsafe
    "partial" :partial
    :safe))

(defn- parse-axiom [st obj]
  (env/mk-axiom
   (resolve-name st (get obj "name"))
   (parse-level-params st (get obj "levelParams"))
   (resolve-expr st (get obj "type"))
   :unsafe? (get obj "isUnsafe" false)))

(defn- parse-def [st obj]
  (env/mk-def
   (resolve-name st (get obj "name"))
   (parse-level-params st (get obj "levelParams"))
   (resolve-expr st (get obj "type"))
   (resolve-expr st (get obj "value"))
   :hints (parse-hints (get obj "hints"))
   :safety (parse-safety (get obj "safety"))
   :all (mapv #(resolve-name st %) (get obj "all"))))

(defn- parse-thm [st obj]
  (env/mk-thm
   (resolve-name st (get obj "name"))
   (parse-level-params st (get obj "levelParams"))
   (resolve-expr st (get obj "type"))
   (resolve-expr st (get obj "value"))
   :all (mapv #(resolve-name st %) (get obj "all"))))

(defn- parse-opaque [st obj]
  (env/mk-opaque
   (resolve-name st (get obj "name"))
   (parse-level-params st (get obj "levelParams"))
   (resolve-expr st (get obj "type"))
   (resolve-expr st (get obj "value"))
   :all (mapv #(resolve-name st %) (get obj "all"))
   :unsafe? (get obj "isUnsafe" false)))

(defn- parse-quot [st obj]
  (env/mk-quot
   (resolve-name st (get obj "name"))
   (parse-level-params st (get obj "levelParams"))
   (resolve-expr st (get obj "type"))
   (keyword (get obj "kind"))))

(defn- parse-recursor-rule [st obj]
  (env/mk-recursor-rule
   (resolve-name st (get obj "ctor"))
   (get obj "nfields")
   (resolve-expr st (get obj "rhs"))))

(defn- parse-inductive [st obj]
  (let [types-raw (get obj "types" (get obj "inductiveVals" []))
        ctors-raw (get obj "ctors" (get obj "constructorVals" []))
        recs-raw (get obj "recs" (get obj "recursorVals" []))
        decls (atom [])]
    ;; Parse inductive types
    (doseq [t types-raw]
      (swap! decls conj
             (env/mk-induct
              (resolve-name st (get t "name"))
              (parse-level-params st (get t "levelParams"))
              (resolve-expr st (get t "type"))
              :num-params (get t "numParams")
              :num-indices (get t "numIndices")
              :all (mapv #(resolve-name st %) (get t "all"))
              :ctors (mapv #(resolve-name st %) (get t "ctors"))
              :num-nested (get t "numNested" 0)
              :rec? (get t "isRec" false)
              :reflexive? (get t "isReflexive" false)
              :unsafe? (get t "isUnsafe" false))))
    ;; Parse constructors
    (doseq [c ctors-raw]
      (swap! decls conj
             (env/mk-ctor
              (resolve-name st (get c "name"))
              (parse-level-params st (get c "levelParams"))
              (resolve-expr st (get c "type"))
              (resolve-name st (get c "induct"))
              (get c "cidx")
              (get c "numParams")
              (get c "numFields")
              :unsafe? (get c "isUnsafe" false))))
    ;; Parse recursors
    (doseq [r recs-raw]
      (swap! decls conj
             (env/mk-recursor
              (resolve-name st (get r "name"))
              (parse-level-params st (get r "levelParams"))
              (resolve-expr st (get r "type"))
              :all (mapv #(resolve-name st %) (get r "all"))
              :num-params (get r "numParams")
              :num-indices (get r "numIndices")
              :num-motives (get r "numMotives")
              :num-minors (get r "numMinors")
              :rules (mapv #(parse-recursor-rule st %) (get r "rules"))
              :k? (get r "k" false)
              :unsafe? (get r "isUnsafe" false))))
    @decls))

(defn- parse-decl-line [st obj]
  (cond
    (contains? obj "axiom")
    (update st :decls conj (parse-axiom st (get obj "axiom")))

    (contains? obj "def")
    (let [d (get obj "def")]
      ;; Can be object or array (format evolution)
      (if (vector? d)
        (reduce (fn [st' x] (update st' :decls conj (parse-def st' x))) st d)
        (update st :decls conj (parse-def st d))))

    (contains? obj "thm")
    (let [d (get obj "thm")]
      (if (vector? d)
        (reduce (fn [st' x] (update st' :decls conj (parse-thm st' x))) st d)
        (update st :decls conj (parse-thm st d))))

    (contains? obj "opaque")
    (update st :decls conj (parse-opaque st (get obj "opaque")))

    (contains? obj "quot")
    (update st :decls conj (parse-quot st (get obj "quot")))

    (contains? obj "inductive")
    (let [decls (parse-inductive st (get obj "inductive"))]
      (update st :decls into decls))

    :else st))

;; ============================================================
;; Line dispatch
;; ============================================================

(defn- parse-line [st obj]
  (cond
    (contains? obj "meta") (assoc st :meta (get obj "meta"))
    (contains? obj "in")   (parse-name-line st obj)
    (contains? obj "il")   (parse-level-line st obj)
    (contains? obj "ie")   (parse-expr-line st obj)
    :else                  (parse-decl-line st obj)))

;; ============================================================
;; Raw declaration parsers — emit CI-shells with expr IDs
;; ============================================================

(defn- parse-axiom-raw [st obj]
  {:tag 0
   :name (resolve-name st (get obj "name"))
   :lps (parse-level-params st (get obj "levelParams"))
   :type-id (get obj "type")
   :unsafe? (get obj "isUnsafe" false)})

(defn- parse-def-raw [st obj]
  {:tag 1
   :name (resolve-name st (get obj "name"))
   :lps (parse-level-params st (get obj "levelParams"))
   :type-id (get obj "type")
   :value-id (get obj "value")
   :hints (parse-hints (get obj "hints"))
   :safety (parse-safety (get obj "safety"))
   :all (mapv #(resolve-name st %) (get obj "all"))})

(defn- parse-thm-raw [st obj]
  {:tag 2
   :name (resolve-name st (get obj "name"))
   :lps (parse-level-params st (get obj "levelParams"))
   :type-id (get obj "type")
   :value-id (get obj "value")
   :all (mapv #(resolve-name st %) (get obj "all"))})

(defn- parse-opaque-raw [st obj]
  {:tag 3
   :name (resolve-name st (get obj "name"))
   :lps (parse-level-params st (get obj "levelParams"))
   :type-id (get obj "type")
   :value-id (get obj "value")
   :all (mapv #(resolve-name st %) (get obj "all"))
   :unsafe? (get obj "isUnsafe" false)})

(defn- parse-quot-raw [st obj]
  {:tag 4
   :name (resolve-name st (get obj "name"))
   :lps (parse-level-params st (get obj "levelParams"))
   :type-id (get obj "type")
   :quot-kind (keyword (get obj "kind"))})

(defn- parse-recursor-rule-raw [st obj]
  {:ctor (resolve-name st (get obj "ctor"))
   :nfields (get obj "nfields")
   :rhs-id (get obj "rhs")})

(defn- parse-inductive-raw [st obj]
  (let [types-raw (get obj "types" (get obj "inductiveVals" []))
        ctors-raw (get obj "ctors" (get obj "constructorVals" []))
        recs-raw (get obj "recs" (get obj "recursorVals" []))
        decls (atom [])]
    ;; Parse inductive types
    (doseq [t types-raw]
      (swap! decls conj
             {:tag 5
              :name (resolve-name st (get t "name"))
              :lps (parse-level-params st (get t "levelParams"))
              :type-id (get t "type")
              :num-params (get t "numParams")
              :num-indices (get t "numIndices")
              :all (mapv #(resolve-name st %) (get t "all"))
              :ctors (mapv #(resolve-name st %) (get t "ctors"))
              :num-nested (get t "numNested" 0)
              :is-rec (get t "isRec" false)
              :is-reflexive (get t "isReflexive" false)
              :is-unsafe (get t "isUnsafe" false)}))
    ;; Parse constructors
    (doseq [c ctors-raw]
      (swap! decls conj
             {:tag 6
              :name (resolve-name st (get c "name"))
              :lps (parse-level-params st (get c "levelParams"))
              :type-id (get c "type")
              :induct-name (resolve-name st (get c "induct"))
              :cidx (get c "cidx")
              :num-params (get c "numParams")
              :num-fields (get c "numFields")
              :is-unsafe (get c "isUnsafe" false)}))
    ;; Parse recursors
    (doseq [r recs-raw]
      (swap! decls conj
             {:tag 7
              :name (resolve-name st (get r "name"))
              :lps (parse-level-params st (get r "levelParams"))
              :type-id (get r "type")
              :all (mapv #(resolve-name st %) (get r "all"))
              :num-params (get r "numParams")
              :num-indices (get r "numIndices")
              :num-motives (get r "numMotives")
              :num-minors (get r "numMinors")
              :rules (mapv #(parse-recursor-rule-raw st %) (get r "rules"))
              :is-k (get r "k" false)
              :is-unsafe (get r "isUnsafe" false)}))
    @decls))

(defn- parse-decl-line-raw [st obj]
  (cond
    (contains? obj "axiom")
    (update st :decls conj (parse-axiom-raw st (get obj "axiom")))

    (contains? obj "def")
    (let [d (get obj "def")]
      (if (vector? d)
        (reduce (fn [st' x] (update st' :decls conj (parse-def-raw st' x))) st d)
        (update st :decls conj (parse-def-raw st d))))

    (contains? obj "thm")
    (let [d (get obj "thm")]
      (if (vector? d)
        (reduce (fn [st' x] (update st' :decls conj (parse-thm-raw st' x))) st d)
        (update st :decls conj (parse-thm-raw st d))))

    (contains? obj "opaque")
    (update st :decls conj (parse-opaque-raw st (get obj "opaque")))

    (contains? obj "quot")
    (update st :decls conj (parse-quot-raw st (get obj "quot")))

    (contains? obj "inductive")
    (let [decls (parse-inductive-raw st (get obj "inductive"))]
      (update st :decls into decls))

    :else st))

(defn- parse-line-raw [st obj]
  (cond
    (contains? obj "meta") (assoc st :meta (get obj "meta"))
    (contains? obj "in")   (parse-name-line st obj)
    (contains? obj "il")   (parse-level-line st obj)
    (contains? obj "ie")   (parse-expr-line st obj)
    :else                  (parse-decl-line-raw st obj)))

;; ============================================================
;; Public API
;; ============================================================

(defn parse-ndjson-string
  "Parse a lean4export NDJSON string. Returns parser state with :decls."
  [s]
  (let [lines (clojure.string/split-lines s)]
    (reduce (fn [st line]
              (let [line (clojure.string/trim line)]
                (if (empty? line)
                  st
                  (parse-line st (json/read-str line)))))
            (mk-parser-state)
            lines)))

(defn parse-ndjson-file
  "Parse a lean4export NDJSON file. Returns parser state with :decls."
  [path]
  (parse-ndjson-string (slurp path)))

(defn parse-ndjson-file-streaming
  "Parse a lean4export NDJSON file, calling decl-fn on each declaration.
   decl-fn receives [state decl] and returns updated state.
   This avoids holding all declarations in memory.
   Returns {:final-state state :parser-meta meta}."
  [path init-state decl-fn]
  (with-open [rdr (io/reader path)]
    (let [parser-st (atom (mk-parser-state))]
      (try
        (loop [state init-state
               lines (line-seq rdr)]
          (if-let [line (first lines)]
            (let [line (clojure.string/trim line)]
              (if (empty? line)
                (recur state (next lines))
                (let [obj (json/read-str line)
                      old-decl-count (count (:decls @parser-st))]
                  (swap! parser-st parse-line obj)
                  (let [new-decls (:decls @parser-st)
                        new-state (if (> (count new-decls) old-decl-count)
                                    ;; New declarations emitted — process them
                                    (let [fresh (subvec new-decls old-decl-count)]
                                      (swap! parser-st assoc :decls []) ;; clear to save memory
                                      (reduce decl-fn state fresh))
                                    state)]
                    (recur new-state (next lines))))))
            {:final-state state
             :parser-meta (:meta @parser-st)}))
        (finally
          (.close ^ExprStore (:exprs @parser-st)))))))

(defn parse-ndjson-file-streaming-raw
  "Parse a lean4export NDJSON file, calling decl-fn on each CI-shell.
   CI-shells contain expression IDs instead of resolved Expr objects.
   decl-fn receives [state ci-shell] and returns updated state.
   Returns {:final-state state :parser-state parser-state :parser-meta meta}.
   The parser-state contains :exprs (ExprStore), :names, :levels for bulk export."
  [path init-state decl-fn]
  (with-open [rdr (io/reader path)]
    (let [parser-st (atom (mk-parser-state))]
      (try
        (loop [state init-state
               lines (line-seq rdr)]
          (if-let [line (first lines)]
            (let [line (clojure.string/trim line)]
              (if (empty? line)
                (recur state (next lines))
                (let [obj (json/read-str line)
                      old-decl-count (count (:decls @parser-st))]
                  (swap! parser-st parse-line-raw obj)
                  (let [new-decls (:decls @parser-st)
                        new-state (if (> (count new-decls) old-decl-count)
                                    (let [fresh (subvec new-decls old-decl-count)]
                                      (swap! parser-st assoc :decls [])
                                      (reduce decl-fn state fresh))
                                    state)]
                    (recur new-state (next lines))))))
            {:final-state state
             :parser-state @parser-st
             :parser-meta (:meta @parser-st)}))
        (catch Exception e
          ;; Don't close ExprStore here — caller needs it for bulk export
          (throw e))))))

(defn build-env
  "Build a kernel environment from parsed declarations.
   Does NOT type-check — just adds declarations in order."
  [decls]
  (reduce (fn [env ci]
            (try
              (env/add-constant env ci)
              (catch Exception ex
                (println "Warning: skipping" (.name ^ansatz.kernel.ConstantInfo ci) "-" (.getMessage ex))
                env)))
          (env/empty-env)
          decls))

(defn load-ndjson
  "Parse an NDJSON file and build an environment (without type-checking)."
  [path]
  (let [st (parse-ndjson-file path)
        num-exprs (.size ^ExprStore (:exprs st))]
    (.close ^ExprStore (:exprs st))
    {:env (build-env (:decls st))
     :meta (:meta st)
     :num-names (.size ^ArrayList (:names st))
     :num-levels (.size ^ArrayList (:levels st))
     :num-exprs num-exprs
     :num-decls (count (:decls st))}))
