(ns ansatz.export.role-input
  "Bounded raw candidate assembly over the existing trusted exporter decoder.
   Text/index/record gates are not an authentication or untrusted-file boundary."
  (:require [ansatz.export.parser :as parser]
            [ansatz.export.evidence :as evidence]
            [ansatz.export.storage :as storage])
  (:import [ansatz.kernel ExprStore]
           [java.io ByteArrayInputStream ByteArrayOutputStream]
           [java.nio ByteBuffer]
           [java.nio.charset StandardCharsets CodingErrorAction]
           [java.util ArrayList]
           [java.util.zip GZIPInputStream]))

(def ^:private input-keys #{:inflated-bytes :records :record-chars :name-index :level-index :expr-index :level-work :companion-rows})
(defn- fail [message data] (throw (ex-info message data)))
(defn- number! [value maximum field]
  (when-not (and (integer? value) (<= 0 value maximum))
    (fail "Unsupported raw export numeric field" {:field field}))
  (long value))

(defn- inflate [^bytes payload maximum]
  (with-open [input (GZIPInputStream. (ByteArrayInputStream. payload))
              output (ByteArrayOutputStream.)]
    (let [buffer (byte-array 8192)]
      (loop [size 0]
        (let [n (.read input buffer)]
          (if (neg? n)
            (str (.decode (doto (.newDecoder StandardCharsets/UTF_8)
                            (.onMalformedInput CodingErrorAction/REPORT)
                            (.onUnmappableCharacter CodingErrorAction/REPORT))
                          (ByteBuffer/wrap (.toByteArray output))))
            (let [total (+' size n)]
              (when (> total maximum) (fail "Candidate inflated byte limit exceeded" {:limit :inflated-bytes}))
              (.write output buffer 0 n)
              (recur total))))))))

(defn- ci-headers! [record name-ref! expr-ref!]
  (letfn [(array! [value field visit]
            (when-not (vector? value) (fail "Raw CI field requires an explicit array" {:field field}))
            (doseq [item value] (visit item)))
          (header! [kind value]
            (when-not (map? value) (fail "Raw CI header must be an object" {}))
            (name-ref! (get value "name"))
            (expr-ref! (get value "type"))
            (array! (get value "levelParams") :levelParams name-ref!)
            (when (contains? #{:def :thm :opaque} kind) (expr-ref! (get value "value")))
            (when (contains? #{:def :thm :opaque :induct :recursor} kind)
              (array! (get value "all") :all name-ref!))
            (doseq [field (case kind
                            :induct ["numParams" "numIndices" "numNested"]
                            :ctor ["cidx" "numParams" "numFields"]
                            :recursor ["numParams" "numIndices" "numMotives" "numMinors"] [])]
              (number! (get value field) Integer/MAX_VALUE field))
            (doseq [field (case kind
                            (:axiom :opaque :ctor) ["isUnsafe"]
                            :induct ["isUnsafe" "isRec" "isReflexive"]
                            :recursor ["isUnsafe" "k"] [])]
              (when-not (boolean? (get value field))
                (fail "Raw CI field requires an explicit boolean" {:field field})))
            (case kind
              :def (do
                     (when-not (contains? #{"safe" "unsafe" "partial"} (get value "safety"))
                       (fail "Unsupported raw definition safety" {}))
                     (let [hint (get value "hints")]
                       (when-not (or (and (string? hint) (contains? #{"opaque" "abbrev"} hint))
                                     (and (map? hint) (= #{"regular"} (set (keys hint)))
                                          (integer? (get hint "regular"))
                                          (<= 0 (get hint "regular") 4294967295)))
                         (fail "Unsupported raw reducibility hints" {}))))
              :quot (when-not (contains? #{"type" "ctor" "lift" "ind"} (get value "kind"))
                      (fail "Unsupported raw quotient kind" {}))
              :induct (array! (get value "ctors") :ctors name-ref!)
              :ctor (name-ref! (get value "induct"))
              :recursor (array! (get value "rules") :rules
                                (fn [rule]
                                  (name-ref! (get rule "ctor")) (expr-ref! (get rule "rhs"))
                                  (number! (get rule "nfields") Integer/MAX_VALUE :nfields)))
              nil))]
    (doseq [[key kind] [["axiom" :axiom] ["def" :def] ["thm" :thm] ["opaque" :opaque] ["quot" :quot]]]
      (when (contains? record key)
        (let [value (get record key)]
          (doseq [header (if (and (contains? #{:def :thm} kind) (vector? value)) value [value])]
            (header! kind header)))))
    (when-let [group (get record "inductive")]
      (doseq [[key alias kind] [["types" "inductiveVals" :induct]
                                ["ctors" "constructorVals" :ctor]
                                ["recs" "recursorVals" :recursor]]]
        (when (and (contains? group key) (contains? group alias))
          (fail "Raw inductive record contains conflicting field aliases" {}))
        (array! (get group key (get group alias)) key #(header! kind %))))))

(defn- guards [limits evidence-limits]
  (let [records (volatile! 0)
        names (volatile! {0 {:height 1 :cost 1}}) levels (volatile! {0 {:height 1 :cost 1}})
        exprs (volatile! #{}) level-work (volatile! 0)
        index! (fn [value kind]
                 (number! value (get limits kind) kind))
        ref! (fn [table id field]
               (or (get table (number! id Integer/MAX_VALUE field))
                   (fail "Raw export reference precedes its declaration" {:field field})))
        ;; Guard only fields narrowed by the ExprStore writer. CI expression
        ;; roots remain full integers and are checked by the shared materializer.
        expr! (fn [record]
                (let [id (index! (get record "ie") :expr-index)
                      e-ref #(index! % :expr-index)
                      n-ref #(index! % :name-index)
                      l-ref #(index! % :level-index)]
                  (when (contains? @exprs id) (fail "Repeated raw expression id" {}))
                  (when-not (= 1 (count (filter #(contains? record %)
                                                ["bvar" "sort" "const" "app" "lam" "forallE" "letE"
                                                 "proj" "natVal" "strVal" "mdata"])))
                    (fail "Raw expression requires exactly one supported variant" {}))
                  (cond
                    (contains? record "bvar") (number! (get record "bvar") Long/MAX_VALUE :bvar)
                    (contains? record "sort") (l-ref (get record "sort"))
                    (contains? record "const") (let [data (get record "const")
                                                     universes (get data "us")]
                                                 (n-ref (get data "name"))
                                                 (when-not (and (vector? universes) (<= (count universes) 65535))
                                                   (fail "Raw constant universes require an explicit array within the store format width" {}))
                                                 (doseq [u universes] (l-ref u)))
                    (contains? record "app") (let [data (get record "app")]
                                               (e-ref (get data "fn")) (e-ref (get data "arg")))
                    (or (contains? record "lam") (contains? record "forallE"))
                    (let [data (or (get record "lam") (get record "forallE"))]
                      (when-not (contains? #{"default" "implicit" "strictImplicit" "instImplicit"}
                                           (get data "binderInfo"))
                        (fail "Unsupported raw binder information" {}))
                      (n-ref (get data "name")) (e-ref (get data "type")) (e-ref (get data "body")))
                    (contains? record "letE") (let [data (get record "letE")]
                                                (n-ref (get data "name"))
                                                (doseq [field ["type" "value" "body"]] (e-ref (get data field))))
                    (contains? record "proj") (let [data (get record "proj")]
                                                (n-ref (get data "typeName")) (e-ref (get data "struct"))
                                                (number! (get data "idx") Integer/MAX_VALUE :projection))
                    (contains? record "natVal")
                    (let [value (get record "natVal")]
                      ;; ExprStore writes a UInt16 byte length, including the
                      ;; positive BigInteger sign byte. Bound decimal text before
                      ;; conversion and bit length before toByteArray allocation.
                      (when-not (or (integer? value)
                                    (and (string? value) (<= (.length ^String value) 157824)
                                         (re-matches #"[0-9]+" value)))
                        (fail "Raw natural literal exceeds the store format width" {}))
                      (let [number (biginteger value)]
                        (when (or (neg? (.signum number)) (> (.bitLength number) 524279))
                          (fail "Raw natural literal exceeds the store format width" {}))))
                    (contains? record "mdata") (e-ref (get-in record ["mdata" "expr"]))
                    :else nil)
                  (vswap! exprs conj id)))]
    {:before-line!
     (fn [^String line]
       (when (> (.length line) (:record-chars limits))
         (fail "Candidate record character limit exceeded" {:limit :record-chars}))
       (when (> (vswap! records inc) (:records limits))
         (fail "Candidate record count limit exceeded" {:limit :records})))
     :before-record!
     (fn [record]
       (when-not (map? record) (fail "Raw export record must be an object" {}))
       (when-not (= 1 (count (filter #(contains? record %)
                                     ["meta" "in" "il" "ie" "axiom" "def" "thm" "opaque" "quot" "inductive"])))
         (fail "Raw export record requires one supported record kind" {}))
       (ci-headers! record #(ref! @names % :declaration-name) #(index! % :expr-index))
       (cond
         (contains? record "in")
         (let [_ (when-not (= 1 (count (filter #(contains? record %) ["str" "num"])))
                   (fail "Raw name requires one supported variant" {}))
               id (index! (get record "in") :name-index)
               data (or (get record "str") (get record "num"))
               prefix (ref! @names (get data "pre") :name-prefix)
               text (when (contains? record "str") (get data "str"))
               _ (when (and (contains? record "str") (not (string? text)))
                   (fail "Unsupported raw name string" {}))
               height (inc (:height prefix))
               cost (+' (:cost prefix) 1 (if text (*' 2 (.length ^String text)) 0))]
           (when (contains? @names id) (fail "Repeated raw name id" {}))
           (when (> height (:name-depth evidence-limits)) (fail "Candidate Name depth exceeded" {:limit :name-depth}))
           (when (contains? record "num") (number! (get data "i") Long/MAX_VALUE :name-number))
           (vswap! names assoc id {:height height :cost cost}))
         (contains? record "il")
         (let [_ (when-not (= 1 (count (filter #(contains? record %) ["succ" "max" "imax" "param"])))
                   (fail "Raw Level requires one supported variant" {}))
               id (index! (get record "il") :level-index)
               children (cond (contains? record "succ") [(get record "succ")]
                              (contains? record "max") (get record "max")
                              (contains? record "imax") (get record "imax")
                              :else [])
               _ (when (and (or (contains? record "max") (contains? record "imax"))
                            (not (and (vector? children) (= 2 (count children)))))
                   (fail "Raw max/imax requires two children" {}))
               child-info (mapv #(ref! @levels % :level-child) children)
               height (inc (reduce max 0 (map :height child-info)))
               atom-cost (if (contains? record "param")
                           (:cost (ref! @names (get record "param") :level-param)) 1)
               cost (min (inc' (:level-work limits)) (+' atom-cost (reduce +' 0 (map :cost child-info))))
               work (*' 64 cost)]
           (when (contains? @levels id) (fail "Repeated raw level id" {}))
           (when (> height (:level-depth evidence-limits)) (fail "Candidate Level depth exceeded" {:limit :level-depth}))
           ;; Conservative local-constructor tree work, before normalized Level
           ;; constructors can revisit shared children. Expr assembly has its own
           ;; independent expanded-walk gate in evidence/materialize.
           (when (> (vswap! level-work +' work) (:level-work limits))
             (fail "Candidate Level construction work exceeded" {:limit :level-work}))
           (vswap! levels assoc id {:height height :cost cost}))
         (contains? record "ie") (expr! record)
         :else nil))}))

(defn- close-store! [^ExprStore store] (.close store))

(defn with-candidate
  "Assemble raw shells into a bounded CI batch and call f with detached CIs,
   original :inductive-groups and :meta. Close the parser store before returning
   f's result, including on assembly/replay/callback failure. A close failure
   prevents a successful result and is suppressed on an existing original error.
   JSON/Name/Level decoding is existing trusted infrastructure; input gates bound
   volume/index allocation and recursive constructors, not arbitrary decoder IO."
  [payload input-limits evidence-limits f]
  (when-not (and (map? input-limits) (= input-keys (set (keys input-limits)))
                 (every? #(and (integer? %) (pos? %) (<= % Long/MAX_VALUE)) (vals input-limits))
                 (every? #(<= (get input-limits %) Integer/MAX_VALUE) [:name-index :level-index :expr-index])
                 (every? #(and (integer? %) (<= 1 % 256))
                         (map evidence-limits [:name-depth :level-depth])) (ifn? f))
    (fail "Explicit finite raw candidate limits required" {}))
  (let [parsed (parser/parse-ndjson-string-raw
                (inflate payload (:inflated-bytes input-limits)) (guards input-limits evidence-limits))
        failure (volatile! nil)]
    (try
      (let [shells (:decls parsed)
            requested (mapv :name shells)
            by-name (into {} (map (juxt :name identity)) shells)
            result (evidence/materialize
                    requested {:shell by-name
                               :expr #(.readRaw ^ExprStore (:exprs parsed) (int %))
                               :name #(.get ^ArrayList (:names parsed) (int %))
                               :level #(.get ^ArrayList (:levels parsed) (int %))}
                    evidence-limits storage/resolve-ci-shell)]
        (f {:decls (mapv (:constants result) requested)
            :inductive-groups (:inductive-groups parsed) :meta (:meta parsed) :usage (:usage result)}))
      (catch Throwable error (vreset! failure error) (throw error))
      (finally
        (try (close-store! (:exprs parsed))
             (catch Throwable cleanup
               (if-let [original @failure]
                 (when-not (identical? original cleanup) (.addSuppressed ^Throwable original cleanup))
                 (throw cleanup))))))))
