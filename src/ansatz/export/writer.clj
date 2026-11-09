(ns ansatz.export.writer
  "Write declarations as a lean4export NDJSON file (format 3.1.0), the inverse of
   `ansatz.export.parser`.

   The file can be replayed by any checker that reads lean4export output, among
   them Lean 4's own kernel (`Lean.Environment.replay`, the Lean Kernel Arena's
   official checker, see tools/lean-replay). This lets Lean independently
   re-check what Ansatz admitted.

   `write-closure!` exports the dependency closure of a set of constants:
   - every constant referenced by a type, value or recursor rule;
   - an inductive's whole mutual group with its constructors and recursors,
     including nested auxiliaries (`T.rec_1` ...), as one `inductive` record.
     Lean regenerates the constructors and recursors and compares them with
     the exported ones;
   - the four quotient primitives as one unit after `Eq` (Lean adds them
     together);
   - `Nat` for natural number literals, and `String.ofList` for string
     literals (the kernel expands them through these).

   Declarations are written in dependency order, each after the names,
   levels and expressions it uses. Expressions are hash-consed by structure, so
   shared subterms are written once and the cost is linear in the size of the
   expression DAG.

   Lean's format has a `nondep` flag on `let` that Ansatz does not keep; it is
   written as false. Metadata is written as an empty object. A free variable or
   metavariable in a declaration throws: the environment holds only closed
   terms."
  (:require [ansatz.kernel.name :as name]
            [clojure.java.io :as io]
            [clojure.string :as str])
  (:import [ansatz.kernel ConstantInfo ConstantInfo$RecursorRule Env Expr Level Name]
           [java.io Writer]
           [java.util ArrayDeque ArrayList HashMap IdentityHashMap LinkedHashSet]))

(set! *warn-on-reflection* true)

(def format-version "3.1.0")

;; ============================================================
;; Names and constants
;; ============================================================

(defn- ->name ^Name [n]
  (cond (instance? Name n) n
        (symbol? n) (name/from-string (str n))
        (string? n) (name/from-string n)
        :else (throw (ex-info "Not a constant name" {:name n}))))

(defn- lookup ^ConstantInfo [^Env env ^Name n]
  (or (.lookup env n)
      (throw (ex-info (str "Unknown constant " n) {:name (str n)}))))

(defn- lookup? ^ConstantInfo [^Env env ^Name n] (.lookup env n))

(defn- const-levels [^Expr e] (seq (.o1 e)))

(defn- expr-constants
  "Add to `out` the constants an expression references, including the
   constants the kernel needs to interpret its literals."
  [^Expr root ^LinkedHashSet out]
  (let [seen (IdentityHashMap.)
        stack (ArrayDeque.)]
    (.push stack root)
    (while (not (.isEmpty stack))
      (let [^Expr e (.pop stack)]
        (when-not (.containsKey seen e)
          (.put seen e true)
          (case (int (.tag e))
            2 (.add out (.o0 e))
            3 (do (.push stack (.o0 e)) (.push stack (.o1 e)))
            (4 5) (do (.push stack (.o1 e)) (.push stack (.o2 e)))
            6 (do (.push stack (.o1 e)) (.push stack (.o2 e)) (.push stack (.o3 e)))
            7 (.add out (name/from-string "Nat"))
            8 (.add out (name/from-string "String.ofList"))
            9 (.push stack (.o1 e))
            10 (do (.add out (.o0 e)) (.push stack (.o1 e)))
            nil))))
    out))

(def ^:private quot-names (mapv name/from-string ["Quot" "Quot.mk" "Quot.lift" "Quot.ind"]))

(defn- inductive-group
  "The constants of an inductive's mutual group, in lean4export order:
   types, then their constructors, then the recursors (nested auxiliaries
   `T.rec_1` ... after the main ones)."
  [^Env env ^ConstantInfo ind]
  (let [types (mapv #(lookup env (->name %)) (or (seq (.all ind)) [(.name ind)]))
        ctors (vec (for [^ConstantInfo t types, c (.ctors t)] (lookup env c)))
        main-recs (keep #(lookup? env (name/mk-str (.name ^ConstantInfo %) "rec")) types)
        aux-recs (for [^ConstantInfo t types
                       :let [rs (->> (iterate inc 1)
                                     (map #(lookup? env (name/mk-str (.name t) (str "rec_" %))))
                                     (take-while some?))]
                       r rs]
                   r)]
    {:types types :ctors ctors :recs (vec (concat main-recs aux-recs))}))

(defn- unit-of
  "The unit a constant is written in: [:inductive head-name], [:quot] or [:single name]."
  [^Env env ^Name n]
  (let [ci (lookup env n)]
    (case (int (.tag ci))
      4 [:quot]
      5 [:inductive (->name (first (or (seq (.all ci)) [(.name ci)])))]
      6 [:inductive (let [ind (lookup env (.inductName ci))]
                      (->name (first (or (seq (.all ind)) [(.name ind)]))))]
      7 [:inductive (->name (first (.all ci)))]
      [:single n])))

(defn- unit-constants
  "The ConstantInfos a unit writes."
  [^Env env [kind n]]
  (case kind
    :single [(lookup env n)]
    :quot (mapv #(lookup env %) quot-names)
    :inductive (let [{:keys [types ctors recs]} (inductive-group env (lookup env n))]
                 (vec (concat types ctors recs)))))

(defn- ci-exprs [^ConstantInfo ci]
  (cond-> [(.type ci)]
    (#{1 2 3} (int (.tag ci))) (conj (.value ci))
    (= 7 (int (.tag ci))) (into (map #(.rhs ^ConstantInfo$RecursorRule %) (.rules ci)))))

(defn- unit-deps
  "The units a unit depends on, excluding itself."
  [^Env env unit]
  (let [out (LinkedHashSet.)]
    (doseq [ci (unit-constants env unit), e (ci-exprs ci)]
      (expr-constants e out))
    (when (= :quot (first unit)) (.add out (name/from-string "Eq")))
    (into [] (comp (map #(unit-of env %)) (distinct) (remove #(= % unit))) out)))

(defn closure-units
  "The units (see `unit-of`) of the dependency closure of `roots`, in
   dependency order: every unit after the units it uses."
  [^Env env roots]
  (let [done (java.util.HashSet.)
        on-stack (java.util.HashSet.)
        order (ArrayList.)
        stack (ArrayDeque.)]
    (doseq [r roots
            :let [u (unit-of env (->name r))]
            :when (not (.contains done u))]
      (.push stack [u (unit-deps env u)])
      (.add on-stack u)
      (while (not (.isEmpty stack))
        (let [[u deps] (.peek stack)]
          (if-let [d (first (remove #(.contains done %) deps))]
            (do (.pop stack)
                (.push stack [u (rest (drop-while #(not= d %) deps))])
                (when-not (.contains on-stack d)
                  (.add on-stack d)
                  (.push stack [d (unit-deps env d)])))
            (do (.pop stack)
                (.remove on-stack u)
                (.add done u)
                (.add order u))))))
    (vec order)))

;; ============================================================
;; NDJSON emission
;; ============================================================

(defn- json-str ^String [^String s]
  (let [sb (StringBuilder. (+ 2 (.length s)))]
    (.append sb \")
    (dotimes [i (.length s)]
      (let [c (.charAt s i)]
        (case c
          \" (.append sb "\\\"")
          \\ (.append sb "\\\\")
          \newline (.append sb "\\n")
          \return (.append sb "\\r")
          \tab (.append sb "\\t")
          (if (< (int c) 0x20)
            (.append sb (format "\\u%04x" (int c)))
            (.append sb c)))))
    (.append sb \")
    (.toString sb)))

(deftype ^:private Tables [^Writer w ^HashMap names ^HashMap levels
                           ^IdentityHashMap expr-ids ^HashMap expr-keys
                           ^longs counters])

(defn- line! [^Tables t ^String s]
  (.write ^Writer (.w t) s)
  (.write ^Writer (.w t) "\n"))

(defn- next-id! ^long [^Tables t i]
  (let [^longs c (.counters t) v (aget c i)]
    (aset c i (inc v))
    v))

(declare name-id*)

(defn- name-id
  "Id of a Name. Binder names are sometimes kept as strings; one is written as a
   single-component name (binder names do not affect checking)."
  ^long [^Tables t n]
  (cond (instance? Name n) (name-id* t n)
        (nil? n) 0
        :else (name-id* t (name/mk-str Name/ANONYMOUS_NAME (str n)))))

(defn- name-id* ^long [^Tables t ^Name n]
  (if (= Name/ANONYMOUS (.tag n))
    0
    (if-let [i (.get ^HashMap (.names t) n)]
      (long i)
      (let [p (name-id t (.prefix n))
            i (next-id! t 0)]
        (if (= Name/STR (.tag n))
          (line! t (str "{\"in\":" i ",\"str\":{\"pre\":" p ",\"str\":" (json-str (.str n)) "}}"))
          (line! t (str "{\"in\":" i ",\"num\":{\"pre\":" p ",\"i\":" (.num n) "}}")))
        (.put ^HashMap (.names t) n i)
        i))))

(defn- level-id ^long [^Tables t ^Level l]
  (if (= Level/ZERO (.tag l))
    0
    (if-let [i (.get ^HashMap (.levels t) l)]
      (long i)
      (let [s (case (int (.tag l))
                1 (str "\"succ\":" (level-id t (.o0 l)))
                2 (str "\"max\":[" (level-id t (.o0 l)) "," (level-id t (.o1 l)) "]")
                3 (str "\"imax\":[" (level-id t (.o0 l)) "," (level-id t (.o1 l)) "]")
                4 (str "\"param\":" (name-id t (.o0 l)))
                (throw (ex-info "Level metavariable in an exported declaration" {:level (str l)})))
            i (next-id! t 1)]
        (line! t (str "{\"il\":" i "," s "}"))
        (.put ^HashMap (.levels t) l i)
        i))))

(defn- binder-info ^String [bi]
  (case bi
    :implicit "implicit"
    :strict-implicit "strictImplicit"
    :inst-implicit "instImplicit"
    "default"))

(defn- expr-children [^Expr e]
  (case (int (.tag e))
    3 [(.o0 e) (.o1 e)]
    (4 5) [(.o1 e) (.o2 e)]
    6 [(.o1 e) (.o2 e) (.o3 e)]
    (9 10) [(.o1 e)]
    []))

(defn- emit-node!
  "Write one node whose children already have ids. Hash-conses on the
   node's payload and child ids."
  ^long [^Tables t ^Expr e]
  (let [^IdentityHashMap ids (.expr-ids t)
        cid (fn [x] (long (.get ids x)))
        [k body]
        (case (int (.tag e))
          0 [[0 (.longVal e)] (str "\"bvar\":" (.longVal e))]
          1 (let [l (level-id t (.o0 e))] [[1 l] (str "\"sort\":" l)])
          2 (let [n (name-id t (.o0 e))
                  us (mapv #(level-id t %) (const-levels e))]
              [[2 n us] (str "\"const\":{\"name\":" n ",\"us\":[" (str/join "," us) "]}")])
          3 (let [f (cid (.o0 e)) a (cid (.o1 e))]
              [[3 f a] (str "\"app\":{\"fn\":" f ",\"arg\":" a "}")])
          (4 5) (let [n (name-id t (.o0 e)) ty (cid (.o1 e)) b (cid (.o2 e))
                      bi (binder-info (.o3 e))]
                  [[(.tag e) n ty b bi]
                   (str (if (= 4 (int (.tag e))) "\"lam\":{" "\"forallE\":{")
                        "\"name\":" n ",\"type\":" ty ",\"body\":" b
                        ",\"binderInfo\":\"" bi "\"}")])
          6 (let [n (name-id t (.o0 e)) ty (cid (.o1 e)) v (cid (.o2 e)) b (cid (.o3 e))]
              [[6 n ty v b] (str "\"letE\":{\"name\":" n ",\"type\":" ty ",\"value\":" v
                                 ",\"body\":" b ",\"nondep\":false}")])
          7 [[7 (str (.o0 e))] (str "\"natVal\":\"" (.o0 e) "\"")]
          8 [[8 (.o0 e)] (str "\"strVal\":" (json-str (.o0 e)))]
          9 (let [x (cid (.o1 e))] [[9 x] (str "\"mdata\":{\"expr\":" x ",\"data\":{}}")])
          10 (let [n (name-id t (.o0 e)) s (cid (.o1 e))]
               [[10 n (.longVal e) s] (str "\"proj\":{\"typeName\":" n ",\"idx\":" (.longVal e)
                                           ",\"struct\":" s "}")])
          (throw (ex-info "Free variable or metavariable in an exported declaration"
                          {:expr (str e)})))]
    (if-let [i (.get ^HashMap (.expr-keys t) k)]
      (long i)
      (let [i (next-id! t 2)]
        (line! t (str "{\"ie\":" i "," body "}"))
        (.put ^HashMap (.expr-keys t) k i)
        i))))

(defn- expr-id
  "Write an expression bottom-up without recursion and return its id."
  ^long [^Tables t ^Expr root]
  (let [^IdentityHashMap ids (.expr-ids t)
        stack (ArrayDeque.)]
    (.push stack root)
    (while (not (.isEmpty stack))
      (let [^Expr e (.peek stack)]
        (if (.containsKey ids e)
          (.pop stack)
          (let [pending (remove #(.containsKey ids %) (expr-children e))]
            (if (seq pending)
              (doseq [c pending] (.push stack c))
              (do (.pop stack)
                  (.put ids e (emit-node! t e))))))))
    (long (.get ids root))))

(defn- ids-json [xs] (str "[" (str/join "," xs) "]"))

(defn- lparams-json [^Tables t ^ConstantInfo ci]
  (ids-json (map #(name-id t (->name %)) (.levelParams ci))))

(defn- all-json [^Tables t ^ConstantInfo ci]
  (ids-json (map #(name-id t (->name %)) (or (seq (.all ci)) [(.name ci)]))))

(defn- hints-json [^ConstantInfo ci]
  (let [h (.getHintsCode ci)]
    (cond (= h ConstantInfo/REDUCIBILITY_OPAQUE) "\"opaque\""
          (= h ConstantInfo/REDUCIBILITY_ABBREV) "\"abbrev\""
          :else (str "{\"regular\":" h "}"))))

(defn- safety-json [^ConstantInfo ci]
  (case (int (.getDefinitionSafety ci)) 1 "\"unsafe\"" 2 "\"partial\"" "\"safe\""))

(defn- write-single! [^Tables t ^ConstantInfo ci]
  (let [ty (expr-id t (.type ci))
        n (name-id t (.name ci))
        lps (lparams-json t ci)]
    (case (int (.tag ci))
      0 (line! t (str "{\"axiom\":{\"name\":" n ",\"levelParams\":" lps ",\"type\":" ty
                      ",\"isUnsafe\":" (.isUnsafe ci) "}}"))
      1 (let [v (expr-id t (.value ci)) all (all-json t ci)]
          (line! t (str "{\"def\":{\"name\":" n ",\"levelParams\":" lps ",\"type\":" ty
                        ",\"value\":" v ",\"hints\":" (hints-json ci)
                        ",\"safety\":" (safety-json ci) ",\"all\":" all "}}")))
      2 (let [v (expr-id t (.value ci)) all (all-json t ci)]
          (line! t (str "{\"thm\":{\"name\":" n ",\"levelParams\":" lps ",\"type\":" ty
                        ",\"value\":" v ",\"all\":" all "}}")))
      3 (let [v (expr-id t (.value ci)) all (all-json t ci)]
          (line! t (str "{\"opaque\":{\"name\":" n ",\"levelParams\":" lps ",\"type\":" ty
                        ",\"value\":" v ",\"isUnsafe\":" (.isUnsafe ci) ",\"all\":" all "}}")))
      4 (line! t (str "{\"quot\":{\"name\":" n ",\"levelParams\":" lps ",\"type\":" ty
                      ",\"kind\":\"" (name (.quotKind ci)) "\"}}")))))

(defn- write-inductive! [^Tables t ^Env env head]
  (let [{:keys [types ctors recs]} (inductive-group env (lookup env head))
        type-json (fn [^ConstantInfo ci]
                    (let [ty (expr-id t (.type ci))]
                      (str "{\"name\":" (name-id t (.name ci)) ",\"levelParams\":" (lparams-json t ci)
                           ",\"type\":" ty ",\"numParams\":" (.numParams ci)
                           ",\"numIndices\":" (.numIndices ci) ",\"all\":" (all-json t ci)
                           ",\"ctors\":" (ids-json (map #(name-id t %) (.ctors ci)))
                           ",\"numNested\":" (.numNested ci) ",\"isRec\":" (.isRec ci)
                           ",\"isUnsafe\":" (.isUnsafe ci) ",\"isReflexive\":" (.isReflexive ci) "}")))
        ctor-json (fn [^ConstantInfo ci]
                    (let [ty (expr-id t (.type ci))]
                      (str "{\"name\":" (name-id t (.name ci)) ",\"levelParams\":" (lparams-json t ci)
                           ",\"type\":" ty ",\"induct\":" (name-id t (.inductName ci))
                           ",\"cidx\":" (.cidx ci) ",\"numParams\":" (.numParams ci)
                           ",\"numFields\":" (.numFields ci) ",\"isUnsafe\":" (.isUnsafe ci) "}")))
        rule-json (fn [^ConstantInfo$RecursorRule r]
                    (let [rhs (expr-id t (.rhs r))]
                      (str "{\"ctor\":" (name-id t (.ctor r)) ",\"nfields\":" (.nfields r)
                           ",\"rhs\":" rhs "}")))
        rec-json (fn [^ConstantInfo ci]
                   (let [ty (expr-id t (.type ci))
                         rules (mapv rule-json (.rules ci))]
                     (str "{\"name\":" (name-id t (.name ci)) ",\"levelParams\":" (lparams-json t ci)
                          ",\"type\":" ty ",\"all\":" (all-json t ci)
                          ",\"numParams\":" (.numParams ci) ",\"numIndices\":" (.numIndices ci)
                          ",\"numMotives\":" (.numMotives ci) ",\"numMinors\":" (.numMinors ci)
                          ",\"rules\":[" (str/join "," rules) "],\"k\":" (.isK ci)
                          ",\"isUnsafe\":" (.isUnsafe ci) "}")))
        ;; Build the member records first: they write the names and expressions they use.
        ts (mapv type-json types)
        cs (mapv ctor-json ctors)
        rs (mapv rec-json recs)]
    (line! t (str "{\"inductive\":{\"types\":[" (str/join "," ts) "],\"ctors\":[" (str/join "," cs)
                  "],\"recs\":[" (str/join "," rs) "]}}"))))

(defn- meta-line ^String []
  (str "{\"meta\":{\"exporter\":{\"name\":\"ansatz\",\"version\":\"" format-version "\"},"
       "\"lean\":{\"githash\":\"\",\"version\":\"4.33.1\"},"
       "\"format\":{\"version\":\"" format-version "\"}}}"))

(defn write-closure!
  "Write the dependency closure of `roots` (constant names as strings, symbols
   or Names) in `env` to `out` (a path, File or Writer) as lean4export NDJSON.
   Returns {:units n :constants n :axioms [names] :non-safe [names] :names n
   :levels n :exprs n}. `:axioms` lists the axioms in the closure, for the trust
   report. `:non-safe` lists the unsafe and partial constants: Lean's
   `Environment.replay` skips them, so Lean does not check them (a safe
   declaration that uses one is then rejected as using an unknown constant)."
  [^Env env roots out]
  (let [units (closure-units env roots)
        own? (not (instance? Writer out))
        ^Writer w (if own? (io/writer (io/file (str out)) :encoding "UTF-8") out)]
    (try
      (let [t (Tables. w (HashMap.) (HashMap.) (IdentityHashMap.) (HashMap.) (long-array [1 1 0]))
            n-consts (volatile! 0)
            axioms (volatile! [])
            non-safe (volatile! [])]
        (line! t (meta-line))
        (doseq [[kind n :as u] units]
          (doseq [^ConstantInfo ci (unit-constants env u)]
            (when (.isAxiom ci) (vswap! axioms conj (str (.name ci))))
            (when (or (.isUnsafeDeclaration ci)
                      (and (.isDef ci) (= 2 (int (.getDefinitionSafety ci)))))
              (vswap! non-safe conj (str (.name ci))))
            (vswap! n-consts inc))
          (case kind
            :inductive (write-inductive! t env n)
            (doseq [ci (unit-constants env u)] (write-single! t ci))))
        (.flush w)
        (let [^longs c (.counters t)]
          {:units (count units) :constants @n-consts :axioms @axioms :non-safe @non-safe
           :names (dec (aget c 0)) :levels (dec (aget c 1)) :exprs (aget c 2)}))
      (finally (when own? (.close w))))))
