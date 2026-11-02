;; Ansatz kernel for Clojure — Lean-compatible hierarchical names.
;; Thin wrapper over Java Name class for interned identity comparison.

(ns ansatz.kernel.name
  "Hierarchical names matching Lean's Name type.
   Uses Java Name class with intern table for identity-based comparison.
   Name.anonymous is represented as Name/ANONYMOUS_NAME.
   Name.str as Name/mkStr.
   Name.num as Name/mkNum."
  (:import [ansatz.kernel Name]))

(defn anonymous [] Name/ANONYMOUS_NAME)

(defn mk-str
  "Create a Name.str: parent.s"
  [parent s]
  (Name/mkStr parent s))

(defn mk-num
  "Create a Name.num: parent.n"
  [parent n]
  (Name/mkNum parent (long n)))

(defn anonymous? [^Name n] (or (nil? n) (.isAnonymous n)))

(defn str-name? [^Name n] (and (some? n) (.isStr n)))
(defn num-name? [^Name n] (and (some? n) (.isNum n)))

(defn name-prefix ^Name [^Name n]
  (when (some? n) (.prefix n)))

(defn name-component [^Name n]
  (when (some? n)
    (case (.tag n)
      1 (.str n)    ;; STR
      2 (.num n)    ;; NUM
      nil)))

(defn ->string
  "Convert a Name to its dot-separated string representation."
  [^Name n]
  (if (or (nil? n) (.isAnonymous n))
    "[anonymous]"
    (.toString n)))

(defn from-string
  "Parse a dot-separated string into a Name."
  [s]
  (Name/fromString s))

;; Lean 4 v4.33.1 Init/Prelude.lean: Name.appendCore and macro-scope views.
(defn append-core
  "Lean Name.appendCore: concatenate components without interpreting scopes."
  [a b]
  (loop [n b parts ()]
    (if (anonymous? n)
      (reduce (fn [p part]
                (if (str-name? part)
                  (mk-str p (name-component part))
                  (mk-num p (name-component part)))) a parts)
      (recur (name-prefix n) (conj parts n)))))

(defn has-macro-scopes?
  "Lean Name.hasMacroScopes: trailing numbers preceded by _hyg."
  [n]
  (loop [n n]
    (cond
      (num-name? n) (recur (name-prefix n))
      (str-name? n) (= "_hyg" (name-component n))
      :else false)))

(defn erase-macro-scopes
  "Lean Name.eraseMacroScopes / eraseMacroScopesAux."
  [n]
  (if-not (has-macro-scopes? n)
    n
    (loop [n n]
      (cond
        (anonymous? n) (anonymous)
        (and (str-name? n) (= "_@" (name-component n))) (name-prefix n)
        :else (recur (name-prefix n))))))

(defn- assemble-parts [parts]
  (reduce (fn [p part]
            (if (str-name? part)
              (mk-str p (name-component part))
              (mk-num p (name-component part))))
          (anonymous) parts))

(defn- extract-imported [scopes ctx n]
  (loop [n n parts ()]
    (cond
      (anonymous? n) (throw (ex-info "Invalid macro-scoped name" {:kind :invalid-name}))
      (and (str-name? n) (= "_@" (name-component n)))
      {:name (name-prefix n) :ctx ctx :imported (assemble-parts parts) :scopes scopes}
      :else (recur (name-prefix n) (conj parts n)))))

(defn- extract-main-module [scopes n]
  (loop [n n parts ()]
    (cond
      (anonymous? n) (throw (ex-info "Invalid macro-scoped name" {:kind :invalid-name}))
      (num-name? n) (extract-imported scopes (assemble-parts parts) n)
      (= "_@" (name-component n))
      {:name (name-prefix n) :ctx (assemble-parts parts) :imported (anonymous) :scopes scopes}
      :else (recur (name-prefix n) (conj parts n)))))

(defn extract-macro-scopes
  "Lean extractMacroScopes: decode name, imported components, context and scopes."
  [n]
  (if-not (has-macro-scopes? n)
    {:name n :imported (anonymous) :ctx (anonymous) :scopes ()}
    (loop [n n scopes ()]
      (if (num-name? n)
        (recur (name-prefix n) (conj scopes (name-component n)))
        (extract-main-module scopes (name-prefix n))))))

(defn macro-scopes-view-review
  "Lean MacroScopesView.review: reconstruct a hygienic name from its view."
  [{:keys [name imported ctx scopes]}]
  (if (empty? scopes)
    name
    (reduce mk-num (mk-str (append-core (append-core (mk-str name "_@") imported) ctx)
                           "_hyg") scopes)))

(defn modify-base
  "Lean Init/Meta/Defs.lean Name.modifyBase: preserve scopes around f's result."
  [n f]
  (if (has-macro-scopes? n)
    (let [view (extract-macro-scopes n)]
      (macro-scopes-view-review (update view :name f)))
    (f n)))

(defn append
  "Lean Name.append: concatenate names, propagating scopes from one argument."
  [a b]
  (let [a-scoped? (has-macro-scopes? a)
        b-scoped? (has-macro-scopes? b)]
    (cond
      (and a-scoped? b-scoped?)
      (throw (ex-info "Invalid Name.append: both arguments have macro scopes"
                      {:kind :invalid-name}))
      a-scoped? (modify-base a #(append-core % b))
      b-scoped? (modify-base b #(append-core a %))
      :else (append-core a b))))
